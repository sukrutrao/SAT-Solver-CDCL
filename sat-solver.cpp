#include <iostream>
#include <string>
#include <cmath>
#include <algorithm>
#include <vector>

using namespace std;

enum CState
{
    satisfied,
    unsatisfied,
    unit,
    unresolved
};

enum RetVal
{
    r_satisfied,
    r_unsatisfied,
    r_normal,
    r_completed
};

class SATSolverCDCL
{
    public:
        vector<int> literals;
        vector<int> literal_frequency;
        vector<int> original_literal_frequency;
        vector<int> literal_polarity;
        vector< vector<int> > literal_list_per_clause;
        vector<int> literal_antecedent;
        vector<int> literal_decision_level;
        int literal_count;
        int original_clause_count;
        int clause_count;
        int learned_clause_count;
        int assigned_literal_count;
        int current_decision_level;
        bool already_unsatisfied;
        int kappa;
        int kappa_decision_level;
        int kappa_antecedent;
        SATSolverCDCL() {}
        void initialize();
        int unit_propagate(int);
        bool all_variables_assigned();
        int pick_branching_variable();
        int variable_to_literal_index(int);
        vector<int> resolve(vector<int>,int);
        vector<int> get_learned_clause(int,int);
        void assign_literal(int,int,int);
        void unassign_literal(int);
        int apply_transform(int);
        int get_clause_state(int);
        int CDCL();
        int conflict_analysis_and_backtrack();
        void show_result(int);
        void solve();
};

void SATSolverCDCL::initialize()
{
    char c; // store first character
    string s; // dummy string

    while(true)
    {
        cin>>c;
        if(c=='c') // if comment
        {
            getline(cin,s); // ignore
        }
        else // else, if would be a p
        {
            cin >> s; // this would be cnf
            break;
        }
    }
    cin>>literal_count;
    cin>>original_clause_count;
    clause_count = original_clause_count;
    learned_clause_count = 0;
    assigned_literal_count = 0;
    current_decision_level = -1;
    kappa_antecedent = -1;
    kappa_decision_level = -1;
    already_unsatisfied = false;
    kappa = literal_count;
    // set the vectors to their appropriate sizes and initial values
    literals.clear();
    literals.resize(literal_count,-1);
    literal_frequency.clear();
    literal_frequency.resize(literal_count,0);
    literal_polarity.clear();
    literal_polarity.resize(literal_count,0);
    literal_list_per_clause.clear();
    literal_list_per_clause.resize(clause_count);
    literal_antecedent.clear();
    literal_antecedent.resize(literal_count,-1); // for kappa
    literal_decision_level.clear();
    literal_decision_level.resize(literal_count,-1); // we will set the decision level of kappa as the level of conflict
    
    int literal; // store the incoming literal value
    int literal_count_in_clause = 0;
    // iterate over the clauses
    for(int i = 0; i < clause_count; i++)
    {
        literal_count_in_clause = 0;
        while(true) // while the ith clause gets more literals
        {
            cin>>literal;     
            if(literal > 0) // if the variable has positive polarity
            {
                literal_list_per_clause[i].push_back(literal); // store it in the form 2n
                // increment frequency and polarity of the literal
                literal_frequency[literal-1]++; 
                literal_polarity[literal-1]++;
            }
            else if(literal < 0) // if the variable has negative polarity
            {
                literal_list_per_clause[i].push_back(literal); // store it in the form 2n+1
                // increment frequency and decrement polarity of the literal
                literal_frequency[-1-literal]++;
                literal_polarity[-1-literal]--;
            }
            else
            {
                if(literal_count_in_clause == 0)
                {
                    already_unsatisfied = true;
                }
                break; // read 0, so move to next clause
            }    
            literal_count_in_clause++;
        }       
    }
    original_literal_frequency = literal_frequency; // backup for restoring when backtracking
/*    literal_decision_level[kappa] = -1;
    literal_antecedent[kappa] = -1; */
    cout << "Done initializing" << endl;
}

int SATSolverCDCL::variable_to_literal_index(int variable)
{
    return (variable > 0) ? variable-1 : -variable-1;
}

vector<int> SATSolverCDCL::resolve(vector<int> clause, int antecedent_of_l)
{
    vector<int> result = clause;
    int antecedent_of_l_index = variable_to_literal_index(antecedent_of_l);
    vector<int> antecedent = literal_list_per_clause[literal_antecedent[antecedent_of_l_index]];
    result.insert(result.end(),antecedent.begin(),antecedent.end());
 /*   cout << "Result Initial : " << endl;
    for(int i = 0; i < result.size(); i++)
    {
        cout << result[i] << " ";
    }
    cout << endl;*/
    int count = 0;
    for(int i = 0; i < result.size(); i++)
    {
        if(result[i] == antecedent_of_l || result[i] == -antecedent_of_l)
        {
            result.erase(result.begin()+i);
            i--;
            count++;
        }
    }
    sort(result.begin(),result.end());
    result.erase(unique(result.begin(),result.end()),result.end());
    if(count != 2)
    {
        cout<<"Error!"<<endl;
        exit(0);
    }
  //  unassign_literal(antecedent_of_l);
 /*   cout << "Result Final : " << endl;
    for(int i = 0; i < result.size(); i++)
    {
        cout << result[i] << " ";
    }
    cout << endl;*/
    return result;
}

vector<int> SATSolverCDCL::get_learned_clause(int decision_level, int clause) // clause should be literal_antecedent of kappa
{
    int t = 0;
    cout << "In glk" << endl;  
 /*   cout << "Learning clause at level : " << decision_level << endl;
    cout << "Decision levels are : ";
    for(int i = 0; i < literal_decision_level.size(); i++)
    {
        cout << literal_decision_level[i] << " ";
    }
    cout << endl;*/
    vector<int> current_clause = literal_list_per_clause[clause]; // TODO check this exists
    vector<int> next_clause;
    int count = 0;
    do
    {
        count = 0;
        if(t > 50)
        {
            cout << "Exiting" << endl;
            exit(0);
        }
  //      cout << "In do-while" << endl;
   /*     cout << "Current clause : " << endl;
        for(int i = 0; i < current_clause.size(); i++)
        {
            int literal = variable_to_literal_index(current_clause[i]);
            cout << literal << " ";
        }
        cout << endl; */
        int level_count = 0;
        for(int i = 0; i < current_clause.size(); i++)
        {
            int literal = variable_to_literal_index(current_clause[i]);
            if(literal_decision_level[literal] == decision_level)
            {
                level_count++;
            }
        }
 //       cout << "LC : " << level_count << endl;
        if(level_count == 1)
        {
            cout << "Sigma is true " << endl;
            if(t == 0)
            {
                cout << "QQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQQ" << endl;
                exit(0);
            }
            else
            {
                return current_clause;
            }
        }
        for(int i = 0; i < current_clause.size(); i++)
        {
            int literal = variable_to_literal_index(current_clause[i]);
  //          cout << "Literal : " << literal << " DL : " << literal_decision_level[literal] << endl;
            if(literal_decision_level[literal] == decision_level && literal_antecedent[literal] != -1) // can optimize this by checking other two conditions before the loop
            {
    //            cout << "INIF Literal : " << literal << " DL : " << literal_decision_level[literal] << endl;
                current_clause = resolve(current_clause,current_clause[i]);
                break;
            }
            else
            {
                count++;
            }
        }
    /*    if(count == current_clause.size())
        {
            cout << "Did not find any" << endl;
            return current_clause;
        }*/
  //      current_clause = next_clause;
        t++;
    }while(true);
}

void SATSolverCDCL::assign_literal(int literal, int decision_level, int antecedent)
{
    cout << "LIA : " << literal << endl;
    int value = (literal>0) ? 1 : 0;
    literal = variable_to_literal_index(literal);
  //  literal = (literal>0) ? literal-1 : -literal-1;
    literals[literal] = value;
    literal_decision_level[literal] = decision_level;
    literal_antecedent[literal] = antecedent;
    literal_frequency[literal] = -1;
    assigned_literal_count++;
}

void SATSolverCDCL::unassign_literal(int literal)
{
    literals[literal] = -1;
    literal_antecedent[literal] = -1;
    literal_decision_level[literal] = -1;
    literal_frequency[literal] = original_literal_frequency[literal];
    assigned_literal_count--;
}

bool SATSolverCDCL::all_variables_assigned()
{
    return assigned_literal_count == literal_count;
}

int SATSolverCDCL::pick_branching_variable()
{
    int variable = distance(literal_frequency.begin(),max_element(literal_frequency.begin(),literal_frequency.end()));
    if(literal_frequency[variable] < 0)
    {
        cout << "LT0!!!!!!!!!!!!" << endl;
        exit(0);
    }
    if(literal_polarity[variable] >= 0)
    {
        cout << "Picked " << variable+1 << endl;
        return variable+1;
    }
    cout << "Picked " << -variable-1 << endl;
    return -variable-1;
}

int SATSolverCDCL::unit_propagate(int decision_level)
{
    bool unit_clause_found = false;
    cout << "State at start of unit propagation : " << endl;
 /*   cout << "Literals : " << endl;
    for(int i = 0; i < literals.size(); i++)
    {
        cout << literals[i] << " ";
    }
    cout << endl;
    for(int k = 0; k < clause_count; k++)
    {
        if(get_clause_state(k) == CState::unsatisfied)
        {
            cout << "Clause unsatisfied is : k : " << k << endl;
            for(int c = 0; c < literal_list_per_clause[k].size(); c++)
            {
                cout << literal_list_per_clause[k][c] << " ";
            }
            cout << endl;
            
        }
    }*/
    do 
    {
        unit_clause_found = false;
        for(int i = 0; (i < clause_count) && !unit_clause_found; i++)
        {
 //           cout << "In for UP" << endl;
        //    cout << "In UP I : " << i << "State : " << get_clause_state(i) << endl;
            int clause_state = get_clause_state(i);
            if(clause_state == CState::unit) // if a unit clause is found
            {
                unit_clause_found = true;
                cout << "Found a unit clause : " << i << " clause count : " << clause_count << endl;
        /*        cout << "Literals : " << endl;
                for(int i = 0; i < literals.size(); i++)
                {
                    cout << literals[i] << " ";
                }
                cout << endl;*/
                for(int j = 0; j < literal_list_per_clause[i].size(); j++)
                {
                    int literal = variable_to_literal_index(literal_list_per_clause[i][j]);
                    if(literals[literal] == -1) // unassigned variable found
                    {
                        cout << "Literal found is : " << literal << " in clause : " << i << endl;
                //        int literal_here = literal_list_per_clause[i][j]/2; // variable index
                        literal_antecedent[literal] = i; // antecedent is this clause
                        literal_decision_level[literal] = decision_level; //get_decision_level(literal_here); //TODO or current_decision_level? // find decision level
                        // graph edges ??? TODO
                        if(literal_list_per_clause[i][j] > 0) // if positive polarity
                        {
                            literals[literal] = 1; // assign positive
                        }
                        else 
                        {
                            literals[literal] = 0; // assign negative
                        }
                        literal_frequency[literal] = -1;
                        assigned_literal_count++;
                   /*     for(int k = 0; k < clause_count; k++)
                        {
                            if(get_clause_state(k) == CState::unsatisfied)
                            {
                                cout << "Clause unsatisfied is : k : " << k << endl;
                                for(int c = 0; c < literal_list_per_clause[k].size(); c++)
                                {
                                    cout << literal_list_per_clause[k][c] << " ";
                                }
                                cout << endl;
                                literal_antecedent[kappa] = k;
                                literal_decision_level[kappa] = current_decision_level; //? TODO check!
                                cout << "LDLK : " << literal_decision_level[kappa] << endl;
                                return RetVal::r_unsatisfied;
                            }
                        }*/
                        break;
                    }
                }
            }
            else if(clause_state == CState::unsatisfied)
            {
                // TODO declare conflict?
                cout << "Found conflict in clause : " << i << endl; 
                for(int j = 0; j < literals.size(); j++)
                {
                    cout << j << " : " << literals[j] << "@" << literal_decision_level[j] << " A : " << literal_antecedent[j] << endl;
                }
                cout << endl; 
                for(int j = 0; j < literal_list_per_clause[i].size(); j++)
                {
                    cout << literal_list_per_clause[i][j] << " ";
                }
                cout << endl;
                literal_antecedent[kappa] = i;
                cout << "Antecedent of kappa : " << i << endl;
                literal_decision_level[kappa] = decision_level; //? TODO check!
                cout << "LDLK : " << literal_decision_level[kappa] << endl;
                return RetVal::r_unsatisfied;
            }
      //      cout << "At end" << endl;
            
        }    
    }while(unit_clause_found);
    return RetVal::r_normal;
}

// TODO - with watched literals, clauses_states make no sense - DONE

int SATSolverCDCL::get_clause_state(int clause)
{
    int false_count = 0;
    int unset_count = 0;
  /*  cout << "Clause is : " << endl;
    for(int i = 0; i < literal_list_per_clause[clause].size(); i++)
    {
        cout << literal_list_per_clause[clause][i] << " ";
    }
    cout << endl;*/
/*    cout << "Literals : ";
    for(int i = 0; i < literals.size(); i++)
    {
        cout << literals[i] << " ";
    }
    cout << endl;
    cout << "Clause ID : " << clause << endl; */
    for(int i = 0; i < literal_list_per_clause[clause].size(); i++)
    {
        int literal_index = literal_list_per_clause[clause][i];
    //    cout << "LI : " << literal_index << endl;
        if((literal_index > 0 && literals[literal_index-1] == 0) || (literal_index < 0 && literals[-literal_index-1] == 1))
        {
            false_count++;
        }
        else if((literal_index > 0 && literals[literal_index-1] == -1) || (literal_index < 0 && literals[-literal_index-1] == -1))
        {
            unset_count++;
        }
        else if((literal_index > 0 && literals[literal_index-1] == 1) || (literal_index < 0 && literals[-literal_index-1] == 0))
        {
            return CState::satisfied;
        }
    }
  //  cout << "FC : " << false_count << " UC : " << unset_count << endl;
    if(false_count == literal_list_per_clause[clause].size()) // TODO what about references' positions?
    {
        return CState::unsatisfied;
    }
    if(unset_count == 1)
    {
        return CState::unit;
    }
    return CState::unresolved;
}

int SATSolverCDCL::CDCL()
{
    int decision_level = 0;
    if(already_unsatisfied)
    {
        show_result(RetVal::r_unsatisfied);
        return RetVal::r_completed;
    }
    if(unit_propagate(0) == RetVal::r_unsatisfied)
    {
        show_result(RetVal::r_unsatisfied);
        return RetVal::r_completed;
    }
//    current_decision_level = 0;
    while(!all_variables_assigned())
    {  
        cout << "#####################################################################################" << endl; 
        if(kappa != literal_count)
        {
            cout << "KE!" << endl;
            exit(0);
        } 
        int current_literal = pick_branching_variable();
        decision_level++;
        assign_literal(current_literal,decision_level,-1);
        cout << "Literals : ";
        for(int i = 0; i < literals.size(); i++)
        {
            cout << literals[i] << " ";
        }
        cout << endl;
        while(true)
        {
            cout << "Starting UP" << endl;
            if(kappa != literal_count)
            {
                cout << "KE!" << endl;
                exit(0);
            } 
            if(unit_propagate(decision_level) == RetVal::r_unsatisfied)
            {
                if(literal_decision_level[kappa] < 0) // this will happen when decision_level < 0 by CAandB
                {
                    cout << "Got top level conflict by beta" << endl;
                    show_result(RetVal::r_unsatisfied);
                    return RetVal::r_completed;
                }                
                decision_level = conflict_analysis_and_backtrack();
            }
            else
            {
                break;
            }
        }
        
    }
    show_result(RetVal::r_satisfied);
    return RetVal::r_completed;
}

// TODO change frequency when learning - seems done
int SATSolverCDCL::conflict_analysis_and_backtrack()
{
    cout << "Number of clauses : " << clause_count << " DLK : " << literal_decision_level[kappa] << endl;
    if(literal_decision_level[kappa] == 0)
    {
        cout << "Kappa decision level is 0" << endl;
        return -1;
    }
    vector<int> learnt_clause = get_learned_clause(literal_decision_level[kappa],literal_antecedent[kappa]);
 //   cout << "Learned clause : " << endl;
    for(int i = 0; i < learnt_clause.size(); i++)
    {
        cout << learnt_clause[i] << " ";
    }
    cout << endl;
    learned_clause_count++;
    literal_list_per_clause.push_back(learnt_clause);
    for(int i = 0; i < learnt_clause.size(); i++)
    {
        int literal = variable_to_literal_index(learnt_clause[i]);
        literal_frequency[literal]++; 
        if(learnt_clause[i] > 0)
        {
            literal_polarity[literal]++;
        }
        else
        {
            literal_polarity[literal]--; 
        }
    }
    clause_count++;
    int backtracked_decision_level = -1;
    for(int i = 0; i < learnt_clause.size(); i++)
    {
        int literal = variable_to_literal_index(learnt_clause[i]);
        if(literal_decision_level[literal] != literal_decision_level[kappa] && literal_decision_level[literal] > backtracked_decision_level)
        {
            backtracked_decision_level = literal_decision_level[literal];
        }
    } 
    cout << "BDL : " << backtracked_decision_level << endl;
    for(int i = 0; i < literals.size(); i++)
    {
        if(literal_decision_level[i] > backtracked_decision_level)
        {
            unassign_literal(i);
        }
    }
    return backtracked_decision_level;
}

void SATSolverCDCL::solve()
{
    CDCL();
}

void SATSolverCDCL::show_result(int result)
{
    if(result == RetVal::r_satisfied) // if the formula is satisfiable
    {
        cout<<"SAT"<<endl;
        for(int i = 0; i < literals.size(); i++)
        {
            if(i != 0)
            {
                cout<<" ";
            }
            if(literals[i] != -1)
            {
                cout<<pow(-1,(literals[i]+1))*(i+1);
            }
            else // for literals which can take either value, arbitrarily assign them to be true
            {
                cout<<(i+1);
            }
        }
    }
    else // if the formula is unsatisfiable
    {
        cout<<"UNSAT";
    }
}

int main()
{
    SATSolverCDCL solver;
    solver.initialize();
    solver.solve();
    return 0;
}
