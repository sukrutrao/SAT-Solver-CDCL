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
        vector< vector<int> > literal_clause_matrix;
        vector< vector<int> > clause_list_per_literal;
        vector< vector<int> > literal_list_per_clause;
        vector<int> clause_reference_first;
        vector<int> clause_reference_second;
        vector<int> clause_states;
        vector<int> literal_antecedent;
        vector<int> literal_decision_level;
        vector< vector<int> > implication_graph;
        int literal_count;
        int original_clause_count;
        int clause_count;
        int learned_clause_count;
        int assigned_literal_count;
        int current_decision_level;
        bool already_unsatisfied;
        int kappa;
        SATSolverCDCL() {}
        void initialize();
        int unit_propagate();
        bool mu0(int,int);
        bool mu1(int,int);
        bool all_variables_assigned();
        int pick_branching_variable();
        bool xi(vector<int>,int,int);
        bool sigma(vector<int>,int);
        vector<int> resolve(vector<int>,int);
        vector<int> get_learned_clause(int);
        int get_decision_level(int);
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
            cin>>s; // this would be cnf
            break;
        }
    }
    cin>>literal_count;
    cin>>original_clause_count;
    clause_count = original_clause_count;
    learned_clause_count = 0;
    assigned_literal_count = 0;
    current_decision_level = -1;
    already_unsatisfied = false;
    kappa = literal_count;
    // set the vectors to their appropriate sizes and initial values
    literals.clear();
    literals.resize(literal_count,-1);
    literal_frequency.clear();
    literal_frequency.resize(literal_count,0);
    literal_polarity.clear();
    literal_polarity.resize(literal_count,0);
    literal_clause_matrix.clear();
    literal_clause_matrix.resize(clause_count,literals);
    clause_list_per_literal.clear();
    clause_list_per_literal.resize(literal_count);
    literal_list_per_clause.clear();
    literal_list_per_clause.resize(clause_count);
    clause_reference_first.clear();
    clause_reference_first.resize(clause_count,0);
    clause_reference_second.clear();
    clause_reference_second.resize(clause_count,1); // take care of empty or unit clauses !!!
    clause_states.clear();
    clause_states.resize(clause_count,CState::unresolved);
    literal_antecedent.clear();
    literal_antecedent.resize(literal_count+1,-1); // for kappa
    literal_decision_level.clear();
    literal_decision_level.resize(literal_count+1,-1); // we will set the decision level of kappa as the level of conflict
    implication_graph.clear();
    implication_graph.resize(literal_count);
    
    int literal; // store the incoming literal value
    int literal_count = 0;
    // iterate over the clauses
    for(int i = 0; i < clause_count; i++)
    {
        literal_count = 0;
        while(true) // while the ith clause gets more literals
        {
            cin>>literal;     
            if(literal > 0) // if the variable has positive polarity
            {
                literal_list_per_clause[i].push_back(2*(literal-1)); // store it in the form 2n
                // increment frequency and polarity of the literal
                literal_frequency[literal-1]++; 
                literal_polarity[literal-1]++;
                clause_list_per_literal[literal-1].push_back(i);
                literal_clause_matrix[i][literal-1] = 0;
            }
            else if(literal < 0) // if the variable has negative polarity
            {
                literal_list_per_clause[i].push_back(2*((-1)*literal-1)+1); // store it in the form 2n+1
                // increment frequency and decrement polarity of the literal
                literal_frequency[-1-literal]++;
                literal_polarity[-1-literal]--;
                clause_list_per_literal[-literal-1].push_back(i);
                literal_clause_matrix[i][-literal-1] = 1;
            }
            else
            {
                if(literal_count == 1)
                {
                    clause_reference_second[i] = 0;
                    clause_states[i] = CState::unit;
                }
                else if(literal_count == 0)
                {
                    already_unsatisfied = true;
                }
                break; // read 0, so move to next clause
            }    
            literal_count++;
        }       
    }
    original_literal_frequency = literal_frequency; // backup for restoring when backtracking
    literal_decision_level[kappa] = -1;
    literal_antecedent[kappa] = -1;
    cout << "Done initializing" << endl;
}

bool SATSolverCDCL::mu0(int literal_index_in_clause, int clause)
{
    int literal_with_polarity = literal_list_per_clause[clause][literal_index_in_clause];
    if(literal_with_polarity%2 == 0 && literals[literal_with_polarity/2] == 0)
    {
        return true;
    }
    if(literal_with_polarity%2 == 1 && literals[literal_with_polarity/2] == 1)
    {
        return true;
    }
    return false;
}

bool SATSolverCDCL::mu1(int literal_index_in_clause, int clause)
{
    int literal_with_polarity = literal_list_per_clause[clause][literal_index_in_clause];
 //   cout << "LWP : " << literal_with_polarity << endl;
    if(literal_with_polarity%2 == 0 && literals[literal_with_polarity/2] == 1)
    {
   //     cout << "First" << endl;
        return true;
    }
    if(literal_with_polarity%2 == 1 && literals[literal_with_polarity/2] == 0)
    {
   //     cout << "Second" << endl;
        return true;
    }
  //  cout << "False" << endl;
    return false;
}

bool SATSolverCDCL::xi(vector<int> clause, int literal, int decision_level)
{
    bool found_flag = false;
    for(int i = 0; i < clause.size(); i++)
    {
        if(clause[i]/2 == literal)
        {
            found_flag = true;
            break;
        }
    }
    if(found_flag && literal_decision_level[literal] == decision_level && literal_antecedent[literal] != -1) // can optimize this by checking other two conditions before the loop
    {
        return true;
    }
    return false;
}

bool SATSolverCDCL::sigma(vector<int> clause, int decision_level)
{
    int level_count = 0;
    for(int i = 0; i < clause.size(); i++)
    {
        if(literal_decision_level[clause[i]/2] == decision_level)
        {
            level_count++;
        }
    }
    if(level_count == 1)
    {
        return true;
    }
    return false;
}

vector<int> SATSolverCDCL::resolve(vector<int> clause, int antecedent_of_l)
{
    vector<int> result = clause;
    vector<int> second = literal_list_per_clause[literal_antecedent[antecedent_of_l]];
    result.insert(result.end(),second.begin(),second.end());
    cout << "Result Initial : " << endl;
    for(int i = 0; i < result.size(); i++)
    {
        cout << result[i] << " ";
    }
    cout << endl;
    int count = 0;
    for(int i = 0; i < result.size(); i++)
    {
        if(result[i]/2 == antecedent_of_l)
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
    cout << "Result Final : " << endl;
    for(int i = 0; i < result.size(); i++)
    {
        cout << result[i] << " ";
    }
    return result;
}

vector<int> SATSolverCDCL::get_learned_clause(int decision_level)
{
    int t = 0;  
 /*   cout << "Learning clause at level : " << decision_level << endl;
    cout << "Decision levels are : ";
    for(int i = 0; i < literal_decision_level.size(); i++)
    {
        cout << literal_decision_level[i] << " ";
    }
    cout << endl;*/
    vector<int> current_clause = literal_list_per_clause[literal_antecedent[kappa]]; // TODO check this exists
    vector<int> next_clause;
    int count = 0;
    do
    {
        count = 0;
 /*       cout << "Current clause : " << endl;
        for(int i = 0; i < current_clause.size(); i++)
        {
            cout << current_clause[i] << " ";
        }
        cout << endl;*/
        if(sigma(current_clause,decision_level))
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
            if(xi(current_clause,current_clause[i]/2,decision_level))
            {
               next_clause = resolve(current_clause,current_clause[i]/2); // TODO unassign and move watched references?
               break;
            }
            else
            {
                count++;
            }
        }
    /*    if(count == current_clause.size())
        {
            return current_clause;
        }*/
        current_clause = next_clause;
        t++;
    }while(true);
}

int SATSolverCDCL::get_decision_level(int literal)
{
    int current_max = 0;
    int antecedent = literal_antecedent[literal];
    if(antecedent == -1)
    {
        return current_max;
    }
    for(int i = 0; i < literal_list_per_clause[antecedent].size(); i++)
    {
        if(literal_list_per_clause[antecedent][i]/2 != literal && literal_decision_level[literal_list_per_clause[antecedent][i]/2] > current_max)
        {
            current_max = literal_decision_level[literal_list_per_clause[antecedent][i]/2];
        }
    }
    return current_max;
}

void SATSolverCDCL::assign_literal(int literal, int decision_level, int antecedent)
{
    literals[literal/2] = (literal%2+1)%2;
    literal_decision_level[literal/2] = decision_level;
    literal_antecedent[literal/2] = antecedent;
    literal_frequency[literal/2] = -1;
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
    if(literal_frequency[variable]<0)
    {
        cout << "LT0!!!!!!!!!!!!" << endl;
        exit(0);
    }
    if(literal_polarity[variable] >= 0)
    {
        cout << "Picked " << 2*variable << endl;
        return 2*variable;
    }
    cout << "Picked " << 2*variable+1 << endl;
    return 2*variable+1;
}

int SATSolverCDCL::unit_propagate()
{
    bool unit_clause_found = false;
 /*   cout << "State at start of unit propagation : " << endl;
    cout << "Literals : " << endl;
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
      /*          cout << "Found a unit clause : " << i << " clause count : " << clause_count << endl;
                cout << "Literals : " << endl;
                for(int i = 0; i < literals.size(); i++)
                {
                    cout << literals[i] << " ";
                }
                cout << endl;*/
                for(int j = 0; j < literal_list_per_clause[i].size(); j++)
                {
                    if(literals[literal_list_per_clause[i][j]/2] == -1) // unassigned variable found
                    {
                //        cout << "Literal found is : " << literal_list_per_clause[i][j]/2 << endl;
                        int literal_here = literal_list_per_clause[i][j]/2; // variable index
                        literal_antecedent[literal_here] = i; // antecedent is this clause
                        literal_decision_level[literal_here] = current_decision_level; //get_decision_level(literal_here); //TODO or current_decision_level? // find decision level
                        // graph edges ??? TODO
                        if(literal_list_per_clause[i][j]%2 == 0) // if positive polarity
                        {
                            literals[literal_here] = 1; // assign positive
                        }
                        else 
                        {
                            literals[literal_here] = 0; // assign negative
                        }
                        literal_frequency[literal_here] = -1;
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
      /*          for(int i = 0; i < literals.size(); i++)
                {
                    cout << literals[i] << " " << "DL " << literal_decision_level[i] << endl;
                }
                cout << endl;*/
                literal_antecedent[kappa] = i;
                literal_decision_level[kappa] = current_decision_level; //? TODO check!
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
    for(int i = 0; i < literal_list_per_clause[clause].size(); i++)
    {
        if(mu0(i,clause))
        {
            false_count++;
        }
        else if(literals[literal_list_per_clause[clause][i]/2] == -1)
        {
            unset_count++;
        }
        else if(mu1(i,clause))
        {
            return CState::satisfied;
        }
    }
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
 /*   if(already_unsatisfied)
    {
        show_result(RetVal::r_unsatisfied);
        return RetVal::r_completed;
    } */
    if(unit_propagate() == RetVal::r_unsatisfied)
    {
        show_result(RetVal::r_unsatisfied);
        return RetVal::r_completed;
    }
    current_decision_level = 0;
    while(!all_variables_assigned())
    {  
   //     cout << "#####################################################################################" << endl;  
  /*      for(int i = 0; i < clause_count; i++)
        {
            if(get_clause_state(i) == CState::unit)
            {
                cout << "Unit clause found : " << i << endl;
                for(int c = 0; c < literal_list_per_clause[i].size(); c++)
                {
                    cout << literal_list_per_clause[i][c] << " ";
                }
                cout << endl;
                exit(0);
            }
        }   */  
        int current_literal = pick_branching_variable();
        current_decision_level++;
      /*  literals[current_literal/2] = (current_literal%2+1)%2;
        literal_decision_level[current_literal/2] = current_decision_level;
        literal_antecedent[current_literal/2] = -1;
        literal_frequency[current_literal/2] = -1;
        assigned_literal_count++;*/
        assign_literal(current_literal,current_decision_level,-1);
        while(true)
        {
            if(unit_propagate() == RetVal::r_unsatisfied)
            {
                int beta = conflict_analysis_and_backtrack();
                cout << "Beta : " << beta << endl;
                if(beta < 0)
                {
                    cout << "Got top level conflict by beta" << endl;
                    show_result(RetVal::r_unsatisfied);
                    return RetVal::r_completed;
                }
                current_decision_level = beta;
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
    vector<int> learnt_clause = get_learned_clause(literal_decision_level[kappa]);
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
        literal_frequency[learnt_clause[i]/2]++; 
        if(learnt_clause[i]%2 == 0)
        {
            literal_polarity[learnt_clause[i]/2]++;
        }
        else
        {
            literal_polarity[learnt_clause[i]/2]--; 
        }
        clause_list_per_literal[learnt_clause[i]/2].push_back(clause_count);
    }
    clause_count++;
    int backtracked_decision_level = 0;
    if(learnt_clause.size() > 1)
    {
       for(int i = 0; i < learnt_clause.size(); i++)
        {
            if(literal_decision_level[learnt_clause[i]/2] != literal_decision_level[kappa] && literal_decision_level[learnt_clause[i]/2] > backtracked_decision_level)
            {
                backtracked_decision_level = literal_decision_level[learnt_clause[i]/2];
            }
        } 
    }
    else
    {
        if(literal_decision_level[learnt_clause[0]/2] == 0)
        {
            return -1;
        }
        else
        {
            backtracked_decision_level = 0;
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
    
 /*   if(unit_propagate() == RetVal::r_unsatisfied)
    {
        
        cout << "Got conflict again in backtrack" << endl;
   //     return -1;
        return conflict_analysis_and_backtrack();
    }
    cout << "Returning backtracked decision level" << backtracked_decision_level << endl; */
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
