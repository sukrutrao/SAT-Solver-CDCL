/* mu_x = 0, u, 1 - one for each variable
l^mu - one for each variable, omega^mu - one per clause, phi^mu - for whole formula
clause states - satisfied, unsatisfied, unit, unresolved
alpha_x - antecedent - any clause or NIL, delta_x - decision level - -1,0,1,..,size of X
lambda - first arg variable is present in second arg clause
mu_0 - literal z false in w
mu_1 - literal z true in w
edge between z1 and z2 - between every variable in antecedent of kappa and kappa
if z1 literal is 0 in antecedent of z2 and z2 literal is 1 in antecedent of z2
iota of z1 and z2 - antecedent of z2, when there is an edge between z1 and z2

*/

// vector containing literals and their assignments - three possible assignments
// linked list referncing to each clause for every literal 
// every clause contains reference of assignment of every literal it contains, and two pointers for pointing to watched literals - also contains clause state - one out of 4?
// every literal contains an antecedent and decision level 

// Idea - redundant matrix of clause x variable to quickly check if a variable is in a clause and with what polarity

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
        bool lambda(int,int);
        bool mu0(int,int);
        bool mu1(int,int);
        bool all_variables_assigned();
        int pick_branching_variable();
        bool epsilon(int,int);
        bool xi(vector<int>,int,int);
        vector<int> resolve(vector<int>,int);
        vector<int> get_learned_clause(int);
        int get_decision_level(int);
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
    cout << "Done initializing" << endl;
}

bool SATSolverCDCL::lambda(int literal, int clause)
{
    if(literal_clause_matrix[clause][literal] != -1)
    {
        return true;
    }
    return false;
}

bool SATSolverCDCL::mu0(int literal, int clause)
{
    if(literal_clause_matrix[clause][literal] == 0 && literals[literal] == 0)
    {
        return true;
    }
    if(literal_clause_matrix[clause][literal] == 1 && literals[literal] == 1)
    {
        return true;
    }
    return false;
}

bool SATSolverCDCL::mu1(int literal, int clause)
{
 //   cout << "In mu1" << endl;
    if(literal_clause_matrix[clause][literal] == 0 && literals[literal] == 1)
    {
  //      cout << "In if" << endl;
        return true;
    }
    if(literal_clause_matrix[clause][literal] == 1 && literals[literal] == 0)
    {
        return true;
    }
 //   cout << "Returning from mu1" << endl;
    return false;
}

bool SATSolverCDCL::epsilon(int z1, int z2)
{
    if(z2 == kappa && lambda(z1,literal_antecedent[kappa]))
    {
        return true;
    }
    if(z2 != kappa)
    {
        int omega = literal_antecedent[z2];
        if(mu0(z1,omega) && mu1(z2,omega))
        {
            return true;
        }
    }
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
    if(found_flag && literal_decision_level[literal] == decision_level && literal_antecedent[literal] != -1)
    {
        return true;
    }
    return false;
}

vector<int> SATSolverCDCL::resolve(vector<int> clause, int antecedent_of_l)
{
    vector<int> first = clause;
    vector<int> second = literal_list_per_clause[literal_antecedent[antecedent_of_l]];
    vector<int> result;
    result.clear();
    result.insert(result.end(),first.begin(),first.end());
    result.insert(result.end(),second.begin(),second.end());
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
    if(count != 2)
    {
        cout<<"Error!"<<endl;
    }
    unassign_literal(antecedent_of_l);
    return result;
}

vector<int> SATSolverCDCL::get_learned_clause(int decision_level)
{
    vector<int> current_clause = literal_list_per_clause[literal_antecedent[kappa]]; // TODO check this exists
    vector<int> next_clause;
    int count = 0;
    do
    {
        count = 0;
        for(int i = 0; i < current_clause.size(); i++)
        {
            if(xi(current_clause,current_clause[i],decision_level))
            {
               next_clause = resolve(current_clause,current_clause[i]); // TODO unassign and move watched references?
               break;
            }
            else
            {
                count++;
            }
        }
        if(count == current_clause.size())
        {
            return current_clause;
        }
        current_clause = next_clause;
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
        if(literal_list_per_clause[antecedent][i] != literal && literal_decision_level[i] > current_max)
        {
            current_max = literal_decision_level[i];
        }
    }
    return current_max;
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
    bool restart_unit_search = true;
    cout << "State at start of unit propagation : " << endl;
    cout << "Literals : " << endl;
    for(int i = 0; i < literals.size(); i++)
    {
        cout << literals[i] << " ";
    }
    cout << endl;
    do 
    {
        unit_clause_found = false;
        restart_unit_search = false;
        for(int i = 0; i < clause_count && !restart_unit_search; i++)
        {
 //           cout << "In for UP" << endl;
            if(get_clause_state(i) == CState::unit) // if a unit clause is found
            {
                unit_clause_found = true;
    //            cout << "Found a unit clause" << endl;
                for(int j = 0; j < literal_list_per_clause[i].size(); j++)
                {
                    if(literals[literal_list_per_clause[i][j]/2] == -1) // unassigned variable found
                    {
                        cout << "Literal found is : " << literals[literal_list_per_clause[i][j]/2] << endl;
                        int literal_here = literal_list_per_clause[i][j]/2; // variable index
                        literal_antecedent[literal_here] = i; // antecedent is this clause
                        literal_decision_level[literal_here] = get_decision_level(literal_here); // find decision level
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
        //                cout << "Applying transform" << endl;
                        int result_transform = apply_transform(literal_here); // apply transform
                        if(result_transform == RetVal::r_satisfied || result_transform == RetVal::r_unsatisfied)
                        {
                            return result_transform;
                        }
                        restart_unit_search = true;
                        break;
                    }
                }
            }
            else if(get_clause_state(i) == CState::unsatisfied)
            {
                // TODO declare conflict?
                return RetVal::r_unsatisfied;
            }
      //      cout << "At end" << endl;
        }    
    }while(unit_clause_found);
    return RetVal::r_normal;
}

// TODO - with watched literals, clauses_states make no sense - DONE

int SATSolverCDCL::apply_transform(int literal_to_apply)
{
    int value_to_apply = literals[literal_to_apply];
 //   cout << "AppT : " << "LTA : " << literal_to_apply << " VTA : " << value_to_apply << " S : " << clause_list_per_literal[literal_to_apply].size() << endl;
    for(int i = 0; i < clause_list_per_literal[literal_to_apply].size(); i++)
    {
  //      cout << "In for" << endl;
        int clause = clause_list_per_literal[literal_to_apply][i];
        int first_ref = clause_reference_first[clause];
        int second_ref = clause_reference_second[clause];
        int used_ref = -1;
        int other_ref = -1;
        if(literal_list_per_clause[clause][first_ref]/2 == literal_to_apply)
        {
            used_ref = first_ref;
            other_ref = second_ref;
        }
        else if(literal_list_per_clause[clause][second_ref]/2 == literal_to_apply)
        {
            used_ref = second_ref;
            other_ref = first_ref;
        }
        if(used_ref == -1)
        {
            continue;
        }
        if(mu0(literal_to_apply,clause))
        {
                        
        }
    }
//    cout << "Returning from AppT" << endl;
    return RetVal::r_normal;
}

int SATSolverCDCL::get_clause_state(int clause)
{
 //   cout << "Entered gcs" << endl;
    int first_ref = literal_list_per_clause[clause][clause_reference_first[clause]];
    int second_ref = literal_list_per_clause[clause][clause_reference_second[clause]];
 //   cout << "Before mu1" << endl;
    if(mu1(first_ref,clause) || mu1(second_ref,clause)) // TODO check if correct condition
    {
 //       cout << "In if in gcs" << endl;       
        return CState::satisfied;
    }
    int false_count = 0;
    int unset_count = 0;
//    cout << "Before for" << endl;
    for(int i = 0; i < literal_list_per_clause[clause].size(); i++)
    {
        if(literals[literal_list_per_clause[clause][i]] == 0)
        {
            false_count++;
        }
        else if(literals[literal_list_per_clause[clause][i]] == -1)
        {
            unset_count++;
        }
    }
 //   cout << "After for" << endl;
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
 //   cout << "Enter CDCL()" << endl;
    if(already_unsatisfied)
    {
        show_result(RetVal::r_unsatisfied);
        return RetVal::r_completed;
    }
    if(unit_propagate() == RetVal::r_unsatisfied)
    {
        show_result(RetVal::r_unsatisfied);
        return RetVal::r_completed;
    }
    current_decision_level = 0;
 //   cout << "Entering while" << endl;
    while(!all_variables_assigned())
    {  
        int current_literal = pick_branching_variable();
        current_decision_level++;
        // TODO assign and also set decision level, maybe antecedent
        literals[current_literal/2] = (current_literal%2+1)%2;
        literal_decision_level[current_literal/2] = current_decision_level;
        literal_antecedent[current_literal/2] = -1;
        literal_frequency[current_literal/2] = -1;
        assigned_literal_count++;
        if(unit_propagate() == RetVal::r_unsatisfied)
        {
            int beta = conflict_analysis_and_backtrack();
            if(beta < 0)
            {
                show_result(RetVal::r_unsatisfied);
                return RetVal::r_completed;
            }
      //      backtrack(beta);
            current_decision_level = beta;
        }
    }
    show_result(RetVal::r_satisfied);
    return RetVal::r_completed;
}

int SATSolverCDCL::conflict_analysis_and_backtrack()
{
    if(literal_decision_level[kappa] == 0)
    {
        return -1;
    }
    vector<int> learnt_clause = get_learned_clause(literal_decision_level[kappa]);
    learned_clause_count++;
    literal_list_per_clause.push_back(learnt_clause);
    vector<int> literal_clause_matrix_row(literal_count,-1);
    for(int i = 0; i < learnt_clause.size(); i++)
    {
        if(learnt_clause[i]%2 == 0)
        {
            literal_clause_matrix_row[learnt_clause[i]/2] = 0;  
        }
        else
        {
            literal_clause_matrix_row[learnt_clause[i]/2] = 1;  
        }
        clause_list_per_literal[learnt_clause[i]/2].push_back(clause_count);
    }
    literal_clause_matrix.push_back(literal_clause_matrix_row);
    clause_count++;
    return literal_decision_level[kappa]-1;
}

void SATSolverCDCL::solve()
{
  //  cout << "Start solve()" << endl;
    CDCL();
 //   cout << "End solve()" << endl;
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
                cout<<pow(-1,literals[i])*(i+1);
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
