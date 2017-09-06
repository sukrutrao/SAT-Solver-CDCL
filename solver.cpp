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
    satisfied,
    unsatisfied,
    normal,
    completed
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
    literal_decision_level.resize(literal_count,-1);
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
                    clauses_reference_second[i] = 0;
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
    if(literal_clause_matrix[clause][literal] == 0 && literals[literal] == 1)
    {
        return true;
    }
    if(literal_clause_matrix[clause][literal] == 1 && literals[literal] == 0)
    {
        return true;
    }
    return false;
}

bool SATSolverCDCL::epsilon(int z1, int z2)
{
    if(z2 == kappa && lambda(z1,literal_antecedent(kappa)))
    {
        return true;
    }
    if(z2 != kappa)
    {
        int omega = literal_antecedent(z2);
        if(mu0(z1,omega) && mu1(z2,omega))
        {
            return true;
        }
    }
    return false;
}

int SATSolverCDCL::decision_level(int literal)
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

bool SATSolverCDCL::all_variables_assigned()
{
    return assigned_literal_count == literal_count;
}

int SATSolverCDCL::pick_branching_variable()
{
    int variable = distance(literal_frequency.begin(),max_element(literal_frequency.begin(),literal_frequency.end()));
    if(literal_polarity[variable] >= 0)
    {
        return 2*variable;
    }
    return 2*variable+1;
}

int SATSolverCDCL::unit_propagate()
{
    for(int i = 0; i < clause_count; i++)
    {
        if(clause_states[i] == CState::unit)
        {
            for(int j = 0; j < literal_list_per_clause[i].size(); j++)
            {
                if(literals[literal_list_per_clause[i][j]/2] == -1)
                {
                    int literal_here = literal_list_per_clause[i][j]/2;
                    literal_antecedent[literal_here] = i;
                    literal_decision_level[literal_here] = decision_level(literal_here);
                    if(literal_list_per_clause[i][j]%2 == 0)
                    {
                        
                    }
                }
            }
        }
    }
}

int SATSolverCDCL::apply_transform(int literal_to_apply)
{
    
}

int SATSolverCDCL::CDCL()
{
    if(already_unsatisfied)
    {
        show_result(RetVal::unsatisfied);
        return RetVal::completed;
    }
    if(unit_propagate() == RetVal::unsatisfied)
    {
        show_result(RetVal::unsatisfied);
        return RetVal::completed;
    }
    current_decision_level = 0;
    while(!all_variables_assigned())
    {
        int current_literal = pick_branching_variable;
        current_decision_level++;
        // assign and also set decision level, maybe antecedent
        if(unit_propagate() == RetVal::unsatisfied)
        {
            int beta = conflict_analysis();
            if(beta < 0)
            {
                show_result(RetVal::unsatisfied);
                return RetVal::completed;
            }
            backtrack(beta);
            current_decision_level = beta;
        }
    }
    show_result(RetVal::satisfied);
    return RetVal::completed;
}

void SATSolverCDCL::show_result(int result)
{
    if(result == RetVal::satisfied) // if the formula is satisfiable
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
                cout<<pow(-1,f.literals[i])*(i+1);
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


