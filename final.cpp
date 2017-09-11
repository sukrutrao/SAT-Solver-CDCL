/*
 * Program to implement a SAT solver based on Conflict Driven Clause Learning with non-chronological backtracking
 * Sukrut Rao
 * CS15BTECH11036
 */

#include <iostream>
#include <algorithm>
#include <vector>
#include <cmath>
#include <random>

using namespace std;

/*
 * enum to store exit states for certain functions in the solver
 */
enum RetVal
{
    r_satisfied, // the formula has been satisfied
    r_unsatisfied, // the formula has been unsatisfied
    r_normal // the formula is unresolved so far
};

/*
 * class containing the member variables and functions of the CDCL SAT solver
 */
class SATSolverCDCL
{
    private:
        /*
         * a vector to store the state of each variable, where the assignment is as 
         * 1 - assigned true
         * 0 - assigned false
         * -1 - unassigned
         */
        vector<int> literals;
        
        /*
         * a 2D vector that stores a list of literals for every clause
         * for the one indexed variable l, l is stored when it is present with positive polarity
         * and -l is stored when it is present with negative polarity
         */
        vector< vector<int> > literal_list_per_clause;
        
        /*
         * vector that stores the total number of occurrences of the variable in the formula
         * this is updated when clauses are learnt
         * this is used for choosing the next variable to be assigned
         */
        vector<int> literal_frequency;
        
        /*
         * vector that stores the difference in the number of positive and negative occurrences
         * of the variable in the formula. this is updated when clauses are learnt
         */
        vector<int> literal_polarity;
        
        /*
         * vector to store backup of the frequencies, as the original will be set to -1 when
         * the variable is assigned. this is use to reset the value back to the original if and when the
         * variable is later unassigned
         */
        vector<int> original_literal_frequency;
        int literal_count; // number of variables in the formula
        int clause_count; // number of clauses in the formula
        int kappa_antecedent; // antecedent of the conflict, kappa 
        
        /*
         * vector to store the decision level of each variable
         * when not yet assigned, it contains -1
         */
        vector<int> literal_decision_level;
        
        /*
         * vector to store the antecedent of each variable
         * NIL is represented by -1
         */
        vector<int> literal_antecedent;
        int assigned_literal_count; // the number of variables assigned so far
        bool already_unsatisfied; // if the formula contains any empty clause originally
        int pick_counter; // the number of times we have chosen a variable freely based on frequency
        random_device random_generator;
        mt19937 generator;
        
        int unit_propagate(int); // to perform unit propagation 
        // to assign a literal with given value, antecedent and decision level
        void assign_literal(int,int,int);
        void unassign_literal(int); // to unassign a given literal
         // to convert the one indexed literal with sign to zero indexed without sign
        int literal_to_variable_index(int);
        int conflict_analysis_and_backtrack(int); // to perform conflict analysis and backtrack
        vector<int>& resolve(vector<int>&,int); // to resolve two clauses and get the result
        int pick_branching_variable(); // to pick the next free assignment
        bool all_variables_assigned(); // to check if all variables have already been assigned
        void show_result(int); // to display the result of the solver
        
    public:
        SATSolverCDCL() : generator(random_generator()) {} // constructor
        void initialize(); // to initialize the solver
        int CDCL(); // to perform the CDCL algorithm and return the appropriate result state
        void solve(); // to solve the problem and display the result
};

/*
 * function to initialize the solver
 */
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
    cin >> literal_count;
    cin >> clause_count;
    assigned_literal_count = 0; // no literals assigned so far
    // set the default values
    kappa_antecedent = -1;
    pick_counter = 0;
    already_unsatisfied = false;
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
    literal_antecedent.resize(literal_count,-1);
    literal_decision_level.clear();
    literal_decision_level.resize(literal_count,-1);
    
    int literal; // store the incoming literal value
    int literal_count_in_clause = 0; // number of literals in the incoming clause
    // iterate over the clauses
    for(int i = 0; i < clause_count; i++)
    {
        literal_count_in_clause = 0;
        while(true) // while the ith clause gets more literals
        {
            cin>>literal;     
            if(literal > 0) // if the variable has positive polarity
            {
                literal_list_per_clause[i].push_back(literal); // store it
                // increment frequency and polarity of the literal
                literal_frequency[literal-1]++; 
                literal_polarity[literal-1]++;
            }
            else if(literal < 0) // if the variable has negative polarity
            {
                literal_list_per_clause[i].push_back(literal); // store it
                // increment frequency and decrement polarity of the literal
                literal_frequency[-1-literal]++;
                literal_polarity[-1-literal]--;
            }
            else
            {
                if(literal_count_in_clause == 0) // if any clause is empty, we can stop
                {
                    already_unsatisfied = true;
                }
                break; // read 0, so move to next clause
            }    
            literal_count_in_clause++;
        }       
    }
    original_literal_frequency = literal_frequency; // backup for restoring when backtracking
}

/*
 * function to implement the Conflict Driven Clause Learning algorithm
 * Return value : the return status, which is
 *                RetVal::r_satisfied if the formula is satisfiable
 *                RetVal::r_unsatisfied if the formula is not satisfiable
 */
int SATSolverCDCL::CDCL()
{
    int decision_level = 0; // initial decision level
    if(already_unsatisfied) // if we had found an empty clause, we know that it is unsatisfiable
    {
        return RetVal::r_unsatisfied;
    }
    // initial unit propagation to find existing top level conflicts
    int unit_propagate_result = unit_propagate(decision_level);
    if(unit_propagate_result == RetVal::r_unsatisfied)
    {
        return unit_propagate_result;
    }
    while(!all_variables_assigned())
    {
        int picked_variable = pick_branching_variable(); // pick the next free variable with assignment
        decision_level++; // increment the current decision level
        // assign the variable at the current decision level with no antecedent
        assign_literal(picked_variable,decision_level,-1);
        /*
         * unit propagate and backtrack repeatedly till no conflicts are left or 
         * we found that the formula is unsatisfiable
         */ 
        while(true)
        {
            unit_propagate_result = unit_propagate(decision_level);
            if(unit_propagate_result == RetVal::r_unsatisfied)
            {
                // if the conflict was at the top level, the formula is unsatisfiable
                if(decision_level == 0)
                {
                    return unit_propagate_result;
                }
                /*
                 * if not, perform the conflict analysis, learn clauses, and backtrack
                 * to a previous decision level
                 */
                decision_level = conflict_analysis_and_backtrack(decision_level);
            }
            else // if unit propagation gave no conflicts, continue choosing another free assignment
            {
                break;
            }
        }
    }
    // if we reached here, all variables were successfully assigned, and the formula is satisfiable
    return RetVal::r_satisfied;    
}

/*
 * function to perform unit propagation on the formula
 * Arguments : decision_level - the current decision level at which unit propagation is taking place
 * Return value : Return state denoting the status, where
 *                RetVal::r_normal - unit propagation ended successfully with no conflicts
 *                RetVal::r_unsatisfied - unit propagation found a conflict
 */
int SATSolverCDCL::unit_propagate(int decision_level)
{
    bool unit_clause_found = false; // if a unit clause has been found
    int false_count = 0; // number of false literals in the clause
    int unset_count = 0; // number of unset literals in the clause
    int literal_index;
    bool satisfied_flag = false; // if the clause is satisfied due to the presence of a true literal
    int last_unset_literal = -1; // index of an unset literal
    do 
    {
        unit_clause_found = false;
        // iterate over all clauses if no unit clause has been found so far
        for(int i = 0; i < literal_list_per_clause.size() && !unit_clause_found; i++)
        {
            false_count = 0;
            unset_count = 0;
            satisfied_flag = false;
            // iterate over all literals
            for(int j = 0; j < literal_list_per_clause[i].size(); j++)
            {
                // get the vector index of the literal
                literal_index = literal_to_variable_index(literal_list_per_clause[i][j]);
                if(literals[literal_index] == -1) // if unassigned
                {
                    unset_count++;
                    last_unset_literal = j; // store the index, may be needed later
                }
                else if((literals[literal_index] == 0 && literal_list_per_clause[i][j] > 0) || (literals[literal_index] == 1 && literal_list_per_clause[i][j] < 0)) // if false in the clause
                {
                    false_count++;
                }
                else // if true in the clause, so the clause is satisfied
                {
                    satisfied_flag = true;
                    break;
                }
            }
            if(satisfied_flag) // if the clause is satisfied, move to the next
            {
                continue;
            }          
            // if exactly one literal is unset, this clause is unit 
            if(unset_count == 1)
            {
                // assign the unset literal at this decision level and this clause i as the antecedent
                assign_literal(literal_list_per_clause[i][last_unset_literal],decision_level,i);
                unit_clause_found = true; // we have found a unit clause, so restart iteratin
                break;
            }
            // if the clause is unsatisfied
            else if(false_count == literal_list_per_clause[i].size())
            {
                // unsatisfied clause
                kappa_antecedent = i; // set the antecedent of kappa to this clause
                return RetVal::r_unsatisfied; // return a conflict status
            }
        }        
    }
    while(unit_clause_found); // if a unit clause was found, we restart iterating over the clauses
    kappa_antecedent = -1;
    return RetVal::r_normal; // return normally
}

/*
 * function to assign a value, decision level, and antecedent to a variable
 * Arguments : variable - the one indexed signed form of the variable, where the sign tells the direction
 *                        of assignment
 *             decision_level - the decision level to assign at
 *             antecedent - the antecedent of the assignment
 */
void SATSolverCDCL::assign_literal(int variable, int decision_level, int antecedent)
{
    int literal = literal_to_variable_index(variable); // get the index
    int value = (variable > 0) ? 1 : 0; // choose the assignment based on sign
    literals[literal] = value; // assign
    literal_decision_level[literal] = decision_level; // set decision level
    literal_antecedent[literal] = antecedent; // set antecedent
    literal_frequency[literal] = -1; // unset frequency so this is not chosen for assignment again
    assigned_literal_count++; // increment the count of number of variables assigned
}

/*
 * function to unassign a variable
 * Arguments : literal_index - the index of the variable to unassign
 */
void SATSolverCDCL::unassign_literal(int literal_index)
{
    literals[literal_index] = -1; // unassign value
    literal_decision_level[literal_index] = -1; // unassign decision level
    literal_antecedent[literal_index] = -1; // unassign antecedent
    literal_frequency[literal_index] = original_literal_frequency[literal_index]; // restore frequency count
    assigned_literal_count--; // decrement the count of the number of variables assigned
}

/*
 * function to convert the one indexed signed form of the literal to the zero indexed vector index
 * Arguments : variable - the one indexed signed form
 * Return value : the zero indexed vector index
 */
int SATSolverCDCL::literal_to_variable_index(int variable)
{
    return (variable > 0) ? variable-1 : -variable-1;    
}

/*
 * function to perform conflict analysis and backtrack
 * Arguments : decision_level - the decision level of the conflict
 * Return value : the backtracked decision level
 */
int SATSolverCDCL::conflict_analysis_and_backtrack(int decision_level)
{
    // the new clause to learn, initialized with the antecedent of the conflict
    vector<int> learnt_clause = literal_list_per_clause[kappa_antecedent];
    int conflict_decision_level = decision_level;
    int this_level_count = 0; // number of literals from the same decision level found
    int resolver_literal; // literal whose antecedent will next be used to resolve
    int literal; // to store the index
    do
    {
        this_level_count = 0;
        // iterate over all literals
        for(int i = 0; i < learnt_clause.size(); i++)
        {
            literal = literal_to_variable_index(learnt_clause[i]); // get the index
            // if a literal at the same decision level has been found
            if(literal_decision_level[literal] == conflict_decision_level)
            {
                this_level_count++;
            }
            // if a literal at the same decision level has been found with an antecedent
            if(literal_decision_level[literal] == conflict_decision_level && literal_antecedent[literal] != -1)
            {
                // the antecedent could be used to resolve if a UIP has not been found
                resolver_literal = literal;
            }
        }
        // exactly one literal at the same decision level means we have a UIP
        if(this_level_count == 1)
        {
            break;
        }
        // otherwise resolve with the antecedent of the candidate resolver literal
        learnt_clause = resolve(learnt_clause,resolver_literal);
    }
    while(true);
    literal_list_per_clause.push_back(learnt_clause); // add the learnt clause to the list
    // update the polarities and frequencies from the learnt clause
    for(int i = 0; i < learnt_clause.size(); i++)
    {
        int literal_index = literal_to_variable_index(learnt_clause[i]);
        int update = (learnt_clause[i] > 0) ? 1 : -1;
        literal_polarity[literal_index] += update;
         // update frequency only if it is not currently assigned, else only update the backup
        if(literal_frequency[literal_index] != -1)
        {
            literal_frequency[literal_index]++;
        }
        original_literal_frequency[literal_index]++;        
    }
    clause_count++; // increment the clause count
    int backtracked_decision_level = 0; // decision level to backtrack to
    for(int i = 0; i < learnt_clause.size(); i++)
    {
        int literal_index = literal_to_variable_index(learnt_clause[i]);
        int decision_level_here = literal_decision_level[literal_index];
        // find the maximum decision level in the clause other than the conflict decision level
        if(decision_level_here != conflict_decision_level && decision_level_here > backtracked_decision_level)
        {
            backtracked_decision_level = decision_level_here;
        }
    }
    for(int i = 0; i < literals.size(); i++)
    {
        if(literal_decision_level[i] > backtracked_decision_level)
        {
            unassign_literal(i); // unassign all literals above the level we backtrack to
        }
    }
    return backtracked_decision_level; // return the level we are at now
}

/*
 * function to resolve a clause with the antecedent of a literal and return the result
 * Arguments : input_clause - the existing clause
 *             literal - the literal whose antecedent must be resolved with
 * Return value : the resultant clause
 */
vector<int>& SATSolverCDCL::resolve(vector<int> &input_clause, int literal)
{
    // get the second clause
    vector<int> second_input = literal_list_per_clause[literal_antecedent[literal]];
    // concatenate the two
    input_clause.insert(input_clause.end(),second_input.begin(),second_input.end());
    for(int i = 0; i < input_clause.size(); i++)
    {
         // remove the literal from the concatenated version
        if(input_clause[i] == literal+1 || input_clause[i] == -literal-1)
        {
            input_clause.erase(input_clause.begin()+i);
            i--;
        }
    }
    // remove duplicates from the result
    sort(input_clause.begin(),input_clause.end());
    input_clause.erase(unique(input_clause.begin(),input_clause.end()),input_clause.end());
    return input_clause; // return the result
}

/*
 * function to pick a variable and an assignment to be assigned freely next
 * Return value : the one indexed signed form of the variable where the sign denotes the direction
 *                of the assignment
 */
int SATSolverCDCL::pick_branching_variable()
{
    // to generate a random integer between 1 and 10, for deciding the mechanism of choosing
    uniform_int_distribution<int> choose_branch(1,10);
    // to generate a random integer corrsponding to the index of one of the literals
    uniform_int_distribution<int> choose_literal(0,literal_count-1);
    int random_value = choose_branch(generator); // get the value to choose the branch
     // if we have spent too long trying to randomly find an unassigned variable
    bool too_many_attempts = false;
    // number of attempts to find an unassigned variable randomly so far
    int attempt_counter = 0;
    do 
    {
         /*
         * for 60% of the time or when less than half the literals have been assigned
         * choose the literal with the highest frequency
         */
        if(random_value > 4 || assigned_literal_count < literal_count/2 || too_many_attempts)
        {
            pick_counter++; // increment the number of picks so far this way
            /*
             * if we reached 20 times the literal count, divide all frequencies by 2
             * this favours frequencies from recently learnt clauses
             */ 
            if(pick_counter == 20*literal_count)
            {
                for(int i = 0; i < literals.size(); i++)
                {
                    original_literal_frequency[i] /= 2;
                    if(literal_frequency[i] != -1)
                    {
                        literal_frequency[i] /= 2;
                    }
                }
                pick_counter = 0; // reset pick counter
            }
            // find the variable with the highest frequency out of those unassigned
            int variable = distance(literal_frequency.begin(),max_element(literal_frequency.begin(),literal_frequency.end()));
            // choose assignment based on which polarity is greater
            if(literal_polarity[variable] >= 0)
            {
                return variable+1;
            }
            return -variable-1; 
        }
        else // we pick the variable randomly
        {
            /*
             * we try up to 10 times the number of literals to get an unassigned variable
             * if we don't, we go back and choose the one with the highest frequency
             */
            while(attempt_counter < 10*literal_count)
            {
                int variable = choose_literal(generator); // pick a random variable
                if(literal_frequency[variable] != -1) // if unassigned
                {
                    // choose the assignment with the higher frequency
                    if(literal_polarity[variable] >= 0)
                    {
                        return variable+1;
                    }
                    return -variable-1; 
                }
                attempt_counter++; // increment the number of attempts if we could not find yet
            }
            too_many_attempts = true; // we have attempted too many times
        }
    }
    while(too_many_attempts); // if we have attempted too many times, go back to the first branch
}

/*
 * function to check if all variables have been assigned so far
 * Return value : true, if yes, false, if no
 */
bool SATSolverCDCL::all_variables_assigned()
{
    return literal_count == assigned_literal_count;
}

/*
 * function to display the result of the solver
 * Arguments : result_status - the status that CDCL returned
 */
void SATSolverCDCL::show_result(int result_status)
{
    if(result_status == RetVal::r_satisfied) // if the formula is satisfiable
    {
        cout << "SAT" << endl;
        for(int i = 0; i < literals.size(); i++)
        {
            if(i != 0)
            {
                cout << " ";
            }
            if(literals[i] != -1)
            {
                cout << pow(-1,(literals[i]+1))*(i+1);
            }
            else // for literals which can take either value, arbitrarily assign them to be true
            {
                cout << (i+1);
            }
        }
    }
    else // if the formula is unsatisfiable
    {
        cout << "UNSAT";
    }
}

/*
 * function to solve the problem by calling the CDCL() function and then showing the result
 */
void SATSolverCDCL::solve()
{
    int result_status = CDCL();
    show_result(result_status);
}

/*
 * the main() function
 */
int main()
{
    SATSolverCDCL solver;
    solver.initialize();
    solver.solve();
    return 0;
}
