#include "cadicallean.hpp"
#include <iostream>
#include <cassert>
#include <cstdlib>
#include <sstream>

CadicalLean::CadicalLean(CaDiCaL::Solver * s, int order, int edge_bound, const std::string& edge_counter_path,
                         int degree_bound, const std::string& degree_counter_path) 
    : solver(s), 
      n(order), 
      num_edge_vars(n * (n - 1) / 2),
      assign(new int[n * (n - 1) / 2]),
      fixed(new bool[n * (n - 1) / 2]),
      edge_bound(edge_bound), 
      edge_counter_path(edge_counter_path),
      degree_bound(degree_bound),
      degree_counter_path(degree_counter_path),
      sol_count(0) {
    
    solver->connect_external_propagator(this);
    for (int i = 0; i < num_edge_vars; i++) {
        assign[i] = l_Undef;
        fixed[i] = false;
    }
    current_trail.push_back(std::vector<int>());
    for (int i = 0; i < num_edge_vars; i++) {
        solver->add_observed_var(i + 1);
    }
}

CadicalLean::~CadicalLean () {
    if (n != 0) {
        solver->disconnect_external_propagator();
        delete[] assign;
        delete[] fixed;
    }
}

void CadicalLean::notify_assignment(int lit, bool is_fixed) {
    int var = abs(lit) - 1;
    assign[var] = (lit > 0) ? l_True : l_False;
    fixed[var] = is_fixed;

    // Print the partial assignment
    std::cout << "Partial assignment: ";
    for (int i = 0; i < num_edge_vars; i++) {
        if (assign[i] != l_Undef) {
            std::cout << (assign[i] == l_True ? i + 1 : -(i + 1)) << " ";
        }
    }
    std::cout << std::endl;
    
    bool constraint_violated = false;
    
    // Check edge count if edge_bound is non-negative
    if (edge_bound >= 0) {
        if (check_edge_count()) {
            constraint_violated = true;
        }
    }
    
    // Check degree count if degree_bound is non-negative
    if (degree_bound >= 0) {
        if (check_degree_count()) {
            constraint_violated = true;
        }
    }
    
    // If either constraint is violated, generate and add blocking clause
    if (constraint_violated) {
        std::vector<int> clause = generate_blocking_clause();
        if (!clause.empty()) {
            std::cout << "Constraint bound exceeded. Adding blocking clause: ";
            for (const auto& lit : clause) {
                std::cout << lit << " ";
            }
            std::cout << std::endl;
            
            new_clauses.push_back(clause);
            solver->add_trusted_clause(clause);
        }
    }
}

void CadicalLean::notify_new_decision_level () {
}

void CadicalLean::notify_backtrack (size_t new_level) {
}

bool CadicalLean::cb_check_found_model (const std::vector<int> & model) {
    assert(model.size() == num_edge_vars);
    sol_count += 1;

    std::cout << "Found model #" << sol_count << ": ";
    std::vector<int> clause;
    for (const auto& lit: model) {
        if (lit > 0) {
            std::cout << lit << " ";
        }
        clause.push_back(-lit);
    }
    std::cout << std::endl;

    // Instead of directly adding the clause, store it for later addition
    new_clauses.push_back(clause);
    solver->add_trusted_clause(clause);

    // Print out the added blocking clause
    std::cout << "Added blocking clause: ";
    for (const auto& lit : clause) {
        std::cout << lit << " ";
    }
    std::cout << std::endl;

    // Signal that we want to continue searching
    return false;
}

bool CadicalLean::cb_has_external_clause () {
    return !new_clauses.empty();
}

int CadicalLean::cb_add_external_clause_lit () {
    if (new_clauses.empty()) return 0;
    
    int lit = new_clauses.back().back();
    new_clauses.back().pop_back();
    
    if (new_clauses.back().empty()) {
        new_clauses.pop_back();
    }
    
    return lit;
}

int CadicalLean::cb_decide () {
    // Callback skeleton
    return 0;
}

int CadicalLean::cb_propagate () {
    // Callback skeleton
    return 0;
}

int CadicalLean::cb_add_reason_clause_lit (int plit) {
    std::cout << "Adding reason clause literal: " << plit << std::endl;
    return 0;
}

bool CadicalLean::check_edge_count() {
    // Prepare the command to run edge_counter with current assignment
    std::stringstream cmd;
    cmd << edge_counter_path << " " << n;  // First argument is the order n
    
    // Add all variable assignments in the required format
    // For each potential edge variable, add:
    // - The positive variable number if assigned true
    // - The negative variable number if assigned false
    // - 0 if the variable is unassigned
    for (int i = 0; i < num_edge_vars; i++) {
        int var_num = i + 1;  // Convert to 1-based indexing
        if (assign[i] == l_True) {
            cmd << " " << var_num;  // Positive variable number
        } else if (assign[i] == l_False) {
            cmd << " " << -var_num;  // Negative variable number
        } else {
            cmd << " " << 0;  // Unassigned variable
        }
    }
    
    std::cout << "Running edge counter: " << cmd.str() << std::endl;
    
    // Execute the command and capture output
    FILE* pipe = popen(cmd.str().c_str(), "r");
    if (!pipe) {
        std::cerr << "Error executing edge counter" << std::endl;
        return false;
    }
    
    // Read the binary result (0 or 1)
    char buffer[128];
    std::string result = "";
    while (!feof(pipe)) {
        if (fgets(buffer, 128, pipe) != NULL)
            result += buffer;
    }
    pclose(pipe);
    
    // Trim whitespace
    result.erase(0, result.find_first_not_of(" \n\r\t"));
    result.erase(result.find_last_not_of(" \n\r\t") + 1);
    
    // Parse the output - should be 0 or 1
    int exceeded = 0;
    try {
        exceeded = std::stoi(result);
        std::cout << "Edge counter result: " << exceeded << std::endl;
    } catch (const std::exception& e) {
        std::cerr << "Error parsing edge counter output: " << result << std::endl;
        return false;
    }
    
    // Return true if bound is exceeded (result is 1)
    return (exceeded == 1);
}

bool CadicalLean::check_degree_count() {
    // Prepare the command to run degree_counter with current assignment
    std::stringstream cmd;
    cmd << degree_counter_path << " " << n;  // First argument is the order n
    
    // Add all variable assignments in the required format
    // For each potential edge variable, add:
    // - The positive variable number if assigned true
    // - The negative variable number if assigned false
    // - 0 if the variable is unassigned
    for (int i = 0; i < num_edge_vars; i++) {
        int var_num = i + 1;  // Convert to 1-based indexing
        if (assign[i] == l_True) {
            cmd << " " << var_num;  // Positive variable number
        } else if (assign[i] == l_False) {
            cmd << " " << -var_num;  // Negative variable number
        } else {
            cmd << " " << 0;  // Unassigned variable
        }
    }
    
    std::cout << "Running degree counter: " << cmd.str() << std::endl;
    
    // Execute the command and capture output
    FILE* pipe = popen(cmd.str().c_str(), "r");
    if (!pipe) {
        std::cerr << "Error executing degree counter" << std::endl;
        return false;
    }
    
    // Read the binary result (0 or 1)
    char buffer[128];
    std::string result = "";
    while (!feof(pipe)) {
        if (fgets(buffer, 128, pipe) != NULL)
            result += buffer;
    }
    pclose(pipe);
    
    // Trim whitespace
    result.erase(0, result.find_first_not_of(" \n\r\t"));
    result.erase(result.find_last_not_of(" \n\r\t") + 1);
    
    // Parse the output - should be 0 or 1
    int exceeded = 0;
    try {
        exceeded = std::stoi(result);
        std::cout << "Degree counter result: " << exceeded << std::endl;
    } catch (const std::exception& e) {
        std::cerr << "Error parsing degree counter output: " << result << std::endl;
        return false;
    }
    
    // Return true if bound is exceeded (result is 1)
    return (exceeded == 1);
}

std::vector<int> CadicalLean::generate_blocking_clause() {
    std::vector<int> clause;
    
    // Add negation of all positive edge variables in the current assignment
    for (int i = 0; i < num_edge_vars; i++) {
        if (assign[i] == l_True) {
            clause.push_back(-(i + 1));
        }
    }
    
    return clause;
}