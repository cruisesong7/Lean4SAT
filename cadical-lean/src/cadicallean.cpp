#include "cadicallean.hpp"
#include <iostream>
#include <cassert>
#include <cstdlib>
#include <sstream>

CadicalLean::CadicalLean(CaDiCaL::Solver * s, int order, int max_edges, const std::string& edge_counter_path) : solver(s), n(order), max_edges(max_edges), edge_counter_path(edge_counter_path), sol_count(0) {
    num_edge_vars = n * (n - 1) / 2;
    assign = new int[num_edge_vars];
    fixed = new bool[num_edge_vars];
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
    
    // Check edge count after each assignment
    if (check_edge_count()) {
        // If edge count exceeds limit, generate and add blocking clause
        std::vector<int> clause = generate_blocking_clause();
        if (!clause.empty()) {
            std::cout << "Edge count exceeded limit. Adding blocking clause: ";
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
    cmd << edge_counter_path;
    
    // Count positive edge variables
    int positive_count = 0;
    for (int i = 0; i < num_edge_vars; i++) {
        if (assign[i] == l_True) {
            cmd << " " << (i + 1);
            positive_count++;
        }
    }
    
    // If no positive assignments, no need to check edge count
    if (positive_count == 0) {
        std::cout << "No positive edge assignments, edge count is 0" << std::endl;
        return false;  // No edges, so can't exceed limit
    }
    
    // Execute the command and capture output
    std::string result = "";
    FILE* pipe = popen(cmd.str().c_str(), "r");
    if (!pipe) {
        std::cerr << "Error executing edge counter" << std::endl;
        return false;
    }
    
    char buffer[128];
    while (!feof(pipe)) {
        if (fgets(buffer, 128, pipe) != NULL)
            result += buffer;
    }
    pclose(pipe);
    
    // Parse the output to get edge count
    int edge_count = 0;
    size_t pos = result.find("Number of edges: ");
    if (pos != std::string::npos) {
        std::stringstream ss(result.substr(pos + 16));
        ss >> edge_count;
        
        std::cout << "Current edge count: " << edge_count << " (max: " << max_edges << ")" << std::endl;
        
        // Return true if edge count exceeds limit and max_edges is valid
        return (max_edges >= 0) && (edge_count > max_edges);
    }
    
    return false;
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