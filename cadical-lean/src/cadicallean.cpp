#include "cadicallean.hpp"
#include <iostream>
#include <cassert>
#include <cstdlib>
#include <sstream>
#include <chrono>
#include <lean/lean.h>

// Add these external function declarations
extern "C" lean_object* readInput_Str(lean_object* w);
extern "C" lean_object* edgesExceedBound(lean_object* w, lean_object* upperbound);
extern "C" void lean_initialize_runtime_module();
extern "C" void lean_initialize();
extern "C" void lean_io_mark_end_initialization();
extern "C" lean_object* initialize_Leansat(uint8_t builtin, lean_object* w);
extern "C" lean_object* DegreeExceedBound(lean_object* w, lean_object* upperbound);

CadicalLean::CadicalLean(CaDiCaL::Solver * s, int order, int edge_bound, const std::string& edge_counter_path,
                         int degree_bound, const std::string& degree_counter_path, bool use_lean) 
    : solver(s), 
      n(order), 
      num_edge_vars(n * (n - 1) / 2),
      assign(new int[n * (n - 1) / 2]),
      fixed(new bool[n * (n - 1) / 2]),
      edge_bound(edge_bound), 
      edge_counter_path(edge_counter_path),
      degree_bound(degree_bound),
      degree_counter_path(degree_counter_path),
      sol_count(0),
      edge_check_calls(0),
      degree_check_calls(0),
      edge_check_time(0.0),
      degree_check_time(0.0),
      use_lean(use_lean) {
    
    solver->connect_external_propagator(this);
    for (int i = 0; i < num_edge_vars; i++) {
        assign[i] = l_Undef;
        fixed[i] = false;
    }
    current_trail.push_back(std::vector<int>());
    for (int i = 0; i < num_edge_vars; i++) {
        solver->add_observed_var(i + 1);
    }
    
    // Initialize Lean runtime only if we're using Lean
    if (use_lean) {
        lean_initialize_runtime_module();
        lean_initialize();
        
        lean_object* res = initialize_Leansat(1, lean_io_mk_world());
        if (lean_io_result_is_ok(res)) {
            lean_dec_ref(res);
        } else {
            lean_io_result_show_error(res);
            lean_dec_ref(res);
            std::cerr << "Failed to initialize Lean runtime" << std::endl;
        }
        lean_io_mark_end_initialization();
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

    // Comment out partial assignment printing
    /*
    std::cout << "Partial assignment: ";
    for (int i = 0; i < num_edge_vars; i++) {
        if (assign[i] != l_Undef) {
            std::cout << (assign[i] == l_True ? i + 1 : -(i + 1)) << " ";
        }
    }
    std::cout << std::endl;
    */
    
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
            // Comment out blocking clause printing
            /*
            std::cout << "Constraint bound exceeded. Adding blocking clause: ";
            for (const auto& lit : clause) {
                std::cout << lit << " ";
            }
            std::cout << std::endl;
            */
            
            new_clauses.push_back(clause);
            solver->add_trusted_clause(clause);
        }
    }
}

void CadicalLean::notify_new_decision_level () {
}

void CadicalLean::notify_backtrack (size_t new_level) {
}

bool CadicalLean::cb_check_found_model(const std::vector<int> & model) {
    assert(model.size() == num_edge_vars);
    
    // Check if the model satisfies the edge bound constraint
    bool constraint_violated = false;
    
    // First, update the assignment based on the model
    for (size_t i = 0; i < model.size(); i++) {
        int lit = model[i];
        assign[i] = (lit > 0) ? l_True : l_False;
    }
    
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
    
    // If either constraint is violated, add blocking clause but don't count as solution
    if (constraint_violated) {
        std::vector<int> clause = generate_blocking_clause();
        if (!clause.empty()) {
            // Comment out model violation printing
            /*
            std::cout << "Model violates constraint bound. Adding blocking clause: ";
            for (const auto& lit : clause) {
                std::cout << lit << " ";
            }
            std::cout << std::endl;
            */
            
            new_clauses.push_back(clause);
            solver->add_trusted_clause(clause);
        }
        return false; // Continue searching
    }
    
    // If constraints are satisfied, count as a solution
    sol_count += 1;

    // Print the found model (keep this part)
    std::cout << "Found model #" << sol_count << ": ";
    std::vector<int> clause;
    for (const auto& lit: model) {
        if (lit > 0) {
            std::cout << lit << " ";
        }
        clause.push_back(-lit);
    }
    std::cout << std::endl;

    // Add blocking clause for this solution
    new_clauses.push_back(clause);
    solver->add_trusted_clause(clause);

    // Comment out blocking clause printing
    /*
    std::cout << "Added blocking clause: ";
    for (const auto& lit : clause) {
        std::cout << lit << " ";
    }
    std::cout << std::endl;
    */

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
    // Comment out reason clause printing
    // std::cout << "Adding reason clause literal: " << plit << std::endl;
    return 0;
}

bool CadicalLean::check_edge_count() {
    auto start_time = std::chrono::high_resolution_clock::now();
    edge_check_calls++;
    
    if (!use_lean) {
        // Direct C++ implementation for edge counting
        int edge_count = 0;
        for (int i = 0; i < num_edge_vars; i++) {
            if (assign[i] == l_True) {
                edge_count++;
            }
        }
        
        auto end_time = std::chrono::high_resolution_clock::now();
        edge_check_time += std::chrono::duration<double>(end_time - start_time).count();
        
        // Comment out edge count printing
        // std::cout << "C++ edge count: " << edge_count << " (bound: " << edge_bound << ")" << std::endl;
        return edge_count > edge_bound;
    }
    
    // Use Lean for edge counting - keep the original implementation intact
    // Prepare the input string for the edge counter
    std::stringstream ss;
    for (int i = 0; i < num_edge_vars; i++) {
        if (i > 0) ss << " ";
        int var_num = i + 1;  // Convert to 1-based indexing
        if (assign[i] == l_True) {
            ss << var_num;  // Positive variable number
        } else if (assign[i] == l_False) {
            ss << -var_num;  // Negative variable number
        } else {
            ss << 0;  // Unassigned variable
        }
    }
    std::string input_string = ss.str();
    
    // Comment out input printing
    // std::cout << "Checking edge count with input: " << input_string << std::endl;
    
    // Call the Lean functions directly - matching edge_counter.cpp implementation
    lean_object* input_str = lean_mk_string(input_string.c_str());
    lean_object* w = readInput_Str(input_str);
    lean_dec_ref(input_str);
    
    // Use the bound from member variable - convert to unsigned for Lean
    unsigned int abs_bound = (edge_bound < 0) ? 0 : edge_bound;
    lean_object* upperbound = lean_unsigned_to_nat(abs_bound);
    
    lean_object* output = edgesExceedBound(w, upperbound);
    
    bool exceeded = false;
    if (lean_is_scalar(output)) {
        exceeded = lean_unbox(output) != 0;
        // Comment out result printing
        // std::cout << "Edge counter result: " << (exceeded ? "true" : "false") << std::endl;
    } else {
        std::cerr << "Error: Invalid result from edgesExceedBound" << std::endl;
    }
    
    // No cleanup to avoid segfault (matching edge_counter.cpp)
    
    auto end_time = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> elapsed = end_time - start_time;
    edge_check_time += elapsed.count();
    
    return exceeded;
}

bool CadicalLean::check_degree_count() {
    auto start_time = std::chrono::high_resolution_clock::now();
    degree_check_calls++;
    
    if (!use_lean) {
        // Direct C++ implementation for degree counting
        // Create an adjacency list representation
        std::vector<std::vector<int>> adj_list(n);
        
        // Correctly map variables to the adjacency matrix (column by column)
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                if (i != j && j > i) {
                    // Column-by-column mapping
                    int col = j;
                    int row = i;
                    int edge_idx = (col * (col - 1)) / 2 + row;
                    if (assign[edge_idx] == l_True) {
                        adj_list[i].push_back(j);
                        adj_list[j].push_back(i);
                    }
                }
            }
        }
        
        // Check if any vertex has degree exceeding or equal to the bound
        int max_degree = 0;
        for (int i = 0; i < n; i++) {
            max_degree = std::max(max_degree, static_cast<int>(adj_list[i].size()));
            if (static_cast<int>(adj_list[i].size()) >= degree_bound) {
                auto end_time = std::chrono::high_resolution_clock::now();
                degree_check_time += std::chrono::duration<double>(end_time - start_time).count();
                return true;
            }
        }
        
        auto end_time = std::chrono::high_resolution_clock::now();
        degree_check_time += std::chrono::duration<double>(end_time - start_time).count();
        return false;
    }
    
    // Use Lean for degree counting - keep the original implementation intact
    // Prepare the input string for the degree counter
    std::stringstream ss;
    for (int i = 0; i < num_edge_vars; i++) {
        if (i > 0) ss << " ";
        int var_num = i + 1;  // Convert to 1-based indexing
        if (assign[i] == l_True) {
            ss << var_num;  // Positive variable number
        } else if (assign[i] == l_False) {
            ss << -var_num;  // Negative variable number
        } else {
            ss << 0;  // Unassigned variable
        }
    }
    std::string input_string = ss.str();
    
    // Comment out input printing
    // std::cout << "Checking degree count with input: " << input_string << std::endl;
    
    // Call the Lean functions directly - matching degree_counter.cpp implementation
    lean_object* input_str = lean_mk_string(input_string.c_str());
    lean_object* w = readInput_Str(input_str);
    lean_dec_ref(input_str);
    
    // Use the bound from member variable - convert to unsigned for Lean
    unsigned int abs_bound = (degree_bound < 0) ? 0 : degree_bound;
    lean_object* upperbound = lean_unsigned_to_nat(abs_bound);
    
    lean_object* output = DegreeExceedBound(w, upperbound);
    
    bool exceeded = false;
    if (lean_is_scalar(output)) {
        exceeded = lean_unbox(output) != 0;
        // Comment out result printing
        // std::cout << "Degree counter result: " << (exceeded ? "true" : "false") << std::endl;
    } else {
        std::cerr << "Error: Invalid result from DegreeExceedBound" << std::endl;
    }
    
    // No cleanup to avoid segfault (matching degree_counter.cpp)
    
    auto end_time = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> elapsed = end_time - start_time;
    degree_check_time += elapsed.count();
    
    return exceeded;
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

void CadicalLean::print_statistics() {
    std::cout << "\n=== CadicalLean Statistics ===\n";
    std::cout << "Total solutions found: " << sol_count << "\n";
    
    if (edge_bound >= 0) {
        std::cout << "Edge counter calls: " << edge_check_calls << "\n";
        std::cout << "Total time spent in edge checking: " << edge_check_time << " seconds\n";
        std::cout << "Average time per edge check: " << (edge_check_calls > 0 ? edge_check_time / edge_check_calls : 0) << " seconds\n";
    }
    
    if (degree_bound >= 0) {
        std::cout << "Degree counter calls: " << degree_check_calls << "\n";
        std::cout << "Total time spent in degree checking: " << degree_check_time << " seconds\n";
        std::cout << "Average time per degree check: " << (degree_check_calls > 0 ? degree_check_time / degree_check_calls : 0) << " seconds\n";
    }
    
    std::cout << "================================\n";
}