#include "cadicallean.hpp"
#include <iostream>
#include <cassert>

CadicalLean::CadicalLean(CaDiCaL::Solver * s, int order) : solver(s), n(order) {
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
    // Print the partial assignment
    std::cout << "Partial assignment: ";
    for (int i = 0; i < num_edge_vars; i++) {
        if (assign[i] != l_Undef) {
            std::cout << (assign[i] == l_True ? i + 1 : -(i + 1)) << " ";
        }
    }
    std::cout << std::endl;
}

void CadicalLean::notify_new_decision_level () {
}

void CadicalLean::notify_backtrack (size_t new_level) {
}

bool CadicalLean::cb_check_found_model (const std::vector<int> & model) {
    assert(model.size() == num_edge_vars);
    sol_count += 1;

    std::cout << "Found model: ";
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

    // Signal that we have a new clause to add
    return true;
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