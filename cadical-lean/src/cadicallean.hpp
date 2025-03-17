#ifndef CADICALLEAN_HPP
#define CADICALLEAN_HPP

#include <vector>
#include <string>
#include "cadical.hpp"

class CadicalLean : public CaDiCaL::ExternalPropagator {
private:
    CaDiCaL::Solver* solver;
    int n;
    int num_edge_vars;
    int* assign;
    bool* fixed;
    std::vector<std::vector<int>> current_trail;
    std::vector<std::vector<int>> new_clauses;
    
    // Renamed parameter for edge counting
    int edge_bound;
    std::string edge_counter_path;
    int sol_count = 0;

    static const int l_True = 1;
    static const int l_False = -1;
    static const int l_Undef = 0;
    
    // Helper methods for edge counting
    bool check_edge_count();
    std::vector<int> generate_blocking_clause();

public:
    // Updated constructor with renamed parameter
    CadicalLean(CaDiCaL::Solver* s, int order, int edge_bound, const std::string& edge_counter_path = "./edge_counter");
    ~CadicalLean();

    // ExternalPropagator interface methods
    void notify_assignment(int lit, bool is_fixed) override;
    void notify_new_decision_level() override;
    void notify_backtrack(size_t new_level) override;
    bool cb_check_found_model(const std::vector<int>& model) override;
    bool cb_has_external_clause() override;
    int cb_add_external_clause_lit() override;
    int cb_decide() override;
    int cb_propagate() override;
    int cb_add_reason_clause_lit(int plit) override;
};

#endif // CADICALLEAN_HPP