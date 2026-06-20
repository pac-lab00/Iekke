// __SZH_ADD_BEGIN__

#ifndef SEGMENTSOLVER_H
#define SEGMENTSOLVER_H

#include <map>
#include <unordered_map>

#include "../../minisat/core/Solver.h"
#include "SegmentTypes.h"

typedef std::vector<std::pair<std::pair<std::string, std::string>, std::pair<Minisat::Lit, std::string> > > oc_edge_tablet;
typedef std::map<std::string, Minisat::Lit> oc_guard_mapt;
typedef std::map<std::string, int> oc_location_mapt;

namespace Minisat
{

class SegmentSolver : public Solver
{
    std::vector<segment_nodet> nodes;
    std::vector<std::string> id_to_address;

    std::vector<std::vector<int>> chains;
    std::vector<std::vector<int>> chains_atomic_last;
    std::vector<std::vector<int>> chains_atomic_first;
    std::vector<std::vector<segment_treet>> trees;

    int get_atomic_last(int chain, int serial)
    {
        if(serial < 0)
            return serial;
        return chains_atomic_last[chain][serial];
    }
    int get_atomic_first(int chain, int serial)
    {
        if(serial >= int(chains[chain].size()))
            return serial;
        return chains_atomic_first[chain][serial];
    }

    oc_edge_tablet oc_edge_table;
    oc_guard_mapt oc_guard_map;
    oc_location_mapt oc_location_map;
    std::map<std::string, int>* oc_result_order;

    std::vector<std::pair<Lit, int>> literals_to_assign;
    std::set<Lit> assigned_literals;

    // for storing reasons
    std::vector<pooled_reasont> reason_pool;
    std::vector<int> reason_pool_lim;
    int register_reason(pooled_reasont reason); // turn a reason into a stable one

    // for backtracking
    struct trail_updatet
    {
        int chain1, chain2, serial1;
        digit_reasont old_entry;
        trail_updatet() {}
        trail_updatet(int _chain1, int _chain2, int _serial1, digit_reasont _old) :
            chain1(_chain1), chain2(_chain2), serial1(_serial1), old_entry(_old) {}
    };
    std::vector<trail_updatet> trail_update;
    std::vector<int> trail_update_lim;
    std::vector<std::pair<int, int>> trail_rf;
    std::vector<int> trail_rf_lim;
    std::vector<int> trail_guard;
    std::vector<int> trail_guard_lim;
    std::vector<std::pair<int, int>> trail_vital;
    std::vector<int> trail_vital_lim;
    std::vector<std::pair<Lit, Lit>> trail_triplet;
    std::vector<int> trail_triplet_lim;

    struct triplett
    {
        int w1;
        int w2;
        int r;
        Lit rf_lit;
        Lit guard_lit;
        int reason_id1;
        int reason_id2;

        triplett(int _w1, int _w2, int _r, Lit _rf_lit, Lit _guard_lit, int _reason_id1, int _reason_id2) :
            w1(_w1), w2(_w2), r(_r), rf_lit(_rf_lit), guard_lit(_guard_lit), reason_id1(_reason_id1), reason_id2(_reason_id2) {}
    };
    std::unordered_map<Lit, std::vector<triplett>, LitHasher> rf_to_triplets;
    std::unordered_map<Lit, std::vector<triplett>, LitHasher> guard_to_triplets;

    void push_scope();
    void pop_scope(int new_level);

    int conflict_cycle = 0;
    int theory_propagation = 0;

protected:
    CRef propagate();
    void cancelUntil(int level);
    void newDecisionLevel();
    lbool search(int nof_conflicts);
    void analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel);
public:
    SegmentSolver();
    node_idt get_node(std::string name);
    void save_raw_graph(oc_edge_tablet& _oc_edge_table, oc_guard_mapt& _oc_guard_map, oc_location_mapt& _oc_location_map, std::map<std::string, int>& _oc_result_order);
    void set_graph();
    std::vector<std::pair<node_idt, node_idt>> set_skeleton();
    void set_atomic();
    void init_races();
    void init_guards();
    void init_reasonable_edges();
    void init_vital_edges();
    void check_races_in_skeleton();

    typedef std::pair<std::pair<int, int>, edge_kindt> decide_entryt;
    std::map<Lit, decide_entryt> lit_to_edge;
    std::multimap<Lit, int> guard_lit_to_node;

    std::map<std::pair<int, int>, Lit> pair_to_inactive_races; // pair.first < pair.second

    typedef std::pair<std::pair<int, int>, Lit> inactive_edge_t;
    std::vector<std::vector<inactive_edge_t>> tail_to_inactive_edges;
    std::vector<std::vector<inactive_edge_t>> head_to_inactive_edges;
    std::vector<std::vector<Lit>> tail_head_to_inactive_lit;

    Lit check_tail_head_to_inactive_lit(node_idt node1, node_idt node2)
    {
        if(int(tail_head_to_inactive_lit.size()) <= node1)
            return lit_Error;
        if(int(tail_head_to_inactive_lit[node1].size()) <= node2)
            return lit_Error;
        return tail_head_to_inactive_lit[node1][node2];
    }

    void remove_rf(node_idt node1, node_idt node2, Lit lit);

    std::vector<digit_reasont> get_first_successors(node_idt node);
    std::vector<digit_reasont> get_last_predecessors(node_idt node);
    void extract_writes_reads_per_loc(node_idt node, std::vector<digit_reasont>& serials, bool is_successor, std::vector<std::vector<digit_reasont>>& writes_per_loc, std::vector<std::vector<digit_reasont>>& reads_per_loc, bool include_self);
    void get_successors(node_idt node, std::vector<std::vector<digit_reasont>>& writes_per_loc, std::vector<std::vector<digit_reasont>>& reads_per_loc, bool include_self);
    void get_predecessors(node_idt node, std::vector<std::vector<digit_reasont>>& writes_per_loc, std::vector<std::vector<digit_reasont>>& reads_per_loc, bool include_self);

    bool need_add_edge(node_idt node1, node_idt node2); // if false, an edge is implied by existing edges, so that no need to add
    bool add_edge(node_idt node1, node_idt node2, int reason_id);
    bool add_rf(node_idt node1, node_idt node2, Lit lit);
    bool enable_guard(node_idt node);

    bool check_pair(node_idt node1, node_idt node2, int reason_id1, int reason_id2, int reason_id3);

    lbool solve_();
    bool solve() { budgetOff(); assumptions.clear(); return solve_() == l_True; }
    inline bool solve(const vec<Lit>& assumps){ budgetOff(); assumps.copyTo(assumptions); return solve_() == l_True; }
    inline lbool solveLimited(const vec<Lit>& assumps){ assumps.copyTo(assumptions); return solve_(); }

    decide_entryt get_decide_entry(Lit l);
    std::vector<int> check_guard_literal(Lit guard_lit);
    lbool get_assignment(Lit lit);
    bool use_available_info();

    void show_model();

    literal_vector conflict_clause;

    void add_w_w_vital_edge(node_idt w1, node_idt w2, int reason_id);
    void add_w_r_vital_edge(node_idt w2, node_idt r, int reason_id);
    void check_trinary(node_idt w1, node_idt w2, node_idt r, int reason_id1, int reason_id2);

    void assign_literal(Lit l, int reason_id);

    void apply_literal_assignment();

    std::vector<std::string> get_write_order();
};

}

#endif

// __SZH_ADD_END__