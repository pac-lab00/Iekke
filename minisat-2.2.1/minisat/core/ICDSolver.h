// __SZH_ADD_BEGIN__

#ifndef ICDSOLVER_H
#define ICDSOLVER_H

#include <map>

#include "../../minisat/mtl/Queue.h"
#include "../../minisat/core/Solver.h"

#include "ICDTypes.h"
#include "ICD.h"



typedef std::vector<std::pair<std::pair<std::string, std::string>, std::pair<Minisat::Lit, std::string> > > oc_edge_tablet;

namespace Minisat
{

class ICDSolver : public Solver
{
    ICD graph;

    oc_edge_tablet oc_edge_table;
    std::map<std::string, int>* oc_result_order;

    std::vector<std::pair<Lit, literal_set>> literals_to_assign;

    int conflict_cycle;

protected:
    CRef propagate();
    void cancelUntil(int level);
    void newDecisionLevel();
    lbool search(int nof_conflicts);
    void analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel);
public:
    ICDSolver();

    void save_raw_graph(oc_edge_tablet& _oc_edge_table, std::map<std::string, int>& _oc_result_order);
    void set_graph();

    lbool solve_();
    bool solve() { budgetOff(); assumptions.clear(); return solve_() == l_True; }
    inline bool solve(const vec<Lit>& assumps){ budgetOff(); assumps.copyTo(assumptions); return solve_() == l_True; }
    inline lbool solveLimited(const vec<Lit>& assumps){ assumps.copyTo(assumptions); return solve_(); }

    void assign_literal(Lit l, literal_set& lv);
    void assign_literal(Lit l, literal_vector& lv);
};

}


#endif //ICDSOLVER_H

// __SZH_ADD_END__