// __SZH_ADD_BEGIN__
#ifndef GRAPHTYPES_H
#define GRAPHTYPES_H

#include <iostream>
#include <vector>
#include <bitset>
#include <set>

#include "../../minisat/mtl/Vec.h"
#include "../../minisat/mtl/Heap.h"
#include "../../minisat/mtl/Alg.h"
#include "../../minisat/core/SolverTypes.h"
#include "../../minisat/mtl/Sort.h"

#define MAX_NODES 10000

namespace Minisat
{

typedef int node_idt;

typedef std::vector<Lit> literal_vector;
typedef std::set<Lit> literal_set;

enum edge_kindt
{
    OC_NA,
    OC_APO,
    OC_PO,
    OC_RF,
    // the following are exclusive for ICD
    OC_WS,
    OC_FR,
    // the following is for data race
    OC_RACE
};

edge_kindt str_to_kind(const std::string& str);
std::string kind_to_str(edge_kindt kind);
std::ostream& operator<<(std::ostream& out, const literal_vector& v);

typedef std::vector<Lit> literal_vector;

class reasont
{
    Lit terminal1;
    Lit terminal2;
    std::vector<reasont*> sources;

    void get_full_reason_rec(literal_vector& lv)
    {
        if(terminal1.x > 0) lv.push_back(terminal1);
        if(terminal2.x > 0) lv.push_back(terminal2);
        for(auto source : sources)
            if(source != NULL)
                source->get_full_reason_rec(lv);
    }

public:
    int real_size = 0; // may be greater than sources.size(), because some sources are too trivial to be maintained. BUT THEY COUNT.

    bool trivial() {return terminal1.x < 0 && terminal2.x < 0 && sources.empty();}

    reasont(Lit _terminal1 = lit_Error) :
        terminal1(_terminal1), terminal2(lit_Error) {}
    reasont(reasont* _source1, reasont* _source2) :
        terminal1(lit_Error),  terminal2(lit_Error)
    {
        if(_source1 != NULL && !_source1->trivial())
            sources.push_back(_source1);
        if(_source2 != NULL && !_source2->trivial())
            sources.push_back(_source2);
    }
    reasont(std::vector<reasont*> _sources, Lit _terminal1 = lit_Error, Lit _terminal2 = lit_Error) :
        terminal1(_terminal1), terminal2(_terminal2), sources(_sources) {}
    
    bool push_source_unless_trivial(reasont* source) // return true if non-trivial so that really pushed
    {
        bool non_trivial = !source->trivial();
        if(non_trivial)
            sources.push_back(source);
        return non_trivial;
    }
    void pop_source() { sources.pop_back(); }
    int source_size() { return int(sources.size()); }

    literal_vector get_full_reason()
    {
        literal_vector lv;
        get_full_reason_rec(lv);
        return lv;
    }
};

typedef std::pair<node_idt, reasont> elementt;

class pooled_reasont
{
    std::vector<Lit> terminals;
    std::vector<int> sources;

    void get_full_reason_rec(literal_vector& lv, const std::vector<pooled_reasont>& reason_pool) const
    {
        for(auto terminal : terminals)
            lv.push_back(terminal);
        for(int source : sources)
            reason_pool[source].get_full_reason_rec(lv, reason_pool);
    }

public:
    pooled_reasont(std::initializer_list<Lit> _terminals = {}, std::initializer_list<int> _sources = {})
    {
        for(auto terminal : _terminals)
            if(terminal.x != -1)
                terminals.push_back(terminal);
        for(auto source : _sources)
            if(source != -1)
                sources.push_back(source);
    }

    literal_vector get_full_reason(const std::vector<pooled_reasont>& reason_pool) const
    {
        literal_vector lv;
        get_full_reason_rec(lv, reason_pool);
        return lv;
    }

    bool trivial() { return terminals.empty() && sources.empty(); }
};
}

std::string get_address(std::string name);

#endif // GRAPHTYPES_H
// __SZH_ADD_END__