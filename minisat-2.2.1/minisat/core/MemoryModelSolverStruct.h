#ifndef MEMORY_MODEL_SOLVER_STRUCT_H
#define MEMORY_MODEL_SOLVER_STRUCT_H

#include <vector>
#include <set>
#include <unordered_set>

#include "../../minisat/mtl/Vec.h"
#include "../../minisat/mtl/Heap.h"
#include "../../minisat/mtl/Alg.h"
#include "../../minisat/core/SolverTypes.h"
#include "../../minisat/mtl/Sort.h"
#include "GraphTypes.h"

typedef std::vector<std::pair<std::pair<std::string, std::string>, std::pair<Minisat::Lit, std::string> > > oc_edge_tablet;
typedef std::vector<std::pair<std::string, std::pair<Minisat::Lit, std::string> > > oc_label_tablet;

namespace Minisat
{

class unary_must_may_sett
{
public:
    std::set<int> elements;

    bool contains(int node_id) { return elements.find(node_id) != elements.end(); }
    void set(int node_id) { elements.insert(node_id); }
    int size() { return elements.size(); }
};
typedef unary_must_may_sett unary_must_sett;
typedef unary_must_may_sett unary_may_sett;

class binary_must_may_sett
{
public:
    std::set<std::pair<int, int>> elements;

    bool contains(int node1_id, int node2_id) { return elements.find(std::make_pair(node1_id, node2_id)) != elements.end(); }
    void set(int node1_id, int node2_id) { elements.insert(std::make_pair(node1_id, node2_id)); }
    int size() { return elements.size(); }
};

typedef binary_must_may_sett binary_must_sett;
typedef binary_must_may_sett binary_may_sett;

class unary_sett
{
    std::vector<elementt> elements; //1 for in, 0 for not in
    std::set<int> element_set;
public:
    unary_sett(int size = 0) {elements.resize(size);}

    bool contains(int node_id) {return bool(elements[node_id].first);}
    reasont& get_reason(int node_id) {return elements[node_id].second;}

    std::set<int>& all_elements() {return element_set;}
    int get_element_num() {return element_set.size();}

    void set(int node_id, reasont reason)
    {
        elements[node_id] = std::make_pair(1, reason);
        element_set.insert(node_id);
    }
    void unset(int node_id) 
    {
        elements[node_id] = std::make_pair(0, reasont());
        element_set.erase(node_id);
    }

    int size() {return elements.size();}
};

class binary_sett //also called event graph!
{
    std::vector<std::vector<elementt>> elements; //1 for in, 0 for not in
    std::vector<std::set<int>> outs;
    std::vector<std::set<int>> ins;
    int element_num = 0;
public:
    binary_sett(int size = 0) 
    {
        elements.resize(size);
        outs.resize(size);
        ins.resize(size);
        for(auto& row : elements)
            row.resize(size);
    }

    bool contains(int node1_id, int node2_id) {return bool(elements[node1_id][node2_id].first);}
    reasont& get_reason(int node1_id, int node2_id) {return elements[node1_id][node2_id].second;}

    void set(int node1_id, int node2_id, reasont reason)
    {
        elements[node1_id][node2_id] = std::make_pair(1, reason);
        outs[node1_id].insert(node2_id);
        ins[node2_id].insert(node1_id);
        element_num++;
    }
    void unset(int node1_id, int node2_id) 
    {
        elements[node1_id][node2_id] = std::make_pair(0, reasont());
        outs[node1_id].erase(node2_id);
        ins[node2_id].erase(node1_id);
        element_num--;
    }

    std::set<int>& get_outs(int node_id) {return outs[node_id];}
    std::set<int>& get_ins(int node_id) {return ins[node_id];}

    int size() {return outs.size();}
    int get_element_num() {return element_num;}
};
}

#endif // MEMORY_MODEL_SOLVER_STRUCT_H
