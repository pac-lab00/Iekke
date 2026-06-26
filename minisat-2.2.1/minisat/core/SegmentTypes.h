// __SZH_ADD_BEGIN__
#ifndef SEGMENTTYPES_H
#define SEGMENTTYPES_H

#include <unordered_set>

#include "../../minisat/core/GraphTypes.h"

namespace Minisat
{

struct digit_reasont
{
    int digit;
    int reason_id;
    digit_reasont(int _digit = INT32_MAX, int _reason_id = -1)
        : digit(_digit), reason_id(_reason_id) {}
    bool operator<(const digit_reasont& right) const
    {
        if(digit != right.digit)
            return digit < right.digit;
        return false;
    }
};

struct segment_edget
{
    int from;
	int to;
	edge_kindt kind;
    Lit lit;

	segment_edget(int _from = -1, int _to = -1, edge_kindt _kind = OC_NA, Lit _lit = lit_Error)
        : from(_from), to(_to), kind(_kind), lit(_lit) {}

	bool operator==(const segment_edget& right) const;
};

struct segment_nodet
{
    std::string name;
    int address;

    bool is_write;
    bool is_read;

    // about segment
    int chain;
    int serial;

	// for writes only
	bool guard_enabled;
    Lit guard_lit;

    // for preventive reasoning
    std::vector<digit_reasont> out_vital;
    std::vector<digit_reasont> in_vital;
    std::unordered_set<node_idt> has_out_vital;

	std::vector<segment_edget> in_rf;
	std::vector<segment_edget> out_rf;

    segment_nodet(std::string _name, int _address, int id);

    int location; //for sort EPO properly

	friend std::ostream& operator<<(std::ostream& out, segment_nodet& node)
	{
		if(node.is_write)
			out << node.name << "(" << node.chain << ", " << node.serial << ", w)";
		else if(node.is_read)
			out << node.name << "(" << node.chain << " " << node.serial << ", r)";
		else
			out << node.name << "(" << node.chain << " " << node.serial << ")";
		return out;
	}
};

struct segment_treet
{
    int from_chain;
    int to_chain;
    std::vector<digit_reasont> raw_data;

    struct segment_tree_nodet {
        int l; // [l, r)
        int r;
        digit_reasont value;
        segment_tree_nodet() : l(-1), r(-1) {}
    };
    std::vector<segment_tree_nodet> data;

private:
    // The interval is [l, r)
    void build_tree_rec(int node_id, int l, int r);
    digit_reasont get_min_rec(int node_id, int l, int r);
    digit_reasont get_argleq_rec(int node_id, int val);
    void update_rec(int node_id, int pos, digit_reasont val);

public:
    segment_treet(int size);
    digit_reasont get_min(int from_serial);
    digit_reasont get_argleq(int to_serial);
    digit_reasont update(int serial, digit_reasont new_entry); // return the old entry
};

}
#endif
// __SZH_ADD_END__