// __SZH_ADD_BEGIN__

#include "SegmentTypes.h"

using namespace Minisat;

Minisat::segment_nodet::segment_nodet(std::string _name, int _address, int id) : 
    name(_name), 
    address(_address), 
    is_write(false), 
    is_read(false),
    chain(-1),
    serial(-1),
    guard_enabled(false),
    guard_lit(),
    in_rf(),
    out_rf() {}

void segment_treet::build_tree_rec(int node_id, int l, int r)
{
    data[node_id].l = l;
    data[node_id].r = r;
    if(l == r - 1)
        return;
    int mid = (l + r) >> 1;
    build_tree_rec(node_id * 2, l, mid);
    build_tree_rec(node_id * 2 + 1, mid, r);
}

segment_treet::segment_treet(int size)
{
    raw_data = std::vector<digit_reasont>(size);
    data = std::vector<segment_tree_nodet>(size * 4);
    build_tree_rec(1, 0, size);
}

digit_reasont segment_treet::get_min_rec(int node_id, int l, int r)
{
    int node_l = data[node_id].l;
    int node_r = data[node_id].r;
    if(node_l >= r || node_r <= l)
        return digit_reasont();
    if(node_l >= l && node_r <= r)
        return data[node_id].value;
    return std::min(get_min_rec(node_id * 2, l, r), get_min_rec(node_id * 2 + 1, l, r));
}

digit_reasont segment_treet::get_min(int from_serial)
{
    return get_min_rec(1, from_serial, raw_data.size());

    // digit_reasont min;
    // for(int i = from_serial; i < int(raw_data.size()); i++)
    //     if(raw_data[i] < min)
    //         min = raw_data[i];
    // return min;
}

digit_reasont segment_treet::get_argleq_rec(int node_id, int val)
{
    int node_l = data[node_id].l;
    int node_r = data[node_id].r;
    digit_reasont node_value = data[node_id].value;

    if(node_l >= node_r || node_value.digit > val)
        return digit_reasont(-1, -1);

    if(node_l == node_r - 1)
        return digit_reasont(node_l, node_value.reason_id);

    if(data[node_id * 2 + 1].value.digit <= val)
        return get_argleq_rec(node_id * 2 + 1, val);
    return get_argleq_rec(node_id * 2, val);
}

digit_reasont segment_treet::get_argleq(int to_serial)
{
    return get_argleq_rec(1, to_serial);

    // for(int i = int(raw_data.size()) - 1; i >= 0; i--)
    //     if(raw_data[i].digit <= to_serial)
    //         return digit_reasont(i, raw_data[i].reason_id);
    // return digit_reasont(-1, -1);
}

void segment_treet::update_rec(int node_id, int pos, digit_reasont val)
{
    int node_l = data[node_id].l;
    int node_r = data[node_id].r;
    if(node_l == node_r - 1)
    {
        data[node_id].value = val;
        return;
    }
    int mid = (node_l + node_r) >> 1;
    if(pos < mid)
        update_rec(node_id * 2, pos, val);
    else
        update_rec(node_id * 2 + 1, pos, val);
    data[node_id].value = std::min(data[node_id * 2].value, data[node_id * 2 + 1].value);
}

digit_reasont segment_treet::update(int serial, digit_reasont new_entry)
{
    digit_reasont old_entry = raw_data[serial];
    raw_data[serial] = new_entry;

    update_rec(1, serial, new_entry);

    return old_entry;
}

// __SZH_ADD_END__