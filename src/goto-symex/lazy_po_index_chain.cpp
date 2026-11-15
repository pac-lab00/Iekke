/// \file
/// lazy_po: --index-chain (the chain carries the index of the last write) and the read-from schema tally
/// \file
/// lazy_po: base round-robin encoding -- read/write values, context-switch counters, guards, active threads

#include "lazy_po.h"
#include <util/ssa_expr.h>
#include <cctype>
#include <optional>
#include <tuple>
#include <util/bitvector_types.h>
#include <util/expr_util.h>
#include <util/pointer_offset_size.h>
#include <util/byte_operators.h>
#include <string>
#include <map>
#include <algorithm>
#include <set>
#include <unordered_set>
#include <cstdlib>
#include <iostream>
#include <chrono>
#include <fstream>
#include <functional>
#include <thread>
#include <util/cprover_prefix.h>
#include <util/format.h>
#include <util/format_expr.h>
#include <util/pointer_expr.h>
#include <util/c_types.h>
#include <util/prefix.h>
#include <util/expr_util.h>
#include <ansi-c/expr2c.h>
#include <util/simplify_expr.h>
#include <util/source_location.h>

#include <util/arith_tools.h>
#include <util/invariant.h>
#include <util/symbol.h>

#include "lazy_po_internal.h"

std::vector<std::size_t> lazy_pot::index_candidates(
  const irep_idt &v,
  const shared_event &read) const
{
  // The chain at (round, thread, label, num) holds 0 or the index of an
  // executed write that comes before that position in the schedule order
  // (round, thread, label, num). A write of another thread can come before
  // the read in some round -- in the same round only if its thread is
  // numbered lower, so with one round only those. A write of the reading
  // thread comes before it only if it comes first in program order: one
  // later in program order would have to run in an earlier round, which the
  // monotone context switches exclude.
  std::vector<std::size_t> result{0};
  const auto &ws = writes.at(v);
  for(std::size_t i = 0; i < ws.size(); ++i)
  {
    const auto &e = ws[i];
    const bool before =
      e.thread != read.thread
        ? (rounds > 1 || e.thread < read.thread)
        : std::tie(e.label, e.num) < std::tie(read.label, read.num);
    if(before)
      result.push_back(i + 1);
  }
  return result;
}

/// --index-chain: per object, the chain carries the value of the last write
/// or its index, whichever the estimate below, in bit cells, finds smaller. A
/// value chain costs a mux of the value's width per (write, round) and an
/// equality of that width per (read, round); an index chain costs the same at
/// the index's width, plus one equality of the value's width per write a read
/// can see (index_candidates). Below three rounds the gain measured about 1%
/// and the estimate chose wrongly on 12 of 142 tasks, so it is not used there.
/// Objects answered by --array-rf have no chain to change, and the
/// active-thread flags are read by the schedule encoding through
/// previous_shared, which must keep returning values for them.
std::string lazy_pot::choose_index_chains()
{
  index_chain_vars.clear();
  index_chain_bits.clear();
  index_chain_values.clear();
  if(!index_chain || rounds < 3)
    return {};
  std::size_t chosen = 0, considered = 0;
  for(const auto &gv : global_variables)
  {
    if(writes.count(gv) == 0 || array_rf_writes.count(gv) != 0)
      continue;
    if(has_prefix(id2string(gv), "__CPROVER_active_thread_"))
      continue;
    const auto &ws = writes.at(gv);
    const auto wbits = pointer_offset_bits(
      narrowed_type(gv, ws.front().s_it->ssa_lhs.type()), ns);
    if(!wbits.has_value())
      continue;
    ++considered;
    const double w = static_cast<double>(numeric_cast_v<std::size_t>(*wbits));
    std::size_t b = 1;
    while((std::size_t(1) << b) < ws.size() + 1)
      ++b;
    const std::size_t nr = reads.count(gv) ? reads.at(gv).size() : 0;
    double cand = 0;
    if(nr)
      for(const auto &rd : reads.at(gv))
        cand += static_cast<double>(index_candidates(gv, rd).size());
    const double accesses = static_cast<double>(ws.size() + nr);
    const double value_cost = double(rounds) * accesses * w;
    const double index_cost =
      double(rounds) * accesses * double(b) + cand * (w + double(b));
    if(index_cost < value_cost)
    {
      index_chain_vars.insert(gv);
      index_chain_bits[gv] = b;
      ++chosen;
    }
  }
  return std::to_string(chosen) + " of " + std::to_string(considered) +
         " objects";
}

