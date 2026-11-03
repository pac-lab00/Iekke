/// \file
/// lazy_po: objects only one thread touches (--thread-private)

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

void lazy_pot::compute_private_objects()
{
  // LAZYPO_THREAD_TALLY reports the classification itself, independently of
  // whether the flag then acts on it: how many threads actually touch each
  // shared object, against the per-program decision goto-symex made.
  if(getenv("LAZYPO_THREAD_TALLY") != nullptr)
  {
    for(const auto &gv : global_variables)
    {
      std::set<unsigned> write_threads, read_threads, all;
      std::size_t nw = 0, nr = 0;
      if(writes.count(gv))
        for(const auto &w : writes.at(gv))
        {
          write_threads.insert(w.thread);
          ++nw;
        }
      if(reads.count(gv))
        for(const auto &r : reads.at(gv))
        {
          read_threads.insert(r.thread);
          ++nr;
        }
      all = write_threads;
      all.insert(read_threads.begin(), read_threads.end());
      std::cerr << "THREAD_TALLY " << gv << " threads=" << all.size()
                << " write_threads=" << write_threads.size()
                << " read_threads=" << read_threads.size() << " writes=" << nw
                << " reads=" << nr << "\n";
    }
  }

  private_objects.clear();
  if(!thread_private)
    return;

  // Classify first, and only act if the result is worth having. Rewriting the
  // chain renumbers variables, and a multi-million-clause SAT search is
  // chaotic in that respect: on elimination_backoff_stack only 38 of 9472
  // shared accesses are private, the formula shrinks by 0.09%, and the search
  // still lands on a trajectory 1.44x worse (283s -> 408s, three runs each).
  // Measured against 13.4% of accesses on 28-race_reach_81-list_racing, where
  // the same change takes 20.7% off the formula. So: do not perturb a formula
  // this is not materially improving.
  std::set<irep_idt> candidates;
  double private_cost = 0, total_cost = 0;

  for(const auto &variable : global_variables)
  {
    std::set<unsigned> threads;
    std::size_t accesses = 0;
    if(writes.count(variable) != 0)
      for(const auto &w : writes.at(variable))
      {
        threads.insert(w.thread);
        ++accesses;
      }
    if(reads.count(variable) != 0)
      for(const auto &r : reads.at(variable))
      {
        threads.insert(r.thread);
        ++accesses;
      }

    // Weigh an access by the width it carries, not by its count. A chain link
    // costs width bits, so counting accesses alone misjudges a program whose
    // private objects are many but narrow: on twalock more than 1% of the
    // accesses are private and removing them takes 1491 clauses out of 212
    // million -- 0.0007% -- while still renumbering every variable, which cost
    // 12% of the runtime.
    const typet *t = nullptr;
    if(writes.count(variable) != 0 && !writes.at(variable).empty())
      t = &writes.at(variable).front().s_it->ssa_lhs.type();
    else if(reads.count(variable) != 0 && !reads.at(variable).empty())
      t = &reads.at(variable).front().s_it->ssa_lhs.type();
    double width = 32; // a type with no fixed size still costs something
    if(t != nullptr)
    {
      const auto bits = pointer_offset_bits(*t, ns);
      if(bits.has_value() && bits->to_long() > 0)
        width = static_cast<double>(bits->to_long());
    }
    const double cost = static_cast<double>(accesses) * width;
    total_cost += cost;
    // One thread: no other thread can interleave a write, so the schedule
    // cannot change what a read sees.
    if(threads.size() <= 1)
    {
      candidates.insert(variable);
      private_cost += cost;
    }
  }

  // A hundredth of the chain's cost is the threshold. The three measured
  // points: 28-race_reach_81 removes 13.4% and the formula drops 20.7%;
  // elimination_backoff_stack removes 0.4% and the formula drops 0.09% while
  // the search gets 1.44x worse; twalock removes 0.0007% and the search gets
  // 12% worse. Below the threshold the chain being rewritten is too small to
  // pay for renumbering every variable after it.
  if(total_cost <= 0 || private_cost * 100 < total_cost)
    return;

  for(auto it = global_variables.begin(); it != global_variables.end();)
  {
    if(candidates.count(*it) != 0)
    {
      private_objects.insert(*it);
      auto w = writes.find(*it);
      if(w != writes.end())
      {
        private_writes.emplace(*it, std::move(w->second));
        writes.erase(w);
      }
      auto r = reads.find(*it);
      if(r != reads.end())
      {
        private_reads.emplace(*it, std::move(r->second));
        reads.erase(r);
      }
      it = global_variables.erase(it);
    }
    else
      ++it;
  }
}

/// "this access happens at all", i.e. the thread reaches it within the round
/// bound. Exactly the disjunction over rounds of the per-round exec, which is
/// what a private object's read-from has to be guarded by: which round it lands
/// in cannot change the answer, only whether it is reached.
exprt lazy_pot::happens_in_any_round(const shared_event &event)
{
  exprt::operandst per_round;
  per_round.reserve(rounds);
  for(std::size_t round = 1; round <= rounds; ++round)
    per_round.push_back(
      create_exec_symbol(event.label, event.num, event.thread, round));
  if(per_round.size() == 1)
    return per_round.front();
  return disjunction(per_round);
}

void lazy_pot::create_private_constraints(symex_target_equationt &equation)
{
  for(const auto &variable : private_objects)
  {
    if(private_writes.count(variable) == 0 || private_reads.count(variable) == 0)
      continue; // nothing observes the object, so it needs no chain at all

    const auto &ws = private_writes.at(variable);
    const typet chain_type =
      narrowed_type(variable, ws.front().s_it->ssa_lhs.type());

    // Same convention as create_write_constraints: the value before any write
    // is the first write's own ssa_lhs, and a read with nothing before it is
    // left unconstrained rather than tied to that sentinel.
    std::vector<exprt> chain;
    chain.reserve(ws.size());
    exprt previous = narrowed_value(variable, ws.front().s_it->ssa_lhs);

    for(const auto &write : ws)
    {
      const symbol_exprt lazy_variable_exprt{
        id2string(to_symbol_expr(write.s_it->ssa_lhs).get_identifier()) +
          "_PRIV",
        chain_type};

      equation.constraint(
        equal_exprt{
          lazy_variable_exprt,
          if_exprt{happens_in_any_round(write),
                   narrowed_value(variable, write.s_it->ssa_lhs),
                   typecast_exprt::conditional_cast(previous, chain_type)}},
        "private write constraint " + id2string(variable),
        write.s_it->source);

      chain.push_back(lazy_variable_exprt);
      previous = lazy_variable_exprt;
    }

    for(const auto &read : private_reads.at(variable))
    {
      // The last write before this read in the thread's own program order.
      // Scanning the whole vector rather than stopping at the first write that
      // is not earlier: the chain is built in collection order, and this does
      // not have to assume that order is sorted by (label, num).
      bool found = false;
      std::size_t before = 0;
      std::pair<unsigned, unsigned> best{0, 0};
      for(std::size_t i = 0; i < ws.size(); ++i)
      {
        const std::pair<unsigned, unsigned> here{ws[i].label, ws[i].num};
        if(here < std::make_pair(read.label, read.num) &&
           (!found || best < here))
        {
          found = true;
          best = here;
          before = i;
        }
      }
      if(!found)
        continue; // reads the pre-first-write value, which constrains nothing

      // Unconditional. The read's value is a fresh symbol: a private object
      // gets no shared or array read-from constraint, so this is the only
      // constraint on it, and every use of it is later in the same thread,
      // executed only where the read is. Tying it also where the read does
      // not happen therefore changes no execution, and makes it a plain
      // definition, which the solver's array theory treats as such
      // (arrayst::defined_by_equality) instead of keeping its Ackermann
      // constraints.
      equation.constraint(
        equal_exprt{narrowed_value(variable, read.s_it->ssa_lhs),
                    typecast_exprt::conditional_cast(
                      chain[before], chain_type)},
        "private read constraint " + id2string(variable),
        read.s_it->source);
    }
  }
}
