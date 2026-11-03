/// \file
/// lazy_po: thread symmetry (--thread-symmetry), ordering interchangeable threads
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

std::string lazy_pot::create_thread_symmetry(symex_target_equationt &equation)
{
  // Two adjacent threads i, i+1 that run the same routine from the same
  // values are interchangeable: exchanging what they do maps every execution
  // to one that reaches the same states. In a round-robin schedule the
  // exchange keeps the number of rounds exactly when the two never run in the
  // same round; where both run, their order inside that round reverses, and
  // the exchanged execution needs another round. So `exact` asks
  // cs(i) >=lex cs(i+1) only of schedules where they never share a round, and
  // loses no behaviour at any bound; `strong` asks it of every schedule, which
  // is sound for a reported violation but can move one to up to twice the
  // rounds. Proved in iekke-proofs/Symmetry.lean, symmetry_exact_joins.
  //
  // Creation needs no condition. Threads are numbered in creation order, so i
  // exists whenever i+1 does. In a schedule the ordering excludes, neither
  // has run before the first round where their vectors differ, since in
  // `exact` they never share a round, and from then on the exchange gives
  // each a block the other ran, at a time the other existed.
  //
  // Identities: pthread_self and pthread_equal tell two threads apart, so
  // either declines the whole program. The mutex owner and the exit flag also
  // hold identities, but a thread only ever compares them with its own, so
  // exchanging identities along with the threads keeps every step. A join is
  // the one step that looks at another thread's identity: pthread_join(h)
  // waits for exited[h], and the handles main keeps are not exchanged. It
  // cannot tell the two apart when both have exited, so every join must find
  // both exited. That is stated through the schedule, by the exit-flag writes
  // having run, not through the value the join reads, which --narrow-shared
  // may carry only for the element read.
  const auto &steps = equation.SSA_steps;
  std::map<unsigned, irep_idt> routine;
  for(const auto &step : steps)
  {
    if(!step.is_function_call())
      continue;
    const std::string f = id2string(step.called_function);
    if(f == "pthread_self" || f == "pthread_equal")
      return "declined, the program calls " + f;
    const unsigned t = step.source.thread_nr;
    if(
      t == 0 || routine.count(t) != 0 || f.rfind("__CPROVER", 0) == 0 ||
      f == "__spawned_thread" || f.rfind("pthread_", 0) == 0)
      continue;
    routine[t] = step.called_function;
  }

  // A program that reads its own identity outside the pthread model tells
  // the threads apart as well.
  for(const auto &step : steps)
  {
    const std::string f = id2string(step.source.function_id);
    if(
      f.rfind("pthread_", 0) == 0 || f == "__spawned_thread" ||
      f.rfind("__CPROVER", 0) == 0)
      continue;
    // The instruction, not the SSA step: the mutex model compares the owner
    // with the identity, and symex merges that condition into the guards and
    // phi assignments of the caller's later steps.
    bool reads_id = false;
    auto look = [&reads_id](const exprt &e) {
      e.visit_pre([&reads_id](const exprt &x) {
        if(
          x.id() == ID_symbol &&
          to_symbol_expr(x).get_identifier() == "__CPROVER_thread_id")
          reads_id = true;
      });
    };
    look(step.source.pc->code());
    if(step.source.pc->has_condition())
      look(step.source.pc->condition());
    if(reads_id)
      return "declined, the program reads __CPROVER_thread_id";
  }

  // The values a thread starts from: the parameters of its routine and of the
  // spawning wrapper, except its identity.
  std::map<unsigned, std::map<irep_idt, exprt>> start;
  for(const auto &step : steps)
  {
    const unsigned t = step.source.thread_nr;
    if(!step.is_assignment() || routine.count(t) == 0)
      continue;
    const std::string name = id2string(step.ssa_lhs.get_object_name());
    const std::string own = id2string(routine.at(t)) + "::";
    const bool param =
      (name.rfind(own, 0) == 0 || name.rfind("__spawned_thread::", 0) == 0) &&
      name != "__spawned_thread::this_thread_id";
    if(!param || !ns.lookup(name).is_parameter)
      continue;
    start[t].emplace(name, step.ssa_rhs);
  }

  // Exchanging the threads exchanges label l of one with label l of the
  // other, so both must run the same accesses at the same labels.
  std::map<unsigned, std::vector<std::tuple<unsigned, unsigned, unsigned>>>
    shape;
  for(const auto *events : {&reads, &writes})
    for(const auto &entry : *events)
      for(const auto &e : entry.second)
        shape[e.thread].emplace_back(
          e.label, e.num, e.s_it->source.pc->location_number);
  for(auto &s : shape)
    std::sort(s.second.begin(), s.second.end());

  const auto is_exited = [](const irep_idt &v) {
    return id2string(v).rfind("__CPROVER_threads_exited", 0) == 0;
  };
  // thread t has written its exit flag before thread `at` takes its turn in
  // round r
  auto exited_before = [&](unsigned t, unsigned at, std::size_t r) {
    exprt::operandst any;
    for(const auto &entry : writes)
      if(is_exited(entry.first))
        for(const auto &w : entry.second)
          if(w.thread == t)
            for(std::size_t q = 1; q <= r; ++q)
              if(q < r || t < at)
                any.push_back(create_exec_symbol(w.label, w.num, t, q));
    return disjunction(any);
  };

  // thread t runs in round r: its context-switch point moves
  auto runs = [&](unsigned t, std::size_t r) {
    exprt::operandst moved;
    for(unsigned l = 1; l <= labels[t] + 1; ++l)
      moved.push_back(and_exprt{
        create_ge_symbol(t, r, l), not_exprt{create_ge_symbol(t, r - 1, l)}});
    return disjunction(moved);
  };

  std::size_t pairs = 0;
  for(const auto &entry : routine)
  {
    const unsigned i = entry.first, j = i + 1;
    const auto next = routine.find(j);
    if(next == routine.end() || next->second != entry.second)
      continue;
    const bool debug = getenv("LAZYPO_SYMMETRY_DEBUG") != nullptr;
    if(labels[i] != labels[j] || shape[i] != shape[j])
    {
      if(debug)
        std::cerr << "SYMMETRY T" << i << " T" << j << " differ in shape: labels "
                  << labels[i] << "/" << labels[j] << " events "
                  << shape[i].size() << "/" << shape[j].size() << "\n";
      continue;
    }
    if(start[i].empty() || start[i].size() != start[j].size())
    {
      if(debug)
        std::cerr << "SYMMETRY T" << i << " T" << j << " differ in start values "
                  << start[i].size() << "/" << start[j].size() << "\n";
      continue;
    }

    exprt::operandst premise;
    bool same_names = true;
    for(const auto &value : start[i])
    {
      const auto other = start[j].find(value.first);
      if(other == start[j].end() || other->second.type() != value.second.type())
      {
        same_names = false;
        break;
      }
      premise.push_back(equal_exprt{value.second, other->second});
    }
    if(!same_names)
      continue;

    // Only the joins: a thread's own exit-flag write is a read-modify-write
    // of the whole array in the SSA, and reads the flags too.
    for(const auto &entry : reads)
      if(is_exited(entry.first))
        for(const auto &join : entry.second)
          if(id2string(join.s_it->source.function_id) == "pthread_join")
            for(std::size_t r = 1; r <= rounds; ++r)
              premise.push_back(implies_exprt{
                create_exec_symbol(join.label, join.num, join.thread, r),
                and_exprt{
                  exited_before(i, join.thread, r),
                  exited_before(j, join.thread, r)}});

    exprt::operandst lex, prefix_equal;
    for(std::size_t r = 1; r <= rounds; ++r)
    {
      const exprt run_i = runs(i, r), run_j = runs(j, r);
      if(thread_symmetry == 1)
        premise.push_back(not_exprt{and_exprt{run_i, run_j}});

      exprt::operandst eq, geq;
      for(unsigned l = 1; l <= labels[i] + 1; ++l)
      {
        const symbol_exprt gi = create_ge_symbol(i, r, l);
        const symbol_exprt gj = create_ge_symbol(j, r, l);
        eq.push_back(equal_exprt{gi, gj});
        geq.push_back(implies_exprt{gj, gi});
      }
      lex.push_back(
        implies_exprt{conjunction(prefix_equal), conjunction(geq)});
      prefix_equal.push_back(conjunction(eq));
    }
    // Known-answer probe: force the first pair into a schedule the ordering
    // excludes (j runs in round 1, i never runs). With the ordering the
    // formula has no model; with LAZYPO_SYMMETRY_PROBE=only it keeps one.
    const char *probe = getenv("LAZYPO_SYMMETRY_PROBE");
    // LAZYPO_SYMMETRY_PROBE=share forces instead a schedule where both run
    // in round 2 after only j ran in round 1: exact keeps it, strong does not.
    if(probe != nullptr && pairs == 0)
    {
      exprt::operandst forced{runs(j, 1), not_exprt{runs(i, 1)}};
      if(std::string(probe) == "share" && rounds >= 2)
      {
        forced.push_back(runs(i, 2));
        forced.push_back(runs(j, 2));
      }
      else
        for(std::size_t r = 2; r <= rounds; ++r)
          forced.push_back(not_exprt{runs(i, r)});
      equation.constraint(
        conjunction(forced), "thread symmetry probe", steps.begin()->source);
    }
    if(probe == nullptr || std::string(probe) != "only")
      equation.constraint(
        implies_exprt{conjunction(premise), conjunction(lex)},
        "thread symmetry",
        steps.begin()->source);
    ++pairs;
  }
  return std::to_string(pairs) + (pairs == 1 ? " pair" : " pairs") + " of " +
         std::to_string(routine.size()) + " threads";
}

