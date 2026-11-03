/*******************************************************************\

Module: Static round bound for the round-robin (lazy_po) encoding

\*******************************************************************/

/// \file
/// See round_bound.h.

#include "round_bound.h"

#include <util/invariant.h>

#include <algorithm>
#include <functional>
#include <set>
#include <string>

// Take one execution and its happens-before order over atomic blocks: program
// order inside a thread plus the conflict edges between threads (read-from,
// write-write, read-then-overwrite -- any two accesses of one object, at least
// one a write). Call an edge from a block of thread i to a block of thread j
// *backward* when j < i. Then
//
//   R(execution) = 1 + max #backward edges on a happens-before path
//
// rounds suffice to schedule it: give each block the round 1 + (backward
// edges on the heaviest path into it) and order blocks by (round, thread,
// label). A forward or program-order edge never lowers the round and, in the
// same round, goes to a later-or-equal thread; a backward edge raises it by
// one; a thread's blocks in one round stay contiguous. That is a valid
// round-robin schedule, and it is equivalent to the execution because it
// keeps the order of every conflicting pair, so it reaches the same states.
//
// No execution is available here, only every block the unwound program may
// execute and every conflict it may have, so both bounds below over-
// approximate the maximum over all executions:
//
//   count  1 + #blocks (j, l) that some backward edge can enter: l accesses an
//          object that a thread i > j also accesses, at least one side
//          writing. Each backward edge on a path enters a distinct such block.
//   path   1 + max backward edges on a path through the static conflict graph
//          that visits each thread's blocks in increasing label order (a real
//          happens-before path must). Never above count; exponential in the
//          number of threads, so it is capped and falls back to count.
//
// One ordering fact is used: thread i cannot affect anything its ancestor a
// did before spawning (the subtree containing) i, so a backward edge from i
// into a only reaches labels after that spawn. Without it, the spawning
// thread's own write of the child's active flag, and everything before it,
// would count as reachable from the child.
//
// Valid only for the program symex produced: with a loop or recursion bound
// hit ("Unwinding incomplete"), or a thread-spawn loop cut by the thread-
// creation bound, it bounds the truncated program.
// Ancestors of each thread, with the label at which each ancestor spawned the
// child leading to it.
static std::map<unsigned, std::vector<std::pair<unsigned, unsigned>>>
ancestor_chains(const spawn_pointst &spawn_points)
{
  std::map<unsigned, std::vector<std::pair<unsigned, unsigned>>> ancestors;
  for(const auto &sp : spawn_points)
  {
    unsigned child = sp.first;
    auto &chain = ancestors[child];
    std::set<unsigned> seen{child};
    while(true)
    {
      const auto it = spawn_points.find(child);
      if(it == spawn_points.end() || !seen.insert(it->second.first).second)
        break;
      chain.emplace_back(it->second.first, it->second.second);
      child = it->second.first;
    }
  }
  return ancestors;
}

round_boundt compute_round_bound(
  const std::vector<round_bound_eventt> &events,
  const spawn_pointst &spawn_points,
  std::size_t max_rounds)
{
  const auto ancestors = ancestor_chains(spawn_points);
  // Can thread `from` reach label `label` of thread `to` by a direct edge?
  const auto edge_feasible =
    [&ancestors](unsigned from, unsigned to, unsigned label) {
      const auto it = ancestors.find(from);
      if(it == ancestors.end())
        return true;
      for(const auto &anc : it->second)
        if(anc.first == to)
          return label > anc.second;
      return true;
    };

  // Per object, which threads access it and which of them write it.
  struct object_accesst
  {
    std::set<unsigned> accessing;
    std::set<unsigned> writing;
  };
  std::map<irep_idt, object_accesst> objects;
  // Per block (thread, label): objects read, objects written.
  std::map<std::pair<unsigned, unsigned>, std::pair<std::set<irep_idt>, std::set<irep_idt>>>
    blocks;
  for(const auto &e : events)
  {
    objects[e.object].accessing.insert(e.thread);
    if(e.write)
    {
      objects[e.object].writing.insert(e.thread);
      blocks[{e.thread, e.label}].second.insert(e.object);
    }
    else
      blocks[{e.thread, e.label}].first.insert(e.object);
  }
  // Objects one thread alone touches cannot carry an edge.
  for(auto it = blocks.begin(); it != blocks.end();)
  {
    const auto shared = [&objects](const std::set<irep_idt> &objs) {
      for(const auto &x : objs)
        if(objects.at(x).accessing.size() > 1)
          return true;
      return false;
    };
    if(!shared(it->second.first) && !shared(it->second.second))
      it = blocks.erase(it);
    else
      ++it;
  }

  // count: blocks a backward edge can enter.
  std::size_t backward_targets = 0;
  for(const auto &entry : blocks)
  {
    const unsigned j = entry.first.first;
    const unsigned l = entry.first.second;
    bool target = false;
    const auto check = [&](const irep_idt &x, bool block_writes) {
      const auto &acc = objects.at(x);
      for(const unsigned i : block_writes ? acc.accessing : acc.writing)
        if(i > j && edge_feasible(i, j, l))
          return true;
      return false;
    };
    for(const auto &x : entry.second.second)
      if(!target && check(x, true))
        target = true;
    for(const auto &x : entry.second.first)
      if(!target && check(x, false))
        target = true;
    if(target)
      ++backward_targets;
  }
  round_boundt result{1 + backward_targets, 1 + backward_targets, false, false};
  // min(., max_rounds) of a bound is a bound on min(true value, max_rounds).
  const auto clamp = [max_rounds](round_boundt &r) {
    if(max_rounds == 0)
      return;
    if(r.path >= max_rounds)
    {
      r.path = max_rounds;
      r.at_max_rounds = true;
    }
    r.count = std::min(r.count, max_rounds);
  };

  // path: longest backward-weighted path, each thread's blocks visited in
  // increasing label order. State = (current thread, last label visited in
  // every thread); a smaller last label dominates a larger one, so moving out
  // of the current thread always leaves from the earliest block that has the
  // edge.
  std::vector<unsigned> thread_ids;
  std::map<unsigned, std::vector<unsigned>> thread_labels; // sorted
  for(const auto &entry : blocks)
    thread_labels[entry.first.first].push_back(entry.first.second);
  for(const auto &tl : thread_labels)
    thread_ids.push_back(tl.first);
  const std::size_t n = thread_ids.size();
  if(n < 2)
  {
    result.path_exact = true;
    clamp(result);
    return result;
  }

  // Conflict lists: for block v and thread index a, the sorted labels of a's
  // blocks that conflict with v. Built per object, so the cost follows the
  // conflicts that exist rather than all pairs of blocks; bounded so that a
  // program with one heavily shared object does not build a quadratic table.
  std::map<unsigned, std::size_t> thread_index;
  for(std::size_t a = 0; a < n; ++a)
    thread_index[thread_ids[a]] = a;
  // object -> blocks that access it, and whether each one writes it
  std::map<irep_idt, std::vector<std::pair<std::pair<unsigned, unsigned>, bool>>>
    object_blocks;
  for(const auto &entry : blocks)
  {
    for(const auto &x : entry.second.first)
      if(!entry.second.second.count(x))
        object_blocks[x].push_back({entry.first, false});
    for(const auto &x : entry.second.second)
      object_blocks[x].push_back({entry.first, true});
  }
  const std::size_t max_pairs = 20000000;
  std::size_t pairs = 0;
  std::map<std::pair<unsigned, unsigned>, std::vector<std::set<unsigned>>>
    conflict_sets;
  for(const auto &entry : object_blocks)
    for(const auto &u : entry.second)
      for(const auto &v : entry.second)
      {
        if(u.first.first == v.first.first || !(u.second || v.second))
          continue;
        auto &per_thread = conflict_sets[v.first];
        per_thread.resize(n);
        per_thread[thread_index.at(u.first.first)].insert(u.first.second);
        if(++pairs > max_pairs)
        {
          clamp(result);
          return result;
        }
      }
  std::map<std::pair<unsigned, unsigned>, std::vector<std::vector<unsigned>>>
    conflicts_with;
  for(const auto &entry : blocks)
  {
    auto &per_thread = conflicts_with[entry.first];
    per_thread.resize(n);
    const auto cs = conflict_sets.find(entry.first);
    if(cs != conflict_sets.end())
      for(std::size_t a = 0; a < n; ++a)
        per_thread[a].assign(cs->second[a].begin(), cs->second[a].end());
  }

  // Memoised search; the key packs (current thread, last labels). Two caps:
  // states (each one a vector), and candidate transitions examined, since
  // every state scans every block of every other thread.
  const std::size_t max_states = 1000000;
  const std::size_t max_work = 200000000;
  std::size_t work = 0;
  std::map<std::vector<unsigned>, std::size_t> memo;
  bool capped = false;
  // Early exit: the DFS walks real paths from a start state, so `prefix` is
  // the number of backward edges already on the one being explored; reaching
  // max_rounds - 1 proves path >= max_rounds, and nothing more is needed.
  bool reached = false;
  const std::size_t target = max_rounds > 0 ? max_rounds - 1 : 0;
  std::function<std::size_t(std::vector<unsigned> &, std::size_t)> best =
    [&](std::vector<unsigned> &state, std::size_t prefix) -> std::size_t {
    // state[0] = index of the current thread, state[1 + a] = last label in a
    const auto m = memo.find(state);
    if(m != memo.end())
      return m->second;
    if(reached)
      return 0;
    if(capped || memo.size() >= max_states || work >= max_work)
    {
      capped = true;
      return 0;
    }
    const std::size_t cur = state[0];
    const unsigned cur_last = state[1 + cur];
    std::size_t value = 0;
    for(std::size_t t = 0; t < n && !capped && !reached; ++t)
    {
      if(t == cur)
        continue;
      for(const unsigned l : thread_labels[thread_ids[t]])
      {
        ++work;
        if(l <= state[1 + t])
          continue;
        if(!edge_feasible(thread_ids[cur], thread_ids[t], l))
          continue;
        // earliest block of the current thread, at or after where we are,
        // that conflicts with (t, l)
        const auto &from = conflicts_with.at({thread_ids[t], l})[cur];
        const auto it = std::lower_bound(from.begin(), from.end(), cur_last);
        if(it == from.end())
          continue;
        std::vector<unsigned> next = state;
        next[0] = static_cast<unsigned>(t);
        next[1 + cur] = *it;
        next[1 + t] = l;
        const std::size_t step = thread_ids[t] < thread_ids[cur] ? 1 : 0;
        if(max_rounds > 0 && prefix + step >= target)
        {
          reached = true;
          return 0;
        }
        value = std::max(value, step + best(next, prefix + step));
        if(reached)
          return 0;
      }
    }
    memo.emplace(state, value);
    return value;
  };

  std::size_t longest = 0;
  for(std::size_t t = 0; t < n && !capped && !reached; ++t)
  {
    std::vector<unsigned> start(n + 1, 0);
    start[0] = static_cast<unsigned>(t);
    start[1 + t] = thread_labels[thread_ids[t]].front();
    longest = std::max(longest, best(start, 0));
  }
  if(reached)
  {
    result.path = max_rounds;
    result.path_exact = true;
    clamp(result);
    return result;
  }
  if(!capped)
  {
    result.path = 1 + longest;
    result.path_exact = true;
    INVARIANT(
      result.path <= result.count,
      "every backward edge on a path enters a distinct backward target");
  }
  clamp(result);
  return result;
}

// The cone is closed downward in program order, so it is one label per
// thread: limit[t] = the last block of t in it (0: none, labels start at 1).
// A thread's limit only grows, and each growth scans the newly covered reads
// once; an object's writers in a thread are raised to the last of them the
// first time a feasible reader in the cone asks, after which nothing about
// that (object, thread) pair can change.
property_conet property_cone(
  const std::vector<round_bound_eventt> &events,
  const spawn_pointst &spawn_points,
  const std::map<unsigned, unsigned> &property_blocks)
{
  const auto ancestors = ancestor_chains(spawn_points);
  // As edge_feasible in compute_round_bound: thread `from` cannot affect what
  // its ancestor `to` did before spawning it.
  const auto feasible = [&ancestors](unsigned from, unsigned to, unsigned label) {
    const auto it = ancestors.find(from);
    if(it == ancestors.end())
      return true;
    for(const auto &anc : it->second)
      if(anc.first == to)
        return label > anc.second;
    return true;
  };

  // object -> writing thread -> its last write of the object
  std::map<irep_idt, std::map<unsigned, unsigned>> last_write;
  // thread -> (label, object) of its reads, by label
  std::map<unsigned, std::vector<std::pair<unsigned, irep_idt>>> reads_of;
  std::set<std::pair<unsigned, unsigned>> all_blocks;
  for(const auto &e : events)
  {
    all_blocks.insert({e.thread, e.label});
    if(e.write)
    {
      unsigned &last = last_write[e.object][e.thread];
      last = std::max(last, e.label);
    }
    else
      reads_of[e.thread].emplace_back(e.label, e.object);
  }
  for(auto &entry : reads_of)
    std::sort(entry.second.begin(), entry.second.end());

  std::map<unsigned, unsigned> limit;
  std::map<unsigned, unsigned> scanned; // reads of t already followed, by label
  std::set<std::pair<irep_idt, unsigned>> raised; // (object, writing thread)
  std::vector<unsigned> worklist;
  const auto raise = [&](unsigned thread, unsigned label) {
    unsigned &l = limit[thread];
    if(label > l)
    {
      l = label;
      worklist.push_back(thread);
    }
  };
  for(const auto &pb : property_blocks)
    raise(pb.first, pb.second);

  while(!worklist.empty())
  {
    const unsigned t = worklist.back();
    worklist.pop_back();
    const unsigned upto = limit[t];
    unsigned &from = scanned[t];
    if(upto <= from)
      continue;
    // Spawn: t can only run once its parent has reached the spawn.
    if(from == 0)
    {
      const auto sp = spawn_points.find(t);
      if(sp != spawn_points.end())
        raise(sp->second.first, sp->second.second);
    }
    // Flow: whatever a read of t in the cone may read from.
    const auto &reads = reads_of[t];
    auto it = std::upper_bound(
      reads.begin(),
      reads.end(),
      std::make_pair(from, irep_idt{}),
      [](const std::pair<unsigned, irep_idt> &a,
         const std::pair<unsigned, irep_idt> &b) { return a.first < b.first; });
    for(; it != reads.end() && it->first <= upto; ++it)
    {
      const auto lw = last_write.find(it->second);
      if(lw == last_write.end())
        continue;
      for(const auto &writer : lw->second)
        if(
          writer.first != t && !raised.count({it->second, writer.first}) &&
          feasible(writer.first, t, it->first))
        {
          raised.insert({it->second, writer.first});
          raise(writer.first, writer.second);
        }
    }
    from = upto;
  }

  property_conet cone;
  cone.total_blocks = all_blocks.size();
  for(const auto &e : events)
  {
    const auto l = limit.find(e.thread);
    if(l != limit.end() && e.label <= l->second)
      cone.events.push_back(e);
  }
  for(const auto &b : all_blocks)
  {
    const auto l = limit.find(b.first);
    if(l != limit.end() && b.second <= l->second)
      ++cone.blocks;
  }
  return cone;
}

symbol_exprt empty_round_symbol(std::size_t round)
{
  return symbol_exprt{
    "__lazypo_empty_round_R" + std::to_string(round), bool_typet{}};
}

std::size_t &infer_rounds_bound()
{
  static std::size_t bound = 0;
  return bound;
}

bool &infer_rounds_bound_is_static()
{
  static bool is_static = false;
  return is_static;
}

fixpoint_projectiont &fixpoint_projection()
{
  static fixpoint_projectiont projection;
  return projection;
}
