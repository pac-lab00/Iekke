/*******************************************************************\

Module: Static whole-program thread-exclusivity analysis

Author: CBMC/lazy_po work

\*******************************************************************/

/// \file
/// Static, pre-symex, whole-program thread-exclusivity analysis.
///
/// See thread_exclusivity.h for the contract. This file documents the
/// soundness argument, because the whole point of the analysis is to let
/// goto-symex assume that nothing else can interfere with a variable, and
/// a wrong answer here means silently reporting "no bug found" on a buggy
/// program.
///
/// SOUNDNESS ARGUMENT
/// ==================
///
/// Let v be a returned variable. We must show: over any execution of the
/// program, at most one thread performs an access to v.
///
/// (1) v's address is never taken anywhere in the program (checked with
///     dirtyt over the whole goto_functionst). Hence no pointer can ever
///     hold v's address, and every access to v is a syntactic occurrence
///     of v's identifier in some instruction. So it is enough to reason
///     about which threads can execute which *instructions*.
///
/// (2) Every FUNCTION_CALL in the program has a symbol (not a
///     dereference) as its callee. This holds after the standard
///     remove_function_pointers pass. If it does not, we give up on the
///     whole program: an unresolved indirect call means we cannot bound
///     which code a thread runs. So the call graph is fully known.
///
/// (3) Every START_THREAD in the program lies in the body of
///     `pthread_create`, i.e. threads are created only through CBMC's own
///     pthread model. Otherwise we give up on the whole program.
///     Consequently the set of *thread instances* in any execution is
///     { the initial thread } union { one instance per execution of a
///     pthread_create call site }.
///
/// (4) Every pthread_create call site passes a literal function address
///     as its start routine (argument 2, modulo typecasts). Otherwise we
///     give up on the whole program. So the set of possible start
///     routines is exactly the finite set `roots` we collect.
///
/// (5) Reachability. We compute, for each root r (and for the program
///     entry point, which is the initial thread's root), the set of
///     functions reach(r) reachable from r along direct calls, *without
///     descending into thread-spawn regions* (the instructions between a
///     START_THREAD's target and its matching END_THREAD belong to the
///     spawned thread, not to the spawning one). We additionally compute
///     `infra`: the functions reachable from the callees that appear
///     inside spawn regions, with root functions treated as leaves. In
///     CBMC's pthread model `infra` is `__spawned_thread` and whatever it
///     calls other than the start routine itself -- code that every
///     spawned thread runs. Any variable mentioned in a spawn-region
///     instruction or in a function in `infra` is therefore rejected
///     outright.
///
/// (6) A variable v is only considered if the set of roots r with
///     `v mentioned somewhere in reach(r)` has size exactly one. Note
///     reach(entry) *does* descend into a root function that is also
///     called directly (a plain, non-dispatch call), so a variable
///     touched both by the initial thread and by a spawned thread is
///     correctly seen as touched by two roots.
///
/// (7) For the single surviving root r we must still show that at most
///     one thread instance executes reach(r). A thread instance executes
///     r's body only if it reaches a call to r. Calls to r are of two
///     kinds:
///       (a) calls from a function in `infra` -- the dispatch that
///           remove_function_pointers generated for `start_routine(arg)`.
///           We *check* that each such call site is guarded: some GOTO in
///           the same function targets the call instruction and its
///           condition mentions address_of(r), and the call instruction
///           cannot be entered by fall-through (the instruction textually
///           before it is an unconditional GOTO or an ASSUME(false)).
///           Hence that call executes only when the dispatched pointer
///           equals address_of(r).
///       (b) calls from anywhere else. Those are ordinary calls and are
///           followed by reach(), so they are already accounted for by
///           (6): they put r's mentions under the calling root as well.
///           If the caller belongs to a second root, (6) rejects v.
///     Additionally we check (R3): every occurrence of address_of(r) in
///     the whole program is either the start-routine argument of a
///     pthread_create call site, or inside the condition of a GOTO in a
///     function in `infra`. Therefore the only way any pointer value can
///     ever be address_of(r) is by flowing from a pthread_create start
///     routine argument, so a thread whose dispatch pointer equals
///     address_of(r) is a thread that was spawned with r as its start
///     routine.
///
/// (8) Finally we check that r can be spawned at most once: exactly one
///     pthread_create call site names r, that call site is not inside a
///     loop, and its enclosing function provably runs at most once (a
///     chain of single, non-looping call sites up to the program entry
///     point; anything else, including recursion or being callable from
///     inside a spawn region, fails).
///
/// (9) Prologue. Step (6) counts the initial thread as touching v if any
///     function in reach(entry) mentions v. That is too strong for code
///     that provably runs before *any* thread has been spawned: while it
///     runs there is only one thread in existence, so its accesses cannot
///     race with anything and must not be counted as a second toucher.
///     (Without this, CBMC's own zero-initialisation of every global in
///     __CPROVER_initialize would make every global look like it is
///     touched by the initial thread, and nothing would ever qualify.)
///     So we exclude from reach(entry), when counting, the functions in a
///     set `prologue`.
///
///     Crucially this is a property of *call contexts*, not of functions.
///     A helper reachable from __CPROVER_initialize (via a C
///     `__attribute__((constructor))` function or a C++ static
///     initialiser, say) can also be called from main *after* threads have
///     been spawned; that second call is a genuine initial-thread access
///     and must be counted. We therefore admit a function into `prologue`
///     only if *every* call site of it in the whole program is
///     prologue-safe -- either directly in the entry function, outside any
///     loop and spawn region, strictly before the first call there that
///     can reach a thread spawn, or inside a function already in
///     `prologue` -- and only if it cannot itself reach a thread spawn and
///     is neither a start routine nor shared spawn infrastructure. This is
///     a least fixpoint (see compute_prologue_functions), so recursion
///     among candidates simply never enters the set. Since the analysis
///     has bailed out on any indirect call (2), `call_sites` is a complete
///     record of every way a function can be entered other than being a
///     start routine, which is excluded; hence every execution of a
///     `prologue` function finishes before any thread is spawned.
///
/// Combining (7) and (8): at most one thread instance ever executes any
/// function in reach(r), and by (6) and (9) no other root's code, and no
/// non-prologue initial-thread code, mentions v, and by (5) neither the
/// shared spawn infrastructure nor a spawn region mentions v, and by (1)
/// there is no aliasing path to v. Hence at most one thread accesses v
/// while any other thread exists.
///
/// Every check above fails "closed": on anything unexpected the variable
/// (or the whole program) is simply not reported, and the caller keeps
/// today's behaviour.

#include "thread_exclusivity.h"

#include <util/cprover_prefix.h>
#include <util/expr_util.h>
#include <util/namespace.h>
#include <util/prefix.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>
#include <util/symbol.h>
#include <util/symbol_table_base.h>

#include <analyses/dirty.h>
#include <goto-programs/goto_functions.h>

#include <cstdlib>
#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace
{
using instruction_ptrt = const goto_programt::instructiont *;

/// Collect the identifiers of all symbols syntactically occurring in \p expr.
void collect_symbols(const exprt &expr, std::unordered_set<irep_idt> &result)
{
  if(expr.id() == ID_symbol)
    result.insert(to_symbol_expr(expr).get_identifier());

  for(const auto &op : expr.operands())
    collect_symbols(op, result);
}

/// Does \p expr contain `address_of(symbol <identifier>)` anywhere?
bool contains_address_of(const exprt &expr, const irep_idt &identifier)
{
  if(expr.id() == ID_address_of && expr.operands().size() == 1)
  {
    const exprt &object = skip_typecast(to_address_of_expr(expr).object());
    if(
      object.id() == ID_symbol &&
      to_symbol_expr(object).get_identifier() == identifier)
    {
      return true;
    }
  }

  for(const auto &op : expr.operands())
    if(contains_address_of(op, identifier))
      return true;

  return false;
}

/// Apply \p visitor to every expression of \p instruction that can mention a
/// variable. This is goto_programt::instructiont::apply() plus the two things
/// it deliberately leaves out but that we must not miss: the callee
/// expression of a FUNCTION_CALL, and the full code of an OTHER instruction
/// (apply() only descends into ID_expression there, while OTHER also covers
/// array_set/array_copy/havoc_object/decl/asm/... which can mention
/// variables).
void for_each_expression(
  const goto_programt::instructiont &instruction,
  const std::function<void(const exprt &)> &visitor)
{
  instruction.apply(visitor);

  if(instruction.is_function_call())
    visitor(instruction.call_function());

  if(instruction.is_other())
    visitor(instruction.get_other());
}

/// Precomputed per-function information.
struct function_infot
{
  std::vector<instruction_ptrt> instructions;
  std::unordered_map<instruction_ptrt, std::size_t> position;
  /// Instruction belongs to a thread-spawn region, i.e. it is executed by a
  /// spawned thread and not by the thread running this function.
  std::vector<bool> in_spawn_region;
  /// Instruction is spanned by a backward branch, so it may be in a loop.
  std::vector<bool> in_loop;
};

struct call_sitet
{
  irep_idt caller;
  std::size_t position;
  bool in_spawn_region;
  bool in_loop;
};

class thread_exclusivity_analysist
{
public:
  thread_exclusivity_analysist(
    const goto_functionst &goto_functions,
    const namespacet &ns)
    : goto_functions(goto_functions), ns(ns), dirty(goto_functions)
  {
  }

  std::unordered_set<irep_idt> operator()();

private:
  const goto_functionst &goto_functions;
  const namespacet &ns;
  dirtyt dirty;

  bool bailed = false;

  std::unordered_map<irep_idt, function_infot> infos;
  /// callee identifier -> all direct call sites of it
  std::unordered_map<irep_idt, std::vector<call_sitet>> call_sites;
  /// caller -> direct callees, from instructions outside spawn regions
  std::unordered_map<irep_idt, std::unordered_set<irep_idt>> callees;
  /// direct callees appearing inside spawn regions
  std::unordered_set<irep_idt> spawn_region_callees;
  /// function -> variables mentioned, from instructions outside spawn regions
  std::unordered_map<irep_idt, std::unordered_set<irep_idt>> mentions;
  /// variables mentioned by spawn-region instructions anywhere
  std::unordered_set<irep_idt> spawn_region_mentions;

  std::unordered_set<irep_idt> roots;
  /// root -> the pthread_create call sites naming it
  std::unordered_map<irep_idt, std::vector<call_sitet>> spawn_sites_of;
  std::unordered_set<irep_idt> infra;
  /// Functions whose execution by the initial thread provably completes
  /// before any thread is spawned (see compute_prologue_functions).
  std::unordered_set<irep_idt> prologue;

  std::unordered_map<irep_idt, int> runs_once_cache; // -1 in progress

  void build_function_info(const irep_idt &id, const goto_programt &body);
  void scan_instructions();
  bool collect_roots();
  std::unordered_set<irep_idt> reachable_from(
    const std::unordered_set<irep_idt> &seeds,
    const std::unordered_set<irep_idt> &stop_at) const;
  bool runs_at_most_once(const irep_idt &function_id);
  void compute_prologue_functions();
  bool root_dispatch_is_exclusive(const irep_idt &root) const;
  bool root_spawned_at_most_once(const irep_idt &root);

  const goto_programt *body_of(const irep_idt &id) const
  {
    const auto it = goto_functions.function_map.find(id);
    if(it == goto_functions.function_map.end() || !it->second.body_available())
      return nullptr;
    return &it->second.body;
  }
};

void thread_exclusivity_analysist::build_function_info(
  const irep_idt &id,
  const goto_programt &body)
{
  function_infot &info = infos[id];

  for(const auto &instruction : body.instructions)
  {
    info.position[&instruction] = info.instructions.size();
    info.instructions.push_back(&instruction);
  }

  const std::size_t n = info.instructions.size();
  info.in_spawn_region.assign(n, false);
  info.in_loop.assign(n, false);

  // Loops: in a linearly ordered goto program, any cycle through position k
  // must contain a branch from some position >= k back to some position <= k.
  // Mark every position spanned by such a backward branch. A goto whose
  // target we cannot locate makes the whole function conservatively loopy.
  std::vector<int> delta(n + 1, 0);
  for(std::size_t u = 0; u < n; ++u)
  {
    const goto_programt::instructiont &instruction = *info.instructions[u];
    if(!instruction.is_goto() && !instruction.is_incomplete_goto())
      continue;

    for(const auto &target : instruction.targets)
    {
      const auto found = info.position.find(&*target);
      if(found == info.position.end())
      {
        info.in_loop.assign(n, true);
        break;
      }
      if(found->second <= u)
      {
        ++delta[found->second];
        --delta[u + 1];
      }
    }
  }

  int running = 0;
  for(std::size_t k = 0; k < n; ++k)
  {
    running += delta[k];
    if(running > 0)
      info.in_loop[k] = true;
  }

  // Spawn regions: START_THREAD's target up to the matching END_THREAD,
  // both inclusive (see goto_convertt::generate_thread_block).
  for(std::size_t u = 0; u < n; ++u)
  {
    const goto_programt::instructiont &instruction = *info.instructions[u];
    if(!instruction.is_start_thread())
      continue;

    // Only CBMC's own pthread model is understood.
    if(id != irep_idt("pthread_create"))
    {
      bailed = true;
      return;
    }

    if(instruction.targets.size() != 1)
    {
      bailed = true;
      return;
    }

    const auto target_position = info.position.find(&*instruction.get_target());
    if(target_position == info.position.end() || target_position->second <= u)
    {
      bailed = true;
      return;
    }

    std::size_t depth = 0;
    std::size_t k = target_position->second;
    for(; k < n; ++k)
    {
      info.in_spawn_region[k] = true;
      if(info.instructions[k]->is_end_thread())
      {
        if(depth == 0)
          break;
        --depth;
      }
      else if(info.instructions[k]->is_start_thread())
        ++depth;
    }

    if(k == n)
    {
      // unmatched START_THREAD
      bailed = true;
      return;
    }
  }
}

void thread_exclusivity_analysist::scan_instructions()
{
  for(const auto &entry : infos)
  {
    const irep_idt &function_id = entry.first;
    const function_infot &info = entry.second;

    for(std::size_t k = 0; k < info.instructions.size(); ++k)
    {
      const goto_programt::instructiont &instruction = *info.instructions[k];
      const bool in_region = info.in_spawn_region[k];

      if(instruction.is_function_call())
      {
        const exprt &callee = skip_typecast(instruction.call_function());
        if(callee.id() != ID_symbol)
        {
          // Unresolved indirect call: we cannot bound what this thread runs.
          bailed = true;
          return;
        }

        const irep_idt callee_id = to_symbol_expr(callee).get_identifier();
        call_sites[callee_id].push_back(
          call_sitet{function_id, k, in_region, info.in_loop[k]});

        if(in_region)
          spawn_region_callees.insert(callee_id);
        else
          callees[function_id].insert(callee_id);
      }

      std::unordered_set<irep_idt> &sink =
        in_region ? spawn_region_mentions : mentions[function_id];
      for_each_expression(
        instruction, [&sink](const exprt &e) { collect_symbols(e, sink); });
    }
  }
}

bool thread_exclusivity_analysist::collect_roots()
{
  const auto pthread_create_sites = call_sites.find(irep_idt("pthread_create"));
  if(pthread_create_sites == call_sites.end())
    return false; // no thread creation at all: nothing to do

  for(const auto &site : pthread_create_sites->second)
  {
    const function_infot &info = infos.at(site.caller);
    const goto_programt::instructiont &instruction =
      *info.instructions[site.position];

    const auto &arguments = instruction.call_arguments();
    if(arguments.size() < 3)
      return false;

    const exprt &argument = skip_typecast(arguments[2]);
    if(argument.id() != ID_address_of || argument.operands().size() != 1)
      return false;

    const exprt &object = skip_typecast(to_address_of_expr(argument).object());
    if(object.id() != ID_symbol)
      return false;

    const irep_idt root = to_symbol_expr(object).get_identifier();
    if(body_of(root) == nullptr)
      return false; // start routine without a body: cannot analyse it

    roots.insert(root);
    spawn_sites_of[root].push_back(site);
  }

  return !roots.empty();
}

std::unordered_set<irep_idt> thread_exclusivity_analysist::reachable_from(
  const std::unordered_set<irep_idt> &seeds,
  const std::unordered_set<irep_idt> &stop_at) const
{
  std::unordered_set<irep_idt> result;
  std::vector<irep_idt> worklist;

  // Functions in stop_at are excluded from the result entirely, not merely
  // left unexpanded: they are the start routines, whose bodies are attributed
  // to their own thread root rather than to the caller.
  for(const auto &seed : seeds)
    if(stop_at.count(seed) == 0 && result.insert(seed).second)
      worklist.push_back(seed);

  while(!worklist.empty())
  {
    const irep_idt current = worklist.back();
    worklist.pop_back();

    const auto found = callees.find(current);
    if(found == callees.end())
      continue;

    for(const auto &callee : found->second)
      if(stop_at.count(callee) == 0 && result.insert(callee).second)
        worklist.push_back(callee);
  }

  return result;
}

bool thread_exclusivity_analysist::runs_at_most_once(
  const irep_idt &function_id)
{
  if(function_id == goto_functionst::entry_point())
    return true;

  const auto cached = runs_once_cache.find(function_id);
  if(cached != runs_once_cache.end())
    return cached->second == 1;

  runs_once_cache[function_id] = -1; // detect cycles (recursion)

  bool result = false;
  const auto sites = call_sites.find(function_id);
  if(sites != call_sites.end() && sites->second.size() == 1)
  {
    const call_sitet &site = sites->second.front();
    // A call site inside a spawn region runs once per spawned thread, and a
    // call site inside a loop runs arbitrarily often.
    if(!site.in_spawn_region && !site.in_loop)
      result = runs_at_most_once(site.caller);
  }

  runs_once_cache[function_id] = result ? 1 : 0;
  return result;
}

/// Identify functions whose execution by the initial thread provably finishes
/// before any thread has been spawned. Accesses made there cannot race with
/// anything -- no other thread exists yet -- so they must not be counted when
/// asking how many threads touch a variable. This is the static counterpart of
/// the pre-spawn prologue that lazy_po already sets aside dynamically, and it
/// is what makes a file-scope loop induction variable qualify at all: CBMC
/// zero-initialises every global in __CPROVER_initialize, which would
/// otherwise make every global look like it is touched by the initial thread
/// as well as by its owning thread.
///
/// Prologue membership is a property of a function's *call contexts*, not of
/// the function on its own. A helper that __CPROVER_initialize reaches (say
/// through a C `__attribute__((constructor))` function or a C++ static
/// initialiser) may perfectly well be called a second time from main *after*
/// threads have been spawned, and that second call is not prologue-safe at
/// all. Marking the helper "prologue" wholesale would then silently drop the
/// initial thread's post-spawn accesses from the root count and wrongly call a
/// raced variable thread-exclusive. So we must only fold a function when
/// *every* way of entering it is pre-spawn.
///
/// We therefore compute the set P of prologue functions as the least fixpoint
/// of the rule
///
///   q in P  iff  q has at least one call site, q cannot transitively reach a
///                thread spawn, q is neither the entry point nor a thread
///                start routine nor shared spawn infrastructure, and *every*
///                call site of q in the whole program is prologue-safe, where
///                a call site is prologue-safe if it either
///                  (a) lies directly in the body of the entry function,
///                      outside any loop and outside any spawn region, at a
///                      position strictly before the first call in the entry
///                      function that can reach a thread spawn (the seed
///                      case -- in practice the call to __CPROVER_initialize),
///                      or
///                  (b) lies in a function that is already in P, outside a
///                      spawn region.
///
/// Justification. For (a): the entry function is a linearly ordered goto
/// program, the call site is spanned by no backward branch (`in_loop` is
/// false), and every instruction that can reach a spawn sits at a later
/// position, so the call completes before any thread exists. For (b): by
/// induction every execution of the caller's body is entirely pre-spawn, so
/// in particular so is this call. Since the rule quantifies over *all* call
/// sites of q, and `call_sites` records every direct call in the program
/// (the analysis has already bailed out if any call is indirect, and a
/// function without a body cannot call anything), every execution of q is
/// pre-spawn.
///
/// Starting from the empty set and only ever adding a function all of whose
/// call sites are *already* justified makes this a least fixpoint. A cycle
/// among candidates (direct or mutual recursion) is therefore simply never
/// added, which loses a little precision and is sound. In practice P is
/// {__CPROVER_initialize} plus whatever it alone calls, which is exactly the
/// intent; anything less obvious is left counted.
void thread_exclusivity_analysist::compute_prologue_functions()
{
  const irep_idt entry = goto_functionst::entry_point();
  const irep_idt pthread_create_id("pthread_create");

  // Functions that can transitively reach a thread spawn.
  std::unordered_set<irep_idt> spawn_reaching;
  {
    // Reverse reachability from pthread_create over `callees`.
    std::unordered_map<irep_idt, std::unordered_set<irep_idt>> callers;
    for(const auto &entry_pair : callees)
      for(const auto &callee : entry_pair.second)
        callers[callee].insert(entry_pair.first);

    std::vector<irep_idt> worklist;
    if(spawn_sites_of.empty() && call_sites.count(pthread_create_id) == 0)
      return;
    spawn_reaching.insert(pthread_create_id);
    worklist.push_back(pthread_create_id);
    while(!worklist.empty())
    {
      const irep_idt current = worklist.back();
      worklist.pop_back();
      const auto found = callers.find(current);
      if(found == callers.end())
        continue;
      for(const auto &caller : found->second)
        if(spawn_reaching.insert(caller).second)
          worklist.push_back(caller);
    }
  }

  const auto entry_info = infos.find(entry);
  if(entry_info == infos.end())
    return;
  const function_infot &info = entry_info->second;

  // Earliest position in the entry function from which a spawn may follow.
  std::size_t first_spawn_reaching_call = info.instructions.size();
  for(std::size_t k = 0; k < info.instructions.size(); ++k)
  {
    const goto_programt::instructiont &instruction = *info.instructions[k];
    if(!instruction.is_function_call())
      continue;
    const exprt &callee = skip_typecast(instruction.call_function());
    if(callee.id() != ID_symbol)
      continue;
    if(spawn_reaching.count(to_symbol_expr(callee).get_identifier()) != 0)
    {
      first_spawn_reaching_call = k;
      break;
    }
  }

  // Is this one call site guaranteed to be executed only before any thread
  // has been spawned, given what we already know to be prologue?
  const auto site_is_prologue_safe = [&](const call_sitet &site) {
    if(site.in_spawn_region)
      return false; // executed by the spawned thread, not by this one
    if(prologue.count(site.caller) != 0)
      return true; // case (b): the whole caller runs in the prologue
    // case (a): directly in the entry function, before anything can spawn
    return site.caller == entry && !site.in_loop &&
           site.position < first_spawn_reaching_call;
  };

  // Does every call site of `function_id` satisfy the rule, so that it can be
  // added to the prologue set?
  const auto qualifies = [&](const irep_idt &function_id) {
    if(function_id == entry)
      return false; // the entry function itself spans the whole execution
    if(spawn_reaching.count(function_id) != 0)
      return false; // may itself spawn a thread and then keep running
    // A start routine is entered by a spawned thread, and the shared spawn
    // infrastructure is run by every spawned thread. Neither is covered by
    // the call-site argument, so exclude both explicitly.
    if(roots.count(function_id) != 0 || infra.count(function_id) != 0)
      return false;

    const auto sites = call_sites.find(function_id);
    if(sites == call_sites.end() || sites->second.empty())
      return false; // never called: no call site justifies anything

    for(const auto &site : sites->second)
      if(!site_is_prologue_safe(site))
        return false;

    return true;
  };

  // Least fixpoint: keep adding functions all of whose call sites are already
  // justified, until nothing changes.
  bool changed = true;
  while(changed)
  {
    changed = false;
    for(const auto &info_entry : infos)
    {
      const irep_idt &function_id = info_entry.first;
      if(prologue.count(function_id) == 0 && qualifies(function_id))
      {
        prologue.insert(function_id);
        changed = true;
      }
    }
  }
}

bool thread_exclusivity_analysist::root_dispatch_is_exclusive(
  const irep_idt &root) const
{
  // (R2) Every call to `root` from the shared spawn infrastructure must be a
  // guarded dispatch on address_of(root), and (R3) address_of(root) must not
  // escape anywhere else in the program.
  const auto sites = call_sites.find(root);
  if(sites == call_sites.end())
    return false; // never actually called: not the shape we understand

  for(const auto &site : sites->second)
  {
    if(site.in_spawn_region)
      return false; // called directly from a spawn region: not the model

    if(infra.count(site.caller) == 0)
      continue; // ordinary call, already accounted for by root counting

    const function_infot &info = infos.at(site.caller);

    // No fall-through into the dispatched call.
    if(site.position == 0)
      return false;
    const goto_programt::instructiont &previous =
      *info.instructions[site.position - 1];
    const bool previous_falls_through = !(
      (previous.is_goto() && previous.condition().is_true()) ||
      (previous.is_assume() && previous.condition().is_false()));
    if(previous_falls_through)
      return false;

    // Some GOTO in the same function jumps to this call under a condition
    // mentioning address_of(root).
    bool guarded = false;
    for(std::size_t k = 0; k < info.instructions.size(); ++k)
    {
      const goto_programt::instructiont &instruction = *info.instructions[k];
      if(!instruction.is_goto() || !instruction.has_condition())
        continue;

      bool targets_call = false;
      for(const auto &target : instruction.targets)
      {
        const auto found = info.position.find(&*target);
        if(found != info.position.end() && found->second == site.position)
          targets_call = true;
      }

      if(targets_call && contains_address_of(instruction.condition(), root))
      {
        guarded = true;
        break;
      }
    }

    if(!guarded)
      return false;
  }

  // (R3) Check every occurrence of address_of(root) in the whole program.
  for(const auto &entry : infos)
  {
    const function_infot &info = entry.second;
    for(std::size_t k = 0; k < info.instructions.size(); ++k)
    {
      const goto_programt::instructiont &instruction = *info.instructions[k];

      bool occurs = false;
      for_each_expression(instruction, [&](const exprt &e) {
        if(contains_address_of(e, root))
          occurs = true;
      });
      if(!occurs)
        continue;

      // Allowed: the start-routine argument of a pthread_create call.
      if(
        instruction.is_function_call() &&
        skip_typecast(instruction.call_function()).id() == ID_symbol &&
        to_symbol_expr(skip_typecast(instruction.call_function()))
            .get_identifier() == irep_idt("pthread_create"))
      {
        const auto &arguments = instruction.call_arguments();
        bool only_in_start_routine_argument =
          !contains_address_of(instruction.call_lhs(), root);
        for(std::size_t a = 0; a < arguments.size(); ++a)
          if(a != 2 && contains_address_of(arguments[a], root))
            only_in_start_routine_argument = false;
        if(
          only_in_start_routine_argument && arguments.size() >= 3 &&
          contains_address_of(arguments[2], root))
        {
          continue;
        }
        return false;
      }

      // Allowed: the condition of a dispatch GOTO in the spawn
      // infrastructure.
      if(
        instruction.is_goto() && instruction.has_condition() &&
        infra.count(entry.first) != 0)
      {
        continue;
      }

      return false;
    }
  }

  return true;
}

bool thread_exclusivity_analysist::root_spawned_at_most_once(
  const irep_idt &root)
{
  const auto sites = spawn_sites_of.find(root);
  if(sites == spawn_sites_of.end() || sites->second.size() != 1)
    return false;

  const call_sitet &site = sites->second.front();
  if(site.in_spawn_region || site.in_loop)
    return false;

  return runs_at_most_once(site.caller);
}

std::unordered_set<irep_idt> thread_exclusivity_analysist::operator()()
{
  const bool debug = getenv("LAZYPO_EXCLUSIVITY_DEBUG") != nullptr;

  for(const auto &entry : goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    build_function_info(entry.first, entry.second.body);
    if(bailed)
    {
      if(debug)
        std::cerr << "EXCLUSIVITY bail: unsupported thread spawn in "
                  << entry.first << "\n";
      return {};
    }
  }

  scan_instructions();
  if(bailed)
  {
    if(debug)
      std::cerr << "EXCLUSIVITY bail: unresolved indirect call\n";
    return {};
  }

  if(!collect_roots())
  {
    if(debug)
      std::cerr << "EXCLUSIVITY bail: no analysable thread entry points\n";
    return {};
  }

  if(infos.find(goto_functionst::entry_point()) == infos.end())
  {
    if(debug)
      std::cerr << "EXCLUSIVITY bail: no entry point body\n";
    return {};
  }

  // Shared spawn infrastructure: everything reachable from the callees found
  // inside spawn regions, with the start routines themselves treated as
  // leaves. Every spawned thread runs this code.
  infra = reachable_from(spawn_region_callees, roots);

  // Per-root reachable function sets. reach(entry) is the initial thread.
  std::unordered_map<irep_idt, std::unordered_set<irep_idt>> reach;
  reach[goto_functionst::entry_point()] =
    reachable_from({goto_functionst::entry_point()}, {});
  for(const auto &root : roots)
    reach[root] = reachable_from({root}, {});

  // Variables that the shared spawn infrastructure touches are touched by
  // every spawned thread.
  std::unordered_set<irep_idt> blacklist = spawn_region_mentions;
  for(const auto &function_id : infra)
  {
    const auto found = mentions.find(function_id);
    if(found != mentions.end())
      blacklist.insert(found->second.begin(), found->second.end());
  }

  // Candidate variables: shared, static-lifetime, address never taken.
  std::unordered_set<irep_idt> candidates;
  for(const auto &entry : ns.get_symbol_table().symbols)
  {
    const symbolt &symbol = entry.second;
    if(!symbol.is_static_lifetime || !symbol.is_shared())
      continue;
    if(symbol.type.id() == ID_code || symbol.type.id() == ID_empty)
      continue;
    if(symbol.is_type || symbol.is_macro)
      continue;
    // CBMC's own bookkeeping globals are deliberately out of scope. Several of
    // them are read and written by machinery whose accesses are not plain
    // syntactic mentions in the goto program (allocation, thread bookkeeping,
    // dynamic-object handling), so a syntactic scan is not a sound basis for
    // claiming exclusivity over them -- and folding them buys nothing for the
    // loop-unwinding problem this analysis exists to solve.
    if(has_prefix(id2string(symbol.name), CPROVER_PREFIX))
      continue;
    if(dirty(symbol.name))
      continue;
    if(blacklist.count(symbol.name) != 0)
      continue;
    candidates.insert(symbol.name);
  }

  compute_prologue_functions();

  // For each candidate, which roots mention it?
  std::unordered_map<irep_idt, std::unordered_set<irep_idt>> roots_touching;
  for(const auto &reach_entry : reach)
  {
    const bool is_initial_thread =
      reach_entry.first == goto_functionst::entry_point();

    for(const auto &function_id : reach_entry.second)
    {
      // Pre-spawn prologue code of the initial thread does not count: no
      // other thread exists while it runs.
      if(is_initial_thread && prologue.count(function_id) != 0)
        continue;

      const auto found = mentions.find(function_id);
      if(found == mentions.end())
        continue;
      for(const auto &identifier : found->second)
        if(candidates.count(identifier) != 0)
          roots_touching[identifier].insert(reach_entry.first);
    }
  }

  std::unordered_set<irep_idt> result;
  for(const auto &entry : roots_touching)
  {
    if(entry.second.size() != 1)
    {
      if(debug)
        std::cerr << "EXCLUSIVITY reject " << entry.first << ": "
                  << entry.second.size() << " roots\n";
      continue;
    }

    const irep_idt &root = *entry.second.begin();
    if(root != goto_functionst::entry_point())
    {
      if(!root_dispatch_is_exclusive(root))
      {
        if(debug)
          std::cerr << "EXCLUSIVITY reject " << entry.first
                    << ": dispatch of root " << root << " not exclusive\n";
        continue;
      }
      if(!root_spawned_at_most_once(root))
      {
        if(debug)
          std::cerr << "EXCLUSIVITY reject " << entry.first << ": root "
                    << root << " may be spawned more than once\n";
        continue;
      }
    }

    result.insert(entry.first);
  }

  if(debug)
  {
    std::cerr << "EXCLUSIVITY roots=";
    for(const auto &root : roots)
      std::cerr << root << " ";
    std::cerr << "\nEXCLUSIVITY infra=";
    for(const auto &function_id : infra)
      std::cerr << function_id << " ";
    std::cerr << "\nEXCLUSIVITY prologue=";
    for(const auto &function_id : prologue)
      std::cerr << function_id << " ";
    std::cerr << "\nEXCLUSIVITY exclusive=";
    for(const auto &identifier : result)
      std::cerr << identifier << " ";
    std::cerr << "\nEXCLUSIVITY count=" << result.size() << "\n";
  }

  return result;
}

} // namespace

std::unordered_set<irep_idt> compute_thread_exclusive_variables(
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  return thread_exclusivity_analysist(goto_functions, ns)();
}
