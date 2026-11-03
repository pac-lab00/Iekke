/*******************************************************************\

Module: Goto Checker using Multi-Path Symbolic Execution Only

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Multi-Path Symbolic Execution only (no SAT solving)

#include "multi_path_symex_only_checker.h"

#include <optional>

#include <vector>

#include <algorithm>

#include <util/simplify_expr.h>
#include <util/ui_message.h>

#include <goto-symex/show_program.h>
#include <goto-symex/show_vcc.h>
#include <goto-symex/thread_exclusivity.h>
#include <goto-symex/symmetric_arrays.h>
#include <goto-symex/thread_spawn_loops.h>

#include <chrono>
#include <cstdlib>
#include <iostream>
#include <unordered_map>

#include "bmc_util.h"
#include "cp2_probe.h"

#include <goto-symex/guard_bdd.h>

/// Remove the shared read and write events whose path guard is a
/// propositional contradiction. A guard names its conditions through
/// goto_symex::\guard#n symbols, so the expression simplifier sees a
/// contradiction such as `c && !c` only when both halves are written side by
/// side; as BDDs over the guard definitions every such contradiction is the
/// constant false. An event that can never execute adds no execution: its read
/// value is unconstrained only on that unexecutable path, and it cannot take
/// part in a data race. Removing it shortens the write chains and the
/// context-switch points of the lazy encoding. The formula itself keeps the
/// usual guards; the BDDs only decide what to remove.
/// BDDs can grow large: the walk stops after LAZYPO_BDD_PRUNE_CAP seconds
/// (default 5) and keeps the remaining events. LAZYPO_NO_BDD_PRUNE turns the
/// removal off.
static std::size_t
bdd_prune_dead_accesses(symex_target_equationt &equation, messaget &log)
{
  const char *cap_env = getenv("LAZYPO_BDD_PRUNE_CAP");
  const double cap = cap_env && atof(cap_env) > 0 ? atof(cap_env) : 5.0;
  const auto t0 = std::chrono::steady_clock::now();
  guard_bdd_convertert bdd;
  std::size_t removed = 0;
  bool stopped = false;
  for(auto it = equation.SSA_steps.begin(); it != equation.SSA_steps.end();)
  {
    if(std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count() > cap)
    {
      stopped = true;
      break;
    }
    // a guard definition precedes its uses, so its BDD is ready when needed
    const bool defines_guard =
      it->is_assignment() && bdd.define(it->ssa_lhs, it->ssa_rhs);
    if(
      !defines_guard && (it->is_shared_read() || it->is_shared_write()) &&
      !it->guard.is_true() && !it->guard.is_false())
    {
      if(bdd.convert(it->guard).is_false())
      {
        it = equation.SSA_steps.erase(it);
        ++removed;
        continue;
      }
    }
    ++it;
  }
  log.status() << "BDD prune: removed " << removed << " shared accesses with a"
               << " contradictory guard" << (stopped ? " (stopped at the cap)" : "")
               << " in "
               << std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count()
               << "s" << messaget::eom;
  return removed;
}

multi_path_symex_only_checkert::multi_path_symex_only_checkert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : incremental_goto_checkert(options, ui_message_handler),
    goto_model(goto_model),
    ns(goto_model.get_symbol_table(), symex_symbol_table),
    equation(ui_message_handler),
    unwindset(goto_model),
    symex(
      ui_message_handler,
      goto_model.get_symbol_table(),
      equation,
      options,
      path_storage,
      guard_manager,
      unwindset)
{
  setup_symex(symex, ns, options, ui_message_handler);
}

incremental_goto_checkert::resultt multi_path_symex_only_checkert::
operator()(propertiest &properties)
{
  generate_equation();

  output_coverage_report(
    options.get_option("symex-coverage-report"),
    goto_model,
    symex,
    ui_message_handler);

  if(options.get_bool_option("show-vcc"))
  {
    show_vcc(options, ui_message_handler, equation);
  }

  if(options.get_bool_option("program-only"))
  {
    show_program(ns, equation);
  }

  if(options.get_bool_option("show-byte-ops"))
  {
    show_byte_ops(options, ui_message_handler, ns, equation);
  }

  resultt result(resultt::progresst::DONE);
  update_properties(properties, result.updated_properties);
  return result;
}

void multi_path_symex_only_checkert::generate_equation()
{
  const auto symex_start = std::chrono::steady_clock::now();

  // __WP_ADD_BEGIN__
  if(options.get_bool_option("unwind-suggest"))
  {
    symex.unwind_suggest();
    symex.show_unwind_suggest(goto_model.get_goto_functions());
    std::exit(0);
  }
  // __WP_ADD_END__

  setup_thread_analyses();

  // --own-view-reads (goto-symex/own_view_writers.h): every pass records
  // what each thread writes after the first spawn; the second pass reads
  // from a thread's own view what only that thread writes. Gated like the
  // analyses of setup_thread_analyses.
  const bool own_view_reads = options.get_bool_option("own-view-reads") &&
                              options.get_unsigned_int_option("rounds") > 0;
  symex.own_view_reads = own_view_reads;
  symex.own_view.known.clear();
  symex.own_view.active = false;
  symex.own_view.start_pass();

  // __SZH_ADD_BEGIN__
  // if the program has threads, we need to symex twice
  symex.try_finding_value_set = true;
  symex.symex_from_entry_point_of(
    goto_symext::get_goto_function(goto_model), symex_symbol_table);

  // Further passes for concurrent programs: the seeded passes that repair
  // late-published pointers (CBMC #305), or the --refined-pointer-analysis
  // ones. See each.
  if(symex.target.has_threads() &&
     !options.get_bool_option("refined-pointer-analysis"))
    symex_seeded_passes(own_view_reads);

  if(options.get_bool_option("refined-pointer-analysis") && symex.target.has_threads())
    symex_refined_pointer_passes();

  report_truncation();
  // __SZH_ADD_END__

  if(getenv("CP2PROBE") != nullptr)
    cp2_constant_probe(equation, ns);

  if(getenv("LAZYPO_NO_BDD_PRUNE") == nullptr)
    bdd_prune_dead_accesses(equation, log);

  symex.remove_dummy_accesses();

  equation.dynamic_object_atomicity(ns);

  if(symex.enable_datarace && !(options.get_unsigned_int_option("rounds") > 0))
    symex.symex_datarace(options.get_option("filename"));

  // __WP_ADD_BEGIN__
  if(symex.enable_deadlock)
    symex.symex_deadlock();
  // __WP_ADD_END__

  if(symex.enable_alloc)
    symex.symex_alloc_check();

  const auto symex_stop = std::chrono::steady_clock::now();
  std::chrono::duration<double> symex_runtime =
    std::chrono::duration<double>(symex_stop - symex_start);
  log.status() << "Runtime Symex: " << symex_runtime.count() << "s"
               << messaget::eom;

  postprocess_equation(symex, equation, options, ns, ui_message_handler);
}

void multi_path_symex_only_checkert::setup_thread_analyses()
{
  // Static, whole-program thread-exclusivity analysis. Gated to the
  // lazy_po/--rounds encoding: without --rounds nothing is computed, the
  // symex state's pointer stays null, and CBMC behaves exactly as before.
  // Also skipped under symex-driven lazy loading, where the full
  // goto_functionst is not available up front.
  if(
    options.get_unsigned_int_option("rounds") > 0 &&
    !options.get_bool_option("symex-driven-lazy-loading"))
  {
    symex.thread_exclusive_variables = compute_thread_exclusive_variables(
      goto_model.get_goto_functions(), ns);
  }

  // Static recognition of "spawn N threads in a loop, join them again in a
  // loop" (thread_spawn_loops.h), so that goto-symex can bound the number of
  // threads it actually creates independently of the loop bound the program
  // itself asks for. Gated exactly like the thread-exclusivity analysis above:
  // only under the lazy_po/--rounds encoding, and never under symex-driven
  // lazy loading, where the whole goto_functionst is not available up front.
  {
    const unsigned bound =
      options.get_unsigned_int_option("thread-creation-bound");

    if(
      bound > 0 && options.get_unsigned_int_option("rounds") > 0 &&
      !options.get_bool_option("symex-driven-lazy-loading"))
    {
      // Report recognised symmetric array families. No consumer yet: the
      // reduction itself has to rewrite array types in the symbol table, not
      // just constants in the goto program, because leaving the declarations
      // at their original size still times out (measured). Gated on an
      // environment variable so it costs nothing until then.
      if(getenv("LAZYPO_SHOW_SYMMETRIC_ARRAYS") != nullptr)
      {
        for(const auto &fam : compute_symmetric_array_families(
              goto_model.get_goto_functions(), ns))
        {
          std::cout << "symmetric-array-family size=" << fam.size;
          for(const auto &a : fam.arrays)
            std::cout << " " << a;
          std::cout << "\n";
        }
      }

      std::vector<std::size_t> handle_array_sizes;
      symex.thread_management_loops = compute_thread_management_loops(
        goto_model.get_goto_functions(), ns, &handle_array_sizes);

      if(!symex.thread_management_loops.empty())
      {
        // Do not bound below what the program can actually create. The
        // analysis exists for families declared `pthread_t t_ids[10000]`,
        // where bounding is the only way to finish; a family of four is the
        // opposite case, and cutting it at two turns a real race into a
        // vacuous SUCCESSFUL (measured: -32 on
        // pthread-race-challenges/thread-join-array-const-race, whose race is
        // between the fourth, unjoined thread and main's unguarded read).
        //
        // Only raised when *every* recognised family has a known size and the
        // largest is still cheap, because the bound is a single global: one
        // 10000-element family and the default stands.
        unsigned effective_bound = bound;
        const std::size_t affordable = 16;
        if(!handle_array_sizes.empty())
        {
          std::size_t largest = 0;
          for(const std::size_t n : handle_array_sizes)
          {
            if(n == 0 || n > affordable)
            {
              largest = 0;
              break;
            }
            largest = std::max(largest, n);
          }
          if(largest > effective_bound)
            effective_bound = static_cast<unsigned>(largest);
        }

        symex.thread_creation_bound = effective_bound;
        log.statistics() << "Thread-management loops recognised: "
                         << symex.thread_management_loops.size()
                         << "; bounding thread creation at "
                         << symex.thread_creation_bound
                         << (symex.thread_creation_bound != bound
                               ? " (raised to the declared handle-array size)"
                               : "")
                         << messaget::eom;
      }
    }
  }
}

// CBMC issue #305, in the configuration that actually ships.
//
// Value sets are built in symex order, which for a concurrent program is
// not an execution order: a thread spawned first is symexed first, so a
// pointer another thread publishes later is not in its set, the
// dereference resolves against the stale entry, and the interleaving is
// never encoded. The 13-line reproduction is ~/bench-minrepro/p305.c,
// where the reader is spawned before the publisher and the reachable
// assertion was reported SUCCESSFUL.
//
// The repair is a second pass: the first collects what every pointer may
// point to, the second builds the equation with that collection available
// so a *shared read of a pointer* can top up its own entry
// (goto_symex_statet::seed_published_targets). try_finding_value_set stays
// on, which is deliberate -- it is what keeps value_set_dereferencet
// resolving against the state's own set rather than the global union.
// Widening the dereference is what --refined-pointer-analysis does below,
// and it suppresses real races.
//
// Only for programs that have threads: without them there is no ordering
// mismatch and the second pass would be pure cost.
//
// One seeded pass is not a fixpoint. A publication that travels through a
// second thread -- the updater stores &n2 into g2, a relay copies g2 into
// g1, the reader reads g1 -- reaches the relay's copy only in the seeded
// pass, so g1's collected entry gains &n2 only after the reader, symexed
// first, has read g1 against the old one. That read then resolves against
// a stale set exactly as in #305: a real interleaving is never encoded, or
// a dereference lands on the wrong object (libvsync/cnalock hands its
// secondary queue over through two threads, and the stale read of
// sec_tail->next gave a false NULL dereference). Reproductions:
// regression/cbmc-concurrency/published_pointer_two_hops{,_false_alarm}.
//
// So repeat the seeded pass until no entry it consulted has grown. A pass
// depends on the collected set only through the entries its seeded reads
// consulted; if none of them grew during the pass, every such read already
// saw its final value, the next pass would be the same, and this pass's
// equation is the one kept. Growth elsewhere -- locals, objects never read
// as published pointers -- cannot change the next pass; counting it as well
// kept the loop going to its cap on the ldv drivers (nsc-ircc: 8 passes,
// no verdict in 900 s, 183 s before).
void multi_path_symex_only_checkert::symex_seeded_passes(
  const bool own_view_reads)
{
  // Under --own-view-reads the first pass's writers decide which reads the
  // seeded passes make from a thread's own view. A pass that finds such an
  // assumption broken -- its points-to sets are topped up, the first
  // pass's were not -- is repeated with what it found; a few times, and
  // then once more without own-view reads.
  symex.own_view.finish_pass();
  symex.own_view.active = own_view_reads;
  const std::size_t max_seeded_passes = 8;
  const std::size_t max_own_view_repetitions = 3;
  std::size_t seeded_passes = 0;
  std::size_t own_view_repetitions = 0;
  bool consulted_grew = false;
  bool own_view_broken = false;

  do
  {
    symex.path_storage.clear();
    symex.target.clear();
    symex.dynamic_counter = 0;
    symex.invalid_object_counter = 0;
    symex.try_finding_value_set = true;
    symex.seed_published_reads = true;
    symex.consulted_published.clear();
    const value_sett before = symex.overall_value_set;

    symex.own_view.start_pass();
    symex.symex_from_entry_point_of(
      goto_symext::get_goto_function(goto_model), symex_symbol_table);
    ++seeded_passes;

    consulted_grew = false;
    for(const auto &id : symex.consulted_published)
    {
      const auto *now = symex.overall_value_set.find_entry(id);
      if(now == nullptr)
        continue;
      const auto *was = before.find_entry(id);
      if(
        was == nullptr ||
        before.make_union_would_change(was->object_map, now->object_map))
      {
        consulted_grew = true;
        break;
      }
    }

    own_view_broken = symex.own_view.active && symex.own_view.finish_pass();
    if(own_view_broken)
    {
      log.status() << "Own-view reads: an object read from one thread's own "
                      "view is written by another; symexing again"
                   << messaget::eom;
      if(++own_view_repetitions == max_own_view_repetitions)
        symex.own_view.active = false;
    }
  } while((consulted_grew && seeded_passes < max_seeded_passes) ||
          own_view_broken);

  if(consulted_grew)
  {
    log.warning() << "points-to sets of shared pointers did not converge in "
                  << seeded_passes
                  << " symex passes; a pointer published late may be"
                     " missing from a dereference"
                  << messaget::eom;
  }
  else
  {
    log.status() << "points-to sets of shared pointers converged after "
                 << seeded_passes << " seeded symex pass(es)"
                 << messaget::eom;
  }

  if(own_view_reads)
  {
    log.status() << "Own-view reads: " << symex.own_view.reads
                 << " shared reads read from the thread's own view"
                 << (symex.own_view.active ? "" : " (given up)")
                 << messaget::eom;
  }
}

// NOT suitable as a default, measured over the whole 3220-pair corpus on
// 2026-10-08. It removes every false alarm the corpus has -- mcslock,
// rec_mcslock, cnalock and 28-race_reach_82-list_racefree, 4 -> 0 -- and
// pays for them with two wrong "this program is safe" answers, which are
// worse: hemlock (recoverable, it is only a truncation -- the race is
// found again at --unwind 3) and per-thread-array-join-counter-race-4
// (not recoverable at any bound tried: 2, 3, 4 rounds 3 and 4). Net -11.
//
// And the two halves do not separate, which was the obvious thing to try:
// running the collection passes to a fixpoint *without* seeding the final
// pass from the union keeps hemlock and repairs only
// 28-race_reach_82-list_racefree, still loses race-4, and comes out worse
// than not using the flag at all (-14). The reason race-4 goes either way
// is that value_set_dereferencet already resolves against
// overall_value_set in the final pass, so merely *growing* the union is
// enough to widen the dereference: there is no configuration in which the
// extra passes teach the analysis something without also widening it.
void multi_path_symex_only_checkert::symex_refined_pointer_passes()
{
  // Was: exactly one further pass with try_finding_value_set off.  That is
  // not enough.  The collection pass above unions state.value_set into
  // overall_value_set as it goes, which repairs a *shared* pointer that is
  // published late -- but a thread-local assigned from it earlier keeps the
  // points-to entry it was given before the publication was symexed, and
  // nothing revisits it.  The dereference then resolves against that stale
  // local, so the interleaving is never encoded and the bug is missed
  // (CBMC #305; 12-line reproduction in ~/bench-minrepro/p305.c, where the
  // reading thread is spawned first and the SSA reads only the pre-
  // publication object instead of building a case split over both).
  //
  // Run further *collection* passes instead, each seeded with the union
  // collected so far, until a whole pass adds nothing -- so the local is
  // re-derived from a pointer that already carries every published target.
  // Then do the final pass, which builds the equation.
  const std::size_t max_refinement_rounds = 8;

  for(std::size_t round = 0; round < max_refinement_rounds; ++round)
  {
    symex.path_storage.clear();
    symex.target.clear();
    symex.dynamic_counter = 0;
    symex.invalid_object_counter = 0;
    symex.try_finding_value_set = true;
    symex.seed_value_set_from_overall = true;
    symex.overall_value_set_changed = false;

    symex.symex_from_entry_point_of(
      goto_symext::get_goto_function(goto_model), symex_symbol_table);

    if(!symex.overall_value_set_changed)
      break;   // fixpoint: nothing new to learn
  }

  if(getenv("IEKKE_DUMP_VALUE_SET") != nullptr)
  {
    std::cout << "=== overall_value_set after refinement ===\n";
    symex.overall_value_set.output(std::cout);
    std::cout << "=== end overall_value_set ===\n";
  }

  symex.path_storage.clear();
  symex.target.clear();
  symex.try_finding_value_set = false;
  symex.seed_value_set_from_overall = true;
  symex.dynamic_counter = 0;
  symex.invalid_object_counter = 0;

  symex.symex_from_entry_point_of(
    goto_symext::get_goto_function(goto_model), symex_symbol_table);
}

void multi_path_symex_only_checkert::report_truncation() const
{
  // Was: an unconditional "Unwinding successfully", printed here before
  // the optional second symex pass and regardless of whether any loop had
  // actually been unwound to completion -- so it announced success just as
  // readily when a bound had been hit and the run had silently become an
  // under-approximation.  Report what actually happened instead, after the
  // last pass, so a caller can tell a proof from "ran out of bound".
  if(symex.unwinding_incomplete)
  {
    // NB: this message must not contain the literal strings that callers
    // grep for to read the verdict. It used to say "... but VERIFICATION
    // SUCCESSFUL is not a proof", which every such grep matched -- so a run
    // that errored, crashed or timed out and produced no verdict of its own
    // was read as a successful verification.
    std::cout << "Unwinding incomplete: " << symex.unwinding_truncated
              << " loop/recursion bound(s) hit; a counterexample is still"
                 " real, but a safe result here is not a proof\n";
  }
  else
    std::cout << "Unwinding successfully\n";

  // The thread-creation bound is an under-approximation of the same kind: a
  // counterexample found under it is real, the absence of one is not a proof.
  // It used to say so only through log.statistics(), invisible at normal
  // verbosity, so a vacuous safe answer looked exactly like a proof.
  //
  // NB, as above: this message must not contain the literal strings callers
  // grep for to read the verdict.
  if(symex.thread_creation_bound_hit)
  {
    std::cout << "Thread creation incomplete: bound "
              << symex.thread_creation_bound
              << " reached; a counterexample is still real, but a safe result"
                 " here is not a proof\n";
  }
}

void multi_path_symex_only_checkert::note_nothing_verified(
  propertiest &properties,
  std::unordered_set<irep_idt> &updated_properties)
{
  // A run that was cut short and then produced no property at all has not
  // proved anything. determine_result() folds the statuses starting from
  // PASS, so an empty set comes out as PASS and the tool announces
  // VERIFICATION SUCCESSFUL having checked nothing -- which on an
  // expected-false task is the worst answer available, not the mildest.
  //
  // The shape that causes it is a setup loop longer than the bound: the
  // unwinding *assumption* makes every path past the bound infeasible, so
  // execution never reaches the code under test. `pthread/indexer`
  // initialises 128 mutexes before creating a thread, and at every bound
  // below 129 it answers SUCCESSFUL with no verification condition
  // generated at all.
  //
  // An empty set on its own is legitimate -- a program with no shared
  // access has nothing to check under --datarace -- so it is the
  // truncation that makes this unsound.
  if(!properties.empty())
    return;
  if(!symex.unwinding_incomplete && !symex.thread_creation_bound_hit)
    return;
  // An empty set is only suspicious when the truncation is what emptied it,
  // and that question only has an answer when something was being looked
  // for. Under --datarace every shared access becomes a property, so an
  // empty set means execution never reached a shared access at all; without
  // it, a program with no assertion legitimately has nothing to check.
  //
  // Both regressions a wider rule caused were of the second kind:
  // `cbmc-concurrency/memory_barrier1` has no assertion and does not use
  // --datarace, and `cbmc/Recursion2` is sequential. An earlier attempt keyed
  // on "no spawn reached the equation" instead, which looked right and was
  // not: simplify_pthread_create_join collapses a create immediately
  // followed by a join into a direct call, so memory_barrier1 has no spawn
  // step either.
  if(!options.get_bool_option("datarace"))
    return;

  std::optional<goto_programt::const_targett> pc;
  if(!equation.SSA_steps.empty())
    pc = equation.SSA_steps.begin()->source.pc;
  else
  {
    const auto entry = goto_model.get_goto_functions().function_map.find(
      goto_functionst::entry_point());
    if(
      entry != goto_model.get_goto_functions().function_map.end() &&
      entry->second.body_available())
    {
      pc = entry->second.body.instructions.begin();
    }
  }
  if(!pc.has_value())
    return;

  const irep_idt id = "truncated.nothing.verified.1";
  properties.emplace(
    id,
    property_infot{*pc,
                   "the bound cut every path before any property was "
                   "reached, so nothing was verified",
                   property_statust::UNKNOWN});
  updated_properties.insert(id);
  log.status() << "No property was generated and the run was truncated:"
                  " nothing has been verified"
               << messaget::eom;
}

void multi_path_symex_only_checkert::update_properties(
  propertiest &properties,
  std::unordered_set<irep_idt> &updated_properties)
{
  if(options.get_bool_option("symex-driven-lazy-loading"))
    update_properties_from_goto_model(properties, goto_model);

  update_properties_status_from_symex_target_equation(
    properties, updated_properties, equation);
  // Since we will not symex any further we can decide the status
  // of all properties that do not occur in the equation now.
  // The current behavior is PASS.
  update_status_of_not_checked_properties(properties, updated_properties);
}
