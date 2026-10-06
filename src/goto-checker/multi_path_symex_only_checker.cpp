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

#include <util/ui_message.h>

#include <goto-symex/show_program.h>
#include <goto-symex/show_vcc.h>
#include <goto-symex/thread_exclusivity.h>
#include <goto-symex/symmetric_arrays.h>
#include <goto-symex/thread_spawn_loops.h>

#include <chrono>
#include <iostream>

#include "bmc_util.h"

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

  // __SZH_ADD_BEGIN__
  // if the program has threads, we need to symex twice
  symex.try_finding_value_set = true;
  symex.symex_from_entry_point_of(
    goto_symext::get_goto_function(goto_model), symex_symbol_table);


  if(options.get_bool_option("refined-pointer-analysis") && symex.target.has_threads())
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

    symex.symex_from_entry_point_of(
      goto_symext::get_goto_function(goto_model), symex_symbol_table);
  }

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
  // __SZH_ADD_END__

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
