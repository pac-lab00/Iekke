/*******************************************************************\

Module: Goto Checker using Multi-Path Symbolic Execution Only

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Multi-Path Symbolic Execution only (no SAT solving)

#include "multi_path_symex_only_checker.h"

#include <util/ui_message.h>

#include <goto-symex/show_program.h>
#include <goto-symex/show_vcc.h>
#include <goto-symex/thread_exclusivity.h>
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
      symex.thread_management_loops = compute_thread_management_loops(
        goto_model.get_goto_functions(), ns);

      if(!symex.thread_management_loops.empty())
      {
        symex.thread_creation_bound = bound;
        log.statistics() << "Thread-management loops recognised: "
                         << symex.thread_management_loops.size()
                         << "; bounding thread creation at " << bound
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
