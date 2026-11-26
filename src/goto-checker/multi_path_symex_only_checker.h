/*******************************************************************\

Module: Goto Checker using Multi-Path Symbolic Execution only

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Multi-Path Symbolic Execution only (no SAT solving)

#ifndef CPROVER_GOTO_CHECKER_MULTI_PATH_SYMEX_ONLY_CHECKER_H
#define CPROVER_GOTO_CHECKER_MULTI_PATH_SYMEX_ONLY_CHECKER_H

#include "incremental_goto_checker.h"

#include <goto-symex/path_storage.h>

#include <goto-instrument/unwindset.h>

#include "symex_bmc.h"

class multi_path_symex_only_checkert : public incremental_goto_checkert
{
public:
  multi_path_symex_only_checkert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model);

  resultt operator()(propertiest &) override;

protected:
  abstract_goto_modelt &goto_model;
  symbol_tablet symex_symbol_table;
  namespacet ns;
  symex_target_equationt equation;
  guard_managert guard_manager;
  path_fifot path_storage; // should go away
  unwindsett unwindset;
  symex_bmct symex;

  /// Generates the equation by running goto-symex
  virtual void generate_equation();

  /// The static analyses of the thread structure that bound or guide symex
  /// under the round-robin (--rounds) encoding: thread-exclusive variables
  /// and thread-management loops, with the thread-creation bound they set.
  void setup_thread_analyses();
  /// Repeat symex, seeded with the pointers published so far, until no
  /// published entry a pass consulted grows (CBMC #305).
  void symex_seeded_passes(bool own_view_reads);
  /// --refined-pointer-analysis: collection passes to a fixpoint of the
  /// overall value set, then the pass that builds the equation.
  void symex_refined_pointer_passes();
  /// Say on stdout whether a loop bound or the thread-creation bound cut the
  /// run, i.e. whether a SUCCESSFUL is a proof.
  void report_truncation() const;

  /// Updates the \p properties from the `equation` and
  /// adds their property IDs to \p updated_properties.
  /// Record that a truncated run generated no property at all, so that an
  /// empty set is not folded into a PASS. See the definition.
  void note_nothing_verified(
    propertiest &properties,
    std::unordered_set<irep_idt> &updated_properties);

  virtual void update_properties(
    propertiest &properties,
    std::unordered_set<irep_idt> &updated_properties);
};

#endif // CPROVER_GOTO_CHECKER_MULTI_PATH_SYMEX_ONLY_CHECKER_H
