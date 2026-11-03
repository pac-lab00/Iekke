/*******************************************************************\

Module: Goto Checker that infers the number of round-robin rounds

\*******************************************************************/

/// \file
/// --infer-rounds: symex once, then look for the least number of round-robin
/// rounds R that shows a violation, up to B = the static round bound capped
/// at --max-rounds (goto-symex/round_bound.h).
///
/// The lazy_po encoding is built in at most two blocks, each from the
/// equation as symex left it, into a fresh solver: one formula with B rounds
/// when B <= --infer-rounds-direct (default 6), otherwise --infer-rounds-first
/// rounds (default 3) and then B. The choice depends on B only.
/// Inside a block of k rounds every R <= k is a solver call under
/// assumptions: Empty_r for r > R switches those rounds off, which makes the
/// k-round formula equivalent to the R-round one. So the first R answering
/// "a property fails" is the least R; and a program whose bug shows at round 1
/// never pays for a formula with B rounds.
///
/// Reaching B is complete only when B is the static bound itself, not the cap.
/// LAZYPO_INFER_COMPLETENESS=1 also asks, inside a block, whether some
/// canonical schedule needs round R+1 (UNSAT: complete at R); on the safe
/// tasks of the 2026-10-27 campaign it never answered UNSAT before B.
///
/// The loop unwinding is fixed by symex: "complete" is relative to it.

#ifndef CPROVER_GOTO_CHECKER_ROUND_INCREMENTAL_SYMEX_CHECKER_H
#define CPROVER_GOTO_CHECKER_ROUND_INCREMENTAL_SYMEX_CHECKER_H

#include "multi_path_symex_checker.h"

class round_incremental_symex_checkert : public multi_path_symex_checkert
{
public:
  round_incremental_symex_checkert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model);

  resultt operator()(propertiest &) override;
};

#endif // CPROVER_GOTO_CHECKER_ROUND_INCREMENTAL_SYMEX_CHECKER_H
