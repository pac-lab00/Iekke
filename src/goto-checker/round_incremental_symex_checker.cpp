/*******************************************************************\

Module: Goto Checker that infers the number of round-robin rounds

\*******************************************************************/

/// \file
/// See round_incremental_symex_checker.h.

#include "round_incremental_symex_checker.h"

#include <solvers/prop/literal_expr.h>
#include <solvers/prop/prop.h>
#include <solvers/sat/cnf.h>

#include <util/std_expr.h>
#include <util/ui_message.h>

#include <goto-symex/round_bound.h>

#include "bmc_util.h"

#include <chrono>
#include <iostream>

round_incremental_symex_checkert::round_incremental_symex_checkert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : multi_path_symex_checkert(options, ui_message_handler, goto_model)
{
}

incremental_goto_checkert::resultt round_incremental_symex_checkert::
operator()(propertiest &properties)
{
  resultt result(resultt::progresst::DONE);

  if(equation_generated && !has_properties_to_check(properties))
    return result;

  infer_rounds_bound() = 0;
  generate_equation();
  update_properties(properties, result.updated_properties);
  if(!has_properties_to_check(properties))
  {
    note_nothing_verified(properties, result.updated_properties);
    return result;
  }
  equation_generated = true;

  const std::size_t bound = infer_rounds_bound();
  if(bound == 0)
  {
    // No threads: postprocess_equation did its usual work, one plain check.
    std::cout << "Infer rounds: no threads, single check" << std::endl;
    std::chrono::duration<double> solver_runtime =
      prepare_property_decider(properties);
    run_property_decider(result, properties, solver_runtime);
    return result;
  }
  const bool bound_is_static = infer_rounds_bound_is_static();

  // The equation as symex left it (postprocess_equation applied no lazy_po
  // under --infer-rounds). Each block of rounds rebuilds the encoding from it,
  // so a bug at round 1 never pays for a formula with B rounds.
  const symex_target_equationt raw_equation = equation;

  std::size_t done = 0; // rounds already shown violation-free
  // Blocks of rounds, chosen from B alone (known before any solving):
  //   B <= direct : one formula with B rounds;
  //   B >  direct : `first` rounds, then B.
  // Measured on the 2026-10-27 campaign (521 tasks, cost = rounds built):
  // 364 of 379 bugs show within 3 rounds, and every safe task has to reach
  // B, so a block between `first` and B only adds a rebuild. Doubling
  // (2,4,8,16,B) cost twice the single formula on safe tasks; fixed steps of
  // 3 or 4 cost 2.3-2.8 times. This schedule keeps safe tasks at +19% over
  // the single formula and bug tasks at less than half of it.
  const std::size_t first = options.get_unsigned_int_option("infer-rounds-first");
  const std::size_t direct =
    options.get_unsigned_int_option("infer-rounds-direct");
  std::vector<std::size_t> blocks;
  if(bound <= direct || first == 0 || first >= bound)
    blocks = {bound};
  else
    blocks = {first, bound};

  for(const std::size_t k : blocks)
  {

    // ---- build the block: lazy_po with k rounds, a fresh solver ----------
    equation = raw_equation;
    apply_lazy_po(equation, options, ns, ui_message_handler, k, true);
    slice(symex, equation, ns, options, ui_message_handler);
    property_decider.reset_solver(ns);
    // The property enters only through the goal literal that each question
    // assumes, not as the clause "some assertion fails" at the root.
    equation.assertion_handles_only = true;
    prepare_property_decider(properties);
    std::cout << "Infer rounds: block of " << k << " round(s)" << std::endl;

    decision_proceduret &dp = property_decider.get_decision_procedure();
    stack_decision_proceduret &stack =
      property_decider.get_stack_decision_procedure();

    // Literals of Empty_2..Empty_k (already in the formula: handle() returns
    // the literal their definition was converted to) and "some property
    // fails". Glucose's simplifier eliminates variables during
    // a solve, and adding a clause over an eliminated variable aborts it
    // (SimpSolver::addClause_, !isEliminated): so every one of these is
    // converted before the first solve and frozen, and the questions are
    // asked by assumptions only.
    std::vector<exprt> empty(k + 1);
    for(std::size_t r = 2; r <= k; ++r)
      empty[r] = dp.handle(empty_round_symbol(r));
    const exprt violation_literal =
      dp.handle(property_decider.goals_disjunction(
        [&properties](const irep_idt &property_id) {
          return is_property_to_check(properties.at(property_id).status);
        }));
    {
      propt &prop = property_decider.get_solver()->prop();
      const auto freeze = [&prop](const exprt &e) {
        if(e.id() == ID_literal)
          prop.set_frozen(to_literal_expr(e).get_literal());
      };
      freeze(violation_literal);
      for(std::size_t r = 2; r <= k; ++r)
        freeze(empty[r]);
    }
    const auto rounds_above = [&](std::size_t from) {
      std::vector<exprt> off;
      for(std::size_t r = from; r <= k; ++r)
        off.push_back(empty[r]);
      return off;
    };

    // Between two solves the clause count must not move (the first solve may
    // add clauses itself, the converter's post-processing, before searching).
    // Checked rather than hoped for: a clause that aborts Glucose only when
    // the simplifier happens to eliminate its variable is invisible on small
    // programs.
    const cnft *cnf =
      dynamic_cast<const cnft *>(&property_decider.get_solver()->prop());
    bool solved_once = false;
    std::size_t clauses_after_last_solve = 0;
    // Solve under assumptions. push() takes literals only: an assumption the
    // converter folded to `true` is dropped, one folded to `false` makes the
    // question UNSAT without a solver call.
    const auto solve_assuming = [&](const std::vector<exprt> &assumptions) {
      std::vector<exprt> literals;
      for(const auto &a : assumptions)
      {
        if(a.is_false())
          return decision_proceduret::resultt::D_UNSATISFIABLE;
        if(!a.is_true())
          literals.push_back(a);
      }
      INVARIANT(
        cnf == nullptr || !solved_once ||
          cnf->no_clauses() == clauses_after_last_solve,
        "the --infer-rounds loop asks its questions by assumptions only");
      stack.push(literals);
      const decision_proceduret::resultt r = property_decider.solve();
      solved_once = true;
      if(cnf != nullptr)
        clauses_after_last_solve = cnf->no_clauses();
      if(r != decision_proceduret::resultt::D_SATISFIABLE)
        stack.pop(); // on SAT the trace is read from this model: leave it
      return r;
    };

    if(violation_literal.is_false())
    {
      done = bound; // no property left to check
      break;
    }

    // ---- rounds done+1 .. k inside the block -------------------------------
    for(std::size_t rounds = done + 1; rounds <= k; ++rounds)
    {
      // a violation with `rounds` rounds
      std::vector<exprt> question_a = rounds_above(rounds + 1);
      question_a.push_back(violation_literal);
      const decision_proceduret::resultt violation =
        solve_assuming(question_a);
      if(violation == decision_proceduret::resultt::D_SATISFIABLE)
      {
        property_decider.update_properties_status_from_goals(
          properties, result.updated_properties, violation, false);
        result.progress = resultt::progresst::FOUND_FAIL;
        std::cout << "Infer rounds: violation found with " << rounds
                  << " round(s), the least that shows it" << std::endl;
        return result;
      }
      if(violation != decision_proceduret::resultt::D_UNSATISFIABLE)
      {
        std::cout << "Infer rounds: solver error at " << rounds << " round(s)"
                  << std::endl;
        property_decider.update_properties_status_from_goals(
          properties, result.updated_properties, violation, false);
        return result;
      }
      std::cout << "Infer rounds: no violation with " << rounds
                << " round(s)" << std::endl;
      done = rounds;
    }
  }

  // No violation within the rounds explored.
  property_decider.update_properties_status_from_goals(
    properties,
    result.updated_properties,
    decision_proceduret::resultt::D_UNSATISFIABLE,
    true);
  if(bound_is_static)
    std::cout << "Infer rounds: complete at " << bound
              << " round(s): the static round bound" << std::endl;
  else
    std::cout << "Infer rounds: stopped at the --max-rounds cap of " << bound
              << " round(s): the result is bounded" << std::endl;
  return result;
}
