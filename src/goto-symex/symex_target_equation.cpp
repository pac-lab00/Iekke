/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution
/// Implementation of functions to build SSA equation.

#include "symex_target_equation.h"
#include <map>

#include <iostream>

#include <string>

#include <cstdlib>

#include <chrono>

#include <unordered_set>
#include <util/std_expr.h>
#include <util/find_symbols.h>
#include <util/byte_operators.h>

#include "solver_hardness.h"
#include <solvers/prop/prop_conv_solver.h>
#include <util/ssa_expr.h>
#include <algorithm>
#include <vector>
#include "ssa_step.h"

static std::function<void(solver_hardnesst &)>
hardness_register_ssa(std::size_t step_index, const SSA_stept &step)
{
  return [step_index, &step](solver_hardnesst &hardness) {
    hardness.register_ssa(step_index, step.cond_expr, step.source.pc);
  };
}

void symex_target_equationt::shared_read(
  const exprt &guard,
  const ssa_exprt &ssa_object,
  unsigned atomic_section_id,
  const sourcet &source)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::SHARED_READ);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.ssa_lhs=ssa_object;
  SSA_step.atomic_section_id=atomic_section_id;

  merge_ireps(SSA_step);
}

void symex_target_equationt::shared_write(
  const exprt &guard,
  const ssa_exprt &ssa_object,
  unsigned atomic_section_id,
  const sourcet &source)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::SHARED_WRITE);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.ssa_lhs=ssa_object;
  SSA_step.atomic_section_id=atomic_section_id;

  merge_ireps(SSA_step);
}

/// spawn a new thread
void symex_target_equationt::spawn(
  const exprt &guard,
  const sourcet &source,
  std::size_t thread_nr)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::SPAWN);
  SSA_stept &SSA_step=SSA_steps.back();
  SSA_step.guard=guard;
  SSA_step.spawned_thread_nr = thread_nr;

  merge_ireps(SSA_step);
}

void symex_target_equationt::memory_barrier(
  const exprt &guard,
  const sourcet &source)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::MEMORY_BARRIER);
  SSA_stept &SSA_step=SSA_steps.back();
  SSA_step.guard=guard;

  merge_ireps(SSA_step);
}

/// start an atomic section
void symex_target_equationt::atomic_begin(
  const exprt &guard,
  unsigned atomic_section_id,
  const sourcet &source)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::ATOMIC_BEGIN);
  SSA_stept &SSA_step=SSA_steps.back();
  SSA_step.guard=guard;
  SSA_step.atomic_section_id=atomic_section_id;

  merge_ireps(SSA_step);
}

/// end an atomic section
void symex_target_equationt::atomic_end(
  const exprt &guard,
  unsigned atomic_section_id,
  const sourcet &source)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::ATOMIC_END);
  SSA_stept &SSA_step=SSA_steps.back();
  SSA_step.guard=guard;
  SSA_step.atomic_section_id=atomic_section_id;

  merge_ireps(SSA_step);
}

void symex_target_equationt::assignment(
  const exprt &guard,
  const ssa_exprt &ssa_lhs,
  const exprt &ssa_full_lhs,
  const exprt &original_full_lhs,
  const exprt &ssa_rhs,
  const sourcet &source,
  assignment_typet assignment_type)
{
  PRECONDITION(ssa_lhs.is_not_nil());

  SSA_steps.emplace_back(SSA_assignment_stept{source,
                                              guard,
                                              ssa_lhs,
                                              ssa_full_lhs,
                                              original_full_lhs,
                                              ssa_rhs,
                                              assignment_type});

  merge_ireps(SSA_steps.back());
}

void symex_target_equationt::decl(
  const exprt &guard,
  const ssa_exprt &ssa_lhs,
  const exprt &initializer,
  const sourcet &source,
  assignment_typet assignment_type)
{
  PRECONDITION(ssa_lhs.is_not_nil());

  SSA_steps.emplace_back(source, goto_trace_stept::typet::DECL);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.ssa_lhs=ssa_lhs;
  SSA_step.ssa_full_lhs = initializer;
  SSA_step.original_full_lhs=ssa_lhs.get_original_expr();
  SSA_step.hidden=(assignment_type!=assignment_typet::STATE);

  // the condition is trivially true, and only
  // there so we see the symbols
  SSA_step.cond_expr=equal_exprt(SSA_step.ssa_lhs, SSA_step.ssa_lhs);

  merge_ireps(SSA_step);
}

/// declare a fresh variable
void symex_target_equationt::dead(
  const exprt &,
  const ssa_exprt &,
  const sourcet &)
{
  // we currently don't record these
}

void symex_target_equationt::location(
  const exprt &guard,
  const sourcet &source)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::LOCATION);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;

  merge_ireps(SSA_step);
}

void symex_target_equationt::function_call(
  const exprt &guard,
  const irep_idt &function_id,
  const std::vector<renamedt<exprt, L2>> &function_arguments,
  const sourcet &source,
  const bool hidden)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::FUNCTION_CALL);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard = guard;
  SSA_step.called_function = function_id;
  for(const auto &arg : function_arguments)
    SSA_step.ssa_function_arguments.emplace_back(arg.get());
  SSA_step.hidden = hidden;

  merge_ireps(SSA_step);
}

void symex_target_equationt::function_return(
  const exprt &guard,
  const irep_idt &function_id,
  const sourcet &source,
  const bool hidden)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::FUNCTION_RETURN);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard = guard;
  SSA_step.called_function = function_id;
  SSA_step.hidden = hidden;

  merge_ireps(SSA_step);
}

void symex_target_equationt::output(
  const exprt &guard,
  const sourcet &source,
  const irep_idt &output_id,
  const std::list<renamedt<exprt, L2>> &args)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::OUTPUT);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  for(const auto &arg : args)
    SSA_step.io_args.emplace_back(arg.get());
  SSA_step.io_id=output_id;

  merge_ireps(SSA_step);
}

void symex_target_equationt::output_fmt(
  const exprt &guard,
  const sourcet &source,
  const irep_idt &output_id,
  const irep_idt &fmt,
  const std::list<exprt> &args)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::OUTPUT);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.io_args=args;
  SSA_step.io_id=output_id;
  SSA_step.formatted=true;
  SSA_step.format_string=fmt;

  merge_ireps(SSA_step);
}

void symex_target_equationt::input(
  const exprt &guard,
  const sourcet &source,
  const irep_idt &input_id,
  const std::list<exprt> &args)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::INPUT);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.io_args=args;
  SSA_step.io_id=input_id;

  merge_ireps(SSA_step);
}

void symex_target_equationt::assumption(
  const exprt &guard,
  const exprt &cond,
  const sourcet &source)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::ASSUME);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.cond_expr=cond;

  merge_ireps(SSA_step);
}

void symex_target_equationt::assertion(
  const exprt &guard,
  const exprt &cond,
  const std::string &msg,
  const sourcet &source)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::ASSERT);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.cond_expr=cond;
  SSA_step.comment=msg;

  merge_ireps(SSA_step);
}

void symex_target_equationt::goto_instruction(
  const exprt &guard,
  const renamedt<exprt, L2> &cond,
  const sourcet &source)
{
  SSA_steps.emplace_back(source, goto_trace_stept::typet::GOTO);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=guard;
  SSA_step.cond_expr = cond.get();

  merge_ireps(SSA_step);
}

void symex_target_equationt::constraint(
  const exprt &cond,
  const std::string &msg,
  const sourcet &source)
{
  // like assumption, but with global effect
  SSA_steps.emplace_back(source, goto_trace_stept::typet::CONSTRAINT);
  SSA_stept &SSA_step=SSA_steps.back();

  SSA_step.guard=true_exprt();
  SSA_step.cond_expr=cond;
  SSA_step.comment=msg;

  merge_ireps(SSA_step);
}


/// LAZYPO_VAR_TALLY: how many SAT variables converting each SSA step creates,
/// summed by the object the step assigns or by constraint kind, plus the
/// backend's total before the solver's own post-processing (array theory,
/// pointers), whose share is the final count minus that total. Steps of the
/// kinds not tallied (declarations, function calls, I/O, assertions) are in
/// the remainder too. Measurement only; with a decision procedure that is
/// not a prop_conv_solvert every count reads 0.
static bool var_tally_on()
{
  static const bool on = getenv("LAZYPO_VAR_TALLY") != nullptr;
  return on;
}

static std::map<std::string, std::size_t> &var_tally()
{
  static std::map<std::string, std::size_t> tally;
  return tally;
}

static std::size_t sat_variables(decision_proceduret &decision_procedure)
{
  const auto *p = dynamic_cast<prop_conv_solvert *>(&decision_procedure);
  return p == nullptr ? 0 : p->prop_no_variables();
}

static void var_tally_add(
  decision_proceduret &decision_procedure,
  std::size_t &before,
  const char *pass,
  const SSA_stept &step)
{
  std::string key = pass;
  if(step.is_constraint())
    key += " " + id2string(step.comment);
  else if(step.ssa_lhs.id() == ID_symbol && is_ssa_expr(step.ssa_lhs))
    key += " " + id2string(to_ssa_expr(step.ssa_lhs).get_object_name());
  const std::size_t now = sat_variables(decision_procedure);
  var_tally()[key] += now - before;
  before = now;
}

static void var_tally_print(decision_proceduret &decision_procedure)
{
  std::vector<std::pair<std::size_t, std::string>> sorted;
  for(const auto &e : var_tally())
    sorted.emplace_back(e.second, e.first);
  std::sort(sorted.rbegin(), sorted.rend());
  std::cerr << "VAR_TALLY before post-processing: "
            << sat_variables(decision_procedure) << " SAT variables\n";
  for(std::size_t i = 0; i < sorted.size() && i < 60; ++i)
    std::cerr << "VAR_TALLY " << sorted[i].first << "\t" << sorted[i].second
              << "\n";
}

void symex_target_equationt::convert_without_assertions(
  decision_proceduret &decision_procedure)
{
  with_solver_hardness(decision_procedure, [&](solver_hardnesst &hardness) {
    hardness.register_ssa_size(SSA_steps.size());
  });

  convert_guards(decision_procedure);
  convert_assignments(decision_procedure);
  convert_decls(decision_procedure);
  convert_assumptions(decision_procedure);
  convert_goto_instructions(decision_procedure);
  convert_function_calls(decision_procedure);
  convert_io(decision_procedure);
  convert_constraints(decision_procedure);
}

/// Categories to skip, from LAZYPO_ABLATE: comma-separated substrings matched
/// against each constraint's description. Measurement only.
static bool ablate_constraint(const std::string &comment)
{
  static const char *const spec = getenv("LAZYPO_ABLATE");
  if(spec == nullptr)
    return false;

  const std::string want(spec);
  std::size_t pos = 0;
  while(pos <= want.size())
  {
    const std::size_t next = want.find(',', pos);
    const std::string piece = want.substr(
      pos, next == std::string::npos ? std::string::npos : next - pos);
    if(!piece.empty() && comment.find(piece) != std::string::npos)
      return true;
    if(next == std::string::npos)
      break;
    pos = next + 1;
  }
  return false;
}

void symex_target_equationt::convert(decision_proceduret &decision_procedure)
{
  // Mark before either conversion pass runs: the POR/canonicality categories
  // are deliberately skipped by convert_constraints and placed by a later
  // pass, and both test !step.ignore.
  if(getenv("LAZYPO_ABLATE_LIST") != nullptr)
  {
    std::map<std::string, std::size_t> tally;
    for(const auto &step : SSA_steps)
      if(step.is_constraint())
        ++tally[id2string(step.comment)];
    for(const auto &entry : tally)
      std::cerr << "ABLATE_LIST " << entry.second << "\t" << entry.first
                << "\n";
  }

  if(getenv("LAZYPO_ABLATE") != nullptr)
  {
    std::size_t n = 0;
    for(auto &step : SSA_steps)
    {
      if(step.is_constraint() && ablate_constraint(id2string(step.comment)))
      {
        step.ignore = true;
        ++n;
      }
    }
    std::cerr << "ABLATE skipped " << n << " constraints matching \""
              << getenv("LAZYPO_ABLATE") << "\"\n";
  }
  const auto convert_SSA_start = std::chrono::steady_clock::now();

  convert_without_assertions(decision_procedure);
  convert_assertions(decision_procedure, !assertion_handles_only);

  if(var_tally_on())
    var_tally_print(decision_procedure);

  const auto convert_SSA_stop = std::chrono::steady_clock::now();
  std::chrono::duration<double> convert_SSA_runtime =
    std::chrono::duration<double>(convert_SSA_stop - convert_SSA_start);
  log.status() << "Runtime Convert SSA: " << convert_SSA_runtime.count() << "s"
               << messaget::eom;
}

void symex_target_equationt::convert_assignments(
  decision_proceduret &decision_procedure)
{
  std::size_t step_index = 0;
  std::size_t tally_before = sat_variables(decision_procedure);
  for(auto &step : SSA_steps)
  {
    if(step.is_assignment() && !step.ignore && !step.converted)
    {
      log.conditional_output(log.debug(), [&step](messaget::mstreamt &mstream) {
        step.output(mstream);
        mstream << messaget::eom;
      });

      decision_procedure.set_to_true(step.cond_expr);
      if(var_tally_on())
        var_tally_add(decision_procedure, tally_before, "assign", step);
      step.converted = true;
      with_solver_hardness(
        decision_procedure, hardness_register_ssa(step_index, step));
    }
    ++step_index;
  }
}

void symex_target_equationt::convert_decls(
  decision_proceduret &decision_procedure)
{
  std::size_t step_index = 0;
  for(auto &step : SSA_steps)
  {
    if(step.is_decl() && !step.ignore && !step.converted)
    {
      // The result is not used, these have no impact on
      // the satisfiability of the formula.
      decision_procedure.handle(step.cond_expr);
      decision_procedure.handle(
        equal_exprt{step.ssa_full_lhs, step.ssa_full_lhs});
      step.converted = true;
      with_solver_hardness(
        decision_procedure, hardness_register_ssa(step_index, step));
    }
    ++step_index;
  }
}

void symex_target_equationt::convert_guards(
  decision_proceduret &decision_procedure)
{
  std::size_t step_index = 0;
  std::size_t tally_before = sat_variables(decision_procedure);
  for(auto &step : SSA_steps)
  {
    if(step.ignore)
      step.guard_handle = false_exprt();
    else
    {
      log.conditional_output(log.debug(), [&step](messaget::mstreamt &mstream) {
        step.output(mstream);
        mstream << messaget::eom;
      });

      step.guard_handle = decision_procedure.handle(step.guard);
      if(var_tally_on())
        var_tally_add(decision_procedure, tally_before, "guard", step);
      with_solver_hardness(
        decision_procedure, hardness_register_ssa(step_index, step));
    }
    ++step_index;
  }
}

void symex_target_equationt::convert_assumptions(
  decision_proceduret &decision_procedure)
{
  std::size_t step_index = 0;
  std::size_t tally_before = sat_variables(decision_procedure);
  for(auto &step : SSA_steps)
  {
    if(step.is_assume())
    {
      if(step.ignore)
        step.cond_handle = true_exprt();
      else
      {
        log.conditional_output(
          log.debug(), [&step](messaget::mstreamt &mstream) {
            step.output(mstream);
            mstream << messaget::eom;
          });

        step.cond_handle = decision_procedure.handle(step.cond_expr);
        if(var_tally_on())
          var_tally_add(decision_procedure, tally_before, "assume", step);

        with_solver_hardness(
          decision_procedure, hardness_register_ssa(step_index, step));
      }
    }
    ++step_index;
  }
}

void symex_target_equationt::convert_goto_instructions(
  decision_proceduret &decision_procedure)
{
  std::size_t step_index = 0;
  std::size_t tally_before = sat_variables(decision_procedure);
  for(auto &step : SSA_steps)
  {
    if(step.is_goto())
    {
      if(step.ignore)
        step.cond_handle = true_exprt();
      else
      {
        log.conditional_output(
          log.debug(), [&step](messaget::mstreamt &mstream) {
            step.output(mstream);
            mstream << messaget::eom;
          });

        step.cond_handle = decision_procedure.handle(step.cond_expr);
        if(var_tally_on())
          var_tally_add(decision_procedure, tally_before, "goto", step);
        with_solver_hardness(
          decision_procedure, hardness_register_ssa(step_index, step));
      }
    }
    ++step_index;
  }
}

/// Vero se la costruzione modulare SAT Modulo SAT e attiva. Stesso switch
/// letto da bmc_util e da solver_factory; qui serve solo a decidere in quale
/// passo di conversione finiscono i vincoli di supporto della canonicalita,
/// il che sotto SMS definisce il taglio master/slave e fuori da SMS e solo
/// ordine di numerazione. Letto una volta: l ambiente non cambia in corsa.
static bool lazypo_sms_modular()
{
  static const bool sms = getenv("LAZYPO_SMS") != nullptr;
  return sms;
}

void symex_target_equationt::convert_constraints(
  decision_proceduret &decision_procedure)
{
  std::size_t step_index = 0;
  std::size_t tally_before = sat_variables(decision_procedure);
  for(auto &step : SSA_steps)
  {
    if(step.is_constraint() && !step.ignore && !step.converted
       && step.comment != "atomic_block_canonical"
       && step.comment != "abr"
       && step.comment != "abw"
       && step.comment != "lw canonical"
       && step.comment != "winr canonical"
       // Mancavano: le catene NRP/LOW e i simboli OBS finivano nel passo base,
       // cioe' nel modulo master. Misurato sul taglio della CNF: il 26% delle
       // clausole POR stava dalla parte sbagliata (tri_longer +19040 su 74170,
       // fib_unsafe-5 +69483 su 264336).
       && step.comment != "nrp canonical"
       && step.comment != "low canonical"
       && step.comment != "obs canonical"
       // La struttura di supporto dell encoding a finestre (i nodi del
       // range-OR e la catena FR) va tenuta fuori da questo passo SOLO
       // quando serve davvero, cioe sotto LAZYPO_SMS: li il taglio fra
       // master e slave e definito da quale passo converte cosa, e senza
       // queste due esclusioni il master cresceva di 33k variabili e 101k
       // clausole rispetto all encoding plain (misurato su safestack
       // --rounds 4 --unwind 3 --por).
       //
       // Fuori da SMS il passo non decide nulla di semantico -- la formula
       // e la stessa in entrambi i casi -- ma decide la NUMERAZIONE delle
       // variabili SAT, e Glucose ne risente parecchio. Convertire qui,
       // accanto ai letterali exec da cui questi nodi dipendono, invece che
       // nel secondo passo: vedi i numeri nel commit che introduce questa
       // condizione. Quindi: se SMS non e attivo, non escluderli.
       && (!lazypo_sms_modular() || (step.comment != "por range"
                                     && step.comment != "por first-read")))
    {
      log.conditional_output(log.debug(), [&step](messaget::mstreamt &mstream) {
        step.output(mstream);
        mstream << messaget::eom;
      });

      decision_procedure.set_to_true(step.cond_expr);
      if(var_tally_on())
        var_tally_add(decision_procedure, tally_before, "constraint", step);
      step.converted = true;

      with_solver_hardness(
        decision_procedure, hardness_register_ssa(step_index, step));
    }
    ++step_index;
  }
}


void symex_target_equationt::convert_concurrency_constraints(
  decision_proceduret &decision_procedure)
{
  std::size_t step_index = 0;
  for(auto &step : SSA_steps)
  {
    if(step.is_constraint() && !step.ignore && !step.converted
       && (step.comment == "cs constraint"
           || step.comment == "write constraint"))
    {
      decision_procedure.set_to_true(step.cond_expr);
      step.converted = true;

      with_solver_hardness(
        decision_procedure, hardness_register_ssa(step_index, step));
    }
    ++step_index;
  }
}

void symex_target_equationt::convert_canonical_constraints(
  decision_proceduret &decision_procedure)
{
  std::size_t step_index = 0;
  for(auto &step : SSA_steps)
  {
    if(step.is_constraint() && !step.ignore && !step.converted
       && (step.comment == "atomic_block_canonical"
           || step.comment == "abr"
           || step.comment == "abw"
           || step.comment == "lw canonical"
           || step.comment == "winr canonical"
           || step.comment == "nrp canonical"
           || step.comment == "low canonical"
           || step.comment == "obs canonical"
           || step.comment == "por range"
           || step.comment == "por first-read"))
    {
      log.conditional_output(log.debug(), [&step](messaget::mstreamt &mstream) {
        step.output(mstream);
        mstream << messaget::eom;
      });

      decision_procedure.set_to_true(step.cond_expr);
      step.converted = true;

      with_solver_hardness(
        decision_procedure, hardness_register_ssa(step_index, step));
    }
    ++step_index;
  }
}

void symex_target_equationt::convert_assertions(
  decision_proceduret &decision_procedure,
  bool optimized_for_single_assertions)
{
  // we find out if there is only _one_ assertion,
  // which allows for a simpler formula

  std::size_t number_of_assertions=count_assertions();

  if(number_of_assertions==0)
    return;

  if(number_of_assertions == 1 && optimized_for_single_assertions)
  {
    std::size_t step_index = 0;
    for(auto &step : SSA_steps)
    {
      // hide already converted assertions in the error trace
      if(step.is_assert() && step.converted)
        step.hidden = true;

      if(step.is_assert() && !step.ignore && !step.converted)
      {
        step.converted = true;
        decision_procedure.set_to_false(step.cond_expr);
        step.cond_handle = false_exprt();

        with_solver_hardness(
          decision_procedure, hardness_register_ssa(step_index, step));
        return; // prevent further assumptions!
      }
      else if(step.is_assume())
      {
        decision_procedure.set_to_true(step.cond_expr);

        with_solver_hardness(
          decision_procedure, hardness_register_ssa(step_index, step));
      }
      ++step_index;
    }

    UNREACHABLE; // unreachable
  }

  // We do (NOT a1) OR (NOT a2) ...
  // where the a's are the assertions
  or_exprt::operandst disjuncts;
  disjuncts.reserve(number_of_assertions);

  exprt assumption=true_exprt();

  std::vector<goto_programt::const_targett> involved_steps;

  for(auto &step : SSA_steps)
  {
    // hide already converted assertions in the error trace
    if(step.is_assert() && step.converted)
      step.hidden = true;

    if(step.is_assert() && !step.ignore && !step.converted)
    {
      step.converted = true;

      log.conditional_output(log.debug(), [&step](messaget::mstreamt &mstream) {
        step.output(mstream);
        mstream << messaget::eom;
      });

      implies_exprt implication(
        assumption,
        step.cond_expr);

      // do the conversion
      step.cond_handle = decision_procedure.handle(implication);

      with_solver_hardness(
        decision_procedure,
        [&involved_steps, &step](solver_hardnesst &hardness) {
          involved_steps.push_back(step.source.pc);
        });

      // store disjunct
      disjuncts.push_back(not_exprt(step.cond_handle));
    }
    else if(step.is_assume())
    {
      // the assumptions have been converted before
      // avoid deep nesting of ID_and expressions
      if(assumption.id()==ID_and)
        assumption.copy_to_operands(step.cond_handle);
      else
        assumption = and_exprt(assumption, step.cond_handle);

      with_solver_hardness(
        decision_procedure,
        [&involved_steps, &step](solver_hardnesst &hardness) {
          involved_steps.push_back(step.source.pc);
        });
    }
  }

  const auto assertion_disjunction = disjunction(disjuncts);
  // the below is 'true' if there are no assertions
  if(!assertion_handles_only)
    decision_procedure.set_to_true(assertion_disjunction);

  with_solver_hardness(
    decision_procedure,
    [&assertion_disjunction, &involved_steps](solver_hardnesst &hardness) {
      hardness.register_assertion_ssas(assertion_disjunction, involved_steps);
    });
}

void symex_target_equationt::convert_function_calls(
  decision_proceduret &decision_procedure)
{
  std::size_t step_index = 0;
  for(auto &step : SSA_steps)
  {
    if(!step.ignore)
    {
      and_exprt::operandst conjuncts;
      step.converted_function_arguments.reserve(step.ssa_function_arguments.size());

      for(const auto &arg : step.ssa_function_arguments)
      {
        if(arg.is_constant() ||
           arg.id()==ID_string_constant)
          step.converted_function_arguments.push_back(arg);
        else
        {
          const irep_idt identifier="symex::args::"+std::to_string(argument_count++);
          symbol_exprt symbol(identifier, arg.type());

          // Symbol on the left: set_to binds the fresh symbol to the
          // argument's own literals instead of giving it new bits and
          // asserting a bitwise equality. It is only read back for the trace.
          equal_exprt eq(symbol, arg);
          merge_irep(eq);

          decision_procedure.set_to(eq, true);
          conjuncts.push_back(eq);
          step.converted_function_arguments.push_back(symbol);
        }
      }
      with_solver_hardness(
        decision_procedure,
        [step_index, &conjuncts, &step](solver_hardnesst &hardness) {
          hardness.register_ssa(
            step_index, conjunction(conjuncts), step.source.pc);
        });
    }
    ++step_index;
  }
}

void symex_target_equationt::convert_io(decision_proceduret &decision_procedure)
{
  std::size_t step_index = 0;
  for(auto &step : SSA_steps)
  {
    if(!step.ignore)
    {
      and_exprt::operandst conjuncts;
      for(const auto &arg : step.io_args)
      {
        if(arg.is_constant() ||
           arg.id()==ID_string_constant)
          step.converted_io_args.push_back(arg);
        else
        {
          const irep_idt identifier =
            "symex::io::" + std::to_string(io_count++);
          symbol_exprt symbol(identifier, arg.type());

          // Symbol on the left: set_to binds the fresh symbol to the
          // argument's own literals instead of giving it new bits and
          // asserting a bitwise equality. It is only read back for the trace.
          equal_exprt eq(symbol, arg);
          merge_irep(eq);

          decision_procedure.set_to(eq, true);
          conjuncts.push_back(eq);
          step.converted_io_args.push_back(symbol);
        }
      }
      with_solver_hardness(
        decision_procedure,
        [step_index, &conjuncts, &step](solver_hardnesst &hardness) {
          hardness.register_ssa(
            step_index, conjunction(conjuncts), step.source.pc);
        });
    }
    ++step_index;
  }
}

/// Merging causes identical ireps to be shared.
/// This is only enabled if the definition SHARING is defined.
/// \param SSA_step The step you want to have shared values.
void symex_target_equationt::merge_ireps(SSA_stept &SSA_step)
{
  merge_irep(SSA_step.guard);

  merge_irep(SSA_step.ssa_lhs);
  merge_irep(SSA_step.ssa_full_lhs);
  merge_irep(SSA_step.original_full_lhs);
  merge_irep(SSA_step.ssa_rhs);

  merge_irep(SSA_step.cond_expr);

  for(auto &step : SSA_step.io_args)
    merge_irep(step);

  for(auto &arg : SSA_step.ssa_function_arguments)
    merge_irep(arg);

  // converted_io_args is merged in convert_io
}

void symex_target_equationt::output(std::ostream &out) const
{
  for(const auto &step : SSA_steps)
  {
    step.output(out);
    out << "--------------\n";
  }
}
