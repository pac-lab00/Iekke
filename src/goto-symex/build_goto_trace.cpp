/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

  Date: July 2005

\*******************************************************************/

/// \file
/// Traces of GOTO Programs

#include "build_goto_trace.h"
#include <cstdlib>
#include <iostream>
#include <set>
#include <util/prefix.h>
#include <util/cprover_prefix.h>

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/simplify_expr.h>
#include <util/symbol.h>

#include <goto-programs/goto_functions.h>

#include <solvers/decision_procedure.h>

#include "partial_order_concurrency.h"

static exprt build_full_lhs_rec(
  const decision_proceduret &decision_procedure,
  const namespacet &ns,
  const exprt &src_original, // original identifiers
  const exprt &src_ssa)      // renamed identifiers
{
  if(src_ssa.id()!=src_original.id())
    return src_original;

  const irep_idt id=src_original.id();

  if(id==ID_index)
  {
    // get index value from src_ssa
    exprt index_value = decision_procedure.get(to_index_expr(src_ssa).index());

    if(index_value.is_not_nil())
    {
      simplify(index_value, ns);
      index_exprt tmp=to_index_expr(src_original);
      tmp.index()=index_value;
      tmp.array() = build_full_lhs_rec(
        decision_procedure,
        ns,
        to_index_expr(src_original).array(),
        to_index_expr(src_ssa).array());
      return std::move(tmp);
    }

    return src_original;
  }
  else if(id==ID_member)
  {
    member_exprt tmp=to_member_expr(src_original);
    tmp.struct_op() = build_full_lhs_rec(
      decision_procedure,
      ns,
      to_member_expr(src_original).struct_op(),
      to_member_expr(src_ssa).struct_op());
  }
  else if(id==ID_if)
  {
    if_exprt tmp2=to_if_expr(src_original);

    tmp2.false_case() = build_full_lhs_rec(
      decision_procedure,
      ns,
      tmp2.false_case(),
      to_if_expr(src_ssa).false_case());

    tmp2.true_case() = build_full_lhs_rec(
      decision_procedure,
      ns,
      tmp2.true_case(),
      to_if_expr(src_ssa).true_case());

    exprt tmp = decision_procedure.get(to_if_expr(src_ssa).cond());

    if(tmp.is_true())
      return tmp2.true_case();
    else if(tmp.is_false())
      return tmp2.false_case();
    else
      return std::move(tmp2);
  }
  else if(id==ID_typecast)
  {
    typecast_exprt tmp=to_typecast_expr(src_original);
    tmp.op() = build_full_lhs_rec(
      decision_procedure,
      ns,
      to_typecast_expr(src_original).op(),
      to_typecast_expr(src_ssa).op());
    return std::move(tmp);
  }
  else if(id==ID_byte_extract_little_endian ||
          id==ID_byte_extract_big_endian)
  {
    byte_extract_exprt tmp = to_byte_extract_expr(src_original);
    tmp.op() = build_full_lhs_rec(
      decision_procedure, ns, tmp.op(), to_byte_extract_expr(src_ssa).op());

    // re-write into big case-split
  }

  return src_original;
}

/// set internal field for variable assignment related to dynamic_object[0-9]
/// and dynamic_[0-9]_array.
static void set_internal_dynamic_object(
  const exprt &expr,
  goto_trace_stept &goto_trace_step,
  const namespacet &ns)
{
  if(expr.id()==ID_symbol)
  {
    const auto &type = expr.type();
    if(type.id() != ID_code && type.id() != ID_mathematical_function)
    {
      const irep_idt &id = to_ssa_expr(expr).get_original_name();
      const symbolt *symbol;
      if(!ns.lookup(id, symbol))
      {
        bool result = symbol->type.get_bool(ID_C_dynamic);
        if(result)
          goto_trace_step.internal = true;
      }
    }
  }
  else
  {
    forall_operands(it, expr)
      set_internal_dynamic_object(*it, goto_trace_step, ns);
  }
}

/// set internal for variables assignments related to dynamic_object and CPROVER
/// internal functions (e.g., __CPROVER_initialize)
static void update_internal_field(
  const SSA_stept &SSA_step,
  goto_trace_stept &goto_trace_step,
  const namespacet &ns)
{
  // set internal for dynamic_object in both lhs and rhs expressions
  set_internal_dynamic_object(SSA_step.ssa_lhs, goto_trace_step, ns);
  set_internal_dynamic_object(SSA_step.ssa_rhs, goto_trace_step, ns);

  // set internal field to CPROVER functions (e.g., __CPROVER_initialize)
  if(SSA_step.is_function_call())
  {
    if(SSA_step.source.pc->source_location().as_string().empty())
      goto_trace_step.internal=true;
  }

  // set internal field to input and output steps
  if(goto_trace_step.type==goto_trace_stept::typet::OUTPUT ||
      goto_trace_step.type==goto_trace_stept::typet::INPUT)
  {
    goto_trace_step.internal=true;
  }

  // set internal field to _start function-return step
  if(SSA_step.source.function_id == goto_functionst::entry_point())
  {
    // "__CPROVER_*" function calls in __CPROVER_start are already marked as
    // internal. Don't mark any other function calls (i.e. "main"), function
    // arguments or any other parts of a code_function_callt as internal.
    if(SSA_step.source.pc->code().get_statement() != ID_function_call)
      goto_trace_step.internal=true;
  }
}

/// Replace nondet values that appear in \p type by their values as found by
/// \p solver.
static void
replace_nondet_in_type(typet &type, const decision_proceduret &solver)
{
  if(type.id() == ID_array)
  {
    array_typet &array_type = to_array_type(type);
    array_type.size() = solver.get(array_type.size());
  }

  if(type.has_subtype())
    replace_nondet_in_type(to_type_with_subtype(type).subtype(), solver);
}

/// Replace nondet values that appear in the type of \p expr and its
/// subexpressions type by their values as found by \p solver.
static void
replace_nondet_in_type(exprt &expr, const decision_proceduret &solver)
{
  replace_nondet_in_type(expr.type(), solver);
  for(auto &sub : expr.operands())
    replace_nondet_in_type(sub, solver);
}

static bool get_round_robin_trace_time(
  const SSA_stept &SSA_step,
  const decision_proceduret &decision_procedure,
  mp_integer &dest)
{
  if(SSA_step.round_robin_exec_symbols.empty())
    return false;

  for(std::size_t i = 0; i < SSA_step.round_robin_exec_symbols.size(); ++i)
  {
    if(decision_procedure.get(SSA_step.round_robin_exec_symbols[i]).is_true())
    {
      const mp_integer round = i + 1;
      const mp_integer thread = SSA_step.round_robin_thread;
      const mp_integer label = SSA_step.round_robin_label;
      const mp_integer num = SSA_step.round_robin_num;
      const mp_integer trace_order = SSA_step.round_robin_trace_order;

      dest =
        round * power(2, 128) +
        thread * power(2, 96) +
        label * power(2, 64) +
        num * power(2, 32) +
        trace_order;
      return true;
    }
  }

  return false;
}

/// Report what the model actually blamed for a datarace counterexample.
/// Enabled with LAZYPO_DR_PAIR=1. The counterexample says only that the
/// property failed; it never names the two accesses that were paired, so a
/// genuine pair and an artefact look identical from outside. The step counts
/// also explain an empty trace: every step with scheduling symbols but none
/// true in the model is dropped below, so a trace comes out empty exactly
/// when the constraint was satisfied without any event being scheduled.
static void report_datarace_pair(
  const symex_target_equationt &target,
  const decision_proceduret &decision_procedure)
{
  std::size_t steps = 0, guard_true = 0, with_exec = 0, exec_true = 0;
  std::set<irep_idt> variables;

  for(const auto &step : target.SSA_steps)
  {
    ++steps;
    if(!decision_procedure.get(step.guard_handle).is_true())
      continue;
    ++guard_true;

    if(!step.round_robin_exec_symbols.empty())
    {
      ++with_exec;
      for(const auto &e : step.round_robin_exec_symbols)
        if(decision_procedure.get(e).is_true())
        {
          ++exec_true;
          break;
        }
    }

    if(
      (step.is_shared_read() || step.is_shared_write()) &&
      can_cast_expr<symbol_exprt>(step.ssa_lhs))
    {
      variables.insert(step.ssa_lhs.get_l1_object_identifier());
    }
  }

  std::cout << "DR_PAIR steps=" << steps << " guard_true=" << guard_true
            << " with_exec_symbols=" << with_exec
            << " exec_true=" << exec_true << "\n";

  // Where does the failing assert sit? The output loop returns as soon as it
  // reaches it, so an assert that carries no scheduling symbols of its own
  // sorts to the front and truncates the trace before any event is emitted.
  std::size_t idx = 0, assert_idx = 0, shared_before = 0, shared_total = 0;
  bool found_assert = false;
  for(const auto &step : target.SSA_steps)
  {
    ++idx;
    const bool is_shared = step.is_shared_read() || step.is_shared_write();
    if(is_shared)
      ++shared_total;
    if(
      !found_assert && step.is_assert() &&
      decision_procedure.get(step.cond_handle).is_false())
    {
      found_assert = true;
      assert_idx = idx;
      shared_before = shared_total;
      std::cout << "DR_PAIR failing_assert at step " << assert_idx << "/"
                << steps << " exec_symbols="
                << step.round_robin_exec_symbols.size()
                << " shared_steps_before=" << shared_before << "\n";
    }
  }
  if(!found_assert)
    std::cout << "DR_PAIR failing_assert: <none found>\n";

  // For each blamed variable, show every access the model kept: which thread
  // it belongs to, whether its path guard holds, and whether any of its
  // per-round Exec symbols is true. A race needs two of these in different
  // threads; if only one thread shows up here, the pair the solver chose is
  // not backed by two executing accesses.
  const auto dump_accesses = [&](const irep_idt &v) {
    for(const auto &step : target.SSA_steps)
    {
      if(!(step.is_shared_read() || step.is_shared_write()))
        continue;
      if(!can_cast_expr<symbol_exprt>(step.ssa_lhs))
        continue;
      if(step.ssa_lhs.get_l1_object_identifier() != v)
        continue;
      const bool guard = decision_procedure.get(step.guard_handle).is_true();
      bool any_exec = false;
      for(const auto &e : step.round_robin_exec_symbols)
        if(decision_procedure.get(e).is_true())
        {
          any_exec = true;
          break;
        }
      std::cout << "DR_PAIR   access thread=" << step.round_robin_thread
                << " label=" << step.round_robin_label
                << " num=" << step.round_robin_num
                << (step.is_shared_write() ? " W" : " R")
                << " guard=" << (guard ? 1 : 0)
                << " exec_syms=" << step.round_robin_exec_symbols.size()
                << " exec_true=" << (any_exec ? 1 : 0) << "\n";
    }
  };

  const auto show = [&](const char *name) {
    const exprt value =
      decision_procedure.get(symbol_exprt::typeless(irep_idt(name)));
    std::cout << " " << name << "=";
    const auto n = numeric_cast<mp_integer>(value);
    if(n.has_value())
      std::cout << *n;
    else
      std::cout << "?";
  };

  std::cout << "DR_PAIR roles:";
  for(const char *s : {"t1", "t2", "r1", "r2"})
    show(s);
  std::cout << "  swap:";
  for(const char *s : {"t3", "t4", "r3", "r4"})
    show(s);
  std::cout << "\n";

  bool blamed_any = false;
  for(const auto &v : variables)
  {
    if(has_prefix(id2string(v), CPROVER_PREFIX))
      continue;
    for(const std::string &suffix : {std::string(""), std::string("_swap")})
    {
      const symbol_exprt p1(id2string(v) + "_phase_1" + suffix, bool_typet());
      const symbol_exprt p2(id2string(v) + "_phase_2" + suffix, bool_typet());
      if(
        decision_procedure.get(p1).is_true() &&
        decision_procedure.get(p2).is_true())
      {
        std::cout << "DR_PAIR blamed" << suffix << ": " << v << "\n";
        dump_accesses(v);
        blamed_any = true;
      }
    }
  }
  if(!blamed_any)
    std::cout << "DR_PAIR blamed: <none> -- no variable has both phases "
                 "satisfied in the model\n";
}

void build_goto_trace(
  const symex_target_equationt &target,
  ssa_step_predicatet is_last_step_to_keep,
  const decision_proceduret &decision_procedure,
  const namespacet &ns,
  goto_tracet &goto_trace)
{
  if(getenv("LAZYPO_DR_PAIR") != nullptr)
    report_datarace_pair(target, decision_procedure);

  // We need to re-sort the steps according to their clock.
  // Furthermore, read-events need to occur before write
  // events with the same clock.

  typedef symex_target_equationt::SSA_stepst::const_iterator ssa_step_iteratort;
  typedef std::map<mp_integer, std::vector<ssa_step_iteratort>> time_mapt;
  time_mapt time_map;

  mp_integer current_time=0;

  ssa_step_iteratort last_step_to_keep = target.SSA_steps.end();
  bool last_step_was_kept = false;
  ssa_step_iteratort deferred_last_step = target.SSA_steps.end();

  // The two accesses the datarace constraint blamed. The encoding names them
  // per event, so they can be identified exactly instead of inferred; without
  // this they never reach the trace, because a shared access only carries the
  // clock, and a race witnessed on the read side leaves no edge at all.
  std::set<const SSA_stept *> blamed_accesses;
  for(const auto &step : target.SSA_steps)
  {
    if(!(step.is_shared_read() || step.is_shared_write()))
      continue;
    if(!can_cast_expr<symbol_exprt>(step.ssa_lhs))
      continue;
    const std::string v =
      id2string(step.ssa_lhs.get_l1_object_identifier());
    const std::string suffix = "_T" + std::to_string(step.round_robin_thread) +
                               "_L" + std::to_string(step.round_robin_label) +
                               "_N" + std::to_string(step.round_robin_num);
    for(const std::string &role :
        {std::string("_phase_1"), std::string("_phase_2_w"),
         std::string("_phase_2_r"), std::string("_phase_1_swap"),
         std::string("_phase_2_swap_w")})
    {
      const symbol_exprt candidate(v + role + suffix, bool_typet());
      if(decision_procedure.get(candidate).is_true())
      {
        blamed_accesses.insert(&step);
        break;
      }
    }
  }

  // First sort the SSA steps by time, in the process dropping steps
  // we definitely don't want to retain in the final trace:

  for(ssa_step_iteratort it = target.SSA_steps.begin();
      it != target.SSA_steps.end();
      it++)
  {
    if(
      last_step_to_keep == target.SSA_steps.end() &&
      is_last_step_to_keep(it, decision_procedure))
    {
      last_step_to_keep = it;
    }

    const SSA_stept &SSA_step = *it;

    if(!decision_procedure.get(SSA_step.guard_handle).is_true())
      continue;

    mp_integer round_robin_time = 0;
    const bool has_round_robin_time =
      get_round_robin_trace_time(SSA_step, decision_procedure, round_robin_time);
    if(!SSA_step.round_robin_exec_symbols.empty() && !has_round_robin_time)
      continue;

    if(it->is_constraint() ||
       it->is_spawn())
      continue;
    else if(it->is_atomic_begin())
    {
      // for atomic sections the timing can only be determined once we see
      // a shared read or write (if there is none, the time will be
      // reverted to the time before entering the atomic section); we thus
      // use a temporary negative time slot to gather all events
      current_time*=-1;
      continue;
    }
    else if(it->is_shared_read() || it->is_shared_write() ||
            it->is_atomic_end())
    {
      mp_integer time_before=current_time;

      if(it->is_shared_read() || it->is_shared_write())
      {
        // these are just used to get the time stamp -- the clock type is
        // computed to be of the minimal necessary size, but we don't need to
        // know it to get the value so just use typeless

        // __SZH_ADD_BEGIN__
        if(has_round_robin_time)
        {
          current_time = round_robin_time;
        }
        else if(!target.oc_edges.empty()) // use deagle
        {
          std::string name = id2string(it->ssa_lhs.get_identifier());
          if(target.oc_result_order.find(name) != target.oc_result_order.end())
            current_time = target.oc_result_order.at(name);
          else
            current_time = 0;
        }
        // __SZH_ADD_END__
        else
        {
          exprt clock_value = decision_procedure.get(
            symbol_exprt::typeless(partial_order_concurrencyt::rw_clock_id(it)));

          const auto cv = numeric_cast<mp_integer>(clock_value);
          if(cv.has_value())
            current_time = *cv;
          else
            current_time = 0;
        }
      }
      else if(it->is_atomic_end() && current_time<0)
        current_time*=-1;

      INVARIANT(current_time >= 0, "time keeping inconsistency");
      // move any steps gathered in an atomic section

      if(time_before<0)
      {
        time_mapt::const_iterator time_before_steps_it =
          time_map.find(time_before);

        if(time_before_steps_it != time_map.end())
        {
          std::vector<ssa_step_iteratort> &current_time_steps =
            time_map[current_time];

          current_time_steps.insert(
            current_time_steps.end(),
            time_before_steps_it->second.begin(),
            time_before_steps_it->second.end());

          time_map.erase(time_before_steps_it);
        }
      }

      // Keep the accesses that constitute the race, so the witness actually
      // exhibits it. Every other shared access stays out, as before.
      if(
        (it->is_shared_read() || it->is_shared_write()) &&
        blamed_accesses.count(&*it) != 0)
      {
        time_map[current_time].push_back(it);
      }

      continue;
    }

    // drop PHI and GUARD assignments altogether
    if(it->is_assignment() &&
       (SSA_step.assignment_type==
          symex_target_equationt::assignment_typet::PHI ||
        SSA_step.assignment_type==
          symex_target_equationt::assignment_typet::GUARD))
    {
      continue;
    }

    if(it == last_step_to_keep)
    {
      last_step_was_kept = true;
      if(getenv("LAZYPO_DR_PAIR") != nullptr)
        std::cout << "DR_PAIR last_step_to_keep key="
                  << (has_round_robin_time ? round_robin_time : current_time)
                  << " (has_round_robin_time="
                  << (has_round_robin_time ? 1 : 0) << ")\n";

      // A property assert that carries no scheduling symbols belongs to no
      // thread and no round; the clock it would inherit here is simply
      // whatever the last shared access left behind. Since the output loop
      // stops at this step, letting it sort mid-schedule truncates the
      // counterexample -- for a data race, typically before the second
      // thread appears at all. Defer it and append it after everything.
      if(SSA_step.round_robin_exec_symbols.empty())
      {
        deferred_last_step = it;
        continue;
      }
    }

    if(has_round_robin_time)
      time_map[round_robin_time].push_back(it);
    else
      time_map[current_time].push_back(it);
  }

  INVARIANT(
    last_step_to_keep == target.SSA_steps.end() || last_step_was_kept,
    "last step in SSA trace to keep must not be filtered out as a sync "
    "instruction, not-taken branch, PHI node, or similar");

  // Fold away any leftover atomic-section placeholder slots. A negative key
  // is the temporary slot atomic_begin creates by negating current_time; it
  // normally disappears when the section ends, but if the equation finishes
  // inside one, both the gathered steps and anything placed at current_time
  // afterwards keep it. Since real event keys are large positives, such a
  // step would sort ahead of the whole trace -- and because the output loop
  // stops at last_step_to_keep, a violation assert stranded there truncates
  // the trace to nothing.
  {
    std::vector<mp_integer> negative_keys;
    for(const auto &entry : time_map)
      if(entry.first < 0)
        negative_keys.push_back(entry.first);

    for(const auto &key : negative_keys)
    {
      auto moved = time_map.find(key);
      INVARIANT(moved != time_map.end(), "key just collected must exist");
      std::vector<ssa_step_iteratort> &target_slot = time_map[-key];
      target_slot.insert(
        target_slot.end(), moved->second.begin(), moved->second.end());
      time_map.erase(moved);
    }
  }

  if(deferred_last_step != target.SSA_steps.end())
  {
    const mp_integer after_everything =
      time_map.empty() ? mp_integer(0) : time_map.rbegin()->first + 1;
    time_map[after_everything].push_back(deferred_last_step);
  }

  if(getenv("LAZYPO_DR_PAIR") != nullptr)
  {
    std::size_t queued = 0;
    for(const auto &t : time_map)
      queued += t.second.size();
    std::cout << "DR_PAIR smallest_key="
              << (time_map.empty() ? mp_integer(0) : time_map.begin()->first)
              << " largest_key="
              << (time_map.empty() ? mp_integer(0) : time_map.rbegin()->first)
              << "\n";
    std::cout << "DR_PAIR time_map slots=" << time_map.size()
              << " queued_steps=" << queued
              << " last_step_to_keep_found="
              << (last_step_to_keep != target.SSA_steps.end() ? 1 : 0)
              << " last_step_was_kept=" << (last_step_was_kept ? 1 : 0)
              << "\n";
  }

  // Now build the GOTO trace, ordered by time, then by SSA trace order.

  // produce the step numbers
  unsigned step_nr = 0;

  for(const auto &time_and_ssa_steps : time_map)
  {
    for(const auto &ssa_step_it : time_and_ssa_steps.second)
    {
      const auto &SSA_step = *ssa_step_it;
      goto_trace.steps.push_back(goto_trace_stept());
      goto_trace_stept &goto_trace_step = goto_trace.steps.back();

      goto_trace_step.step_nr = ++step_nr;

      goto_trace_step.thread_nr = SSA_step.source.thread_nr;
      goto_trace_step.pc = SSA_step.source.pc;
      goto_trace_step.function_id = SSA_step.source.function_id;
      if(SSA_step.is_assert())
      {
        goto_trace_step.comment = SSA_step.comment;
        goto_trace_step.property_id = SSA_step.get_property_id();
      }
      goto_trace_step.type = SSA_step.type;
      goto_trace_step.hidden = SSA_step.hidden;
      goto_trace_step.format_string = SSA_step.format_string;
      goto_trace_step.io_id = SSA_step.io_id;
      goto_trace_step.formatted = SSA_step.formatted;
      goto_trace_step.called_function = SSA_step.called_function;
      goto_trace_step.function_arguments = SSA_step.converted_function_arguments;

      for(auto &arg : goto_trace_step.function_arguments)
        arg = decision_procedure.get(arg);

      // update internal field for specific variables in the counterexample
      update_internal_field(SSA_step, goto_trace_step, ns);

      goto_trace_step.assignment_type =
        (SSA_step.is_assignment() &&
         (SSA_step.assignment_type ==
            symex_targett::assignment_typet::VISIBLE_ACTUAL_PARAMETER ||
          SSA_step.assignment_type ==
            symex_targett::assignment_typet::HIDDEN_ACTUAL_PARAMETER))
          ? goto_trace_stept::assignment_typet::ACTUAL_PARAMETER
          : goto_trace_stept::assignment_typet::STATE;

      if(SSA_step.original_full_lhs.is_not_nil())
      {
        goto_trace_step.full_lhs = simplify_expr(
          build_full_lhs_rec(
            decision_procedure,
            ns,
            SSA_step.original_full_lhs,
            SSA_step.ssa_full_lhs),
          ns);
        replace_nondet_in_type(goto_trace_step.full_lhs, decision_procedure);
      }

      if(SSA_step.ssa_full_lhs.is_not_nil())
      {
        goto_trace_step.full_lhs_value =
          decision_procedure.get(SSA_step.ssa_full_lhs);
        simplify(goto_trace_step.full_lhs_value, ns);
        replace_nondet_in_type(
          goto_trace_step.full_lhs_value, decision_procedure);
      }

      for(const auto &j : SSA_step.converted_io_args)
      {
        if(j.is_constant() || j.id() == ID_string_constant)
        {
          goto_trace_step.io_args.push_back(j);
        }
        else
        {
          exprt tmp = decision_procedure.get(j);
          goto_trace_step.io_args.push_back(tmp);
        }
      }

      if(SSA_step.is_assert() || SSA_step.is_assume() || SSA_step.is_goto())
      {
        goto_trace_step.cond_expr = SSA_step.cond_expr;

        goto_trace_step.cond_value =
          decision_procedure.get(SSA_step.cond_handle).is_true();
      }

      if(ssa_step_it == last_step_to_keep)
        return;
    }
  }
}

void build_goto_trace(
  const symex_target_equationt &target,
  symex_target_equationt::SSA_stepst::const_iterator last_step_to_keep,
  const decision_proceduret &decision_procedure,
  const namespacet &ns,
  goto_tracet &goto_trace)
{
  const auto is_last_step_to_keep =
    [last_step_to_keep](
      symex_target_equationt::SSA_stepst::const_iterator it,
      const decision_proceduret &) { return last_step_to_keep == it; };

  return build_goto_trace(
    target, is_last_step_to_keep, decision_procedure, ns, goto_trace);
}

static bool is_failed_assertion_step(
  symex_target_equationt::SSA_stepst::const_iterator step,
  const decision_proceduret &decision_procedure)
{
  return step->is_assert() &&
         decision_procedure.get(step->cond_handle).is_false();
}

void build_goto_trace(
  const symex_target_equationt &target,
  const decision_proceduret &decision_procedure,
  const namespacet &ns,
  goto_tracet &goto_trace)
{
  build_goto_trace(
    target, is_failed_assertion_step, decision_procedure, ns, goto_trace);
}
