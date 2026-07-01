/// \file
/// LazyCSeq context-bounded concurrency SSA transformation

#include "lazy_c_seq.h"
#include <algorithm>
#include <thread>
#include <util/cprover_prefix.h>
#include <util/format.h>
#include <util/format_expr.h>
#include <util/pointer_expr.h>
#include <util/c_types.h>
#include <util/prefix.h>
#include <util/simplify_expr.h>
#include <util/source_location.h>

#include <util/arith_tools.h>


static void align_pointer_equalities(exprt &e)
{
  for(auto &op : e.operands())
    align_pointer_equalities(op);

  if(e.id() == ID_equal || e.id() == ID_notequal)
  {
    auto &binary = to_binary_expr(e);
    if(
      binary.op0().type() != binary.op1().type() &&
      binary.op0().type().id() == ID_pointer &&
      binary.op1().type().id() == ID_pointer)
    {
      binary.op1() =
        typecast_exprt::conditional_cast(binary.op1(), binary.op0().type());
    }
  }
  else if(e.id() == ID_if)
  {

    auto &if_e = to_if_expr(e);
    if(if_e.true_case().type() != if_e.false_case().type())
    {
      if_e.false_case() = typecast_exprt::conditional_cast(
        if_e.false_case(), if_e.true_case().type());
    }
    if(if_e.type() != if_e.true_case().type())
      if_e.type() = if_e.true_case().type();
  }
  else if(e.id() == ID_with)
  {

    auto &with_e = to_with_expr(e);
    if(with_e.type() != with_e.old().type())
      with_e.type() = with_e.old().type();
  }
}

void lazy_c_seqt::operator()(
  symex_target_equationt &equation,
  message_handlert &message_handler)
{
  messaget log{message_handler};
  log.statistics() << "Adding Iekke constraints with " << rounds << " rounds"
                   << messaget::eom;

  //check_shared_event(equation, message_handler);

  handling_active_threads(equation/*, message_handler*/);

  collect_reads_and_writes(equation.SSA_steps/*, message_handler*/);

  if(por)
    build_atomic_blocks();

  create_write_constraints(equation/*, message_handler*/);

  create_read_constraints(equation/*, message_handler*/);

  if(por)
    create_lazy_variable_read();

  create_cs_constraint(equation/*, message_handler*/);

  if(por) {
    create_lw_tot_symbol(equation/*, message_handler*/);

    create_winr_tot_symbol(equation/*, message_handler*/);

    create_atomic_canonical(equation/*, message_handler*/);
  }

  handling_atomic_sections(equation/*, message_handler*/);

  if(datarace) {
    log.warning() << "Datarace Enabled " << messaget::eom;
    handling_datarace(equation/*, message_handler*/);
  }
  else
    handling_guards(equation/*, message_handler*/);

  for(auto &step : equation.SSA_steps)
  {
    align_pointer_equalities(step.cond_expr);
    align_pointer_equalities(step.guard);
  }
}

void lazy_c_seqt::create_write_constraints(
  symex_target_equationt &equation/*,
  message_handlert &message_handler*/)
{
  //messaget log{message_handler};

  //log.warning() << "-------------------WRITES--------------------------"
  //              << messaget::eom;

  for(auto global_variable : global_variables)
  {
    if(this->writes.count(global_variable) == 0)
      continue;
    exprt previous = this->writes.at(global_variable).front().s_it->ssa_lhs;

    irep_idt sentinel_id_name = "id_T0_L0_N0_R0_V"+id2string(global_variable);
    symbol_exprt sentinel_id_symbol{sentinel_id_name, unsignedbv_typet(bit_writes[global_variable])};
    lazy_variable first_lazy_struct = lazy_variable{
      0, 0, 0, 0, 0, this->writes.at(global_variable).front().s_it->ssa_lhs, sentinel_id_symbol};
    this->lazy_variables[global_variable].emplace_back(first_lazy_struct);

    for(std::size_t round = 1; round <= rounds; ++round)
    {
      for(const auto &write : this->writes.at(global_variable))
      {
        const symbol_exprt lazy_variable_exprt = create_lazy_symbol(
          write.label,
          write.thread,
          round,
          write.s_it->ssa_lhs,
          write.s_it->ssa_lhs.type());
        irep_idt id_name = "id_T" + std::to_string(write.thread) + "_L" +
                             std::to_string(write.label) + "_N" + std::to_string(write.num) +
                             "_R" + std::to_string(round)+ "_V"+id2string(global_variable);
        symbol_exprt id_symbol{id_name, unsignedbv_typet(bit_writes[global_variable])};
        lazy_variable lazy_struct =
          lazy_variable{round, write.label, write.num, write.thread, 0, lazy_variable_exprt,
            id_symbol};
        this->lazy_variables[global_variable].emplace_back(lazy_struct);

        const symbol_exprt exec =
          create_exec_symbol(write.label, write.num, write.thread, round);

        equal_exprt constraint{
          lazy_variable_exprt,
          if_exprt{exec, write.s_it->ssa_lhs,
                   typecast_exprt::conditional_cast(
                     previous, write.s_it->ssa_lhs.type())}};

        //log.warning() << format(constraint) << messaget::eom;
        equation.constraint(constraint, "write constraint", write.s_it->source);

        previous = lazy_variable_exprt;
      }
    }

    auto &lvs = this->lazy_variables[global_variable];
    std::sort(lvs.begin(), lvs.end(),
      [](const lazy_variable &a, const lazy_variable &b) {
        return std::tie(a.round, a.thread, a.label, a.num)
             < std::tie(b.round, b.thread, b.label, b.num);
      });

    const auto &front_src = this->writes.at(global_variable).front().s_it->source;
    // id-inline: l'id e' una costante (indice lex), non serve un simbolo dedicato.
    // get_id_symbol / LW ritornano from_integer(id) direttamente, quindi niente
    // simbolo exptr_id ne' la sua equazione di definizione.
    for(std::size_t i = 0; i < lvs.size(); ++i)
      lvs[i].id = static_cast<unsigned>(i);
    (void)front_src;
  }
}

void lazy_c_seqt::create_read_constraints(
  symex_target_equationt &equation/*,
  message_handlert &message_handler*/)
{
  //messaget log{message_handler};
  //log.warning() << "-------------------READS--------------------------"
  //              << messaget::eom;

  for(auto global_variable : global_variables)
  {
    if(this->reads.count(global_variable) == 0)
      continue;
    for(const auto &read : this->reads.at(global_variable))
    {
      exprt temp_constraint = read.s_it->ssa_lhs;
      for(std::size_t round = rounds; round >= 1; --round)
      {
        const symbol_exprt exec =
          create_exec_symbol(read.label, read.num, read.thread, round);

        std::optional<symbol_exprt> previous =
          previous_shared(global_variable, read.label, read.num, read.thread, round);
        if(previous.has_value())
        {
          temp_constraint = if_exprt{exec,
            typecast_exprt::conditional_cast(
              previous.value(), read.s_it->ssa_lhs.type()),
            temp_constraint};
        }
        else {
          temp_constraint = if_exprt{exec, read.s_it->ssa_lhs, temp_constraint};
        }
      }
      equal_exprt final_constraint{read.s_it->ssa_lhs, temp_constraint};
      //log.warning() << format(final_constraint) << messaget::eom;
      equation.constraint(
        final_constraint, "read constraint", read.s_it->source);
    }
    std::reverse(lazy_variables_read[global_variable].begin(), lazy_variables_read[global_variable].end());
  }
}

std::optional<symbol_exprt> lazy_c_seqt::previous_shared(
  irep_idt variable,
  unsigned label,
  unsigned num,
  unsigned thread,
  std::size_t round)
{
  if(lazy_variables.count(variable) == 0)
    return std::nullopt;
  symbol_exprt previous = lazy_variables.at(variable).front().symbol;
  for(const auto &lazy_variable : lazy_variables.at(variable))
  {
    if(round > lazy_variable.round)
    {
      previous = lazy_variable.symbol;
      continue;
    }
    if(round == lazy_variable.round && thread > lazy_variable.thread)
    {
      previous = lazy_variable.symbol;
      continue;
    }
    if(
      round == lazy_variable.round && thread == lazy_variable.thread &&
      label > lazy_variable.label)
    {
      previous = lazy_variable.symbol;
      continue;
    }
    if(
      round == lazy_variable.round && thread == lazy_variable.thread &&
      label == lazy_variable.label && num > lazy_variable.num)
    {
      previous = lazy_variable.symbol;
      continue;
    }
    if (previous == lazy_variables.at(variable).front().symbol && (label > lazy_variables.at(variable).front().label || (label <= lazy_variables.at(variable).front().label && num > lazy_variables.at(variable).front().num)))
      return std::nullopt;
    return previous;
  }
  return previous;
}

void lazy_c_seqt::check_shared_event(
    symex_target_equationt &equation/*,
    message_handlert &message_handler*/)
{
  // messaget log{message_handler};
  //
  // log.warning() << "-------------------CHECKING EVENTS--------------------------"
  //                << messaget::eom;

  symex_target_equationt temp_equation{equation};
  temp_equation.clear();

  auto ssa_steps = equation.SSA_steps;
  std::unordered_set<std::size_t> assignments;

  for(symex_target_equationt::SSA_stepst::const_iterator s_it =
        ssa_steps.begin();
      s_it != ssa_steps.end();
      s_it++)
  {
    if (s_it->is_assignment())
    {
      assignments.insert(s_it->ssa_lhs.hash());
    }
  }

  for(symex_target_equationt::SSA_stepst::const_iterator s_it =
        ssa_steps.begin();
      s_it != ssa_steps.end();
      s_it++)
  {
    bool assigned = true;
    if (s_it->is_shared_write())
    {
      if (assignments.count(s_it->ssa_lhs.hash()) == 0)
      {
        assigned = false;
      }
    }
    if (!assigned)
    {
      equation.SSA_steps.pop_front();
      //log.warning() << "Invalid event: SHARED_WRITE(" << format(s_it->get_ssa_expr()) << ")" << messaget::eom;
    }
    else
    {
      SSA_stept step{equation.SSA_steps.front()};
      step.type = equation.SSA_steps.front().type;

      equation.SSA_steps.pop_front();
      temp_equation.SSA_steps.emplace_back(step);
    }
  }
  equation = temp_equation;
}

void lazy_c_seqt::create_cs_constraint(
  symex_target_equationt &equation/*,
  message_handlert &message_handler*/)
{
  //messaget log{message_handler};
  //log.warning() << "-------------------CS--------------------------"
  //              << messaget::eom;

  for(unsigned thread = 0; thread <= threads; ++thread)
  {
    exprt previous;
    unsigned max_num = 0;

    max_num = labels[thread];

    n_bit[thread] = 0 ? 0 : 32 - __builtin_clz(max_num + 1);

    //log.warning() << "thread " << thread << ": from 0 to " << max_num << messaget::eom;

    for(size_t round = 0; round <= rounds; ++round)
    {
      symbol_exprt cs = create_cs_symbol(thread, round);

      if(round == 0)
      {
        less_than_or_equal_exprt constraint{cs, from_integer({0}, unsignedbv_typet{n_bit[thread]})};
        //log.warning() << format(constraint) << messaget::eom;
        equation.constraint(
          constraint,
          "cs constraint",
          equation.SSA_steps.begin()->source);
        previous = cs;
      }
      else {
          less_than_or_equal_exprt constraint{previous, cs};
          //log.warning() << format(constraint) << messaget::eom;
          equation.constraint(
            constraint,
            "cs constraint",
            equation.SSA_steps.begin()->source);
          previous = cs;
      }
      if(round == rounds)
      {
        exprt max{from_integer({max_num + 1}, unsignedbv_typet{n_bit[thread]})};
        less_than_or_equal_exprt last_constraint{cs, max};
        //log.warning() << format(last_constraint) << messaget::eom;
        equation.constraint(
          last_constraint,
          "cs constraint",
          equation.SSA_steps.begin()->source);
        previous = cs;
      }
    }
    for (size_t label = 0; label <= labels[thread]; label++)
    {
      for(size_t round = 1; round <= rounds; ++round)
      {
        exprt label_exp{
          from_integer({label}, unsignedbv_typet{n_bit[thread]})};

        symbol_exprt enabled =
          create_enabled_symbol(label, thread, round);

        symbol_exprt cs_curr =
          create_cs_symbol(thread, round);

        symbol_exprt cs_prev =
          create_cs_symbol(thread, round - 1);

        std::string active_name =
          "__CPROVER_active_thread_T" + std::to_string(thread);
        exprt active_thread_value = true_exprt{};
        if (label > 0) {
          std::optional<symbol_exprt> active_thread =
            previous_shared(active_name, label, 0, thread, round);
          if(active_thread.has_value())
          {
            active_thread_value = active_thread.value();
          }
        }


        if (label != 0) {
          greater_than_exprt expr_1{cs_curr, label_exp};
          exprt expr_2;
          if(round == 1)
            expr_2 = true_exprt{};
          else
          {
            expr_2 = less_than_or_equal_exprt{cs_prev, label_exp};
          }
          and_exprt expr_3{expr_1, expr_2};
          equal_exprt enabled_expr{enabled, expr_3};
          simplify(enabled_expr, ns);
          //log.warning() << format(enabled_expr) << messaget::eom;
          equation.constraint(
            enabled_expr, "cs constraint", equation.SSA_steps.begin()->source);
          implies_exprt active_expr{enabled, active_thread_value};
          simplify(active_expr, ns);
          //log.warning() << format(active_expr) << messaget::eom;
          equation.constraint(active_expr, "cs constraint", equation.SSA_steps.begin()->source);
        }
        else {
          equal_exprt enabled_expr{enabled, false_exprt{}};
          simplify(enabled_expr, ns);
          //log.warning() << format(enabled_expr) << messaget::eom;
          equation.constraint(
            enabled_expr, "cs constraint", equation.SSA_steps.begin()->source);
        }

        const auto git = guards[thread].find(label);
        const bool has_guards = (label > 0 && git != guards[thread].end());
        unsigned nmax =
          has_guards ? static_cast<unsigned>(git->second.size()) : 1;
        for(unsigned num = 0; num < nmax; ++num)
        {
          exprt expr_5;
          if (has_guards) {
            expr_5 = and_exprt{enabled, git->second.at(num)};
          }
          else {
            expr_5 = enabled;
          }
          symbol_exprt exec = create_exec_symbol(label, num, thread, round);
          equal_exprt constraint{exec, expr_5};
          simplify(constraint, ns);
          //log.warning() << format(constraint) << messaget::eom;
          equation.constraint(constraint, "cs constraint", equation.SSA_steps.begin()->source);
        }
      }
    }
  }
}

void lazy_c_seqt::handling_atomic_sections(
  symex_target_equationt &equation/*,
  message_handlert &message_handler*/)
{
  //messaget log{message_handler};

  //log.warning()
  //  << "-------------------ATOMIC SECTIONS--------------------------"
  //  << messaget::eom;

  for(auto atomic_section : atomic_sections)
  {
    // log.warning() << "atomic section Thread " << atomic_section.first << ": L"
    //               << atomic_section.second.first << " : L"
    //               << atomic_section.second.second << messaget::eom;
    exprt constraint;

    if (atomic_section.second.first != atomic_section.second.second)
    {
      for(std::size_t round = 1; round <= rounds; round++)
      {
        symbol_exprt cs = create_cs_symbol(atomic_section.first, round);
        constraint = or_exprt{
          less_than_or_equal_exprt{
            cs,
            from_integer(
              atomic_section.second.first,
              unsignedbv_typet{n_bit[atomic_section.first]})},
          greater_than_exprt{
            cs,
            from_integer(
              atomic_section.second.second,
              unsignedbv_typet{n_bit[atomic_section.first]})}};

        //log.warning() << format(constraint) << messaget::eom;
        equation.constraint(
          constraint, "atomic constraint", equation.SSA_steps.begin()->source);
      }
    }
  }
}

void lazy_c_seqt::handling_guards(
  symex_target_equationt &equation/*,
  message_handlert &message_handler*/)
{
  //messaget log{message_handler};

  //log.warning() << "-------------------GUARDS--------------------------"
  //              << messaget::eom;

  symex_target_equationt temp_equation{equation};
  temp_equation.clear();

  auto ssa_steps = equation.SSA_steps;

  for(symex_target_equationt::SSA_stepst::const_iterator s_it =
        ssa_steps.begin();
      s_it != ssa_steps.end();
      s_it++)
  {
    exprt guard = s_it->guard;

    if(s_it->is_assert() || s_it->is_assume())
    {
      shared_event blocking_event = blocking_events.front();
      blocking_events.erase(blocking_events.begin());
      SSA_stept step{equation.SSA_steps.front()};
      equation.SSA_steps.pop_front();
      symbol_exprt reach = create_reach_symbol(
        blocking_event.label, blocking_event.s_it->source.thread_nr);

      exprt constraint = false_exprt{};

      for(std::size_t round = 1; round <= rounds; round++)
      {
        symbol_exprt enabled = create_enabled_symbol(
          blocking_event.label, blocking_event.thread, round);

        constraint = or_exprt{constraint, enabled};
      }

      simplify(constraint, ns);

      equal_exprt final_constraint{reach, constraint};
      simplify(final_constraint, ns);
      //log.warning() << format(final_constraint) << messaget::eom;
      temp_equation.constraint(
        final_constraint,
        "blocking statement constraint",
        blocking_event.s_it->source);

      exprt new_guard = reach;
      step.guard = new_guard;
      exprt new_cond = s_it->cond_expr;
      exprt new_expr = implies_exprt{new_guard, new_cond};
      simplify(new_expr, ns);
      step.cond_expr = new_expr;
      step.type = s_it->type;
      //log.warning() << format(step.get_ssa_expr()) << messaget::eom;
      //log.warning() << "guard: " << format(step.guard) << messaget::eom;
      temp_equation.SSA_steps.emplace_back(step);
    }
    else
    {
      SSA_stept step{equation.SSA_steps.front()};
      step.type = equation.SSA_steps.front().type;

      equation.SSA_steps.pop_front();
      temp_equation.SSA_steps.emplace_back(step);
    }
  }
  equation = temp_equation;
}

void lazy_c_seqt::handling_active_threads(
  symex_target_equationt &equation/*,
  message_handlert &message_handler*/)
{
  // messaget log{message_handler};
  //
  // log.warning() << "-------------------ACTIVE THREAD--------------------------"
  //               << messaget::eom;

  symex_target_equationt temp_equation{equation};
  temp_equation.clear();

  auto ssa_steps = equation.SSA_steps;

  unsigned thread_current = 0;

  for(symex_target_equationt::SSA_stepst::const_iterator s_it =
        ssa_steps.begin();
      s_it != ssa_steps.end();
      s_it++)
  {
    exprt guard = s_it->guard;

    if(s_it->source.thread_nr > thread_current)
      thread_current = s_it->source.thread_nr;
  }
  std::unordered_map<unsigned, bool> thread_ends;


  exprt guard = true_exprt{};

  for(unsigned thread = 0; thread <= thread_current; thread++)
  {
    thread_ends[thread] = false;
    exprt symbol = create_active_thread_symbol(thread);
    if(thread == 0)
      create_active_thread_statements(
        ssa_steps.begin()->source,
        guard,
        ssa_steps.begin()->atomic_section_id,
        thread,
        temp_equation,
        //message_handler,
        true_exprt{});
    else
      create_active_thread_statements(
        ssa_steps.begin()->source,
        guard,
        ssa_steps.begin()->atomic_section_id,
        thread,
        temp_equation,
        //message_handler,
        false_exprt{});
  }

  unsigned thread_created = 1;
  thread_current = 0;
  bool thread_creating = false;
  bool thread_id_writing = false;

  symex_target_equationt::SSA_stepst::const_iterator prev;

  for(symex_target_equationt::SSA_stepst::const_iterator s_it =
        ssa_steps.begin();
      s_it != ssa_steps.end();
      s_it++)
  {
    guard = s_it->guard;

    if(s_it->source.thread_nr > thread_current)
    {
      thread_ends[thread_current] = true;
      exprt prev_guard = prev->guard;

      create_active_thread_statements(
        prev->source,
        prev_guard,
        prev->atomic_section_id,
        thread_current,
        temp_equation,
        //message_handler,
        false_exprt{});

      thread_current = s_it->source.thread_nr;

      SSA_stept step{equation.SSA_steps.front()};
      step.type = equation.SSA_steps.front().type;

      equation.SSA_steps.pop_front();
      temp_equation.SSA_steps.emplace_back(step);

      prev = s_it;
      continue;
    }

    if (s_it->source.pc->source_location().get_function() == "pthread_create" && thread_creating && thread_id_writing)
    {
      thread_creating = false;
      thread_id_writing = false;
      create_active_thread_statements(
        s_it->source,
        guard,
        s_it->atomic_section_id,
        thread_created,
        temp_equation,
        //message_handler,
        true_exprt{});

      thread_created++;

      SSA_stept step{equation.SSA_steps.front()};
      step.type = equation.SSA_steps.front().type;

      equation.SSA_steps.pop_front();
      temp_equation.SSA_steps.emplace_back(step);
    }

    if(s_it->is_function_call() && s_it->called_function == "pthread_create")
    {
      thread_creating = true;
    }
    else
    {
      if (thread_creating && s_it->is_shared_write() && s_it->ssa_lhs.get_l1_object_identifier() == "__CPROVER_next_thread_id")
        thread_id_writing = true;
      SSA_stept step{equation.SSA_steps.front()};
      step.type = equation.SSA_steps.front().type;

      equation.SSA_steps.pop_front();
      temp_equation.SSA_steps.emplace_back(step);
    }
    prev = s_it;
  }
  for (auto thread_end : thread_ends)
  {
    if (thread_end.second == false)
    {
      thread_ends[thread_current] = true;
      exprt prev_guard = true_exprt{};
      unsigned thread = thread_end.first;

      create_active_thread_statements(
        prev->source,
        prev_guard,
        prev->atomic_section_id,
        thread,
        temp_equation,
        //message_handler,
        false_exprt{});
    }
  }
  equation = temp_equation;
}

void lazy_c_seqt::create_active_thread_statements(
  const symex_targett::sourcet &source,
  exprt &guard,
  unsigned int atomic_section_id,
  unsigned &thread,
  symex_target_equationt &equation/*,
  message_handlert &message_handler*/,
  const exprt &value)
{
  //messaget log{message_handler};

  SSA_stept event_step{source, goto_trace_stept::typet::SHARED_WRITE};
  event_step.guard = guard;
  ssa_exprt event_expr{active_threads_vector.at(thread).symbol};
  event_expr.set_level_2(active_threads_vector.at(thread).l2);
  event_step.ssa_lhs = event_expr;
  event_step.atomic_section_id = atomic_section_id;
  equation.SSA_steps.emplace_back(event_step);
  //log.warning() << format(event_step.get_ssa_expr()) << messaget::eom;

  SSA_stept active_step{source, goto_trace_stept::typet::ASSIGNMENT};
  active_step.guard = guard;
  ssa_exprt active_expr{active_threads_vector.at(thread).symbol};
  active_expr.set_level_2(active_threads_vector.at(thread).l2);
  active_threads_vector.at(thread).l2++;
  active_step.ssa_lhs = active_expr;
  active_step.ssa_rhs = value;
  active_step.cond_expr = equal_exprt{active_step.ssa_lhs, active_step.ssa_rhs};
  active_step.assignment_type =
    symex_targett::assignment_typet::HIDDEN;
  active_step.hidden = true;
  active_step.atomic_section_id = atomic_section_id;
  equation.SSA_steps.emplace_back(active_step);
  //log.warning() << format(active_step.get_ssa_expr()) << messaget::eom;
}

symbol_exprt lazy_c_seqt::phase_1(/*messaget log,*/ symex_target_equationt &equation, irep_idt v) {

  //log.warning() << "------------------ fase 1 per " << as_string(v) << " iniziata" << messaget::eom;
  irep_idt phase_1_name =  as_string(v) + "_phase_1";
  symbol_exprt phase_1_symbl{phase_1_name, bool_typet{}};

  exprt phase_1_exp = false_exprt{};

  for (std::size_t thread = 0; thread <= threads; thread++) {
    irep_idt phase_1_t_name =  as_string(v) + "_phase_1_T" + std::to_string(thread);
    symbol_exprt phase_1_t_symbl{phase_1_t_name, bool_typet{}};

    phase_1_exp = or_exprt{phase_1_exp, phase_1_t_symbl};

    exprt phase_1_t_exp = false_exprt{};

    if(this->writes.count(v) != 0) {
      for (auto write : writes.at(v)) {
        std::string func = id2string(write.s_it->source.pc->source_location().get_function());
        bool is_pthread = (func.rfind("pthread", 0) == 0);
        if (write.thread != thread || is_pthread)
          continue;
        irep_idt phase_1_t_v_name =  as_string(v) + "_phase_1_T" + std::to_string(thread) + "_L" + std::to_string(write.label) + "_N" + std::to_string(write.num);
        symbol_exprt phase_1_t_v_symbl{phase_1_t_v_name, bool_typet{}};

        phase_1_t_exp = or_exprt{phase_1_t_exp, phase_1_t_v_symbl};

        int atom = write.s_it->atomic_section_id != 0;
        exprt phase_1_t_v_exp =
          and_exprt{
            equal_exprt{create_dr_thread_symbol(1), from_integer({thread}, unsignedbv_typet{threads_bits})},
            and_exprt{
              create_exec_tot_symbol(/*log,*/ equation, write.label, write.num, thread),
              and_exprt{
                equal_exprt{create_dr_atom_symbol(1), from_integer({atom}, bool_typet{})},
                equal_exprt{create_dr_loc_symbol(1), typecast_exprt(write.where, size_type())}
                }
              }
          };

        exprt exp2 = true_exprt{};
        for (std::size_t round = 1; round <= rounds; round++) {
          exprt enabled_exp = true_exprt{};
          if (write.label < labels[write.thread]) {
            enabled_exp = not_exprt{create_enabled_symbol(write.label+1,thread,round)};
          }
          exprt exp = implies_exprt{
            create_exec_symbol(write.label,write.num,thread,round),
            and_exprt{
              equal_exprt{create_dr_round_symbol(1),from_integer({round}, unsignedbv_typet{rounds_bits})},
              enabled_exp
            }};
          exp2 = and_exprt{exp2, exp};
        }
        phase_1_t_v_exp = equal_exprt{
          phase_1_t_v_symbl,
          and_exprt{phase_1_t_v_exp, exp2}};

        simplify(phase_1_t_v_exp, ns);
        //log.warning() << format(phase_1_t_v_exp) << messaget::eom;
        equation.constraint(
          phase_1_t_v_exp, "datarace constraint", equation.SSA_steps.begin()->source);
      }
    }
    phase_1_t_exp = equal_exprt {phase_1_t_symbl, phase_1_t_exp};
    simplify(phase_1_t_exp, ns);
    //log.warning() << format(phase_1_t_exp) << messaget::eom;
    equation.constraint(
      phase_1_t_exp, "datarace constraint", equation.SSA_steps.begin()->source);
  }

  phase_1_exp = equal_exprt {phase_1_symbl, phase_1_exp};
  simplify(phase_1_exp, ns);
  //log.warning() << format(phase_1_exp) << messaget::eom;
  equation.constraint(
    phase_1_exp, "datarace constraint", equation.SSA_steps.begin()->source);

  return phase_1_symbl;
}

symbol_exprt lazy_c_seqt::phase_2(/*messaget log,*/ symex_target_equationt &equation, irep_idt v) {
  //log.warning() << "------------------ fase 2 per " << as_string(v) << " iniziata" << messaget::eom;
  irep_idt phase_2_name = as_string(v) + "_phase_2";
  symbol_exprt phase_2_symbl{phase_2_name, bool_typet{}};

  exprt phase_2_exp = false_exprt{};

  for (std::size_t thread = 0; thread <= threads; thread++) {
    irep_idt phase_2_t_name = as_string(v) + "_phase_2_T" + std::to_string(thread);
    symbol_exprt phase_2_t_symbl{phase_2_t_name, bool_typet{}};

    phase_2_exp = or_exprt{phase_2_exp, phase_2_t_symbl};

    exprt phase_2_t_exp = false_exprt{};

    if(this->writes.count(v) != 0) {
      for (auto write : writes.at(v)) {
        std::string func = id2string(write.s_it->source.pc->source_location().get_function());
        bool is_pthread = (func.rfind("pthread", 0) == 0);
        if (write.thread != thread || is_pthread)
          continue;
        irep_idt phase_2_t_v_name = as_string(v) + "_phase_2_w_T" + std::to_string(thread) + "_L" + std::to_string(write.label) + "_N" + std::to_string(write.num);
        symbol_exprt phase_2_t_v_symbl{phase_2_t_v_name, bool_typet{}};

        phase_2_t_exp = or_exprt{phase_2_t_exp, phase_2_t_v_symbl};

        int atom = write.s_it->atomic_section_id != 0;
        exprt phase_2_t_v_exp =
          and_exprt{
            equal_exprt{create_dr_thread_symbol(2), from_integer({thread}, unsignedbv_typet{threads_bits})},
            and_exprt{
              create_exec_tot_symbol(/*log,*/ equation, write.label, write.num, thread),
              and_exprt{
                equal_exprt{create_dr_atom_symbol(2), from_integer({atom}, bool_typet{})},
                equal_exprt{create_dr_loc_symbol(2), typecast_exprt(write.where, size_type())}
              }
            }
          };

        exprt exp2 = true_exprt{};
        for (std::size_t round = 1; round <= rounds; round++) {
          exprt enabled_exp = true_exprt{};
          if (write.label > 1) {
            enabled_exp = not_exprt{create_enabled_symbol(write.label-1,thread,round)};
          }
          exprt exp = implies_exprt{
            create_exec_symbol(write.label,write.num,thread,round),
            and_exprt{
              equal_exprt{create_dr_round_symbol(2),from_integer({round}, unsignedbv_typet{rounds_bits})},
              enabled_exp
            }};
          exp2 = and_exprt{exp2, exp};
        }
        phase_2_t_v_exp = equal_exprt{
          phase_2_t_v_symbl,
          and_exprt{phase_2_t_v_exp, exp2}};

        simplify(phase_2_t_v_exp, ns);
        //log.warning() << format(phase_2_t_v_exp) << messaget::eom;
        equation.constraint(
          phase_2_t_v_exp, "datarace constraint", equation.SSA_steps.begin()->source);
      }
    }
    if(this->reads.count(v) != 0) {
      for (auto read : reads.at(v)) {
        std::string func = id2string(read.s_it->source.pc->source_location().get_function());
        bool is_pthread = (func.rfind("pthread", 0) == 0);
        if (read.thread != thread || is_pthread)
          continue;
        irep_idt phase_2_t_v_name =  as_string(v) + "_phase_2_r_T" + std::to_string(thread) + "_L" + std::to_string(read.label) + "_N" + std::to_string(read.num);
        symbol_exprt phase_2_t_v_symbl{phase_2_t_v_name, bool_typet{}};

        phase_2_t_exp = or_exprt{phase_2_t_exp, phase_2_t_v_symbl};

        int atom = read.s_it->atomic_section_id != 0;
        exprt phase_2_t_v_exp =
          and_exprt{
            equal_exprt{create_dr_thread_symbol(2), from_integer({thread}, unsignedbv_typet{threads_bits})},
            and_exprt{
              create_exec_tot_symbol(/*log,*/ equation, read.label, read.num, thread),
              and_exprt{
                equal_exprt{create_dr_atom_symbol(2), from_integer({atom}, bool_typet{})},
                equal_exprt{create_dr_loc_symbol(2), typecast_exprt(read.where, size_type())}
              }
            }
          };

        exprt exp2 = true_exprt{};
        for (std::size_t round = 1; round <= rounds; round++) {
          exprt enabled_exp = true_exprt{};
          if (read.label > 1) {
            enabled_exp = not_exprt{create_enabled_symbol(read.label-1,thread,round)};
          }
          exprt exp = implies_exprt{
            create_exec_symbol(read.label,read.num,thread,round),
            and_exprt{
              equal_exprt{create_dr_round_symbol(2),from_integer({round}, unsignedbv_typet{rounds_bits})},
              enabled_exp
            }};
          exp2 = and_exprt{exp2, exp};
        }
        phase_2_t_v_exp = equal_exprt{
          phase_2_t_v_symbl,
          and_exprt{phase_2_t_v_exp, exp2}};

        simplify(phase_2_t_v_exp, ns);
        //log.warning() << format(phase_2_t_v_exp) << messaget::eom;
        equation.constraint(
          phase_2_t_v_exp, "datarace constraint", equation.SSA_steps.begin()->source);
      }
    }
    phase_2_t_exp = equal_exprt {phase_2_t_symbl, phase_2_t_exp};
    simplify(phase_2_t_exp, ns);
    //log.warning() << format(phase_2_t_exp) << messaget::eom;
    equation.constraint(
      phase_2_t_exp, "datarace constraint", equation.SSA_steps.begin()->source);
  }

  phase_2_exp = equal_exprt {phase_2_symbl, phase_2_exp};
  simplify(phase_2_exp, ns);
  //log.warning() << format(phase_2_exp) << messaget::eom;
  equation.constraint(
    phase_2_exp, "datarace constraint", equation.SSA_steps.begin()->source);

  return phase_2_symbl;
}

symbol_exprt lazy_c_seqt::same_round(/*messaget log,*/ symex_target_equationt &equation) {
  //log.warning() << "------------------ sameround" << messaget::eom;
  irep_idt same_round_name = "same_round";
  symbol_exprt same_round_symbl{same_round_name, bool_typet{}};


  exprt same_round_exp = and_exprt{
    notequal_exprt{
      create_dr_thread_symbol(1),
      create_dr_thread_symbol(2)
    },
    and_exprt{
      implies_exprt{
        less_than_exprt{create_dr_thread_symbol(1),
      create_dr_thread_symbol(2)},
        equal_exprt{create_dr_round_symbol(1),
      create_dr_round_symbol(2)}
      },
      and_exprt{
        implies_exprt{
          less_than_exprt{create_dr_thread_symbol(2),
          create_dr_thread_symbol(1)},
            equal_exprt{create_dr_round_symbol(2),
          plus_exprt{create_dr_round_symbol(1), from_integer({1}, unsignedbv_typet{rounds_bits})}}},
        and_exprt{
          or_exprt{not_exprt{create_dr_atom_symbol(1)}, not_exprt{create_dr_atom_symbol(2)}},
          equal_exprt{create_dr_loc_symbol(1),create_dr_loc_symbol(2)}
          }
        }
    }
  };

  same_round_exp = equal_exprt{same_round_symbl, same_round_exp};
  simplify(same_round_exp, ns);
  //log.warning() << format(same_round_exp) << messaget::eom;
  equation.constraint(
    same_round_exp, "datarace constraint", equation.SSA_steps.begin()->source);

  return same_round_symbl;
}

symbol_exprt lazy_c_seqt::no_interf(/*messaget log,*/ symex_target_equationt &equation) {
  //log.warning() << "------------------ no interf" << messaget::eom;
  irep_idt no_interf_name = "no_interf";
  symbol_exprt no_interf_symbl{no_interf_name, bool_typet{}};

  exprt no_interf_exp = true_exprt{};


  for (std::size_t thread = 0; thread <= threads; thread++) {
    irep_idt no_interf_t_name = "no_interf_T" + std::to_string(thread);
    symbol_exprt no_interf_t_symbl{no_interf_t_name, bool_typet{}};

    exprt exp1 = true_exprt{};
    exprt exp2 = true_exprt{};
    for (std::size_t round = 1; round <= rounds; round++) {
      exprt exp1r = true_exprt{};
      exprt exp2r = true_exprt{};
        exp1r = implies_exprt{
          equal_exprt{create_dr_round_symbol(1), from_integer({round}, unsignedbv_typet{rounds_bits})},
          equal_exprt{create_cs_symbol(thread,round), create_cs_symbol(thread,round-1)}
        };
      if (round > 1) {
        exp2r = implies_exprt{
          equal_exprt{create_dr_round_symbol(2), from_integer({round}, unsignedbv_typet{rounds_bits})},
          equal_exprt{create_cs_symbol(thread,round), create_cs_symbol(thread,round-1)}
        };
      }
      exp1 = and_exprt{exp1, exp1r};
      exp2 = and_exprt{exp2, exp2r};
    }

    exprt no_interf_t_exp = and_exprt{
      and_exprt{
        implies_exprt{
          or_exprt{
            and_exprt{
              less_than_exprt{create_dr_thread_symbol(1), from_integer({thread}, unsignedbv_typet{threads_bits})},
              less_than_exprt{from_integer({thread}, unsignedbv_typet{threads_bits}), create_dr_thread_symbol(2)}},
            and_exprt{
              less_than_exprt{create_dr_thread_symbol(2),create_dr_thread_symbol(1)},
              less_than_exprt{create_dr_thread_symbol(1), from_integer({thread}, unsignedbv_typet{threads_bits})}}
          },
          exp1
        },
        implies_exprt{
          and_exprt{
          less_than_exprt{from_integer({thread}, unsignedbv_typet{threads_bits}), create_dr_thread_symbol(2)},
            less_than_exprt{create_dr_thread_symbol(2), create_dr_thread_symbol(1)}},
          exp2}
      }
    };

    no_interf_t_exp = equal_exprt{no_interf_t_symbl, no_interf_t_exp};
    simplify(no_interf_t_exp, ns);
    //log.warning() << format(no_interf_t_exp) << messaget::eom;
    equation.constraint(
      no_interf_t_exp, "datarace constraint", equation.SSA_steps.begin()->source);

    no_interf_exp = and_exprt{no_interf_exp, no_interf_t_symbl};
  }
  no_interf_exp = equal_exprt{no_interf_symbl, no_interf_exp};
  simplify(no_interf_exp, ns);
  //log.warning() << format(no_interf_exp) << messaget::eom;
  equation.constraint(
    no_interf_exp, "datarace constraint", equation.SSA_steps.begin()->source);

  return no_interf_symbl;
}

void lazy_c_seqt::handling_datarace(
  symex_target_equationt &equation/*,
  message_handlert &message_handler*/) {

  // messaget log{message_handler};
  //
  // log.warning() << "-------------------DATARACE--------------------------"
  //               << messaget::eom;

  irep_idt phases_name = "phases";
  symbol_exprt phases_symbl{phases_name, bool_typet{}};
  exprt phases_exp = false_exprt{};
  for (auto v : global_variables) {
    if (v.starts_with("__CPROVER"))
      continue;
    if (equation.symbol_is_atomic(ns,v))
      continue;
    symbol_exprt pha_1 = phase_1(/*log,*/ equation, v);
    //log.warning() << "------------------ fase 1 per " << as_string(v) << " fatta " << messaget::eom;
    symbol_exprt pha_2 = phase_2(/*log,*/ equation, v);
    //log.warning() << "------------------ fase 2 per " << as_string(v) << " fatta " << messaget::eom;
    exprt pha_1_2 = and_exprt{pha_1, pha_2};
    phases_exp = or_exprt{phases_exp, pha_1_2};
    //log.warning() << "------------------ merging fase 1 e 2 per " << as_string(v) << " fatto " << messaget::eom;
  }
  phases_exp = equal_exprt{phases_symbl, phases_exp};
  simplify(phases_exp, ns);
  //log.warning() << format(phases_exp) << messaget::eom;
  equation.constraint(
    phases_exp, "datarace constraint", equation.SSA_steps.begin()->source);

  symbol_exprt same_round_symbl = same_round(/*log,*/ equation);

  symbol_exprt no_interf_symbl = no_interf(/*log,*/ equation);

  exprt datarace_contraint = and_exprt{phases_symbl, and_exprt{same_round_symbl, no_interf_symbl}};
  simplify(datarace_contraint, ns);
  //log.warning() << "ASSERT: " << format(datarace_contraint) << messaget::eom;
  //equation.constraint(
   // datarace_contraint, "datarace constraint", equation.SSA_steps.begin()->source);
  equation.assertion(true_exprt{},not_exprt{datarace_contraint},"datarace",equation.SSA_steps.begin()->source);
}

void lazy_c_seqt::collect_reads_and_writes(
  symex_target_equationt::SSA_stepst &ssa_steps/*,
  message_handlert &message_handler*/)
{
  // messaget log{message_handler};
  //
  // log.warning() << "-------------------COLLECTING--------------------------"
  //               << messaget::eom;

  unsigned num = 0;
  symex_target_equationt::SSA_stepst::iterator prev =
        ssa_steps.begin();
  std::map<unsigned, std::vector<symex_target_equationt::SSA_stepst::iterator>>
    pending_trace_steps;

  struct trace_position
  {
    bool valid = false;
    unsigned label = 0;
    unsigned num = 0;
    unsigned thread = 0;
    unsigned next_order = 0;
  };
  std::map<unsigned, trace_position> last_trace_positions;

  const auto should_stage_trace_step = [](const SSA_stept &step) {
    if(!step.round_robin_exec_symbols.empty())
      return false;

    if(step.is_assignment())
    {
      return step.assignment_type != symex_targett::assignment_typet::PHI &&
             step.assignment_type != symex_targett::assignment_typet::GUARD;
    }

    return step.is_decl() || step.is_function_call() ||
           step.is_function_return() || step.is_goto() || step.is_location() ||
           step.is_output();
  };

  const auto annotate_with_position = [this](SSA_stept &step, trace_position &pos) {
    annotate_round_robin_trace_event(
      step,
      pos.label,
      pos.num,
      pos.thread,
      pos.next_order++);
  };

  const auto annotate_trace_event =
    [this, &pending_trace_steps, &last_trace_positions, &annotate_with_position](
      symex_target_equationt::SSA_stepst::iterator event,
      unsigned label,
      unsigned event_num,
      unsigned thread,
      symex_target_equationt::SSA_stepst::iterator next,
      const symex_target_equationt::SSA_stepst::iterator &end) {
      unsigned event_order = 0;
      auto &pending = pending_trace_steps[thread];
      auto &last_position = last_trace_positions[thread];

      if(last_position.valid)
      {
        for(auto pending_step : pending)
          annotate_with_position(*pending_step, last_position);
      }
      else
      {
        trace_position first_position{true, label, event_num, thread, 0};
        // Local initialisation steps before the first shared event only serve to
        // position the round-robin trace; they should not pollute the cex.
        for(auto pending_step : pending)
        {
          if(pending_step->is_assignment())
            pending_step->hidden = true;
          annotate_with_position(*pending_step, first_position);
        }
        event_order = first_position.next_order;
      }
      pending.clear();

      annotate_round_robin_trace_event(
        *event,
        label,
        event_num,
        thread,
        event_order);

      last_position = trace_position{true, label, event_num, thread, event_order + 1};
      if(next != end && next->is_assignment())
        annotate_with_position(*next, last_position);
    };

  for(symex_target_equationt::SSA_stepst::iterator s_it =
        ssa_steps.begin();
      s_it != ssa_steps.end();
      s_it++)
  {
    if(this->labels.count(s_it->source.thread_nr) == 0)
    {
      threads = s_it->source.thread_nr;
      labels[s_it->source.thread_nr] = 0;
    }

    if(should_stage_trace_step(*s_it))
      pending_trace_steps[s_it->source.thread_nr].push_back(s_it);

    if(s_it->is_assert() || s_it->is_assume())
    {
      if (labels[s_it->source.thread_nr] == 0  || s_it->atomic_section_id == 0 || (s_it->atomic_section_id != 0 && !prev->is_atomic_begin() && prev->guard != s_it->guard))
      {
        labels[s_it->source.thread_nr]++;
        num = 0;
      }
      else
        num++;

      exprt where = from_integer(-1,size_type());
      shared_event shared_event{s_it, where, labels[s_it->source.thread_nr], num, s_it->source.thread_nr};
      annotate_trace_event(
              s_it,
              shared_event.label,
              shared_event.num,
              shared_event.thread,
              ssa_steps.end(),
              ssa_steps.end());
      {
        auto &gv = guards[s_it->source.thread_nr][labels[s_it->source.thread_nr]];
        if(gv.size() <= num)
          gv.resize(num + 1, true_exprt{});
        gv[num] = s_it->guard;
      }

      // log.warning() << "Thread: " << shared_event.s_it->source.thread_nr
      //               << "\tBlocking statement: " << shared_event.label << "\t"
      //               << format(s_it->cond_expr) << messaget::eom;

      this->blocking_events.emplace_back(shared_event);
      shared_events.emplace_back(shared_event);
      prev = s_it;
    }

    if(s_it->is_atomic_begin())
    {
      labels[s_it->source.thread_nr]++;
      {
        auto &gv = guards[s_it->source.thread_nr][labels[s_it->source.thread_nr]];
        if(gv.size() <= num)
          gv.resize(num + 1, true_exprt{});
        gv[num] = s_it->guard;
      }
      atomic_sections.emplace_back(
        s_it->source.thread_nr, std::pair<unsigned,unsigned>(labels[s_it->source.thread_nr], NULL));
      //log.warning() << "ATOMIC BEGIN: " << labels[s_it->source.thread_nr] << messaget::eom;
      prev = s_it;
    }

    if(s_it->is_atomic_end())
    {
      atomic_sections.back().second.second =  labels[s_it->source.thread_nr];
      num = 0;
      //log.warning() << "ATOMIC END: " <<  labels[s_it->source.thread_nr] << messaget::eom;
    }

    if(s_it->is_shared_write()) {
      // TODO: this may be too restrictive
      if(can_cast_expr<symbol_exprt>(s_it->ssa_lhs))
      {
        if (labels[s_it->source.thread_nr] == 0 || (s_it->atomic_section_id == 0 && s_it->source.pc->source_location() != prev->source.pc->source_location()) ||
          (s_it->atomic_section_id == 0 && s_it->source.pc->source_location() == prev->source.pc->source_location() && s_it->guard != prev->guard) ||
          (s_it->atomic_section_id != 0 && prev->guard != s_it->guard))
        {
          labels[s_it->source.thread_nr]++;
          num = 0;
        }
        else
          num++;

        exprt where = from_integer(-1,size_type());
        auto next = s_it;
        next++;
        if (next->is_assignment() && next->ssa_rhs.id() == ID_with) { //ARRAY
          where = to_with_expr(next->ssa_rhs).where();
        }
        else { //STRUCT
          std::string id = id2string(to_symbol_expr(s_it->ssa_lhs).get_identifier());
          auto pos = id.rfind("..");
          if(pos != std::string::npos)
          {
            std::string field = id.substr(pos + 2);
            where = from_integer(hash_string(field), size_type());
          }
        }

        shared_event shared_event{s_it, where,  labels[s_it->source.thread_nr], num, s_it->source.thread_nr};
        annotate_trace_event(
                  s_it,
                  shared_event.label,
                  shared_event.num,
                  shared_event.thread,
                  next,
                  ssa_steps.end());
        {
          auto &gv = guards[s_it->source.thread_nr][labels[s_it->source.thread_nr]];
          if(gv.size() <= num)
            gv.resize(num + 1, true_exprt{});
          gv[num] = s_it->guard;
        }

        // log.warning()
        //   << "Thread: " << shared_event.s_it->source.thread_nr
        //   << "\tWrite: " << shared_event.label << "   \t"
        //   << to_symbol_expr(shared_event.s_it->ssa_lhs).get_identifier()
        //   << "\tL" << shared_event.label << messaget::eom;
        shared_events.emplace_back(shared_event);
        this->writes[shared_event.s_it->ssa_lhs.get_l1_object_identifier()]
          .emplace_back(shared_event);
        this->global_variables.emplace(
          shared_event.s_it->ssa_lhs.get_l1_object_identifier());
        prev = s_it;
      }
      else
      {
        // log.warning() << "Skipping: "
        //               << "Thread: " << s_it->source.thread_nr
        //               << "\tWrite: " << s_it->source.pc->location_number
        //               << messaget::eom;
      }
    }
    if(s_it->is_shared_read())
    {
      // TODO: this may be too restrictive
      if(can_cast_expr<symbol_exprt>(s_it->ssa_lhs))
      {
        if (labels[s_it->source.thread_nr] == 0 || (s_it->atomic_section_id == 0 && s_it->source.pc->source_location() != prev->source.pc->source_location()) ||
          (s_it->atomic_section_id == 0 && s_it->source.pc->source_location() == prev->source.pc->source_location() && s_it->guard != prev->guard) ||
          (s_it->atomic_section_id != 0 && prev->guard != s_it->guard))
        {
          labels[s_it->source.thread_nr]++;
          num = 0;
        }
        else
          num++;

        exprt where = from_integer(-1,size_type());
        auto next = s_it;
        next++;
        if (next->is_assignment() && next->ssa_rhs.id() == ID_index) { //ARRAY
          where = to_index_expr(next->ssa_rhs).index();
        }
        else { //STRUCT
          std::string id = id2string(to_symbol_expr(s_it->ssa_lhs).get_identifier());
          auto pos = id.rfind("..");
          if(pos != std::string::npos)
          {
            std::string field = id.substr(pos + 2);
            where = from_integer(hash_string(field), size_type());
          }
        }

        shared_event shared_event{s_it, where,  labels[s_it->source.thread_nr], num, s_it->source.thread_nr};
        annotate_trace_event(
                  s_it,
                  shared_event.label,
                  shared_event.num,
                  shared_event.thread,
                  next,
                  ssa_steps.end());
        {
          auto &gv = guards[s_it->source.thread_nr][labels[s_it->source.thread_nr]];
          if(gv.size() <= num)
            gv.resize(num + 1, true_exprt{});
          gv[num] = s_it->guard;
        }

        // log.warning()
        //   << "Thread: " << shared_event.s_it->source.thread_nr
        //   << "\tRead: " << shared_event.label << "   \t"
        //   << to_symbol_expr(shared_event.s_it->ssa_lhs).get_identifier()
        //   << "\tL" << shared_event.label << messaget::eom;

        shared_events.emplace_back(shared_event);

        this->reads[shared_event.s_it->ssa_lhs.get_l1_object_identifier()].emplace_back(shared_event);
        this->global_variables.insert(shared_event.s_it->ssa_lhs.get_l1_object_identifier());
        prev = s_it;
      }
      else
      {
        // log.warning() << "Skipping: " << "Thread: " << s_it->source.thread_nr
        //               << "\tRead: " << s_it->source.pc->location_number
        //               << messaget::eom;
      }
    }
  }
  for(auto global_variable : global_variables) {
    const unsigned n_ids =
      (this->writes.count(global_variable)
         ? this->writes.at(global_variable).size() * rounds
         : 0) + 1;
    this->bit_writes[global_variable] = 32 - __builtin_clz(n_ids);
  }

  for(auto &thread_and_pending : pending_trace_steps)
  {
    unsigned thread = thread_and_pending.first;
    auto last_position_it = last_trace_positions.find(thread);

    trace_position fallback{true, 0, 0, thread, 0};
    trace_position &pos = (last_position_it != last_trace_positions.end() &&
                           last_position_it->second.valid)
                            ? last_position_it->second
                            : fallback;

    for(auto pending_step : thread_and_pending.second)
    {
      if(pending_step->round_robin_exec_symbols.empty())
        annotate_with_position(*pending_step, pos);
    }
  }

  threads_bits = 0 ? 0 : 32 - __builtin_clz(threads + 1);
  rounds_bits = 0 ? 0 : 32 - __builtin_clz(rounds + 1);
}

void lazy_c_seqt::annotate_round_robin_trace_event(
  SSA_stept &step,
  unsigned label,
  unsigned num,
  unsigned thread,
  unsigned trace_order)
{
  step.round_robin_label = label;
  step.round_robin_num = num;
  step.round_robin_thread = thread;
  step.round_robin_trace_order = trace_order;
  if(step.is_decl())
    step.hidden = true;
  step.round_robin_exec_symbols.clear();
  step.round_robin_exec_symbols.reserve(rounds);

  for(std::size_t round = 1; round <= rounds; ++round)
    step.round_robin_exec_symbols.push_back(
      create_exec_symbol(label, num, thread, round));
}

symbol_exprt lazy_c_seqt::create_lazy_symbol(
  unsigned label,
  unsigned thread,
  size_t round,
  ssa_exprt lhs,
  typet type)
{
  std::string suffix = "_T" + std::to_string(thread) + "_L" +
                       std::to_string(label) + "_R" + std::to_string(round);
  irep_idt lazy_variable_name =
    id2string(to_symbol_expr(lhs).get_identifier()) + suffix;
  symbol_exprt lazy_variable_exprt{lazy_variable_name, type};

  return lazy_variable_exprt;
}

symbol_exprt
lazy_c_seqt::create_exec_symbol(unsigned label, unsigned num, unsigned thread, size_t round)
{
  for(const auto &exec : exec_vector)
  {
    if(exec.label == label && exec.num == num && exec.round == round && exec.thread == thread)
      return exec.symbol;
  }
  irep_idt exec_name = "Ex_T" + std::to_string(thread) + "_L" +
                       std::to_string(label) + "_N" + std::to_string(num) +
                       "_R" + std::to_string(round);
  symbol_exprt exec_symbol{exec_name, bool_typet{}};

  exec exec_struct{label, num, thread, round, exec_symbol};
  exec_vector.emplace_back(exec_struct);

  return exec_symbol;
}

symbol_exprt
lazy_c_seqt::create_exec_tot_symbol(/*messaget log,*/ symex_target_equationt &equation, unsigned label, unsigned num, unsigned thread)
{
  for(const auto &exec : exec_tot_vector)
  {
    if(exec.label == label && exec.num == num && exec.thread == thread)
      return exec.symbol;
  }

  exprt constraint = false_exprt{};
  irep_idt exec_name = "Ex_T" + std::to_string(thread) + "_L" +
                       std::to_string(label) + "_N" + std::to_string(num);
  symbol_exprt exec_symbol{exec_name, bool_typet{}};

  exec_tot exec_struct{label, num, thread, exec_symbol};
  exec_tot_vector.emplace_back(exec_struct);

  for (std::size_t round = 1; round <= rounds; round++) {
    constraint = or_exprt{constraint, create_exec_symbol(label,num,thread,round)};
  }
  constraint = equal_exprt{exec_symbol, constraint};
  simplify(constraint, ns);
  //log.warning() << format(constraint) << messaget::eom;
  equation.constraint(
    constraint, "exec tot constraint", equation.SSA_steps.begin()->source);

  return exec_symbol;
}

symbol_exprt lazy_c_seqt::create_enabled_symbol(
  unsigned label,
  unsigned thread,
  size_t round)
{
  for(const auto &enabled : enabled_vector)
  {
    if(
      enabled.label == label && enabled.round == round &&
      enabled.thread == thread)
      return enabled.symbol;
  }
  irep_idt enabled_name = "En_T" + std::to_string(thread) + "_L" +
                          std::to_string(label) + "_R" + std::to_string(round);
  symbol_exprt enabled_symbol{enabled_name, bool_typet{}};

  enabled enabled_struct{label, thread, round, enabled_symbol};
  enabled_vector.emplace_back(enabled_struct);

  return enabled_symbol;
}

symbol_exprt lazy_c_seqt::create_cs_symbol(size_t thread, size_t round)
{
  for(const auto &cs : cs_vector)
  {
    if(cs.thread == thread && cs.round == round)
      return cs.symbol;
  }
  irep_idt cs_name =
    "cs_T" + std::to_string(thread) + "_R" + std::to_string(round);
  symbol_exprt cs_symbol{cs_name, unsignedbv_typet{n_bit[thread]}};

  cs cs_struct{thread, round, cs_symbol};
  cs_vector.emplace_back(cs_struct);

  return cs_symbol;
}

symbol_exprt lazy_c_seqt::create_reach_symbol(unsigned label, size_t thread)
{
  for(const auto &reach : reach_vector)
  {
    if(reach.label == label && reach.thread == thread)
      return reach.symbol;
  }
  irep_idt reach_name =
    "reach_T" + std::to_string(thread) + "_L" + std::to_string(label);
  symbol_exprt reach_symbol{reach_name, bool_typet{}};

  reach reach_struct{label, thread, reach_symbol};
  reach_vector.emplace_back(reach_struct);

  return reach_symbol;
}

symbol_exprt lazy_c_seqt::create_active_thread_symbol(unsigned thread)
{
  irep_idt active_thread_name = "__CPROVER_active_thread_T" + std::to_string(thread);
  symbol_exprt active_thread_expr{active_thread_name, bool_typet{}};

  active_thread active_thread_struct{thread, 1, active_thread_expr};
  active_threads_vector.emplace(thread, active_thread_struct);

  return active_thread_expr;
}

symbol_exprt lazy_c_seqt::create_dr_thread_symbol(unsigned num)
{
  if (dr_thread.find(num) != dr_thread.end())
    return dr_thread.at(num);
  irep_idt thread_name = "t" + std::to_string(num);
  symbol_exprt thread_expr{thread_name, unsignedbv_typet{threads_bits}};

  dr_thread.emplace(num, thread_expr);
  return thread_expr;
}

symbol_exprt lazy_c_seqt::create_dr_round_symbol(unsigned num)
{
  if (dr_round.find(num) != dr_round.end())
    return dr_round.at(num);
  irep_idt round_name = "r" + std::to_string(num);
  symbol_exprt round_expr{round_name, unsignedbv_typet{rounds_bits}};

  dr_round.emplace(num, round_expr);

  return round_expr;
}

symbol_exprt lazy_c_seqt::create_dr_atom_symbol(unsigned num)
{
  if (dr_atom.find(num) != dr_atom.end())
    return dr_atom.at(num);
  irep_idt atom_name = "a" + std::to_string(num);
  symbol_exprt atom_expr{atom_name, bool_typet{}};

  dr_atom.emplace(num, atom_expr);

  return atom_expr;
}

symbol_exprt lazy_c_seqt::create_dr_loc_symbol(unsigned num)
{
  if (dr_loc.find(num) != dr_loc.end())
    return dr_loc.at(num);

  irep_idt loc_name = "loc" + std::to_string(num);
  symbol_exprt loc_expr{loc_name, size_type()};

  dr_loc.emplace(num, loc_expr);

  return loc_expr;
}
void lazy_c_seqt::create_winr_tot_symbol(
  symex_target_equationt &equation/*,message_handlert &message_handler*/)
{
  for(auto global_variable : global_variables)
  {
    if(this->writes.count(global_variable) == 0)
      continue;

    auto sorted_writes = this->writes.at(global_variable);
    std::sort(sorted_writes.begin(), sorted_writes.end(),
      [](const shared_event &a, const shared_event &b) {
        return std::tie(a.thread, a.label, a.num) > std::tie(b.thread, b.label, b.num);
      });
    for(std::size_t round = rounds + 1; round-- > 0; )
    {
      for(const auto &write : sorted_writes)
      {
        create_WINR_symbol(global_variable, write.thread, write.label, write.num, round,equation/*, message_handler*/);
      }
    }
  }
}

void lazy_c_seqt::create_lw_tot_symbol(
  symex_target_equationt &equation/*,message_handlert &message_handler*/) {
  for(auto global_variable : global_variables)
  {
    if(this->reads.count(global_variable) == 0)
      continue;
    // ascending lex (thread, label, num) so LW(prev_of_prev) is cached when needed
    auto sorted_reads = this->reads.at(global_variable);
    std::sort(sorted_reads.begin(), sorted_reads.end(),
      [](const shared_event &a, const shared_event &b) {
        return std::tie(a.thread, a.label, a.num) < std::tie(b.thread, b.label, b.num);
      });
    for(std::size_t round = 0; round <= rounds; ++round){
      for(const auto &read : sorted_reads)
      {
        create_LW_symbol(global_variable,read.thread, read.label,read.num, round, equation/*, message_handler*/);
      }
    }
  }
}

void lazy_c_seqt::create_atomic_canonical(
  symex_target_equationt &equation/*,message_handlert &message_handler*/) {
  for(std::size_t round = 1; round <= rounds; ++round){
    for(const auto &entry : atomic_blocks)
    {
      const atomic_block &b = entry.second;
      if(b.label == 0)
        continue;
      if(b.reads.empty() && b.writes.empty())
        continue;
      const auto &src = !b.reads.empty()
        ? b.reads.begin()->second.front().s_it->source
        : b.writes.begin()->second.front().s_it->source;

      const exprt cs_1 = create_enabled_symbol(b.label, b.thread, round);
      exprt cs = equal_exprt(create_cs_symbol(b.thread, round-1), from_integer(b.label, unsignedbv_typet(n_bit[b.thread])));
      exprt fire_cond = and_exprt(cs_1, cs);
      exprt abr = b.reads.empty()
        ? exprt(false_exprt{})
        : exprt(create_ABR(b.reads, round, b.label, b.thread, equation/*,message_handlert &message_handler*/));
      exprt abw = b.writes.empty()
        ? exprt(false_exprt{})
        : exprt(create_ABW(b.writes, round, b.label, b.thread, equation/*,message_handlert &message_handler*/));
      exprt expression = implies_exprt(fire_cond, or_exprt(abr, abw));
      simplify(expression, ns);
      equation.constraint(expression, "atomic_block_canonical", src);
    }
  }
}

symbol_exprt lazy_c_seqt::create_ABR(
  const std::map<irep_idt, std::vector<shared_event>> &reads, std::size_t round,
  unsigned label, unsigned thread,
  symex_target_equationt &equation/*,message_handlert &message_handler*/) {
  exprt result = false_exprt{};
  const symex_targett::sourcet *src = nullptr;
  for(auto global_variable : global_variables){
    if(reads.count(global_variable) == 0)
      continue;
    for(const auto &rd : reads.at(global_variable))
    {
      if(src == nullptr)
        src = &rd.s_it->source;


      std::optional<lazy_variable> pw =
        get_previous_write(rd.thread, rd.label, rd.num, round, global_variable);
      bool prev_outside =
        !pw.has_value() ||
        pw->round < round ||
        (pw->round == round && pw->thread < rd.thread) ||
        (pw->round == round && pw->thread == rd.thread && pw->label < rd.label);
      if(!prev_outside)
        continue;
      exprt exec = create_exec_symbol(rd.label, rd.num, rd.thread, round);


      // ABR = paper eq(2) puro. La precondizione di delay (cs_t(r-2)==l) sta nel
      // firing guard di create_atomic_canonical, non qui.
      exprt lw_neq = notequal_exprt{
        create_LW_symbol(global_variable, rd.thread, rd.label, rd.num, round, equation),
        create_LW_symbol(global_variable, rd.thread, rd.label, rd.num, round - 1, equation)};
      result = or_exprt{result, and_exprt{exec, lw_neq}};
    }
  }
  irep_idt abr_r = "ABR_T" + std::to_string(thread) + "_L" + std::to_string(label) +
     "_R" + std::to_string(round);
  symbol_exprt sym{abr_r, bool_typet{}};
  simplify(result, ns);
  equation.constraint(equal_exprt{sym, result}, "abr", *src);
  atomic_block_rounds.push_back({thread, label, static_cast<unsigned>(round), sym});
  return sym;
}
symbol_exprt lazy_c_seqt::create_ABW(
  const std::map<irep_idt, std::vector<shared_event>> &writes, std::size_t round,
  unsigned label, unsigned thread,
  symex_target_equationt &equation/*,message_handlert &message_handler*/)
{
  exprt result = false_exprt{};
  const symex_targett::sourcet *src = nullptr;
  for(auto global_variable : global_variables){
    if(writes.count(global_variable) == 0)
      continue;
    for(const auto &write : writes.at(global_variable)) {
      if(src == nullptr)
        src = &write.s_it->source;
      exprt exec = create_exec_symbol(write.label, write.num, write.thread, round);

      exprt id_prev = get_id_symbol(write, round - 1,global_variable);
      exprt id_curr = get_id_symbol(write, round,global_variable);
      exprt winr_control= equal_exprt(create_WINR_symbol(global_variable, write.thread, write.label+1, 0, round,equation/*, message_handler*/),id_curr);
      exprt write_a = greater_than_exprt(id_prev, create_WINR_symbol(global_variable, write.thread, write.label+1, 0, round - 1,equation/*, message_handler*/));
      exprt write_b = and_exprt(winr_control, less_than_exprt(id_prev, create_LW_symbol(global_variable,
        write.thread, write.label,write.num,round,equation/*, message_handler*/)));
      result = or_exprt{result, and_exprt{exec, or_exprt{write_a, write_b}}};
    }
  }
  irep_idt abw_r = "ABW_T" + std::to_string(thread) + "_L" + std::to_string(label) +
     "_R" + std::to_string(round);
  symbol_exprt sym{abw_r, bool_typet{}};
  simplify(result, ns);
  equation.constraint(equal_exprt{sym, result}, "abw", *src);
  atomic_block_rounds.push_back({thread, label, static_cast<unsigned>(round), sym});
  return sym;
}

void lazy_c_seqt::build_atomic_blocks(){
  for(const auto &entry : reads)
  {
    const irep_idt &var = entry.first;
    for(const auto &rd : entry.second)
    {
      auto &b = atomic_blocks[{rd.thread, rd.label}];
      b.thread = rd.thread;
      b.label = rd.label;
      b.reads[var].push_back(rd);
    }
  }
  for(const auto &entry : writes)
  {
    const irep_idt &var = entry.first;
    for(const auto &wr : entry.second)
    {
      auto &b = atomic_blocks[{wr.thread, wr.label}];
      b.thread = wr.thread;
      b.label = wr.label;
      b.writes[var].push_back(wr);
    }
  }
}


symbol_exprt lazy_c_seqt::create_LW_symbol(irep_idt variable, unsigned thread, unsigned label, unsigned num,size_t round,
  symex_target_equationt &equation/*,message_handlert &message_handler*/)
{
  const unsignedbv_typet type(bit_writes[variable]);
  const auto &src = equation.SSA_steps.begin()->source;
  std::optional<lazy_variable> prev_op = get_previous_write(thread, label, num, round, variable);


  auto emit = [&](unsigned t, unsigned l, unsigned n, size_t r, const exprt &rhs) {
    for(const auto &lw : lw_variables[variable])
      if(lw.round == r && lw.label == l && lw.num == n && lw.thread == t)
        return lw.exptr_id;
    irep_idt lw_id = "LW_T" + std::to_string(t) + "_L" + std::to_string(l) +
      "_N" + std::to_string(n) + "_R" + std::to_string(r) + "_V" + id2string(variable);
    symbol_exprt sym{lw_id, type};
    exprt rhs_s = rhs;
    simplify(rhs_s, ns);
    equation.constraint(equal_exprt{sym, rhs_s}, "lw canonical", src);
    lw_variables[variable].push_back({r, l, n, t, sym});
    return sym;
  };

  if(!prev_op.has_value())
    return emit(0, 0, 0, 0, from_integer(0, type));

  const lazy_variable &prev = *prev_op;


  for(const auto &lw : lw_variables[variable])
    if(lw.round == prev.round && lw.label == prev.label && lw.num == prev.num && lw.thread == prev.thread)
      return lw.exptr_id;

  if(prev.round == 0)
    return emit(prev.thread, prev.label, prev.num, 0, from_integer(0, type));

  symbol_exprt exec = create_exec_symbol(prev.label, prev.num, prev.thread, prev.round);
  std::optional<lazy_variable> prev_op_ = get_previous_write(prev.thread, prev.label, prev.num, prev.round, variable);
  exprt inner_lw_expr = from_integer(0, type);
  if(prev_op_.has_value()) {
    lazy_variable prev_value = *prev_op_;

    bool found = false;
    for(const auto &lw : lw_variables[variable])
      if(lw.round == prev_value.round && lw.label == prev_value.label && lw.num == prev_value.num && lw.thread == prev_value.thread)
      { inner_lw_expr = lw.exptr_id; found = true; break; }
    if(!found)

      inner_lw_expr = create_LW_symbol(variable, prev.thread, prev.label, prev.num, prev.round, equation);
  }
  return emit(prev.thread, prev.label, prev.num, prev.round,
    if_exprt{exec, from_integer(prev.id, type), inner_lw_expr});
}

symbol_exprt lazy_c_seqt::create_WINR_symbol(irep_idt variable, unsigned thread, unsigned label, unsigned num, size_t round, symex_target_equationt &equation)
{
  const unsignedbv_typet type(bit_writes[variable]);
  const auto &src = equation.SSA_steps.begin()->source;
  std::optional<lazy_variable_read> next_op = get_next_read(thread, label, num, round, variable);

  auto emit = [&](unsigned t, unsigned l, unsigned n, size_t r, const exprt &rhs) {
    for(const auto &w : winr_variables[variable])
      if(w.round == r && w.label == l && w.num == n && w.thread == t)
        return w.exptr_id;
    irep_idt winr_id = "WINR_T" + std::to_string(t) + "_L" + std::to_string(l) +
      "_N" + std::to_string(n) + "_R" + std::to_string(r) + "_V" + id2string(variable);
    symbol_exprt sym{winr_id, type};
    exprt rhs_s = rhs;
    simplify(rhs_s, ns);
    equation.constraint(equal_exprt{sym, rhs_s}, "winr canonical", src);
    winr_variables[variable].push_back({r, l, n, t, sym});
    return sym;
  };

  if(!next_op.has_value()) {
    unsigned max_val = 0;
    for(const auto &[k, v] : labels)
      if(v > max_val) max_val = v;
    return emit(threads, max_val, 0, rounds,
      from_integer((1ULL << bit_writes[variable]) - 1, unsignedbv_typet(bit_writes[variable])));
  }

  const lazy_variable_read &next = *next_op;

  for(const auto &w : winr_variables[variable])
    if(w.round == next.round && w.label == next.label && w.num == next.num && w.thread == next.thread)
      return w.exptr_id;
  std::optional<lazy_variable_read> next_op_ =
    get_next_read(next.thread, next.label, next.num, next.round, variable, true);

  symbol_exprt exec = create_exec_symbol(next.label, next.num, next.thread, next.round);
  symbol_exprt lw   = create_LW_symbol(variable, next.thread, next.label, next.num, next.round, equation);

  exprt inner_winr_expr =
    from_integer((1ULL << bit_writes[variable]) - 1, unsignedbv_typet(bit_writes[variable]));

  if(next_op_.has_value()) {
    lazy_variable_read next_value = *next_op_;
    bool found = false;
    for(const auto &winr : winr_variables[variable])
      if(winr.round == next_value.round && winr.label == next_value.label &&
         winr.num == next_value.num && winr.thread == next_value.thread)
      { inner_winr_expr = winr.exptr_id; found = true; break; }
    if(!found)
      inner_winr_expr = create_WINR_symbol(
        variable, next_value.thread, next_value.label, next_value.num, next_value.round, equation);
  }

  return emit(next.thread, next.label, next.num, next.round,
              if_exprt{exec, lw, inner_winr_expr});
}
exprt lazy_c_seqt::get_id_symbol(const shared_event &event, std::size_t round, irep_idt variable)
{
  const unsignedbv_typet type(bit_writes[variable]);
  unsigned id = lazy_variables.at(variable).front().id;
  for(const auto &lazy_variable : lazy_variables.at(variable)) {
    if(lazy_variable.label == event.label && lazy_variable.num == event.num && lazy_variable.round == round && lazy_variable.thread == event.thread) {
      id = lazy_variable.id;
      break;
    }
  }
  return from_integer(id, type);
}
std::optional<lazy_c_seqt::lazy_variable> lazy_c_seqt::get_previous_write(unsigned thread, unsigned label, unsigned num, std::size_t round, irep_idt variable)
{
  if(lazy_variables.count(variable) == 0)
    return std::nullopt;
  lazy_variable previous = lazy_variables.at(variable).front();
  auto& front_var = lazy_variables.at(variable).front();
  for(const auto &lazy_variable : lazy_variables.at(variable))
  {
    if(round > lazy_variable.round)
    {
      previous = lazy_variable;
      continue;
    }
    if(round == lazy_variable.round && thread > lazy_variable.thread)
    {
      previous = lazy_variable;
      continue;
    }
    if(
      round == lazy_variable.round && thread == lazy_variable.thread &&
      label > lazy_variable.label)
    {
      previous = lazy_variable;
      continue;
    }
    if(
      round == lazy_variable.round && thread == lazy_variable.thread &&
      label == lazy_variable.label && num > lazy_variable.num)
    {
      previous = lazy_variable;
      continue;
    }
    if (previous.round == front_var.round &&
      previous.label == front_var.label &&
      previous.thread == front_var.thread &&
      previous.num == front_var.num &&  (label > lazy_variables.at(variable).front().label || (label <= lazy_variables.at(variable).front().label && num > lazy_variables.at(variable).front().num)))
      return std::nullopt;
    return previous;
  }
  return previous;
}
void lazy_c_seqt::create_lazy_variable_read() {
  for(auto global_variable : global_variables)
  {
    if(this->reads.count(global_variable) == 0)
      continue;
    for(std::size_t round = rounds; round >= 1; --round) {
      for(const auto &read : this->reads.at(global_variable)) {
        lazy_variable_read lazy_variable_read{round,read.label,read.num, read.thread};
        lazy_variables_read[global_variable].emplace_back(lazy_variable_read);
        {
        }
      }
    }
  }
}

std::optional<lazy_c_seqt::lazy_variable_read>
lazy_c_seqt::get_next_read(unsigned thread, unsigned label, unsigned num,
  std::size_t round, irep_idt variable, bool strict)
{
  if(lazy_variables_read.count(variable) == 0)
    return std::nullopt;
  std::optional<lazy_variable_read> best;
  const auto qk = std::tie(round, thread, label, num);
  for(const auto &lv : lazy_variables_read.at(variable))
  {
    const auto lk = std::tie(lv.round, lv.thread, lv.label, lv.num);
    if(strict ? lk <= qk : lk < qk)
      continue;
    if(!best.has_value())
    { best = lv; continue; }
    const auto bk = std::tie(best->round, best->thread, best->label, best->num);
    if(lk < bk) best = lv;
  }
  return best;
}
