/// \file
/// LazyCSeq context-bounded concurrency SSA transformation

#ifndef CPROVER_GOTO_SYMEX_LAZY_C_SEQ_H
#define CPROVER_GOTO_SYMEX_LAZY_C_SEQ_H

#include "symex_target_equation.h"

#include <optional>

class lazy_c_seqt
{
public:
  explicit lazy_c_seqt(const namespacet &ns, const std::size_t rounds, const bool datarace)
    : ns(ns), rounds(rounds), datarace(datarace)
  {
  }

  void operator()(symex_target_equationt &, message_handlert &);

private:
  const namespacet &ns;
  const std::size_t rounds;
  const bool datarace;

  struct shared_event
  {
    symex_target_equationt::SSA_stepst::const_iterator s_it;
    unsigned label;
    unsigned num;
    unsigned thread;
  };
  struct lazy_variable
  {
    std::size_t round;
    unsigned label;
    unsigned num;
    unsigned thread;
    symbol_exprt symbol;
  };
  struct active_thread
  {
    unsigned thread;
    std::size_t l2;
    symbol_exprt symbol;
  };
  struct exec
  {
    unsigned label;
    unsigned thread;
    std::size_t round;
    symbol_exprt symbol;
  };
  struct exec_tot
  {
    unsigned label;
    unsigned thread;
    symbol_exprt symbol;
  };
  struct enabled
  {
    unsigned label;
    unsigned thread;
    std::size_t round;
    symbol_exprt symbol;
  };
  struct cs
  {
    std::size_t thread;
    std::size_t round;
    symbol_exprt symbol;
  };
  struct reach
  {
    unsigned label;
    std::size_t thread;
    symbol_exprt symbol;
  };

  std::size_t threads = 0;
  std::size_t threads_bits;
  std::size_t rounds_bits;
  std::unordered_map<unsigned, symbol_exprt> dr_thread;
  std::unordered_map<unsigned, symbol_exprt> dr_round;
  std::unordered_set<irep_idt> global_variables;
  std::unordered_map<irep_idt, std::vector<shared_event>> writes;
  std::unordered_map<irep_idt, std::vector<shared_event>> reads;
  std::vector<shared_event> blocking_events;
  std::vector<shared_event> shared_events;
  std::unordered_map<irep_idt, std::vector<lazy_variable>> lazy_variables;
  std::unordered_map<unsigned, active_thread> active_threads_vector;
  std::vector<exec> exec_vector;
  std::vector<exec_tot> exec_tot_vector;
  std::vector<enabled> enabled_vector;
  std::vector<cs> cs_vector;
  std::vector<reach> reach_vector;
  std::vector<std::pair<unsigned, std::pair<std::size_t, std::size_t>>>
    atomic_sections; // < thread < start_label, end_label > >
  std::unordered_map<unsigned, unsigned> n_bit;
  std::unordered_map<unsigned, unsigned> labels;
  std::unordered_map<unsigned,std::unordered_map<unsigned, exprt>> guards; // < thread, < label, guard > >

  void handling_active_threads(
    symex_target_equationt &equation/*,
    message_handlert &message_handler*/);

  void check_shared_event(
    symex_target_equationt &equation/*,
    message_handlert &message_handler*/);

  void handling_atomic_sections(
    symex_target_equationt &equation/*,
    message_handlert &message_handler*/);

  void collect_reads_and_writes(
    const symex_target_equationt::SSA_stepst &ssa_steps/*,
    message_handlert &message_handler*/);

  void create_write_constraints(
    symex_target_equationt &equation/*,
    message_handlert &message_handler*/);

  void create_read_constraints(
    symex_target_equationt &equation/*,
    message_handlert &message_handler*/);

  std::optional<symbol_exprt> previous_shared(
    irep_idt variable,
    unsigned label,
    unsigned num,
    unsigned thread,
    std::size_t round);

  void create_cs_constraint(
    symex_target_equationt &equation/*,
    message_handlert &message_handler*/);

  void create_reach_constraint(
    symex_target_equationt &equation/*,
    message_handlert &message_handler*/);

  void handling_guards(
    symex_target_equationt &equation/*,
    message_handlert &message_handler*/);

  void handling_datarace(
    symex_target_equationt &equation,
    message_handlert &message_handler);

  symbol_exprt phase_1(messaget log, symex_target_equationt &equation, irep_idt v);
  symbol_exprt phase_2(messaget log, symex_target_equationt &equation, irep_idt v);
  symbol_exprt same_round(messaget log, symex_target_equationt &equation);
  symbol_exprt no_interf(messaget log, symex_target_equationt &equation);

  symbol_exprt create_lazy_symbol(
    unsigned label,
    unsigned thread,
    std::size_t round,
    ssa_exprt lhs,
    typet type);

  symbol_exprt
  create_exec_symbol(unsigned label, unsigned thread, std::size_t round);

  symbol_exprt
  create_exec_tot_symbol(messaget log, symex_target_equationt &equation, unsigned label, unsigned thread);

  symbol_exprt
  create_enabled_symbol(unsigned label, unsigned thread, std::size_t round);

  symbol_exprt create_cs_symbol(std::size_t thread, std::size_t round);

  symbol_exprt create_reach_symbol(unsigned label, std::size_t thread);

  symbol_exprt create_active_thread_symbol(unsigned thread);

  symbol_exprt create_dr_thread_symbol(unsigned num);

  symbol_exprt create_dr_round_symbol(unsigned num);

  void create_active_thread_statements(
    const symex_targett::sourcet &source,
    exprt &guard,
    unsigned int atomic_section_id,
    unsigned &thread,
    symex_target_equationt &equation/*,
    message_handlert &message_handler*/,
    const exprt &value);
};

#endif //CPROVER_GOTO_SYMEX_LAZY_C_SEQ_H
