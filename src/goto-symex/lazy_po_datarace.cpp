/// \file
/// lazy_po: data-race encoding (--datarace)

#include "lazy_po.h"
#include <util/ssa_expr.h>
#include <cctype>
#include <optional>
#include <tuple>
#include <util/bitvector_types.h>
#include <util/expr_util.h>
#include <util/pointer_offset_size.h>
#include <util/byte_operators.h>
#include <string>
#include <map>
#include <algorithm>
#include <set>
#include <unordered_set>
#include <cstdlib>
#include <iostream>
#include <chrono>
#include <fstream>
#include <functional>
#include <thread>
#include <util/cprover_prefix.h>
#include <util/format.h>
#include <util/format_expr.h>
#include <util/pointer_expr.h>
#include <util/c_types.h>
#include <util/prefix.h>
#include <util/expr_util.h>
#include <ansi-c/expr2c.h>
#include <util/simplify_expr.h>
#include <util/source_location.h>

#include <util/arith_tools.h>
#include <util/invariant.h>
#include <util/symbol.h>

#include "lazy_po_internal.h"

exprt lazy_pot::phase_1(symex_target_equationt &equation, irep_idt v) {

  irep_idt phase_1_name =  as_string(v) + "_phase_1";
  symbol_exprt phase_1_symbl{phase_1_name, bool_typet{}};

  exprt phase_1_exp = false_exprt{};
  exprt::operandst phase_1_ops;

  for (std::size_t thread = 0; thread <= threads; thread++) {
    irep_idt phase_1_t_name =  as_string(v) + "_phase_1_T" + std::to_string(thread);
    symbol_exprt phase_1_t_symbl{phase_1_t_name, bool_typet{}};


    exprt phase_1_t_exp = false_exprt{};
    exprt::operandst phase_1_t_ops;

    if(this->writes.count(v) != 0) {
      for (auto write : writes.at(v)) {
        std::string func = id2string(write.s_it->source.pc->source_location().get_function());
        // pthread_create's own write to its thread-ID output parameter is
        // user-visible data (the caller supplied that pointer), not library
        // bookkeeping -- unlike pthread_mutex_lock/_unlock/_init, pthread_join,
        // pthread_cond_wait and friends, which only ever touch their own
        // internal state objects here. Excluding it hid a genuine race: see
        // ~/tid_write_race.c, a 9-line reproducer where one thread's
        // pthread_create races an unsynchronised read of the thread-ID global
        // in another thread, reported SUCCESSFUL with the blanket exclusion.
        bool is_pthread = (func.rfind("pthread", 0) == 0) && func != "pthread_create";
        if (write.thread != thread || is_pthread || write.race_exempt)
          continue;
        irep_idt phase_1_t_v_name =  as_string(v) + "_phase_1_T" + std::to_string(thread) + "_L" + std::to_string(write.label) + "_N" + std::to_string(write.num);
        symbol_exprt phase_1_t_v_symbl{phase_1_t_v_name, bool_typet{}};

        phase_1_t_ops.push_back(phase_1_t_v_symbl);

        int atom = write.s_it->in_program_atomic_section();
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
        equation.constraint(
          phase_1_t_v_exp, "datarace constraint", equation.SSA_steps.begin()->source);
      }
    }
    // A thread with no candidate access contributes false: leave it out,
    // rather than define its symbol as false (see handling_datarace).
    if(phase_1_t_ops.empty())
      continue;
    phase_1_ops.push_back(phase_1_t_symbl);
    phase_1_t_exp = equal_exprt {phase_1_t_symbl, disjunction(phase_1_t_ops)};
    simplify(phase_1_t_exp, ns);
    equation.constraint(
      phase_1_t_exp, "datarace constraint", equation.SSA_steps.begin()->source);
  }

  if(phase_1_ops.empty())
    return false_exprt{};
  phase_1_exp = equal_exprt {phase_1_symbl, disjunction(phase_1_ops)};
  simplify(phase_1_exp, ns);
  equation.constraint(
    phase_1_exp, "datarace constraint", equation.SSA_steps.begin()->source);

  return phase_1_symbl;
}

exprt lazy_pot::phase_2(symex_target_equationt &equation, irep_idt v) {
  irep_idt phase_2_name = as_string(v) + "_phase_2";
  symbol_exprt phase_2_symbl{phase_2_name, bool_typet{}};

  exprt phase_2_exp = false_exprt{};
  exprt::operandst phase_2_ops;

  for (std::size_t thread = 0; thread <= threads; thread++) {
    irep_idt phase_2_t_name = as_string(v) + "_phase_2_T" + std::to_string(thread);
    symbol_exprt phase_2_t_symbl{phase_2_t_name, bool_typet{}};


    exprt phase_2_t_exp = false_exprt{};
    exprt::operandst phase_2_t_ops;

    if(this->writes.count(v) != 0) {
      for (auto write : writes.at(v)) {
        std::string func = id2string(write.s_it->source.pc->source_location().get_function());
        // pthread_create is exempted above handling_datarace's first check of
        // this shape -- see the comment there.
        bool is_pthread = (func.rfind("pthread", 0) == 0) && func != "pthread_create";
        if (write.thread != thread || is_pthread || write.race_exempt)
          continue;
        irep_idt phase_2_t_v_name = as_string(v) + "_phase_2_w_T" + std::to_string(thread) + "_L" + std::to_string(write.label) + "_N" + std::to_string(write.num);
        symbol_exprt phase_2_t_v_symbl{phase_2_t_v_name, bool_typet{}};

        phase_2_t_ops.push_back(phase_2_t_v_symbl);

        int atom = write.s_it->in_program_atomic_section();
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
        equation.constraint(
          phase_2_t_v_exp, "datarace constraint", equation.SSA_steps.begin()->source);
      }
    }
    if(this->reads.count(v) != 0) {
      for (auto read : reads.at(v)) {
        std::string func = id2string(read.s_it->source.pc->source_location().get_function());
        // pthread_create is exempted above handling_datarace's first check of
        // this shape -- see the comment there.
        bool is_pthread = (func.rfind("pthread", 0) == 0) && func != "pthread_create";
        if (read.thread != thread || is_pthread || read.race_exempt)
          continue;
        irep_idt phase_2_t_v_name =  as_string(v) + "_phase_2_r_T" + std::to_string(thread) + "_L" + std::to_string(read.label) + "_N" + std::to_string(read.num);
        symbol_exprt phase_2_t_v_symbl{phase_2_t_v_name, bool_typet{}};

        phase_2_t_ops.push_back(phase_2_t_v_symbl);

        int atom = read.s_it->in_program_atomic_section();
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
        equation.constraint(
          phase_2_t_v_exp, "datarace constraint", equation.SSA_steps.begin()->source);
      }
    }
    // A thread with no candidate access contributes false: leave it out,
    // rather than define its symbol as false (see handling_datarace).
    if(phase_2_t_ops.empty())
      continue;
    phase_2_ops.push_back(phase_2_t_symbl);
    phase_2_t_exp = equal_exprt {phase_2_t_symbl, disjunction(phase_2_t_ops)};
    simplify(phase_2_t_exp, ns);
    equation.constraint(
      phase_2_t_exp, "datarace constraint", equation.SSA_steps.begin()->source);
  }

  if(phase_2_ops.empty())
    return false_exprt{};
  phase_2_exp = equal_exprt {phase_2_symbl, disjunction(phase_2_ops)};
  simplify(phase_2_exp, ns);
  equation.constraint(
    phase_2_exp, "datarace constraint", equation.SSA_steps.begin()->source);

  return phase_2_symbl;
}

symbol_exprt lazy_pot::same_round(symex_target_equationt &equation) {
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
  equation.constraint(
    same_round_exp, "datarace constraint", equation.SSA_steps.begin()->source);

  return same_round_symbl;
}

symbol_exprt lazy_pot::no_interf(symex_target_equationt &equation) {
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
        // cs(t,round) == cs(t,round-1): (C2) already gives
        // GE(round-1,i) => GE(round,i) for every i, so only the converse
        // direction needs asserting here for full equality.
        exprt cs_eq_1 = true_exprt{};
        for(unsigned i = 1; i <= labels[thread] + 1; ++i)
          cs_eq_1 = and_exprt{
            cs_eq_1,
            implies_exprt{
              create_ge_symbol(thread, round, i),
              create_ge_symbol(thread, round - 1, i)}};
        exp1r = implies_exprt{
          equal_exprt{create_dr_round_symbol(1), from_integer({round}, unsignedbv_typet{rounds_bits})},
          cs_eq_1
        };
      if (round > 1) {
        exprt cs_eq_2 = true_exprt{};
        for(unsigned i = 1; i <= labels[thread] + 1; ++i)
          cs_eq_2 = and_exprt{
            cs_eq_2,
            implies_exprt{
              create_ge_symbol(thread, round, i),
              create_ge_symbol(thread, round - 1, i)}};
        exp2r = implies_exprt{
          equal_exprt{create_dr_round_symbol(2), from_integer({round}, unsignedbv_typet{rounds_bits})},
          cs_eq_2
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
    equation.constraint(
      no_interf_t_exp, "datarace constraint", equation.SSA_steps.begin()->source);

    no_interf_exp = and_exprt{no_interf_exp, no_interf_t_symbl};
  }
  no_interf_exp = equal_exprt{no_interf_symbl, no_interf_exp};
  simplify(no_interf_exp, ns);
  equation.constraint(
    no_interf_exp, "datarace constraint", equation.SSA_steps.begin()->source);

  return no_interf_symbl;
}

// __SZH_DR_ADD_BEGIN__
// Mirror of phase_1, but iterating reads instead of writes, using roles
// 3/4 (create_dr_thread_symbol(3) etc.) instead of 1/2. phase_1/phase_2
// (roles 1/2) can only witness a race where the mandatory-write access
// (role 1) executes in the same round as, or one round before, the
// second access (role 2) -- same_round's round relationship (tied to
// which of dr_thread(1)/dr_thread(2) is numerically smaller, encoding
// the fixed round-robin sweep order within a round) never allows
// dr_round(2) < dr_round(1). That misses a real race where the
// chronologically-first access is a READ and a conflicting WRITE happens
// later: no witness pairing exists in the original encoding for it,
// regardless of --unwind/--rounds (confirmed by exhaustive offline
// search: 110+99 unwind/rounds combinations up to unwind=44/rounds=20,
// none resolved several real SV-COMP benchmarks hitting exactly this
// pattern). phase_1_swap/phase_2_swap/same_round_swap/no_interf_swap
// mirror the exact same machinery with the roles reversed (role 3 =
// read, role 4 = write) and role 3/4's own independent dr_thread/
// dr_round/dr_atom/dr_loc symbols (create_dr_*_symbol is a generic,
// num-indexed symbol cache -- roles 3/4 are entirely fresh SAT variables,
// unrelated to roles 1/2). The final detection ORs both pairings
// together in handling_datarace, so this is purely additive: it can only
// add coverage, never remove or alter what roles 1/2 already detect.
exprt lazy_pot::phase_1_swap(symex_target_equationt &equation, irep_idt v) {

  irep_idt phase_1_name =  as_string(v) + "_phase_1_swap";
  symbol_exprt phase_1_symbl{phase_1_name, bool_typet{}};

  exprt phase_1_exp = false_exprt{};
  exprt::operandst phase_1_ops;

  for (std::size_t thread = 0; thread <= threads; thread++) {
    irep_idt phase_1_t_name =  as_string(v) + "_phase_1_swap_T" + std::to_string(thread);
    symbol_exprt phase_1_t_symbl{phase_1_t_name, bool_typet{}};


    exprt phase_1_t_exp = false_exprt{};
    exprt::operandst phase_1_t_ops;

    if(this->reads.count(v) != 0) {
      for (auto read : reads.at(v)) {
        std::string func = id2string(read.s_it->source.pc->source_location().get_function());
        // pthread_create is exempted above handling_datarace's first check of
        // this shape -- see the comment there.
        bool is_pthread = (func.rfind("pthread", 0) == 0) && func != "pthread_create";
        if (read.thread != thread || is_pthread || read.race_exempt)
          continue;
        irep_idt phase_1_t_v_name =  as_string(v) + "_phase_1_swap_T" + std::to_string(thread) + "_L" + std::to_string(read.label) + "_N" + std::to_string(read.num);
        symbol_exprt phase_1_t_v_symbl{phase_1_t_v_name, bool_typet{}};

        phase_1_t_ops.push_back(phase_1_t_v_symbl);

        int atom = read.s_it->in_program_atomic_section();
        exprt phase_1_t_v_exp =
          and_exprt{
            equal_exprt{create_dr_thread_symbol(3), from_integer({thread}, unsignedbv_typet{threads_bits})},
            and_exprt{
              create_exec_tot_symbol(/*log,*/ equation, read.label, read.num, thread),
              and_exprt{
                equal_exprt{create_dr_atom_symbol(3), from_integer({atom}, bool_typet{})},
                equal_exprt{create_dr_loc_symbol(3), typecast_exprt(read.where, size_type())}
                }
              }
          };

        exprt exp2 = true_exprt{};
        for (std::size_t round = 1; round <= rounds; round++) {
          exprt enabled_exp = true_exprt{};
          if (read.label < labels[read.thread]) {
            enabled_exp = not_exprt{create_enabled_symbol(read.label+1,thread,round)};
          }
          exprt exp = implies_exprt{
            create_exec_symbol(read.label,read.num,thread,round),
            and_exprt{
              equal_exprt{create_dr_round_symbol(3),from_integer({round}, unsignedbv_typet{rounds_bits})},
              enabled_exp
            }};
          exp2 = and_exprt{exp2, exp};
        }
        phase_1_t_v_exp = equal_exprt{
          phase_1_t_v_symbl,
          and_exprt{phase_1_t_v_exp, exp2}};

        simplify(phase_1_t_v_exp, ns);
        equation.constraint(
          phase_1_t_v_exp, "datarace constraint", equation.SSA_steps.begin()->source);
      }
    }
    // A thread with no candidate access contributes false: leave it out,
    // rather than define its symbol as false (see handling_datarace).
    if(phase_1_t_ops.empty())
      continue;
    phase_1_ops.push_back(phase_1_t_symbl);
    phase_1_t_exp = equal_exprt {phase_1_t_symbl, disjunction(phase_1_t_ops)};
    simplify(phase_1_t_exp, ns);
    equation.constraint(
      phase_1_t_exp, "datarace constraint", equation.SSA_steps.begin()->source);
  }

  if(phase_1_ops.empty())
    return false_exprt{};
  phase_1_exp = equal_exprt {phase_1_symbl, disjunction(phase_1_ops)};
  simplify(phase_1_exp, ns);
  equation.constraint(
    phase_1_exp, "datarace constraint", equation.SSA_steps.begin()->source);

  return phase_1_symbl;
}

// Mirror of phase_2, but writes-only (the read-iterating half is
// dropped, since role 3 already covers the read side for this pairing;
// a race needs at least one write, and role 3 = read here), using role 4.
exprt lazy_pot::phase_2_swap(symex_target_equationt &equation, irep_idt v) {
  irep_idt phase_2_name = as_string(v) + "_phase_2_swap";
  symbol_exprt phase_2_symbl{phase_2_name, bool_typet{}};

  exprt phase_2_exp = false_exprt{};
  exprt::operandst phase_2_ops;

  for (std::size_t thread = 0; thread <= threads; thread++) {
    irep_idt phase_2_t_name = as_string(v) + "_phase_2_swap_T" + std::to_string(thread);
    symbol_exprt phase_2_t_symbl{phase_2_t_name, bool_typet{}};


    exprt phase_2_t_exp = false_exprt{};
    exprt::operandst phase_2_t_ops;

    if(this->writes.count(v) != 0) {
      for (auto write : writes.at(v)) {
        std::string func = id2string(write.s_it->source.pc->source_location().get_function());
        // pthread_create is exempted above handling_datarace's first check of
        // this shape -- see the comment there.
        bool is_pthread = (func.rfind("pthread", 0) == 0) && func != "pthread_create";
        if (write.thread != thread || is_pthread || write.race_exempt)
          continue;
        irep_idt phase_2_t_v_name = as_string(v) + "_phase_2_swap_w_T" + std::to_string(thread) + "_L" + std::to_string(write.label) + "_N" + std::to_string(write.num);
        symbol_exprt phase_2_t_v_symbl{phase_2_t_v_name, bool_typet{}};

        phase_2_t_ops.push_back(phase_2_t_v_symbl);

        int atom = write.s_it->in_program_atomic_section();
        exprt phase_2_t_v_exp =
          and_exprt{
            equal_exprt{create_dr_thread_symbol(4), from_integer({thread}, unsignedbv_typet{threads_bits})},
            and_exprt{
              create_exec_tot_symbol(/*log,*/ equation, write.label, write.num, thread),
              and_exprt{
                equal_exprt{create_dr_atom_symbol(4), from_integer({atom}, bool_typet{})},
                equal_exprt{create_dr_loc_symbol(4), typecast_exprt(write.where, size_type())}
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
              equal_exprt{create_dr_round_symbol(4),from_integer({round}, unsignedbv_typet{rounds_bits})},
              enabled_exp
            }};
          exp2 = and_exprt{exp2, exp};
        }
        phase_2_t_v_exp = equal_exprt{
          phase_2_t_v_symbl,
          and_exprt{phase_2_t_v_exp, exp2}};

        simplify(phase_2_t_v_exp, ns);
        equation.constraint(
          phase_2_t_v_exp, "datarace constraint", equation.SSA_steps.begin()->source);
      }
    }
    // A thread with no candidate access contributes false: leave it out,
    // rather than define its symbol as false (see handling_datarace).
    if(phase_2_t_ops.empty())
      continue;
    phase_2_ops.push_back(phase_2_t_symbl);
    phase_2_t_exp = equal_exprt {phase_2_t_symbl, disjunction(phase_2_t_ops)};
    simplify(phase_2_t_exp, ns);
    equation.constraint(
      phase_2_t_exp, "datarace constraint", equation.SSA_steps.begin()->source);
  }

  if(phase_2_ops.empty())
    return false_exprt{};
  phase_2_exp = equal_exprt {phase_2_symbl, disjunction(phase_2_ops)};
  simplify(phase_2_exp, ns);
  equation.constraint(
    phase_2_exp, "datarace constraint", equation.SSA_steps.begin()->source);

  return phase_2_symbl;
}

// Mirror of same_round for roles 3/4 -- identical relational structure
// (it encodes the fixed round-robin sweep order within a round, which
// doesn't depend on what kind of access each role represents), just
// parameterized on the independent role-3/4 symbols.
symbol_exprt lazy_pot::same_round_swap(symex_target_equationt &equation) {
  irep_idt same_round_name = "same_round_swap";
  symbol_exprt same_round_symbl{same_round_name, bool_typet{}};


  exprt same_round_exp = and_exprt{
    notequal_exprt{
      create_dr_thread_symbol(3),
      create_dr_thread_symbol(4)
    },
    and_exprt{
      implies_exprt{
        less_than_exprt{create_dr_thread_symbol(3),
      create_dr_thread_symbol(4)},
        equal_exprt{create_dr_round_symbol(3),
      create_dr_round_symbol(4)}
      },
      and_exprt{
        implies_exprt{
          less_than_exprt{create_dr_thread_symbol(4),
          create_dr_thread_symbol(3)},
            equal_exprt{create_dr_round_symbol(4),
          plus_exprt{create_dr_round_symbol(3), from_integer({1}, unsignedbv_typet{rounds_bits})}}},
        and_exprt{
          or_exprt{not_exprt{create_dr_atom_symbol(3)}, not_exprt{create_dr_atom_symbol(4)}},
          equal_exprt{create_dr_loc_symbol(3),create_dr_loc_symbol(4)}
          }
        }
    }
  };

  same_round_exp = equal_exprt{same_round_symbl, same_round_exp};
  simplify(same_round_exp, ns);
  equation.constraint(
    same_round_exp, "datarace constraint", equation.SSA_steps.begin()->source);

  return same_round_symbl;
}

// Mirror of no_interf for roles 3/4.
symbol_exprt lazy_pot::no_interf_swap(symex_target_equationt &equation) {
  irep_idt no_interf_name = "no_interf_swap";
  symbol_exprt no_interf_symbl{no_interf_name, bool_typet{}};

  exprt no_interf_exp = true_exprt{};


  for (std::size_t thread = 0; thread <= threads; thread++) {
    irep_idt no_interf_t_name = "no_interf_swap_T" + std::to_string(thread);
    symbol_exprt no_interf_t_symbl{no_interf_t_name, bool_typet{}};

    exprt exp1 = true_exprt{};
    exprt exp2 = true_exprt{};
    for (std::size_t round = 1; round <= rounds; round++) {
      exprt exp1r = true_exprt{};
      exprt exp2r = true_exprt{};
        exprt cs_eq_1 = true_exprt{};
        for(unsigned i = 1; i <= labels[thread] + 1; ++i)
          cs_eq_1 = and_exprt{
            cs_eq_1,
            implies_exprt{
              create_ge_symbol(thread, round, i),
              create_ge_symbol(thread, round - 1, i)}};
        exp1r = implies_exprt{
          equal_exprt{create_dr_round_symbol(3), from_integer({round}, unsignedbv_typet{rounds_bits})},
          cs_eq_1
        };
      if (round > 1) {
        exprt cs_eq_2 = true_exprt{};
        for(unsigned i = 1; i <= labels[thread] + 1; ++i)
          cs_eq_2 = and_exprt{
            cs_eq_2,
            implies_exprt{
              create_ge_symbol(thread, round, i),
              create_ge_symbol(thread, round - 1, i)}};
        exp2r = implies_exprt{
          equal_exprt{create_dr_round_symbol(4), from_integer({round}, unsignedbv_typet{rounds_bits})},
          cs_eq_2
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
              less_than_exprt{create_dr_thread_symbol(3), from_integer({thread}, unsignedbv_typet{threads_bits})},
              less_than_exprt{from_integer({thread}, unsignedbv_typet{threads_bits}), create_dr_thread_symbol(4)}},
            and_exprt{
              less_than_exprt{create_dr_thread_symbol(4),create_dr_thread_symbol(3)},
              less_than_exprt{create_dr_thread_symbol(3), from_integer({thread}, unsignedbv_typet{threads_bits})}}
          },
          exp1
        },
        implies_exprt{
          and_exprt{
          less_than_exprt{from_integer({thread}, unsignedbv_typet{threads_bits}), create_dr_thread_symbol(4)},
            less_than_exprt{create_dr_thread_symbol(4), create_dr_thread_symbol(3)}},
          exp2}
      }
    };

    no_interf_t_exp = equal_exprt{no_interf_t_symbl, no_interf_t_exp};
    simplify(no_interf_t_exp, ns);
    equation.constraint(
      no_interf_t_exp, "datarace constraint", equation.SSA_steps.begin()->source);

    no_interf_exp = and_exprt{no_interf_exp, no_interf_t_symbl};
  }
  no_interf_exp = equal_exprt{no_interf_symbl, no_interf_exp};
  simplify(no_interf_exp, ns);
  equation.constraint(
    no_interf_exp, "datarace constraint", equation.SSA_steps.begin()->source);

  return no_interf_symbl;
}

void lazy_pot::handling_datarace(
  symex_target_equationt &equation) {


  irep_idt phases_name = "phases";
  symbol_exprt phases_symbl{phases_name, bool_typet{}};
  exprt phases_exp = false_exprt{};
  exprt::operandst phases_ops;
  // __SZH_DR_ADD_BEGIN__
  irep_idt phases_swap_name = "phases_swap";
  symbol_exprt phases_swap_symbl{phases_swap_name, bool_typet{}};
  exprt phases_swap_exp = false_exprt{};
  exprt::operandst phases_swap_ops;
  // __SZH_DR_ADD_END__
  if(getenv("IEKKE_DUMP_GLOBALS") != nullptr)
  {
    std::cout << "=== shared objects seen by the race encoding ===\n";
    for(auto v : global_variables)
    {
      std::set<unsigned> rt, wt;
      if(reads.count(v))
        for(const auto &e : reads.at(v))
          rt.insert(e.thread);
      if(writes.count(v))
        for(const auto &e : writes.at(v))
          wt.insert(e.thread);
      std::cout << "  " << v << "  reads=" << (reads.count(v) ? reads.at(v).size() : 0)
                << " from " << rt.size() << " thread(s)"
                << "  writes=" << (writes.count(v) ? writes.at(v).size() : 0)
                << " from " << wt.size() << " thread(s)";
      if(getenv("IEKKE_DUMP_ACCESSES") != nullptr)
      {
        std::cout << "\n";
        if(writes.count(v))
          for(const auto &e : writes.at(v))
            std::cout << "      W t=" << e.thread << " label=" << e.label
                      << " num=" << e.num
                      << " atomic=" << (e.s_it->atomic_section_id != 0)
                      << " ultimo_del_blocco="
                      << (e.label < labels[e.thread] ? "forse" : "si")
                      << " fn=" << id2string(
                           e.s_it->source.pc->source_location().get_function())
                      << "\n";
        if(reads.count(v))
          for(const auto &e : reads.at(v))
            std::cout << "      R t=" << e.thread << " label=" << e.label
                      << " num=" << e.num
                      << " atomic=" << (e.s_it->atomic_section_id != 0)
                      << " primo_del_blocco="
                      << (e.label > 1 ? "forse" : "si")
                      << " fn=" << id2string(
                           e.s_it->source.pc->source_location().get_function())
                      << "\n";
        std::cout << "   ";
      }
      if(v.starts_with("__CPROVER"))
        std::cout << "   [skipped: __CPROVER]";
      else if(equation.symbol_is_atomic(ns, v))
        std::cout << "   [skipped: atomic]";
      std::cout << "\n";
    }
    std::cout << "=== end shared objects ===\n";
  }
  for (auto v : global_variables) {
    if (v.starts_with("__CPROVER"))
      continue;
    if (equation.symbol_is_atomic(ns,v))
      continue;
    // A pairing needs both its accesses: where one side has no candidate
    // the pairing is false, and the other side is not encoded at all. On
    // the ldv-linux irda driver nsc-ircc each of the 23000 shared objects
    // was encoded for every thread and both pairings, mostly as symbols
    // defined false: the data-race phase took resident memory from 5 to
    // 12 GB.
    const exprt pha_1 = phase_1(/*log,*/ equation, v);
    if(!pha_1.is_false())
    {
      const exprt pha_2 = phase_2(/*log,*/ equation, v);
      if(!pha_2.is_false())
        phases_ops.push_back(and_exprt{pha_1, pha_2});
    }
    // __SZH_DR_ADD_BEGIN__
    // Read-first/write-second pairing (see phase_1_swap): a race that
    // phase_1/phase_2 (write-first only) cannot witness.
    const exprt pha_1_swap = phase_1_swap(equation, v);
    if(!pha_1_swap.is_false())
    {
      const exprt pha_2_swap = phase_2_swap(equation, v);
      if(!pha_2_swap.is_false())
        phases_swap_ops.push_back(and_exprt{pha_1_swap, pha_2_swap});
    }
    // __SZH_DR_ADD_END__
  }
  // One disjunction over all shared objects. Was: or_exprt{previous, next}
  // per object, a chain as deep as the number of objects, and simplifying
  // it recursed once per level: on the ldv-linux irda driver nsc-ircc the
  // stack overflowed (47000 frames) and the run died on SIGSEGV.
  phases_exp = disjunction(phases_ops);
  phases_swap_exp = disjunction(phases_swap_ops);
  phases_exp = equal_exprt{phases_symbl, phases_exp};
  simplify(phases_exp, ns);
  equation.constraint(
    phases_exp, "datarace constraint", equation.SSA_steps.begin()->source);

  // __SZH_DR_ADD_BEGIN__
  phases_swap_exp = equal_exprt{phases_swap_symbl, phases_swap_exp};
  simplify(phases_swap_exp, ns);
  equation.constraint(
    phases_swap_exp, "datarace constraint", equation.SSA_steps.begin()->source);
  // __SZH_DR_ADD_END__

  symbol_exprt same_round_symbl = same_round(/*log,*/ equation);

  symbol_exprt no_interf_symbl = no_interf(/*log,*/ equation);

  // __SZH_DR_ADD_BEGIN__
  symbol_exprt same_round_swap_symbl = same_round_swap(equation);

  symbol_exprt no_interf_swap_symbl = no_interf_swap(equation);
  // __SZH_DR_ADD_END__

  exprt datarace_contraint = and_exprt{phases_symbl, and_exprt{same_round_symbl, no_interf_symbl}};
  // __SZH_DR_ADD_BEGIN__
  // Purely additive: OR in the read-first/write-second pairing. Cannot
  // regress the original (roles 1/2) detection -- it is untouched above
  // -- only widen it with a witness the original pairing structurally
  // cannot express.
  exprt datarace_contraint_swap = and_exprt{phases_swap_symbl, and_exprt{same_round_swap_symbl, no_interf_swap_symbl}};
  datarace_contraint = or_exprt{datarace_contraint, datarace_contraint_swap};
  // __SZH_DR_ADD_END__
  simplify(datarace_contraint, ns);
  //equation.constraint(
   // datarace_contraint, "datarace constraint", equation.SSA_steps.begin()->source);
  equation.assertion(true_exprt{},not_exprt{datarace_contraint},"datarace",equation.SSA_steps.begin()->source);
}
