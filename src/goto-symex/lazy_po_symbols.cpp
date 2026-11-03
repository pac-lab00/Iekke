/// \file
/// lazy_po: creation of the encoding symbols (exec, enabled, cs, ge, reach, data-race, tag totals)

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

symbol_exprt lazy_pot::create_lazy_symbol(
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
lazy_pot::create_exec_symbol(unsigned label, unsigned num, unsigned thread, size_t round)
{
  const uint64_t key = chain_key(round, thread, label, num);
  auto it = exec_map.find(key);
  if(it != exec_map.end())
    return it->second;

  irep_idt exec_name = "Ex_T" + std::to_string(thread) + "_L" +
                       std::to_string(label) + "_N" + std::to_string(num) +
                       "_R" + std::to_string(round);
  symbol_exprt exec_symbol{exec_name, bool_typet{}};

  exec exec_struct{label, num, thread, round, exec_symbol};
  exec_vector.emplace_back(exec_struct);
  exec_map.emplace(key, exec_symbol);

  return exec_symbol;
}

symbol_exprt
lazy_pot::create_exec_symbol_fast(unsigned label, unsigned num, unsigned thread, size_t round)
{

  return create_exec_symbol(label, num, thread, round);
}

symbol_exprt
lazy_pot::create_exec_tot_symbol(symex_target_equationt &equation, unsigned label, unsigned num, unsigned thread)
{
  const uint64_t tot_key = chain_key(0, thread, label, num);
  {
    auto it = exec_tot_map.find(tot_key);
    if(it != exec_tot_map.end())
      return it->second;
  }

  exprt constraint = false_exprt{};
  irep_idt exec_name = "Ex_T" + std::to_string(thread) + "_L" +
                       std::to_string(label) + "_N" + std::to_string(num);
  symbol_exprt exec_symbol{exec_name, bool_typet{}};

  exec_tot exec_struct{label, num, thread, exec_symbol};
  exec_tot_vector.emplace_back(exec_struct);
  exec_tot_map.emplace(tot_key, exec_symbol);

  for (std::size_t round = 1; round <= rounds; round++) {
    constraint = or_exprt{constraint, create_exec_symbol(label,num,thread,round)};
  }
  constraint = equal_exprt{exec_symbol, constraint};
  simplify(constraint, ns);
  equation.constraint(
    constraint, "exec tot constraint", equation.SSA_steps.begin()->source);

  return exec_symbol;
}

symbol_exprt lazy_pot::create_enabled_symbol(
  unsigned label,
  unsigned thread,
  size_t round)
{
  const uint64_t en_key = chain_key(round, thread, label, 0);
  {
    auto it = enabled_map.find(en_key);
    if(it != enabled_map.end())
      return it->second;
  }
  irep_idt enabled_name = "En_T" + std::to_string(thread) + "_L" +
                          std::to_string(label) + "_R" + std::to_string(round);
  symbol_exprt enabled_symbol{enabled_name, bool_typet{}};

  enabled enabled_struct{label, thread, round, enabled_symbol};
  enabled_vector.emplace_back(enabled_struct);
  enabled_map.emplace(en_key, enabled_symbol);

  return enabled_symbol;
}

symbol_exprt lazy_pot::create_cs_symbol(size_t thread, size_t round)
{
  const uint64_t cs_key = chain_key(round, static_cast<unsigned>(thread), 0, 0);
  {
    auto it = cs_map.find(cs_key);
    if(it != cs_map.end())
      return it->second;
  }
  irep_idt cs_name =
    "cs_T" + std::to_string(thread) + "_R" + std::to_string(round);
  symbol_exprt cs_symbol{cs_name, unsignedbv_typet{n_bit[thread]}};

  cs cs_struct{thread, round, cs_symbol};
  cs_vector.emplace_back(cs_struct);
  cs_map.emplace(cs_key, cs_symbol);

  return cs_symbol;
}

symbol_exprt lazy_pot::create_ge_symbol(size_t thread, size_t round, unsigned i)
{
  // GE(thread,round,i) <=> cs(thread,round) >= i, for i in 1..labels[thread]+1.
  // Order/thermometer encoding of the context-switch counter: replaces
  // the raw n_bit-wide bitvector cs used to; a threshold comparison that
  // used to need an O(n_bit)-variable comparator circuit per (label,
  // round) pair is now a single literal read, and monotonicity in round
  // and in threshold (asserted once in create_cs_constraint) gives the
  // solver a direct implication chain instead of bitvector arithmetic to
  // propagate through. See create_cs_constraint for the (C1)-(C3)
  // defining constraints.
  const uint64_t ge_key = chain_key(round, static_cast<unsigned>(thread), i, 1);
  {
    auto it = ge_map.find(ge_key);
    if(it != ge_map.end())
      return it->second;
  }
  irep_idt ge_name = "csge_T" + std::to_string(thread) + "_R" +
                      std::to_string(round) + "_I" + std::to_string(i);
  symbol_exprt ge_symbol{ge_name, bool_typet{}};

  ge ge_struct{thread, round, i, ge_symbol};
  ge_vector.emplace_back(ge_struct);
  ge_map.emplace(ge_key, ge_symbol);

  return ge_symbol;
}

symbol_exprt lazy_pot::create_reach_symbol(unsigned label, size_t thread)
{
  const uint64_t re_key = chain_key(0, static_cast<unsigned>(thread), label, 0);
  {
    auto it = reach_map.find(re_key);
    if(it != reach_map.end())
      return it->second;
  }
  irep_idt reach_name =
    "reach_T" + std::to_string(thread) + "_L" + std::to_string(label);
  symbol_exprt reach_symbol{reach_name, bool_typet{}};

  reach reach_struct{label, thread, reach_symbol};
  reach_vector.emplace_back(reach_struct);
  reach_map.emplace(re_key, reach_symbol);

  return reach_symbol;
}

symbol_exprt lazy_pot::create_active_thread_symbol(unsigned thread)
{
  irep_idt active_thread_name = "__CPROVER_active_thread_T" + std::to_string(thread);
  symbol_exprt active_thread_expr{active_thread_name, bool_typet{}};

  active_thread active_thread_struct{thread, 1, active_thread_expr};
  active_threads_vector.emplace(thread, active_thread_struct);

  return active_thread_expr;
}

symbol_exprt lazy_pot::create_dr_thread_symbol(unsigned num)
{
  if (dr_thread.find(num) != dr_thread.end())
    return dr_thread.at(num);
  irep_idt thread_name = "t" + std::to_string(num);
  symbol_exprt thread_expr{thread_name, unsignedbv_typet{threads_bits}};

  dr_thread.emplace(num, thread_expr);
  return thread_expr;
}

symbol_exprt lazy_pot::create_dr_round_symbol(unsigned num)
{
  if (dr_round.find(num) != dr_round.end())
    return dr_round.at(num);
  irep_idt round_name = "r" + std::to_string(num);
  symbol_exprt round_expr{round_name, unsignedbv_typet{rounds_bits}};

  dr_round.emplace(num, round_expr);

  return round_expr;
}

symbol_exprt lazy_pot::create_dr_atom_symbol(unsigned num)
{
  if (dr_atom.find(num) != dr_atom.end())
    return dr_atom.at(num);
  irep_idt atom_name = "a" + std::to_string(num);
  symbol_exprt atom_expr{atom_name, bool_typet{}};

  dr_atom.emplace(num, atom_expr);

  return atom_expr;
}

symbol_exprt lazy_pot::create_dr_loc_symbol(unsigned num)
{
  if (dr_loc.find(num) != dr_loc.end())
    return dr_loc.at(num);

  irep_idt loc_name = "loc" + std::to_string(num);
  symbol_exprt loc_expr{loc_name, size_type()};

  dr_loc.emplace(num, loc_expr);

  return loc_expr;
}
void lazy_pot::create_winr_tot_symbol(
  symex_target_equationt &equation)
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
        create_WINR_symbol(global_variable, write.thread, write.label, write.num, round,equation);
      }
    }
  }
}

void lazy_pot::create_lw_tot_symbol(
  symex_target_equationt &equation) {
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
        create_LW_symbol(global_variable,read.thread, read.label,read.num, round, equation);
      }
    }
  }
}

void lazy_pot::create_nrp_tot_symbol(
  symex_target_equationt &equation)
{
  for(auto global_variable : global_variables)
  {
    if(this->reads.count(global_variable) == 0)
      continue;

    auto sorted_reads = this->reads.at(global_variable);
    std::sort(sorted_reads.begin(), sorted_reads.end(),
      [](const shared_event &a, const shared_event &b) {
        return std::tie(a.thread, a.label, a.num) > std::tie(b.thread, b.label, b.num);
      });
    for(std::size_t round = rounds + 1; round-- > 0; )
    {
      for(const auto &read : sorted_reads)
      {
        create_NRP_symbol(global_variable, read.thread, read.label, read.num, round, equation);
      }
    }
  }
}

void lazy_pot::create_low_tot_symbol(
  symex_target_equationt &equation)
{
  for(auto global_variable : global_variables)
  {
    if(this->writes.count(global_variable) == 0)
      continue;
    auto sorted_writes = this->writes.at(global_variable);
    std::sort(sorted_writes.begin(), sorted_writes.end(),
      [](const shared_event &a, const shared_event &b) {
        return std::tie(a.thread, a.label, a.num) < std::tie(b.thread, b.label, b.num);
      });
    for(std::size_t round = 0; round <= rounds; ++round)
    {
      for(const auto &write : sorted_writes)
      {
        create_LOW_symbol(global_variable, write.thread, write.label, write.num, round, equation);
      }
    }
  }
}
