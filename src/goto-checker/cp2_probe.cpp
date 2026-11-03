/*******************************************************************\

Module: CP2PROBE, where symbolic execution leaves values non-constant

\*******************************************************************/

/// \file
/// CP2PROBE: see cp2_probe.h

#include "cp2_probe.h"

#include <util/simplify_expr.h>
#include <util/ssa_expr.h>

#include <goto-symex/goto_symex_is_constant.h>
#include <goto-symex/symex_target_equation.h>

#include <algorithm>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace
{
struct cp2_object_writest
{
  std::set<unsigned> threads;
  std::set<exprt> values;
  bool nonconstant = false;
};

std::vector<std::string> cp2_prefixes(const std::string &s)
{
  // proper prefixes ending a component, before `..member` or `[[index]]`
  std::vector<std::string> result;
  for(std::size_t i = s.size(); i-- > 1;)
  {
    if((s[i - 1] == '.' && s[i] == '.') || (s[i - 1] == '[' && s[i] == '['))
      result.push_back(s.substr(0, i - 1));
  }
  return result;
}

exprt cp2_substitute(
  const exprt &expr,
  const std::unordered_map<irep_idt, exprt> &constants,
  bool &changed)
{
  if(is_ssa_expr(expr))
  {
    const auto it = constants.find(to_ssa_expr(expr).get_identifier());
    if(it != constants.end())
    {
      changed = true;
      return it->second;
    }
    return expr;
  }
  if(!expr.has_operands())
    return expr;
  exprt result = expr;
  bool any = false;
  for(auto &op : result.operands())
  {
    bool c = false;
    exprt n = cp2_substitute(op, constants, c);
    if(c)
    {
      op = std::move(n);
      any = true;
    }
  }
  if(any)
    changed = true;
  return any ? result : expr;
}
} // namespace

void cp2_constant_probe(
  const symex_target_equationt &equation,
  const namespacet &ns)
{
  // ---- Part 1: shared reads ----
  std::unordered_map<irep_idt, cp2_object_writest> post_exact, post_below;
  std::unordered_map<irep_idt, exprt> last_before; // nil if unknown
  bool spawned = false;
  for(const auto &step : equation.SSA_steps)
  {
    if(step.is_spawn())
      spawned = true;
    if(!spawned && step.is_assignment())
    {
      const irep_idt id = step.ssa_lhs.get_l1_object_identifier();
      const bool constant =
        step.guard.is_true() && goto_symex_is_constantt()(step.ssa_rhs);
      last_before[id] = constant ? step.ssa_rhs : static_cast<exprt>(nil_exprt{});
      for(const auto &p : cp2_prefixes(id2string(id)))
        last_before[p] = nil_exprt{};
    }
    if(!spawned || !step.is_shared_write())
      continue;
    const irep_idt id = step.ssa_lhs.get_l1_object_identifier();
    // the value written: the assignment defining the write's L2 symbol is
    // looked up below; here only the writer threads
    post_exact[id].threads.insert(step.source.thread_nr);
    for(const auto &p : cp2_prefixes(id2string(id)))
      post_below[p].threads.insert(step.source.thread_nr);
  }
  // values written after the spawn: the assignment defining each write's
  // L2 symbol
  {
    std::unordered_set<irep_idt> written_l2;
    spawned = false;
    for(const auto &step : equation.SSA_steps)
    {
      if(step.is_spawn())
        spawned = true;
      if(spawned && step.is_shared_write())
        written_l2.insert(step.ssa_lhs.get_identifier());
    }
    for(const auto &step : equation.SSA_steps)
    {
      if(!step.is_assignment())
        continue;
      if(written_l2.count(step.ssa_lhs.get_identifier()) == 0)
        continue;
      auto &w = post_exact[step.ssa_lhs.get_l1_object_identifier()];
      if(goto_symex_is_constantt()(step.ssa_rhs) && w.values.size() < 5)
        w.values.insert(step.ssa_rhs);
      else
        w.nonconstant = true;
    }
  }

  enum classt
  {
    FROZEN,
    SELF0,
    SELFN,
    SAMECONST,
    MULTI,
    N_CLASSES
  };
  const char *class_names[] = {"frozen", "self0", "selfN", "sameconst", "multi"};
  std::size_t reads[N_CLASSES] = {}, pointer_reads[N_CLASSES] = {};
  std::size_t frozen_with_value = 0;
  std::unordered_map<irep_idt, exprt> seeded; // read symbol -> its value
  std::map<irep_idt, std::pair<std::size_t, int>> per_object;

  for(const auto &step : equation.SSA_steps)
  {
    if(!step.is_shared_read())
      continue;
    const irep_idt id = step.ssa_lhs.get_l1_object_identifier();
    std::set<unsigned> threads;
    bool overlap_only_exact = true;
    const auto e = post_exact.find(id);
    if(e != post_exact.end())
      threads.insert(e->second.threads.begin(), e->second.threads.end());
    const auto b = post_below.find(id);
    if(b != post_below.end())
    {
      threads.insert(b->second.threads.begin(), b->second.threads.end());
      overlap_only_exact = false;
    }
    for(const auto &p : cp2_prefixes(id2string(id)))
    {
      const auto pe = post_exact.find(p);
      if(pe != post_exact.end() && !pe->second.threads.empty())
      {
        threads.insert(pe->second.threads.begin(), pe->second.threads.end());
        overlap_only_exact = false;
      }
    }
    const unsigned reader = step.source.thread_nr;
    const auto lb = last_before.find(id);
    const bool before_constant =
      lb != last_before.end() && lb->second.is_not_nil();
    classt c = MULTI;
    if(threads.empty())
    {
      c = FROZEN;
      if(before_constant)
      {
        ++frozen_with_value;
        seeded[step.ssa_lhs.get_identifier()] = lb->second;
      }
    }
    else if(threads.size() == 1 && *threads.begin() == reader)
      c = reader == 0 ? SELF0 : SELFN;
    else if(
      overlap_only_exact && e != post_exact.end() && !e->second.nonconstant &&
      before_constant)
    {
      std::set<exprt> values = e->second.values;
      values.insert(lb->second);
      if(values.size() == 1)
      {
        c = SAMECONST;
        seeded[step.ssa_lhs.get_identifier()] = lb->second;
      }
    }
    ++reads[c];
    if(step.ssa_lhs.type().id() == ID_pointer)
      ++pointer_reads[c];
    auto &entry = per_object[id];
    ++entry.first;
    entry.second = c;
  }

  std::size_t total = 0;
  for(std::size_t c = 0; c < N_CLASSES; ++c)
    total += reads[c];
  std::cout << "CP2PROBE shared_reads=" << total;
  for(std::size_t c = 0; c < N_CLASSES; ++c)
    std::cout << ' ' << class_names[c] << '=' << reads[c] << '/'
              << pointer_reads[c];
  std::cout << " frozen_with_constant=" << frozen_with_value
            << " (reads/pointer reads)\n";
  {
    std::vector<std::pair<std::size_t, irep_idt>> ranked;
    for(const auto &entry : per_object)
      ranked.emplace_back(entry.second.first, entry.first);
    std::sort(ranked.rbegin(), ranked.rend());
    for(std::size_t i = 0; i < ranked.size() && i < 12; ++i)
      std::cout << "CP2PROBE object " << ranked[i].second
                << " reads=" << ranked[i].first << " class="
                << class_names[per_object[ranked[i].second].second] << '\n';
  }

  // ---- Part 2: constants symex did not propagate ----
  const char *kind_names[] = {
    "state", "hidden", "vis_param", "hid_param", "phi", "guard"};
  for(int seeded_run = 0; seeded_run < 2; ++seeded_run)
  {
    std::unordered_map<irep_idt, exprt> constants;
    if(seeded_run)
      constants = seeded;
    std::size_t assignments[6] = {}, constant_rhs[6] = {}, folded[6] = {},
                folded_simplify_only[6] = {};
    std::size_t conditions = 0, conditions_folded = 0, guards_folded = 0;
    std::size_t shared_write_values = 0, shared_write_folded = 0;
    std::unordered_set<irep_idt> written_l2;
    for(const auto &step : equation.SSA_steps)
      if(step.is_shared_write())
        written_l2.insert(step.ssa_lhs.get_identifier());

    for(const auto &step : equation.SSA_steps)
    {
      if(step.is_assignment())
      {
        const int k = static_cast<int>(step.assignment_type);
        ++assignments[k];
        const bool is_write =
          written_l2.count(step.ssa_lhs.get_identifier()) != 0;
        if(is_write)
          ++shared_write_values;
        if(goto_symex_is_constantt()(step.ssa_rhs))
        {
          ++constant_rhs[k];
          if(!is_write)
            constants[step.ssa_lhs.get_identifier()] = step.ssa_rhs;
          continue;
        }
        bool changed = false;
        exprt rhs = cp2_substitute(step.ssa_rhs, constants, changed);
        exprt simplified = simplify_expr(rhs, ns);
        if(goto_symex_is_constantt()(simplified))
        {
          ++folded[k];
          if(!changed)
            ++folded_simplify_only[k];
          if(is_write)
            ++shared_write_folded;
          else
            constants[step.ssa_lhs.get_identifier()] = simplified;
        }
      }
      else if(
        step.is_assert() || step.is_assume() || step.is_goto() ||
        step.is_constraint())
      {
        if(step.cond_expr.is_constant())
          continue;
        ++conditions;
        bool changed = false;
        exprt cond = cp2_substitute(step.cond_expr, constants, changed);
        if(changed && simplify_expr(cond, ns).is_constant())
          ++conditions_folded;
      }
      if(!step.guard.is_constant())
      {
        bool changed = false;
        exprt g = cp2_substitute(step.guard, constants, changed);
        if(changed && simplify_expr(g, ns).is_constant())
          ++guards_folded;
      }
    }
    std::cout << "CP2PROBE " << (seeded_run ? "seeded" : "exact");
    for(int k = 0; k < 6; ++k)
      std::cout << ' ' << kind_names[k] << '=' << assignments[k] << ':'
                << constant_rhs[k] << ':' << folded[k] << ':'
                << folded_simplify_only[k];
    std::cout << " conds=" << conditions << ':' << conditions_folded
              << " guards_folded=" << guards_folded
              << " write_values=" << shared_write_values << ':'
              << shared_write_folded
              << " (assignments:constant:folded:by-simplify-alone)\n";
  }
}
