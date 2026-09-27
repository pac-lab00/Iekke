/*******************************************************************\

Module: Thread-aware SSA slicing

Author: Gennaro Parlato, gennaro.parlato@unimol.it

\*******************************************************************/

/// \file
/// Implementation of \ref thread_aware_slice. The soundness argument, and the
/// measurement that bounds what this is worth, are in the header.

#include "thread_aware_slice.h"

#include <util/std_expr.h>

#include <goto-symex/symex_target_equation.h>

#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace
{

/// Every SSA symbol read by an expression.
void collect_symbols(const exprt &expr, std::unordered_set<irep_idt> &into)
{
  if(expr.id() == ID_symbol)
    into.insert(to_symbol_expr(expr).get_identifier());

  for(const auto &op : expr.operands())
    collect_symbols(op, into);
}

/// Everything \p step reads: its guard, its condition, its right-hand side,
/// and the index and offset expressions inside its left-hand side.
void collect_reads(const SSA_stept &step, std::unordered_set<irep_idt> &into)
{
  collect_symbols(step.guard, into);

  if(step.cond_expr.is_not_nil())
    collect_symbols(step.cond_expr, into);

  if(step.ssa_rhs.is_not_nil())
    collect_symbols(step.ssa_rhs, into);

  // The left-hand side of a shared access is not just a name: for an array or
  // a dereference it carries the expressions that decide which object is
  // touched, and the encoding pairs accesses by object.
  if(step.ssa_lhs.is_not_nil())
    collect_symbols(step.ssa_lhs, into);
}

} // namespace

std::size_t thread_aware_slice(symex_target_equationt &equation)
{
  std::vector<SSA_stept *> steps;
  steps.reserve(equation.SSA_steps.size());
  for(auto &step : equation.SSA_steps)
    steps.push_back(&step);

  // Which step defines which symbol. SSA names are unique, so the first
  // definition is the only one; guard against a malformed equation by not
  // overwriting.
  std::unordered_map<irep_idt, std::size_t> definition;
  for(std::size_t i = 0; i < steps.size(); ++i)
  {
    if(!steps[i]->is_assignment())
      continue;
    if(steps[i]->ssa_lhs.is_nil() || steps[i]->ssa_lhs.id() != ID_symbol)
      continue;
    definition.emplace(steps[i]->ssa_lhs.get_identifier(), i);
  }

  // Seed with every step that is not a removable assignment. Steps an earlier
  // pass already marked ignored stay ignored and seed nothing.
  std::vector<bool> keep(steps.size(), false);
  std::vector<std::size_t> worklist;
  for(std::size_t i = 0; i < steps.size(); ++i)
  {
    if(steps[i]->ignore)
    {
      keep[i] = true; // already gone; do not count it again below
      continue;
    }
    if(!steps[i]->is_assignment())
    {
      keep[i] = true;
      worklist.push_back(i);
    }
  }

  // Backward closure: whatever a kept step reads is kept.
  std::unordered_set<irep_idt> read;
  while(!worklist.empty())
  {
    const std::size_t i = worklist.back();
    worklist.pop_back();

    read.clear();
    collect_reads(*steps[i], read);

    for(const auto &symbol : read)
    {
      const auto entry = definition.find(symbol);
      if(entry == definition.end())
        continue; // an input, or defined by a step we never remove

      if(!keep[entry->second])
      {
        keep[entry->second] = true;
        worklist.push_back(entry->second);
      }
    }
  }

  std::size_t removed = 0;
  for(std::size_t i = 0; i < steps.size(); ++i)
  {
    if(!keep[i])
    {
      steps[i]->ignore = true;
      ++removed;
    }
  }

  return removed;
}
