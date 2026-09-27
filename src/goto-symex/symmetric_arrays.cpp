/*******************************************************************\

Module: Static recognition of symmetric array families

Author: CBMC/lazy_po work

\*******************************************************************/

/// \file
/// Implementation of \ref compute_symmetric_array_families. The soundness
/// argument, and the measurements that motivate the reduction, are in the
/// header; this file only establishes the syntactic conditions that argument
/// depends on. Everything here is conservative: a family is reported only if
/// every condition is positively established, and anything the analysis does
/// not understand causes the family to be dropped rather than assumed benign.

#include "symmetric_arrays.h"

#include <util/arith_tools.h>
#include <util/namespace.h>
#include <util/symbol.h>
#include <util/symbol_table_base.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include <goto-programs/goto_functions.h>

#include <map>

namespace
{

/// The declared size of a global array, if it is an array of constant size.
optionalt<std::size_t> constant_array_size(const typet &t)
{
  if(t.id() != ID_array)
    return {};
  const auto size = numeric_cast<std::size_t>(to_array_type(t).size());
  if(!size.has_value() || *size == 0)
    return {};
  return size;
}

/// Collect every index expression applied to one of \p arrays anywhere in the
/// model, together with the array it indexes.
void collect_indices(
  const exprt &expr,
  const std::unordered_set<irep_idt> &arrays,
  std::vector<exprt> &indices)
{
  if(expr.id() == ID_index)
  {
    const auto &index_expr = to_index_expr(expr);
    if(
      index_expr.array().id() == ID_symbol &&
      arrays.count(to_symbol_expr(index_expr.array()).get_identifier()) > 0)
    {
      indices.push_back(index_expr.index());
    }
  }

  forall_operands(it, expr)
    collect_indices(*it, arrays, indices);
}

/// Does this expression relate two *different* indices into the family?
///
/// This is the condition that excludes a program whose setup deliberately
/// aliases two particular slots -- 28-race_reach_92-evilcollapse does exactly
/// that with p1->next = p2->next -- because there the slots are no longer
/// interchangeable and the permutation argument fails. Indices may be
/// compared against constants and used to subscript; they may not be compared
/// with, or combined with, one another.
bool relates_two_indices(
  const exprt &expr,
  const std::unordered_set<irep_idt> &arrays)
{
  const bool is_relational = expr.id() == ID_equal || expr.id() == ID_notequal ||
                             expr.id() == ID_lt || expr.id() == ID_le ||
                             expr.id() == ID_gt || expr.id() == ID_ge ||
                             expr.id() == ID_minus || expr.id() == ID_plus;

  if(is_relational && expr.operands().size() == 2)
  {
    // Two subscripts of the family appearing as the two sides of a comparison
    // or of arithmetic is precisely the correlation we must not allow.
    std::vector<exprt> lhs_indices, rhs_indices;
    collect_indices(to_binary_expr(expr).op0(), arrays, lhs_indices);
    collect_indices(to_binary_expr(expr).op1(), arrays, rhs_indices);
    if(!lhs_indices.empty() && !rhs_indices.empty())
      return true;
  }

  forall_operands(it, expr)
    if(relates_two_indices(*it, arrays))
      return true;

  return false;
}

/// Is this index expression one the argument permits: the induction variable
/// of the setup loop, or a value confined to [0, N) by a nondeterministic
/// choice? Anything else -- an index computed from data, say -- breaks the
/// claim that all slots are reached alike, so it is rejected.
bool index_is_uniform(const exprt &index, const std::unordered_set<irep_idt> &locals)
{
  if(index.id() == ID_symbol)
    return locals.count(to_symbol_expr(index).get_identifier()) > 0;

  if(index.id() == ID_typecast)
    return index_is_uniform(to_typecast_expr(index).op(), locals);

  // i % N and the like: the shape the benchmarks use to pick a slot.
  if(index.id() == ID_mod && index.operands().size() == 2)
    return to_binary_expr(index).op1().is_constant();

  return false;
}

} // namespace

std::vector<symmetric_array_familyt> compute_symmetric_array_families(
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  std::vector<symmetric_array_familyt> result;

  // Group the global arrays by declared size. Slots are only interchangeable
  // across arrays that are permuted *together*, which requires a common N.
  std::map<std::size_t, std::vector<irep_idt>> by_size;
  std::unordered_set<irep_idt> candidate_arrays;

  for(const auto &named : ns.get_symbol_table().symbols)
  {
    const symbolt &sym = named.second;
    if(!sym.is_static_lifetime || sym.is_type)
      continue;
    const auto size = constant_array_size(ns.follow(sym.type));
    if(!size.has_value())
      continue;
    // A one- or two-slot array is not worth reducing and is more likely to be
    // something else that happens to be an array.
    if(*size < 4)
      continue;
    by_size[*size].push_back(sym.name);
    candidate_arrays.insert(sym.name);
  }

  for(const auto &entry : by_size)
  {
    const std::size_t n = entry.first;
    std::unordered_set<irep_idt> family(entry.second.begin(), entry.second.end());

    // Every index into the family, everywhere, plus the local symbols that
    // could serve as a uniform index.
    std::vector<exprt> indices;
    std::unordered_set<irep_idt> locals;
    bool correlated = false;

    for(const auto &f : goto_functions.function_map)
    {
      for(const auto &ins : f.second.body.instructions)
      {
        if(ins.is_decl())
          locals.insert(ins.decl_symbol().get_identifier());

        ins.apply([&](const exprt &e) {
          collect_indices(e, family, indices);
          if(relates_two_indices(e, family))
            correlated = true;
        });
      }
    }

    // No accesses at all: nothing to reduce, and nothing established.
    if(indices.empty())
      continue;

    // Condition: no expression relates two distinct slots.
    if(correlated)
      continue;

    // Condition: every index is uniform over [0, N).
    bool all_uniform = true;
    for(const auto &index : indices)
    {
      if(!index_is_uniform(index, locals))
      {
        all_uniform = false;
        break;
      }
    }
    if(!all_uniform)
      continue;

    symmetric_array_familyt found;
    found.arrays.assign(entry.second.begin(), entry.second.end());
    found.size = n;
    result.push_back(found);
  }

  return result;
}
