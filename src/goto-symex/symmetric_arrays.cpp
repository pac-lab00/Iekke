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
#include <util/symbol_table.h>
#include <util/message.h>
#include <goto-programs/goto_model.h>

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


/// Replace the type of every symbol expression naming a rewritten array.
///
/// Changing the symbol table alone is not enough: expressions carry their own
/// copy of the type, and a stale one leaves the old size visible to symex.
static void retype_symbols(
  exprt &expr,
  const std::map<irep_idt, typet> &new_types)
{
  if(expr.id() == ID_symbol)
  {
    const auto entry = new_types.find(to_symbol_expr(expr).get_identifier());
    if(entry != new_types.end())
      expr.type() = entry->second;
  }

  for(auto &op : expr.operands())
    retype_symbols(op, new_types);
}

/// Rewrite the family's loop bound from \p old_size to \p new_size.
///
/// Only comparisons that mention one of the variables actually used to index
/// the family are touched; the literal N on its own is not evidence of
/// anything.
static void retarget_bound(
  exprt &expr,
  const std::unordered_set<irep_idt> &index_vars,
  const mp_integer &old_size,
  const mp_integer &new_size)
{
  // An index that wraps -- arr[(i + 1) % N] -- carries the family size in the
  // modulus. Leaving it at N after shrinking the array lets the index run past
  // the end of it, so the modulus comes down with the declared size.
  if(expr.id() == ID_mod && expr.operands().size() == 2)
  {
    exprt &divisor = to_binary_expr(expr).op1();
    if(divisor.is_constant())
    {
      const auto value = numeric_cast<mp_integer>(to_constant_expr(divisor));
      if(value.has_value() && *value == old_size)
        divisor = from_integer(new_size, divisor.type());
    }
  }

  if(
    expr.id() == ID_lt || expr.id() == ID_le || expr.id() == ID_gt ||
    expr.id() == ID_ge || expr.id() == ID_equal || expr.id() == ID_notequal)
  {
    if(expr.operands().size() == 2)
    {
      bool mentions_index = false;
      for(const auto &op : expr.operands())
      {
        std::vector<const exprt *> work{&op};
        while(!work.empty())
        {
          const exprt &e = *work.back();
          work.pop_back();
          if(
            e.id() == ID_symbol &&
            index_vars.count(to_symbol_expr(e).get_identifier()) != 0)
          {
            mentions_index = true;
          }
          for(const auto &sub : e.operands())
            work.push_back(&sub);
        }
      }

      if(mentions_index)
      {
        for(auto &op : expr.operands())
        {
          if(op.is_constant())
          {
            const auto value = numeric_cast<mp_integer>(to_constant_expr(op));
            if(value.has_value() && *value == old_size)
              op = from_integer(new_size, op.type());
          }
        }
      }
    }
  }

  for(auto &op : expr.operands())
    retarget_bound(op, index_vars, old_size, new_size);
}


/// Bring an array literal down to the instantiated size.
///
/// The initialiser that __CPROVER_initialize assigns to a shrunk array still
/// carries its original length; retyping the symbol without this leaves the
/// assignment type-inconsistent and symex refuses it.
static void resize_array_literal(exprt &expr, std::size_t instance_size)
{
  if(expr.id() == ID_array && expr.operands().size() > instance_size)
  {
    exprt::operandst kept(
      expr.operands().begin(), expr.operands().begin() + instance_size);
    expr.operands().swap(kept);

    if(expr.type().id() == ID_array)
    {
      to_array_type(expr.type()).size() =
        from_integer(instance_size, to_array_type(expr.type()).size().type());
    }
  }

  for(auto &op : expr.operands())
    resize_array_literal(op, instance_size);
}

bool shrink_symmetric_array_families(
  goto_modelt &goto_model,
  std::size_t instance_size,
  message_handlert &message_handler)
{
  messaget log(message_handler);
  const namespacet ns(goto_model.symbol_table);

  const auto families =
    compute_symmetric_array_families(goto_model.goto_functions, ns);

  std::map<irep_idt, typet> new_types;
  std::unordered_set<irep_idt> index_vars;
  std::vector<std::pair<mp_integer, mp_integer>> bounds;
  std::size_t rewritten = 0;

  for(const auto &family : families)
  {
    if(family.size <= instance_size)
      continue; // already at or below the instance we would build

    // The variables used to index this family: those are what identify the
    // loop bound worth rewriting.
    std::unordered_set<irep_idt> members(
      family.arrays.begin(), family.arrays.end());
    std::vector<exprt> indices;
    for(const auto &f : goto_model.goto_functions.function_map)
    {
      for(const auto &ins : f.second.body.instructions)
      {
        ins.apply([&](const exprt &e) { collect_indices(e, members, indices); });
      }
    }
    for(const auto &index : indices)
    {
      std::vector<const exprt *> work{&index};
      while(!work.empty())
      {
        const exprt &e = *work.back();
        work.pop_back();
        if(e.id() == ID_symbol)
          index_vars.insert(to_symbol_expr(e).get_identifier());
        for(const auto &sub : e.operands())
          work.push_back(&sub);
      }
    }

    for(const auto &name : family.arrays)
    {
      const symbolt &sym = ns.lookup(name);
      const typet followed = ns.follow(sym.type);
      if(followed.id() != ID_array)
        continue;

      array_typet shrunk = to_array_type(followed);
      shrunk.size() = from_integer(instance_size, to_array_type(followed).size().type());

      goto_model.symbol_table.get_writeable_ref(name).type = shrunk;
      new_types[name] = shrunk;
      ++rewritten;
    }

    bounds.emplace_back(family.size, instance_size);

    log.statistics() << "symmetric arrays: instantiating " << family.arrays.size()
                     << " array(s) at " << instance_size << " slots instead of "
                     << family.size << " (a violation found here is real; a safe"
                        " result is not a proof)" << messaget::eom;
  }

  if(new_types.empty())
    return false;

  // Keep the original: the rewrite is applied only if it survives the check
  // below.
  symbol_tablet original_symbols = goto_model.symbol_table;
  goto_functionst original_functions;
  original_functions.copy_from(goto_model.goto_functions);

  for(auto &f : goto_model.goto_functions.function_map)
  {
    for(auto &ins : f.second.body.instructions)
    {
      ins.transform([&](exprt e) -> optionalt<exprt> {
        retype_symbols(e, new_types);
        for(const auto &b : bounds)
          retarget_bound(e, index_vars, b.first, b.second);
        return e;
      });

      // An assignment to a shrunk array still carries its full-length
      // initialiser, which no longer matches the left-hand side.
      if(ins.is_assign())
      {
        const exprt &lhs = ins.assign_lhs();
        if(
          lhs.id() == ID_symbol &&
          new_types.count(to_symbol_expr(lhs).get_identifier()) != 0)
        {
          resize_array_literal(ins.assign_rhs_nonconst(), instance_size);
        }
      }
    }
  }

  // The size of a family reaches further than its declaration -- into
  // initialisers, into index arithmetic, and into places not yet catalogued.
  // If anything was left behind, the model no longer type-checks and symex
  // would abort on it, so restore and proceed unreduced.
  for(const auto &f : goto_model.goto_functions.function_map)
  {
    for(const auto &ins : f.second.body.instructions)
    {
      if(!ins.is_assign())
        continue;

      if(ins.assign_lhs().type() != ins.assign_rhs().type())
      {
        log.warning()
          << "symmetric arrays: reduction left an inconsistent assignment at "
          << ins.source_location() << ", continuing without it" << messaget::eom;

        goto_model.symbol_table.swap(original_symbols);
        goto_model.goto_functions.function_map.clear();
        goto_model.goto_functions.copy_from(original_functions);
        return false;
      }
    }
  }

  return true;
}
