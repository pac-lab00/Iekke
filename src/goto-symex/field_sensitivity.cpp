/*******************************************************************\

Module: Field-sensitive SSA

Author: Michael Tautschnig

\*******************************************************************/

#include "field_sensitivity.h"

#include <util/arith_tools.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include "goto_symex_state.h"
#include "symex_target.h"

#define ENABLE_ARRAY_FIELD_SENSITIVITY

exprt field_sensitivityt::apply(
  const namespacet &ns,
  goto_symex_statet &state,
  ssa_exprt ssa_expr,
  bool write) const
{
  if(!run_apply || write)
    return std::move(ssa_expr);
  else
    return get_fields(ns, state, ssa_expr);
}

exprt field_sensitivityt::apply(
  const namespacet &ns,
  goto_symex_statet &state,
  exprt expr,
  bool write) const
{
  if(!run_apply)
    return expr;

  if(expr.id() != ID_address_of)
  {
    // Materialising the array operand of a store at a symbolic index is the
    // lowering framing the untouched elements back over themselves, not a
    // read the program performs. Produce the values, record no events: the
    // writes are already conditioned on `i == k` in field_assignments_rec,
    // and without this the same store is recorded as reading every element,
    // so two threads storing to different elements are paired on all of them.
    const bool framing_base = expr.id() == ID_with &&
                              expr.operands().size() == 3 &&
                              !to_with_expr(expr).where().is_constant();
#ifdef ENABLE_ARRAY_FIELD_SENSITIVITY
    // A load `a[i]` at an undecided i of an array still in symbol form --
    // among others the base of `with(a[i], member, v)`, the lowering of
    // `p->member = v` with `p = &a[i]`. Expanded by the plain walk below,
    // every element of `a` was renamed with the path guard, so the load was
    // recorded as reading all of them: a thread working on a[1] under a[1]'s
    // mutex was paired, on a[0], with a thread storing a[0] under a[0]'s
    // (goblint 06-symbeq_06..08). Expand it reading element k only under the
    // condition that the load meets it: the bytes [i * s, i * s + s), for
    // elements of size s, meet element k's exactly when i == k. (Were i * s
    // to overflow it would only add reads, never remove one.)
    // goto_symex_statet::rename does the same for an array that is already
    // expanded when it walks the expression.
    const bool index_load =
      !write && expr.id() == ID_index && is_ssa_expr(expr.op0()) &&
      is_divisible(to_ssa_expr(expr.op0())) &&
      expr.op0().type().id() == ID_array &&
      !simplify_expr(expr.op1(), ns).is_constant() &&
      (expr.op1().type().id() == ID_signedbv ||
       expr.op1().type().id() == ID_unsignedbv);
    const auto element_size =
      index_load
        ? pointer_offset_size(to_array_type(expr.op0().type()).element_type(), ns)
        : optionalt<mp_integer>{};
#else
    const bool index_load = false;
    const optionalt<mp_integer> element_size;
#endif
    bool is_base = true;
    Forall_operands(it, expr)
    {
      if(framing_base && is_base)
      {
        state.record_events.push(false);
        *it = apply(ns, state, std::move(*it), write);
        state.record_events.pop();
      }
      else if(
        index_load && is_base && element_size.has_value() && *element_size > 0)
      {
        *it = get_fields_in_range(
          ns,
          state,
          to_ssa_expr(*it),
          mult_exprt{
            expr.op1(), from_integer(*element_size, expr.op1().type())},
          *element_size,
          0);
      }
      else
        *it = apply(ns, state, std::move(*it), write);
      is_base = false;
    }
  }

  if(!write && is_ssa_expr(expr))
  {
    return apply(ns, state, to_ssa_expr(expr), write);
  }
  else if(
    !write && expr.id() == ID_member &&
    to_member_expr(expr).struct_op().id() == ID_struct)
  {
    return simplify_opt(std::move(expr), ns);
  }
#ifdef ENABLE_ARRAY_FIELD_SENSITIVITY
  else if(
    !write && expr.id() == ID_index &&
    to_index_expr(expr).array().id() == ID_array)
  {
    return simplify_opt(std::move(expr), ns);
  }
#endif // ENABLE_ARRAY_FIELD_SENSITIVITY
  else if(expr.id() == ID_member)
  {
    // turn a member-of-an-SSA-expression into a single SSA expression, thus
    // encoding the member as an individual symbol rather than only the full
    // struct
    member_exprt &member = to_member_expr(expr);

    if(
      is_ssa_expr(member.struct_op()) &&
      (member.struct_op().type().id() == ID_struct ||
       member.struct_op().type().id() == ID_struct_tag))
    {
      // place the entire member expression, not just the struct operand, in an
      // SSA expression
      ssa_exprt tmp = to_ssa_expr(member.struct_op());
      bool was_l2 = !tmp.get_level_2().empty();

      tmp.remove_level_2();
      member.struct_op() = tmp.get_original_expr();
      tmp.set_expression(member);
      if(was_l2)
        return state.rename(std::move(tmp), ns).get();
      else
        return std::move(tmp);
    }
  }
#ifdef ENABLE_ARRAY_FIELD_SENSITIVITY
  else if(expr.id() == ID_index)
  {
    // turn a index-of-an-SSA-expression into a single SSA expression, thus
    // encoding the index access into an array as an individual symbol rather
    // than only the full array
    index_exprt &index = to_index_expr(expr);
    if(should_simplify)
      simplify(index.index(), ns);

    if(
      is_ssa_expr(index.array()) && index.array().type().id() == ID_array &&
      index.index().id() == ID_constant)
    {
      // place the entire index expression, not just the array operand, in an
      // SSA expression
      ssa_exprt tmp = to_ssa_expr(index.array());
      auto l2_index = state.rename(index.index(), ns);
      if(should_simplify)
        l2_index.simplify(ns);
      bool was_l2 = !tmp.get_level_2().empty();
      exprt l2_size =
        state.rename(to_array_type(index.array().type()).size(), ns).get();
      if(l2_size.is_nil() && index.array().id() == ID_symbol)
      {
        // In case the array type was incomplete, attempt to retrieve it from
        // the symbol table.
        const symbolt *array_from_symbol_table = ns.get_symbol_table().lookup(
          to_symbol_expr(index.array()).get_identifier());
        if(array_from_symbol_table != nullptr)
          l2_size = to_array_type(array_from_symbol_table->type).size();
      }

      if(
        l2_size.id() == ID_constant &&
        numeric_cast_v<mp_integer>(to_constant_expr(l2_size)) <=
          max_field_sensitivity_array_size)
      {
        if(l2_index.get().id() == ID_constant)
        {
          // place the entire index expression, not just the array operand,
          // in an SSA expression
          ssa_exprt ssa_array = to_ssa_expr(index.array());
          ssa_array.remove_level_2();
          index.array() = ssa_array.get_original_expr();
          index.index() = l2_index.get();
          tmp.set_expression(index);
          if(was_l2)
            return state.rename(std::move(tmp), ns).get();
          else
            return std::move(tmp);
        }
        else if(!write)
        {
          // Expand the array and return `{array[0]; array[1]; ...}[index]`
          exprt expanded_array =
            get_fields(ns, state, to_ssa_expr(index.array()));
          return index_exprt{std::move(expanded_array), index.index()};
        }
      }
    }
  }
#endif // ENABLE_ARRAY_FIELD_SENSITIVITY
  return expr;
}

exprt field_sensitivityt::get_fields(
  const namespacet &ns,
  goto_symex_statet &state,
  const ssa_exprt &ssa_expr) const
{
  if(ssa_expr.type().id() == ID_struct || ssa_expr.type().id() == ID_struct_tag)
  {
    const struct_typet &type = to_struct_type(ns.follow(ssa_expr.type()));
    const struct_union_typet::componentst &components = type.components();

    struct_exprt::operandst fields;
    fields.reserve(components.size());

    const exprt &struct_op = ssa_expr.get_original_expr();

    for(const auto &comp : components)
    {
      ssa_exprt tmp = ssa_expr;
      bool was_l2 = !tmp.get_level_2().empty();
      tmp.remove_level_2();
      tmp.set_expression(member_exprt{struct_op, comp.get_name(), comp.type()});
      if(was_l2)
      {
        fields.push_back(state.rename(get_fields(ns, state, tmp), ns).get());
      }
      else
        fields.push_back(get_fields(ns, state, tmp));
    }

    return struct_exprt(std::move(fields), ssa_expr.type());
  }
#ifdef ENABLE_ARRAY_FIELD_SENSITIVITY
  else if(
    ssa_expr.type().id() == ID_array &&
    to_array_type(ssa_expr.type()).size().id() == ID_constant)
  {
    const mp_integer mp_array_size = numeric_cast_v<mp_integer>(
      to_constant_expr(to_array_type(ssa_expr.type()).size()));
    if(mp_array_size < 0 || mp_array_size > max_field_sensitivity_array_size)
      return ssa_expr;

    const array_typet &type = to_array_type(ssa_expr.type());
    const std::size_t array_size = numeric_cast_v<std::size_t>(mp_array_size);

    array_exprt::operandst elements;
    elements.reserve(array_size);

    const exprt &array = ssa_expr.get_original_expr();

    for(std::size_t i = 0; i < array_size; ++i)
    {
      const index_exprt index(array, from_integer(i, type.index_type()));
      ssa_exprt tmp = ssa_expr;
      bool was_l2 = !tmp.get_level_2().empty();
      tmp.remove_level_2();
      tmp.set_expression(index);
      if(was_l2)
      {
        elements.push_back(state.rename(get_fields(ns, state, tmp), ns).get());
      }
      else
        elements.push_back(get_fields(ns, state, tmp));
    }

    return array_exprt(std::move(elements), type);
  }
#endif // ENABLE_ARRAY_FIELD_SENSITIVITY
  else
    return ssa_expr;
}

void field_sensitivityt::field_assignments(
  const namespacet &ns,
  goto_symex_statet &state,
  const ssa_exprt &lhs,
  const exprt &rhs,
  symex_targett &target,
  bool allow_pointer_unsoundness)
{
  const exprt lhs_fs = apply(ns, state, lhs, false);

  if(lhs != lhs_fs)
  {
    bool run_apply_bak = run_apply;
    run_apply = false;
    // A store through a pointer at an undecided offset is lowered to
    // `o' == byte_update(o, offset, v)`, which the split below turns into one
    // assignment per field and element of o -- each of them, untouched ones
    // included, an unconditional shared write carrying the value this thread
    // read when the statement started. Any field another thread updated in
    // between is reset to that stale value: a lost update that exists only in
    // the lowering. In goblint 28-race_reach_74..76 a pthread_mutex_lock on
    // a[3].mutex republished a[4].datum and broke an assertion protected by
    // a[4]'s own mutex. As for a `with` at a non-constant index (below),
    // publish only the leaves whose bytes the store meets.
    const exprt saved_offset = store_offset;
    const mp_integer saved_size = store_size;
    const irep_idt saved_object = store_object;
    store_offset = nil_exprt{};
    store_object = lhs.get_l1_object_identifier();
    if(
      (rhs.id() == ID_byte_update_little_endian ||
       rhs.id() == ID_byte_update_big_endian) &&
      rhs.operands().size() == 3 &&
      (rhs.op1().type().id() == ID_signedbv ||
       rhs.op1().type().id() == ID_unsignedbv) &&
      !simplify_expr(rhs.op1(), ns).is_constant())
    {
      const auto size = pointer_offset_size(rhs.op2().type(), ns);
      if(size.has_value() && *size > 0)
      {
        store_offset = rhs.op1();
        store_size = *size;
      }
    }
    field_assignments_rec(
      ns, state, lhs_fs, rhs, target, allow_pointer_unsoundness);
    store_offset = saved_offset;
    store_size = saved_size;
    store_object = saved_object;
    run_apply = run_apply_bak;
  }
}

/// Assign to the individual fields \p lhs_fs of a non-expanded symbol \p lhs.
/// This is required whenever prior steps have updated the full object rather
/// than individual fields, e.g., in case of assignments to an array at an
/// unknown index.
/// \param ns: a namespace to resolve type symbols/tag types
/// \param state: symbolic execution state
/// \param lhs_fs: expanded symbol
/// \param ssa_rhs: right-hand-side value to assign
/// \param target: symbolic execution equation store
/// \param allow_pointer_unsoundness: allow pointer unsoundness
/// The condition under which the store \p rhs, assigned to an array that is
/// a part of \p object, writes element \p k -- or nullopt when that is not
/// known, in which case the element counts as written, as before:
///   with(b, i, v)  at an undecided i:   i == k, or k is written in b (b is
///                                      taken as the old value, as before,
///                                      unless it is itself a store)
///   c ? x : y                          c ? (k in x) : (k in y)
///   object's own old value             false
/// The `if` is what a store through a pointer with more than one target
/// leaves, the old value being the other target's case.
static optionalt<exprt> element_written(
  const exprt &rhs,
  const irep_idt &object,
  std::size_t k)
{
  if(rhs.id() == ID_with && rhs.operands().size() == 3)
  {
    const with_exprt &with = to_with_expr(rhs);
    if(with.where().is_constant())
      return {};
    const exprt here =
      equal_exprt{with.where(), from_integer(k, with.where().type())};
    // The base is taken to be the array's old value unless it is itself a
    // recognised store, as 6c5dd7e4 always took it.
    const auto in_base = element_written(with.old(), object, k);
    if(!in_base.has_value() || in_base->is_false())
      return {here};
    return {or_exprt{here, *in_base}};
  }
  if(rhs.id() == ID_if)
  {
    const if_exprt &ite = to_if_expr(rhs);
    const auto t = element_written(ite.true_case(), object, k);
    const auto f = element_written(ite.false_case(), object, k);
    if(!t.has_value() || !f.has_value())
      return {};
    if(t->is_false() && f->is_false())
      return {false_exprt{}};
    return {if_exprt{ite.cond(), *t, *f}};
  }
  if(
    is_ssa_expr(rhs) && !object.empty() &&
    to_ssa_expr(rhs).get_l1_object_identifier() == object)
  {
    return {false_exprt{}};
  }
  return {};
}

void field_sensitivityt::field_assignments_rec(
  const namespacet &ns,
  goto_symex_statet &state,
  const exprt &lhs_fs,
  const exprt &ssa_rhs,
  symex_targett &target,
  bool allow_pointer_unsoundness,
  const mp_integer &lo)
{
  if(is_ssa_expr(lhs_fs))
  {
    // See field_assignments: publish this leaf only if the store meets it.
    exprt meets = true_exprt{};
    const auto leaf_size = pointer_offset_size(lhs_fs.type(), ns);
    if(store_offset.is_not_nil() && lo >= 0 && leaf_size.has_value())
    {
      const exprt &offset = store_offset;
      meets = binary_relation_exprt{
        offset, ID_lt, from_integer(lo + *leaf_size, offset.type())};
      if(lo - store_size >= 0 || offset.type().id() == ID_signedbv)
        meets = and_exprt{
          meets,
          binary_relation_exprt{
            offset, ID_gt, from_integer(lo - store_size, offset.type())}};
    }
    const goto_symex_statet::shared_write_condition_scopet write_cond{
      state, meets};

    const ssa_exprt ssa_lhs = state
                                .assignment(
                                  to_ssa_expr(lhs_fs),
                                  ssa_rhs,
                                  ns,
                                  true,
                                  true,
                                  allow_pointer_unsoundness)
                                .get();

    // do the assignment
    target.assignment(
      state.guard.as_expr(),
      ssa_lhs,
      ssa_lhs,
      ssa_lhs.get_original_expr(),
      ssa_rhs,
      state.source,
      symex_targett::assignment_typet::STATE);
  }
  else if(
    ssa_rhs.type().id() == ID_struct || ssa_rhs.type().id() == ID_struct_tag)
  {
    const struct_typet &type = to_struct_type(ns.follow(ssa_rhs.type()));
    const struct_union_typet::componentst &components = type.components();

    PRECONDITION(
      components.empty() ||
      (lhs_fs.has_operands() && lhs_fs.operands().size() == components.size()));

    exprt::operandst::const_iterator fs_it = lhs_fs.operands().begin();
    for(const auto &comp : components)
    {
      const exprt member_rhs =
        simplify_opt(member_exprt{ssa_rhs, comp.get_name(), comp.type()}, ns);
      const exprt &member_lhs = *fs_it;
      const auto at = lo < 0 ? optionalt<mp_integer>{}
                             : member_offset(type, comp.get_name(), ns);

      field_assignments_rec(
        ns,
        state,
        member_lhs,
        member_rhs,
        target,
        allow_pointer_unsoundness,
        at.has_value() ? lo + *at : mp_integer{-1});
      ++fs_it;
    }
  }
#ifdef ENABLE_ARRAY_FIELD_SENSITIVITY
  else if(const auto &type = type_try_dynamic_cast<array_typet>(ssa_rhs.type()))
  {
    const std::size_t array_size =
      numeric_cast_v<std::size_t>(to_constant_expr(type->size()));
    PRECONDITION(lhs_fs.operands().size() == array_size);

    if(array_size > max_field_sensitivity_array_size)
      return;

    // A store at a *non-constant* index is lowered by symbolic execution into
    // read the whole array, write the whole array, with every element other
    // than the one stored to framed over from the value that was read.  The
    // split below turns that into one assignment per element, of the shape
    //   a[[k]] == (index == k ? new_value : a[[k]]#read)
    // Each of those assignments is an unconditional shared write of element k.
    // In a concurrent program that is wrong: the storing thread publishes a
    // write to every element of the array carrying the value it read when the
    // statement started, so any element another thread updated in between is
    // reset to that stale value.  The lost update is an artefact of the
    // lowering -- the program performs a single store -- and it produces
    // spurious counterexamples, including apparent violations of mutual
    // exclusion when the array holds per-element mutexes (a store to
    // a[i].datum frames a[k].mutex back to its pre-lock state).
    //
    // Record the element-selection condition so that only the element actually
    // stored to emits a *visible* write event; the SSA equality defining each
    // a[[k]] is unaffected, so this thread's own view of the array stays
    // exactly as before.  Framed-away elements simply keep whatever value the
    // interleaving gave them.
    //
    // A store through a pointer with more than one target arrives as
    // `c ? with(a, i, v) : a#old`, not as a bare `with`, and was not
    // recognised: every element's write was published, so on
    // workstealqueue_mutex-2 one thread's `r->field++` on items[2] republished
    // items[0] over the other thread's update of it. element_written sees
    // through the `if`.

    const auto element_size = pointer_offset_size(type->element_type(), ns);

    exprt::operandst::const_iterator fs_it = lhs_fs.operands().begin();
    for(std::size_t i = 0; i < array_size; ++i)
    {
      const exprt index_rhs = simplify_opt(
        index_exprt{ssa_rhs, from_integer(i, type->index_type())}, ns);
      const exprt &index_lhs = *fs_it;

      const auto written = element_written(ssa_rhs, store_object, i);
      const exprt element_cond =
        written.has_value() ? *written : static_cast<exprt>(true_exprt{});

      {
        const goto_symex_statet::shared_write_condition_scopet write_cond{
          state, element_cond};

        field_assignments_rec(
          ns,
          state,
          index_lhs,
          index_rhs,
          target,
          allow_pointer_unsoundness,
          lo >= 0 && element_size.has_value() ? lo + *element_size * i
                                              : mp_integer{-1});
      }
      ++fs_it;
    }
  }
#endif // ENABLE_ARRAY_FIELD_SENSITIVITY
  else if(lhs_fs.has_operands())
  {
    PRECONDITION(
      ssa_rhs.has_operands() &&
      lhs_fs.operands().size() == ssa_rhs.operands().size());

    exprt::operandst::const_iterator fs_it = lhs_fs.operands().begin();
    for(const exprt &op : ssa_rhs.operands())
    {
      // Position of the parts unknown here: no store condition below.
      field_assignments_rec(
        ns, state, *fs_it, op, target, allow_pointer_unsoundness, -1);
      ++fs_it;
    }
  }
  else
  {
    UNREACHABLE;
  }
}

exprt field_sensitivityt::get_fields_in_range(
  const namespacet &ns,
  goto_symex_statet &state,
  const ssa_exprt &ssa_expr,
  const exprt &offset,
  const mp_integer &size,
  const mp_integer &lo,
  bool l2) const
{
  // Unlike get_fields, which renames each part as a whole once it is built,
  // rename every leaf here, under the conditions of all the parts that hold
  // it: renamed as a whole, a part would emit its leaves' events after the
  // inner conditions were gone.
  const bool rename_leaves = l2 || !ssa_expr.get_level_2().empty();

  // One part, starting at byte `at`, under "[offset, offset + size) meets
  // its bytes", when its size is known and the condition applies.
  auto part = [&](ssa_exprt tmp, const mp_integer &at, bool condition) {
    const auto part_size = pointer_offset_size(tmp.type(), ns);
    exprt meets = true_exprt{};
    if(condition && part_size.has_value())
    {
      meets = binary_relation_exprt{
        offset, ID_lt, from_integer(at + *part_size, offset.type())};
      if(at - size >= 0 || offset.type().id() == ID_signedbv)
        meets = and_exprt{
          meets,
          binary_relation_exprt{
            offset, ID_gt, from_integer(at - size, offset.type())}};
    }
    // On the read events only: see goto_symex_statet::shared_read_cond.
    const goto_symex_statet::shared_read_condition_scopet read_cond{
      state, meets};
    return is_divisible(tmp)
             ? get_fields_in_range(
                 ns, state, tmp, offset, size, at, rename_leaves)
             : rename_leaves ? state.rename(exprt{tmp}, ns).get()
                             : static_cast<exprt>(tmp);
  };

  if(ssa_expr.type().id() == ID_struct || ssa_expr.type().id() == ID_struct_tag)
  {
    const struct_typet &type = to_struct_type(ns.follow(ssa_expr.type()));
    struct_exprt::operandst fields;
    fields.reserve(type.components().size());
    const exprt &struct_op = ssa_expr.get_original_expr();
    for(const auto &comp : type.components())
    {
      ssa_exprt tmp = ssa_expr;
      tmp.remove_level_2();
      tmp.set_expression(member_exprt{struct_op, comp.get_name(), comp.type()});
      const auto at = member_offset(type, comp.get_name(), ns);
      // Members are not conditioned: a load of one member of an element
      // still reads the element, and the untouched members of a store's
      // base are written back from what was read, which has to be current.
      fields.push_back(part(std::move(tmp), at.has_value() ? lo + *at : lo,
                            false));
    }
    return struct_exprt(std::move(fields), ssa_expr.type());
  }
#ifdef ENABLE_ARRAY_FIELD_SENSITIVITY
  else if(
    ssa_expr.type().id() == ID_array &&
    to_array_type(ssa_expr.type()).size().id() == ID_constant)
  {
    const mp_integer mp_array_size = numeric_cast_v<mp_integer>(
      to_constant_expr(to_array_type(ssa_expr.type()).size()));
    if(mp_array_size < 0 || mp_array_size > max_field_sensitivity_array_size)
      return ssa_expr;
    const array_typet &type = to_array_type(ssa_expr.type());
    const auto element_size = pointer_offset_size(type.element_type(), ns);
    const std::size_t array_size = numeric_cast_v<std::size_t>(mp_array_size);
    array_exprt::operandst elements;
    elements.reserve(array_size);
    const exprt &array = ssa_expr.get_original_expr();
    for(std::size_t i = 0; i < array_size; ++i)
    {
      ssa_exprt tmp = ssa_expr;
      tmp.remove_level_2();
      tmp.set_expression(index_exprt{array, from_integer(i, type.index_type())});
      elements.push_back(part(
        std::move(tmp),
        element_size.has_value() ? lo + *element_size * i : lo,
        element_size.has_value()));
    }
    return array_exprt(std::move(elements), type);
  }
#endif // ENABLE_ARRAY_FIELD_SENSITIVITY
  else
    return ssa_expr;
}

bool field_sensitivityt::is_divisible(const ssa_exprt &expr) const
{
  if(expr.type().id() == ID_struct || expr.type().id() == ID_struct_tag)
    return true;

#ifdef ENABLE_ARRAY_FIELD_SENSITIVITY
  if(
    expr.type().id() == ID_array &&
    to_array_type(expr.type()).size().id() == ID_constant &&
    numeric_cast_v<mp_integer>(to_constant_expr(
      to_array_type(expr.type()).size())) <= max_field_sensitivity_array_size)
  {
    return true;
  }
#endif

  return false;
}

exprt field_sensitivityt::simplify_opt(exprt e, const namespacet &ns) const
{
  if(!should_simplify)
    return e;

  return simplify_expr(std::move(e), ns);
}
