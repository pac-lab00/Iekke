/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "symex_assign.h"

#include "expr_skeleton.h"
#include "goto_symex_state.h"
#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/expr_util.h>
#include <util/pointer_offset_size.h>
#include <util/range.h>
#include <util/simplify_expr.h>

#include "symex_config.h"

// We can either use with_exprt or update_exprt when building expressions that
// modify components of an array or a struct. Set USE_UPDATE to use
// update_exprt.
// #define USE_UPDATE

constexpr bool use_update()
{
#ifdef USE_UPDATE
  return true;
#else
  return false;
#endif
}

void symex_assignt::assign_rec(
  const exprt &lhs,
  const expr_skeletont &full_lhs,
  const exprt &rhs,
  exprt::operandst &guard)
{
  if(is_ssa_expr(lhs))
  {
    assign_symbol(to_ssa_expr(lhs), full_lhs, rhs, guard);
  }
  else if(lhs.id() == ID_index)
    assign_array<use_update()>(to_index_expr(lhs), full_lhs, rhs, guard);
  else if(lhs.id()==ID_member)
  {
    const typet &type = to_member_expr(lhs).struct_op().type();
    if(type.id() == ID_struct || type.id() == ID_struct_tag)
    {
      assign_struct_member<use_update()>(
        to_member_expr(lhs), full_lhs, rhs, guard);
    }
    else if(type.id() == ID_union || type.id() == ID_union_tag)
    {
      // should have been replaced by byte_extract
      throw unsupported_operation_exceptiont(
        "assign_rec: unexpected assignment to union member");
    }
    else
      throw unsupported_operation_exceptiont(
        "assign_rec: unexpected assignment to member of '" + type.id_string() +
        "'");
  }
  else if(lhs.id()==ID_if)
    assign_if(to_if_expr(lhs), full_lhs, rhs, guard);
  else if(lhs.id()==ID_typecast)
    assign_typecast(to_typecast_expr(lhs), full_lhs, rhs, guard);
  else if(goto_symex_statet::is_read_only_object(lhs))
  {
    // ignore
  }
  else if(lhs.id()==ID_byte_extract_little_endian ||
          lhs.id()==ID_byte_extract_big_endian)
  {
    assign_byte_extract(to_byte_extract_expr(lhs), full_lhs, rhs, guard);
  }
  else if(lhs.id() == ID_complex_real)
  {
    // this is stuff like __real__ x = 1;
    const complex_real_exprt &complex_real_expr = to_complex_real_expr(lhs);

    const complex_imag_exprt complex_imag_expr(complex_real_expr.op());

    complex_exprt new_rhs(
      rhs, complex_imag_expr, to_complex_type(complex_real_expr.op().type()));

    assign_rec(complex_real_expr.op(), full_lhs, new_rhs, guard);
  }
  else if(lhs.id() == ID_complex_imag)
  {
    const complex_imag_exprt &complex_imag_expr = to_complex_imag_expr(lhs);

    const complex_real_exprt complex_real_expr(complex_imag_expr.op());

    complex_exprt new_rhs(
      complex_real_expr, rhs, to_complex_type(complex_imag_expr.op().type()));

    assign_rec(complex_imag_expr.op(), full_lhs, new_rhs, guard);
  }
  else
    throw unsupported_operation_exceptiont(
      "assignment to '" + lhs.id_string() + "' not handled");
}

/// Assignment from the rhs value to the lhs variable
struct assignmentt final
{
  ssa_exprt lhs;
  /// Skeleton to reconstruct the original lhs in the assignment
  expr_skeletont original_lhs_skeleton;
  exprt rhs;
};

/// Assign a struct expression to a symbol. If \ref symex_assignt::assign_symbol
/// was used then we would assign the whole symbol, before extracting its
/// components, with results like
/// `x = {1, 2}; x..field1 = x.field1; x..field2 = x.field2;`
/// This abbreviates the process, directly producing
/// `x..field1 = 1; x..field2 = 2;`
/// \param lhs: symbol to assign (already renamed to L1)
/// \param full_lhs: expression skeleton corresponding to \p lhs, to be included
///   in the result trace
/// \param rhs: struct expression to assign to \p lhs
/// \param guard: guard conjuncts that must hold for this assignment to be made
void symex_assignt::assign_from_struct(
  const ssa_exprt &lhs, // L1
  const expr_skeletont &full_lhs,
  const struct_exprt &rhs,
  const exprt::operandst &guard)
{
  const auto &components = to_struct_type(ns.follow(lhs.type())).components();
  PRECONDITION(rhs.operands().size() == components.size());

  for(const auto &comp_rhs : make_range(components).zip(rhs.operands()))
  {
    const auto &comp = comp_rhs.first;
    const exprt lhs_field = state.field_sensitivity.apply(
      ns, state, member_exprt{lhs, comp.get_name(), comp.type()}, true);
    INVARIANT(
      lhs_field.id() == ID_symbol,
      "member of symbol should be susceptible to field-sensitivity");

    assign_symbol(to_ssa_expr(lhs_field), full_lhs, comp_rhs.second, guard);
  }
}

void symex_assignt::assign_non_struct_symbol(
  const ssa_exprt &lhs, // L1
  const expr_skeletont &full_lhs,
  const exprt &rhs,
  const exprt::operandst &guard)
{
  // A store into one element of a shared array that field sensitivity does not
  // split -- of symbolic size, or of constant size above
  // max_field_sensitivity_array_size -- is `a#new == with(a#old, i, v)`: the
  // whole array, rebuilt from this thread's last view of it. Published as a
  // whole, it would put back elements another thread stored to since that
  // view: a lost update. So the old value is read and the new one written in
  // an atomic section of their own, and the elements copied back are the
  // current ones -- exactly what a store to element i alone leaves in the
  // others. A store to a member path of the element (`a[i].m = v`) renames
  // the carried bases inside the section too, see member_store below. The index and the stored
  // value are renamed first, outside it: they are reads the program makes on
  // their own, and making them atomic with the store would hide races.
  // The section is atomic for values only: the data-race encoding still
  // sees a plain store (SSA_stept::in_program_atomic_section).
  static unsigned monolithic_store_section =
    SSA_stept::first_store_atomic_section;
  const bool monolithic_store =
    state.atomic_section_id == 0 && lhs.type().id() == ID_array &&
    !state.field_sensitivity.is_divisible(lhs) &&
    (rhs.id() == ID_with || rhs.id() == ID_byte_update_little_endian ||
     rhs.id() == ID_byte_update_big_endian) &&
    rhs.operands().size() == 3 && rhs.op0() == lhs &&
    state.write_is_shared(lhs, ns) ==
      goto_symex_statet::write_is_shared_resultt::SHARED;

  exprt l2_rhs;
  if(monolithic_store)
  {
    // Through a pointer that may point elsewhere the store is guarded, as in
    // the branch below; the old value is then the one read here.
    const exprt l2_cond =
      guard.empty() ? static_cast<exprt>(true_exprt{})
                    : state.rename(conjunction(guard), ns).get();
    exprt l2_where = state.rename(rhs.op1(), ns).get();
    // The stored value of `a[i].m = v` is `with(a[i], m, v)` (deeper for a
    // nested member, member_store_depth). Its bases are not reads the program
    // makes -- the other members are carried back -- and, read before the
    // section, they could be stale by the time of the store, losing the
    // members another thread stored in between. So they are renamed inside
    // the section, with the old value; v stays outside, so
    // `a[i].m = a[i].m + 1` keeps its real lost update.
    const bool member_store =
      rhs.op2().id() == ID_with && rhs.op2().operands().size() == 3 &&
      to_with_expr(rhs.op2()).where().id() == ID_member_name &&
      to_with_expr(rhs.op2()).old().id() == ID_index &&
      to_index_expr(to_with_expr(rhs.op2()).old()).array() == rhs.op0();
    exprt l2_value = rhs.op2();
    const std::size_t member_levels =
      member_store ? member_store_depth(rhs.op2()) : 0;
    // the stored value at the end of the member chain
    const auto stored_value = [member_levels](exprt &e) -> exprt & {
      exprt *part = &e;
      for(std::size_t level = 0; level < member_levels; ++level)
        part = &to_with_expr(*part).new_value();
      return *part;
    };
    if(member_store)
    {
      exprt &v = stored_value(l2_value);
      v = state.rename(v, ns).get();
    }
    else
      l2_value = state.rename(rhs.op2(), ns).get();
    state.atomic_section_id = ++monolithic_store_section;
    state.read_in_atomic_section.clear();
    state.written_in_atomic_section.clear();
    target.atomic_begin(
      state.guard.as_expr(), state.atomic_section_id, state.source);
    exprt l2_old;
    {
      // Read only where the store reaches this object (see shared_read_cond).
      const goto_symex_statet::shared_read_condition_scopet read_cond{
        state, l2_cond};
      l2_old = state.rename(rhs.op0(), ns).get();
      if(member_store)
      {
        // The bases' read events add nothing: the array is not split, and
        // the read of its old value above already covers every element.
        exprt *part = &l2_value;
        for(std::size_t level = 0; level < member_levels; ++level)
        {
          with_exprt &member_with = to_with_expr(*part);
          member_with.old() = state.rename(member_with.old(), ns).get();
          part = &member_with.new_value();
        }
      }
    }
    exprt l2_new = rhs;
    l2_new.op0() = l2_old;
    l2_new.op1() = std::move(l2_where);
    l2_new.op2() = std::move(l2_value);
    l2_rhs = guard.empty()
               ? std::move(l2_new)
               : static_cast<exprt>(if_exprt{l2_cond, l2_new, l2_old});
  }
  else if(guard.empty())
    l2_rhs = state.rename(rhs, ns).get();
  else
  {
    // Put the assignment guard into the rhs: `(c ? p : q) = e` stores e to p
    // under c and frames the old value of p back over p under !c. That old
    // value is not read by the program -- on the branch where it is used,
    // the program accesses q, not p -- so rename it without recording a
    // shared read, exactly as the write below is made conditional on the
    // guard. Recorded, it carried only the path guard: a store through a
    // pointer to one of two locked objects was seen reading the other while
    // holding the wrong lock, and paired with its writer as a race.
    // Reads inside an atomic section are recorded regardless (see
    // goto_symex_statet::rename), so those are unchanged.
    //
    // The old value of an object field sensitivity splits (a struct, or an
    // array of constant size within the bound) is its leaves' current values.
    // The bare symbol names the whole-object version, which no assignment
    // updates once the object is split: for a struct it is unconstrained, for
    // an array it predates every element store. So it is expanded to the
    // leaves, as stock CBMC does inside the `if`.
    const exprt l2_cond = state.rename(conjunction(guard), ns).get();
    const exprt l2_new = state.rename(rhs, ns).get();
    state.record_events.push(false);
    const exprt l2_old =
      state
        .rename(
          state.field_sensitivity.is_divisible(lhs)
            ? state.field_sensitivity.apply(ns, state, exprt{lhs}, false)
            : exprt{lhs},
          ns)
        .get();
    state.record_events.pop();
    l2_rhs = if_exprt{l2_cond, l2_new, l2_old};
  }

  assignmentt assignment{lhs, full_lhs, l2_rhs};

  if(symex_config.simplify_opt)
    assignment.rhs = simplify_expr(std::move(assignment.rhs), ns);

  // When the assignment is conditional, the rhs built above frames the old
  // value of the object back over itself on the branch where the condition
  // does not hold.  That framing is synthesised here, not written by the
  // program, so it must not surface as a shared write event: publishing it
  // would reset whatever another thread stored between the read of the old
  // value and this write.  Keep the SSA equality as it is (this thread's own
  // view has to stay correct) and make only the *event* conditional.
  const goto_symex_statet::shared_write_condition_scopet write_cond{
    state, guard.empty() ? static_cast<exprt>(true_exprt{}) : conjunction(guard)};

  const ssa_exprt l2_lhs = state
                             .assignment(
                               assignment.lhs,
                               assignment.rhs,
                               ns,
                               symex_config.simplify_opt,
                               symex_config.constant_propagation,
                               symex_config.allow_pointer_unsoundness)
                             .get();

  state.record_events.push(false);
  // Note any other symbols mentioned in the skeleton are rvalues -- for example
  // array indices -- and were renamed to L2 at the start of
  // goto_symext::symex_assign.
  const exprt l2_full_lhs = assignment.original_lhs_skeleton.apply(l2_lhs);
  if(symex_config.run_validation_checks)
  {
    INVARIANT(
      !check_renaming(l2_full_lhs), "l2_full_lhs should be renamed to L2");
  }
  state.record_events.pop();

  auto current_assignment_type =
    ns.lookup(l2_lhs.get_object_name()).is_auxiliary
      ? symex_targett::assignment_typet::HIDDEN
      : assignment_type;

  target.assignment(
    make_and(state.guard.as_expr(), conjunction(guard)),
    l2_lhs,
    l2_full_lhs,
    get_original_name(l2_full_lhs),
    assignment.rhs,
    state.source,
    current_assignment_type);

  if(monolithic_store)
  {
    const unsigned section = state.atomic_section_id;
    state.atomic_section_id = 0;
    target.atomic_end(state.guard.as_expr(), section, state.source);
  }

  const ssa_exprt &l1_lhs = assignment.lhs;
  if(state.field_sensitivity.is_divisible(l1_lhs))
  {
    // Split composite symbol lhs into its components
    state.field_sensitivity.field_assignments(
      ns,
      state,
      l1_lhs,
      assignment.rhs,
      target,
      symex_config.allow_pointer_unsoundness);
    // Erase the composite symbol from our working state. Note that we need to
    // have it in the propagation table and the value set while doing the field
    // assignments, thus we cannot skip putting it in there above.
    state.propagation.erase_if_exists(l1_lhs.get_identifier());
    state.value_set.erase_symbol(l1_lhs, ns);
  }
}

void symex_assignt::assign_symbol(
  const ssa_exprt &lhs, // L1
  const expr_skeletont &full_lhs,
  const exprt &rhs,
  const exprt::operandst &guard)
{
  // Shortcut the common case of a whole-struct initializer:
  if(rhs.id() == ID_struct)
    assign_from_struct(lhs, full_lhs, to_struct_expr(rhs), guard);
  else
    assign_non_struct_symbol(lhs, full_lhs, rhs, guard);
}

void symex_assignt::assign_typecast(
  const typecast_exprt &lhs,
  const expr_skeletont &full_lhs,
  const exprt &rhs,
  exprt::operandst &guard)
{
  // these may come from dereferencing on the lhs
  exprt rhs_typecasted = typecast_exprt::conditional_cast(rhs, lhs.op().type());

  expr_skeletont new_skeleton =
    full_lhs.compose(expr_skeletont::remove_op0(lhs));
  assign_rec(lhs.op(), new_skeleton, rhs_typecasted, guard);
}

template <bool use_update>
void symex_assignt::assign_array(
  const index_exprt &lhs,
  const expr_skeletont &full_lhs,
  const exprt &rhs,
  exprt::operandst &guard)
{
  const exprt &lhs_array=lhs.array();
  const exprt &lhs_index=lhs.index();
  const typet &lhs_index_type = lhs_array.type();

  PRECONDITION(lhs_index_type.id() == ID_array);

  if(use_update)
  {
    // turn
    //   a[i]=e
    // into
    //   a'==UPDATE(a, [i], e)
    const update_exprt new_rhs{lhs_array, index_designatort(lhs_index), rhs};
    const expr_skeletont new_skeleton =
      full_lhs.compose(expr_skeletont::remove_op0(lhs));
    assign_rec(lhs, new_skeleton, new_rhs, guard);
  }
  else
  {
    // turn
    //   a[i]=e
    // into
    //   a'==a WITH [i:=e]
    const with_exprt new_rhs{lhs_array, lhs_index, rhs};
    const expr_skeletont new_skeleton =
      full_lhs.compose(expr_skeletont::remove_op0(lhs));
    assign_rec(lhs_array, new_skeleton, new_rhs, guard);
  }
}

template <bool use_update>
void symex_assignt::assign_struct_member(
  const member_exprt &lhs,
  const expr_skeletont &full_lhs,
  const exprt &rhs,
  exprt::operandst &guard)
{
  // Symbolic execution of a struct member assignment.

  // lhs must be member operand, which
  // takes one operand, which must be a structure.

  exprt lhs_struct = lhs.op();

  // typecasts involved? C++ does that for inheritance.
  if(lhs_struct.id()==ID_typecast)
  {
    if(to_typecast_expr(lhs_struct).op().id() == ID_null_object)
    {
      // ignore, and give up
      return;
    }
    else
    {
      // remove the type cast, we assume that the member is there
      exprt tmp = to_typecast_expr(lhs_struct).op();

      if(tmp.type().id() == ID_struct || tmp.type().id() == ID_struct_tag)
        lhs_struct=tmp;
      else
        return; // ignore and give up
    }
  }

  const irep_idt &component_name=lhs.get_component_name();

  if(use_update)
  {
    // turn
    //   a.c=e
    // into
    //   a'==UPDATE(a, .c, e)
    const update_exprt new_rhs{
      lhs_struct, member_designatort(component_name), rhs};
    const expr_skeletont new_skeleton =
      full_lhs.compose(expr_skeletont::remove_op0(lhs));
    assign_rec(lhs_struct, new_skeleton, new_rhs, guard);
  }
  else
  {
    // turn
    //   a.c=e
    // into
    //   a'==a WITH [c:=e]

    with_exprt new_rhs(lhs_struct, exprt(ID_member_name), rhs);
    new_rhs.where().set(ID_component_name, component_name);
    const expr_skeletont new_skeleton =
      full_lhs.compose(expr_skeletont::remove_op0(lhs));
    assign_rec(lhs_struct, new_skeleton, new_rhs, guard);
  }
}

void symex_assignt::assign_if(
  const if_exprt &lhs,
  const expr_skeletont &full_lhs,
  const exprt &rhs,
  exprt::operandst &guard)
{
  // we have (c?a:b)=e;

  guard.push_back(lhs.cond());
  assign_rec(lhs.true_case(), full_lhs, rhs, guard);
  guard.pop_back();

  guard.push_back(not_exprt(lhs.cond()));
  assign_rec(lhs.false_case(), full_lhs, rhs, guard);
  guard.pop_back();
}

void symex_assignt::assign_byte_extract(
  const byte_extract_exprt &lhs,
  const expr_skeletont &full_lhs,
  const exprt &rhs,
  exprt::operandst &guard)
{
  // we have byte_extract_X(object, offset)=value
  // turn into object=byte_update_X(object, offset, value)

  irep_idt byte_update_id;
  if(lhs.id()==ID_byte_extract_little_endian)
    byte_update_id = ID_byte_update_little_endian;
  else if(lhs.id()==ID_byte_extract_big_endian)
    byte_update_id = ID_byte_update_big_endian;
  else
    UNREACHABLE;

  // A store whose bytes all lie outside the object leaves the object as it
  // was: the bytes of a byte_update that fall outside its operand are
  // dropped. It still cost a write of every member, and a shared-write
  // event on each, which then raced with any access to the object. Such
  // stores come from a dereference resolved against an object the pointer
  // does not point into: on the ldv-linux irda drivers a third of the stores
  // into struct net_device (1872 bytes) were at offsets near 6 MB, each one
  // rewriting all of it. Leave them out. An out-of-bounds access is still
  // reported by the pointer checks, which do not depend on this.
  {
    const auto offset =
      numeric_cast<mp_integer>(simplify_expr(lhs.offset(), ns));
    const auto object_size = pointer_offset_size(lhs.op().type(), ns);
    const auto value_size = pointer_offset_size(rhs.type(), ns);
    if(
      offset.has_value() && object_size.has_value() &&
      value_size.has_value() &&
      (*offset >= *object_size || *offset + *value_size <= 0))
    {
      return;
    }
  }

  const byte_update_exprt new_rhs{byte_update_id, lhs.op(), lhs.offset(), rhs};
  const expr_skeletont new_skeleton =
    full_lhs.compose(expr_skeletont::remove_op0(lhs));
  assign_rec(lhs.op(), new_skeleton, new_rhs, guard);
}
