/// \file
/// lazy_po: array read-from (--array-rf), answering an element read by matching the writes

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

/// Is this expression a whole-array constant whose elements are all the same
/// value? `array_of` says so directly; an `array` literal has to be checked.
/// Anything else cannot serve as the value an element holds before any write.
static std::optional<exprt> uniform_array_value(const exprt &expr)
{
  if(expr.id() == ID_array_of)
    return to_array_of_expr(expr).what();

  if(expr.id() == ID_array && !expr.operands().empty())
  {
    const exprt &first = expr.operands().front();
    for(const auto &op : expr.operands())
      if(op != first)
        return {};
    return first;
  }

  return {};
}

/// `c ? V WITH [i:=v] : V` (either way round) over one object: a point update
/// of V that happens where the condition holds. Returns the condition, the
/// `with` and the version it updates, or nothing.
static std::optional<std::tuple<exprt, with_exprt, exprt>>
conditional_point_update(const exprt &rhs, const irep_idt &variable)
{
  if(rhs.id() != ID_if)
    return {};
  const if_exprt &ite = to_if_expr(rhs);
  const auto match = [&](const exprt &upd, const exprt &keep, const exprt &cond)
    -> std::optional<std::tuple<exprt, with_exprt, exprt>> {
    if(upd.id() != ID_with || upd.operands().size() != 3 ||
       keep.id() != ID_symbol || upd.operands()[0] != keep ||
       narrowing_base(keep) != variable)
      return {};
    return std::make_tuple(cond, to_with_expr(upd), keep);
  };
  if(auto m = match(ite.true_case(), ite.false_case(), ite.cond()))
    return m;
  return match(ite.false_case(), ite.true_case(), not_exprt{ite.cond()});
}

/// `byte_update(V, o, v)` over one object, or `c ? byte_update(V, o, v) : V`
/// (either way round), the form a write through a pointer takes when its type
/// is not the element type. Returns the condition, the offset, the value and
/// the version it updates, or nothing.
static std::optional<std::tuple<exprt, exprt, exprt, exprt>>
point_byte_update(const exprt &rhs, const irep_idt &variable)
{
  const auto plain = [&](const exprt &upd)
    -> std::optional<std::tuple<exprt, exprt, exprt, exprt>> {
    if(upd.id() != ID_byte_update_little_endian)
      return {};
    const auto &bu = to_byte_update_expr(upd);
    if(bu.op().id() != ID_symbol || narrowing_base(bu.op()) != variable)
      return {};
    return std::make_tuple(
      static_cast<exprt>(true_exprt{}), bu.offset(), bu.value(), bu.op());
  };
  if(auto p = plain(rhs))
    return p;
  if(rhs.id() != ID_if)
    return {};
  const if_exprt &ite = to_if_expr(rhs);
  const auto match = [&](const exprt &upd, const exprt &keep, const exprt &cond)
    -> std::optional<std::tuple<exprt, exprt, exprt, exprt>> {
    auto p = plain(upd);
    if(!p || keep.id() != ID_symbol || std::get<3>(*p) != keep)
      return {};
    std::get<0>(*p) = cond;
    return p;
  };
  if(auto m = match(ite.true_case(), ite.false_case(), ite.cond()))
    return m;
  return match(ite.false_case(), ite.true_case(), not_exprt{ite.cond()});
}

/// `c ? V#a : V#b`, both versions of \p variable: the merge symex makes where
/// two paths of one thread meet. It selects the version the path that ran left
/// behind, and every write on either path is an event of its own, executed only
/// where its guard -- which includes the path condition -- holds. So in the
/// read-from encoding it observes nothing but its condition. (Symex merges a
/// shared object only while one thread runs, so a merge is never a write event
/// of its own.)
static bool own_version_merge(const exprt &rhs, const irep_idt &variable)
{
  if(rhs.id() != ID_if)
    return false;
  const if_exprt &ite = to_if_expr(rhs);
  return ite.true_case().id() == ID_symbol &&
         ite.false_case().id() == ID_symbol &&
         narrowing_base(ite.true_case()) == variable &&
         narrowing_base(ite.false_case()) == variable;
}

/// `V#a = V#b` for every candidate V: symex copies a version it has read into
/// a fresh one before indexing it (`#6 = #5; t = #6[i]`). An SSA assignment is
/// an unconditional equality, so an element of the copy is that element of the
/// version copied, and the read-from of the read event it came from applies.
static std::map<irep_idt, irep_idt> own_version_copies(
  const symex_target_equationt &equation,
  const std::set<irep_idt> &variables)
{
  std::map<irep_idt, irep_idt> copy_of;
  for(const auto &step : equation.SSA_steps)
  {
    if(
      step.is_assignment() && !step.ssa_lhs.is_nil() &&
      step.ssa_rhs.id() == ID_symbol &&
      narrowing_base(step.ssa_rhs) == narrowing_base(step.ssa_lhs) &&
      variables.count(narrowing_base(step.ssa_lhs)) != 0)
    {
      copy_of.emplace(
        to_symbol_expr(step.ssa_lhs).get_identifier(),
        to_symbol_expr(step.ssa_rhs).get_identifier());
    }
  }
  return copy_of;
}

/// Follow \p copy_of from \p id to the version it was copied from, until one
/// that is not a copy.
static irep_idt
copied_from(const std::map<irep_idt, irep_idt> &copy_of, irep_idt id)
{
  for(std::size_t hops = 0; hops <= copy_of.size(); ++hops)
  {
    const auto it = copy_of.find(id);
    if(it == copy_of.end())
      break;
    id = it->second;
  }
  return id;
}

void lazy_pot::compute_array_rf(const symex_target_equationt &equation)
{
  array_rf_writes.clear();
  array_rf_default.clear();
  array_rf_bytewise.clear();
  if(!array_rf)
    return;

  // candidates: shared objects of array type that are still in the chain
  std::set<irep_idt> candidates;
  for(const auto &v : global_variables)
  {
    if(writes.count(v) == 0 || writes.at(v).empty())
      continue;
    if(writes.at(v).front().s_it->ssa_lhs.type().id() == ID_array)
      candidates.insert(v);
  }
  if(candidates.empty())
    return;

  // Every occurrence of one of these objects has to be either the base of a
  // `with` or the array of an `index`. A use of the array as a whole -- a copy,
  // a comparison, an argument -- has no index to match on, so the object keeps
  // its chain. Taking an address does not read the value.
  std::set<irep_idt> opaque;
  std::map<irep_idt, std::vector<std::pair<irep_idt, exprt>>> index_uses;
  const bool why = getenv("LAZYPO_ARRAY_WHY") != nullptr;
  // with --array-rf-bytes, byte reads and byte updates are accepted too; the
  // objects they touch are answered byte by byte
  const bool bytes = array_rf_bytes;
  std::set<irep_idt> byte_used;
  std::map<irep_idt, std::vector<typet>> byte_read_types;
  std::function<void(const exprt &, const irep_idt &)> scan =
    [&](const exprt &expr, const irep_idt &parent) {
    if(expr.id() == ID_address_of)
      return;

    // `(T *)a` with a an array is the address of its first element, as for
    // address_of: memory-leak tracking records `(const void *)dynamic_object1`
    if(
      expr.id() == ID_typecast && expr.type().id() == ID_pointer &&
      to_typecast_expr(expr).op().id() == ID_symbol &&
      to_typecast_expr(expr).op().type().id() == ID_array)
    {
      return;
    }

    if(expr.id() == ID_index)
    {
      const auto &idx = to_index_expr(expr);
      if(idx.array().id() == ID_symbol)
      {
        const irep_idt id = to_symbol_expr(idx.array()).get_identifier();
        const irep_idt base = narrowing_base(idx.array());
        if(candidates.count(base) != 0)
        {
          index_uses[base].emplace_back(id, idx.index());
          scan(idx.index(), expr.id());
          return;
        }
      }
    }

    // a byte read of a version, as an index read is an element read
    if(
      bytes && expr.id() == ID_byte_extract_little_endian &&
      to_byte_extract_expr(expr).op().id() == ID_symbol &&
      candidates.count(narrowing_base(to_byte_extract_expr(expr).op())) != 0)
    {
      const auto &be = to_byte_extract_expr(expr);
      const irep_idt base = narrowing_base(be.op());
      index_uses[base].emplace_back(
        to_symbol_expr(be.op()).get_identifier(), be.offset());
      byte_used.insert(base);
      byte_read_types[base].push_back(be.type());
      scan(be.offset(), expr.id());
      return;
    }

    if(expr.id() == ID_with && !expr.operands().empty() &&
       expr.operands()[0].id() == ID_symbol &&
       candidates.count(narrowing_base(expr.operands()[0])) != 0)
    {
      for(std::size_t i = 1; i < expr.operands().size(); ++i)
        scan(expr.operands()[i], expr.id());
      return;
    }

    if(expr.id() == ID_symbol)
    {
      const irep_idt base = narrowing_base(expr);
      if(candidates.count(base) != 0 && opaque.insert(base).second && why)
        std::cerr << "ARRAY_WHY_DETAIL " << base << " used bare inside a "
                  << parent << "\n";
      return;
    }

    for(const auto &op : expr.operands())
      scan(op, expr.id());
  };

  for(const auto &step : equation.SSA_steps)
  {
    // `a#3 = a#2` copies one version of the object to another. It does not
    // observe the array as a whole, so it must not force the chain to stay --
    // and the lambda cannot tell, since it never sees the left-hand side.
    // twalock declined for exactly this: __twa_array#3 = __twa_array#<prev>.
    const bool own_copy =
      step.is_assignment() && !step.ssa_lhs.is_nil() &&
      step.ssa_rhs.id() == ID_symbol &&
      narrowing_base(step.ssa_rhs) == narrowing_base(step.ssa_lhs) &&
      candidates.count(narrowing_base(step.ssa_lhs)) != 0;

    // `V#n = c ? V#k WITH [i:=v] : V#k` updates one element of V where c
    // holds; V#k inside it is the version updated, not an observation.
    if(
      step.is_assignment() && !step.ssa_lhs.is_nil() &&
      candidates.count(narrowing_base(step.ssa_lhs)) != 0)
    {
      if(bytes)
        if(const auto bu = point_byte_update(
             step.ssa_rhs, narrowing_base(step.ssa_lhs)))
        {
          byte_used.insert(narrowing_base(step.ssa_lhs));
          scan(std::get<0>(*bu), "byte update");
          scan(std::get<1>(*bu), "byte update");
          scan(std::get<2>(*bu), "byte update");
          if(!step.guard.is_nil())
            scan(step.guard, "guard");
          continue;
        }
      if(own_version_merge(step.ssa_rhs, narrowing_base(step.ssa_lhs)))
      {
        scan(to_if_expr(step.ssa_rhs).cond(), "merge");
        if(!step.guard.is_nil())
          scan(step.guard, "guard");
        continue;
      }
      if(const auto cu = conditional_point_update(
           step.ssa_rhs, narrowing_base(step.ssa_lhs)))
      {
        scan(std::get<0>(*cu), "conditional update");
        scan(std::get<1>(*cu).where(), "conditional update");
        scan(std::get<1>(*cu).new_value(), "conditional update");
        if(!step.guard.is_nil())
          scan(step.guard, "guard");
        continue;
      }
    }

    if(!step.ssa_rhs.is_nil() && !own_copy)
      scan(
          step.ssa_rhs,
          step.ssa_lhs.is_nil()
            ? irep_idt{"assignment-rhs"}
            : irep_idt{"assignment-rhs, lhs=" +
                       id2string(to_symbol_expr(step.ssa_lhs).get_identifier())});
    if(!step.cond_expr.is_nil() && !step.is_assignment() && !step.is_decl())
      scan(step.cond_expr, "cond_expr");
    if(!step.guard.is_nil())
      scan(step.guard, "guard");
  }

  // how each write decomposes, by the assignment that produces its symbol
  std::map<irep_idt, exprt> defining_rhs;
  for(const auto &step : equation.SSA_steps)
  {
    if(!step.is_assignment() || step.ssa_lhs.is_nil())
      continue;
    if(candidates.count(narrowing_base(step.ssa_lhs)) == 0)
      continue;
    defining_rhs.emplace(
      to_symbol_expr(step.ssa_lhs).get_identifier(), step.ssa_rhs);
  }
  // A local array declared without an initialiser, `pthread_t t_ids[10000];`,
  // has its first version defined by the declaration, not by an assignment.
  // Its contents are whatever the stack held.
  std::set<irep_idt> declared;
  for(const auto &step : equation.SSA_steps)
  {
    if(
      step.is_decl() && !step.ssa_lhs.is_nil() &&
      step.ssa_lhs.id() == ID_symbol &&
      candidates.count(narrowing_base(step.ssa_lhs)) != 0)
    {
      declared.insert(to_symbol_expr(step.ssa_lhs).get_identifier());
    }
  }

  const bool explain = getenv("LAZYPO_ARRAY_WHY") != nullptr;
  const auto copy_of = own_version_copies(equation, candidates);
  for(const auto &variable : candidates)
  {
    if(opaque.count(variable) != 0)
    {
      if(explain)
        std::cerr << "ARRAY_WHY " << variable
                  << " declined: used as a whole object somewhere\n";
      continue;
    }

    // every index use has to name a shared read event, since that is what
    // places it in the schedule
    std::set<irep_idt> read_symbols;
    for(const auto &r : reads.count(variable) ? reads.at(variable)
                                              : std::vector<shared_event>{})
      read_symbols.insert(to_symbol_expr(r.s_it->ssa_lhs).get_identifier());
    bool indices_placed = true;
    for(const auto &use : index_uses[variable])
      if(read_symbols.count(copied_from(copy_of, use.first)) == 0)
      {
        if(indices_placed && explain)
          std::cerr << "ARRAY_WHY_INDEX " << variable << " index of "
                    << use.first << ", not a shared read event\n";
        indices_placed = false;
      }
    if(!indices_placed)
    {
      if(explain)
        std::cerr << "ARRAY_WHY " << variable
                  << " declined: an index() does not name a shared read event\n";
      continue;
    }

    std::vector<array_writet> decomposed;
    std::optional<exprt> initial;
    bool ok = true;
    const auto &ws = writes.at(variable);
    for(std::size_t i = 0; i < ws.size(); ++i)
    {
      const irep_idt id = to_symbol_expr(ws[i].s_it->ssa_lhs).get_identifier();
      const auto it = defining_rhs.find(id);
      if(it == defining_rhs.end() && declared.count(id) != 0)
      {
        // a write of nondeterministic contents, as for an allocation: element
        // j holds the declared version's own element j until written, so two
        // reads of it agree
        array_writet aw{i, true, nil_exprt{}, ws[i].s_it->ssa_lhs};
        aw.havoc = true;
        if(!initial.has_value())
          initial = ws[i].s_it->ssa_lhs;
        decomposed.push_back(aw);
        continue;
      }
      if(it == defining_rhs.end())
      {
        if(getenv("LAZYPO_ARRAY_WHY") != nullptr)
          std::cerr << "ARRAY_WHY_NODEF " << variable << " write symbol " << id
                    << " has no defining assignment in the equation\n";
        ok = false;
        break;
      }
      const exprt &rhs = it->second;
      if(rhs.id() == ID_with && rhs.operands().size() == 3 &&
         narrowing_base(rhs.operands()[0]) == variable)
      {
        decomposed.push_back(
          array_writet{i, false, rhs.operands()[1], rhs.operands()[2]});
        continue;
      }
      if(rhs.id() == ID_symbol && narrowing_base(rhs) == variable)
        continue; // a copy of the previous version writes nothing new
      if(const auto cu = conditional_point_update(rhs, variable))
      {
        array_writet aw{
          i, false, std::get<1>(*cu).where(), std::get<1>(*cu).new_value()};
        aw.condition = std::get<0>(*cu);
        decomposed.push_back(aw);
        continue;
      }
      if(bytes)
        if(const auto bu = point_byte_update(rhs, variable))
        {
          array_writet aw{i, false, nil_exprt{}, std::get<2>(*bu)};
          aw.condition = std::get<0>(*bu);
          aw.bytes = true;
          aw.offset = std::get<1>(*bu);
          // A byte update by ARRAY_OF(c) of n one-byte elements, n possibly
          // symbolic (memset(p, c, n) arrives so), writes the byte c at each
          // of [offset, offset + n): a range write, whose bytes are known
          // without a constant size. Only for a bit-vector element, whose
          // value is its own byte.
          const exprt &v = aw.value;
          if(
            v.id() == ID_array_of && v.type().id() == ID_array &&
            can_cast_type<bitvector_typet>(to_array_type(v.type()).element_type()) &&
            pointer_offset_bits(to_array_type(v.type()).element_type(), ns) ==
              mp_integer{8})
          {
            aw.length = to_array_type(v.type()).size();
            aw.value = to_array_of_expr(v).what();
          }
          decomposed.push_back(aw);
          continue;
        }

      if(rhs.id() == ID_nondet_symbol && rhs.type() == ws[i].s_it->ssa_lhs.type())
      {
        array_writet aw{i, true, nil_exprt{}, rhs};
        aw.havoc = true;
        if(!initial.has_value())
          initial = rhs; // no read can precede the allocation it comes from
        decomposed.push_back(aw);
        continue;
      }
      const auto uniform = uniform_array_value(rhs);
      if(uniform.has_value())
      {
        if(!initial.has_value())
          initial = uniform;
        decomposed.push_back(
          array_writet{i, true, nil_exprt{}, uniform.value()});
        continue;
      }
      if(getenv("LAZYPO_ARRAY_WHY") != nullptr)
        std::cerr << "ARRAY_WHY_WRITE " << variable << " rhs is " << rhs.id()
                  << (rhs.id() == ID_with && !rhs.operands().empty()
                        ? " over " + id2string(narrowing_base(rhs.operands()[0]))
                        : std::string{})
                  << "\n";
      ok = false; // a havoc, a copy, a non-uniform literal: no single value
      break;
    }
    if(!ok || !initial.has_value())
    {
      if(explain)
        std::cerr << "ARRAY_WHY " << variable << " declined: "
                  << (ok ? "no uniform constant initialiser"
                         : "a write is not a single-index update")
                  << "\n";
      continue;
    }

    // A byte-wise object needs a constant size for its element type, for every
    // value written and for every type read. The cost model below is written
    // for element reads; for these objects the selection is used whenever it
    // applies.
    if(bytes && byte_used.count(variable) != 0)
    {
      const auto e_bytes = pointer_offset_size(
        to_array_type(ws.front().s_it->ssa_lhs.type()).element_type(), ns);
      bool sized = e_bytes.has_value() && *e_bytes > 0;
      for(const auto &aw : decomposed)
        if(aw.bytes && aw.length.is_nil())
        {
          const auto s = pointer_offset_size(aw.value.type(), ns);
          sized = sized && s.has_value() && *s > 0;
        }
      // a read of non-constant size (memcpy of n bytes) has no byte count
      for(const auto &t : byte_read_types[variable])
      {
        const auto s = pointer_offset_size(t, ns);
        sized = sized && s.has_value() && *s > 0;
      }
      if(!sized)
      {
        if(explain)
          std::cerr << "ARRAY_WHY " << variable
                    << " declined: byte-wise, a size is unknown\n";
        continue;
      }
      if(explain)
        std::cerr << "ARRAY_WHY " << variable << " ACCEPTED: byte-wise, "
                  << decomposed.size() << " writes (no cost model)\n";
      array_rf_writes.emplace(variable, std::move(decomposed));
      array_rf_default.emplace(variable, initial.value());
      array_rf_bytewise.insert(variable);
      continue;
    }

    // Cost model. The chain amortises over reads and wins on a narrow object
    // read often; the nested selection wins on a wide object written rarely.
    // Require a clear margin, so a formula is not perturbed for little.
    const typet &t = ws.front().s_it->ssa_lhs.type();
    const auto array_bits = pointer_offset_bits(t, ns);
    const auto elem_bits = pointer_offset_bits(to_array_type(t).element_type(), ns);
    if(!elem_bits.has_value() || *elem_bits <= 0)
    {
      if(explain)
        std::cerr << "ARRAY_WHY " << variable
                  << " declined: element size unknown\n";
      continue;
    }
    // Of symbolic size, the chain is a chain of whole arrays, which only the
    // array theory can carry: never cheaper than selecting the element.
    if(!array_bits.has_value())
    {
      if(explain)
        std::cerr << "ARRAY_WHY " << variable << " ACCEPTED: symbolic size\n";
      array_rf_writes.emplace(variable, std::move(decomposed));
      array_rf_default.emplace(variable, initial.value());
      continue;
    }
    const double W = static_cast<double>(ws.size());
    const double Rd =
      reads.count(variable) ? static_cast<double>(reads.at(variable).size()) : 0;
    const double R = static_cast<double>(rounds);
    const double index_bits = 32;
    const double chain_cost = (W + Rd) * R * static_cast<double>(array_bits->to_long());
    // a read at round r sees the writes of every earlier round too, so the
    // selection is W*R deep on average half the time
    const double rf_cost =
      Rd * R * (W * R / 2.0) * (static_cast<double>(elem_bits->to_long()) + index_bits);
    if(rf_cost <= 0 || chain_cost < 2.0 * rf_cost)
    {
      if(explain)
        std::cerr << "ARRAY_WHY " << variable
                  << " declined by the cost model: chain=" << chain_cost
                  << " selection=" << rf_cost << " ratio="
                  << (rf_cost > 0 ? chain_cost / rf_cost : 0)
                  << " (W=" << W << " reads=" << Rd << " array_bits="
                  << array_bits->to_long() << ")\n";
      continue;
    }

    if(explain)
      std::cerr << "ARRAY_WHY " << variable << " ACCEPTED: chain=" << chain_cost
                << " selection=" << rf_cost << " ratio=" << chain_cost / rf_cost
                << "\n";
    array_rf_writes.emplace(variable, std::move(decomposed));
    array_rf_default.emplace(variable, initial.value());
  }
}

void lazy_pot::create_array_rf_constraints(symex_target_equationt &equation)
{
  if(array_rf_writes.empty())
    return;

  // position of an event in the schedule chain, for the "writes before this
  // read" test; the same lexicographic order the chain is sorted by
  const auto before = [](std::size_t ra, const shared_event &a,
                         std::size_t rb, const shared_event &b) {
    return std::make_tuple(ra, a.thread, a.label, a.num) <
           std::make_tuple(rb, b.thread, b.label, b.num);
  };

  auto &fresh = array_rf_fresh;
  auto &replacement = array_rf_replacement;

  std::set<irep_idt> variables;
  for(const auto &entry : array_rf_writes)
    variables.insert(entry.first);
  const auto copy_of = own_version_copies(equation, variables);

  // The steps before the first spawn: main's prologue, while no other thread
  // exists. Every thread is spawned after all of it in main's program order,
  // so a read in a spawned thread, or in main after the spawn, comes after
  // every prologue write in any schedule: no round order is needed between
  // them, only whether the write ran at all.
  std::set<const SSA_stept *> prologue;
  for(const auto &step : equation.SSA_steps)
  {
    if(step.is_spawn())
      break;
    prologue.insert(&step);
  }

  for(const auto &entry : array_rf_writes)
  {
    const irep_idt &variable = entry.first;
    const auto &ws = writes.at(variable);
    const exprt &dflt = array_rf_default.at(variable);
    const typet elem_type = to_array_type(
      ws.front().s_it->ssa_lhs.type()).element_type();

    std::map<irep_idt, const shared_event *> read_of;
    if(reads.count(variable))
      for(const auto &r : reads.at(variable))
        read_of.emplace(to_symbol_expr(r.s_it->ssa_lhs).get_identifier(), &r);

    // The writes of the prologue, in program order. Every thread is spawned
    // after the whole prologue, so a read outside it comes after all of them
    // in any schedule: it folds them once, on whether they ran in any round,
    // instead of once per (write round, read round).
    const auto prologue_writes = [&]() {
      std::vector<std::size_t> pre;
      for(std::size_t wi = 0; wi < entry.second.size(); ++wi)
        if(prologue.count(&*ws[entry.second[wi].event].s_it) != 0)
          pre.push_back(wi);
      std::sort(pre.begin(), pre.end(), [&](std::size_t a, std::size_t b) {
        const auto &ea = ws[entry.second[a].event];
        const auto &eb = ws[entry.second[b].event];
        return std::tie(ea.label, ea.num) < std::tie(eb.label, eb.num);
      });
      return pre;
    };
    // The write `aw` ran, in some round.
    const auto ran_in_some_round = [&](const array_writet &aw) -> exprt {
      exprt::operandst ran;
      for(std::size_t wr = 1; wr <= rounds; ++wr)
        ran.push_back(create_exec_symbol(
          ws[aw.event].label, ws[aw.event].num, ws[aw.event].thread, wr));
      return disjunction(ran);
    };
    // The (write, round of the write) pairs that come before the read `rdev`
    // in its round `round`, in increasing schedule position, leaving out the
    // prologue writes if they are folded separately.
    //
    // The write that wins is the LAST one before the read in schedule order,
    // so the candidates have to be folded in increasing position -- the one
    // wrapped last ends up outermost and takes priority. Folding them in any
    // other order silently elects the wrong write: with the writes walked
    // backwards and the rounds forwards, the outermost became the FIRST write
    // at the LAST round, i.e. the zero initialiser, which forced every read
    // to 0 and proved away a reachable violation.
    using positiont = std::tuple<std::size_t, unsigned, unsigned, unsigned>;
    const auto candidates_before = [&](
      const shared_event &rdev, std::size_t round, bool skip_prologue) {
      std::vector<std::pair<positiont, std::size_t>> candidates;
      for(std::size_t wi = 0; wi < entry.second.size(); ++wi)
      {
        const auto &aw = entry.second[wi];
        if(skip_prologue && prologue.count(&*ws[aw.event].s_it) != 0)
          continue;
        for(std::size_t wr = 1; wr <= rounds; ++wr)
        {
          if(!before(wr, ws[aw.event], round, rdev))
            continue;
          candidates.emplace_back(
            std::make_tuple(
              wr, ws[aw.event].thread, ws[aw.event].label, ws[aw.event].num),
            wi);
        }
      }
      std::sort(candidates.begin(), candidates.end());
      return candidates;
    };

    // --array-rf-bytes: a byte-wise object is answered byte by byte. A read of
    // type T at byte offset o is the bytes o, ..., o+|T|-1 assembled little
    // endian, and byte p holds the value of the last write before the read,
    // in schedule order, whose bytes cover p; else the initial contents.
    // A write a[i] = v covers [i*E, i*E+E), a byte update of v at offset q
    // covers [q, q+|v|), a whole-array write covers every byte. (Proved: the
    // cascade equals applying the writes in order -- iekke-proofs/
    // ByteCascade.lean; the formulas below are checked against SMT array
    // semantics by iekke-proofs/zcheck_bytes.py.)
    const bool bytewise = array_rf_bytewise.count(variable) != 0;
    // Offsets are computed in the index type of the object, as the lowering of
    // byte operations does: a 64-bit offset under ILP32 meets 32-bit indices
    // in the array theory and the solver aborts.
    const typet offset_type =
      to_array_type(ws.front().s_it->ssa_lhs.type()).index_type();
    const unsignedbv_typet byte_type{8};
    const mp_integer element_bytes =
      bytewise ? *pointer_offset_size(elem_type, ns) : mp_integer{1};
    const exprt element_bytes_expr = from_integer(element_bytes, offset_type);
    const auto as_offset = [&](const exprt &e) {
      return typecast_exprt::conditional_cast(e, offset_type);
    };
    // byte at offset p of a whole-array value (nondet contents or a uniform
    // element value)
    const auto whole_byte = [&](const exprt &v, const exprt &p) -> exprt {
      const exprt in_elem = mod_exprt{p, element_bytes_expr};
      if(v.type().id() == ID_array)
        return make_byte_extract(
          index_exprt{v, typecast_exprt::conditional_cast(
            div_exprt{p, element_bytes_expr}, to_array_type(v.type()).index_type())},
          in_elem, byte_type);
      return make_byte_extract(
        typecast_exprt::conditional_cast(v, elem_type), in_elem, byte_type);
    };
    // where the write starts and how many bytes it covers
    const auto range_of = [&](const array_writet &aw)
      -> std::pair<exprt, mp_integer> {
      if(aw.bytes)
        return {as_offset(aw.offset), *pointer_offset_size(aw.value.type(), ns)};
      return {mult_exprt{as_offset(aw.index), element_bytes_expr}, element_bytes};
    };
    const auto byte_hits = [&](const array_writet &aw, exprt ran, const exprt &p)
      -> exprt {
      exprt matches = ran;
      if(!aw.whole_array && !aw.length.is_nil())
      {
        // a range write: [offset, offset + length), length an expression.
        // Written offset <= p and p - offset < length, the difference taken
        // in the unsigned type of the same width: once offset <= p it lies in
        // [0, 2^w), so it is exact, where offset + length could wrap.
        const exprt lo = as_offset(aw.offset);
        const unsignedbv_typet width{
          to_bitvector_type(offset_type).get_width()};
        matches = and_exprt{
          matches,
          binary_relation_exprt{lo, ID_le, p},
          binary_relation_exprt{
            typecast_exprt::conditional_cast(minus_exprt{p, lo}, width),
            ID_lt,
            typecast_exprt::conditional_cast(aw.length, width)}};
      }
      else if(!aw.whole_array)
      {
        const auto r = range_of(aw);
        matches = and_exprt{
          matches,
          binary_relation_exprt{r.first, ID_le, p},
          binary_relation_exprt{
            p, ID_lt, plus_exprt{r.first, from_integer(r.second, offset_type)}}};
      }
      if(!aw.condition.is_true())
        matches = and_exprt{matches, aw.condition};
      return matches;
    };
    const auto byte_value = [&](const array_writet &aw, const exprt &p) -> exprt {
      if(aw.whole_array)
        return whole_byte(aw.value, p);
      if(!aw.length.is_nil())
        return typecast_exprt::conditional_cast(aw.value, byte_type);
      const auto r = range_of(aw);
      const exprt v = aw.bytes
        ? aw.value
        : static_cast<exprt>(typecast_exprt::conditional_cast(aw.value, elem_type));
      return make_byte_extract(v, minus_exprt{p, r.first}, byte_type);
    };

    // the byte range a write covers, when offset and length are constants
    std::map<const array_writet *, std::optional<std::pair<mp_integer, mp_integer>>>
      constant_ranges;
    const auto constant_range = [&](const array_writet &aw)
      -> std::optional<std::pair<mp_integer, mp_integer>> {
      const auto cached = constant_ranges.find(&aw);
      if(cached != constant_ranges.end())
        return cached->second;
      std::optional<std::pair<mp_integer, mp_integer>> result;
      if(!aw.length.is_nil())
      {
        const auto lo =
          numeric_cast<mp_integer>(simplify_expr(as_offset(aw.offset), ns));
        const auto len = numeric_cast<mp_integer>(simplify_expr(aw.length, ns));
        if(lo.has_value() && len.has_value())
          result = std::make_pair(*lo, *len);
      }
      else
      {
        const auto r = range_of(aw);
        const auto lo = numeric_cast<mp_integer>(simplify_expr(r.first, ns));
        if(lo.has_value())
          result = std::make_pair(*lo, r.second);
      }
      constant_ranges.emplace(&aw, result);
      return result;
    };

    // a read of \p rtype at byte offset \p roff of version \p id
    const auto byte_read = [&](const irep_idt &id, const shared_event &rdev,
                               const exprt &roff, const typet &rtype) -> exprt {
      const auto key =
        std::make_pair(id, "bytes:" + roff.pretty() + ":" + rtype.pretty());
      auto it = replacement.find(key);
      if(it != replacement.end())
        return it->second;
      const ssa_exprt elt{symbol_exprt{
        "arf_" + id2string(id) + "_" + std::to_string(fresh++), rtype}};
      const mp_integer n = *pointer_offset_size(rtype, ns);
      // Static disjointness: where the byte's offset and the write's range
      // are constants, the write's hit condition (byte_hits, the one the
      // cascade below uses) is decided by simplification; a write whose hit
      // condition is false is left out of the byte's cascade.
      //
      // With both constant, the hit condition is decided here by arithmetic
      // when every value involved, the end of the write included, fits the
      // offset type, so that arithmetic in the offset type agrees with the
      // integers; otherwise it is still decided by simplifying the condition.
      // Was: always by simplifying, one condition built and simplified per
      // read, byte and write -- on the ldv-linux drivers millions of them for
      // a single heap block (spi-tegra20-slink, 234 writes, 3418 reads).
      const exprt roff_simplified = simplify_expr(roff, ns);
      const bool roff_constant = roff_simplified.is_constant();
      const auto roff_value = numeric_cast<mp_integer>(roff_simplified);
      const std::size_t offset_width =
        to_bitvector_type(offset_type).get_width();
      const mp_integer offset_min = offset_type.id() == ID_signedbv
                                      ? -power(2, offset_width - 1)
                                      : mp_integer{0};
      const mp_integer offset_max =
        (offset_type.id() == ID_signedbv ? power(2, offset_width - 1)
                                         : power(2, offset_width)) -
        1;
      const auto fits = [&](const mp_integer &v) {
        return v >= offset_min && v <= offset_max;
      };
      const auto misses = [&](const array_writet &aw, const mp_integer &b) {
        if(!roff_constant || aw.whole_array || !constant_range(aw).has_value())
          return false;
        const auto range = *constant_range(aw);
        if(roff_value.has_value())
        {
          const mp_integer at = *roff_value + b;
          const mp_integer end = range.first + range.second;
          if(range.second >= 0 && fits(at) && fits(range.first) && fits(end))
            return at < range.first || at >= end;
        }
        const exprt p = plus_exprt{roff, from_integer(b, offset_type)};
        return simplify_expr(byte_hits(aw, true_exprt{}, p), ns).is_false();
      };
      const bool after_prologue = prologue.count(&*rdev.s_it) == 0;
      const std::vector<std::size_t> pre =
        after_prologue ? prologue_writes() : std::vector<std::size_t>{};
      for(std::size_t round = 1; round <= rounds; ++round)
      {
        const auto candidates = candidates_before(rdev, round, after_prologue);

        exprt::operandst byte_ops;
        for(mp_integer b = 0; b < n; ++b)
        {
          const exprt p = plus_exprt{roff, from_integer(b, offset_type)};
          exprt selected = whole_byte(dflt, p);
          for(const std::size_t wi : pre)
          {
            const auto &aw = entry.second[wi];
            if(misses(aw, b))
              continue;
            selected = if_exprt{
              byte_hits(aw, ran_in_some_round(aw), p), byte_value(aw, p), selected};
          }
          for(const auto &candidate : candidates)
          {
            const auto &aw = entry.second[candidate.second];
            if(misses(aw, b))
              continue;
            const symbol_exprt wexec = create_exec_symbol(
              ws[aw.event].label, ws[aw.event].num, ws[aw.event].thread,
              std::get<0>(candidate.first));
            selected = if_exprt{byte_hits(aw, wexec, p), byte_value(aw, p), selected};
          }
          byte_ops.push_back(selected);
        }
        const array_exprt assembled{
          std::move(byte_ops),
          array_typet{byte_type, from_integer(n, size_type())}};
        const symbol_exprt rexec =
          create_exec_symbol(rdev.label, rdev.num, rdev.thread, round);
        equation.constraint(
          implies_exprt{
            rexec,
            equal_exprt{elt, make_byte_extract(assembled, from_integer(0, offset_type), rtype)}},
          "array read-from (bytes) " + id2string(variable),
          rdev.s_it->source);
      }
      it = replacement.emplace(key, elt).first;
      return it->second;
    };

    // Whether a subtree holds a read of this variable: the rewrite below
    // descends only into such subtrees (see subtree_has). Addresses are not
    // reads.
    subtree_memot holds_target;
    const auto reads_variable = [&](const exprt &expr) {
      return (expr.id() == ID_index ||
              (bytewise && expr.id() == ID_byte_extract_little_endian)) &&
             !expr.operands().empty() && expr.operands()[0].id() == ID_symbol &&
             narrowing_base(expr.operands()[0]) == variable;
    };
    const auto is_address = [](const exprt &expr) {
      return expr.id() == ID_address_of;
    };
    const auto contains = [&](const exprt &expr) {
      return subtree_has(expr, reads_variable, is_address, holds_target);
    };

    // rewrite every index(V#k, j) into a fresh scalar, and say what it holds
    std::function<void(exprt &)> rewrite = [&](exprt &expr) {
      if(expr.id() == ID_address_of)
        return;
      if(!contains(as_const(expr)))
        return;

      if(
        bytewise && expr.id() == ID_byte_extract_little_endian &&
        to_byte_extract_expr(expr).op().id() == ID_symbol &&
        narrowing_base(to_byte_extract_expr(expr).op()) == variable)
      {
        const irep_idt id = copied_from(
          copy_of,
          to_symbol_expr(to_byte_extract_expr(expr).op()).get_identifier());
        const auto rd = read_of.find(id);
        if(rd != read_of.end())
        {
          exprt roff = to_byte_extract_expr(expr).offset();
          rewrite(roff);
          expr = byte_read(id, *rd->second, as_offset(roff), expr.type());
          return;
        }
      }

      if(
        bytewise && expr.id() == ID_index &&
        expr.operands()[0].id() == ID_symbol &&
        narrowing_base(expr.operands()[0]) == variable)
      {
        const irep_idt id = copied_from(
          copy_of, to_symbol_expr(expr.operands()[0]).get_identifier());
        const auto rd = read_of.find(id);
        if(rd != read_of.end())
        {
          exprt index = expr.operands()[1];
          rewrite(index);
          expr = byte_read(
            id, *rd->second, mult_exprt{as_offset(index), element_bytes_expr}, elem_type);
          return;
        }
      }

      if(expr.id() == ID_index && expr.operands()[0].id() == ID_symbol &&
         narrowing_base(expr.operands()[0]) == variable)
      {
        const irep_idt id = copied_from(
          copy_of, to_symbol_expr(expr.operands()[0]).get_identifier());
        const auto rd = read_of.find(id);
        if(rd != read_of.end())
        {
          exprt index = expr.operands()[1];
          rewrite(index);
          const auto key =
            std::make_pair(id, index.pretty());
          auto it = replacement.find(key);
          if(it == replacement.end())
          {
            // An ssa_exprt, not a plain symbol: this replaces an
            // index() inside existing SSA steps, and build_goto_trace
            // asserts that what it finds there carries ID_C_SSA_symbol.
            // A bare symbol_exprt passes every solver path and then
            // aborts in "Building error trace" -- so it only shows up
            // when a counterexample is actually built, which is exactly
            // what --graphml-witness does and what no SUCCESSFUL run
            // ever reaches.
            const ssa_exprt elt{symbol_exprt{
              "arf_" + id2string(id) + "_" + std::to_string(fresh++),
              elem_type}};

            const auto element_of = [&](const exprt &v) -> exprt {
              if(v.type().id() == ID_array)
                return index_exprt{v, typecast_exprt::conditional_cast(
                  index, to_array_type(v.type()).index_type())};
              return typecast_exprt::conditional_cast(v, elem_type);
            };
            const auto value_of = [&](const array_writet &aw) -> exprt {
              return aw.havoc
                ? element_of(aw.value)
                : typecast_exprt::conditional_cast(aw.value, elem_type);
            };
            const auto hits = [&](const array_writet &aw, exprt ran) -> exprt {
              exprt matches = aw.whole_array
                ? ran
                : static_cast<exprt>(and_exprt{
                    ran,
                    equal_exprt{
                      typecast_exprt::conditional_cast(aw.index, index.type()),
                      index}});
              if(!aw.condition.is_true())
                matches = and_exprt{matches, aw.condition};
              return matches;
            };

            // After the prologue, its writes are folded once, in program
            // order, on whether they ran in any round. Selecting them per
            // (write round, read round) as below cost rounds^2 copies of the
            // same choice: on weaver/array-eq-symm, whose arrays are written
            // only by main's init loops, the read-from was 87% of 14.8M
            // clauses at u64 and the formula did not fit in 15GB at u256.
            const bool after_prologue =
              prologue.count(&*rd->second->s_it) == 0;
            exprt start = element_of(dflt);
            if(after_prologue)
              for(const std::size_t wi : prologue_writes())
              {
                const auto &aw = entry.second[wi];
                start = if_exprt{hits(aw, ran_in_some_round(aw)), value_of(aw), start};
              }

            for(std::size_t round = 1; round <= rounds; ++round)
            {
              // last write before the read wins; see candidates_before
              const auto candidates =
                candidates_before(*rd->second, round, after_prologue);

              exprt selected = start;
              for(const auto &candidate : candidates)
              {
                const auto &aw = entry.second[candidate.second];
                const symbol_exprt wexec = create_exec_symbol(
                  ws[aw.event].label, ws[aw.event].num, ws[aw.event].thread,
                  std::get<0>(candidate.first));
                selected = if_exprt{hits(aw, wexec), value_of(aw), selected};
              }
              const symbol_exprt rexec = create_exec_symbol(
                rd->second->label, rd->second->num, rd->second->thread, round);
              equation.constraint(
                implies_exprt{rexec, equal_exprt{elt, selected}},
                "array read-from " + id2string(variable),
                rd->second->s_it->source);
            }

            it = replacement.emplace(key, elt).first;
          }
          expr = it->second;
          return;
        }
      }

      for(auto &op : expr.operands())
        rewrite(op);
    };

    for(auto &step : equation.SSA_steps)
    {
      if(step.ignore)
        continue;
      // the assignments that build the array are no longer needed: nothing
      // reads the array value any more
      if(step.is_assignment() && !step.ssa_lhs.is_nil() &&
         narrowing_base(step.ssa_lhs) == variable)
      {
        step.ignore = true;
        continue;
      }
      if(!step.ssa_rhs.is_nil())
        rewrite(step.ssa_rhs);
      if(!step.cond_expr.is_nil())
        rewrite(step.cond_expr);
      if(!step.guard.is_nil())
        rewrite(step.guard);
    }
  }
}
