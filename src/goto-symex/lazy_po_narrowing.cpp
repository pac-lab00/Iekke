/// \file
/// lazy_po: narrowing of shared objects to the bytes they are read through (--narrow-shared), and of the write chains to the bits their values take

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

namespace
{
/// What the equation does to one shared object, as far as narrowing cares.
struct object_usaget
{
  bool read_seen = false;
  bool unusable = false;  ///< a use that would observe bits outside the range
  std::size_t lo = 0;
  std::size_t hi = 0;

  void read(std::size_t offset_bits, std::size_t width_bits)
  {
    if(!read_seen)
    {
      lo = offset_bits;
      hi = offset_bits + width_bits;
      read_seen = true;
    }
    else
    {
      lo = std::min(lo, offset_bits);
      hi = std::max(hi, offset_bits + width_bits);
    }
  }
};
} // namespace

/// Can an assignment producing `base` with this right-hand side be narrowed?
/// Only shapes whose bits outside the read range are the object's own previous
/// bits, fresh nondeterminism, or a constant -- none of which a read can
/// distinguish once the bare-use check below has passed.
static bool narrowing_rhs_ok(const exprt &expr, const irep_idt &base)
{
  if(expr.id() == ID_nondet_symbol || expr.is_constant())
    return true;
  if(expr.id() == ID_symbol)
    return narrowing_base(expr) == base; // a copy between versions
  if(
    expr.id() == ID_byte_update_little_endian ||
    expr.id() == ID_byte_update_big_endian)
  {
    return narrowing_rhs_ok(expr.operands()[0], base);
  }
  if(expr.id() == ID_if) // a phi over two acceptable versions
  {
    return narrowing_rhs_ok(expr.operands()[1], base) &&
           narrowing_rhs_ok(expr.operands()[2], base);
  }
  if(expr.id() == ID_typecast)
    return narrowing_rhs_ok(expr.operands()[0], base);
  return false;
}

static void narrowing_scan(
  const exprt &,
  const namespacet &,
  const std::set<irep_idt> &,
  std::map<irep_idt, object_usaget> &);

/// Walk a right-hand side narrowing_rhs_ok accepted. Its shape is understood,
/// so the object's own symbols in it are not bare uses; the values written and
/// the phi conditions still go through the general scan.
static void narrowing_scan_accepted(
  const exprt &expr,
  const irep_idt &base,
  const namespacet &ns,
  const std::set<irep_idt> &tracked,
  std::map<irep_idt, object_usaget> &usage)
{
  if(expr.id() == ID_if)
  {
    narrowing_scan(expr.operands()[0], ns, tracked, usage);
    narrowing_scan_accepted(expr.operands()[1], base, ns, tracked, usage);
    narrowing_scan_accepted(expr.operands()[2], base, ns, tracked, usage);
  }
  else if(expr.id() == ID_typecast)
  {
    narrowing_scan_accepted(expr.operands()[0], base, ns, tracked, usage);
  }
  else if(
    expr.id() == ID_byte_update_little_endian ||
    expr.id() == ID_byte_update_big_endian)
  {
    // a write does not widen the chain -- see the file comment
    narrowing_scan_accepted(expr.operands()[0], base, ns, tracked, usage);
    narrowing_scan(expr.operands()[1], ns, tracked, usage);
    narrowing_scan(expr.operands()[2], ns, tracked, usage);
  }
  // symbol / nondet_symbol / constant: nothing to record
}

/// Record the byte ranges reads take out of each tracked object, and flag any
/// use that would observe it some other way.
static void narrowing_scan(
  const exprt &expr,
  const namespacet &ns,
  const std::set<irep_idt> &tracked,
  std::map<irep_idt, object_usaget> &usage)
{
  // Taking an object's address does not observe its value; by the time symex
  // has produced this equation every dereference has already been resolved
  // into the byte_extract/byte_update forms handled here. field_sensitivityt
  // skips ID_address_of for the same reason.
  if(expr.id() == ID_address_of)
    return;

  const bool is_extract = expr.id() == ID_byte_extract_little_endian ||
                          expr.id() == ID_byte_extract_big_endian;
  const bool is_update = expr.id() == ID_byte_update_little_endian ||
                         expr.id() == ID_byte_update_big_endian;

  if(is_extract || is_update)
  {
    const irep_idt base = narrowing_base(expr.operands()[0]);
    if(!base.empty() && tracked.count(base) != 0)
    {
      auto &u = usage[base];
      const auto offset = numeric_cast<mp_integer>(expr.operands()[1]);
      const typet &accessed_type =
        is_extract ? expr.type() : expr.operands()[2].type();
      const auto width = pointer_offset_bits(accessed_type, ns);
      if(!offset.has_value() || !width.has_value() || *offset < 0)
        u.unusable = true;
      else if(is_extract)
      {
        u.read(
          numeric_cast_v<std::size_t>(*offset) * 8,
          numeric_cast_v<std::size_t>(*width));
      }

      // operand 0 is accounted for; the rest can still hold other uses
      for(std::size_t i = 1; i < expr.operands().size(); ++i)
        narrowing_scan(expr.operands()[i], ns, tracked, usage);
      return;
    }
  }

  const irep_idt base = narrowing_base(expr);
  if(!base.empty() && tracked.count(base) != 0)
  {
    // a bare occurrence: a whole-object copy, comparison or argument. The
    // chain has to keep every bit this could observe.
    usage[base].unusable = true;
  }

  for(const auto &op : expr.operands())
    narrowing_scan(op, ns, tracked, usage);
}

void lazy_pot::compute_narrowings(const symex_target_equationt &equation)
{
  narrowings.clear();
  if(!narrow_shared)
    return;

  std::set<irep_idt> tracked;
  for(const auto &v : global_variables)
    if(writes.count(v) != 0)
      tracked.insert(v);
  // compute_private_objects has already moved the single-thread objects out of
  // global_variables, and they are narrowed on the same terms
  for(const auto &v : private_objects)
    if(private_writes.count(v) != 0)
      tracked.insert(v);
  if(tracked.empty())
    return;

  std::map<irep_idt, object_usaget> usage;
  for(const auto &step : equation.SSA_steps)
  {
    bool lhs_handled = false;
    if(!step.ssa_lhs.is_nil() && step.is_assignment())
    {
      const irep_idt lhs_base = narrowing_base(step.ssa_lhs);
      if(!lhs_base.empty() && tracked.count(lhs_base) != 0)
      {
        if(narrowing_rhs_ok(step.ssa_rhs, lhs_base))
        {
          narrowing_scan_accepted(step.ssa_rhs, lhs_base, ns, tracked, usage);
          lhs_handled = true;
        }
        else
          usage[lhs_base].unusable = true;
      }
    }

    if(!step.ssa_rhs.is_nil() && !lhs_handled)
      narrowing_scan(step.ssa_rhs, ns, tracked, usage);
    // for an assignment or a decl cond_expr is just `ssa_lhs == ssa_rhs`, so
    // scanning it would re-read the target as a bare use of itself
    if(!step.cond_expr.is_nil() && !step.is_assignment() && !step.is_decl())
      narrowing_scan(step.cond_expr, ns, tracked, usage);
    if(!step.guard.is_nil())
      narrowing_scan(step.guard, ns, tracked, usage);
  }

  for(const auto &v : tracked)
  {
    const auto it = usage.find(v);
    if(it == usage.end() || it->second.unusable || !it->second.read_seen)
      continue;
    const auto &ws = writes.count(v) != 0 ? writes.at(v) : private_writes.at(v);
    const auto full = pointer_offset_bits(ws.front().s_it->ssa_lhs.type(), ns);
    if(!full.has_value() || *full <= 0)
      continue;
    const std::size_t lo = it->second.lo;
    const std::size_t hi = it->second.hi;
    // byte_extract addresses bytes, so only a byte-aligned slice can be named
    if(lo % 8 != 0 || (hi - lo) % 8 != 0)
      continue;
    if(hi - lo >= numeric_cast_v<std::size_t>(*full))
      continue;
    narrowings.emplace(v, narrowingt{lo, hi - lo});
  }
}

exprt lazy_pot::narrowed_value(const irep_idt &variable, const exprt &value) const
{
  const auto v = value_narrowings.find(variable);
  if(v != value_narrowings.end())
    return typecast_exprt{value, v->second};
  const auto it = narrowings.find(variable);
  if(it == narrowings.end())
    return value;
  return make_byte_extract(
    value,
    from_integer(it->second.offset_bits / 8, c_index_type()),
    unsignedbv_typet(it->second.width_bits));
}

typet lazy_pot::narrowed_type(const irep_idt &variable, const typet &type) const
{
  const auto v = value_narrowings.find(variable);
  if(v != value_narrowings.end())
    return v->second;
  const auto it = narrowings.find(variable);
  if(it == narrowings.end())
    return type;
  return unsignedbv_typet(it->second.width_bits);
}

/// Value narrowing: the write chain of a shared bit-vector object carries only
/// the bits its values can take. The ranges come from an interval analysis of
/// the unrolled formula that follows the (round, thread, label) order of the
/// chains; three bounds are intersected:
///
/// - Whole run: the join of every value written, per group of mutually
///   dependent objects. Each write of the unrolled formula fires at most once,
///   so a chain of values inside a group passes through at most as many writes
///   as the group has; iterating that often covers it, without widening.
/// - Round by round: in round r a read of thread t sees a value from a round
///   before r, from a thread before t in round r, or from t itself. Inside a
///   round no value flows back from a later thread, so only t's own writes are
///   iterated. Round r's links hold the values written up to the end of r.
/// - Counting writes: each thread performs its writes in program order, each
///   at most once (one on a path not taken is skipped). Over the states "how
///   many of its writes each thread has passed", the values at a state join
///   those one step before it, with or without that write; every execution
///   walks such a path. This bounds counters across all rounds.
///
/// A value enters the chain truncated to the round's width and every read is
/// stated to fit the widest one (create_write_constraints), so the low bits
/// the read constraints compare fix the whole value. Thread-local code keeps
/// its full width. LAZYPO_NO_NARROW_VALUES turns this off.
void lazy_pot::compute_value_narrowings(const symex_target_equationt &equation)
{
  value_narrowings.clear();
  value_round_types.clear();
  if(getenv("LAZYPO_NO_NARROW_VALUES") != nullptr)
    return;

  struct intervalt
  {
    mp_integer lo, hi;
    bool bottom = true;   // no value yet
    bool unknown = false; // not a number (pointer, struct, ...)
  };
  const auto type_range = [](const typet &t) -> std::optional<intervalt> {
    if(t.id() == ID_bool)
      return intervalt{0, 1, false};
    if(t.id() == ID_c_bool || t.id() == ID_unsignedbv)
    {
      const auto w = to_bitvector_type(t).get_width();
      return intervalt{0, power(2, w) - 1, false};
    }
    if(t.id() == ID_signedbv || t.id() == ID_c_enum)
    {
      const auto w = to_bitvector_type(
        t.id() == ID_c_enum ? to_c_enum_type(t).underlying_type() : t)
        .get_width();
      return intervalt{-power(2, w - 1), power(2, w - 1) - 1, false};
    }
    return {};
  };
  const auto join = [](intervalt &a, const intervalt &b) {
    if(b.bottom)
      return false;
    if(a.bottom)
    {
      a = b;
      return true;
    }
    bool changed = false;
    if(b.lo < a.lo)
      a.lo = b.lo, changed = true;
    if(b.hi > a.hi)
      a.hi = b.hi, changed = true;
    return changed;
  };
  const auto meet = [](intervalt &a, const intervalt &b) {
    if(a.bottom || b.bottom)
      return;
    a.lo = std::max(a.lo, b.lo);
    a.hi = std::min(a.hi, b.hi);
  };
  const auto bits_for = [](const intervalt &v) {
    std::size_t b = 1;
    if(v.lo >= 0)
      while(power(2, b) - 1 < v.hi)
        ++b;
    else
      while(-power(2, b - 1) > v.lo || power(2, b - 1) - 1 < v.hi)
        ++b;
    return b;
  };

  // local SSA definitions, and which shared object each read symbol reads
  std::unordered_map<irep_idt, const exprt *> def;
  for(const auto &step : equation.SSA_steps)
    if(step.is_assignment())
      def[step.ssa_lhs.get_identifier()] = &step.ssa_rhs;
  std::unordered_map<irep_idt, irep_idt> read_of;
  for(const auto &entry : reads)
    for(const auto &r : entry.second)
      read_of[r.s_it->ssa_lhs.get_identifier()] = entry.first;

  // The value a read can return is `value` of its object; locals follow
  // their definitions. Whatever may leave its type's range takes the range.
  std::map<irep_idt, intervalt> value;
  std::unordered_map<irep_idt, intervalt> memo;
  std::function<intervalt(const exprt &, unsigned)> eval;
  eval = [&](const exprt &e, unsigned depth) -> intervalt {
    const auto range = type_range(e.type());
    if(!range)
      return intervalt{0, 0, false, true};
    const intervalt top = *range;
    const auto clamp = [&](const intervalt &v) {
      if(v.bottom)
        return v;
      if(v.unknown || v.lo < top.lo || v.hi > top.hi)
        return top;
      return v;
    };
    if(depth > 200)
      return top;
    if(e.is_constant())
    {
      if(e.type().id() == ID_bool)
        return e.is_true() ? intervalt{1, 1, false} : intervalt{0, 0, false};
      const auto v = numeric_cast<mp_integer>(to_constant_expr(e));
      return v ? intervalt{*v, *v, false} : top;
    }
    if(e.id() == ID_symbol)
    {
      const irep_idt &id = to_symbol_expr(e).get_identifier();
      const auto r = read_of.find(id);
      if(r != read_of.end())
      {
        if(writes.count(r->second) == 0)
          return top;
        const auto v = value.find(r->second);
        return v == value.end() ? intervalt{} : clamp(v->second);
      }
      const auto m = memo.find(id);
      if(m != memo.end())
        return m->second;
      const auto d = def.find(id);
      const intervalt v = d == def.end() ? top : clamp(eval(*d->second, depth + 1));
      memo[id] = v;
      return v;
    }
    if(
      e.id() == ID_equal || e.id() == ID_notequal || e.id() == ID_lt ||
      e.id() == ID_le || e.id() == ID_gt || e.id() == ID_ge ||
      e.id() == ID_and || e.id() == ID_or || e.id() == ID_not)
    {
      return intervalt{0, 1, false};
    }
    if(e.id() == ID_if)
    {
      intervalt v = clamp(eval(to_if_expr(e).true_case(), depth + 1));
      join(v, clamp(eval(to_if_expr(e).false_case(), depth + 1)));
      return v;
    }
    if(e.id() == ID_typecast)
    {
      const exprt &op = to_typecast_expr(e).op();
      if(op.type().id() == ID_bool)
        return intervalt{0, 1, false};
      return clamp(eval(op, depth + 1));
    }
    if(e.id() == ID_plus || e.id() == ID_minus || e.id() == ID_mult)
    {
      intervalt v = clamp(eval(e.operands()[0], depth + 1));
      for(std::size_t k = 1; k < e.operands().size() && !v.bottom; ++k)
      {
        const intervalt b = clamp(eval(e.operands()[k], depth + 1));
        if(b.bottom)
          return b;
        if(e.id() == ID_plus)
          v = intervalt{v.lo + b.lo, v.hi + b.hi, false};
        else if(e.id() == ID_minus)
          v = intervalt{v.lo - b.hi, v.hi - b.lo, false};
        else
        {
          const mp_integer c[] = {
            v.lo * b.lo, v.lo * b.hi, v.hi * b.lo, v.hi * b.hi};
          v = intervalt{
            *std::min_element(c, c + 4), *std::max_element(c, c + 4), false};
        }
      }
      return clamp(v);
    }
    if(e.id() == ID_bitand && top.lo >= 0)
    {
      // a non-negative operand bounds an unsigned result
      intervalt best = top;
      for(const auto &op : e.operands())
      {
        const intervalt b = eval(op, depth + 1);
        if(!b.bottom && !b.unknown && b.lo >= 0 && b.hi < best.hi)
          best = intervalt{0, b.hi, false};
      }
      return best;
    }
    return top;
  };
  // the value a write puts in the chain
  const auto written = [&](const shared_event &w) -> std::optional<intervalt> {
    const auto range = type_range(w.s_it->ssa_lhs.type());
    if(!range)
      return {};
    const auto d = def.find(w.s_it->ssa_lhs.get_identifier());
    intervalt x = d == def.end() ? *range : eval(*d->second, 0);
    if(x.unknown)
      x = *range;
    return x;
  };

  // 1. Whole run, per group of mutually dependent objects (Tarjan, the groups
  // come out dependencies first).
  std::unordered_map<irep_idt, std::set<irep_idt>> reads_below;
  std::unordered_set<irep_idt> walking;
  bool cycle = false;
  std::function<const std::set<irep_idt> &(const irep_idt &)> reads_of_symbol;
  std::function<void(const exprt &, std::set<irep_idt> &)> collect;
  collect = [&](const exprt &e, std::set<irep_idt> &into) {
    if(e.id() == ID_symbol)
    {
      const auto &r = reads_of_symbol(to_symbol_expr(e).get_identifier());
      into.insert(r.begin(), r.end());
      return;
    }
    for(const auto &op : e.operands())
      collect(op, into);
  };
  reads_of_symbol = [&](const irep_idt &id) -> const std::set<irep_idt> & {
    const auto m = reads_below.find(id);
    if(m != reads_below.end())
    {
      // still being walked: definitions lead back to this symbol, and the
      // sets found meanwhile are incomplete (see below)
      if(walking.count(id) != 0)
        cycle = true;
      return m->second;
    }
    reads_below[id];
    walking.insert(id);
    std::set<irep_idt> found;
    const auto r = read_of.find(id);
    if(r != read_of.end())
      found.insert(r->second);
    else if(const auto d = def.find(id); d != def.end())
      collect(*d->second, found);
    walking.erase(id);
    return reads_below[id] = std::move(found);
  };
  std::map<irep_idt, std::set<irep_idt>> depends;
  for(const auto &entry : writes)
    for(const auto &w : entry.second)
    {
      const auto &r = reads_of_symbol(w.s_it->ssa_lhs.get_identifier());
      depends[entry.first].insert(r.begin(), r.end());
    }
  std::map<irep_idt, std::size_t> order, low;
  std::set<irep_idt> on_stack;
  std::vector<irep_idt> stack;
  std::vector<std::vector<irep_idt>> groups;
  std::function<void(const irep_idt &)> visit;
  visit = [&](const irep_idt &v) {
    order[v] = low[v] = order.size();
    stack.push_back(v);
    on_stack.insert(v);
    for(const auto &u : depends[v])
    {
      if(writes.count(u) == 0)
        continue;
      if(order.count(u) == 0)
      {
        visit(u);
        low[v] = std::min(low[v], low[u]);
      }
      else if(on_stack.count(u) != 0)
        low[v] = std::min(low[v], order[u]);
    }
    if(low[v] == order[v])
    {
      groups.emplace_back();
      irep_idt u;
      do
      {
        u = stack.back();
        stack.pop_back();
        on_stack.erase(u);
        groups.back().push_back(u);
      } while(u != v);
    }
  };
  for(const auto &entry : writes)
    if(order.count(entry.first) == 0)
      visit(entry.first);
  // With definitions in a cycle some dependency sets are incomplete, and
  // groups split on them could be evaluated before what they read: take all
  // objects as one group instead.
  if(cycle)
  {
    groups.assign(1, {});
    for(const auto &entry : writes)
      groups.front().push_back(entry.first);
  }
  // a group with more writes than this keeps its type ranges
  const std::size_t group_cap = 512;
  for(const auto &group : groups)
  {
    std::size_t group_writes = 0;
    for(const auto &v : group)
      group_writes += writes.at(v).size();
    if(group_writes > group_cap)
    {
      for(const auto &v : group)
        if(const auto range = type_range(writes.at(v).front().s_it->ssa_lhs.type()))
          value[v] = *range;
      continue;
    }
    for(std::size_t it = 0; it <= group_writes; ++it)
    {
      memo.clear();
      bool changed = false;
      for(const auto &v : group)
        for(const auto &w : writes.at(v))
          if(const auto x = written(w))
            changed |= join(value[v], *x);
      if(!changed)
        break;
    }
  }
  const std::map<irep_idt, intervalt> whole_run = value;

  // The chain starts from the value of the object's first write, whether or
  // not that write runs: every reader can see it from the start.
  std::map<irep_idt, intervalt> start;
  memo.clear();
  for(const auto &entry : writes)
    if(const auto x = written(entry.second.front()))
      start[entry.first] = x->bottom ? *type_range(entry.second.front().s_it->ssa_lhs.type()) : *x;

  std::map<std::size_t, std::vector<std::pair<irep_idt, const shared_event *>>>
    by_thread;
  for(const auto &entry : writes)
    for(const auto &w : entry.second)
      by_thread[w.thread].emplace_back(entry.first, &w);
  for(auto &t : by_thread)
    std::stable_sort(
      t.second.begin(), t.second.end(), [](const auto &a, const auto &b) {
        return a.second->label < b.second->label;
      });

  // 2. Round by round.
  std::vector<std::map<irep_idt, intervalt>> at_round_end(rounds + 1);
  std::map<irep_idt, intervalt> before = start; // up to the end of round r-1
  const std::size_t own_cap = 64;
  for(std::size_t r = 1; r <= rounds; ++r)
  {
    std::map<irep_idt, intervalt> visible = before;
    for(const auto &t : by_thread)
    {
      for(std::size_t it = 0; it <= std::min(t.second.size(), own_cap); ++it)
      {
        memo.clear();
        value = visible;
        bool changed = false;
        for(const auto &vw : t.second)
          if(auto x = written(*vw.second))
          {
            const auto g = whole_run.find(vw.first);
            if(g != whole_run.end())
              meet(*x, g->second);
            changed |= join(visible[vw.first], *x);
          }
        if(!changed)
          break;
        if(it == own_cap)
          for(const auto &vw : t.second)
            if(const auto range = type_range(vw.second->s_it->ssa_lhs.type()))
              visible[vw.first] = *range;
      }
    }
    before = visible;
    at_round_end[r] = visible;
  }

  // 3. Counting writes, when the states are few enough.
  std::map<irep_idt, intervalt> counted;
  {
    const std::size_t state_cap = 2000000;
    std::vector<const std::vector<std::pair<irep_idt, const shared_event *>> *> ts;
    std::vector<std::size_t> radix;
    std::size_t states = 1;
    const std::size_t objects = std::max<std::size_t>(writes.size(), 1);
    for(const auto &t : by_thread)
    {
      ts.push_back(&t.second);
      radix.push_back(t.second.size() + 1);
      states *= t.second.size() + 1;
      if(states * objects > state_cap)
        break;
    }
    if(states * objects <= state_cap)
    {
      std::vector<std::map<irep_idt, intervalt>> at(states);
      at[0] = start;
      for(std::size_t idx = 1; idx < states; ++idx)
      {
        std::size_t rest = idx, stride = 1;
        for(std::size_t k = 0; k < ts.size(); ++k)
        {
          const std::size_t passed = rest % radix[k];
          rest /= radix[k];
          if(passed != 0)
          {
            const std::size_t prev = idx - stride;
            for(const auto &kv : at[prev])
              join(at[idx][kv.first], kv.second);
            const auto &vw = (*ts[k])[passed - 1];
            memo.clear();
            value = at[prev];
            if(const auto x = written(*vw.second))
              join(at[idx][vw.first], *x);
          }
          stride *= radix[k];
        }
      }
      counted = std::move(at[states - 1]);
    }
  }

  for(const auto &entry : writes)
  {
    const typet &t = entry.second.front().s_it->ssa_lhs.type();
    if(t.id() != ID_signedbv && t.id() != ID_unsignedbv)
      continue;
    if(narrowings.count(entry.first) != 0)
      continue;
    if(std::any_of(
         entry.second.begin(), entry.second.end(),
         [&](const shared_event &w) { return w.s_it->ssa_lhs.type() != t; }))
    {
      continue;
    }
    const auto g = whole_run.find(entry.first);
    if(g == whole_run.end() || g->second.bottom || g->second.unknown)
      continue;
    intervalt v = g->second;
    if(const auto c = counted.find(entry.first); c != counted.end())
      meet(v, c->second);
    const std::size_t need = bits_for(v);
    if(need >= to_bitvector_type(t).get_width())
      continue;
    // every round has the final signedness, so extending a link from one
    // round to the next, or to the read's width, keeps its value
    const bool is_signed = v.lo < 0;
    const auto narrow = [&](std::size_t w) {
      return is_signed ? typet(signedbv_typet(w)) : typet(unsignedbv_typet(w));
    };
    std::vector<typet> per_round(rounds + 1, narrow(need));
    std::size_t width = 1;
    for(std::size_t r = 1; r < rounds; ++r)
    {
      intervalt w = v;
      if(const auto e = at_round_end[r].find(entry.first);
         e != at_round_end[r].end())
      {
        meet(w, e->second);
      }
      if(is_signed && w.lo >= 0)
        w.lo = -1; // count the sign bit
      width = std::min(std::max(width, bits_for(w)), need);
      per_round[r] = narrow(width);
    }
    value_narrowings.emplace(entry.first, narrow(need));
    value_round_types.emplace(entry.first, std::move(per_round));
  }
  if(!value_narrowings.empty())
    std::cerr << "Value narrowing: " << value_narrowings.size() << " objects\n";
}
