/*******************************************************************\

Module: Spin-loop reduction

\*******************************************************************/

/// \file
/// A thread waiting in a loop re-reads shared memory until it sees what it
/// waits for. An iteration in which the thread writes no memory and every
/// local of the looping function it assigns ends with the value it had when
/// the iteration began returns the thread to exactly the state it started
/// from: the iteration only read. Removing it from an interleaving leaves an
/// interleaving of the program that reaches the same states (the thread
/// waits at the loop head instead), so the reachable states, and with them
/// assertions, overflow checks and data races, are unchanged: the accesses
/// of a removed iteration are possible at the same point, from the same
/// state, in the iteration it repeats.
///
/// Every iteration of an instrumented loop must therefore change something:
/// at the loop head the pass copies the loop-written locals and a per-thread
/// count of memory writes, and on the back edge it assumes that the count or
/// one of the locals differs from its copy. The count is increased before
/// every assignment to anything but a local of the running function, in the
/// looping function and every function it may call. Calls of the C11 atomic
/// operations are counted at the call, and their bodies are not followed: a
/// load writes nothing; a compare-and-swap writes memory only when it
/// succeeds, and on failure overwrites its expected value, which must be the
/// address of a local of the caller (so success is "the expected value is
/// unchanged"); any other operation writes.
///
/// A loop is left alone when it, or a function it may call, does anything
/// else: creates threads, calls a function without a body that takes a
/// pointer, calls through a function pointer, or runs a statement we do not
/// know. Locals declared inside the loop are not compared: their value at
/// the head is never read again before their declaration resets it.
///
/// What the reduction gains: a wait loop can be fully unwound, since once
/// nothing it reads changes, another iteration is impossible and the
/// unwinding assertion holds.

#include "spin_loops.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/fresh_symbol.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <analyses/natural_loops.h>
#include <linking/static_lifetime_init.h>

#include "goto_model.h"

#include <map>
#include <set>
#include <vector>

namespace
{
const char *const write_count_name = "__CPROVER_spin_writes";

class spin_loopst
{
public:
  explicit spin_loopst(goto_modelt &m) : model(m), ns(m.symbol_table)
  {
  }

  std::size_t run();

private:
  goto_modelt &model;
  namespacet ns;
  std::map<irep_idt, bool> followable_cache;
  std::set<irep_idt> to_count; // functions whose writes are counted

  enum class atomict
  {
    NONE,
    LOAD,
    CAS,
    WRITE
  };

  static atomict atomic_kind(const irep_idt &f)
  {
    const std::string n = id2string(f);
    if(n.rfind("__atomic_", 0) != 0)
      return atomict::NONE;
    if(n.rfind("__atomic_load", 0) == 0 ||
       n.rfind("__atomic_thread_fence", 0) == 0 ||
       n.rfind("__atomic_signal_fence", 0) == 0)
      return atomict::LOAD;
    if(n.rfind("__atomic_compare_exchange", 0) == 0)
      return atomict::CAS;
    if(n.rfind("__atomic_store", 0) == 0)
      return atomict::NONE; // followed: its body is one atomic assignment
    return atomict::WRITE;
  }

  bool is_local_of(const exprt &e, const irep_idt &fn) const
  {
    if(e.id() != ID_symbol)
      return false;
    const symbolt *s;
    if(ns.lookup(to_symbol_expr(e).get_identifier(), s))
      return false;
    // a local of fn is named fn::... (parameters, block locals, temporaries)
    return !s->is_static_lifetime && s->type.id() != ID_code &&
           id2string(s->name).rfind(id2string(fn) + "::", 0) == 0;
  }

  static irep_idt callee_of(const goto_programt::instructiont &i)
  {
    const exprt &f = i.call_function();
    return f.id() == ID_symbol ? to_symbol_expr(f).get_identifier()
                               : irep_idt();
  }

  /// the local of the caller whose address is a compare-and-swap's expected
  /// value (argument 1), or nil
  exprt cas_expected(const goto_programt::instructiont &i,
                     const irep_idt &fn) const
  {
    if(i.call_arguments().size() < 2)
      return nil_exprt();
    exprt e = i.call_arguments()[1];
    while(e.id() == ID_typecast)
      e = to_typecast_expr(e).op();
    if(e.id() != ID_address_of ||
       !is_local_of(to_address_of_expr(e).object(), fn))
      return nil_exprt();
    return to_address_of_expr(e).object();
  }

  /// Can the counting follow everything \p f does? Collects the functions
  /// whose writes must be counted into to_count.
  bool followable(const irep_idt &f)
  {
    auto c = followable_cache.find(f);
    if(c != followable_cache.end())
      return c->second;
    followable_cache[f] = false; // recursion: not followed
    auto it = model.goto_functions.function_map.find(f);
    if(it == model.goto_functions.function_map.end() ||
       !it->second.body_available())
      return false;
    for(const auto &i : it->second.body.instructions)
      if(!followable_instruction(i, f))
        return false;
    followable_cache[f] = true;
    to_count.insert(f);
    return true;
  }

  bool followable_instruction(const goto_programt::instructiont &i,
                              const irep_idt &fn)
  {
    switch(i.type())
    {
    case GOTO:
    case ASSUME:
    case ASSERT:
    case SKIP:
    case LOCATION:
    case DECL:
    case DEAD:
    case ATOMIC_BEGIN:
    case ATOMIC_END:
    case SET_RETURN_VALUE:
    case END_FUNCTION:
    case ASSIGN:
      return true;
    case OTHER:
      return i.get_other().get_statement() == ID_expression;
    case FUNCTION_CALL:
    {
      const irep_idt callee = callee_of(i);
      if(callee.empty())
        return false; // through a function pointer
      const atomict a = atomic_kind(callee);
      if(a == atomict::CAS)
        return cas_expected(i, fn).is_not_nil();
      if(a != atomict::NONE)
        return true;
      auto it = model.goto_functions.function_map.find(callee);
      if(it != model.goto_functions.function_map.end() &&
         it->second.body_available())
        return followable(callee);
      // no body: harmless only if it is handed no pointer
      for(const auto &arg : i.call_arguments())
        if(arg.type().id() == ID_pointer)
          return false;
      return true;
    }
    default:
      return false; // threads, exceptions
    }
  }

  std::size_t instrument_loops(const irep_idt &fn, goto_programt &body,
                               const symbol_exprt &count);
  void count_writes(const irep_idt &fn, goto_programt &body,
                    const symbol_exprt &count);
  symbol_exprt fresh_local(const typet &type, const irep_idt &fn,
                           const source_locationt &loc)
  {
    symbolt &s = get_fresh_aux_symbol(
      type, id2string(fn), "spin_old", loc, ID_C, model.symbol_table);
    s.is_static_lifetime = false;
    return s.symbol_expr();
  }
};

std::size_t spin_loopst::run()
{
  symbolt count_symbol;
  count_symbol.name = write_count_name;
  count_symbol.type = unsigned_int_type();
  count_symbol.mode = ID_C;
  count_symbol.base_name = write_count_name;
  count_symbol.is_static_lifetime = true;
  count_symbol.is_thread_local = true;
  count_symbol.is_lvalue = true;
  count_symbol.value = from_integer(0, unsigned_int_type());
  model.symbol_table.insert(count_symbol);
  const symbol_exprt count = count_symbol.symbol_expr();

  std::size_t n = 0;
  for(auto &fp : model.goto_functions.function_map)
    if(fp.second.body_available() && atomic_kind(fp.first) == atomict::NONE)
      n += instrument_loops(fp.first, fp.second.body, count);
  if(n == 0)
    return 0;
  for(auto &fp : model.goto_functions.function_map)
    if(to_count.count(fp.first))
      count_writes(fp.first, fp.second.body, count);
  // the main thread's copy starts at zero like every other thread's
  auto init = model.goto_functions.function_map.find(INITIALIZE_FUNCTION);
  if(init != model.goto_functions.function_map.end() &&
     init->second.body_available())
  {
    auto &b = init->second.body;
    auto first = b.instructions.begin();
    auto zero = goto_programt::make_assignment(
      count, from_integer(0, count.type()), first->source_location());
    b.insert_before_swap(first, zero);
  }
  model.goto_functions.update();
  return n;
}

std::size_t spin_loopst::instrument_loops(const irep_idt &fn,
                                          goto_programt &body,
                                          const symbol_exprt &count)
{
  natural_loops_mutablet loops(body);
  struct editt
  {
    goto_programt::targett head;
    std::vector<goto_programt::targett> back_edges;
    std::vector<symbol_exprt> compared;
  };
  std::vector<editt> edits;
  for(auto &l : loops.loop_map)
  {
    bool ok = true;
    std::set<irep_idt> declared, seen;
    std::vector<symbol_exprt> compared;
    for(const auto &t : l.second)
      if(t->is_decl())
        declared.insert(t->decl_symbol().get_identifier());
    auto compare = [&](const exprt &e) {
      if(e.id() == ID_symbol && is_local_of(e, fn) &&
         !declared.count(to_symbol_expr(e).get_identifier()) &&
         seen.insert(to_symbol_expr(e).get_identifier()).second)
        compared.push_back(to_symbol_expr(e));
    };
    for(const auto &t : l.second)
    {
      if(!followable_instruction(*t, fn))
      {
        ok = false;
        break;
      }
      if(t->is_assign())
        compare(t->assign_lhs());
      else if(t->is_function_call())
      {
        if(t->call_lhs().is_not_nil())
          compare(t->call_lhs());
        if(atomic_kind(callee_of(*t)) == atomict::CAS)
          compare(cas_expected(*t, fn));
      }
    }
    if(!ok)
      continue;
    editt e;
    e.head = l.first;
    e.compared = compared;
    for(const auto &t : l.second)
      if(t->is_goto() && t->get_target() == e.head)
        e.back_edges.push_back(t);
    if(!e.back_edges.empty())
      edits.push_back(e);
  }

  // a head or back edge shared by two loops would be moved by the first edit
  // under the second: such loops are left alone
  std::set<goto_programt::targett> used;
  std::vector<editt> safe;
  for(auto &e : edits)
  {
    bool clash = !used.insert(e.head).second;
    for(auto &b : e.back_edges)
      if(b != e.head && !used.insert(b).second)
        clash = true;
    if(!clash)
      safe.push_back(e);
  }
  if(!safe.empty())
    to_count.insert(fn);

  for(auto &e : safe)
  {
    const source_locationt &loc = e.head->source_location();
    exprt::operandst changed;
    goto_programt copies;
    std::vector<symbol_exprt> watched = e.compared;
    watched.push_back(count);
    for(const auto &w : watched)
    {
      const symbol_exprt c = fresh_local(w.type(), fn, loc);
      copies.add(goto_programt::make_decl(c, loc));
      copies.add(goto_programt::make_assignment(c, w, loc));
      changed.push_back(notequal_exprt(w, c));
    }
    const exprt some_change = disjunction(changed);
    for(auto &b : e.back_edges)
    {
      auto assume = goto_programt::make_assumption(
        or_exprt(not_exprt(b->condition()), some_change), b->source_location());
      body.insert_before_swap(b, assume);
    }
    body.insert_before_swap(e.head, copies);
  }
  return safe.size();
}

void spin_loopst::count_writes(const irep_idt &fn, goto_programt &body,
                               const symbol_exprt &count)
{
  const exprt one = from_integer(1, count.type());
  const exprt zero = from_integer(0, count.type());
  // inside an atomic section no other thread runs between a comparison and
  // the assignment after it, so a scalar assignment there counts only when
  // it changes the value: storing what memory already holds changes nothing
  bool in_atomic = false;
  for(auto it = body.instructions.begin(); it != body.instructions.end(); ++it)
  {
    const source_locationt loc = it->source_location();
    if(it->is_atomic_begin())
      in_atomic = true;
    else if(it->is_atomic_end())
      in_atomic = false;
    else if(it->is_assign())
    {
      const exprt &lhs = it->assign_lhs();
      // __CPROVER_dead_object, the pointer check's record of a local that
      // went out of scope, is not counted: in an iteration that writes no
      // memory and changes no local of the looping function, no pointer to
      // the local survives, so the record can never match a dereference
      if(is_local_of(lhs, fn) ||
         (lhs.id() == ID_symbol &&
          (to_symbol_expr(lhs).get_identifier() == write_count_name ||
           to_symbol_expr(lhs).get_identifier() ==
             CPROVER_PREFIX "dead_object")))
        continue;
      const typet &t = lhs.type();
      const bool scalar = t.id() == ID_pointer || t.id() == ID_bool ||
                          t.id() == ID_c_bool ||
                          can_cast_type<bitvector_typet>(t);
      const exprt step =
        in_atomic && scalar
          ? exprt(if_exprt(notequal_exprt(lhs, it->assign_rhs()), one, zero))
          : one;
      auto inc =
        goto_programt::make_assignment(count, plus_exprt(count, step), loc);
      body.insert_before_swap(it, inc);
      ++it; // to the original assignment
    }
    else if(it->is_function_call())
    {
      const atomict a = atomic_kind(callee_of(*it));
      exprt step = nil_exprt();
      if(a == atomict::WRITE)
        step = one;
      else if(a == atomict::CAS)
      {
        const exprt expected = cas_expected(*it, fn);
        if(expected.is_nil())
          step = one;
        else
        {
          // success leaves the expected value as it was
          const symbol_exprt before = fresh_local(expected.type(), fn, loc);
          goto_programt save;
          save.add(goto_programt::make_decl(before, loc));
          save.add(goto_programt::make_assignment(before, expected, loc));
          body.insert_before_swap(it, save);
          ++it;
          ++it; // to the call
          step = if_exprt(equal_exprt(expected, before), one, zero);
        }
      }
      // a call result stored outside the caller's locals is a write too
      if(it->call_lhs().is_not_nil() && !is_local_of(it->call_lhs(), fn))
        step = step.is_nil() ? one : plus_exprt(step, one);
      if(step.is_nil())
        continue;
      body.insert_after(
        it,
        goto_programt::make_assignment(count, plus_exprt(count, step), loc));
      ++it;
    }
    else if(it->is_other() &&
            it->get_other().get_statement() != ID_expression)
    {
      auto inc =
        goto_programt::make_assignment(count, plus_exprt(count, one), loc);
      body.insert_before_swap(it, inc);
      ++it;
    }
  }
}
} // namespace

std::size_t spin_loop_reduction(goto_modelt &goto_model)
{
  return spin_loopst(goto_model).run();
}
