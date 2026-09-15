/*******************************************************************\

Module: Static recognition of thread-management loops

Author: CBMC/lazy_po work

\*******************************************************************/

/// \file
/// See thread_spawn_loops.h for the soundness argument this implements.

#include "thread_spawn_loops.h"

#include <util/namespace.h>
#include <util/optional.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <goto-programs/goto_functions.h>

#include <cstdlib>
#include <iostream>
#include <map>
#include <unordered_set>
#include <vector>

namespace
{
bool tml_debug()
{
  static const bool on = getenv("LAZYPO_TML_DEBUG") != nullptr;
  return on;
}

#define TML_BAIL(msg)                                                          \
  do                                                                           \
  {                                                                            \
    if(tml_debug())                                                            \
      std::cerr << "TML bail: " << (msg) << "\n";                             \
    return {};                                                                 \
  } while(0)

/// One recognised loop: everything the checks below need to know about it.
struct management_loopt
{
  irep_idt function_id;
  irep_idt loop_id;
  /// first instruction of the loop (the exit test)
  goto_programt::const_targett head;
  /// the backwards goto that closes the loop
  goto_programt::const_targett back_edge;
  /// where control goes when the loop is left
  goto_programt::const_targett exit;
  /// the induction variable
  irep_idt counter;
  /// the thread-handle array the loop indexes
  irep_idt handle_array;
  /// true for pthread_create, false for pthread_join
  bool is_spawn = false;
};

/// Strip typecasts, which the front end inserts liberally around pthread_t
/// values and around the handle pointer.
const exprt &skip_typecasts(const exprt &e)
{
  const exprt *p = &e;
  while(p->id() == ID_typecast)
    p = &to_typecast_expr(*p).op();
  return *p;
}

/// \return the identifier of \p e if it is a plain symbol, empty otherwise
irep_idt symbol_id(const exprt &e)
{
  const exprt &stripped = skip_typecasts(e);
  if(stripped.id() == ID_symbol)
    return to_symbol_expr(stripped).get_identifier();
  return irep_idt{};
}

/// Match \c array[counter], returning the array identifier, where \p counter
/// must be exactly the loop induction variable.
irep_idt indexed_array(const exprt &e, const irep_idt &counter)
{
  const exprt &stripped = skip_typecasts(e);
  if(stripped.id() != ID_index)
    return irep_idt{};

  const index_exprt &index = to_index_expr(stripped);
  if(symbol_id(index.index()) != counter)
    return irep_idt{};

  return symbol_id(index.array());
}

/// \return true if \p id occurs anywhere in \p e
bool mentions(const exprt &e, const irep_idt &id)
{
  if(e.id() == ID_symbol && to_symbol_expr(e).get_identifier() == id)
    return true;

  for(const auto &op : e.operands())
    if(mentions(op, id))
      return true;

  return false;
}

/// Instructions that may sit in a recognised loop body besides the single
/// pthread call and the counter update.
bool is_inert(const goto_programt::instructiont &i)
{
  return i.type() == SKIP || i.type() == LOCATION;
}

/// Try to recognise the loop closed by the backwards goto \p back_edge.
optionalt<management_loopt> classify_loop(
  const irep_idt &function_id,
  const goto_programt &body,
  goto_programt::const_targett back_edge)
{
  management_loopt result;
  result.function_id = function_id;
  result.back_edge = back_edge;
  result.loop_id = goto_programt::loop_id(function_id, *back_edge);

  // the back edge must be an unconditional jump: a conditional one would mean
  // the body has control flow we have not accounted for
  if(!back_edge->condition().is_true())
    TML_BAIL("conditional back edge");

  result.head = back_edge->get_target();

  // the loop head must be the exit test: IF !cond GOTO exit
  if(!result.head->is_goto() || result.head->condition().is_true())
    TML_BAIL("head is not an exit test");

  result.exit = result.head->get_target();

  // the exit must leave the loop forwards
  {
    bool exit_is_after_back_edge = false;
    for(auto it = std::next(back_edge); it != body.instructions.end(); ++it)
    {
      if(it == result.exit)
      {
        exit_is_after_back_edge = true;
        break;
      }
    }
    if(!exit_is_after_back_edge)
      TML_BAIL("exit is not after the back edge");
  }

  // walk the body: exactly one pthread_create/pthread_join call, plus
  // assignments to a single induction variable
  std::size_t calls = 0;
  exprt handle_argument = nil_exprt{};

  for(auto it = std::next(result.head); it != back_edge; ++it)
  {
    if(is_inert(*it))
      continue;

    if(it->is_assign())
    {
      const irep_idt lhs = symbol_id(it->assign_lhs());
      if(lhs.empty())
        TML_BAIL("assignment to a non-symbol");
      if(result.counter.empty())
        result.counter = lhs;
      else if(result.counter != lhs)
        TML_BAIL("more than one assigned variable");
      continue;
    }

    if(it->is_function_call())
    {
      const irep_idt callee = symbol_id(it->call_function());
      if(callee != "pthread_create" && callee != "pthread_join")
        TML_BAIL("call to " + id2string(callee));

      // the return value must be discarded; otherwise later code observes how
      // often the loop ran
      if(it->call_lhs().is_not_nil())
        TML_BAIL("call return value is used");

      if(it->call_arguments().empty())
        TML_BAIL("call has no arguments");

      ++calls;
      if(calls > 1)
        TML_BAIL("more than one call");

      result.is_spawn = (callee == "pthread_create");
      handle_argument = it->call_arguments().front();
      continue;
    }

    // anything else (a nested goto, an assert, another call, a decl, ...)
    // means the loop does more than manage threads
    TML_BAIL("unexpected instruction in body");
  }

  if(calls != 1 || result.counter.empty())
    TML_BAIL("no call, or no induction variable");

  // the exit test has to be keyed on the induction variable, otherwise
  // stopping early is not "stopping the loop early" in any meaningful sense
  if(!mentions(result.head->condition(), result.counter))
    TML_BAIL("exit test not keyed on the induction variable");

  // nothing after the loop may observe the induction variable
  if(!result.exit->is_dead() ||
     result.exit->dead_symbol().get_identifier() != result.counter)
  {
    TML_BAIL("induction variable is live after the loop");
  }

  // the loop must start at index 0. Together with the bound being the same for
  // every loop over the same handle array, this is what makes "the first k
  // iterations" mean the same k entries in the spawn loop and in the join
  // loops: a join then never reads an entry the bounded spawn loop did not
  // write.
  {
    auto init = result.head;
    while(init != body.instructions.begin())
    {
      --init;
      if(!is_inert(*init))
        break;
    }

    if(
      !init->is_assign() || symbol_id(init->assign_lhs()) != result.counter ||
      !init->assign_rhs().is_constant() ||
      !init->assign_rhs().is_zero())
    {
      TML_BAIL("loop does not start at index 0");
    }
  }

  // the handle argument pins down the thread-handle array
  if(result.is_spawn)
  {
    // pthread_create(&t_ids[i], ...)
    const exprt &arg = skip_typecasts(handle_argument);
    if(arg.id() != ID_address_of)
      TML_BAIL("pthread_create handle argument is not &x");
    result.handle_array =
      indexed_array(to_address_of_expr(arg).object(), result.counter);
  }
  else
  {
    // pthread_join(t_ids[i], ...)
    result.handle_array = indexed_array(handle_argument, result.counter);
  }

  if(result.handle_array.empty())
    TML_BAIL("handle argument is not array[counter]");

  return result;
}

/// \return true if nothing between \p from and the end of \p body can observe
/// that a join loop was left early -- i.e. that main went on while some of the
/// threads it would have waited for may not have finished.
///
/// What is allowed in the tail: the bookkeeping that ends the function, and
/// further thread-management loops (whose instruction location numbers are in
/// \p management_instructions) together with their induction-variable
/// declaration and initialisation.  The latter is what the
/// create_threads(t1); create_threads(t2); ... join_threads(t1);
/// join_threads(t2); shape needs: spawning more threads, or waiting for more
/// threads, cannot tell that the previous wait was cut short.  Anything else
/// -- any other call, any assertion, any branch, any store the other threads
/// could see -- makes us give up.
bool tail_is_inconsequential(
  const goto_programt &body,
  goto_programt::const_targett from,
  const std::unordered_set<unsigned> &management_instructions,
  const std::unordered_set<irep_idt> &management_counters)
{
  for(auto it = from; it != body.instructions.end(); ++it)
  {
    if(management_instructions.count(it->location_number) > 0)
      continue;

    switch(it->type())
    {
    case DEAD:
    case SET_RETURN_VALUE:
    case END_FUNCTION:
    case SKIP:
    case LOCATION:
      break;

    case DECL:
      // declaring the next loop's induction variable, or the next handle array
      break;

    case ASSIGN:
      // only the initialisation of another management loop's counter
      if(management_counters.count(symbol_id(it->assign_lhs())) == 0)
        return false;
      break;

    default:
      return false;
    }
  }
  return true;
}
} // namespace

std::unordered_set<irep_idt> compute_thread_management_loops(
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  std::vector<management_loopt> loops;

  for(const auto &fn : goto_functions.function_map)
  {
    if(!fn.second.body_available())
      continue;

    const goto_programt &body = fn.second.body;
    for(auto it = body.instructions.begin(); it != body.instructions.end();
        ++it)
    {
      if(!it->is_backwards_goto())
        continue;

      auto classified = classify_loop(fn.first, body, it);
      if(classified.has_value())
        loops.push_back(*classified);
    }
  }

  if(tml_debug())
    std::cerr << "TML: " << loops.size() << " candidate loop(s)\n";

  if(loops.empty())
    return {};

  // Everything that belongs to *some* candidate management loop, by location
  // number, plus the induction variables of those loops. A candidate loop body
  // is by construction nothing but a pthread_create/pthread_join call and its
  // counter update, so such instructions are harmless wherever they appear --
  // in particular in the tail after another loop we intend to cut short.
  std::map<irep_idt, std::unordered_set<unsigned>> management_instructions;
  std::map<irep_idt, std::unordered_set<irep_idt>> management_counters;

  for(const auto &loop : loops)
  {
    auto &instructions = management_instructions[loop.function_id];
    for(auto it = loop.head; it != std::next(loop.back_edge); ++it)
      instructions.insert(it->location_number);
    management_counters[loop.function_id].insert(loop.counter);
  }

  // group by thread-handle array
  std::map<irep_idt, std::vector<const management_loopt *>> by_array;
  for(const auto &loop : loops)
    by_array[loop.handle_array].push_back(&loop);

  std::unordered_set<irep_idt> result;

  for(const auto &entry : by_array)
  {
    const irep_idt &array_id = entry.first;
    const auto &array_loops = entry.second;

    // the array must be an ordinary program object (not, say, a CPROVER
    // internal), and it must not be shared: a static-lifetime, non-thread-local
    // handle array is visible to every thread, and its contents then form part
    // of the shared state the other threads can observe.  (Function locals
    // carry is_thread_local, which is exactly what we want.)
    const symbolt *array_symbol = nullptr;
    if(ns.lookup(array_id, array_symbol) || array_symbol == nullptr)
      continue;
    if(array_symbol->is_static_lifetime && !array_symbol->is_thread_local)
    {
      if(tml_debug())
        std::cerr << "TML bail: handle array " << array_id
                  << " is not a local\n";
      continue;
    }

    // at least one spawn loop, or there is nothing to bound
    bool has_spawn = false;
    for(const auto *loop : array_loops)
      has_spawn |= loop->is_spawn;
    if(!has_spawn)
      continue;

    // every mention of the array anywhere in the program must be inside one of
    // these loops (or its own DECL/DEAD): otherwise some other code can tell
    // that only the first k elements were written
    bool array_is_private_to_the_loops = true;

    for(const auto &fn : goto_functions.function_map)
    {
      if(!fn.second.body_available())
        continue;

      const goto_programt &body = fn.second.body;
      for(auto it = body.instructions.begin();
          it != body.instructions.end() && array_is_private_to_the_loops;
          ++it)
      {
        bool mentioned = false;
        it->apply([&](const exprt &e) { mentioned |= mentions(e, array_id); });
        if(!mentioned)
          continue;

        if(
          (it->type() == DECL &&
           it->decl_symbol().get_identifier() == array_id) ||
          (it->type() == DEAD &&
           it->dead_symbol().get_identifier() == array_id))
        {
          continue;
        }

        // inside one of our loops?
        bool inside = false;
        for(const auto *loop : array_loops)
        {
          if(loop->function_id != fn.first)
            continue;
          for(auto j = loop->head; j != std::next(loop->back_edge); ++j)
          {
            if(j == it)
            {
              inside = true;
              break;
            }
          }
          if(inside)
            break;
        }

        if(!inside)
          array_is_private_to_the_loops = false;
      }

      if(!array_is_private_to_the_loops)
        break;
    }

    if(!array_is_private_to_the_loops)
    {
      if(tml_debug())
        std::cerr << "TML bail: array " << array_id
                  << " is mentioned outside the loops\n";
      continue;
    }

    // a join loop may only be cut short if nothing follows it that could
    // notice
    bool joins_are_safe_to_cut = true;
    for(const auto *loop : array_loops)
    {
      if(loop->is_spawn)
        continue;
      const goto_programt &body =
        goto_functions.function_map.at(loop->function_id).body;
      if(!tail_is_inconsequential(
           body,
           loop->exit,
           management_instructions[loop->function_id],
           management_counters[loop->function_id]))
      {
        joins_are_safe_to_cut = false;
        break;
      }
    }

    if(!joins_are_safe_to_cut)
    {
      if(tml_debug())
        std::cerr << "TML bail: code after a join loop over " << array_id
                  << " could observe the early exit\n";
      continue;
    }

    for(const auto *loop : array_loops)
      result.insert(loop->loop_id);
  }

  return result;
}
