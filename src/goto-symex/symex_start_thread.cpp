/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "goto_symex.h"

#include <util/exception_utils.h>
#include <util/expr_initializer.h>

#include "expr_skeleton.h"
#include "path_storage.h"
#include "symex_assign.h"

#include <algorithm>
#include <unordered_set>

/// Whether \p a and \p b cannot both hold: a top-level conjunct of one is the
/// negation of a top-level conjunct of the other. Syntactic, so a false answer
/// only means "not shown".
static bool guards_exclude(const exprt &a, const exprt &b)
{
  const auto conjuncts = [](const exprt &g) {
    return g.id() == ID_and ? g.operands() : exprt::operandst{g};
  };
  const exprt::operandst of_a = conjuncts(a);
  const std::unordered_set<exprt, irep_hash> set_a(of_a.begin(), of_a.end());
  for(const exprt &c : conjuncts(b))
  {
    const exprt negation =
      c.id() == ID_not ? to_not_expr(c).op() : exprt{not_exprt{c}};
    if(set_a.count(negation) != 0)
      return true;
  }
  return false;
}

void goto_symext::symex_start_thread(statet &state)
{
  if(!state.reachable)
    return;

  if(state.atomic_section_id != 0)
    throw incorrect_goto_program_exceptiont(
      "spawning threads out of atomic sections is not allowed; "
      "this would require amendments to ordering constraints",
      state.source.pc->source_location());

  const goto_programt::instructiont &instruction=*state.source.pc;

  INVARIANT(instruction.targets.size() == 1, "start_thread expects one target");

  goto_programt::const_targett thread_target=
    instruction.get_target();

  const std::size_t current_thread_nr = state.source.thread_nr;
  const exprt creation_guard = state.guard.as_expr();

  // --merge-exclusive-threads: a thread this thread created earlier at the
  // same instruction, every creation of which excludes this one, is still
  // pending (threads run in order, after their parent ends), so it can be this
  // thread as well: it runs under the disjunction of the creation guards, and
  // the copies of the locals below take the value of the path that created
  // it, through the phi functions where the paths meet. One body instead of
  // one per path, with the same executions: the creations exclude each other,
  // so at most one of them happens in each.
  // Only for --rounds: the memory models without it number the threads by
  // counting spawns (memory_model_sct::thread_spawn).
  std::size_t new_thread_nr = state.threads.size();
  if(symex_config.merge_exclusive_threads && symex_config.lazy_po_rounds > 0)
  {
    for(std::size_t t = 0; t < state.threads.size(); ++t)
    {
      const statet::threadt &other = state.threads[t];
      if(
        !other.creation_guards.empty() && other.pc == thread_target &&
        other.parent_thread_nr == current_thread_nr &&
        other.function_id == state.source.function_id &&
        std::all_of(
          other.creation_guards.begin(),
          other.creation_guards.end(),
          [&creation_guard](const exprt &g) {
            return guards_exclude(g, creation_guard);
          }))
      {
        new_thread_nr = t;
        break;
      }
    }
  }
  const bool merged = new_thread_nr < state.threads.size();

  // record this
  target.spawn(creation_guard, state.source, new_thread_nr);

  if(merged)
  {
    state.threads[new_thread_nr].guard |= state.guard;
    log.statistics() << "thread creation merged into thread " << new_thread_nr
                     << log.eom;
  }
  else
  {
    // put into thread vector
    state.threads.push_back(statet::threadt(guard_manager));
    statet::threadt &thread = state.threads.back();
    thread.pc = thread_target;
    thread.function_id = state.source.function_id;
    thread.guard = state.guard;
    thread.parent_thread_nr = static_cast<unsigned>(current_thread_nr);
    thread.call_stack.push_back(state.call_stack().top());
    thread.call_stack.back().local_objects.clear();
    thread.call_stack.back().goto_state_map.clear();
  }
  statet::threadt &new_thread = state.threads[new_thread_nr];
  new_thread.creation_guards.push_back(creation_guard);

  // create a copy of the local variables for the new thread
  framet &frame = state.call_stack().top();

  symex_renaming_levelt::viewt view;
  state.get_level2().current_names.get_view(view);

  for(const auto &pair : view)
  {
    const irep_idt l1_o_id = pair.second.first.get_l1_object_identifier();

    // could use iteration over local_objects as l1_o_id is prefix
    if(frame.local_objects.find(l1_o_id)==frame.local_objects.end())
      continue;

    // get original name
    ssa_exprt lhs(pair.second.first.get_original_expr());

    // get L0 name for current thread
    const renamedt<ssa_exprt, L0> l0_lhs =
      symex_level0(std::move(lhs), ns, new_thread_nr);
    // a merged thread has its copy from an earlier creation
    if(!state.level1.has(l0_lhs))
    {
      const irep_idt &l0_name = l0_lhs.get().get_identifier();
      std::size_t l1_index = path_storage.get_unique_l1_index(l0_name, 0);
      CHECK_RETURN(l1_index == 0);

      // set up L1 name
      state.level1.insert(l0_lhs, 0);
    }

    const ssa_exprt lhs_l1 = state.rename_ssa<L1>(l0_lhs.get(), ns).get();
    const irep_idt l1_name = lhs_l1.get_l1_object_identifier();
    // store it
    new_thread.call_stack.back().local_objects.insert(l1_name);

    // make copy
    ssa_exprt rhs = pair.second.first;

    exprt::operandst lhs_conditions;
    state.record_events.push(false);
    symex_assignt{
      state, symex_targett::assignment_typet::HIDDEN, ns, symex_config, target}
      .assign_symbol(lhs_l1, expr_skeletont{}, rhs, lhs_conditions);
    const exprt l2_lhs = state.rename(lhs_l1, ns).get();
    state.record_events.pop();

    // record a shared write in the new thread
    if(
      state.write_is_shared(lhs_l1, ns) ==
        goto_symex_statet::write_is_shared_resultt::SHARED &&
      is_ssa_expr(l2_lhs))
    {
      state.source.thread_nr = new_thread_nr;
      target.shared_write(
        state.guard.as_expr(), to_ssa_expr(l2_lhs), 0, state.source);
      state.source.thread_nr = current_thread_nr;
    }
  }

  // initialize all variables marked thread-local
  const symbol_tablet &symbol_table=ns.get_symbol_table();

  for(const auto &symbol_pair : symbol_table.symbols)
  {
    const symbolt &symbol = symbol_pair.second;

    if(!symbol.is_thread_local ||
       !symbol.is_static_lifetime ||
       (symbol.is_extern && symbol.value.is_nil()))
      continue;

    // get original name
    ssa_exprt lhs(symbol.symbol_expr());

    // get L0 name for current thread
    lhs.set_level_0(new_thread_nr);

    exprt rhs=symbol.value;
    if(rhs.is_nil())
    {
      const auto zero = zero_initializer(symbol.type, symbol.location, ns);
      CHECK_RETURN(zero.has_value());
      rhs = *zero;
    }

    // As for the copies of the locals above, the initialisation belongs to
    // the new thread, not to the spawning one. Recorded in the spawning
    // thread, after its spawn event, it was a write concurrent with the new
    // thread's own accesses to its copy, and once the copy's address was
    // taken (so that it is shared) it was paired with them as a race:
    // `static __thread unsigned slot;`, written through `&slot` by each
    // thread (libvsync/arraylock, no-data-race).
    exprt::operandst lhs_conditions;
    state.record_events.push(false);
    symex_assignt{
      state, symex_targett::assignment_typet::HIDDEN, ns, symex_config, target}
      .assign_symbol(lhs, expr_skeletont{}, rhs, lhs_conditions);
    const ssa_exprt lhs_l1 = state.rename_ssa<L1>(lhs, ns).get();
    const exprt l2_lhs = state.rename(lhs_l1, ns).get();
    state.record_events.pop();

    if(
      state.write_is_shared(lhs_l1, ns) ==
        goto_symex_statet::write_is_shared_resultt::SHARED &&
      is_ssa_expr(l2_lhs))
    {
      state.source.thread_nr = new_thread_nr;
      target.shared_write(
        state.guard.as_expr(), to_ssa_expr(l2_lhs), 0, state.source);
      state.source.thread_nr = current_thread_nr;
    }
  }
}
