/*******************************************************************\

Module: Static recognition of thread-management loops

Author: CBMC/lazy_po work

\*******************************************************************/

/// \file
/// Static, pre-symex recognition of the "spawn N threads in a loop / join
/// them again in a loop" idiom, so that goto-symex can bound the *number of
/// threads it actually creates* independently of the loop bound the program
/// itself asks for.
///
/// Motivation.  A large part of the SV-COMP goblint-regression family is
/// generated from a shared header whose \c create_threads(t) macro expands to
///
///     pthread_t t_ids[N]; for(int i=0; i<N; i++)
///       pthread_create(&t_ids[i], NULL, t_fun, NULL);
///
/// with \c N == 10000, and whose \c join_threads(t) macro is the matching
///
///     for(int i=0; i<N; i++) pthread_join(t_ids[i], NULL);
///
/// Unwinding either loop 10000 times never finishes inside any usable time
/// budget -- the bottleneck is symbolic execution itself, long before the
/// solver is reached -- and unwinding it *fewer* times is, with the standard
/// bounded-unwinding semantics, worse than useless: goto-symex emits
/// \c assume(!loop_guard) when the bound is exceeded, which is \c assume(false)
/// here, so everything after the loop -- including the property -- becomes
/// unreachable and the tool answers a vacuous "no violation".
///
/// What this analysis buys.  \c pthread_create only makes a thread *runnable*;
/// it does not force it to run.  An execution of the program in which only the
/// first k threads have been created, and main has performed only the matching
/// first k joins, is therefore a genuine execution of the N-thread program in
/// which threads k..N-1 were created but not yet scheduled and main has not
/// yet reached their joins -- provided nothing else in the program can observe
/// the difference.  That proviso is what this analysis checks, syntactically
/// and conservatively:
///
/// - the loop body is *exactly* one call to \c pthread_create (respectively
///   \c pthread_join) plus the induction-variable bookkeeping and the back
///   edge -- nothing else runs in the loop, so stopping early skips nothing
///   but thread creation/joining;
/// - the induction variable is \c DEAD immediately at the loop exit, so no
///   later code can observe that it stopped at k instead of N;
/// - the thread-handle array is a local whose every single mention in the
///   whole program is inside one of the recognised loops, so no later code can
///   observe that only its first k elements were written;
/// - every \c pthread_join loop over that array is recognised too, and bounded
///   at the same k, so a join never reads an element the (bounded) spawn loop
///   did not write;
/// - after a recognised join loop there is nothing left in the function but
///   \c DEAD / \c SET_RETURN_VALUE / \c END_FUNCTION and the like, so exiting
///   the join loop early cannot expose any code to a state in which fewer
///   threads have finished than the program would have waited for.
///
/// Under those conditions the bounded exploration is exactly the k-thread
/// program, and every execution of the k-thread program is an execution of the
/// N-thread program.  A counterexample found under the bound is therefore a
/// real counterexample.  The converse does not hold: not finding one only says
/// "no violation with k threads", which is a bound of the same nature as
/// \c --unwind, not a proof.  See \ref goto_symext::thread_creation_bound_hit.
///
/// As with thread_exclusivity.h, anything that cannot be established
/// syntactically makes the analysis give up -- for the array involved, or for
/// the whole program -- and goto-symex then behaves exactly as it does today.

#ifndef CPROVER_GOTO_SYMEX_THREAD_SPAWN_LOOPS_H
#define CPROVER_GOTO_SYMEX_THREAD_SPAWN_LOOPS_H

#include <util/irep.h>

#include <unordered_set>

class goto_functionst;
class namespacet;

/// Compute the set of loop identifiers (as produced by
/// \c goto_programt::loop_id, i.e. "<function>.<loop number>") of loops that
/// do nothing but spawn or join threads over a thread-handle array that the
/// rest of the program never mentions.
///
/// \param goto_functions: the whole program, after the standard goto
///   processing passes (in particular after remove_function_pointers)
/// \param ns: namespace used to classify symbols
/// \return set of loop ids that may be bounded by the thread-creation bound
std::unordered_set<irep_idt> compute_thread_management_loops(
  const goto_functionst &goto_functions,
  const namespacet &ns);

#endif // CPROVER_GOTO_SYMEX_THREAD_SPAWN_LOOPS_H
