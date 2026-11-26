/*******************************************************************\

Module: Static whole-program thread-exclusivity analysis

Author: CBMC/lazy_po work

\*******************************************************************/

/// \file
/// Static, pre-symex, whole-program analysis that identifies shared
/// (static-lifetime, non-thread-local) variables which are provably
/// touched by at most one thread for the entire program run.
///
/// This is the static counterpart of lazy_po's post-hoc, trace-based
/// "Idea 7" single-thread-variable check: that one can only classify a
/// variable once the whole SSA trace exists, which is far too late to
/// influence goto-symex's own loop unwinding. Running the equivalent
/// argument on the goto_functionst *before* symbolic execution starts
/// lets goto-symex treat such a variable exactly as it treats a genuine
/// thread-local: constant-propagate its value forward, and hence prove
/// a loop guard keyed on it false and stop unwinding early.
///
/// The analysis is deliberately, aggressively conservative. Every result
/// it returns must be safe to act on, because acting on a wrong answer
/// makes goto-symex assume a variable cannot be interfered with by
/// another thread -- which would silently drop real bugs. Whenever
/// anything cannot be established syntactically the analysis gives up,
/// either for the single variable involved or (for whole-program
/// properties such as an unresolved indirect call) for the entire
/// program, and the caller then behaves exactly as it does today.

#ifndef CPROVER_GOTO_SYMEX_THREAD_EXCLUSIVITY_H
#define CPROVER_GOTO_SYMEX_THREAD_EXCLUSIVITY_H

#include <util/irep.h>

#include <unordered_set>

class goto_functionst;
class namespacet;

/// Compute the set of shared variable identifiers that are provably accessed
/// by at most one thread over any execution of the whole program.
///
/// A returned identifier satisfies all of the following:
/// - it is a static-lifetime, non-thread-local (i.e. shared) object;
/// - its address is never taken anywhere in the program (\ref dirtyt), so
///   every access to it is a syntactic mention of its identifier and no
///   pointer can alias it;
/// - it is mentioned only in functions reachable from exactly one thread
///   entry point, where reachability does not cross thread-spawn regions;
/// - that thread entry point is provably instantiated at most once.
///
/// The result is empty if any whole-program precondition fails (an
/// unresolved indirect call, a thread spawn that is not the recognised
/// pthread_create model, a pthread_create whose start routine is not a
/// literal function address, ...).
///
/// \param goto_functions: the whole program, after the standard goto
///   processing passes (in particular after remove_function_pointers)
/// \param ns: namespace used to classify symbols
/// \return set of provably thread-exclusive shared variable identifiers
std::unordered_set<irep_idt> compute_thread_exclusive_variables(
  const goto_functionst &goto_functions,
  const namespacet &ns);

#endif // CPROVER_GOTO_SYMEX_THREAD_EXCLUSIVITY_H
