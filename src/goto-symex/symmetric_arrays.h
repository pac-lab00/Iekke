/*******************************************************************\

Module: Static recognition of symmetric array families

Author: CBMC/lazy_po work

\*******************************************************************/

/// \file
/// Static, pre-symex recognition of the "array of N independent,
/// interchangeable slots" idiom, so that a bug hunt can be carried out at a
/// small instance of N instead of the one the program declares.
///
/// Motivation.  Part of the SV-COMP goblint-regression family declares a
/// fixed-size pool of slots and lets each thread pick one nondeterministically:
///
///     struct s *buckets[256];
///     pthread_mutex_t mutexes[256];
///     for(int i = 0; i < 256; i++) { pthread_mutex_init(&mutexes[i], 0);
///                                    buckets[i] = malloc(...); init(...); }
///     /* t1 */ int i = nondet() % 256; assume(i >= 0); insert(p, buckets[i]);
///     /* t2 */ int i = nondet() % 256, j = nondet() % 256;
///              p = take(buckets[j]); lock(&mutexes[i]); ... unlock(&mutexes[i]);
///
/// The violation these encode is a mismatched lock: a node is taken from
/// \c buckets[j] but guarded by \c mutexes[i], so two \c t2 threads sharing a
/// node while holding different mutexes interleave a non-atomic increment and
/// decrement.  A witness therefore touches **one** bucket and **two** mutex
/// indices.  The remaining 254 slots take no part in it.
///
/// Why the bound levers cannot help here, all measured:
///
/// - Unwinding the setup loop fewer than 256 times does not under-approximate.
///   goto-symex emits \c assume(!guard) when a bound is exceeded, which is
///   \c assume(false) for a counted loop, so *every* execution disappears and
///   the tool answers a vacuous "no violation" in well under a second.
/// - Unwinding it fully and bounding only the thread-creation loops still
///   times out: the setup is the cost, not the threads.
/// - Constraining the indices while leaving the loop at 256 still times out,
///   because all 256 slots are built regardless of which are read.
/// - Shrinking the loop bound *and* constraining the indices, but leaving the
///   declarations at [256], also still times out.  The state is in the array
///   type: 256 mutexes is some ten kilobytes of symbolic state, and each
///   access at a symbolic index is a 256-way select however few slots are live.
///
/// So the reduction has to change N itself, in the declarations as well as in
/// the loop bound and the index expressions.
///
/// What this analysis buys, and why it is sound.  The argument is symmetry, not
/// under-approximation, and it is worth being precise because the two licence
/// different things.
///
/// Let the program be P(N), and let \c Sym(N) be the group of permutations of
/// {0..N-1}.  A permutation acts on a state by permuting the slots of every
/// array in the family simultaneously.  The conditions below establish that
/// P(N) is *equivariant* under this action: applying a permutation to the
/// initial state and running is the same as running and then permuting.  This
/// holds because each slot is created identically and independently, every
/// access is at an index drawn from the same nondeterministic range, and no
/// expression relates one slot to a different one.
///
/// Take an execution e of P(N) that reaches the property, and let S be the set
/// of slot indices e touches, k = |S|.  Because the program is equivariant,
/// any permutation carrying S onto {0..k-1} maps e to an execution e' of P(N)
/// that reaches the property and touches only the first k slots.  Since
/// nothing in e' reads or writes a slot with index >= k, e' is also an
/// execution of P(k).  Conversely, an execution of P(k) embeds into P(N) for
/// any N >= k by leaving the remaining slots in their initialised state.
///
/// Hence: **P(N) has a reachable violation iff P(k) does for some k <= N**, so
/// a counterexample found at a small k is a genuine counterexample of the
/// original program.  Note the direction that does *not* hold: the absence of
/// a violation at k says nothing about N, because a witness may need more than
/// k distinct slots.  Only a violation may be reported from a reduced instance;
/// a "no violation" result must be discarded.  This mirrors the discipline that
/// makes bounded thread creation usable for bug finding.
///
/// Because of that asymmetry the minimal k never has to be computed.  The
/// caller escalates k = 2, 3, 4, ... and stops at the first violation.  Each
/// instance is cheap precisely because k is small, every reported violation is
/// real, and exhausting the escalation costs no more than the timeout the
/// unreduced program was already spending.
///
/// The conditions checked here, syntactically and conservatively:
///
/// - the family is one or more globals of array type sharing a single constant
///   size N, all indexed by the same expressions;
/// - every index into the family is either the induction variable of a
///   recognised setup loop, or a value constrained to [0, N) by a
///   nondeterministic choice (\c nondet() % N together with the accompanying
///   non-negativity assumption);
/// - the setup loop is a counted loop from 0 to N whose body writes slot i of
///   each array using only i -- it may allocate, initialise or call an
///   initialiser, but it may not read any slot other than i, so no slot's
///   initial value depends on another's;
/// - no expression anywhere relates two distinct indices into the family:
///   indices are compared against constants and used to subscript, never
///   compared with one another or combined arithmetically;
/// - the property does not quantify over the family, i.e. no loop over all N
///   slots feeds an assertion.
///
/// The fourth condition is what excludes the neighbouring benchmark
/// \c 28-race_reach_92-evilcollapse, whose setup deliberately aliases two
/// specific slots with \c p1->next = p2->next.  That program is not symmetric
/// and the analysis must, and does, decline it.
///
/// What is NOT provided here.  This header and its implementation identify the
/// families and report them; rewriting N is a separate transformation, and an
/// invasive one, because it has to change array types in the symbol table and
/// not merely constants in the goto program -- see the measurements above for
/// why the cheap version is not sufficient.

#ifndef CPROVER_GOTO_SYMEX_SYMMETRIC_ARRAYS_H
#define CPROVER_GOTO_SYMEX_SYMMETRIC_ARRAYS_H

#include <util/irep.h>

#include <cstddef>
#include <unordered_set>
#include <vector>

class goto_functionst;
class namespacet;

/// One family of arrays that are interchangeable in their slots.
struct symmetric_array_familyt
{
  /// The global arrays that are permuted together.
  std::vector<irep_idt> arrays;
  /// Their common declared size, the N of the argument above.
  std::size_t size = 0;
  /// The loop that initialises slot i of each array using only i.
  irep_idt setup_loop;
};

/// Recognise families of arrays whose slots are independent and
/// interchangeable, so that a bug hunt may be carried out at a small instance.
///
/// Conservative: a family is reported only when every condition in the file
/// comment is established syntactically. Anything not understood is omitted.
///
/// \param goto_functions: the goto model to inspect
/// \param ns: namespace for looking up the array types
/// \return the recognised families, empty if none
std::vector<symmetric_array_familyt> compute_symmetric_array_families(
  const goto_functionst &goto_functions,
  const namespacet &ns);

class goto_modelt;
class message_handlert;

/// Instantiate every recognised symmetric array family at \p instance_size
/// slots instead of its declared size.
///
/// This is an under-approximation: it keeps the violations that can be
/// exhibited with that many slots and may lose others, so **only a reported
/// violation may be believed**. A safe result at a reduced instance proves
/// nothing, exactly as for a reduced unwinding bound.
///
/// Why this and not a smaller unwinding bound. The loops that build these
/// families are setup loops: cutting one with an unwinding assumption prunes
/// every path through it, the threads are never spawned, and the run reports
/// success having generated no verification conditions at all. Shrinking the
/// family instead lets the setup loop run to completion, over fewer elements.
///
/// \param goto_model: model to rewrite in place
/// \param instance_size: slots to keep, typically small
/// \param message_handler: for reporting what was rewritten
/// \return true if any family was rewritten
bool shrink_symmetric_array_families(
  goto_modelt &goto_model,
  std::size_t instance_size,
  message_handlert &message_handler);

#endif // CPROVER_GOTO_SYMEX_SYMMETRIC_ARRAYS_H
