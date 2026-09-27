/*******************************************************************\

Module: Thread-aware SSA slicing

Author: Gennaro Parlato, gennaro.parlato@unimol.it

\*******************************************************************/

/// \file
/// Slicing of the SSA equation for concurrent programs.
///
/// \par Why a separate slicer
///
/// \ref slice in bmc_util.cpp used to decline to slice as soon as the equation
/// had threads:
///
///     if(symex_target_equation.has_threads())
///     {
///       // we should build a thread-aware SSA slicer
///       msg.statistics() << "no slicing due to threads";
///     }
///
/// so on every concurrent benchmark \c --slice-formula and \c --simple-slice
/// were silently no-ops.  Neither sequential slicer can simply be switched on
/// in their place.
///
/// \ref symex_slicet visits each step in reverse and collects the symbols it
/// reads, but for \c SHARED_READ, \c SHARED_WRITE, \c CONSTRAINT, \c SPAWN and
/// the atomic-section markers it collects nothing at all (see the "ignore for
/// now" arms of \c symex_slicet::slice).  It therefore keeps the shared
/// accesses themselves while discarding the assignments that compute the
/// values they store: a value that flows only into a shared write has no
/// intra-thread use, so it looks dead.  The write survives referring to a
/// symbol nothing defines, and the solver is then free to choose that symbol's
/// value.  \c symex_slicet::slice also begins with \c simple_slice, which
/// drops everything after the last assertion in equation order -- and equation
/// order is symex's scheduling order, not an execution order, so a shared
/// write that a real interleaving runs *before* the assertion may well sit
/// after it in the equation.
///
/// \c --full-slice is worse, operating on the goto program before symex with
/// no notion of threads at all: on 28-race_reach_81-list_racing, which fails
/// in about two seconds by default, it reports SUCCESSFUL in under one.
///
/// \par What this slicer does
///
/// Only assignment steps are candidates for removal.  Every other kind of step
/// is kept unconditionally.  An assignment is kept exactly when the symbol it
/// defines is demanded, transitively, by a kept step.
///
/// Formally, let K be the least set of steps such that
///
///   - every step that is not an assignment is in K;
///   - if a step in K reads an SSA symbol -- in its guard, its condition, its
///     right-hand side or its left-hand side -- then the step defining that
///     symbol is in K.
///
/// Every step outside K is an assignment whose defined symbol no step in K
/// reads, transitively.  Its value is therefore unconstrained by, and cannot
/// constrain, anything the property or the concurrency encoding mentions, so
/// dropping it preserves the property's truth value in *both* directions.
/// Unlike bounding thread creation or instantiating a symmetric array family
/// at a small size, which are under-approximations that may lose a violation,
/// this is an equivalence, and so is safe to leave on for proofs as well as
/// for bug finding.
///
/// Two consequences of that definition are worth stating, because they are the
/// points the sequential slicer gets wrong:
///
///   - Shared reads and writes are kept, and their operands are demanded.  A
///     shared read is not satisfied by a syntactic definition -- it may take
///     the value of any write to the same object, in any thread -- so the
///     assignment feeding a shared write must survive even though no step in
///     the writing thread reads it.
///   - Constraint steps are kept, and their operands are demanded.  This
///     matters because \ref lazy_pot runs *before* this slice (bmc_util.cpp
///     calls it from \c postprocess_equation, ahead of \c slice) and has
///     already emitted its read-from, write-ordering and context-switch
///     constraints into the equation.  Those name the symbols of shared
///     accesses; closing over them guarantees every symbol the encoding refers
///     to is still defined.
///
/// Location, declaration, function-call, function-return, goto and output
/// steps are kept even though they generate no clauses, because
/// \c lazy_pot::collect_reads_and_writes stages exactly those to reconstruct
/// the round-robin counterexample trace.  Removing them would cost witness
/// quality to save nothing.
///
/// \par How much it is worth
///
/// Less than one might hope, and the reason is worth recording.  On
/// 28-race_reach_81-list_racing at \c --unwind 2 \c --rounds 2 the equation has
/// 6506 steps, of which only 375 are assignments; the other 5472 are the
/// constraints lazy_po emits for 276 shared accesses over 29 objects.  The
/// formula is dominated by the concurrency encoding, not by the program, so
/// removing dead program steps moves the clause count by a couple of per cent.
/// The measured lever on these benchmarks is the read-from encoding -- the
/// product of reads and writes per shared object, and the width of the values
/// involved -- rather than the SSA.
///
/// Conservative in the usual direction: any step whose dependencies cannot be
/// determined is kept.  Slicing too little costs time; slicing too much costs
/// correctness.

#ifndef CPROVER_GOTO_SYMEX_THREAD_AWARE_SLICE_H
#define CPROVER_GOTO_SYMEX_THREAD_AWARE_SLICE_H

#include <cstddef>

class symex_target_equationt;

/// Slice the equation of a concurrent program, preserving the property and
/// every value the concurrency encoding may observe.
///
/// Marks the removed steps ignored rather than erasing them, so the step list
/// and the constraints lazy_po built over it stay index-consistent.
///
/// \param equation: the equation to slice, after lazy_po has run
/// \return the number of assignments newly marked ignored
std::size_t thread_aware_slice(symex_target_equationt &equation);

#endif // CPROVER_GOTO_SYMEX_THREAD_AWARE_SLICE_H
