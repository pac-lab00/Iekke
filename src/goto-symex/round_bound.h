/*******************************************************************\

Module: Static round bound for the round-robin (lazy_po) encoding

\*******************************************************************/

/// \file
/// An upper bound on the number of round-robin rounds that suffices to
/// explore every execution of an unwound concurrent program, computed from
/// the atomic blocks lazy_po assigns and the shared objects each one touches,
/// before any constraint is built. See compute_round_bound.

#ifndef CPROVER_GOTO_SYMEX_ROUND_BOUND_H
#define CPROVER_GOTO_SYMEX_ROUND_BOUND_H

#include <util/irep.h>
#include <util/std_expr.h>

#include <cstddef>
#include <map>
#include <utility>
#include <vector>

/// One access to a shared object, placed in its atomic block: the block is
/// identified by (thread, label), as lazy_po numbers them.
struct round_bound_eventt
{
  irep_idt object;
  unsigned thread;
  unsigned label;
  bool write;
};

/// child thread -> (spawning thread, the spawning thread's label at the
/// spawn). Threads are numbered in spawn order, as lazy_po does.
using spawn_pointst = std::map<unsigned, std::pair<unsigned, unsigned>>;

struct round_boundt
{
  /// 1 + number of blocks that some backward edge can enter.
  std::size_t count;
  /// 1 + maximum number of backward edges on a path that visits each
  /// thread's blocks in increasing label order. Never above count.
  std::size_t path;
  /// false when the path search hit its cap; path is then equal to count.
  bool path_exact;
  /// true when max_rounds was given and a path needing at least that many
  /// rounds was found: path (and count, if larger) are then max_rounds.
  bool at_max_rounds;
};

/// With max_rounds > 0 the result is min(bound, max_rounds): the path search
/// stops as soon as it has found a path needing max_rounds rounds, which is
/// what keeps it cheap on programs whose true bound is in the thousands.
round_boundt compute_round_bound(
  const std::vector<round_bound_eventt> &events,
  const spawn_pointst &spawn_points,
  std::size_t max_rounds = 0);

/// The events of the blocks in the backward cone of the property blocks
/// (thread -> label of its last block holding an assertion). A violation in
/// block V depends only on what happens before V: keep V's thread up to V, and
/// for every read kept, every other thread up to its last write of the object
/// read (it may be the write read from) and its parent up to its spawn. The
/// run restricted to those blocks is still a run -- each kept read sees the
/// same last write, since only writes no kept read can see are gone -- and it
/// reaches V in the same state. So compute_round_bound on these events bounds
/// the rounds any violation needs, and never exceeds the bound on all events:
/// on a correct program that is where --infer-rounds may stop.
struct property_conet
{
  std::vector<round_bound_eventt> events;
  std::size_t blocks = 0;
  std::size_t total_blocks = 0;
};
property_conet property_cone(
  const std::vector<round_bound_eventt> &events,
  const spawn_pointst &spawn_points,
  const std::map<unsigned, unsigned> &property_blocks);

// ---------------------------------------------------------------------------
// --infer-rounds: the formula is built once with B rounds and the round count
// R is chosen by solver assumptions, never by rebuilding it.
// ---------------------------------------------------------------------------

/// The Boolean symbol lazy_po defines, under --infer-rounds, as
///   Empty_r <=> for every thread t and threshold i: GE(t,r,i) => GE(t,r-1,i)
/// i.e. no thread makes progress in round r (cs(t,r) = cs(t,r-1)). Assuming
/// Empty_r for every r > R makes the B-round formula equivalent to the R-round
/// one: Enabled, hence every exec, of those rounds is false, the canonicality
/// constraints of those rounds hold vacuously, and the tag chains that look
/// forward (WINR, NRP, FR) see no executed access there.
symbol_exprt empty_round_symbol(std::size_t round);

/// The number of rounds the last --infer-rounds formula was built with (B, the
/// static bound capped at --max-rounds), set by postprocess_equation for the
/// checker that then solves it; 0 when no such formula was built. One process
/// runs one verification, as for por_auxiliary_symbols().
std::size_t &infer_rounds_bound();
/// Whether that B is the static bound itself rather than the --max-rounds
/// cap: only then does reaching it make a SUCCESSFUL complete.
bool &infer_rounds_bound_is_static();

/// Experiment (LAZYPO_FIXPOINT=1): Boolean projection of the shared memory at
/// the end of the last round of the last --infer-rounds formula -- the bits of
/// the last lazy-chain value of every scalar shared variable, plus, with
/// LAZYPO_FIXPOINT_POS=1, the thresholds GE(t,B,i) of every thread's final
/// position. Locals and thread-private objects are not in it.
struct fixpoint_projectiont
{
  std::vector<exprt> bits;
  std::size_t position_bits = 0;
  std::size_t variables = 0;
  std::size_t skipped_variables = 0;
};
fixpoint_projectiont &fixpoint_projection();

#endif // CPROVER_GOTO_SYMEX_ROUND_BOUND_H
