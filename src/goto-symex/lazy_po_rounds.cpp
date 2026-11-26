/// \file
/// lazy_po: the round count -- static round bound (round_bound.h) and the
/// empty-round symbols --infer-rounds chooses the round count with.

#include "lazy_po.h"

#include <cstdlib>

#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/std_expr.h>

#include "lazy_po_internal.h"
#include "round_bound.h"

std::vector<round_bound_eventt> lazy_pot::round_bound_events() const
{
  std::vector<round_bound_eventt> events;
  for(const auto &entry : reads)
    for(const auto &e : entry.second)
      events.push_back({entry.first, e.thread, e.label, false});
  for(const auto &entry : writes)
    for(const auto &e : entry.second)
      events.push_back({entry.first, e.thread, e.label, true});
  return events;
}

round_boundt lazy_pot::bound_from_events(std::size_t max_rounds) const
{
  return compute_round_bound(round_bound_events(), spawn_points, max_rounds);
}

property_conet lazy_pot::property_cone_events() const
{
  // Every assertion gets a block of its own (collect_reads_and_writes), so
  // the property blocks are those of the blocking events that assert.
  std::map<unsigned, unsigned> property_blocks;
  for(const auto &e : blocking_events)
    if(e.s_it->is_assert())
    {
      unsigned &last = property_blocks[e.thread];
      last = std::max(last, e.label);
    }
  return property_cone(round_bound_events(), spawn_points, property_blocks);
}

std::size_t lazy_pot::static_round_bound(
  symex_target_equationt &equation,
  std::size_t max_rounds,
  bool &at_cap)
{
  // Exactly the first two steps of operator(): the labels, the blocks and the
  // spawn points are the ones the real construction will see.
  handling_active_threads(equation);
  collect_reads_and_writes(equation.SSA_steps);
  const round_boundt bound = bound_from_events(max_rounds);
  at_cap = bound.at_max_rounds;
  return bound.path;
}

// Empty_r <=> no thread makes progress in round r. "cs order monotonicity
// (round)" already gives GE(t,r-1,i) => GE(t,r,i), so the converse over the
// same thresholds -- those create_cs_constraint emits, 1..labels[t]+1 -- is
// cs(t,r) = cs(t,r-1) for every t. Round 1 is never switched off: R >= 1.
void lazy_pot::create_empty_round_literals(symex_target_equationt &equation)
{
  for(std::size_t round = 2; round <= rounds; ++round)
  {
    exprt::operandst unchanged;
    for(unsigned thread = 0; thread <= threads; ++thread)
    {
      const unsigned max_num = labels[thread];
      for(unsigned i = 1; i <= max_num + 1; ++i)
        unchanged.push_back(implies_exprt{
          create_ge_symbol(thread, round, i),
          create_ge_symbol(thread, round - 1, i)});
    }
    equation.constraint(
      equal_exprt{empty_round_symbol(round), conjunction(unchanged)},
      "empty round",
      equation.SSA_steps.begin()->source);
  }
}
