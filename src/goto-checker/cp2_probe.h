/*******************************************************************\

Module: CP2PROBE, where symbolic execution leaves values non-constant

\*******************************************************************/

/// \file
/// CP2PROBE: where symbolic execution leaves values non-constant. A
/// measurement only, printed on stdout when the environment variable CP2PROBE
/// is set; it changes nothing in the equation.
///
/// Part 1 classifies every shared read event by the writes to its object
/// (field-sensitive L1 leaf, overlap with enclosing and enclosed objects
/// included) that the equation records after the first spawn:
///   frozen   no shared write after the first spawn;
///   self0    every such write is by the reading thread, which is main;
///   selfN    every such write is by the reading thread, not main;
///   sameconst every such write, and the last write before the spawn, store
///            one and the same constant;
///   multi    the rest.
///
/// Part 2 re-propagates constants over the finished SSA equation (it is in
/// SSA form, so every symbol has one definition) and counts the assignments
/// whose right-hand side symex left non-constant but which fold to a constant
/// once the constants known for the symbols it mentions are substituted and
/// the result simplified -- by kind of assignment. Run twice: with shared
/// reads unknown ("exact"), and with frozen/sameconst reads given their value
/// ("seeded"), to see what reading those as constants would be worth.

#ifndef CPROVER_GOTO_CHECKER_CP2_PROBE_H
#define CPROVER_GOTO_CHECKER_CP2_PROBE_H

class namespacet;
class symex_target_equationt;

void cp2_constant_probe(
  const symex_target_equationt &equation,
  const namespacet &ns);

#endif // CPROVER_GOTO_CHECKER_CP2_PROBE_H
