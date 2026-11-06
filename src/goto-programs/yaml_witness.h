/*******************************************************************\

Module: Violation Witnesses in the YAML Format

\*******************************************************************/

/// \file
/// Violation witnesses in the YAML format of sv-witnesses (version 2.2)

#ifndef CPROVER_GOTO_PROGRAMS_YAML_WITNESS_H
#define CPROVER_GOTO_PROGRAMS_YAML_WITNESS_H

#include <iosfwd>

class goto_tracet;
class namespacet;

/// Write the `content` of a `violation_sequence` for \p goto_trace: one
/// follow segment per thread creation, then the final segment with the
/// violation. The metadata (task, hashes, specification, data model) is not
/// known here and is left to the caller, which writes the entry around it.
/// \return false, writing nothing, when the trace has no violation a witness
///   can point to (it ends in a built-in location, or a thread that executes a
///   waypoint was never registered by a thread creation in the witness)
bool yaml_violation_content(
  const goto_tracet &goto_trace,
  const namespacet &ns,
  std::ostream &out);

#endif // CPROVER_GOTO_PROGRAMS_YAML_WITNESS_H
