/*******************************************************************\

Module: Spin-loop reduction

\*******************************************************************/

/// \file
/// See spin_loops.cpp.

#ifndef CPROVER_GOTO_PROGRAMS_SPIN_LOOPS_H
#define CPROVER_GOTO_PROGRAMS_SPIN_LOOPS_H

#include <cstddef>

class goto_modelt;

/// Cut the iterations of side-effect-free loops that change nothing.
/// \return the number of loops instrumented
std::size_t spin_loop_reduction(goto_modelt &goto_model);

#endif // CPROVER_GOTO_PROGRAMS_SPIN_LOOPS_H
