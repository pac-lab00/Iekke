/*******************************************************************\

Module: Loop-independent data-race freedom check

\*******************************************************************/

/// \file
/// See static_race_check.cpp.

#ifndef CPROVER_GOTO_PROGRAMS_STATIC_RACE_CHECK_H
#define CPROVER_GOTO_PROGRAMS_STATIC_RACE_CHECK_H

#include <string>

class goto_modelt;

/// "RACE-FREE" when no two conflicting accesses can run concurrently
/// unordered and unprotected, else "UNKNOWN (reason)".
std::string static_race_check(const goto_modelt &goto_model);

#endif // CPROVER_GOTO_PROGRAMS_STATIC_RACE_CHECK_H
