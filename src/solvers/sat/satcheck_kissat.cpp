/// \file
/// Backend SAT in-process basato su kissat.

#include "satcheck_kissat.h"

#include <util/exception_utils.h>
#include <util/invariant.h>
#include <util/threeval.h>

#ifdef HAVE_KISSAT

extern "C"
{
#include <kissat.h>
}

tvt satcheck_kissatt::l_get(literalt a) const
{
  if(a.is_constant())
    return tvt(a.sign());

  if(!solved)
    return tvt(tvt::tv_enumt::TV_UNKNOWN);

  const int val = kissat_value(solver, a.dimacs());
  if(val > 0)
    return tvt(true);
  else if(val < 0)
    return tvt(false);

  return tvt(tvt::tv_enumt::TV_UNKNOWN);
}

const std::string satcheck_kissatt::solver_text()
{
  return std::string("kissat ") + kissat_version();
}

void satcheck_kissatt::lcnf(const bvt &bv)
{
  for(const auto &lit : bv)
  {
    if(lit.is_true())
      return;
    else if(!lit.is_false())
      INVARIANT(lit.var_no() < no_variables(), "reject out of bound variables");
  }

  for(const auto &lit : bv)
    if(!lit.is_false())
      kissat_add(solver, lit.dimacs());

  kissat_add(solver, 0); // chiude la clausola

  if(solver_hardness)
  {
    static size_t cnf_clause_index = 0;
    bvt cnf;
    bool clause_removed = process_clause(bv, cnf);

    if(!clause_removed)
      cnf_clause_index++;

    solver_hardness->register_clause(
      bv, cnf, cnf_clause_index, !clause_removed);
  }

  clause_counter++;
}

propt::resultt satcheck_kissatt::do_prop_solve()
{
  INVARIANT(status != statust::ERROR, "there cannot be an error");

  // kissat non e' incrementale: le assumption sono gia' state consumate come
  // clausole unitarie, quindi un secondo solve risolverebbe un'istanza diversa
  // da quella richiesta senza segnalarlo.
  INVARIANT(
    !solved, "kissat is not incremental: prop_solve() can only be called once");

  log.statistics() << (no_variables() - 1) << " variables, " << clause_counter
                   << " clauses" << messaget::eom;

  // un'assumption falsa rende l'istanza insoddisfacibile per costruzione
  for(const auto &a : assumptions)
  {
    if(a.is_false())
    {
      log.status() << "got FALSE as assumption: instance is UNSATISFIABLE"
                   << messaget::eom;
      status = statust::UNSAT;
      return resultt::P_UNSATISFIABLE;
    }
  }

  // le assumption diventano clausole unitarie a livello 0
  for(const auto &a : assumptions)
  {
    if(!a.is_constant())
    {
      kissat_add(solver, a.dimacs());
      kissat_add(solver, 0);
      clause_counter++;
    }
  }

  const int res = kissat_solve(solver);
  solved = true;

  switch(res)
  {
  case 10:
    log.status() << "SAT checker: instance is SATISFIABLE" << messaget::eom;
    status = statust::SAT;
    return resultt::P_SATISFIABLE;
  case 20:
    log.status() << "SAT checker: instance is UNSATISFIABLE" << messaget::eom;
    break;
  default:
    log.status() << "SAT checker: solving returned without solution"
                 << messaget::eom;
    throw analysis_exceptiont(
      "solving inside kissat SAT solver has been interrupted");
  }

  status = statust::UNSAT;
  return resultt::P_UNSATISFIABLE;
}

void satcheck_kissatt::set_assignment(literalt a, bool value)
{
  INVARIANT(!a.is_constant(), "cannot set an assignment for a constant");
  INVARIANT(false, "method not supported");
}

satcheck_kissatt::satcheck_kissatt(message_handlert &message_handler)
  : cnf_solvert(message_handler), solver(kissat_init())
{
}

satcheck_kissatt::~satcheck_kissatt()
{
  kissat_release(solver);
}

void satcheck_kissatt::set_assumptions(const bvt &bv)
{
  assumptions.clear();
  for(const auto &assumption : bv)
    if(!assumption.is_true())
      assumptions.push_back(assumption);
}

bool satcheck_kissatt::is_in_conflict(literalt a) const
{
  UNIMPLEMENTED;
}

#endif
