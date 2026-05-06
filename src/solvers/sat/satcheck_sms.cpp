#include "satcheck_sms.h"

#include <limits>

#include <util/invariant.h>
#include <util/make_unique.h>
#include <util/threeval.h>


#include "../../../modsat/core/Solver.h"

struct sms_implt
{
  Minisat::Solver master;
  Minisat::Solver slave;
};

static void convert_bv(const bvt &bv, Minisat::vec<Minisat::Lit> &dest)
{
  PRECONDITION(
    bv.size() <= static_cast<std::size_t>(std::numeric_limits<int>::max()));
  dest.capacity(static_cast<int>(bv.size()));

  for(const auto &literal : bv)
  {
    if(!literal.is_false())
      dest.push(Minisat::mkLit(literal.var_no(), literal.sign()));
  }
}

sms_solvert::sms_solvert(message_handlert &message_handler)
  : cnf_solvert(message_handler),
    impl(util_make_unique<sms_implt>()),
    time_limit_seconds(0)
{
}

sms_solvert::~sms_solvert() = default;

const std::string sms_solvert::solver_text()
{
  return "ModSAT SMS (SAT modulo SAT)";
}

void sms_solvert::add_variables_master()
{
  while((unsigned)impl->master.nVars() < no_variables())
    impl->master.newVar();
}

void sms_solvert::add_variables_slave()
{
  while((unsigned)impl->slave.nVars() < no_variables())
    impl->slave.newVar();
}

tvt sms_solvert::l_get(literalt a) const
{
  if(a.is_true())
    return tvt(true);
  if(a.is_false())
    return tvt(false);

  if(a.var_no() >= (unsigned)impl->master.model.size())
    return tvt::unknown();

  using Minisat::lbool;

  tvt result;
  if(impl->master.model[a.var_no()] == l_True)
    result = tvt(true);
  else if(impl->master.model[a.var_no()] == l_False)
    result = tvt(false);
  else
    return tvt::unknown();

  if(a.sign())
    result = !result;

  return result;
}

void sms_solvert::lcnf(const bvt &bv)
{
  try
  {
    for(const auto &literal : bv)
    {
      if(literal.is_true())
        return;
    }

    Minisat::vec<Minisat::Lit> c;
    convert_bv(bv, c);

    if(redirect_to_slave)
    {
      add_variables_slave();
      impl->slave.addClause_(c);
    }
    else
    {
      add_variables_master();
      impl->master.addClause_(c);
      clause_counter++;
    }
  }
  catch(const Minisat::OutOfMemoryException &)
  {
    log.error() << "SAT checker ran out of memory" << messaget::eom;
    status = statust::ERROR;
    throw std::bad_alloc();
  }
}

void sms_solvert::attach_slave(const bvt &shared_vars)
{
  add_variables_master();
  add_variables_slave();

  if(no_variables() == 0)
    return;

  // modsat::attachTo treats [super_vars[0], super_vars.last()] as the shared
  // range and uses super_offset = super_vars[0] - local_vars[0]. Master and
  // slave share the same prop_conv_solvert, so var_no matches 1:1 and offset
  // is 0. Compute the consecutive bounding range over the non-constant shared
  // literals provided by the caller.
  int min_var = std::numeric_limits<int>::max();
  int max_var = -1;
  for(const auto &lit : shared_vars)
  {
    if(lit.is_constant())
      continue;
    int v = static_cast<int>(lit.var_no());
    if(v < min_var)
      min_var = v;
    if(v > max_var)
      max_var = v;
  }

  if(max_var < 0)
    return;

  Minisat::vec<Minisat::Var> super_vars_v, local_vars_v;
  super_vars_v.push(min_var);
  super_vars_v.push(max_var);
  local_vars_v.push(min_var);
  local_vars_v.push(max_var);

  impl->master.addTheory(&impl->slave);
  impl->slave.attachTo(&impl->master, super_vars_v, local_vars_v);
  slave_attached = true;
}

propt::resultt sms_solvert::do_prop_solve()
{
  PRECONDITION(status != statust::ERROR);

  log.statistics() << (no_variables() - 1) << " variables, "
                   << impl->master.nClauses() << " master clauses, "
                   << impl->slave.nClauses() << " slave clauses"
                   << messaget::eom;

  try
  {
    add_variables_master();

    if(!impl->master.okay())
    {
      log.status() << "SAT checker inconsistent: instance is UNSATISFIABLE"
                   << messaget::eom;
      status = statust::UNSAT;
      return resultt::P_UNSATISFIABLE;
    }

    for(const auto &assumption : assumptions)
    {
      if(assumption.is_false())
      {
        status = statust::UNSAT;
        return resultt::P_UNSATISFIABLE;
      }
    }

    Minisat::vec<Minisat::Lit> solver_assumptions;
    convert_bv(assumptions, solver_assumptions);

    using Minisat::lbool;

    lbool solver_result = impl->master.solveLimited(solver_assumptions);

    if(solver_result == l_True)
    {
      log.status() << "SAT checker: instance is SATISFIABLE" << messaget::eom;
      status = statust::SAT;
      return resultt::P_SATISFIABLE;
    }

    if(solver_result == l_False)
    {
      log.status() << "SAT checker: instance is UNSATISFIABLE" << messaget::eom;
      status = statust::UNSAT;
      return resultt::P_UNSATISFIABLE;
    }

    log.status() << "SAT checker: timed out or other error" << messaget::eom;
    status = statust::ERROR;
    return resultt::P_ERROR;
  }
  catch(const Minisat::OutOfMemoryException &)
  {
    log.error() << "SAT checker ran out of memory" << messaget::eom;
    status = statust::ERROR;
    return resultt::P_ERROR;
  }
}

void sms_solvert::set_assignment(literalt a, bool value)
{
  PRECONDITION(!a.is_constant());
  unsigned v = a.var_no();
  bool sign = a.sign();
  impl->master.model.growTo(v + 1);
  value ^= sign;
  impl->master.model[v] = Minisat::lbool(value);
}

void sms_solvert::set_assumptions(const bvt &bv)
{
  assumptions.clear();
  for(const auto &assumption : bv)
  {
    if(!assumption.is_true())
      assumptions.push_back(assumption);
  }
}

bool sms_solvert::is_in_conflict(literalt a) const
{
  int v = a.var_no();
  for(int i = 0; i < impl->master.conflict.size(); i++)
    if(var(impl->master.conflict[i]) == v)
      return true;
  return false;
}
