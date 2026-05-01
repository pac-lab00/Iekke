/*******************************************************************\

Module: SMS backend via Z3 fork (z3/src/sat/sms/)

\*******************************************************************/

#include <unordered_map>

#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/reg_decl_plugins.h"
#include "util/params.h"
#include "util/symbol.h"
#include "util/lbool.h"
#include "sat/sms/sms_solver.h"

namespace z3i {
  using ast_manager_t = ::ast_manager;
  using params_ref_t = ::params_ref;
  using expr_t = ::expr;
  using expr_ref_t = ::expr_ref;
  using expr_ref_vector_t = ::expr_ref_vector;
  using symbol_t = ::symbol;
  using lbool_t = ::lbool;
  using sat_mod_sat_t = ::sat::sat_mod_sat;
}

#include "satcheck_sms_z3.h"

#include <util/invariant.h>
#include <util/make_unique.h>
#include <util/threeval.h>

#include <iostream>
#include <limits>
#include <string>

static void ensure_z3_runtime_initialized()
{
  static bool initialized = false;
  if(!initialized)
  {
    ::memory::initialize(UINT_MAX);
    initialized = true;
  }
}

struct sms_z3_implt
{
  std::unique_ptr<z3i::ast_manager_t> m_ptr;
  z3i::ast_manager_t &m;
  z3i::params_ref_t params;
  z3i::expr_ref_vector_t var_expr;
  z3i::expr_ref_vector_t master_clauses;
  z3i::expr_ref_vector_t slave_clauses;
  z3i::expr_ref_vector_t shared_vars;
  bool solved = false;
  bool last_sat = false;

  std::unique_ptr<z3i::sat_mod_sat_t> engine;

  sms_z3_implt()
    : m_ptr((ensure_z3_runtime_initialized(),
             std::make_unique<z3i::ast_manager_t>())),
      m(*m_ptr),
      params(),
      var_expr(m),
      master_clauses(m),
      slave_clauses(m),
      shared_vars(m)
  {
    ::reg_decl_plugins(m);
    params.set_bool("minimize_lemmas", false);
    params.set_uint("backtrack.conflicts", UINT_MAX);
    params.set_bool("iekke_fast", true);
  }

  z3i::expr_t *expr_for(unsigned var_no)
  {
    while(var_expr.size() <= var_no)
    {
      std::string name = "v" + std::to_string(var_expr.size());
      z3i::expr_t *e = m.mk_const(z3i::symbol_t(name.c_str()), m.mk_bool_sort());
      var_expr.push_back(e);
    }
    return var_expr.get(var_no);
  }

  z3i::expr_ref_t lit_to_expr(literalt l)
  {
    z3i::expr_t *base = expr_for(l.var_no());
    return z3i::expr_ref_t(l.sign() ? m.mk_not(base) : base, m);
  }

  z3i::expr_ref_t clause_to_expr(const bvt &bv)
  {
    z3i::expr_ref_vector_t lits(m);
    std::unordered_map<unsigned, bool> seen;
    for(const auto &l : bv)
    {
      if(l.is_true())
        return z3i::expr_ref_t(m.mk_true(), m);
      if(l.is_false())
        continue;
      auto it = seen.find(l.var_no());
      if(it != seen.end())
      {
        if(it->second != l.sign())
          return z3i::expr_ref_t(m.mk_true(), m);
        continue;
      }
      seen.emplace(l.var_no(), l.sign());
      lits.push_back(lit_to_expr(l));
    }
    if(lits.empty())
      return z3i::expr_ref_t(m.mk_false(), m);
    if(lits.size() == 1)
      return z3i::expr_ref_t(lits.get(0), m);
    return z3i::expr_ref_t(m.mk_or(lits.size(), lits.data()), m);
  }
};

sms_z3_solvert::sms_z3_solvert(message_handlert &message_handler)
  : cnf_solvert(message_handler),
    impl(util_make_unique<sms_z3_implt>()),
    time_limit_seconds(0)
{
}

sms_z3_solvert::~sms_z3_solvert() = default;

const std::string sms_z3_solvert::solver_text()
{
  return "Z3 SMS (SAT modulo SAT, z3 fork backend)";
}

tvt sms_z3_solvert::l_get(literalt a) const
{
  if(a.is_true())
    return tvt(true);
  if(a.is_false())
    return tvt(false);

  if(!impl->solved || !impl->last_sat || !impl->engine)
    return tvt::unknown();

  if(a.var_no() >= impl->var_expr.size())
    return tvt::unknown();

  z3i::expr_t *e = impl->var_expr.get(a.var_no());
  z3i::lbool_t v = impl->engine->value_of(e);

  tvt result;
  if(v == l_true)
    result = tvt(true);
  else if(v == l_false)
    result = tvt(false);
  else
    return tvt::unknown();

  if(a.sign())
    result = !result;
  return result;
}

void sms_z3_solvert::lcnf(const bvt &bv)
{
  for(const auto &l : bv)
    if(l.is_true())
      return;

  for(const auto &l : bv)
    if(!l.is_constant())
      impl->expr_for(l.var_no());

  z3i::expr_ref_t cls = impl->clause_to_expr(bv);

  if(impl->m.is_true(cls.get()))
    return;

  if(redirect_to_slave)
  {
    impl->slave_clauses.push_back(cls.get());
  }
  else
  {
    impl->master_clauses.push_back(cls.get());
    clause_counter++;
  }
}

void sms_z3_solvert::attach_slave(const bvt &shared_vars)
{
  if(no_variables() == 0)
    return;
  for(const auto &l : shared_vars)
  {
    if(l.is_constant())
      continue;
    impl->shared_vars.push_back(impl->expr_for(l.var_no()));
  }
  slave_attached = true;
}

propt::resultt sms_z3_solvert::do_prop_solve()
{
  PRECONDITION(status != statust::ERROR);

  log.statistics() << (no_variables() - 1) << " variables, "
                   << impl->master_clauses.size() << " master clauses, "
                   << impl->slave_clauses.size() << " slave clauses"
                   << messaget::eom;

  for(const auto &assumption : assumptions)
  {
    if(assumption.is_false())
    {
      status = statust::UNSAT;
      return resultt::P_UNSATISFIABLE;
    }
  }

  impl->engine = std::make_unique<z3i::sat_mod_sat_t>(impl->m, impl->params);

  z3i::expr_ref_vector_t all_master(impl->m);
  for(unsigned i = 0; i < impl->master_clauses.size(); i++)
    all_master.push_back(impl->master_clauses.get(i));
  for(const auto &a : assumptions)
  {
    if(a.is_true())
      continue;
    z3i::expr_ref_t er = impl->lit_to_expr(a);
    all_master.push_back(er.get());
  }

  z3i::expr_ref_t formA(impl->m);
  if(all_master.empty())
    formA = impl->m.mk_true();
  else if(all_master.size() == 1)
    formA = all_master.get(0);
  else
    formA = impl->m.mk_and(all_master.size(), all_master.data());

  z3i::expr_ref_t formB(impl->m);
  if(impl->slave_clauses.empty())
    formB = impl->m.mk_true();
  else if(impl->slave_clauses.size() == 1)
    formB = impl->slave_clauses.get(0);
  else
    formB = impl->m.mk_and(impl->slave_clauses.size(), impl->slave_clauses.data());

  bool sat_result = impl->engine->solve(formA, formB, impl->shared_vars);

  impl->solved = true;
  impl->last_sat = sat_result;

  if(sat_result)
  {
    log.status() << "SAT checker: instance is SATISFIABLE" << messaget::eom;
    status = statust::SAT;
    return resultt::P_SATISFIABLE;
  }
  else
  {
    log.status() << "SAT checker: instance is UNSATISFIABLE" << messaget::eom;
    status = statust::UNSAT;
    return resultt::P_UNSATISFIABLE;
  }
}

void sms_z3_solvert::set_assignment(literalt a, bool /*value*/)
{
  PRECONDITION(!a.is_constant());
}

void sms_z3_solvert::set_assumptions(const bvt &bv)
{
  assumptions.clear();
  for(const auto &assumption : bv)
  {
    if(!assumption.is_true())
      assumptions.push_back(assumption);
  }
}

bool sms_z3_solvert::is_in_conflict(literalt a) const
{
  if(!impl->solved || impl->last_sat || !impl->engine)
    return false;
  if(a.var_no() >= impl->var_expr.size())
    return false;
  return impl->engine->in_conflict(impl->var_expr.get(a.var_no()));
}
