/*******************************************************************\

Module: SAT Modulo SAT backend for Glucose (opt-in, LAZYPO_SMS=1)

\*******************************************************************/

#include "satcheck_glucose_sms.h"

#include <algorithm>
#include <cstdlib>
#include <memory>

#include <util/invariant.h>
#include <util/make_unique.h>

#include <core/Solver.h>
#include <core/ShadowTheory.h>
#include <simp/SimpSolver.h>

#ifndef HAVE_GLUCOSE
#  error "Expected HAVE_GLUCOSE"
#endif

// Defined (non-static) in satcheck_glucose.cpp.
void convert(const bvt &bv, Glucose::vec<Glucose::Lit> &dest);

template <typename T>
satcheck_glucose_sms_baset<T>::satcheck_glucose_sms_baset(
  message_handlert &message_handler)
  : satcheck_glucose_baset<T>(message_handler)
{
  // CS-first (the POR fallback decision tier) does not apply to this backend.
  // It exists to keep the search complete when the POR canonicality clauses
  // live in the same formula as everything else: without the tier the solver
  // could exhaust the ordinary decision candidates while POR variables are
  // still unassigned in clauses that are not yet satisfied, and report a
  // partial model as SAT. Under SAT Modulo SAT that precondition is vacuous:
  //   - the master formula holds no canonicality clause at all (measured: of
  //     245682 POR-classified variables on ebs --rounds 8 --unwind 1, exactly
  //     20 occur in any master clause; 35209/42 on dcas, 7281/3 on tri),
  //   - the interface is not POR-classified either -- it is made of the base
  //     encoding literals the canonicality constraints read, so the tier never
  //     touches the variables the slave actually communicates on,
  //   - and a master model needs no confirmation anyway, because the slave is
  //     pruning-only and checkTheoriesOnModel() skips it outright.
  // What the tier does do here is exile ~10-16% of the master's variables --
  // the ones that occur in no master clause, because their defining clauses
  // went to the slave -- into a fallback heap whose activity is never bumped
  // (they appear in no learnt clause either), so they get decided only at
  // maximum depth and are thrown away by every restart. On ebs that is 245662
  // fallback-tier decisions and 270.7s against 82.4s with the tier off.
  // Master only: the slave never calls pickBranchLit() -- it only ever
  // enqueues, propagates and backtracks -- so its own flag is dead either way.
  this->solver->cs_first_enabled = false;
}

template <typename T>
satcheck_glucose_sms_baset<T>::~satcheck_glucose_sms_baset() = default;

template <typename T>
void satcheck_glucose_sms_baset<T>::add_clause_to_solver(const bvt &bv)
{
  Glucose::vec<Glucose::Lit> c;
  convert(bv, c);

  // Note the underscore: add without a superfluous internal copy.
  if(redirect_to_slave && slave != nullptr)
  {
    while((unsigned)slave->nVars() < this->no_variables())
      slave->newVar();
    var_in_slave.resize(this->no_variables(), 0);
    for(int i = 0; i < c.size(); i++)
      var_in_slave[Glucose::var(c[i])] = 1;
    slave->addClause_(c);
  }
  else
  {
    var_in_master.resize(this->no_variables(), 0);
    for(int i = 0; i < c.size(); i++)
      var_in_master[Glucose::var(c[i])] = 1;
    this->solver->addClause_(c);
  }
}

template <typename T>
void satcheck_glucose_sms_baset<T>::set_clause_redirect(bool on)
{
  if(on && slave == nullptr)
  {
    // Non-simplifying slave: eliminating variables in the lower module would
    // pull the interface variables out from under it.
    slave = util_make_unique<Glucose::Solver>();
    slave->verbosity = 0;
  }
  redirect_to_slave = on;
}

template <typename T>
void satcheck_glucose_sms_baset<T>::finalize_modules()
{
  if(slave == nullptr || slave_attached)
    return;

  // The interface is the set of variables that appear in BOTH modules. The
  // paper does not require them to be consecutive: an explicit set avoids
  // raking in the non-shared variables, as modsat's min..max range did.
  this->add_variables();
  while((unsigned)slave->nVars() < this->no_variables())
    slave->newVar();

  Glucose::vec<Glucose::Var> shared;
  const std::size_t n = std::min(var_in_master.size(), var_in_slave.size());
  for(std::size_t v = 0; v < n; v++)
    if(var_in_master[v] && var_in_slave[v])
      shared.push(static_cast<Glucose::Var>(v));

  this->log.statistics() << "SMS: master " << this->solver->nClauses()
                         << " clausole, slave " << slave->nClauses()
                         << " clausole, interfaccia " << shared.size()
                         << " variabili su " << this->no_variables()
                         << messaget::eom;

  // Canonicality can only remove models from the master, never add: a master
  // model is already a real counterexample and need not be confirmed. That
  // holds only for the default placement. Inverted, the slave holds the
  // program encoding and the master keeps just canonicality and the goal, so
  // a master model is a proposed schedule that the slave must confirm.
  // Pruning-only holds exactly when the slave carries canonicality and
  // nothing else: canonicality can only remove models, so a master model is
  // already a real execution. Any other class in there makes the slave
  // semantically necessary and its confirmation of each model mandatory.
  std::string slave_spec;
  if(const char *s = getenv("LAZYPO_SMS_SLAVE"))
    slave_spec = s;
  else if(const char *inv = getenv("LAZYPO_SMS_INVERT"))
    slave_spec = (inv[0] != '\0' && atoi(inv) >= 2) ? "data" : "data,conc";
  else
    slave_spec = "canon";
  const bool only_canon = (slave_spec == "canon");
  slave->setPruningOnly(only_canon);
  this->log.statistics()
    << "SMS: slave = {" << slave_spec << "}, "
    << (only_canon ? "pruning-only (models need no confirmation)"
                   : "semantically necessary (every model is confirmed)")
    << messaget::eom;
  slave->attachTo(this->solver.get(), shared);
  slave_attached = true;

  // The master still holds every variable, including those whose clauses all
  // went to the slave: they constrain nothing here and are not on the
  // interface, so deciding them is wasted work. Measured over
  // fib_unsafe-10..15, one solver at a time: 2083s -> 1960s, better on five of
  // six, never worse. LAZYPO_SMS_KEEP_DEAD restores the old behaviour.
  if(getenv("LAZYPO_SMS_KEEP_DEAD") == nullptr)
  {
    const int dead = this->solver->disableNonModuleDecisions();
    this->log.statistics() << "SMS: " << dead
                           << " variabili del master non vincolate, escluse "
                              "dalle decisioni" << messaget::eom;
  }
}

template <typename T>
void satcheck_glucose_sms_baset<T>::before_solve()
{
  // DPLL(T) scaffold validator: a shadow theory that receives copies of clauses
  // already in the formula. Semantically neutral by construction, but it
  // exercises markers, lazy reasons, conflict analysis and backtracking.
  // LAZYPO_SMS_SHADOW=<n> = how many clauses to shadow.
  if(shadow_theory == nullptr)
  {
    if(const char *n = getenv("LAZYPO_SMS_SHADOW"))
    {
      shadow_theory = util_make_unique<Glucose::ShadowTheory>(*this->solver);
      this->solver->addTheory(shadow_theory.get());
      shadow_theory->setup(atoi(n));
      this->log.statistics()
        << "teoria-ombra: " << shadow_theory->size()
        << " clausole spostate nella teoria" << messaget::eom;
    }
  }
}

template <typename T>
void satcheck_glucose_sms_baset<T>::after_solve(bool /*sat_result*/)
{
  if(slave != nullptr)
    this->log.statistics()
      << "SMS slave: conflitti di interfaccia " << slave->stats_slave_conflicts
      << ", letterali rimandati al master " << slave->stats_slave_up
      << ", reason materializzate " << slave->stats_slave_reasons
      << ", propagazioni a livello 0 " << slave->stats_slave_up_level0
      << (slave->stats_slave_conflicts == 0 && slave->stats_slave_reasons == 0 &&
              slave->stats_slave_up_level0 == 0
            ? "  [refutazione POR-free: il master non ha mai usato lo slave]"
            : "")
      << ", conferme sul modello totale evitate "
      << this->solver->stats_model_checks_skipped
      << ", modelli con variabili private non decise "
      << slave->stats_slave_incomplete << " (al massimo "
      << slave->stats_slave_undecided_max
      << " variabili per modello, di cui tag POR veri: "
      << slave->stats_slave_undecided_por << ")" << messaget::eom;

  if(slave != nullptr)
    this->log.statistics()
      << "SMS profilo: interrogazioni allo slave " << slave->stats_theory_calls
      << ", di cui con almeno un letterale nuovo "
      << slave->stats_theory_calls_fed << " ("
      << (slave->stats_theory_calls ? 100.0 * slave->stats_theory_calls_fed /
                                        slave->stats_theory_calls
                                    : 0.0)
      << "%), letterali entrati " << slave->stats_theory_lits_in
      << ", di cui rimandate dal gate " << slave->stats_theory_calls_gated
      << ", propagazioni interne dello slave " << slave->propagations
      << " (master " << this->solver->propagations << ")" << messaget::eom;

  if(slave != nullptr && slave->slave_undecided_vars.size() > 0)
  {
    auto &out = this->log.statistics();
    out << "SMS slave: variabili private non decise:";
    for(int i = 0; i < slave->slave_undecided_vars.size(); i++)
      out << ' ' << slave->slave_undecided_vars[i];
    out << messaget::eom;
  }

  if(shadow_theory != nullptr)
    this->log.statistics()
      << "teoria-ombra: propagazioni " << shadow_theory->propagations()
      << ", conflitti " << shadow_theory->conflicts() << ", reason costruite "
      << shadow_theory->reasons_built() << messaget::eom;
}

template class satcheck_glucose_sms_baset<Glucose::Solver>;
template class satcheck_glucose_sms_baset<Glucose::SimpSolver>;

const std::string satcheck_glucose_sms_no_simplifiert::solver_text()
{
  return "Glucose Syrup without simplifier (SAT Modulo SAT)";
}

const std::string satcheck_glucose_sms_simplifiert::solver_text()
{
  return "Glucose Syrup with simplifier (SAT Modulo SAT)";
}

void satcheck_glucose_sms_simplifiert::set_frozen(literalt a)
{
  try
  {
    if(!a.is_constant())
    {
      add_variables();
      solver->setFrozen(a.var_no(), true);
    }
  }
  catch(Glucose::OutOfMemoryException)
  {
    log.error() << "SAT checker ran out of memory" << messaget::eom;
    status = statust::ERROR;
    throw std::bad_alloc();
  }
}

bool satcheck_glucose_sms_simplifiert::is_eliminated(literalt a) const
{
  PRECONDITION(!a.is_constant());

  return solver->isEliminated(a.var_no());
}
