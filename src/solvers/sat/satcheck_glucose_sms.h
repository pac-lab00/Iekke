/*******************************************************************\

Module: SAT Modulo SAT backend for Glucose (opt-in, LAZYPO_SMS=1)

 The plain in-process Glucose backend lives in satcheck_glucose.{h,cpp} and
 knows nothing about this. Here the canonicality constraints of the round-
 bounded POR are kept OUT of the master formula and put into a separate slave
 solver, attached to the master as a DPLL(T) theory over the shared interface
 variables. The master formula is then exactly the plain encoding.

 Selected by solver_factory when LAZYPO_SMS is set in the environment.

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SAT_SATCHECK_GLUCOSE_SMS_H
#define CPROVER_SOLVERS_SAT_SATCHECK_GLUCOSE_SMS_H

#include "satcheck_glucose.h"

#include <vector>

namespace Glucose // NOLINT(readability/namespace)
{
class ShadowTheory; // NOLINT(readability/identifiers)
}

template <typename T>
class satcheck_glucose_sms_baset : public satcheck_glucose_baset<T>
{
public:
  explicit satcheck_glucose_sms_baset(message_handlert &message_handler);
  ~satcheck_glucose_sms_baset() override;

  /// From now on lcnf() routes clauses to the slave module (bmc_util calls this
  /// around convert_canonical_constraints()).
  void set_clause_redirect(bool on) override;
  /// All clauses loaded: attach master and slave on the shared interface.
  void finalize_modules() override;

protected:
  void add_clause_to_solver(const bvt &bv) override;
  void before_solve() override;
  void after_solve(bool sat_result) override;

  // The slave module: holds the canonicality clauses, attached to `solver` (the
  // master) as a pruning-only theory.
  std::unique_ptr<Glucose::Solver> slave;
  // DPLL(T) scaffold validator, opt-in with LAZYPO_SMS_SHADOW=<n>.
  std::unique_ptr<Glucose::ShadowTheory> shadow_theory;
  bool redirect_to_slave = false;
  bool slave_attached = false;
  std::vector<char> var_in_master, var_in_slave;
};

class satcheck_glucose_sms_no_simplifiert
  : public satcheck_glucose_sms_baset<Glucose::Solver>
{
public:
  using satcheck_glucose_sms_baset<
    Glucose::Solver>::satcheck_glucose_sms_baset;
  const std::string solver_text() override;
};

class satcheck_glucose_sms_simplifiert
  : public satcheck_glucose_sms_baset<Glucose::SimpSolver>
{
public:
  using satcheck_glucose_sms_baset<
    Glucose::SimpSolver>::satcheck_glucose_sms_baset;
  const std::string solver_text() override;
  void set_frozen(literalt a) override;
  bool is_eliminated(literalt a) const;
};

#endif // CPROVER_SOLVERS_SAT_SATCHECK_GLUCOSE_SMS_H
