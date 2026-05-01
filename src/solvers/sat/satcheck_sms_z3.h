/*******************************************************************\

Module: SMS (SAT modulo SAT) backend via Z3 fork

Wrapper that uses Z3's `sat::sat_mod_sat` (in z3/src/sat/sms/) as the
SMS engine instead of modsat. Same public interface as `sms_solvert`
to be drop-in compatible with the existing solver factory wiring.

PImpl isolates the heavy Z3 includes (ast_manager, expr_ref_vector,
sms_solver) from the rest of CBMC.

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SAT_SATCHECK_SMS_Z3_H
#define CPROVER_SOLVERS_SAT_SATCHECK_SMS_Z3_H

#include "cnf.h"

#include <solvers/hardness_collector.h>

#include <memory>

struct sms_z3_implt;

class sms_z3_solvert : public cnf_solvert, public hardness_collectort
{
public:
  explicit sms_z3_solvert(message_handlert &message_handler);
  ~sms_z3_solvert() override;

  const std::string solver_text() override;

  tvt l_get(literalt a) const override final;
  void lcnf(const bvt &bv) override final;
  void set_assignment(literalt a, bool value) override;
  void set_assumptions(const bvt &_assumptions) override;
  bool is_in_conflict(literalt a) const override;
  bool has_set_assumptions() const override final { return true; }
  bool has_is_in_conflict() const override final { return true; }

  void set_time_limit_seconds(uint32_t lim) override
  {
    time_limit_seconds = lim;
  }

  /// Subsequent lcnf() calls go to slave instead of master.
  bool redirect_to_slave = false;

  /// Wire slave as theory of master after both formulas loaded.
  /// shared_vars: SAT vars shared between master and slave.
  void attach_slave(const bvt &shared_vars);

protected:
  resultt do_prop_solve() override;

  std::unique_ptr<sms_z3_implt> impl;
  uint32_t time_limit_seconds;
  bvt assumptions;
  bool slave_attached = false;
};

#endif // CPROVER_SOLVERS_SAT_SATCHECK_SMS_Z3_H
