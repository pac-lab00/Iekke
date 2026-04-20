/*******************************************************************\

Module: SMS (SAT modulo SAT) via modsat

Wrapper con master+slave: il master contiene la formula principale,
lo slave i canonical constraints. Le variabili condivise sono mappate
tramite un unico prop_conv_solvert (stessi var_no in entrambi).

ATTENZIONE: questo header non deve essere incluso insieme a
satcheck_minisat2.h nello stesso translation unit, perche' entrambi
definirebbero Minisat::Solver con interfacce incompatibili.
L'implementazione (satcheck_sms.cpp) usa PImpl per isolare modsat.

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SAT_SATCHECK_SMS_H
#define CPROVER_SOLVERS_SAT_SATCHECK_SMS_H

#include "cnf.h"

#include <solvers/hardness_collector.h>

#include <memory>

struct sms_implt;

class sms_solvert : public cnf_solvert, public hardness_collectort
{
public:
  explicit sms_solvert(message_handlert &message_handler);
  ~sms_solvert() override;

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

  /// Quando true, le successive chiamate a lcnf() vanno allo slave
  /// invece che al master. Usato per separare i canonical constraints.
  bool redirect_to_slave = false;

  /// Dopo aver caricato tutte le clausole in master e slave,
  /// collega lo slave come Theory del master.
  /// \param shared_vars: le variabili SAT condivise tra le due formule
  void attach_slave(const bvt &shared_vars);

protected:
  resultt do_prop_solve() override;

  std::unique_ptr<sms_implt> impl;
  uint32_t time_limit_seconds;

  void add_variables_master();
  void add_variables_slave();
  bvt assumptions;

  bool slave_attached = false;
};

#endif // CPROVER_SOLVERS_SAT_SATCHECK_SMS_H
