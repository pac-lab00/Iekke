/// \file
/// Backend SAT in-process basato su kissat.
///
/// kissat non e' incrementale: non offre solve-sotto-assumption ne' analisi del
/// conflitto finale. Le assumption vengono quindi aggiunte come clausole
/// unitarie immediatamente prima della risoluzione, esattamente come fa il path
/// esterno (external_satt::write_cnf_file). La conseguenza e' che l'istanza puo'
/// essere risolta una sola volta: un secondo prop_solve() con assumption diverse
/// sarebbe scorretto, ed e' impedito da un invariante.

#ifndef CPROVER_SOLVERS_SAT_SATCHECK_KISSAT_H
#define CPROVER_SOLVERS_SAT_SATCHECK_KISSAT_H

#include "cnf.h"

#include <solvers/hardness_collector.h>

// NOLINTNEXTLINE(readability/identifiers)
struct kissat;

class satcheck_kissatt : public cnf_solvert, public hardness_collectort
{
public:
  explicit satcheck_kissatt(message_handlert &message_handler);
  virtual ~satcheck_kissatt();

  const std::string solver_text() override;
  tvt l_get(literalt a) const override;

  void lcnf(const bvt &bv) override;
  void set_assignment(literalt a, bool value) override;

  void set_assumptions(const bvt &_assumptions) override;
  bool has_set_assumptions() const override
  {
    return true;
  }

  // kissat non espone il core finale: niente analisi del conflitto.
  bool has_is_in_conflict() const override
  {
    return false;
  }
  bool is_in_conflict(literalt a) const override;

protected:
  resultt do_prop_solve() override;

  kissat *solver;
  bvt assumptions;
  bool solved = false;
};

#endif // CPROVER_SOLVERS_SAT_SATCHECK_KISSAT_H
