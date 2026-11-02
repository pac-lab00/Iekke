/*******************************************************************\

Module: Symbolic Execution

Author: Iekke

\*******************************************************************/

/// \file
/// BDDs of path guards, for decisions about the equation (which events can
/// never execute, which never execute together). The formula itself keeps the
/// usual guards.

#ifndef CPROVER_GOTO_SYMEX_GUARD_BDD_H
#define CPROVER_GOTO_SYMEX_GUARD_BDD_H

#include <util/std_expr.h>

#include <solvers/prop/bdd_expr.h>

#include <string>
#include <unordered_map>

/// BDD conversion of path guards that converts each goto_symex::\guard#n
/// definition once, in program order, and reuses it; the plain
/// bdd_exprt::from_expr would convert a shared definition again at every use.
class guard_bdd_convertert : public bdd_exprt
{
public:
  std::unordered_map<irep_idt, bddt> guard_bdd;

  /// Record the definition of a guard symbol (an assignment step of the
  /// equation), if \p lhs is one. Definitions precede their uses, so walking
  /// the equation in order defines every guard before it is needed.
  bool define(const exprt &lhs, const exprt &rhs)
  {
    if(
      lhs.type().id() != ID_bool || lhs.id() != ID_symbol ||
      id2string(to_symbol_expr(lhs).get_identifier()).find("guard#") ==
        std::string::npos)
    {
      return false;
    }
    guard_bdd.emplace(to_symbol_expr(lhs).get_identifier(), convert(rhs));
    return true;
  }

  bddt convert(const exprt &e)
  {
    if(e.is_constant())
      return e.is_false() ? bdd_mgr.bdd_false() : bdd_mgr.bdd_true();
    if(e.id() == ID_symbol)
    {
      const auto g = guard_bdd.find(to_symbol_expr(e).get_identifier());
      if(g != guard_bdd.end())
        return g->second;
      return from_expr(e);
    }
    if(e.id() == ID_not)
      return convert(to_not_expr(e).op()).bdd_not();
    if(e.id() == ID_and || e.id() == ID_or)
    {
      bddt r = convert(e.operands().front());
      for(std::size_t i = 1; i < e.operands().size(); ++i)
        r = e.id() == ID_and ? r.bdd_and(convert(e.operands()[i]))
                             : r.bdd_or(convert(e.operands()[i]));
      return r;
    }
    if(e.id() == ID_implies)
      return convert(to_implies_expr(e).lhs())
        .bdd_not()
        .bdd_or(convert(to_implies_expr(e).rhs()));
    return from_expr(e);
  }

  bddt bdd_true()
  {
    return bdd_mgr.bdd_true();
  }

  bddt bdd_false()
  {
    return bdd_mgr.bdd_false();
  }
};

#endif // CPROVER_GOTO_SYMEX_GUARD_BDD_H
