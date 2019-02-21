/*******************************************************************\

Module: Simplified strategy iteration solver by binary search

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_BINSEARCH_H
#define CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_BINSEARCH_H

#include "strategy_solver_base.h"
#include "tpolyhedra_domain.h"

class strategy_solver_binsearcht:public strategy_solver_baset
{
public:
  strategy_solver_binsearcht(
    tpolyhedra_domaint &_tpolyhedra_domain,
    incremental_solvert &_solver,
    const namespacet &_ns):
    strategy_solver_baset(_solver, _ns),
    tpolyhedra_domain(_tpolyhedra_domain)
  {
  }

  virtual bool iterate(invariantt &inv);
  virtual bool iterate_for_ins(invariantt &_inv, 
    const incremental_solvert::constraintst &conds);
  
  inline exprt make_false_cond(
    const exprt &cond)
  {
    if(cond.id()==ID_implies)
      return implies_exprt(cond.op0(), 
                           equal_exprt(cond.op1().op0(), false_exprt()));
    else return equal_exprt(cond.op0(), false_exprt());
  }

protected:
  tpolyhedra_domaint &tpolyhedra_domain;
};

#endif
