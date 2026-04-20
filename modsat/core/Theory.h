/*
 * Theory.h
 *
 *  Created on: 2013-04-14
 *      Author: sam
 */

#ifndef THEORY_H_
#define THEORY_H_

#include "mtl/Vec.h"
#include "mtl/Heap.h"
#include "mtl/Alg.h"
#include "utils/Options.h"
#include "core/SolverTypes.h"
#include "Solver.h"

//Super simple, stripped down theory interface for an SMT solver.
//Our SAT modulo SAT solver implements this interface, because it is a SAT modulo Theory solver that can itself also be a theory solver.
namespace Minisat{
class Solver;
class Theory{
public:
    virtual ~Theory(){};
	virtual void backtrackTheory(int level)=0;
	virtual bool propagateTheory(vec<Lit> & conflict)=0;
	virtual bool solveTheory(vec<Lit> & conflict)=0;
	//Lazily construct the reason clause explaining this propagation
	virtual void buildTheoryReason(Lit p, vec<Lit> & reason)=0;
};
}

#endif /* THEORY_H_ */
