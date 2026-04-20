/*
 * Config.cpp
 *
 *  Created on: 2012-10-31
 *      Author: sam
 */


#include "Config.h"

using namespace Minisat;

#ifndef NDEBUG
int dbg_total_iterations=0;
#endif

static const char* _cat = "CORE";
static const char* _cat_sms = "SMS";
static const char* _cat_bmc= "BMC";
IntOption    Minisat::opt_verb   ("MAIN", "verb",   "Verbosity level (0=silent, 1=some, 2=more).", 0, IntRange(0, 2));
 DoubleOption  Minisat::opt_var_decay         (_cat, "var-decay",   "The variable activity decay factor",            0.95,     DoubleRange(0, false, 1, false));
 DoubleOption  Minisat::opt_clause_decay      (_cat, "cla-decay",   "The clause activity decay factor",              0.999,    DoubleRange(0, false, 1, false));
 DoubleOption  Minisat::opt_random_var_freq   (_cat, "rnd-freq",    "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
 DoubleOption  Minisat::opt_random_seed       (_cat, "rnd-seed",    "Used by the random variable selection",         91648253, DoubleRange(0, false, HUGE_VAL, false));
 IntOption     Minisat::opt_ccmin_mode        (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
 IntOption     Minisat::opt_phase_saving      (_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
 BoolOption    Minisat::opt_rnd_init_act      (_cat, "rnd-init",    "Randomize the initial activity", false);
 BoolOption    Minisat::opt_luby_restart      (_cat, "luby",        "Use the Luby restart sequence", true);
 IntOption     Minisat::opt_restart_first     (_cat, "rfirst",      "The base restart interval", 100, IntRange(1, INT32_MAX));
 DoubleOption  Minisat::opt_restart_inc       (_cat, "rinc",        "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
 DoubleOption  Minisat::opt_garbage_frac      (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));
BoolOption Minisat::opt_separate_ca(_cat,"separate-ca","Give each solver a separate clause allocation space (drastically increases memory use for large numbers of modules), instead of combining them.", false);


 BoolOption Minisat::opt_interpolate(_cat_sms,"interpolate","Store learnt interface clauses to form interpolants between modules",false);
 IntOption Minisat::opt_eager_prop(_cat_sms,"eager-prop","Controls whether unit propagation is allowed to cross subsolver boundaries. 0= Disable. 1= Enable.", 1, IntRange(0,1));
 IntOption Minisat::opt_subsearch(_cat_sms,"subsearch","Control how the solver performs search on the subsolvers: 0=abort as soon as a conflict backtracks past the supersolvers decisionlevel. 1=Abort only once a conflict on the super-interface variables is found, allowing backtracks past those variables in the process. 2=Abort only when the the super-solvers assignment is proven to be in conflict. 3=Don't continue subsearach if the subsolver has backtracked past super-solver decisions. 4=Don't continue past the last interpolant level if any solver has backtracked past a super solver's decisions",2,IntRange(0,4));
 BoolOption Minisat::opt_careful_subsearch(_cat_sms,"careful-subsearch","Controls whether a subsolver always ensures that all of the parent solver's shared literals are enqueued before continuing subsearch, or not.",true);

 BoolOption Minisat::opt_witness(_cat,"witness","Produce a witness if the instance is SAT",false);
IntOption    Minisat::opt_k(_cat_bmc, "k","Maximum number of steps to unroll.\n", INT32_MAX, IntRange(0, INT32_MAX));
IntOption    Minisat::opt_start_k(_cat_bmc, "start-k","Minimum number of steps to unroll (ie, start checking at this number of time steps).\n", 0, IntRange(0, INT32_MAX));
BoolOption Minisat::opt_print_depth(_cat_bmc,"print-depth-lines","Print HWMCC format depth bound (ie, 'u' lines)\n",true);
BoolOption Minisat::opt_permanent_theory_conflicts(_cat_sms,"permanent-theory-conflicts","True if conflict clauses from theory solvers are treated as permanent clauses; false if they are treated as learnt clauses (that is, allowed to be deleted by the solver)",true);
BoolOption Minisat::opt_modular(_cat_sms,"modular","If false, combine all partitions into a single solver and solve them normally, instead of maintaining the partitions.",true);
