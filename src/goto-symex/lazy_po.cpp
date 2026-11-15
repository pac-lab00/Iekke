/// \file
/// LazyCSeq context-bounded concurrency SSA transformation: driver (operator()) and process-wide POR symbol registry

#include "lazy_po.h"
#include <util/ssa_expr.h>
#include <cctype>
#include <optional>
#include <tuple>
#include <util/bitvector_types.h>
#include <util/expr_util.h>
#include <util/pointer_offset_size.h>
#include <util/byte_operators.h>
#include <string>
#include <map>
#include <algorithm>
#include <set>
#include <unordered_set>
#include <cstdlib>
#include <iostream>
#include <chrono>
#include <fstream>
#include <functional>
#include <thread>
#include <util/cprover_prefix.h>
#include <util/format.h>
#include <util/format_expr.h>
#include <util/pointer_expr.h>
#include <util/c_types.h>
#include <util/prefix.h>
#include <util/expr_util.h>
#include <ansi-c/expr2c.h>
#include <util/simplify_expr.h>
#include <util/source_location.h>

#include <util/arith_tools.h>
#include <util/invariant.h>
#include <util/symbol.h>

#include "lazy_po_internal.h"

const std::vector<symbol_exprt> &por_auxiliary_symbols()
{
  return por_symbol_registry();
}

void clear_por_auxiliary_symbols()
{
  por_symbol_registry().clear();
}

// Whether this node itself needs the alignment below: the three cases it
// handles, tested in the same order.
static bool misaligned_here(const exprt &e)
{
  if(e.id() == ID_equal || e.id() == ID_notequal)
  {
    const auto &binary = to_binary_expr(e);
    return binary.op0().type() != binary.op1().type() &&
           binary.op0().type().id() == ID_pointer &&
           binary.op1().type().id() == ID_pointer;
  }
  if(e.id() == ID_if)
  {
    const auto &if_e = to_if_expr(e);
    return if_e.true_case().type() != if_e.false_case().type() ||
           if_e.type() != if_e.true_case().type();
  }
  if(e.id() == ID_with)
    return to_with_expr(e).type() != to_with_expr(e).old().type();
  return false;
}

static bool misaligned_below(const exprt &e, subtree_memot &memo)
{
  return subtree_has(
    e, misaligned_here, [](const exprt &) { return false; }, memo);
}

// Descends only into subtrees that hold a node to align (see subtree_has).
static void align_pointer_equalities(exprt &e, subtree_memot &memo)
{
  if(!misaligned_below(as_const(e), memo))
    return;
  for(auto &op : e.operands())
    align_pointer_equalities(op, memo);

  if(e.id() == ID_equal || e.id() == ID_notequal)
  {
    auto &binary = to_binary_expr(e);
    if(
      binary.op0().type() != binary.op1().type() &&
      binary.op0().type().id() == ID_pointer &&
      binary.op1().type().id() == ID_pointer)
    {
      binary.op1() =
        typecast_exprt::conditional_cast(binary.op1(), binary.op0().type());
    }
  }
  else if(e.id() == ID_if)
  {
    auto &if_e = to_if_expr(e);
    if(if_e.true_case().type() != if_e.false_case().type())
    {
      if_e.false_case() = typecast_exprt::conditional_cast(
        if_e.false_case(), if_e.true_case().type());
    }
    if(if_e.type() != if_e.true_case().type())
      if_e.type() = if_e.true_case().type();
  }
  else if(e.id() == ID_with)
  {
    auto &with_e = to_with_expr(e);
    if(with_e.type() != with_e.old().type())
      with_e.type() = with_e.old().type();
  }
}

void lazy_pot::operator()(
  symex_target_equationt &equation,
  message_handlert &message_handler)
{
  messaget log{message_handler};
  clear_por_auxiliary_symbols();
  log.statistics() << "Adding Iekke constraints with " << rounds << " rounds"
                   << messaget::eom;

  // Instrumentation per fase: separa il costo di costruzione da quello del
  // solver, e dentro la costruzione separa base da POR. Serve per attribuire
  // le regressioni di performance alla fase giusta invece che al totale di
  // postprocess_equation.
  const auto t_start = std::chrono::steady_clock::now();
  auto t_last = t_start;
  const auto phase = [&](const char *name) {
    const auto now = std::chrono::steady_clock::now();
    // the process's current resident memory (VmRSS, not the peak) at the end
    // of the phase, where /proc provides it
    long rss_kb = -1;
    {
      std::ifstream status("/proc/self/status");
      std::string line;
      while(std::getline(status, line))
        if(line.rfind("VmRSS:", 0) == 0)
          rss_kb = std::atol(line.c_str() + 6);
    }
    log.statistics()
      << "lazy_po phase " << name << ": "
      << std::chrono::duration_cast<std::chrono::milliseconds>(now - t_last)
           .count()
      << "ms, resident "
      << (rss_kb < 0 ? std::string{"n/a"}
                     : std::to_string(rss_kb / 1024) + " MB")
      << messaget::eom;
    t_last = now;
  };

  //check_shared_event(equation, message_handler);

  handling_active_threads(equation);
  phase("active-threads");

  collect_reads_and_writes(equation.SSA_steps);
  phase("collect-events");

  // LAZYPO_ROUND_BOUND=1 prints the static round bound (compute_round_bound)
  // and carries on; LAZYPO_ROUND_BOUND=only prints it and exits before any
  // constraint is built, so a corpus can be measured without the solver.
  if(const char *rb = getenv("LAZYPO_ROUND_BOUND"))
  {
    // Rounds are capped at 25 (LAZYPO_ROUND_BOUND_MAX, 0 = no cap): above it
    // a SUCCESSFUL is bounded again, and the search stops as soon as it has
    // shown the cap is reached.
    std::size_t max_rounds = 25;
    if(const char *mr = getenv("LAZYPO_ROUND_BOUND_MAX"))
      max_rounds = std::strtoul(mr, nullptr, 10);
    const round_boundt bound = bound_from_events(max_rounds);
    std::cout << "Round bound (static): count=" << bound.count
              << " path=" << bound.path
              << (bound.path_exact ? "" : " (path capped, = count)")
              << (bound.at_max_rounds ? " (at max rounds)" : "")
              << " max=" << max_rounds << " rounds=" << rounds << "\n";
    const property_conet cone = property_cone_events();
    const round_boundt cone_bound =
      compute_round_bound(cone.events, spawn_points, max_rounds);
    std::cout << "Round bound (property cone): count=" << cone_bound.count
              << " path=" << cone_bound.path
              << (cone_bound.path_exact ? "" : " (path capped, = count)")
              << (cone_bound.at_max_rounds ? " (at max rounds)" : "")
              << " blocks=" << cone.blocks << "/" << cone.total_blocks << "\n";
    for(const auto &sp : spawn_points)
      std::cout << "Round bound spawn: thread " << sp.first << " by thread "
                << sp.second.first << " at label " << sp.second.second << "\n";
    std::cout << std::flush;
    if(std::string(rb) == "only")
      std::exit(0);
  }

  if(skipped_writes || skipped_reads)
    log.error() << "lazy_po: accessi shared SCARTATI dal modello di memoria -- W="
                << skipped_writes << " R=" << skipped_reads
                << " (ssa_lhs non e' un symbol_exprt; quelle scritture sono "
                   "invisibili agli altri thread)" << messaget::eom;

  compute_private_objects();
  phase("private-objects");

  compute_array_rf(equation);
  phase("array-rf-plan");

  if(por)
  {
    build_atomic_blocks();
    phase("atomic-blocks");
  }

  create_write_constraints(equation);
  if(!index_chain_summary.empty())
    log.statistics() << "index chain: " << index_chain_summary
                     << messaget::eom;
  phase("base-writes");

  create_read_constraints(equation);
  phase("base-reads");

  create_private_constraints(equation);
  phase("private-reads");

  create_array_rf_constraints(equation);
  phase("array-read-from");

  if(por)
  {
    create_lazy_variable_read();
    phase("lazy-reads");
  }

  create_cs_constraint(equation);
  phase("context-switch");

  if(empty_round_literals)
  {
    create_empty_round_literals(equation);
    phase("empty-round-literals");
  }

  if(thread_symmetry != 0)
  {
    log.status() << "thread symmetry: " << create_thread_symmetry(equation)
                 << messaget::eom;
    phase("thread-symmetry");
  }

  if(por) {
    enumerate_accesses();

    // NOTE: tried making this run unconditionally (before enumerate_accesses,
    // so it would also cover base mode) on the theory that it only reads
    // lazy_variables (always populated) and lazy_variables_read (empty
    // outside --por). That's true for the lex-order checks, but this
    // function ALSO checks write/read .id uniqueness, and read .id is only
    // assigned by enumerate_accesses() just above -- calling it earlier
    // meant every lazy_variable_read entry still had its default/unset id,
    // producing spurious "duplicate id" invariant failures the moment a
    // variable had both a write and a read (confirmed: crashed
    // elimination_backoff_stack --por, which worked fine before). Reverted
    // to its original, safe position (after enumerate_accesses, --por
    // only); making the ordering-only half of this check run in base mode
    // too would need splitting it into two functions, not attempted here.
    validate_access_order();
    phase("enumerate+validate");

    // POR's pruning, not part of the definition of a schedule: dropping it
    // admits more schedules, so verdicts must not change.
    create_atomic_canonical(equation);
    phase("canonicality+NRP/LOW");
  }

  //handling_atomic_sections(equation);

  // handling_guards must run before handling_datarace: it walks
  // equation.SSA_steps matching every assert/assume against
  // blocking_events by position, and handling_datarace appends one more
  // (self-contained, already reachability-guarded) assert step of its own
  // at the end. Running handling_guards first keeps its assert/assume
  // count in sync with blocking_events; running it only in the non-datarace
  // branch left every other built-in-library assert/assume (double-free,
  // etc.) unguarded by round-robin reachability under --datarace, so
  // preconditions violated only on schedules the round bound never
  // reaches were still reported as FAILURE.
  handling_guards(equation);
  phase("guards");

  if(datarace) {
    log.warning() << "Datarace Enabled " << messaget::eom;
    handling_datarace(equation);
    phase("datarace");
  }

  // The constraints built since the first pass -- the exec constraints of
  // the schedule above all -- carry their own copies of the path guards, and
  // a guard may read an --array-rf object: pthread_join assumes
  // __CPROVER_threads_exited[t]. Left as they are, those reads name an array
  // whose defining assignments are gone, so they are unconstrained. Rewrite
  // them too; a read already seen keeps its element.
  create_array_rf_constraints(equation);
  phase("array-read-from (late)");

  // one memo for all steps: it holds what it records (see subtree_has)
  subtree_memot memo;
  for(auto &step : equation.SSA_steps)
  {
    align_pointer_equalities(step.cond_expr, memo);
    align_pointer_equalities(step.guard, memo);
  }
  phase("pointer-alignment");


  log.statistics()
    << "lazy_po total: "
    << std::chrono::duration_cast<std::chrono::milliseconds>(
         std::chrono::steady_clock::now() - t_start)
         .count()
    << "ms" << messaget::eom;
}

