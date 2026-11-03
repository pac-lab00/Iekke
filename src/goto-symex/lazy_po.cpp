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
  tag_stats() = tag_chain_statst{};
  bv_tags = getenv("LAZYPO_TAG_BV") != nullptr;
  xcheck_tags = getenv("LAZYPO_TAG_XCHECK") != nullptr;
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

  // LAZYPO_OWNWRITE_TALLY: reads that no other thread can reach between an
  // earlier write of the same thread and the read -- same label, no context
  // switch in between -- so they read that write (when the write is
  // executed); and how many of those writes store a constant, the value
  // being the right-hand side of the assignment step that follows the write
  // event.
  if(getenv("LAZYPO_OWNWRITE_TALLY") != nullptr)
  {
    std::size_t all = 0, own = 0, own_const = 0;
    for(const auto &entry : reads)
    {
      const auto w = writes.find(entry.first);
      for(const auto &r : entry.second)
      {
        ++all;
        if(w == writes.end())
          continue;
        const shared_event *latest = nullptr;
        for(const auto &e : w->second)
          if(e.thread == r.thread && e.label == r.label && e.num < r.num &&
             (latest == nullptr || e.num > latest->num))
            latest = &e;
        if(latest == nullptr)
          continue;
        ++own;
        auto next = latest->s_it;
        ++next;
        while(next != equation.SSA_steps.end() && !next->is_assignment())
          ++next;
        if(next != equation.SSA_steps.end() &&
           next->ssa_lhs.get_identifier() ==
             latest->s_it->ssa_lhs.get_identifier() &&
           next->ssa_rhs.is_constant())
          ++own_const;
      }
    }
    std::cerr << "OWNWRITE_TALLY reads=" << all << " after-own-write=" << own
                << " of-a-constant=" << own_const << "\n";
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

  if(getenv("LAZYPO_SCHEMA_TALLY") != nullptr)
    schema_tally(equation);

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
    if(getenv("LAZYPO_FIXPOINT") != nullptr)
      collect_fixpoint_projection();
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

    // Guardia sulla larghezza degli id. Se un id raggiunge la sentinella ⊥
    // (2^bits-1 usata da WINR/NRP e da boundary_id), i confronti di canonicita'
    // scambiano un accesso reale per "nessun accesso" e il POR pota schedule
    // legittimi -- fallimento silenzioso. Meglio urlare.
    // Serve solo al percorso bitvector: l'encoding a finestre usa gli id come
    // indici di array, non come costanti in un tipo di larghezza fissa, e la
    // sentinella ⊥ non esiste piu' (boundary_index restituisce n).
    for(const auto &gv : global_variables)
    {
      if(!bv_tags && !xcheck_tags)
        break;
      const unsigned bits = bit_writes[gv];
      const unsigned bottom = static_cast<unsigned>((1ULL << bits) - 1);
      unsigned max_id = 0;
      if(lazy_variables.count(gv))
        for(const auto &lv : lazy_variables.at(gv))
          max_id = std::max(max_id, lv.id);
      if(lazy_variables_read.count(gv))
        for(const auto &lv : lazy_variables_read.at(gv))
          max_id = std::max(max_id, lv.id);
      if(max_id >= bottom)
        log.error() << "lazy_po: id overflow su " << id2string(gv)
                    << " -- max_id=" << max_id << " sentinella=" << bottom
                    << " bits=" << bits
                    << " (il POR potrebbe potare esecuzioni valide)"
                    << messaget::eom;
    }

    if(bv_tags || xcheck_tags)
    {
      create_lw_tot_symbol(equation);
      create_winr_tot_symbol(equation);
    }
    phase("tags-LW-WINR");

    // Re-enabled (was on-demand-only): create_NRP_symbol's on-demand
    // descent walks forward through essentially every read-of-x position
    // across all rounds before hitting a memo entry, since nothing
    // pre-populates it bottom-up the way LW/WINR are below -- confirmed
    // (gdb backtrace: create_NRP_symbol recursing into itself) to
    // stack-overflow in --por mode on benchmarks with many accesses to one
    // shared variable at realistic round bounds (the tool's own benchexec
    // configs use rounds up to 21, well within the crash region). Both
    // functions already sort in the direction that keeps each on-demand
    // call landing on a fresh memo entry (create_nrp_tot_symbol
    // descending like create_winr_tot_symbol; create_low_tot_symbol
    // ascending like create_lw_tot_symbol already above) -- they just
    // were never invoked.
    if(bv_tags || xcheck_tags)
    {
      create_nrp_tot_symbol(equation);
      create_low_tot_symbol(equation);
    }

    // POR's pruning, not part of the definition of a schedule: dropping it
    // admits more schedules, so verdicts must not change. Gated so the ~40% of
    // the encoding it and its feeder symbols occupy can be priced, the way the
    // context-boundary tightening was.
    if(getenv("LAZYPO_NO_ATOMIC_CANON") == nullptr)
      create_atomic_canonical(equation);
    phase("canonicality+NRP/LOW");

    if(getenv("LAZYPO_TAG_DEBUG"))
    {
      const auto &s = tag_stats();
      std::vector<std::pair<unsigned, irep_idt>> by_bits;
      for(const auto &gv : global_variables)
        by_bits.emplace_back(bit_writes[gv], gv);
      std::sort(by_bits.begin(), by_bits.end(),
        [](const std::pair<unsigned, irep_idt> &a,
           const std::pair<unsigned, irep_idt> &b) {
          return a.first > b.first;
        });
      std::cerr << "TAGDBG variables=" << global_variables.size() << "\n";
      for(const auto &e : by_bits)
      {
        const irep_idt &gv = e.second;
        const std::size_t nw = writes.count(gv) ? writes.at(gv).size() : 0;
        const std::size_t nr = reads.count(gv) ? reads.at(gv).size() : 0;
        const std::size_t nids =
          (lazy_variables.count(gv) ? lazy_variables.at(gv).size() : 0) +
          (lazy_variables_read.count(gv) ? lazy_variables_read.at(gv).size() : 0);
        std::cerr << "TAGDBG var bits=" << e.first << " W=" << nw
                  << " R=" << nr << " ids=" << nids
                  << " LW=" << (lw_variables.count(gv) ? lw_variables.at(gv).size() : 0)
                  << " WINR=" << (winr_variables.count(gv) ? winr_variables.at(gv).size() : 0)
                  << " NRP=" << (nrp_variables.count(gv) ? nrp_variables.at(gv).size() : 0)
                  << " LOW=" << (low_variables.count(gv) ? low_variables.at(gv).size() : 0)
                  << " OBS=" << (obs_variables.count(gv) ? obs_variables.at(gv).size() : 0)
                  << " name=" << id2string(gv) << "\n";
      }
      std::cerr << "TAGDBG TOTAL symbols LW=" << s.lw << " WINR=" << s.winr
                << " NRP=" << s.nrp << " LOW=" << s.low << " OBS=" << s.obs
                << " sum=" << (s.lw + s.winr + s.nrp + s.low + s.obs) << "\n";
      std::cerr << "TAGDBG TOTAL symbol-bits LW=" << s.lw_bits
                << " WINR=" << s.winr_bits << " NRP=" << s.nrp_bits
                << " LOW=" << s.low_bits
                << " sum=" << (s.lw_bits + s.winr_bits + s.nrp_bits + s.low_bits)
                << "\n";
      std::cerr << "TAGDBG TOTAL cmps rel=" << s.cmp_rel
                << " rel_bits=" << s.cmp_rel_bits << " neq=" << s.cmp_neq
                << " neq_bits=" << s.cmp_neq_bits << " eq=" << s.cmp_eq
                << " eq_bits=" << s.cmp_eq_bits << "\n";
      std::cerr << "TAGDBG WINDOW range_nodes=" << s.range_nodes
                << " fr_nodes=" << s.fr_nodes
                << " queries=" << s.window_queries << "\n";
      std::cerr << "TAGDBG atomic_blocks=" << atomic_blocks.size()
                << " rounds=" << rounds << " bv_tags=" << bv_tags << "\n";
    }
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

  if(xcheck_tags && !xcheck_pairs.empty())
  {
    // Un'unica asserzione: la congiunzione di tutte le equivalenze. Emessa
    // qui, dopo handling_guards, perche' quello consuma un blocking event
    // per ogni assert gia' presente nell'equazione.
    exprt all = true_exprt{};
    for(const auto &p : xcheck_pairs)
      all = and_exprt{all, equal_exprt{p.first, p.second}};
    simplify(all, ns);
    equation.assertion(
      true_exprt{}, all, "window/bv tag encoding equivalence",
      equation.SSA_steps.begin()->source);
    log.statistics() << "tag xcheck: " << xcheck_pairs.size()
                     << " ABR/ABW witness pairs asserted equivalent"
                     << messaget::eom;
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

  if(getenv("LAZYPO_CONSTRAINT_TALLY") != nullptr)
  {
    // Iterative: these expressions have overflowed the stack here before.
    const auto node_count = [](const exprt &e) {
      std::size_t n = 0;
      std::vector<const exprt *> stack{&e};
      while(!stack.empty())
      {
        const exprt *cur = stack.back();
        stack.pop_back();
        ++n;
        for(const auto &op : cur->operands())
          stack.push_back(&op);
      }
      return n;
    };

    // Tree nodes count a shared subexpression once per occurrence; ireps are
    // shared, so that over-states anything that reuses structure -- a guard
    // conjoined once per round is one object, not R. Count distinct nodes by
    // hash as well, and the gap between the two IS the sharing.
    std::map<std::string, std::pair<std::size_t, std::size_t>> by_kind;
    std::map<std::string, std::unordered_set<std::size_t>> uniq_by_kind;
    std::size_t total_nodes = 0, total_constraints = 0;
    for(const auto &step : equation.SSA_steps)
    {
      if(!step.is_constraint())
        continue;
      const std::size_t n = node_count(step.cond_expr);
      {
        auto &u = uniq_by_kind[id2string(step.comment)];
        std::vector<const exprt *> st{&step.cond_expr};
        while(!st.empty())
        {
          const exprt *cur = st.back();
          st.pop_back();
          if(!u.insert(cur->hash()).second)
            continue; // already seen this subterm: shared, not a new node
          for(const auto &op : cur->operands())
            st.push_back(&op);
        }
      }
      auto &slot = by_kind[id2string(step.comment)];
      ++slot.first;
      slot.second += n;
      ++total_constraints;
      total_nodes += n;
    }

    std::vector<std::pair<std::string, std::pair<std::size_t, std::size_t>>>
      sorted(by_kind.begin(), by_kind.end());
    std::sort(
      sorted.begin(), sorted.end(),
      [](const std::pair<std::string, std::pair<std::size_t, std::size_t>> &a,
         const std::pair<std::string, std::pair<std::size_t, std::size_t>> &b) {
        return a.second.second > b.second.second;
      });

    std::cerr << "TALLY total constraints=" << total_constraints
              << " nodes=" << total_nodes << "\n";
    for(const auto &e : sorted)
    {
      const double pct =
        total_nodes > 0 ? 100.0 * static_cast<double>(e.second.second) /
                            static_cast<double>(total_nodes)
                        : 0.0;
      std::cerr << "TALLY " << e.first << " count=" << e.second.first
                << " nodes=" << e.second.second << " (" << pct << "%)"
                << " distinct=" << uniq_by_kind[e.first].size() << "\n";
    }
  }


  log.statistics()
    << "lazy_po total: "
    << std::chrono::duration_cast<std::chrono::milliseconds>(
         std::chrono::steady_clock::now() - t_start)
         .count()
    << "ms" << messaget::eom;
}


namespace
{
/// Collect every symbol identifier occurring in an expression.
void dead_audit_symbols(const exprt &expr, std::set<irep_idt> &out)
{
  if(expr.id() == ID_symbol)
    out.insert(to_symbol_expr(expr).get_identifier());
  for(const auto &op : expr.operands())
    dead_audit_symbols(op, out);
}
} // namespace

void lazy_pot::dead_audit(const symex_target_equationt &equation)
{
  // every symbol the equation reads anywhere other than as a shared-read target
  std::set<irep_idt> used;
  for(const auto &step : equation.SSA_steps)
  {
    if(step.is_shared_read())
      continue; // the read's own lhs is not a use of itself
    if(!step.ssa_rhs.is_nil())
      dead_audit_symbols(step.ssa_rhs, used);
    if(!step.cond_expr.is_nil() && !step.is_assignment() && !step.is_decl())
      dead_audit_symbols(step.cond_expr, used);
    if(!step.guard.is_nil())
      dead_audit_symbols(step.guard, used);
  }

  std::size_t dead = 0, live = 0;
  const auto report = [&](const irep_idt &variable,
                          const std::vector<shared_event> &rs,
                          const std::vector<shared_event> *ws) {
    std::set<unsigned> lines;
    std::size_t d = 0;
    for(const auto &r : rs)
    {
      lines.insert(static_cast<unsigned>(
        std::atoi(id2string(r.s_it->source.pc->source_location().get_line())
                    .c_str())));
      const irep_idt id =
        to_symbol_expr(r.s_it->ssa_lhs).get_identifier();
      if(used.count(id) == 0)
      {
        ++d;
        ++dead;
      }
      else
        ++live;
    }
    std::cerr << "DEAD_AUDIT " << variable << " reads=" << rs.size()
              << " dead_reads=" << d << " distinct_read_lines=" << lines.size()
              << " writes=" << (ws != nullptr ? ws->size() : 0) << "\n";
  };

  std::set<irep_idt> all;
  for(const auto &e : reads)
    all.insert(e.first);
  for(const auto &e : writes)
    all.insert(e.first);
  for(const auto &e : private_reads)
    all.insert(e.first);
  for(const auto &e : private_writes)
    all.insert(e.first);

  static const std::vector<shared_event> none;
  for(const auto &v : all)
  {
    const auto *rs = reads.count(v)           ? &reads.at(v)
                     : private_reads.count(v) ? &private_reads.at(v)
                                              : &none;
    const auto *ws = writes.count(v)           ? &writes.at(v)
                     : private_writes.count(v) ? &private_writes.at(v)
                                               : nullptr;
    report(v, *rs, ws);
  }
  std::cerr << "DEAD_AUDIT TOTAL dead_reads=" << dead << " live_reads=" << live
            << "\n";

  // Fan-out: one source-level access through a pointer that may alias k
  // objects becomes k shared accesses, each with its own rounds-deep chain.
  // The .i file puts whole statements on one line, so source lines cannot
  // separate program points -- (thread, label, num) can.
  // Key on the goto instruction itself. Label and num cannot answer this: the
  // dereference of a pointer with k targets expands into k separate shared
  // accesses, and each one is given its own label, so by label they all look
  // like distinct program points. The instruction they came from is shared.
  std::map<const void *, std::set<irep_idt>> at_point;
  for(const auto *m : {&reads, &private_reads})
    for(const auto &entry : *m)
      for(const auto &r : entry.second)
        at_point[static_cast<const void *>(&*r.s_it->source.pc)]
          .insert(entry.first);

  std::map<std::size_t, std::size_t> histogram;
  std::size_t accesses = 0;
  for(const auto &p : at_point)
  {
    ++histogram[p.second.size()];
    accesses += p.second.size();
  }
  std::cerr << "DEAD_AUDIT FANOUT read program points=" << at_point.size()
            << " shared reads=" << accesses << "\n";
  for(const auto &h : histogram)
    std::cerr << "DEAD_AUDIT FANOUT   " << h.second << " points read "
              << h.first << " object(s)\n";
}
