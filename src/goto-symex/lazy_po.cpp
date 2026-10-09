/// \file
/// LazyCSeq context-bounded concurrency SSA transformation

#include "lazy_po.h"
#include <util/ssa_expr.h>
#include <cctype>
#include <optional>
#include <tuple>
#include <util/expr_util.h>
#include <util/pointer_offset_size.h>
#include <util/byte_operators.h>
#include <string>
#include <map>
#include <algorithm>
#include <set>
#include <cstdlib>
#include <iostream>
#include <chrono>
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


// Campi impaccati nella chiave delle memo: num [0,20), label [20,40),
// thread [40,52), round [52,64). Un overflow silenzioso farebbe collidere
// posizioni distinte nelle cache delle catene (una LW di un thread diventa
// quella di un altro) -- stessa classe di guasto del troncamento degli id in
// bit_writes. Meglio abortire che emettere vincoli sbagliati.
static const unsigned chain_key_num_max = 1u << 20;
static const unsigned chain_key_label_max = 1u << 20;
static const unsigned chain_key_thread_max = 1u << 12;
static const std::size_t chain_key_round_max = std::size_t(1) << 12;

static uint64_t chain_key(std::size_t round, unsigned thread, unsigned label, unsigned num)
{
  PRECONDITION(num < chain_key_num_max);
  PRECONDITION(label < chain_key_label_max);
  PRECONDITION(thread < chain_key_thread_max);
  PRECONDITION(round < chain_key_round_max);
  return (uint64_t(round) << 52) | (uint64_t(thread) << 40) |
         (uint64_t(label) << 20) | uint64_t(num);
}

// ---------------------------------------------------------------------------
// Diagnostica Fase 1 (LAZYPO_TAG_DEBUG): quantifica quanto della formula
// nasce dalle catene dei tag (LW/WINR/NRP/LOW/OBS) e dai confronti bitvector
// contro di esse. Puramente osservativa: non tocca i vincoli emessi.
// ---------------------------------------------------------------------------
struct tag_chain_statst
{
  std::size_t lw = 0, winr = 0, nrp = 0, low = 0, obs = 0;
  std::size_t lw_bits = 0, winr_bits = 0, nrp_bits = 0, low_bits = 0,
              obs_bits = 0;
  // confronti emessi in create_ABR / create_ABW / create_OBS_symbol
  std::size_t cmp_rel = 0, cmp_rel_bits = 0;   // <, >= contro costante
  std::size_t cmp_neq = 0, cmp_neq_bits = 0;   // LW^r != LW^{r-1}
  std::size_t cmp_eq = 0, cmp_eq_bits = 0;     // OBS: WINR == costante
  // encoding a finestre
  std::size_t range_nodes = 0, fr_nodes = 0, window_queries = 0;
};

static tag_chain_statst &tag_stats()
{
  static tag_chain_statst s;
  return s;
}

// Registry della provenance POR: i simboli ausiliari introdotti dalla
// riduzione (catene dei tag e testimoni di blocco). Serve al backend SAT per
// classificare le variabili corrispondenti senza indovinare dai nomi dopo il
// bit-blasting, dove un simbolo diventa molti letterali e i nomi sparaiscono.
// Ambito processo: una run = un'equazione, ripulito a ogni costruzione.
static std::vector<symbol_exprt> &por_symbol_registry()
{
  static std::vector<symbol_exprt> registry;
  return registry;
}

const std::vector<symbol_exprt> &por_auxiliary_symbols()
{
  return por_symbol_registry();
}

void clear_por_auxiliary_symbols()
{
  por_symbol_registry().clear();
}

static const symbol_exprt &register_por_symbol(const symbol_exprt &sym)
{
  por_symbol_registry().push_back(sym);
  return por_symbol_registry().back();
}

static void align_pointer_equalities(exprt &e)
{
  for(auto &op : e.operands())
    align_pointer_equalities(op);

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
    log.statistics()
      << "lazy_po phase " << name << ": "
      << std::chrono::duration_cast<std::chrono::milliseconds>(now - t_last)
           .count()
      << "ms" << messaget::eom;
    t_last = now;
  };

  //check_shared_event(equation, message_handler);

  handling_active_threads(equation);
  phase("active-threads");

  collect_reads_and_writes(equation.SSA_steps);
  phase("collect-events");

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

  for(auto &step : equation.SSA_steps)
  {
    align_pointer_equalities(step.cond_expr);
    align_pointer_equalities(step.guard);
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


/// Drop the L2 counter so every version of an object maps to one name. The L1
/// frame suffix stays: that is what global_variables is keyed on.
///
/// The counter is `#` followed by digits, and it is not always at the end --
/// field sensitivity appends the component after it, as in
/// `queue#1..element`. Erasing from the `#` to the end would turn that into
/// `queue`, so the object would never be recognised and every analysis keyed
/// on this name would silently decline it.
static irep_idt narrowing_base(const exprt &expr)
{
  if(expr.id() != ID_symbol)
    return irep_idt{};
  std::string id = id2string(to_symbol_expr(expr).get_identifier());
  const std::size_t hash = id.find('#');
  if(hash == std::string::npos)
    return irep_idt{id};
  std::size_t end = hash + 1;
  while(end < id.size() && isdigit(static_cast<unsigned char>(id[end])))
    ++end;
  id.erase(hash, end - hash);
  return irep_idt{id};
}

namespace
{
/// What the equation does to one shared object, as far as narrowing cares.
struct object_usaget
{
  bool read_seen = false;
  bool unusable = false;  ///< a use that would observe bits outside the range
  std::size_t lo = 0;
  std::size_t hi = 0;

  void read(std::size_t offset_bits, std::size_t width_bits)
  {
    if(!read_seen)
    {
      lo = offset_bits;
      hi = offset_bits + width_bits;
      read_seen = true;
    }
    else
    {
      lo = std::min(lo, offset_bits);
      hi = std::max(hi, offset_bits + width_bits);
    }
  }
};
} // namespace

/// Can an assignment producing `base` with this right-hand side be narrowed?
/// Only shapes whose bits outside the read range are the object's own previous
/// bits, fresh nondeterminism, or a constant -- none of which a read can
/// distinguish once the bare-use check below has passed.
static bool narrowing_rhs_ok(const exprt &expr, const irep_idt &base)
{
  if(expr.id() == ID_nondet_symbol || expr.is_constant())
    return true;
  if(expr.id() == ID_symbol)
    return narrowing_base(expr) == base; // a copy between versions
  if(
    expr.id() == ID_byte_update_little_endian ||
    expr.id() == ID_byte_update_big_endian)
  {
    return narrowing_rhs_ok(expr.operands()[0], base);
  }
  if(expr.id() == ID_if) // a phi over two acceptable versions
  {
    return narrowing_rhs_ok(expr.operands()[1], base) &&
           narrowing_rhs_ok(expr.operands()[2], base);
  }
  if(expr.id() == ID_typecast)
    return narrowing_rhs_ok(expr.operands()[0], base);
  return false;
}

static void narrowing_scan(
  const exprt &,
  const namespacet &,
  const std::set<irep_idt> &,
  std::map<irep_idt, object_usaget> &);

/// Walk a right-hand side narrowing_rhs_ok accepted. Its shape is understood,
/// so the object's own symbols in it are not bare uses; the values written and
/// the phi conditions still go through the general scan.
static void narrowing_scan_accepted(
  const exprt &expr,
  const irep_idt &base,
  const namespacet &ns,
  const std::set<irep_idt> &tracked,
  std::map<irep_idt, object_usaget> &usage)
{
  if(expr.id() == ID_if)
  {
    narrowing_scan(expr.operands()[0], ns, tracked, usage);
    narrowing_scan_accepted(expr.operands()[1], base, ns, tracked, usage);
    narrowing_scan_accepted(expr.operands()[2], base, ns, tracked, usage);
  }
  else if(expr.id() == ID_typecast)
  {
    narrowing_scan_accepted(expr.operands()[0], base, ns, tracked, usage);
  }
  else if(
    expr.id() == ID_byte_update_little_endian ||
    expr.id() == ID_byte_update_big_endian)
  {
    // a write does not widen the chain -- see the file comment
    narrowing_scan_accepted(expr.operands()[0], base, ns, tracked, usage);
    narrowing_scan(expr.operands()[1], ns, tracked, usage);
    narrowing_scan(expr.operands()[2], ns, tracked, usage);
  }
  // symbol / nondet_symbol / constant: nothing to record
}

/// Record the byte ranges reads take out of each tracked object, and flag any
/// use that would observe it some other way.
static void narrowing_scan(
  const exprt &expr,
  const namespacet &ns,
  const std::set<irep_idt> &tracked,
  std::map<irep_idt, object_usaget> &usage)
{
  // Taking an object's address does not observe its value; by the time symex
  // has produced this equation every dereference has already been resolved
  // into the byte_extract/byte_update forms handled here. field_sensitivityt
  // skips ID_address_of for the same reason.
  if(expr.id() == ID_address_of)
    return;

  const bool is_extract = expr.id() == ID_byte_extract_little_endian ||
                          expr.id() == ID_byte_extract_big_endian;
  const bool is_update = expr.id() == ID_byte_update_little_endian ||
                         expr.id() == ID_byte_update_big_endian;

  if(is_extract || is_update)
  {
    const irep_idt base = narrowing_base(expr.operands()[0]);
    if(!base.empty() && tracked.count(base) != 0)
    {
      auto &u = usage[base];
      const auto offset = numeric_cast<mp_integer>(expr.operands()[1]);
      const typet &accessed_type =
        is_extract ? expr.type() : expr.operands()[2].type();
      const auto width = pointer_offset_bits(accessed_type, ns);
      if(!offset.has_value() || !width.has_value() || *offset < 0)
        u.unusable = true;
      else if(is_extract)
      {
        u.read(
          numeric_cast_v<std::size_t>(*offset) * 8,
          numeric_cast_v<std::size_t>(*width));
      }

      // operand 0 is accounted for; the rest can still hold other uses
      for(std::size_t i = 1; i < expr.operands().size(); ++i)
        narrowing_scan(expr.operands()[i], ns, tracked, usage);
      return;
    }
  }

  const irep_idt base = narrowing_base(expr);
  if(!base.empty() && tracked.count(base) != 0)
  {
    // a bare occurrence: a whole-object copy, comparison or argument. The
    // chain has to keep every bit this could observe.
    usage[base].unusable = true;
  }

  for(const auto &op : expr.operands())
    narrowing_scan(op, ns, tracked, usage);
}

void lazy_pot::compute_narrowings(const symex_target_equationt &equation)
{
  narrowings.clear();
  if(!narrow_shared)
    return;

  std::set<irep_idt> tracked;
  for(const auto &v : global_variables)
    if(writes.count(v) != 0)
      tracked.insert(v);
  // compute_private_objects has already moved the single-thread objects out of
  // global_variables, and they are narrowed on the same terms
  for(const auto &v : private_objects)
    if(private_writes.count(v) != 0)
      tracked.insert(v);
  if(tracked.empty())
    return;

  std::map<irep_idt, object_usaget> usage;
  for(const auto &step : equation.SSA_steps)
  {
    bool lhs_handled = false;
    if(!step.ssa_lhs.is_nil() && step.is_assignment())
    {
      const irep_idt lhs_base = narrowing_base(step.ssa_lhs);
      if(!lhs_base.empty() && tracked.count(lhs_base) != 0)
      {
        if(narrowing_rhs_ok(step.ssa_rhs, lhs_base))
        {
          narrowing_scan_accepted(step.ssa_rhs, lhs_base, ns, tracked, usage);
          lhs_handled = true;
        }
        else
          usage[lhs_base].unusable = true;
      }
    }

    if(!step.ssa_rhs.is_nil() && !lhs_handled)
      narrowing_scan(step.ssa_rhs, ns, tracked, usage);
    // for an assignment or a decl cond_expr is just `ssa_lhs == ssa_rhs`, so
    // scanning it would re-read the target as a bare use of itself
    if(!step.cond_expr.is_nil() && !step.is_assignment() && !step.is_decl())
      narrowing_scan(step.cond_expr, ns, tracked, usage);
    if(!step.guard.is_nil())
      narrowing_scan(step.guard, ns, tracked, usage);
  }

  for(const auto &v : tracked)
  {
    const auto it = usage.find(v);
    if(it == usage.end() || it->second.unusable || !it->second.read_seen)
      continue;
    const auto &ws = writes.count(v) != 0 ? writes.at(v) : private_writes.at(v);
    const auto full = pointer_offset_bits(ws.front().s_it->ssa_lhs.type(), ns);
    if(!full.has_value() || *full <= 0)
      continue;
    const std::size_t lo = it->second.lo;
    const std::size_t hi = it->second.hi;
    // byte_extract addresses bytes, so only a byte-aligned slice can be named
    if(lo % 8 != 0 || (hi - lo) % 8 != 0)
      continue;
    if(hi - lo >= numeric_cast_v<std::size_t>(*full))
      continue;
    narrowings.emplace(v, narrowingt{lo, hi - lo});
  }
}

exprt lazy_pot::narrowed_value(const irep_idt &variable, const exprt &value) const
{
  const auto it = narrowings.find(variable);
  if(it == narrowings.end())
    return value;
  return make_byte_extract(
    value,
    from_integer(it->second.offset_bits / 8, c_index_type()),
    unsignedbv_typet(it->second.width_bits));
}

typet lazy_pot::narrowed_type(const irep_idt &variable, const typet &type) const
{
  const auto it = narrowings.find(variable);
  if(it == narrowings.end())
    return type;
  return unsignedbv_typet(it->second.width_bits);
}



/// Is this expression a whole-array constant whose elements are all the same
/// value? `array_of` says so directly; an `array` literal has to be checked.
/// Anything else cannot serve as the value an element holds before any write.
static std::optional<exprt> uniform_array_value(const exprt &expr)
{
  if(expr.id() == ID_array_of)
    return to_array_of_expr(expr).what();

  if(expr.id() == ID_array && !expr.operands().empty())
  {
    const exprt &first = expr.operands().front();
    for(const auto &op : expr.operands())
      if(op != first)
        return {};
    return first;
  }

  return {};
}

void lazy_pot::compute_array_rf(const symex_target_equationt &equation)
{
  array_rf_writes.clear();
  array_rf_default.clear();
  if(!array_rf)
    return;

  // candidates: shared objects of array type that are still in the chain
  std::set<irep_idt> candidates;
  for(const auto &v : global_variables)
  {
    if(writes.count(v) == 0 || writes.at(v).empty())
      continue;
    if(writes.at(v).front().s_it->ssa_lhs.type().id() == ID_array)
      candidates.insert(v);
  }
  if(candidates.empty())
    return;

  // Every occurrence of one of these objects has to be either the base of a
  // `with` or the array of an `index`. A use of the array as a whole -- a copy,
  // a comparison, an argument -- has no index to match on, so the object keeps
  // its chain. Taking an address does not read the value.
  std::set<irep_idt> opaque;
  std::map<irep_idt, std::vector<std::pair<irep_idt, exprt>>> index_uses;
  const bool why = getenv("LAZYPO_ARRAY_WHY") != nullptr;
  std::function<void(const exprt &, const irep_idt &)> scan =
    [&](const exprt &expr, const irep_idt &parent) {
    if(expr.id() == ID_address_of)
      return;

    if(expr.id() == ID_index)
    {
      const auto &idx = to_index_expr(expr);
      if(idx.array().id() == ID_symbol)
      {
        const irep_idt id = to_symbol_expr(idx.array()).get_identifier();
        const irep_idt base = narrowing_base(idx.array());
        if(candidates.count(base) != 0)
        {
          index_uses[base].emplace_back(id, idx.index());
          scan(idx.index(), expr.id());
          return;
        }
      }
    }

    if(expr.id() == ID_with && !expr.operands().empty() &&
       expr.operands()[0].id() == ID_symbol &&
       candidates.count(narrowing_base(expr.operands()[0])) != 0)
    {
      for(std::size_t i = 1; i < expr.operands().size(); ++i)
        scan(expr.operands()[i], expr.id());
      return;
    }

    if(expr.id() == ID_symbol)
    {
      const irep_idt base = narrowing_base(expr);
      if(candidates.count(base) != 0 && opaque.insert(base).second && why)
        std::cerr << "ARRAY_WHY_DETAIL " << base << " used bare inside a "
                  << parent << "\n";
      return;
    }

    for(const auto &op : expr.operands())
      scan(op, expr.id());
  };

  for(const auto &step : equation.SSA_steps)
  {
    // `a#3 = a#2` copies one version of the object to another. It does not
    // observe the array as a whole, so it must not force the chain to stay --
    // and the lambda cannot tell, since it never sees the left-hand side.
    // twalock declined for exactly this: __twa_array#3 = __twa_array#<prev>.
    const bool own_copy =
      step.is_assignment() && !step.ssa_lhs.is_nil() &&
      step.ssa_rhs.id() == ID_symbol &&
      narrowing_base(step.ssa_rhs) == narrowing_base(step.ssa_lhs) &&
      candidates.count(narrowing_base(step.ssa_lhs)) != 0;

    if(!step.ssa_rhs.is_nil() && !own_copy)
      scan(
          step.ssa_rhs,
          step.ssa_lhs.is_nil()
            ? irep_idt{"assignment-rhs"}
            : irep_idt{"assignment-rhs, lhs=" +
                       id2string(to_symbol_expr(step.ssa_lhs).get_identifier())});
    if(!step.cond_expr.is_nil() && !step.is_assignment() && !step.is_decl())
      scan(step.cond_expr, "cond_expr");
    if(!step.guard.is_nil())
      scan(step.guard, "guard");
  }

  // how each write decomposes, by the assignment that produces its symbol
  std::map<irep_idt, exprt> defining_rhs;
  for(const auto &step : equation.SSA_steps)
  {
    if(!step.is_assignment() || step.ssa_lhs.is_nil())
      continue;
    if(candidates.count(narrowing_base(step.ssa_lhs)) == 0)
      continue;
    defining_rhs.emplace(
      to_symbol_expr(step.ssa_lhs).get_identifier(), step.ssa_rhs);
  }

  const bool explain = getenv("LAZYPO_ARRAY_WHY") != nullptr;
  for(const auto &variable : candidates)
  {
    if(opaque.count(variable) != 0)
    {
      if(explain)
        std::cerr << "ARRAY_WHY " << variable
                  << " declined: used as a whole object somewhere\n";
      continue;
    }

    // every index use has to name a shared read event, since that is what
    // places it in the schedule
    std::set<irep_idt> read_symbols;
    for(const auto &r : reads.count(variable) ? reads.at(variable)
                                              : std::vector<shared_event>{})
      read_symbols.insert(to_symbol_expr(r.s_it->ssa_lhs).get_identifier());
    bool indices_placed = true;
    for(const auto &use : index_uses[variable])
      if(read_symbols.count(use.first) == 0)
        indices_placed = false;
    if(!indices_placed)
    {
      if(explain)
        std::cerr << "ARRAY_WHY " << variable
                  << " declined: an index() does not name a shared read event\n";
      continue;
    }

    std::vector<array_writet> decomposed;
    std::optional<exprt> initial;
    bool ok = true;
    const auto &ws = writes.at(variable);
    for(std::size_t i = 0; i < ws.size(); ++i)
    {
      const irep_idt id = to_symbol_expr(ws[i].s_it->ssa_lhs).get_identifier();
      const auto it = defining_rhs.find(id);
      if(it == defining_rhs.end())
      {
        if(getenv("LAZYPO_ARRAY_WHY") != nullptr)
          std::cerr << "ARRAY_WHY_NODEF " << variable << " write symbol " << id
                    << " has no defining assignment in the equation\n";
        ok = false;
        break;
      }
      const exprt &rhs = it->second;
      if(rhs.id() == ID_with && rhs.operands().size() == 3 &&
         narrowing_base(rhs.operands()[0]) == variable)
      {
        decomposed.push_back(
          array_writet{i, false, rhs.operands()[1], rhs.operands()[2]});
        continue;
      }
      if(rhs.id() == ID_symbol && narrowing_base(rhs) == variable)
        continue; // a copy of the previous version writes nothing new

      const auto uniform = uniform_array_value(rhs);
      if(uniform.has_value())
      {
        if(!initial.has_value())
          initial = uniform;
        decomposed.push_back(
          array_writet{i, true, nil_exprt{}, uniform.value()});
        continue;
      }
      if(getenv("LAZYPO_ARRAY_WHY") != nullptr)
        std::cerr << "ARRAY_WHY_WRITE " << variable << " rhs is " << rhs.id()
                  << (rhs.id() == ID_with && !rhs.operands().empty()
                        ? " over " + id2string(narrowing_base(rhs.operands()[0]))
                        : std::string{})
                  << "\n";
      ok = false; // a havoc, a copy, a non-uniform literal: no single value
      break;
    }
    if(!ok || !initial.has_value())
    {
      if(explain)
        std::cerr << "ARRAY_WHY " << variable << " declined: "
                  << (ok ? "no uniform constant initialiser"
                         : "a write is not a single-index update")
                  << "\n";
      continue;
    }

    // Cost model. The chain amortises over reads and wins on a narrow object
    // read often; the nested selection wins on a wide object written rarely.
    // Require a clear margin, so a formula is not perturbed for little.
    const typet &t = ws.front().s_it->ssa_lhs.type();
    const auto array_bits = pointer_offset_bits(t, ns);
    const auto elem_bits = pointer_offset_bits(to_array_type(t).element_type(), ns);
    if(!array_bits.has_value() || !elem_bits.has_value() || *elem_bits <= 0)
      continue;
    const double W = static_cast<double>(ws.size());
    const double Rd =
      reads.count(variable) ? static_cast<double>(reads.at(variable).size()) : 0;
    const double R = static_cast<double>(rounds);
    const double index_bits = 32;
    const double chain_cost = (W + Rd) * R * static_cast<double>(array_bits->to_long());
    // a read at round r sees the writes of every earlier round too, so the
    // selection is W*R deep on average half the time
    const double rf_cost =
      Rd * R * (W * R / 2.0) * (static_cast<double>(elem_bits->to_long()) + index_bits);
    if(rf_cost <= 0 || chain_cost < 2.0 * rf_cost)
    {
      if(explain)
        std::cerr << "ARRAY_WHY " << variable
                  << " declined by the cost model: chain=" << chain_cost
                  << " selection=" << rf_cost << " ratio="
                  << (rf_cost > 0 ? chain_cost / rf_cost : 0)
                  << " (W=" << W << " reads=" << Rd << " array_bits="
                  << array_bits->to_long() << ")\n";
      continue;
    }

    if(explain)
      std::cerr << "ARRAY_WHY " << variable << " ACCEPTED: chain=" << chain_cost
                << " selection=" << rf_cost << " ratio=" << chain_cost / rf_cost
                << "\n";
    array_rf_writes.emplace(variable, std::move(decomposed));
    array_rf_default.emplace(variable, initial.value());
  }
}

void lazy_pot::create_array_rf_constraints(symex_target_equationt &equation)
{
  if(array_rf_writes.empty())
    return;

  // position of an event in the schedule chain, for the "writes before this
  // read" test; the same lexicographic order the chain is sorted by
  const auto before = [](std::size_t ra, const shared_event &a,
                         std::size_t rb, const shared_event &b) {
    return std::make_tuple(ra, a.thread, a.label, a.num) <
           std::make_tuple(rb, b.thread, b.label, b.num);
  };

  std::size_t fresh = 0;
  std::map<std::pair<irep_idt, std::string>, ssa_exprt> replacement;

  for(const auto &entry : array_rf_writes)
  {
    const irep_idt &variable = entry.first;
    const auto &ws = writes.at(variable);
    const exprt &dflt = array_rf_default.at(variable);
    const typet elem_type = to_array_type(
      ws.front().s_it->ssa_lhs.type()).element_type();

    std::map<irep_idt, const shared_event *> read_of;
    if(reads.count(variable))
      for(const auto &r : reads.at(variable))
        read_of.emplace(to_symbol_expr(r.s_it->ssa_lhs).get_identifier(), &r);

    // rewrite every index(V#k, j) into a fresh scalar, and say what it holds
    std::function<void(exprt &)> rewrite = [&](exprt &expr) {
      if(expr.id() == ID_address_of)
        return;

      if(expr.id() == ID_index && expr.operands()[0].id() == ID_symbol &&
         narrowing_base(expr.operands()[0]) == variable)
      {
        const irep_idt id =
          to_symbol_expr(expr.operands()[0]).get_identifier();
        const auto rd = read_of.find(id);
        if(rd != read_of.end())
        {
          exprt index = expr.operands()[1];
          rewrite(index);
          const auto key =
            std::make_pair(id, index.pretty());
          auto it = replacement.find(key);
          if(it == replacement.end())
          {
            // An ssa_exprt, not a plain symbol: this replaces an
            // index() inside existing SSA steps, and build_goto_trace
            // asserts that what it finds there carries ID_C_SSA_symbol.
            // A bare symbol_exprt passes every solver path and then
            // aborts in "Building error trace" -- so it only shows up
            // when a counterexample is actually built, which is exactly
            // what --graphml-witness does and what no SUCCESSFUL run
            // ever reaches.
            const ssa_exprt elt{symbol_exprt{
              "arf_" + id2string(id) + "_" + std::to_string(fresh++),
              elem_type}};

            for(std::size_t round = 1; round <= rounds; ++round)
            {
              // The write that wins is the LAST one before this read in
              // schedule order, so the candidates have to be folded in
              // increasing position -- the one wrapped last ends up outermost
              // and takes priority. Folding them in any other order silently
              // elects the wrong write: with the writes walked backwards and
              // the rounds forwards, the outermost became the FIRST write at
              // the LAST round, i.e. the zero initialiser, which forced every
              // read to 0 and proved away a reachable violation.
              std::vector<std::pair<std::tuple<std::size_t, unsigned, unsigned, unsigned>,
                                    std::size_t>> candidates;
              for(std::size_t wi = 0; wi < entry.second.size(); ++wi)
              {
                const auto &aw = entry.second[wi];
                for(std::size_t wr = 1; wr <= rounds; ++wr)
                {
                  if(!before(wr, ws[aw.event], round, *rd->second))
                    continue;
                  candidates.emplace_back(
                    std::make_tuple(wr, ws[aw.event].thread, ws[aw.event].label,
                                    ws[aw.event].num),
                    wi);
                }
              }
              std::sort(candidates.begin(), candidates.end());

              exprt selected = typecast_exprt::conditional_cast(dflt, elem_type);
              for(const auto &candidate : candidates)
              {
                const auto &aw = entry.second[candidate.second];
                const symbol_exprt wexec = create_exec_symbol(
                  ws[aw.event].label, ws[aw.event].num, ws[aw.event].thread,
                  std::get<0>(candidate.first));
                exprt matches = aw.whole_array
                  ? static_cast<exprt>(wexec)
                  : static_cast<exprt>(and_exprt{
                      wexec,
                      equal_exprt{
                        typecast_exprt::conditional_cast(aw.index, index.type()),
                        index}});
                selected = if_exprt{
                  matches,
                  typecast_exprt::conditional_cast(aw.value, elem_type),
                  selected};
              }
              const symbol_exprt rexec = create_exec_symbol(
                rd->second->label, rd->second->num, rd->second->thread, round);
              equation.constraint(
                implies_exprt{rexec, equal_exprt{elt, selected}},
                "array read-from " + id2string(variable),
                rd->second->s_it->source);
            }

            it = replacement.emplace(key, elt).first;
          }
          expr = it->second;
          return;
        }
      }

      for(auto &op : expr.operands())
        rewrite(op);
    };

    for(auto &step : equation.SSA_steps)
    {
      if(step.ignore)
        continue;
      // the assignments that build the array are no longer needed: nothing
      // reads the array value any more
      if(step.is_assignment() && !step.ssa_lhs.is_nil() &&
         narrowing_base(step.ssa_lhs) == variable)
      {
        step.ignore = true;
        continue;
      }
      if(!step.ssa_rhs.is_nil())
        rewrite(step.ssa_rhs);
      if(!step.cond_expr.is_nil())
        rewrite(step.cond_expr);
      if(!step.guard.is_nil())
        rewrite(step.guard);
    }
  }
}

void lazy_pot::compute_private_objects()
{
  // LAZYPO_THREAD_TALLY reports the classification itself, independently of
  // whether the flag then acts on it: how many threads actually touch each
  // shared object, against the per-program decision goto-symex made.
  if(getenv("LAZYPO_THREAD_TALLY") != nullptr)
  {
    for(const auto &gv : global_variables)
    {
      std::set<unsigned> write_threads, read_threads, all;
      std::size_t nw = 0, nr = 0;
      if(writes.count(gv))
        for(const auto &w : writes.at(gv))
        {
          write_threads.insert(w.thread);
          ++nw;
        }
      if(reads.count(gv))
        for(const auto &r : reads.at(gv))
        {
          read_threads.insert(r.thread);
          ++nr;
        }
      all = write_threads;
      all.insert(read_threads.begin(), read_threads.end());
      std::cerr << "THREAD_TALLY " << gv << " threads=" << all.size()
                << " write_threads=" << write_threads.size()
                << " read_threads=" << read_threads.size() << " writes=" << nw
                << " reads=" << nr << "\n";
    }
  }

  private_objects.clear();
  if(!thread_private)
    return;

  // Classify first, and only act if the result is worth having. Rewriting the
  // chain renumbers variables, and a multi-million-clause SAT search is
  // chaotic in that respect: on elimination_backoff_stack only 38 of 9472
  // shared accesses are private, the formula shrinks by 0.09%, and the search
  // still lands on a trajectory 1.44x worse (283s -> 408s, three runs each).
  // Measured against 13.4% of accesses on 28-race_reach_81-list_racing, where
  // the same change takes 20.7% off the formula. So: do not perturb a formula
  // this is not materially improving.
  std::set<irep_idt> candidates;
  double private_cost = 0, total_cost = 0;

  for(const auto &variable : global_variables)
  {
    std::set<unsigned> threads;
    std::size_t accesses = 0;
    if(writes.count(variable) != 0)
      for(const auto &w : writes.at(variable))
      {
        threads.insert(w.thread);
        ++accesses;
      }
    if(reads.count(variable) != 0)
      for(const auto &r : reads.at(variable))
      {
        threads.insert(r.thread);
        ++accesses;
      }

    // Weigh an access by the width it carries, not by its count. A chain link
    // costs width bits, so counting accesses alone misjudges a program whose
    // private objects are many but narrow: on twalock more than 1% of the
    // accesses are private and removing them takes 1491 clauses out of 212
    // million -- 0.0007% -- while still renumbering every variable, which cost
    // 12% of the runtime.
    const typet *t = nullptr;
    if(writes.count(variable) != 0 && !writes.at(variable).empty())
      t = &writes.at(variable).front().s_it->ssa_lhs.type();
    else if(reads.count(variable) != 0 && !reads.at(variable).empty())
      t = &reads.at(variable).front().s_it->ssa_lhs.type();
    double width = 32; // a type with no fixed size still costs something
    if(t != nullptr)
    {
      const auto bits = pointer_offset_bits(*t, ns);
      if(bits.has_value() && bits->to_long() > 0)
        width = static_cast<double>(bits->to_long());
    }
    const double cost = static_cast<double>(accesses) * width;
    total_cost += cost;
    // One thread: no other thread can interleave a write, so the schedule
    // cannot change what a read sees.
    if(threads.size() <= 1)
    {
      candidates.insert(variable);
      private_cost += cost;
    }
  }

  // A hundredth of the chain's cost is the threshold. The three measured
  // points: 28-race_reach_81 removes 13.4% and the formula drops 20.7%;
  // elimination_backoff_stack removes 0.4% and the formula drops 0.09% while
  // the search gets 1.44x worse; twalock removes 0.0007% and the search gets
  // 12% worse. Below the threshold the chain being rewritten is too small to
  // pay for renumbering every variable after it.
  if(total_cost <= 0 || private_cost * 100 < total_cost)
    return;

  for(auto it = global_variables.begin(); it != global_variables.end();)
  {
    if(candidates.count(*it) != 0)
    {
      private_objects.insert(*it);
      auto w = writes.find(*it);
      if(w != writes.end())
      {
        private_writes.emplace(*it, std::move(w->second));
        writes.erase(w);
      }
      auto r = reads.find(*it);
      if(r != reads.end())
      {
        private_reads.emplace(*it, std::move(r->second));
        reads.erase(r);
      }
      it = global_variables.erase(it);
    }
    else
      ++it;
  }
}

/// "this access happens at all", i.e. the thread reaches it within the round
/// bound. Exactly the disjunction over rounds of the per-round exec, which is
/// what a private object's read-from has to be guarded by: which round it lands
/// in cannot change the answer, only whether it is reached.
exprt lazy_pot::happens_in_any_round(const shared_event &event)
{
  exprt::operandst per_round;
  per_round.reserve(rounds);
  for(std::size_t round = 1; round <= rounds; ++round)
    per_round.push_back(
      create_exec_symbol(event.label, event.num, event.thread, round));
  if(per_round.size() == 1)
    return per_round.front();
  return disjunction(per_round);
}

void lazy_pot::create_private_constraints(symex_target_equationt &equation)
{
  for(const auto &variable : private_objects)
  {
    if(private_writes.count(variable) == 0 || private_reads.count(variable) == 0)
      continue; // nothing observes the object, so it needs no chain at all

    const auto &ws = private_writes.at(variable);
    const typet chain_type =
      narrowed_type(variable, ws.front().s_it->ssa_lhs.type());

    // Same convention as create_write_constraints: the value before any write
    // is the first write's own ssa_lhs, and a read with nothing before it is
    // left unconstrained rather than tied to that sentinel.
    std::vector<exprt> chain;
    chain.reserve(ws.size());
    exprt previous = narrowed_value(variable, ws.front().s_it->ssa_lhs);

    for(const auto &write : ws)
    {
      const symbol_exprt lazy_variable_exprt{
        id2string(to_symbol_expr(write.s_it->ssa_lhs).get_identifier()) +
          "_PRIV",
        chain_type};

      equation.constraint(
        equal_exprt{
          lazy_variable_exprt,
          if_exprt{happens_in_any_round(write),
                   narrowed_value(variable, write.s_it->ssa_lhs),
                   typecast_exprt::conditional_cast(previous, chain_type)}},
        "private write constraint " + id2string(variable),
        write.s_it->source);

      chain.push_back(lazy_variable_exprt);
      previous = lazy_variable_exprt;
    }

    for(const auto &read : private_reads.at(variable))
    {
      // The last write before this read in the thread's own program order.
      // Scanning the whole vector rather than stopping at the first write that
      // is not earlier: the chain is built in collection order, and this does
      // not have to assume that order is sorted by (label, num).
      bool found = false;
      std::size_t before = 0;
      std::pair<unsigned, unsigned> best{0, 0};
      for(std::size_t i = 0; i < ws.size(); ++i)
      {
        const std::pair<unsigned, unsigned> here{ws[i].label, ws[i].num};
        if(here < std::make_pair(read.label, read.num) &&
           (!found || best < here))
        {
          found = true;
          best = here;
          before = i;
        }
      }
      if(!found)
        continue; // reads the pre-first-write value, which constrains nothing

      equation.constraint(
        implies_exprt{
          happens_in_any_round(read),
          equal_exprt{narrowed_value(variable, read.s_it->ssa_lhs),
                      typecast_exprt::conditional_cast(
                        chain[before], chain_type)}},
        "private read constraint " + id2string(variable),
        read.s_it->source);
    }
  }
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

void lazy_pot::create_write_constraints(
  symex_target_equationt &equation)
{
  if(getenv("LAZYPO_DEAD_AUDIT") != nullptr)
    dead_audit(equation);

  // Both this chain and create_read_constraints, which runs straight after,
  // are built from it.
  compute_narrowings(equation);

  for(auto global_variable : global_variables)
  {
    if(this->writes.count(global_variable) == 0)
      continue;
    const ssa_exprt &initial =
      this->writes.at(global_variable).front().s_it->ssa_lhs;
    const typet chain_type = narrowed_type(global_variable, initial.type());

    // The chain's round-0 element is the object's value before the first
    // write. Unnarrowed that is the SSA symbol itself; narrowed it has to be a
    // symbol of the slice's type, since the chain is typed symbol_exprt, so
    // name one and tie it to the slice.
    symbol_exprt sentinel = initial;
    exprt previous = initial;
    if(narrowings.count(global_variable) != 0)
    {
      sentinel = symbol_exprt{
        id2string(initial.get_identifier()) + "_T0_L0_R0", chain_type};
      equation.constraint(
        equal_exprt{sentinel, narrowed_value(global_variable, initial)},
        "write constraint " + id2string(global_variable),
        this->writes.at(global_variable).front().s_it->source);
      previous = sentinel;
    }

    irep_idt sentinel_id_name = "id_T0_L0_N0_R0_V"+id2string(global_variable);
    symbol_exprt sentinel_id_symbol{sentinel_id_name, unsignedbv_typet(bit_writes[global_variable])};
    lazy_variable first_lazy_struct = lazy_variable{
      0, 0, 0, 0, 0, sentinel, sentinel_id_symbol};
    this->lazy_variables[global_variable].emplace_back(first_lazy_struct);

    for(std::size_t round = 1; round <= rounds; ++round)
    {
      for(const auto &write : this->writes.at(global_variable))
      {
        const symbol_exprt lazy_variable_exprt = create_lazy_symbol(
          write.label,
          write.thread,
          round,
          write.s_it->ssa_lhs,
          chain_type);
        irep_idt id_name = "id_T" + std::to_string(write.thread) + "_L" +
                             std::to_string(write.label) + "_N" + std::to_string(write.num) +
                             "_R" + std::to_string(round)+ "_V"+id2string(global_variable);
        symbol_exprt id_symbol{id_name, unsignedbv_typet(bit_writes[global_variable])};
        lazy_variable lazy_struct =
          lazy_variable{round, write.label, write.num, write.thread, 0, lazy_variable_exprt,
            id_symbol};
        this->lazy_variables[global_variable].emplace_back(lazy_struct);

        const symbol_exprt exec =
          create_exec_symbol(write.label, write.num, write.thread, round);

        if(array_rf_writes.count(global_variable) == 0)
        {
          equal_exprt constraint{
            lazy_variable_exprt,
            if_exprt{exec,
                     narrowed_value(global_variable, write.s_it->ssa_lhs),
                     typecast_exprt::conditional_cast(previous, chain_type)}};

          equation.constraint(
            constraint,
            "write constraint " + id2string(global_variable),
            write.s_it->source);
        }

        previous = lazy_variable_exprt;
      }
    }

    auto &lvs = this->lazy_variables[global_variable];
    std::sort(lvs.begin(), lvs.end(),
      [](const lazy_variable &a, const lazy_variable &b) {
        return std::tie(a.round, a.thread, a.label, a.num)
             < std::tie(b.round, b.thread, b.label, b.num);
      });

    const auto &front_src = this->writes.at(global_variable).front().s_it->source;
    // id-inline: l'id e' una costante (indice lex), non serve un simbolo dedicato.
    // get_id_symbol / LW ritornano from_integer(id) direttamente, quindi niente
    // simbolo exptr_id ne' la sua equazione di definizione.
    for(std::size_t i = 0; i < lvs.size(); ++i)
      lvs[i].id = static_cast<unsigned>(i);
    (void)front_src;
  }
}

void lazy_pot::create_read_constraints(
  symex_target_equationt &equation)
{
  for(auto global_variable : global_variables)
  {
    if(this->reads.count(global_variable) == 0)
      continue;
    // an --array-rf object answers its element reads directly; it has no
    // array value for a read to be tied to
    if(array_rf_writes.count(global_variable) != 0)
      continue;
    const bool implication_form = read_implication;

    for(const auto &read : this->reads.at(global_variable))
    {
      if(implication_form)
      {
        // One-hot selection stated directly. At most one round is enabled for
        // a given access, so at most one of these is active and it names the
        // same write the mux would have selected.
        for(std::size_t round = 1; round <= rounds; ++round)
        {
          // still created unconditionally: registering the symbol is what the
          // rest of the encoding looks it up by
          const symbol_exprt exec =
            create_exec_symbol(read.label, read.num, read.thread, round);

          std::optional<symbol_exprt> previous = previous_shared(
            global_variable, read.label, read.num, read.thread, round);
          if(!previous.has_value())
            continue; // that branch reads `read = read`, which constrains nothing

          implies_exprt constraint{
            exec,
            equal_exprt{
              narrowed_value(global_variable, read.s_it->ssa_lhs),
              typecast_exprt::conditional_cast(
                previous.value(),
                narrowed_type(global_variable, read.s_it->ssa_lhs.type()))}};
          equation.constraint(
            constraint,
            "read constraint " + id2string(global_variable),
            read.s_it->source);
        }
        continue;
      }

      const exprt read_value = narrowed_value(global_variable, read.s_it->ssa_lhs);
      const typet read_type =
        narrowed_type(global_variable, read.s_it->ssa_lhs.type());
      exprt temp_constraint = read_value;
      for(std::size_t round = rounds; round >= 1; --round)
      {
        const symbol_exprt exec =
          create_exec_symbol(read.label, read.num, read.thread, round);

        std::optional<symbol_exprt> previous =
          previous_shared(global_variable, read.label, read.num, read.thread, round);
        if(previous.has_value())
        {
          temp_constraint = if_exprt{exec,
            typecast_exprt::conditional_cast(previous.value(), read_type),
            temp_constraint};
        }
        else {
          temp_constraint = if_exprt{exec, read_value, temp_constraint};
        }
      }
      equal_exprt final_constraint{read_value, temp_constraint};
      equation.constraint(
        final_constraint,
        "read constraint " + id2string(global_variable),
        read.s_it->source);
    }
    std::reverse(lazy_variables_read[global_variable].begin(), lazy_variables_read[global_variable].end());
  }
}

std::optional<symbol_exprt> lazy_pot::previous_shared(
  irep_idt variable,
  unsigned label,
  unsigned num,
  unsigned thread,
  std::size_t round)
{
  // Was an O(|lazy_variables[variable]|) linear scan; lazy_variables[variable]
  // is already sorted lexicographically by (round, thread, label, num) (see
  // create_write_constraints / validate_access_order), exactly like the POR
  // path's get_previous_write, so this can use the same lower_bound approach.
  // Behaviourally identical to the previous linear scan, including its
  // pre-existing "no update happened" special case below.
  if(lazy_variables.count(variable) == 0)
    return std::nullopt;
  const auto &v = lazy_variables.at(variable);
  const auto qk = std::make_tuple(round, thread, label, num);
  const auto it = std::lower_bound(
    v.begin(),
    v.end(),
    qk,
    [](const lazy_variable &lv, const std::tuple<std::size_t, unsigned, unsigned, unsigned> &k) {
      return std::make_tuple(lv.round, lv.thread, lv.label, lv.num) < k;
    });
  if(it != v.begin())
    return std::prev(it)->symbol;
  if(label > v.front().label || (label <= v.front().label && num > v.front().num))
    return std::nullopt;
  return v.front().symbol;
}

exprt lazy_pot::active_at_turn(
  unsigned thread,
  unsigned label,
  std::size_t round)
{
  // active_thread_t^(r) del paper: valutata al turno round-robin di t nel round
  // r, cioe' l'ultima versione SSA del flag di attivita' scritta prima della
  // posizione (round, thread, label, 0). Vera esattamente quando t e' stato
  // creato prima di quel turno e non e' terminato prima di esso.
  if(label == 0)
    return true_exprt{};
  const std::string active_name =
    "__CPROVER_active_thread_T" + std::to_string(thread);
  std::optional<symbol_exprt> active =
    previous_shared(active_name, label, 0, thread, round);
  if(active.has_value())
    return active.value();
  return true_exprt{};
}

void lazy_pot::check_shared_event(
    symex_target_equationt &equation)
{
  symex_target_equationt temp_equation{equation};
  temp_equation.clear();

  auto ssa_steps = equation.SSA_steps;
  std::unordered_set<std::size_t> assignments;

  for(symex_target_equationt::SSA_stepst::const_iterator s_it =
        ssa_steps.begin();
      s_it != ssa_steps.end();
      s_it++)
  {
    if (s_it->is_assignment())
    {
      assignments.insert(s_it->ssa_lhs.hash());
    }
  }

  for(symex_target_equationt::SSA_stepst::const_iterator s_it =
        ssa_steps.begin();
      s_it != ssa_steps.end();
      s_it++)
  {
    bool assigned = true;
    if (s_it->is_shared_write())
    {
      if (assignments.count(s_it->ssa_lhs.hash()) == 0)
      {
        assigned = false;
      }
    }
    if (!assigned)
    {
      equation.SSA_steps.pop_front();
    }
    else
    {
      SSA_stept step{equation.SSA_steps.front()};
      step.type = equation.SSA_steps.front().type;

      equation.SSA_steps.pop_front();
      temp_equation.SSA_steps.emplace_back(step);
    }
  }
  equation = temp_equation;
}

void lazy_pot::create_cs_constraint(
  symex_target_equationt &equation)
{
  std::set<irep_idt> hoisted_guards;

  if(getenv("LAZYPO_GUARD_STATS") != nullptr)
  {
    const auto nodes = [](const exprt &e) {
      std::size_t n = 0;
      std::vector<const exprt *> st{&e};
      while(!st.empty())
      {
        const exprt *cur = st.back();
        st.pop_back();
        ++n;
        for(const auto &op : cur->operands())
          st.push_back(&op);
      }
      return n;
    };

    std::size_t slots = 0, trivial = 0, tree = 0, biggest = 0;
    std::unordered_set<std::size_t> distinct;
    std::size_t distinct_tree = 0;
    for(const auto &per_thread : guards)
    {
      for(const auto &per_label : per_thread.second)
      {
        for(const auto &g : per_label.second)
        {
          ++slots;
          if(g.is_true() || g.is_false())
          {
            ++trivial;
            continue;
          }
          const std::size_t n = nodes(g);
          tree += n;
          if(n > biggest)
            biggest = n;
          if(distinct.insert(g.hash()).second)
            distinct_tree += n;
        }
      }
    }
    std::cerr << "GUARDS slots=" << slots << " trivial=" << trivial
              << " distinct=" << distinct.size() << " rounds=" << rounds
              << "\n";
    std::cerr << "GUARDS nodes_over_slots=" << tree
              << " nodes_over_distinct=" << distinct_tree
              << " biggest=" << biggest << "\n";
    // Each non-trivial guard is conjoined once per round, so this is what the
    // constraint tree carries for guards before any sharing is accounted for.
    std::cerr << "GUARDS tree_cost_in_cs=" << (tree * rounds) << "\n";
  }

  for(unsigned thread = 0; thread <= threads; ++thread)
  {
    unsigned max_num = labels[thread];

    // n_bit is no longer used to size cs itself (see below), but is kept
    // computed/populated since other cs-adjacent call sites historically
    // relied on it; harmless if unused.
    n_bit[thread] = 0 ? 0 : 32 - __builtin_clz(max_num + 1);

    // Order/thermometer encoding of cs(thread,*): GE(thread,round,i) means
    // cs(thread,round) >= i, for i in 1..max_num+1. Two monotonicity
    // families replace the old bitvector cs and its monotone-chain/bound
    // constraints:
    //   (C1) within a round, GE is monotone in the threshold i:
    //        GE(t,r,i+1) => GE(t,r,i), for i in 1..max_num.
    //   (C2) across rounds, GE is monotone in r for a fixed threshold:
    //        GE(t,r-1,i) => GE(t,r,i), for i in 1..max_num+1.
    //   (C3) cs^0 = 0: GE(t,0,i) is false for every i in 1..max_num+1.
    // cs^R <= max_num+1 is now just the encoding's domain bound (there is
    // no threshold beyond max_num+1), so nothing to assert for it.
    for(size_t round = 0; round <= rounds; ++round)
    {
      for(unsigned i = 1; i <= max_num; ++i)
        equation.constraint(
          implies_exprt{
            create_ge_symbol(thread, round, i + 1),
            create_ge_symbol(thread, round, i)},
          "cs order monotonicity (threshold)",
          equation.SSA_steps.begin()->source);

      if(round == 0)
      {
        for(unsigned i = 1; i <= max_num + 1; ++i)
          equation.constraint(
            not_exprt{create_ge_symbol(thread, 0, i)},
            "cs order initial",
            equation.SSA_steps.begin()->source);
      }
      else
      {
        for(unsigned i = 1; i <= max_num + 1; ++i)
          equation.constraint(
            implies_exprt{
              create_ge_symbol(thread, round - 1, i),
              create_ge_symbol(thread, round, i)},
            "cs order monotonicity (round)",
            equation.SSA_steps.begin()->source);
      }
    }
    for (size_t label = 0; label <= labels[thread]; label++)
    {
      for(size_t round = 1; round <= rounds; ++round)
      {
        symbol_exprt enabled =
          create_enabled_symbol(label, thread, round);

        exprt active_thread_value = active_at_turn(thread, label, round);

        if (label != 0) {
          // Enabled(l,t,r) = (cs^r > l) & (cs^{r-1} <= l)
          //                = GE(t,r,l+1) & !GE(t,r-1,l+1)
          symbol_exprt ge_curr =
            create_ge_symbol(thread, round, static_cast<unsigned>(label) + 1);
          symbol_exprt ge_prev =
            create_ge_symbol(thread, round - 1, static_cast<unsigned>(label) + 1);
          and_exprt expr_3{ge_curr, not_exprt{ge_prev}};
          equal_exprt enabled_expr{enabled, expr_3};
          simplify(enabled_expr, ns);
          equation.constraint(
            enabled_expr, "cs constraint", equation.SSA_steps.begin()->source);
          implies_exprt active_expr{enabled, active_thread_value};
          simplify(active_expr, ns);
          equation.constraint(active_expr, "cs constraint", equation.SSA_steps.begin()->source);
        }
        else {
          equal_exprt enabled_expr{enabled, false_exprt{}};
          simplify(enabled_expr, ns);
          equation.constraint(
            enabled_expr, "cs constraint", equation.SSA_steps.begin()->source);
        }

        static const bool hoist_guards =
          getenv("LAZYPO_GUARD_HOIST") != nullptr;

        const auto git = guards[thread].find(label);
        const bool has_guards = (label > 0 && git != guards[thread].end());
        unsigned nmax =
          has_guards ? static_cast<unsigned>(git->second.size()) : 1;
        for(unsigned num = 0; num < nmax; ++num)
        {
          exprt expr_5;
          if (has_guards) {
            exprt g = git->second.at(num);
            if(hoist_guards && !g.is_true() && !g.is_false())
            {
              // Define the guard once and refer to it by name afterwards, so
              // the round loop conjoins a literal rather than re-embedding the
              // whole path condition. The definition itself costs no clauses:
              // a top-level `fresh symbol = expr` is bound to the expression's
              // literal rather than asserted.
              const irep_idt gname = "guard_T" + std::to_string(thread) + "_L" +
                                     std::to_string(label) + "_N" +
                                     std::to_string(num);
              const symbol_exprt gsym{gname, bool_typet{}};
              if(hoisted_guards.insert(gname).second)
              {
                equation.constraint(
                  equal_exprt{gsym, g}, "guard definition",
                  equation.SSA_steps.begin()->source);
              }
              g = gsym;
            }
            expr_5 = and_exprt{enabled, g};
          }
          else {
            expr_5 = enabled;
          }
          symbol_exprt exec = create_exec_symbol(label, num, thread, round);
          equal_exprt constraint{exec, expr_5};
          simplify(constraint, ns);
          equation.constraint(constraint, "cs constraint", equation.SSA_steps.begin()->source);
        }

        // Tightening dei confini di contesto (paper, sec:uniqueCS): un contesto
        // non vuoto non puo' iniziare con un blocco le cui guard sono tutte
        // false, perche' quel prefisso si sposterebbe nel contesto precedente
        // senza cambiare la sequenza di accessi eseguiti. Esente la prima
        // traversata dopo la creazione del thread, come la clausola di
        // creazione della canonicalita': senza activity a r-1 lo spostamento
        // e' impossibile e il vincolo taglierebbe schedule legittimi.
        //
        // Was `cs^{r-1} == label`; Enabled already conjoins
        // !GE(t,r-1,label+1), so only the remaining direction,
        // GE(t,r-1,label) (i.e. cs^{r-1} >= label), needs to be added
        // here -- together they pin cs^{r-1} == label exactly as before.
        // An optional strengthening, not part of the definition of the
        // schedule: gated so its ~10% of the encoding can be priced.
        static const bool no_tighten =
          getenv("LAZYPO_NO_CS_TIGHTEN") != nullptr;
        if(label != 0 && round > 1 && !no_tighten)
        {
          exprt witness = false_exprt{};
          for(unsigned num = 0; num < nmax; ++num)
            witness = or_exprt{
              witness, create_exec_symbol(label, num, thread, round)};

          implies_exprt tightening{
            and_exprt{
              enabled,
              create_ge_symbol(thread, round - 1, static_cast<unsigned>(label)),
              active_at_turn(thread, label, round - 1)},
            witness};
          simplify(tightening, ns);
          equation.constraint(
            tightening,
            "cs boundary tightening",
            equation.SSA_steps.begin()->source);
        }
      }

      // At-most-one-round-enabled no longer needs an explicit hint
      // constraint (previously a pairwise-O(rounds^2), then a
      // ladder-O(rounds), auxiliary encoding): under the order encoding,
      // (C1)-(C3) plus the Enabled definition above already give unit
      // propagation the same power in both directions --
      // Enabled(l,t,r) forces GE(t,r,l+1) and !GE(t,r-1,l+1), which (C2)
      // propagates to !GE(t,r'<r,l+1) and (C1)+(C2) to GE(t,r'>r,l+1),
      // immediately falsifying every other round's Enabled(l,t,r') via
      // its own definition -- with zero extra variables or clauses.
    }
  }
}

void lazy_pot::handling_atomic_sections(
  symex_target_equationt &equation)
{
  for(auto atomic_section : atomic_sections)
  {
    exprt constraint;

    if (atomic_section.second.first != atomic_section.second.second)
    {
      for(std::size_t round = 1; round <= rounds; round++)
      {
        // Was `cs <= lo OR cs > hi`; order encoding: cs <= lo is
        // !GE(round,lo+1), cs > hi is GE(round,hi+1).
        constraint = or_exprt{
          not_exprt{create_ge_symbol(
            atomic_section.first, round, atomic_section.second.first + 1)},
          create_ge_symbol(
            atomic_section.first, round, atomic_section.second.second + 1)};

        equation.constraint(
          constraint, "atomic constraint", equation.SSA_steps.begin()->source);
      }
    }
  }
}

void lazy_pot::handling_guards(
  symex_target_equationt &equation)
{
  // temp_equation only needs equation's non-SSA_steps state (message
  // handler, oc_edges/oc_guard_map, use_cat/use_deagle_* flags, ...), which
  // is exactly what survives equation.clear() anyway; copy-constructing from
  // equation with SSA_steps still fully populated copied the whole
  // (potentially hundreds-of-thousands-of-elements) list just to immediately
  // discard it. Swap SSA_steps out for the duration of the copy instead, so
  // the copy is O(1) rather than O(|SSA_steps|).
  symex_target_equationt::SSA_stepst original_steps;
  std::swap(original_steps, equation.SSA_steps);
  symex_target_equationt temp_equation{equation};
  std::swap(original_steps, equation.SSA_steps);

  // Consumo in ordine con un cursore: l'erase(begin()) precedente ricopiava
  // tutta la coda a ogni assert/assume (O(n^2) sui programmi con molti
  // blocking statement). at() sostituisce anche il front() su vettore vuoto,
  // che era UB se gli eventi bloccanti non coprivano tutti gli assert/assume.
  //
  // Previously also copied equation.SSA_steps wholesale into a local
  // 'ssa_steps' just to have something stable to iterate while separately
  // draining equation.SSA_steps one pop_front() at a time (3-4 copies of
  // every SSA_stept: into ssa_steps, into the local 'step', and again into
  // temp_equation.SSA_steps). Splicing the node directly into
  // temp_equation.SSA_steps is O(1) and needs none of those copies; 'it'
  // stays a valid reference to the same node afterwards (splice guarantee),
  // so it can still be read/written in place.
  std::size_t blocking_cursor = 0;

  for(auto it = equation.SSA_steps.begin(); it != equation.SSA_steps.end();)
  {
    auto next = std::next(it);

    if(it->is_assert() || it->is_assume())
    {
      shared_event blocking_event = blocking_events.at(blocking_cursor++);
      // blocking_event.s_it aliases equation.SSA_steps.front(), which the
      // splice below moves out from under it; capture .source first,
      // otherwise both uses of blocking_event.s_it below are a
      // use-after-free (found via ASan: heap-use-after-free in
      // handling_guards).
      const auto blocking_source = blocking_event.s_it->source;

      temp_equation.SSA_steps.splice(
        temp_equation.SSA_steps.end(), equation.SSA_steps, it);

      // TEMP-tried-and-reverted: collapsing this to the already-cached
      // cs(thread,rounds) > label comparator shrank the master formula
      // (fewer vars/clauses) but made SMS solving dramatically slower
      // (1800s timeout vs 731s) -- likely friction at the master/slave
      // routing boundary from embedding a raw cs-comparator directly in
      // an assert/assume guard instead of a separately-tagged constraint.
      // Reverted; kept as a named, memoized symbol instead.
      symbol_exprt reach = create_reach_symbol(
        blocking_event.label, blocking_source.thread_nr);

      exprt constraint = false_exprt{};

      for(std::size_t round = 1; round <= rounds; round++)
      {
        symbol_exprt enabled = create_enabled_symbol(
          blocking_event.label, blocking_event.thread, round);

        constraint = or_exprt{constraint, enabled};
      }

      simplify(constraint, ns);

      equal_exprt final_constraint{reach, constraint};
      simplify(final_constraint, ns);
      temp_equation.constraint(
        final_constraint,
        "blocking statement constraint",
        blocking_source);

      // Paper (sec:blocking statement): "for every statement other than
      // assume/assert we keep CBMC's guard unchanged ... to each
      // assume/assert we CONJOIN the reachability predicate of its program
      // point" -- the original path guard (the intra-thread branch
      // condition CBMC already built) must still hold; reach only adds the
      // round-robin-schedule-reached condition on top of it. This was
      // replacing it->guard outright, discarding the path guard entirely.
      // The is_true() short-circuit below skips a functionally-redundant
      // and_exprt{true, reach} Tseitin gadget when the guard happens to
      // already be trivial -- NOT always the case in general (assume/join
      // guards in concurrent programs routinely fold real path
      // conditions in via symex_assume_l2), just a cheap, always-correct
      // fast path when it applies.
      if(it->guard.is_true())
        it->guard = reach;
      else
        it->guard = and_exprt{it->guard, reach};
      // it->cond_expr already has the form (original_guard => c) --
      // vcc()/symex_assume_l2 build assert/assume conditions that way
      // before this function ever sees them. implies_exprt{it->guard,
      // it->cond_expr} therefore built (original_guard AND reach) =>
      // (original_guard => c), which is logically just reach =>
      // (original_guard => c) (the original_guard on the left is
      // redundant once it also appears on the right of the nested
      // implication) but re-embeds the full original_guard expression a
      // second time, doubling its Tseitin/CNF-conversion cost for every
      // blocking statement with a non-trivial guard. Using 'reach'
      // (rather than it->guard) here is equivalent and drops the
      // duplicate.
      exprt new_expr = implies_exprt{reach, it->cond_expr};
      simplify(new_expr, ns);
      it->cond_expr = new_expr;
    }
    else
    {
      temp_equation.SSA_steps.splice(
        temp_equation.SSA_steps.end(), equation.SSA_steps, it);
    }
    it = next;
  }
  // Move only SSA_steps back, not the whole struct: equation's other
  // fields (message handler, oc_edges/oc_guard_map, use_cat/use_deagle_*
  // flags, ...) were never touched by this function and are already
  // correct on equation itself; a full struct copy-assignment here would
  // reallocate every SSA_stept node (std::list has no move-assignment on
  // this class -- the user-declared destructor suppresses it, so even
  // std::move(temp_equation) would still copy), silently invalidating
  // every iterator collect_reads_and_writes stored earlier (in
  // blocking_events/reads/writes/...) for handling_datarace to use right
  // after this call returns. Moving just the list preserves every node's
  // identity (found via a segfault when handling_guards started running
  // before handling_datarace instead of only one of the two ever running).
  equation.SSA_steps = std::move(temp_equation.SSA_steps);
}

void lazy_pot::handling_active_threads(
  symex_target_equationt &equation)
{
  // See handling_guards for why this swap-around-the-copy avoids copying
  // the (potentially huge) SSA_steps list just to immediately discard it.
  symex_target_equationt::SSA_stepst original_steps;
  std::swap(original_steps, equation.SSA_steps);
  symex_target_equationt temp_equation{equation};
  std::swap(original_steps, equation.SSA_steps);

  auto ssa_steps = equation.SSA_steps;

  unsigned thread_current = 0;

  for(symex_target_equationt::SSA_stepst::const_iterator s_it =
        ssa_steps.begin();
      s_it != ssa_steps.end();
      s_it++)
  {
    exprt guard = s_it->guard;

    if(s_it->source.thread_nr > thread_current)
      thread_current = s_it->source.thread_nr;
  }
  std::unordered_map<unsigned, bool> thread_ends;


  exprt guard = true_exprt{};

  for(unsigned thread = 0; thread <= thread_current; thread++)
  {
    thread_ends[thread] = false;
    exprt symbol = create_active_thread_symbol(thread);
    if(thread == 0)
      create_active_thread_statements(
        ssa_steps.begin()->source,
        guard,
        ssa_steps.begin()->atomic_section_id,
        thread,
        temp_equation,
        true_exprt{});
    else
      create_active_thread_statements(
        ssa_steps.begin()->source,
        guard,
        ssa_steps.begin()->atomic_section_id,
        thread,
        temp_equation,
        false_exprt{});
  }

  unsigned thread_created = 1;
  thread_current = 0;

  // Was: a thread was deemed to have ended as soon as a step with a larger
  // source.thread_nr appeared, and __CPROVER_active_thread_T<t> was set to
  // false at that point. That assumes symex emits each thread's steps in one
  // contiguous, monotonically increasing block. It does not. When a spawned
  // function is passed the address of a local of the spawning function,
  //
  //   unsigned loc = 7; __CPROVER_ASYNC_0: f(&loc);
  //
  // symex emits the copy of that local into the *new* thread's frame -- a
  // step whose source.thread_nr is the new thread's -- while the spawning
  // thread still has steps to come. The old test fired on that copy and
  // marked the spawning thread inactive at its own spawn statement, so that
  // thread was never scheduled again: every later statement of it, including
  // any further spawns and the final assertion, became unreachable, and the
  // run reported VERIFICATION SUCCESSFUL vacuously. That is what made the
  // whole verify-treercu benchmark vacuous under --rounds -- main never got
  // past its first __CPROVER_ASYNC spawn, so the second thread was never
  // created and __CPROVER_assume(__unbuffered_cnt == NUM_THREADS) was
  // unsatisfiable, "proving" the safe case and all seven injected bugs alike.
  //
  // A thread ends at the *last* step that belongs to it, which is what is
  // computed here. On a trace whose steps really are contiguous that is
  // exactly the step the old test fired on, and the thread owning the very
  // last step of the trace is still left to the thread_ends sweep below, so
  // the equation this emits is unchanged for such traces.
  std::unordered_map<unsigned, const SSA_stept *> last_step_of_thread;
  for(const auto &trace_step : ssa_steps)
    last_step_of_thread[trace_step.source.thread_nr] = &trace_step;

  const symex_target_equationt::SSA_stepst::const_iterator trace_last =
    ssa_steps.empty() ? ssa_steps.end() : std::prev(ssa_steps.end());

  symex_target_equationt::SSA_stepst::const_iterator prev = ssa_steps.begin();

  for(symex_target_equationt::SSA_stepst::const_iterator s_it =
        ssa_steps.begin();
      s_it != ssa_steps.end();
      s_it++)
  {
    guard = s_it->guard;

    if(s_it->source.thread_nr > thread_current)
      thread_current = s_it->source.thread_nr;

    // Was: detected thread creation by pattern-matching the source
    // function name "pthread_create" plus a shared write to
    // __CPROVER_next_thread_id. That heuristic never fires for threads
    // spawned via CBMC's native __CPROVER_ASYNC_n: form (no
    // pthread_create call at all), so such threads' active-thread flag
    // was never set to true anywhere, making every one of their writes
    // invisible -- a silent false negative (confirmed: 5 of this repo's
    // own regression tests using __CPROVER_ASYNC report VERIFICATION
    // SUCCESSFUL under --rounds where plain CBMC correctly reports
    // FAILED). CBMC already emits a dedicated SPAWN step for both spawn
    // forms (is_spawn()), which is exactly what CBMC's own memory models
    // use for the same purpose -- use that instead of the source-level
    // pattern match. thread_created increments in spawn order, which is
    // CBMC's own thread numbering order, so no heuristic is needed for
    // the target thread index either. Using the spawn step's own
    // atomic_section_id (rather than a hard-coded 1, which was tuned
    // specifically for pthread_create's library wrapper) is correct for
    // both forms: a pthread_create SPAWN sits inside that library's
    // atomic section, an __CPROVER_ASYNC one does not.
    if(s_it->is_spawn())
    {
      create_active_thread_statements(
        s_it->source,
        guard,
        s_it->atomic_section_id,
        thread_created,
        temp_equation,
        true_exprt{});

      thread_created++;
    }

    SSA_stept step{equation.SSA_steps.front()};
    step.type = equation.SSA_steps.front().type;

    equation.SSA_steps.pop_front();
    temp_equation.SSA_steps.emplace_back(step);

    prev = s_it;

    // A thread ends at its own last step (see above). The thread that owns
    // the very last step of the whole trace is deliberately left to the
    // thread_ends sweep below, which marks it with an unconditional guard --
    // that is what the previous code did for it, and leaving it there is what
    // keeps this change a no-op on contiguous traces.
    const unsigned step_thread = s_it->source.thread_nr;
    if(s_it != trace_last && last_step_of_thread[step_thread] == &*s_it)
    {
      thread_ends[step_thread] = true;

      exprt end_guard = s_it->guard;
      unsigned int atomic_section_id = s_it->atomic_section_id;

      if(s_it->is_atomic_begin())
        atomic_section_id = 1;

      unsigned ending_thread = step_thread;
      create_active_thread_statements(
        s_it->source,
        end_guard,
        atomic_section_id,
        ending_thread,
        temp_equation,
        false_exprt{});
    }
  }
  for (auto thread_end : thread_ends)
  {
    if (thread_end.second == false)
    {
      thread_ends[thread_current] = true;
      exprt prev_guard = true_exprt{};
      unsigned thread = thread_end.first;

      unsigned int atomic_section_id = prev->atomic_section_id;

      if(prev->is_atomic_begin())
        atomic_section_id = 1;

      create_active_thread_statements(
        prev->source,
        prev_guard,
        atomic_section_id,
        thread,
        temp_equation,
        false_exprt{});
    }
  }
  equation = temp_equation;
}

void lazy_pot::create_active_thread_statements(
  const symex_targett::sourcet &source,
  exprt &guard,
  unsigned int atomic_section_id,
  unsigned &thread,
  symex_target_equationt &equation,
  const exprt &value)
{
  // thread_created (the caller's index into this map) comes from a
  // heuristic pthread_create-call-site match, independent of
  // thread_current (the real max thread_nr in the trace, which is what
  // populates this map up front in handling_active_threads). If that
  // heuristic ever over-counts, active_threads_vector.at(thread) below
  // throws an uncaught std::out_of_range and the whole run aborts with no
  // diagnostic. Register defensively instead: emplace() is a no-op when
  // thread is already present, so this only changes behaviour on the
  // mismatch case, and only by warning + continuing instead of crashing.
  // 'log' (a messaget local to operator()) isn't reachable from this
  // member function, so this can only register silently rather than warn;
  // still strictly better than the uncaught std::out_of_range this
  // replaces.
  if(active_threads_vector.count(thread) == 0)
    create_active_thread_symbol(thread);

  SSA_stept event_step{source, goto_trace_stept::typet::SHARED_WRITE};
  event_step.guard = guard;
  ssa_exprt event_expr{active_threads_vector.at(thread).symbol};
  event_expr.set_level_2(active_threads_vector.at(thread).l2);
  event_step.ssa_lhs = event_expr;
  event_step.atomic_section_id = atomic_section_id;
  equation.SSA_steps.emplace_back(event_step);

  SSA_stept active_step{source, goto_trace_stept::typet::ASSIGNMENT};
  active_step.guard = guard;
  ssa_exprt active_expr{active_threads_vector.at(thread).symbol};
  active_expr.set_level_2(active_threads_vector.at(thread).l2);
  active_threads_vector.at(thread).l2++;
  active_step.ssa_lhs = active_expr;
  active_step.ssa_rhs = value;
  active_step.cond_expr = equal_exprt{active_step.ssa_lhs, active_step.ssa_rhs};
  active_step.assignment_type =
    symex_targett::assignment_typet::HIDDEN;
  active_step.hidden = true;
  active_step.atomic_section_id = atomic_section_id;
  equation.SSA_steps.emplace_back(active_step);
}

symbol_exprt lazy_pot::phase_1(symex_target_equationt &equation, irep_idt v) {

  irep_idt phase_1_name =  as_string(v) + "_phase_1";
  symbol_exprt phase_1_symbl{phase_1_name, bool_typet{}};

  exprt phase_1_exp = false_exprt{};

  for (std::size_t thread = 0; thread <= threads; thread++) {
    irep_idt phase_1_t_name =  as_string(v) + "_phase_1_T" + std::to_string(thread);
    symbol_exprt phase_1_t_symbl{phase_1_t_name, bool_typet{}};

    phase_1_exp = or_exprt{phase_1_exp, phase_1_t_symbl};

    exprt phase_1_t_exp = false_exprt{};

    if(this->writes.count(v) != 0) {
      for (auto write : writes.at(v)) {
        std::string func = id2string(write.s_it->source.pc->source_location().get_function());
        // pthread_create's own write to its thread-ID output parameter is
        // user-visible data (the caller supplied that pointer), not library
        // bookkeeping -- unlike pthread_mutex_lock/_unlock/_init, pthread_join,
        // pthread_cond_wait and friends, which only ever touch their own
        // internal state objects here. Excluding it hid a genuine race: see
        // ~/tid_write_race.c, a 9-line reproducer where one thread's
        // pthread_create races an unsynchronised read of the thread-ID global
        // in another thread, reported SUCCESSFUL with the blanket exclusion.
        bool is_pthread = (func.rfind("pthread", 0) == 0) && func != "pthread_create";
        if (write.thread != thread || is_pthread || write.race_exempt)
          continue;
        irep_idt phase_1_t_v_name =  as_string(v) + "_phase_1_T" + std::to_string(thread) + "_L" + std::to_string(write.label) + "_N" + std::to_string(write.num);
        symbol_exprt phase_1_t_v_symbl{phase_1_t_v_name, bool_typet{}};

        phase_1_t_exp = or_exprt{phase_1_t_exp, phase_1_t_v_symbl};

        int atom = write.s_it->atomic_section_id != 0;
        exprt phase_1_t_v_exp =
          and_exprt{
            equal_exprt{create_dr_thread_symbol(1), from_integer({thread}, unsignedbv_typet{threads_bits})},
            and_exprt{
              create_exec_tot_symbol(/*log,*/ equation, write.label, write.num, thread),
              and_exprt{
                equal_exprt{create_dr_atom_symbol(1), from_integer({atom}, bool_typet{})},
                equal_exprt{create_dr_loc_symbol(1), typecast_exprt(write.where, size_type())}
                }
              }
          };

        exprt exp2 = true_exprt{};
        for (std::size_t round = 1; round <= rounds; round++) {
          exprt enabled_exp = true_exprt{};
          if (write.label < labels[write.thread]) {
            enabled_exp = not_exprt{create_enabled_symbol(write.label+1,thread,round)};
          }
          exprt exp = implies_exprt{
            create_exec_symbol(write.label,write.num,thread,round),
            and_exprt{
              equal_exprt{create_dr_round_symbol(1),from_integer({round}, unsignedbv_typet{rounds_bits})},
              enabled_exp
            }};
          exp2 = and_exprt{exp2, exp};
        }
        phase_1_t_v_exp = equal_exprt{
          phase_1_t_v_symbl,
          and_exprt{phase_1_t_v_exp, exp2}};

        simplify(phase_1_t_v_exp, ns);
        equation.constraint(
          phase_1_t_v_exp, "datarace constraint", equation.SSA_steps.begin()->source);
      }
    }
    phase_1_t_exp = equal_exprt {phase_1_t_symbl, phase_1_t_exp};
    simplify(phase_1_t_exp, ns);
    equation.constraint(
      phase_1_t_exp, "datarace constraint", equation.SSA_steps.begin()->source);
  }

  phase_1_exp = equal_exprt {phase_1_symbl, phase_1_exp};
  simplify(phase_1_exp, ns);
  equation.constraint(
    phase_1_exp, "datarace constraint", equation.SSA_steps.begin()->source);

  return phase_1_symbl;
}

symbol_exprt lazy_pot::phase_2(symex_target_equationt &equation, irep_idt v) {
  irep_idt phase_2_name = as_string(v) + "_phase_2";
  symbol_exprt phase_2_symbl{phase_2_name, bool_typet{}};

  exprt phase_2_exp = false_exprt{};

  for (std::size_t thread = 0; thread <= threads; thread++) {
    irep_idt phase_2_t_name = as_string(v) + "_phase_2_T" + std::to_string(thread);
    symbol_exprt phase_2_t_symbl{phase_2_t_name, bool_typet{}};

    phase_2_exp = or_exprt{phase_2_exp, phase_2_t_symbl};

    exprt phase_2_t_exp = false_exprt{};

    if(this->writes.count(v) != 0) {
      for (auto write : writes.at(v)) {
        std::string func = id2string(write.s_it->source.pc->source_location().get_function());
        // pthread_create is exempted above handling_datarace's first check of
        // this shape -- see the comment there.
        bool is_pthread = (func.rfind("pthread", 0) == 0) && func != "pthread_create";
        if (write.thread != thread || is_pthread || write.race_exempt)
          continue;
        irep_idt phase_2_t_v_name = as_string(v) + "_phase_2_w_T" + std::to_string(thread) + "_L" + std::to_string(write.label) + "_N" + std::to_string(write.num);
        symbol_exprt phase_2_t_v_symbl{phase_2_t_v_name, bool_typet{}};

        phase_2_t_exp = or_exprt{phase_2_t_exp, phase_2_t_v_symbl};

        int atom = write.s_it->atomic_section_id != 0;
        exprt phase_2_t_v_exp =
          and_exprt{
            equal_exprt{create_dr_thread_symbol(2), from_integer({thread}, unsignedbv_typet{threads_bits})},
            and_exprt{
              create_exec_tot_symbol(/*log,*/ equation, write.label, write.num, thread),
              and_exprt{
                equal_exprt{create_dr_atom_symbol(2), from_integer({atom}, bool_typet{})},
                equal_exprt{create_dr_loc_symbol(2), typecast_exprt(write.where, size_type())}
              }
            }
          };

        exprt exp2 = true_exprt{};
        for (std::size_t round = 1; round <= rounds; round++) {
          exprt enabled_exp = true_exprt{};
          if (write.label > 1) {
            enabled_exp = not_exprt{create_enabled_symbol(write.label-1,thread,round)};
          }
          exprt exp = implies_exprt{
            create_exec_symbol(write.label,write.num,thread,round),
            and_exprt{
              equal_exprt{create_dr_round_symbol(2),from_integer({round}, unsignedbv_typet{rounds_bits})},
              enabled_exp
            }};
          exp2 = and_exprt{exp2, exp};
        }
        phase_2_t_v_exp = equal_exprt{
          phase_2_t_v_symbl,
          and_exprt{phase_2_t_v_exp, exp2}};

        simplify(phase_2_t_v_exp, ns);
        equation.constraint(
          phase_2_t_v_exp, "datarace constraint", equation.SSA_steps.begin()->source);
      }
    }
    if(this->reads.count(v) != 0) {
      for (auto read : reads.at(v)) {
        std::string func = id2string(read.s_it->source.pc->source_location().get_function());
        // pthread_create is exempted above handling_datarace's first check of
        // this shape -- see the comment there.
        bool is_pthread = (func.rfind("pthread", 0) == 0) && func != "pthread_create";
        if (read.thread != thread || is_pthread || read.race_exempt)
          continue;
        irep_idt phase_2_t_v_name =  as_string(v) + "_phase_2_r_T" + std::to_string(thread) + "_L" + std::to_string(read.label) + "_N" + std::to_string(read.num);
        symbol_exprt phase_2_t_v_symbl{phase_2_t_v_name, bool_typet{}};

        phase_2_t_exp = or_exprt{phase_2_t_exp, phase_2_t_v_symbl};

        int atom = read.s_it->atomic_section_id != 0;
        exprt phase_2_t_v_exp =
          and_exprt{
            equal_exprt{create_dr_thread_symbol(2), from_integer({thread}, unsignedbv_typet{threads_bits})},
            and_exprt{
              create_exec_tot_symbol(/*log,*/ equation, read.label, read.num, thread),
              and_exprt{
                equal_exprt{create_dr_atom_symbol(2), from_integer({atom}, bool_typet{})},
                equal_exprt{create_dr_loc_symbol(2), typecast_exprt(read.where, size_type())}
              }
            }
          };

        exprt exp2 = true_exprt{};
        for (std::size_t round = 1; round <= rounds; round++) {
          exprt enabled_exp = true_exprt{};
          if (read.label > 1) {
            enabled_exp = not_exprt{create_enabled_symbol(read.label-1,thread,round)};
          }
          exprt exp = implies_exprt{
            create_exec_symbol(read.label,read.num,thread,round),
            and_exprt{
              equal_exprt{create_dr_round_symbol(2),from_integer({round}, unsignedbv_typet{rounds_bits})},
              enabled_exp
            }};
          exp2 = and_exprt{exp2, exp};
        }
        phase_2_t_v_exp = equal_exprt{
          phase_2_t_v_symbl,
          and_exprt{phase_2_t_v_exp, exp2}};

        simplify(phase_2_t_v_exp, ns);
        equation.constraint(
          phase_2_t_v_exp, "datarace constraint", equation.SSA_steps.begin()->source);
      }
    }
    phase_2_t_exp = equal_exprt {phase_2_t_symbl, phase_2_t_exp};
    simplify(phase_2_t_exp, ns);
    equation.constraint(
      phase_2_t_exp, "datarace constraint", equation.SSA_steps.begin()->source);
  }

  phase_2_exp = equal_exprt {phase_2_symbl, phase_2_exp};
  simplify(phase_2_exp, ns);
  equation.constraint(
    phase_2_exp, "datarace constraint", equation.SSA_steps.begin()->source);

  return phase_2_symbl;
}

symbol_exprt lazy_pot::same_round(symex_target_equationt &equation) {
  irep_idt same_round_name = "same_round";
  symbol_exprt same_round_symbl{same_round_name, bool_typet{}};


  exprt same_round_exp = and_exprt{
    notequal_exprt{
      create_dr_thread_symbol(1),
      create_dr_thread_symbol(2)
    },
    and_exprt{
      implies_exprt{
        less_than_exprt{create_dr_thread_symbol(1),
      create_dr_thread_symbol(2)},
        equal_exprt{create_dr_round_symbol(1),
      create_dr_round_symbol(2)}
      },
      and_exprt{
        implies_exprt{
          less_than_exprt{create_dr_thread_symbol(2),
          create_dr_thread_symbol(1)},
            equal_exprt{create_dr_round_symbol(2),
          plus_exprt{create_dr_round_symbol(1), from_integer({1}, unsignedbv_typet{rounds_bits})}}},
        and_exprt{
          or_exprt{not_exprt{create_dr_atom_symbol(1)}, not_exprt{create_dr_atom_symbol(2)}},
          equal_exprt{create_dr_loc_symbol(1),create_dr_loc_symbol(2)}
          }
        }
    }
  };

  same_round_exp = equal_exprt{same_round_symbl, same_round_exp};
  simplify(same_round_exp, ns);
  equation.constraint(
    same_round_exp, "datarace constraint", equation.SSA_steps.begin()->source);

  return same_round_symbl;
}

symbol_exprt lazy_pot::no_interf(symex_target_equationt &equation) {
  irep_idt no_interf_name = "no_interf";
  symbol_exprt no_interf_symbl{no_interf_name, bool_typet{}};

  exprt no_interf_exp = true_exprt{};


  for (std::size_t thread = 0; thread <= threads; thread++) {
    irep_idt no_interf_t_name = "no_interf_T" + std::to_string(thread);
    symbol_exprt no_interf_t_symbl{no_interf_t_name, bool_typet{}};

    exprt exp1 = true_exprt{};
    exprt exp2 = true_exprt{};
    for (std::size_t round = 1; round <= rounds; round++) {
      exprt exp1r = true_exprt{};
      exprt exp2r = true_exprt{};
        // cs(t,round) == cs(t,round-1): (C2) already gives
        // GE(round-1,i) => GE(round,i) for every i, so only the converse
        // direction needs asserting here for full equality.
        exprt cs_eq_1 = true_exprt{};
        for(unsigned i = 1; i <= labels[thread] + 1; ++i)
          cs_eq_1 = and_exprt{
            cs_eq_1,
            implies_exprt{
              create_ge_symbol(thread, round, i),
              create_ge_symbol(thread, round - 1, i)}};
        exp1r = implies_exprt{
          equal_exprt{create_dr_round_symbol(1), from_integer({round}, unsignedbv_typet{rounds_bits})},
          cs_eq_1
        };
      if (round > 1) {
        exprt cs_eq_2 = true_exprt{};
        for(unsigned i = 1; i <= labels[thread] + 1; ++i)
          cs_eq_2 = and_exprt{
            cs_eq_2,
            implies_exprt{
              create_ge_symbol(thread, round, i),
              create_ge_symbol(thread, round - 1, i)}};
        exp2r = implies_exprt{
          equal_exprt{create_dr_round_symbol(2), from_integer({round}, unsignedbv_typet{rounds_bits})},
          cs_eq_2
        };
      }
      exp1 = and_exprt{exp1, exp1r};
      exp2 = and_exprt{exp2, exp2r};
    }

    exprt no_interf_t_exp = and_exprt{
      and_exprt{
        implies_exprt{
          or_exprt{
            and_exprt{
              less_than_exprt{create_dr_thread_symbol(1), from_integer({thread}, unsignedbv_typet{threads_bits})},
              less_than_exprt{from_integer({thread}, unsignedbv_typet{threads_bits}), create_dr_thread_symbol(2)}},
            and_exprt{
              less_than_exprt{create_dr_thread_symbol(2),create_dr_thread_symbol(1)},
              less_than_exprt{create_dr_thread_symbol(1), from_integer({thread}, unsignedbv_typet{threads_bits})}}
          },
          exp1
        },
        implies_exprt{
          and_exprt{
          less_than_exprt{from_integer({thread}, unsignedbv_typet{threads_bits}), create_dr_thread_symbol(2)},
            less_than_exprt{create_dr_thread_symbol(2), create_dr_thread_symbol(1)}},
          exp2}
      }
    };

    no_interf_t_exp = equal_exprt{no_interf_t_symbl, no_interf_t_exp};
    simplify(no_interf_t_exp, ns);
    equation.constraint(
      no_interf_t_exp, "datarace constraint", equation.SSA_steps.begin()->source);

    no_interf_exp = and_exprt{no_interf_exp, no_interf_t_symbl};
  }
  no_interf_exp = equal_exprt{no_interf_symbl, no_interf_exp};
  simplify(no_interf_exp, ns);
  equation.constraint(
    no_interf_exp, "datarace constraint", equation.SSA_steps.begin()->source);

  return no_interf_symbl;
}

// __SZH_DR_ADD_BEGIN__
// Mirror of phase_1, but iterating reads instead of writes, using roles
// 3/4 (create_dr_thread_symbol(3) etc.) instead of 1/2. phase_1/phase_2
// (roles 1/2) can only witness a race where the mandatory-write access
// (role 1) executes in the same round as, or one round before, the
// second access (role 2) -- same_round's round relationship (tied to
// which of dr_thread(1)/dr_thread(2) is numerically smaller, encoding
// the fixed round-robin sweep order within a round) never allows
// dr_round(2) < dr_round(1). That misses a real race where the
// chronologically-first access is a READ and a conflicting WRITE happens
// later: no witness pairing exists in the original encoding for it,
// regardless of --unwind/--rounds (confirmed by exhaustive offline
// search: 110+99 unwind/rounds combinations up to unwind=44/rounds=20,
// none resolved several real SV-COMP benchmarks hitting exactly this
// pattern). phase_1_swap/phase_2_swap/same_round_swap/no_interf_swap
// mirror the exact same machinery with the roles reversed (role 3 =
// read, role 4 = write) and role 3/4's own independent dr_thread/
// dr_round/dr_atom/dr_loc symbols (create_dr_*_symbol is a generic,
// num-indexed symbol cache -- roles 3/4 are entirely fresh SAT variables,
// unrelated to roles 1/2). The final detection ORs both pairings
// together in handling_datarace, so this is purely additive: it can only
// add coverage, never remove or alter what roles 1/2 already detect.
symbol_exprt lazy_pot::phase_1_swap(symex_target_equationt &equation, irep_idt v) {

  irep_idt phase_1_name =  as_string(v) + "_phase_1_swap";
  symbol_exprt phase_1_symbl{phase_1_name, bool_typet{}};

  exprt phase_1_exp = false_exprt{};

  for (std::size_t thread = 0; thread <= threads; thread++) {
    irep_idt phase_1_t_name =  as_string(v) + "_phase_1_swap_T" + std::to_string(thread);
    symbol_exprt phase_1_t_symbl{phase_1_t_name, bool_typet{}};

    phase_1_exp = or_exprt{phase_1_exp, phase_1_t_symbl};

    exprt phase_1_t_exp = false_exprt{};

    if(this->reads.count(v) != 0) {
      for (auto read : reads.at(v)) {
        std::string func = id2string(read.s_it->source.pc->source_location().get_function());
        // pthread_create is exempted above handling_datarace's first check of
        // this shape -- see the comment there.
        bool is_pthread = (func.rfind("pthread", 0) == 0) && func != "pthread_create";
        if (read.thread != thread || is_pthread || read.race_exempt)
          continue;
        irep_idt phase_1_t_v_name =  as_string(v) + "_phase_1_swap_T" + std::to_string(thread) + "_L" + std::to_string(read.label) + "_N" + std::to_string(read.num);
        symbol_exprt phase_1_t_v_symbl{phase_1_t_v_name, bool_typet{}};

        phase_1_t_exp = or_exprt{phase_1_t_exp, phase_1_t_v_symbl};

        int atom = read.s_it->atomic_section_id != 0;
        exprt phase_1_t_v_exp =
          and_exprt{
            equal_exprt{create_dr_thread_symbol(3), from_integer({thread}, unsignedbv_typet{threads_bits})},
            and_exprt{
              create_exec_tot_symbol(/*log,*/ equation, read.label, read.num, thread),
              and_exprt{
                equal_exprt{create_dr_atom_symbol(3), from_integer({atom}, bool_typet{})},
                equal_exprt{create_dr_loc_symbol(3), typecast_exprt(read.where, size_type())}
                }
              }
          };

        exprt exp2 = true_exprt{};
        for (std::size_t round = 1; round <= rounds; round++) {
          exprt enabled_exp = true_exprt{};
          if (read.label < labels[read.thread]) {
            enabled_exp = not_exprt{create_enabled_symbol(read.label+1,thread,round)};
          }
          exprt exp = implies_exprt{
            create_exec_symbol(read.label,read.num,thread,round),
            and_exprt{
              equal_exprt{create_dr_round_symbol(3),from_integer({round}, unsignedbv_typet{rounds_bits})},
              enabled_exp
            }};
          exp2 = and_exprt{exp2, exp};
        }
        phase_1_t_v_exp = equal_exprt{
          phase_1_t_v_symbl,
          and_exprt{phase_1_t_v_exp, exp2}};

        simplify(phase_1_t_v_exp, ns);
        equation.constraint(
          phase_1_t_v_exp, "datarace constraint", equation.SSA_steps.begin()->source);
      }
    }
    phase_1_t_exp = equal_exprt {phase_1_t_symbl, phase_1_t_exp};
    simplify(phase_1_t_exp, ns);
    equation.constraint(
      phase_1_t_exp, "datarace constraint", equation.SSA_steps.begin()->source);
  }

  phase_1_exp = equal_exprt {phase_1_symbl, phase_1_exp};
  simplify(phase_1_exp, ns);
  equation.constraint(
    phase_1_exp, "datarace constraint", equation.SSA_steps.begin()->source);

  return phase_1_symbl;
}

// Mirror of phase_2, but writes-only (the read-iterating half is
// dropped, since role 3 already covers the read side for this pairing;
// a race needs at least one write, and role 3 = read here), using role 4.
symbol_exprt lazy_pot::phase_2_swap(symex_target_equationt &equation, irep_idt v) {
  irep_idt phase_2_name = as_string(v) + "_phase_2_swap";
  symbol_exprt phase_2_symbl{phase_2_name, bool_typet{}};

  exprt phase_2_exp = false_exprt{};

  for (std::size_t thread = 0; thread <= threads; thread++) {
    irep_idt phase_2_t_name = as_string(v) + "_phase_2_swap_T" + std::to_string(thread);
    symbol_exprt phase_2_t_symbl{phase_2_t_name, bool_typet{}};

    phase_2_exp = or_exprt{phase_2_exp, phase_2_t_symbl};

    exprt phase_2_t_exp = false_exprt{};

    if(this->writes.count(v) != 0) {
      for (auto write : writes.at(v)) {
        std::string func = id2string(write.s_it->source.pc->source_location().get_function());
        // pthread_create is exempted above handling_datarace's first check of
        // this shape -- see the comment there.
        bool is_pthread = (func.rfind("pthread", 0) == 0) && func != "pthread_create";
        if (write.thread != thread || is_pthread || write.race_exempt)
          continue;
        irep_idt phase_2_t_v_name = as_string(v) + "_phase_2_swap_w_T" + std::to_string(thread) + "_L" + std::to_string(write.label) + "_N" + std::to_string(write.num);
        symbol_exprt phase_2_t_v_symbl{phase_2_t_v_name, bool_typet{}};

        phase_2_t_exp = or_exprt{phase_2_t_exp, phase_2_t_v_symbl};

        int atom = write.s_it->atomic_section_id != 0;
        exprt phase_2_t_v_exp =
          and_exprt{
            equal_exprt{create_dr_thread_symbol(4), from_integer({thread}, unsignedbv_typet{threads_bits})},
            and_exprt{
              create_exec_tot_symbol(/*log,*/ equation, write.label, write.num, thread),
              and_exprt{
                equal_exprt{create_dr_atom_symbol(4), from_integer({atom}, bool_typet{})},
                equal_exprt{create_dr_loc_symbol(4), typecast_exprt(write.where, size_type())}
              }
            }
          };

        exprt exp2 = true_exprt{};
        for (std::size_t round = 1; round <= rounds; round++) {
          exprt enabled_exp = true_exprt{};
          if (write.label > 1) {
            enabled_exp = not_exprt{create_enabled_symbol(write.label-1,thread,round)};
          }
          exprt exp = implies_exprt{
            create_exec_symbol(write.label,write.num,thread,round),
            and_exprt{
              equal_exprt{create_dr_round_symbol(4),from_integer({round}, unsignedbv_typet{rounds_bits})},
              enabled_exp
            }};
          exp2 = and_exprt{exp2, exp};
        }
        phase_2_t_v_exp = equal_exprt{
          phase_2_t_v_symbl,
          and_exprt{phase_2_t_v_exp, exp2}};

        simplify(phase_2_t_v_exp, ns);
        equation.constraint(
          phase_2_t_v_exp, "datarace constraint", equation.SSA_steps.begin()->source);
      }
    }
    phase_2_t_exp = equal_exprt {phase_2_t_symbl, phase_2_t_exp};
    simplify(phase_2_t_exp, ns);
    equation.constraint(
      phase_2_t_exp, "datarace constraint", equation.SSA_steps.begin()->source);
  }

  phase_2_exp = equal_exprt {phase_2_symbl, phase_2_exp};
  simplify(phase_2_exp, ns);
  equation.constraint(
    phase_2_exp, "datarace constraint", equation.SSA_steps.begin()->source);

  return phase_2_symbl;
}

// Mirror of same_round for roles 3/4 -- identical relational structure
// (it encodes the fixed round-robin sweep order within a round, which
// doesn't depend on what kind of access each role represents), just
// parameterized on the independent role-3/4 symbols.
symbol_exprt lazy_pot::same_round_swap(symex_target_equationt &equation) {
  irep_idt same_round_name = "same_round_swap";
  symbol_exprt same_round_symbl{same_round_name, bool_typet{}};


  exprt same_round_exp = and_exprt{
    notequal_exprt{
      create_dr_thread_symbol(3),
      create_dr_thread_symbol(4)
    },
    and_exprt{
      implies_exprt{
        less_than_exprt{create_dr_thread_symbol(3),
      create_dr_thread_symbol(4)},
        equal_exprt{create_dr_round_symbol(3),
      create_dr_round_symbol(4)}
      },
      and_exprt{
        implies_exprt{
          less_than_exprt{create_dr_thread_symbol(4),
          create_dr_thread_symbol(3)},
            equal_exprt{create_dr_round_symbol(4),
          plus_exprt{create_dr_round_symbol(3), from_integer({1}, unsignedbv_typet{rounds_bits})}}},
        and_exprt{
          or_exprt{not_exprt{create_dr_atom_symbol(3)}, not_exprt{create_dr_atom_symbol(4)}},
          equal_exprt{create_dr_loc_symbol(3),create_dr_loc_symbol(4)}
          }
        }
    }
  };

  same_round_exp = equal_exprt{same_round_symbl, same_round_exp};
  simplify(same_round_exp, ns);
  equation.constraint(
    same_round_exp, "datarace constraint", equation.SSA_steps.begin()->source);

  return same_round_symbl;
}

// Mirror of no_interf for roles 3/4.
symbol_exprt lazy_pot::no_interf_swap(symex_target_equationt &equation) {
  irep_idt no_interf_name = "no_interf_swap";
  symbol_exprt no_interf_symbl{no_interf_name, bool_typet{}};

  exprt no_interf_exp = true_exprt{};


  for (std::size_t thread = 0; thread <= threads; thread++) {
    irep_idt no_interf_t_name = "no_interf_swap_T" + std::to_string(thread);
    symbol_exprt no_interf_t_symbl{no_interf_t_name, bool_typet{}};

    exprt exp1 = true_exprt{};
    exprt exp2 = true_exprt{};
    for (std::size_t round = 1; round <= rounds; round++) {
      exprt exp1r = true_exprt{};
      exprt exp2r = true_exprt{};
        exprt cs_eq_1 = true_exprt{};
        for(unsigned i = 1; i <= labels[thread] + 1; ++i)
          cs_eq_1 = and_exprt{
            cs_eq_1,
            implies_exprt{
              create_ge_symbol(thread, round, i),
              create_ge_symbol(thread, round - 1, i)}};
        exp1r = implies_exprt{
          equal_exprt{create_dr_round_symbol(3), from_integer({round}, unsignedbv_typet{rounds_bits})},
          cs_eq_1
        };
      if (round > 1) {
        exprt cs_eq_2 = true_exprt{};
        for(unsigned i = 1; i <= labels[thread] + 1; ++i)
          cs_eq_2 = and_exprt{
            cs_eq_2,
            implies_exprt{
              create_ge_symbol(thread, round, i),
              create_ge_symbol(thread, round - 1, i)}};
        exp2r = implies_exprt{
          equal_exprt{create_dr_round_symbol(4), from_integer({round}, unsignedbv_typet{rounds_bits})},
          cs_eq_2
        };
      }
      exp1 = and_exprt{exp1, exp1r};
      exp2 = and_exprt{exp2, exp2r};
    }

    exprt no_interf_t_exp = and_exprt{
      and_exprt{
        implies_exprt{
          or_exprt{
            and_exprt{
              less_than_exprt{create_dr_thread_symbol(3), from_integer({thread}, unsignedbv_typet{threads_bits})},
              less_than_exprt{from_integer({thread}, unsignedbv_typet{threads_bits}), create_dr_thread_symbol(4)}},
            and_exprt{
              less_than_exprt{create_dr_thread_symbol(4),create_dr_thread_symbol(3)},
              less_than_exprt{create_dr_thread_symbol(3), from_integer({thread}, unsignedbv_typet{threads_bits})}}
          },
          exp1
        },
        implies_exprt{
          and_exprt{
          less_than_exprt{from_integer({thread}, unsignedbv_typet{threads_bits}), create_dr_thread_symbol(4)},
            less_than_exprt{create_dr_thread_symbol(4), create_dr_thread_symbol(3)}},
          exp2}
      }
    };

    no_interf_t_exp = equal_exprt{no_interf_t_symbl, no_interf_t_exp};
    simplify(no_interf_t_exp, ns);
    equation.constraint(
      no_interf_t_exp, "datarace constraint", equation.SSA_steps.begin()->source);

    no_interf_exp = and_exprt{no_interf_exp, no_interf_t_symbl};
  }
  no_interf_exp = equal_exprt{no_interf_symbl, no_interf_exp};
  simplify(no_interf_exp, ns);
  equation.constraint(
    no_interf_exp, "datarace constraint", equation.SSA_steps.begin()->source);

  return no_interf_symbl;
}
// __SZH_DR_ADD_END__


// L'offset di un accesso puo' essere sepolto sotto un `if`.
//
// Un oggetto dinamico di dimensione *simbolica* non viene spezzato per
// elemento dalla field sensitivity (che richiede una size costante), quindi
// `datas[i] = v` arriva nella SSA come
//
//   obj#4 == (datas == &obj ? obj#3 WITH [0:=v] : obj#2)
//
// La destra non e' un `with`: e' un `if` che lo contiene, perche' il
// puntatore potrebbe puntare altrove. Il test sulla forma falliva, `where`
// restava al sentinella -1 per *ogni* accesso all'oggetto, e la condizione di
// corsa confronta `dr_loc(1) == dr_loc(2)` -- quindi due thread che scrivono
// elementi diversi finivano sulla stessa locazione e venivano dichiarati in
// corsa. E' la famiglia per-thread-array-index / per-thread-index-* / sssc12,
// e il riproduttore minimo e' ~/heapidx/c_constthreads.c (22 righe, con il
// controllo a indice uguale che deve restare FAILED).
//
// Conservativo per costruzione: se i rami portano indici diversi non c'e' un
// solo offset da attribuire all'accesso e si torna al sentinella, cioe' al
// comportamento di prima.
static bool with_index_under_if(const exprt &e, exprt &out, bool &found)
{
  if(e.id() == ID_with && e.operands().size() == 3)
  {
    const exprt &w = to_with_expr(e).where();
    if(found)
      return out == w;
    out = w;
    found = true;
    return true;
  }
  // A read through a symbolic-size malloc'd pointer goes through CBMC's own
  // pointer-identity resolution (the #305 fix's value-set dereference),
  // which wraps a plain indexed access -- not a with -- in the same
  // if-chain shape: `ptr == &obj1 ? obj1[k] : (ptr == &obj2 ? obj2[k] :
  // ...)`. Reading `arr[k]` as a function-call argument (e.g.
  // `pthread_join(tids[k], ...)`) takes exactly this path, even when `k`
  // is a compile-time constant -- it is the pointer, not the index, that
  // is symbolic here. Recognising only `with` left this case at the
  // sentinel, so a write (which does produce a `with`) and this kind of
  // read could never be seen as the same location: see
  // ~/tidrace_check/tid_symmalloc_only.c.
  if(e.id() == ID_index)
  {
    const index_exprt &idx = to_index_expr(e);
    if(found)
      return out == idx.index();
    out = idx.index();
    found = true;
    return true;
  }
  // `if`'s own condition is always its first operand, by construction --
  // skip it by position, not by type. The previous type-based skip
  // (`op.type().id() == ID_bool`) assumed the condition was the only
  // bool-typed operand, which holds when the if's VALUE type is the array
  // element type (the #305 pointer-identity chain this was written for).
  // It breaks when the if itself computes a boolean result, as happens one
  // level up from the `not`/`equal` case just below, inside a guard
  // update: then the true/false branches are bool-typed too, and the old
  // skip wrongly discarded them along with the condition.
  if(e.id() == ID_if)
  {
    const if_exprt &ife = to_if_expr(e);
    return with_index_under_if(ife.true_case(), out, found) &&
           with_index_under_if(ife.false_case(), out, found);
  }
  // Reading `arr[k]` inside an `if`-condition (`if (arr[k] != 0) ...`),
  // rather than materialising it into a plain temporary first, folds the
  // dereference straight into the boolean test: `!(arr[k] == 0)`. The
  // if-chain above is still there (that part was already handled), but
  // each branch is now `not(equal(index_or_with, constant))`, not a bare
  // `with`/`index` directly -- so the recursion stopped one layer too
  // early and the read landed on the sentinel. `not`/`equal`/`notequal`
  // carry the same offset as whichever operand resolves to one; the other
  // operand is typically a plain constant (e.g. the `0` being compared
  // against), which recurses here too but contributes nothing (falls to
  // the catch-all below without touching `found`/`out`). See
  // ~/tidrace_check/tid_ifcond_const.c.
  if(e.id() == ID_not || e.id() == ID_equal || e.id() == ID_notequal)
  {
    for(const auto &op : e.operands())
    {
      if(!with_index_under_if(op, out, found))
        return false;
    }
    return true;
  }
  // A _Bool element is one byte wide, so reading it as a value (rather than
  // assigning it to a plain temporary) goes through an explicit byte
  // extraction on top of everything above: `byte_extract(obj[k], 0,
  // c_bool[8]) != 0`, not a bare `obj[k]` under the comparison. Recurse into
  // the object being extracted from -- the offset we want is in there, not
  // in the byte/type-width arguments alongside it. See
  // ~/tidrace_check/flags_bool_ifcond.c.
  if(
    e.id() == ID_byte_extract_little_endian ||
    e.id() == ID_byte_extract_big_endian)
  {
    return with_index_under_if(to_byte_extract_expr(e).op(), out, found);
  }
  return true;
}

/// \return l'offset dell'accesso se sotto gli `if` ce n'e' esattamente uno,
///   altrimenti nil.
static exprt access_offset(const exprt &rhs)
{
  exprt out = nil_exprt{};
  bool found = false;
  if(!with_index_under_if(rhs, out, found) || !found)
    return nil_exprt{};
  return out;
}

void lazy_pot::handling_datarace(
  symex_target_equationt &equation) {


  irep_idt phases_name = "phases";
  symbol_exprt phases_symbl{phases_name, bool_typet{}};
  exprt phases_exp = false_exprt{};
  // __SZH_DR_ADD_BEGIN__
  irep_idt phases_swap_name = "phases_swap";
  symbol_exprt phases_swap_symbl{phases_swap_name, bool_typet{}};
  exprt phases_swap_exp = false_exprt{};
  // __SZH_DR_ADD_END__
  if(getenv("IEKKE_DUMP_GLOBALS") != nullptr)
  {
    std::cout << "=== shared objects seen by the race encoding ===\n";
    for(auto v : global_variables)
    {
      std::set<unsigned> rt, wt;
      if(reads.count(v))
        for(const auto &e : reads.at(v))
          rt.insert(e.thread);
      if(writes.count(v))
        for(const auto &e : writes.at(v))
          wt.insert(e.thread);
      std::cout << "  " << v << "  reads=" << (reads.count(v) ? reads.at(v).size() : 0)
                << " from " << rt.size() << " thread(s)"
                << "  writes=" << (writes.count(v) ? writes.at(v).size() : 0)
                << " from " << wt.size() << " thread(s)";
      if(getenv("IEKKE_DUMP_ACCESSES") != nullptr)
      {
        std::cout << "\n";
        if(writes.count(v))
          for(const auto &e : writes.at(v))
            std::cout << "      W t=" << e.thread << " label=" << e.label
                      << " num=" << e.num
                      << " atomic=" << (e.s_it->atomic_section_id != 0)
                      << " ultimo_del_blocco="
                      << (e.label < labels[e.thread] ? "forse" : "si")
                      << " fn=" << id2string(
                           e.s_it->source.pc->source_location().get_function())
                      << "\n";
        if(reads.count(v))
          for(const auto &e : reads.at(v))
            std::cout << "      R t=" << e.thread << " label=" << e.label
                      << " num=" << e.num
                      << " atomic=" << (e.s_it->atomic_section_id != 0)
                      << " primo_del_blocco="
                      << (e.label > 1 ? "forse" : "si")
                      << " fn=" << id2string(
                           e.s_it->source.pc->source_location().get_function())
                      << "\n";
        std::cout << "   ";
      }
      if(v.starts_with("__CPROVER"))
        std::cout << "   [skipped: __CPROVER]";
      else if(equation.symbol_is_atomic(ns, v))
        std::cout << "   [skipped: atomic]";
      std::cout << "\n";
    }
    std::cout << "=== end shared objects ===\n";
  }
  for (auto v : global_variables) {
    if (v.starts_with("__CPROVER"))
      continue;
    if (equation.symbol_is_atomic(ns,v))
      continue;
    symbol_exprt pha_1 = phase_1(/*log,*/ equation, v);
    symbol_exprt pha_2 = phase_2(/*log,*/ equation, v);
    exprt pha_1_2 = and_exprt{pha_1, pha_2};
    phases_exp = or_exprt{phases_exp, pha_1_2};
    // __SZH_DR_ADD_BEGIN__
    // Read-first/write-second pairing (see phase_1_swap): a race that
    // phase_1/phase_2 (write-first only) cannot witness.
    symbol_exprt pha_1_swap = phase_1_swap(equation, v);
    symbol_exprt pha_2_swap = phase_2_swap(equation, v);
    exprt pha_1_2_swap = and_exprt{pha_1_swap, pha_2_swap};
    phases_swap_exp = or_exprt{phases_swap_exp, pha_1_2_swap};
    // __SZH_DR_ADD_END__
  }
  phases_exp = equal_exprt{phases_symbl, phases_exp};
  simplify(phases_exp, ns);
  equation.constraint(
    phases_exp, "datarace constraint", equation.SSA_steps.begin()->source);

  // __SZH_DR_ADD_BEGIN__
  phases_swap_exp = equal_exprt{phases_swap_symbl, phases_swap_exp};
  simplify(phases_swap_exp, ns);
  equation.constraint(
    phases_swap_exp, "datarace constraint", equation.SSA_steps.begin()->source);
  // __SZH_DR_ADD_END__

  symbol_exprt same_round_symbl = same_round(/*log,*/ equation);

  symbol_exprt no_interf_symbl = no_interf(/*log,*/ equation);

  // __SZH_DR_ADD_BEGIN__
  symbol_exprt same_round_swap_symbl = same_round_swap(equation);

  symbol_exprt no_interf_swap_symbl = no_interf_swap(equation);
  // __SZH_DR_ADD_END__

  exprt datarace_contraint = and_exprt{phases_symbl, and_exprt{same_round_symbl, no_interf_symbl}};
  // __SZH_DR_ADD_BEGIN__
  // Purely additive: OR in the read-first/write-second pairing. Cannot
  // regress the original (roles 1/2) detection -- it is untouched above
  // -- only widen it with a witness the original pairing structurally
  // cannot express.
  exprt datarace_contraint_swap = and_exprt{phases_swap_symbl, and_exprt{same_round_swap_symbl, no_interf_swap_symbl}};
  datarace_contraint = or_exprt{datarace_contraint, datarace_contraint_swap};
  // __SZH_DR_ADD_END__
  simplify(datarace_contraint, ns);
  //equation.constraint(
   // datarace_contraint, "datarace constraint", equation.SSA_steps.begin()->source);
  equation.assertion(true_exprt{},not_exprt{datarace_contraint},"datarace",equation.SSA_steps.begin()->source);
}

void lazy_pot::collect_reads_and_writes(
  symex_target_equationt::SSA_stepst &ssa_steps)
{
  unsigned num = 0;
  skipped_writes = 0; skipped_reads = 0;
  symex_target_equationt::SSA_stepst::iterator prev =
        ssa_steps.begin();
  std::map<unsigned, std::vector<symex_target_equationt::SSA_stepst::iterator>>
    pending_trace_steps;

  struct trace_position
  {
    bool valid = false;
    unsigned label = 0;
    unsigned num = 0;
    unsigned thread = 0;
    unsigned next_order = 0;
  };
  std::map<unsigned, trace_position> last_trace_positions;

  const auto should_stage_trace_step = [](const SSA_stept &step) {
    if(!step.round_robin_exec_symbols.empty())
      return false;

    if(step.is_assignment())
    {
      return step.assignment_type != symex_targett::assignment_typet::PHI &&
             step.assignment_type != symex_targett::assignment_typet::GUARD;
    }

    return step.is_decl() || step.is_function_call() ||
           step.is_function_return() || step.is_goto() || step.is_location() ||
           step.is_output();
  };

  const auto annotate_with_position = [this](SSA_stept &step, trace_position &pos) {
    annotate_round_robin_trace_event(
      step,
      pos.label,
      pos.num,
      pos.thread,
      pos.next_order++);
  };

  const auto annotate_trace_event =
    [this, &pending_trace_steps, &last_trace_positions, &annotate_with_position](
      symex_target_equationt::SSA_stepst::iterator event,
      unsigned label,
      unsigned event_num,
      unsigned thread,
      symex_target_equationt::SSA_stepst::iterator next,
      const symex_target_equationt::SSA_stepst::iterator &end) {
      unsigned event_order = 0;
      auto &pending = pending_trace_steps[thread];
      auto &last_position = last_trace_positions[thread];

      if(last_position.valid)
      {
        for(auto pending_step : pending)
          annotate_with_position(*pending_step, last_position);
      }
      else
      {
        trace_position first_position{true, label, event_num, thread, 0};
        // Local initialisation steps before the first shared event only serve to
        // position the round-robin trace; they should not pollute the cex.
        for(auto pending_step : pending)
        {
          if(pending_step->is_assignment())
            pending_step->hidden = true;
          annotate_with_position(*pending_step, first_position);
        }
        event_order = first_position.next_order;
      }
      pending.clear();

      annotate_round_robin_trace_event(
        *event,
        label,
        event_num,
        thread,
        event_order);

      last_position = trace_position{true, label, event_num, thread, event_order + 1};
      if(next != end && next->is_assignment())
        annotate_with_position(*next, last_position);
    };

  // Idea: before the first thread is spawned, thread 0 is the only
  // thread that exists, so no context-switch point placed in that
  // prologue can ever matter to the schedule space -- and the paper's
  // own canonicality formula (Enabled/ABR/ABW over the gap) already
  // forces every such split's fire_cond to false, since a gap with no
  // other live thread can contain no executed access. Physically
  // folding thread 0's pre-spawn accesses into a single label (rather
  // than adding constraints to rule out the extra splits after the
  // fact) means create_cs_constraint's per-label loop never builds the
  // GE/Enabled/Exec/tightening machinery for them at all. This is
  // purely thread 0's own straight-line code, so nothing about
  // multi-thread scheduling is lost; a blocking statement in that
  // prologue still gets its own label below (unaffected by this cut),
  // so the exact set of reachable prologue asserts/assumes is preserved.
  //
  // The cut point is the last shared write/read strictly before the
  // FIRST is_spawn() step -- not the spawn step itself. handling_active_
  // threads injects the new thread's active-flag write (itself a shared
  // write) immediately before the spawn step; that flag write must keep
  // its own label, since active_at_turn/phase_1 use its position to
  // determine exactly when a thread becomes active relative to other
  // accesses -- folding it into the merged prologue would make a race
  // between an initializer and the spawned thread's first access
  // indistinguishable from one that predates thread creation entirely.
  symex_target_equationt::SSA_stepst::iterator prologue_end_step =
    ssa_steps.end();
  {
    auto spawn_it = ssa_steps.begin();
    for(; spawn_it != ssa_steps.end(); ++spawn_it)
      if(spawn_it->is_spawn())
        break;
    if(spawn_it != ssa_steps.end())
    {
      auto it = spawn_it;
      while(it != ssa_steps.begin())
      {
        --it;
        if(it->is_shared_write() || it->is_shared_read())
        {
          prologue_end_step = it;
          break;
        }
      }
    }
  }
  // Idea 1 (physical pre-spawn context-switch elimination) is implemented
  // above but disabled by default: A/B-measured on elimination_backoff_stack,
  // triangular-longest-2 and safestack_test (base and --por, idea1 vs
  // noidea1 binaries built from an otherwise-identical tree), it reduces
  // label count as designed but does NOT reliably translate into a wall-
  // clock win. Base mode got worse on every benchmark with any real
  // prologue to fold (elimination_backoff_stack +68%, safestack +109%,
  // reproduced on repeat); --por is benchmark-dependent, not consistently
  // either way (elimination_backoff_stack +82% worse, safestack -63%
  // better). Net: this does not meet a no regression bar, so it stays
  // off pending a mechanistic explanation (leading hypothesis: as with the
  // earlier 'reach' OR-chain collapse this session, removing variables/
  // clauses that looked purely redundant removed propagation structure the
  // solver -- and possibly --por's canonicality machinery -- was actually
  // using, rather than being pure overhead). The prologue-detection logic
  // above is left in place, inert, so this can be flipped back to
  // '(prologue_end_step != ssa_steps.end())' for further investigation
  // without re-deriving it.
  //
  // Re-measured 2026-09-28 against the current tree, which has since gained
  // the _Atomic RMW fix, the publication filter and arrays-uf: 44 tasks of
  // the lazypo-mono-cur configuration under --por, four binaries one flip
  // apart, run one at a time, with the headline cases repeated three times in
  // isolation (spread under 1%, so these are not noise). The conclusion
  // stands, but the --por figure above is stale. elimination_backoff_stack is
  // now 1.72x *better* with folding on (260.9/260.8/260.3s becomes
  // 151.5/152.4/151.4s) and fib_unsafe-10 1.40x better, while
  // per-thread-array-join-counter is 3.13x worse (4.38s becomes 13.68s).
  // Geometric mean over the 16 tasks taking more than a second is 0.959x --
  // slightly worse than leaving it off -- with per-task ratios from 0.32x to
  // 1.40x. No mode produced a wrong answer, so both folds are sound; what
  // they are not is reliable.
  //
  // The mechanism the hypothesis above was reaching for: folding labels
  // barely touches the formula at all. Cutting 20.5% of the labels buys 0.07%
  // of the clauses, because the cs encoding is a thermometer over boolean GE
  // symbols -- numerous and nearly free -- while the clause mass sits in the
  // wide-bitvector read-from and SSA terms. Label folding can therefore only
  // act on the solver's search, never on the problem's size, and which way it
  // acts turns out to be structural rather than proportional to the labels
  // removed: elimination_backoff_stack gains 1.72x from a 0.9% label
  // reduction (7474 to 7409), while per-thread-array-join-counter loses 3.13x
  // from a 15% one (272 to 230). That asymmetry, not the label count, is what
  // any future attempt here has to predict.
  bool in_prologue = false;

  // Idea 7 (thread-exclusive-variable label folding, off critical path of
  // Idea 1 above -- independent of whether in_prologue is enabled): a
  // variable touched by at most one thread, once thread 0's own pre-spawn
  // prologue accesses are set aside (those are already provably harmless
  // on their own -- see prologue_end_step above, computed regardless of
  // in_prologue), can never be raced on by any other thread: no other
  // thread ever executes an instruction that touches it, so a context-
  // switch point placed at one of its accesses carries no scheduling
  // information for anyone. Fold such accesses into whichever label
  // they're adjacent to instead of giving each its own. Needs a full
  // pre-pass because whether a variable qualifies isn't known until every
  // access to it in the whole trace has been seen (e.g. fib_unsafe.h's
  // p/q/cur/prev/next/x: file-scope globals that are, in practice, each
  // used by exactly one thread for the entire program -- but declaration
  // scope alone doesn't tell us that, only scanning every access does).
  //
  // Re-measured 2026-09-28 under --por: the !this->por gate at the use sites
  // below is still the right call. elimination_backoff_stack goes from 260.9s
  // to 514.5s with the gate removed (1.97x worse, three reps, spread under
  // 1%) -- worse than the A/B could show, since it simply timed out at the
  // competition's 300s cap, and it was the only task in the sample to lose an
  // answer. Geometric mean over the tasks taking more than a second is
  // 1.004x, so there is nothing on average to buy that risk with.
  std::unordered_set<irep_idt> single_thread_variables;
  {
    std::unordered_map<irep_idt, std::unordered_set<std::size_t>>
      threads_touching;
    bool scan_in_prologue = (prologue_end_step != ssa_steps.end());
    for(auto it = ssa_steps.begin(); it != ssa_steps.end(); ++it)
    {
      if(scan_in_prologue && it == prologue_end_step)
        scan_in_prologue = false;
      if(!(it->is_shared_write() || it->is_shared_read()))
        continue;
      if(!can_cast_expr<symbol_exprt>(it->ssa_lhs))
        continue;
      if(scan_in_prologue && it->source.thread_nr == 0)
        continue;
      threads_touching[it->ssa_lhs.get_l1_object_identifier()].insert(
        it->source.thread_nr);
    }
    for(const auto &entry : threads_touching)
      if(entry.second.size() <= 1)
        single_thread_variables.insert(entry.first);
  }

  // Publication filter. A write to (or read of) a freshly allocated object,
  // performed before the allocating thread stores that object's address into
  // a shared location, cannot take part in a race: any other thread has to
  // obtain the address by reading the location it was published to, and that
  // read is necessarily ordered after the publishing write, which is itself
  // ordered after the access we are looking at. The pointer dependence alone
  // establishes happens-before, with or without a lock.
  //
  // Without this, the allocation-time and init() writes of a node that is
  // only later linked into a shared list pair up with the post-publication
  // accesses of another thread, and a race is reported on a race-free program
  // -- the 28-race_reach_8* and libvsync families. Races on the published
  // pointer itself are untouched: that is a different variable and keeps all
  // of its events.
  //
  // Deliberately NOT exempting an object whose address never reaches a shared
  // location: it can still be handed to another thread as a pthread_create
  // argument, and an access placed after that spawn would then be excused
  // wrongly. Such objects already behave correctly (nothing pairs with them),
  // so there is nothing to gain and soundness to lose.
  const auto dynamic_object_key = [](const irep_idt &id) -> std::string {
    const std::string s = id2string(id);
    const std::string tag = "dynamic_object";
    const auto pos = s.find(tag);
    if(pos == std::string::npos)
      return std::string();
    auto end = pos + tag.size();
    while(end < s.size() && isdigit(static_cast<unsigned char>(s[end])))
      ++end;
    if(end == pos + tag.size())
      return std::string();
    return s.substr(pos, end - pos);
  };

  std::function<void(const exprt &, std::set<std::string> &)> scan_symbols =
    [&](const exprt &e, std::set<std::string> &out) {
      if(e.id() == ID_symbol)
      {
        const std::string k = dynamic_object_key(e.get(ID_identifier));
        if(!k.empty())
          out.insert(k);
      }
      for(const auto &op : e.operands())
        scan_symbols(op, out);
    };

  // Which objects can the value of this expression be the address of?
  // Two sources: an address-of taken right here, and any pointer-typed
  // symbol whose value we have already resolved. The second is what makes
  // `list->next = node` count as a publication -- after SSA renaming its
  // right-hand side is the variable `node`, not `&dynamic_objectN`.
  std::unordered_map<irep_idt, std::set<std::string>> points_to;

  std::function<void(const exprt &, std::set<std::string> &)> value_objects =
    [&](const exprt &e, std::set<std::string> &out) {
      if(e.id() == ID_address_of)
      {
        scan_symbols(e, out);
        return;
      }
      if(e.id() == ID_symbol)
      {
        const auto it = points_to.find(e.get(ID_identifier));
        if(it != points_to.end())
          out.insert(it->second.begin(), it->second.end());
      }
      for(const auto &op : e.operands())
        value_objects(op, out);
    };

  // Only ordinary scalar data may be exempted -- see the note on
  // pre_publication_access below. An aggregate access is either a whole
  // object (a mutex being initialised, say) or something whose internal
  // structure the filter does not model, and excusing those can hide a real
  // race rather than a spurious one.
  const auto is_scalar_data = [&](const typet &t) {
    if(t.id().empty())
      return false;
    const irep_idt id = ns.follow(t).id();
    return id == ID_signedbv || id == ID_unsignedbv || id == ID_floatbv ||
           id == ID_fixedbv || id == ID_bool || id == ID_c_bool ||
           id == ID_pointer || id == ID_c_enum;
  };

  // Only under --datarace, the only mode that pairs accesses. The filter
  // used to remove the events outright, which thinned the value flow as well
  // and cost a correct unreach-call answer when it applied everywhere; it now
  // only marks them race_exempt.
  const bool pubfilter_enabled =
    datarace && getenv("LAZYPO_NO_PUBFILTER") == nullptr;

  // The thread that allocated each dynamic object, read off malloc's own
  // model: it stores the fresh address into a CPROVER-internal global, and
  // that right-hand side is a literal address-of, so no points-to set can
  // widen it and attribute the allocation elsewhere. "First thread to touch
  // the object" was tried instead and does not work -- under
  // --refined-pointer-analysis main writes through a pointer wide enough to
  // reach every node, so all four objects of 28-race_reach_84 came out
  // allocated by thread 0.
  //
  // Objects with no such record (not every dynamic object comes from the
  // malloc model) fall back to first_publisher below, which is what this
  // filter used before.
  std::unordered_map<std::string, std::size_t> allocator;

  // The first thread seen publishing each object, in equation order. Only
  // used for the fallback just described.
  std::unordered_map<std::string, std::size_t> first_publisher;

  // (object, thread) -> that thread's own earliest step ordinal at which it
  // makes the object's address visible to others. Keyed by thread because
  // the ordinals below are per-thread counters: comparing one thread's
  // ordinal against another's compares two different counters and means
  // nothing.
  std::map<std::pair<std::string, std::size_t>, std::size_t> publication;
  if(pubfilter_enabled)
  {
    std::map<unsigned, std::size_t> scan_ord;
    for(auto it = ssa_steps.begin(); it != ssa_steps.end(); ++it)
    {
      const std::size_t my_ord = scan_ord[it->source.thread_nr]++;

      // learn what pointer-valued targets may point to
      if(it->is_assignment() && can_cast_expr<symbol_exprt>(it->ssa_lhs))
      {
        std::set<std::string> objs;
        value_objects(it->ssa_rhs, objs);
        if(!objs.empty())
          points_to[it->ssa_lhs.get_identifier()].insert(
            objs.begin(), objs.end());
      }

      if(!it->is_shared_write())
        continue;

      // CBMC's own bookkeeping is not a publication -- malloc's model
      // stores the fresh object's address into internal globals, which would
      // otherwise date the publication to the allocation itself and leave
      // every user-level initialisation unexempted. It is, however, exactly
      // where the allocating thread can be read off.
      if(can_cast_expr<symbol_exprt>(it->ssa_lhs) &&
         has_prefix(
           id2string(it->ssa_lhs.get_l1_object_identifier()), CPROVER_PREFIX))
      {
        auto alloc_next = it;
        ++alloc_next;
        if(alloc_next != ssa_steps.end() && alloc_next->is_assignment())
        {
          std::set<std::string> fresh;
          value_objects(alloc_next->ssa_rhs, fresh);
          for(const auto &k : fresh)
            allocator.emplace(
              k, static_cast<std::size_t>(it->source.thread_nr));
        }
        continue;
      }

      // the stored value lives in the assignment step that follows
      auto next = it;
      ++next;
      if(next == ssa_steps.end() || !next->is_assignment())
        continue;

      std::set<std::string> published;
      value_objects(next->ssa_rhs, published);
      for(const auto &k : published)
      {
        // Earliest publication *by this thread*. A thread that only appears
        // to publish the object records its own entry and leaves the
        // allocating thread's window alone.
        const auto key =
          std::make_pair(k, static_cast<std::size_t>(it->source.thread_nr));
        const auto pub = publication.find(key);
        if(pub == publication.end())
          publication.emplace(key, my_ord);
        else if(my_ord < pub->second)
          pub->second = my_ord;
        first_publisher.emplace(
          k, static_cast<std::size_t>(it->source.thread_nr));
      }
    }
  }

  // On by default under --datarace. Measured paired over all 1029
  // no-data-race tasks, same bounds, only the filter differing: correct
  // 1002 -> 1006, wrong 9 -> 5, score +57. The five it fixes are the
  // 28-race_reach_8* family; the four libvsync false alarms are a different
  // problem (CBMC's unsound pointer-typed shared writes, issue #305) and are
  // untouched. 09-regions_03-list2_rc's FAILED was spurious before the
  // filter -- it came from a pre-pthread_create write that cannot race with
  // anything -- and its real race was lost with the filter until the excused
  // accesses were kept in the value flow (see collect_reads_and_writes).
  // Turn the filter off with LAZYPO_NO_PUBFILTER.
  const bool pubfilter_off = !pubfilter_enabled;
  const bool pubfilter_debug = getenv("LAZYPO_PUBFILTER_DEBUG") != nullptr;
  if(pubfilter_debug)
  {
    for(const auto &a : allocator)
      std::cerr << "PUBFILTER " << a.first << " allocated by thread "
                << a.second << "\n";
    for(const auto &p : publication)
      std::cerr << "PUBFILTER published " << p.first.first << " by thread "
                << p.first.second << " at its ordinal " << p.second << "\n";
  }

  const auto pre_publication_access =
    [&](const irep_idt &l1_id, std::size_t thread, std::size_t ordinal,
        const typet &access_type) {
      if(pubfilter_off)
        return false;
      const std::string k = dynamic_object_key(l1_id);
      if(k.empty())
        return false;
      // The window must be closed by a publication this thread performs
      // itself: an object whose address this thread never stores anywhere
      // may still have escaped by a route this pass does not see (a thread
      // argument, say), so no exemption is given at all.
      const auto pub = publication.find(std::make_pair(k, thread));
      if(pub == publication.end())
        return false;
      // And only the allocating thread may be exempted. Asking instead for a
      // match on the *publisher* makes the filter fail exactly when the
      // points-to set is wide enough to invent one: under
      // --refined-pointer-analysis main appeared to publish both workers'
      // nodes, which cost 28-race_reach_84 and _94 a false alarm each.
      const auto alloc = allocator.find(k);
      if(alloc != allocator.end())
      {
        if(alloc->second != thread)
          return false;
      }
      else
      {
        const auto fp = first_publisher.find(k);
        if(fp == first_publisher.end() || fp->second != thread)
          return false;
      }
      const bool exempt = ordinal < pub->second && is_scalar_data(access_type);
      if(exempt && pubfilter_debug)
        std::cerr << "PUBFILTER exempt " << id2string(l1_id) << " thread "
                  << thread << " ordinal " << ordinal << " < its pub "
                  << pub->second << "\n";
      return exempt;
    };

  std::map<unsigned, std::size_t> step_ordinal;

  for(symex_target_equationt::SSA_stepst::iterator s_it =
        ssa_steps.begin();
      s_it != ssa_steps.end();
      s_it++)
  {
    // must advance in lockstep with the publication pre-pass above
    const std::size_t step_ord = step_ordinal[s_it->source.thread_nr]++;

    if(in_prologue && s_it == prologue_end_step)
      in_prologue = false;

    if(this->labels.count(s_it->source.thread_nr) == 0)
    {
      // massimo, non assegnamento: i thread non compaiono necessariamente in
      // ordine crescente nell'equazione, e da `threads` dipende threads_bits.
      threads = std::max<std::size_t>(threads, s_it->source.thread_nr);
      labels[s_it->source.thread_nr] = 0;
    }

    if(should_stage_trace_step(*s_it))
      pending_trace_steps[s_it->source.thread_nr].push_back(s_it);

    if(s_it->is_assert() || s_it->is_assume())
    {
      if (labels[s_it->source.thread_nr] == 0  || s_it->atomic_section_id == 0)
      {
        labels[s_it->source.thread_nr]++;
        num = 0;
      }
      else
        num++;

      exprt where = from_integer(-1,size_type());
      shared_event shared_event{s_it, where, labels[s_it->source.thread_nr], num, s_it->source.thread_nr};
      annotate_trace_event(
              s_it,
              shared_event.label,
              shared_event.num,
              shared_event.thread,
              ssa_steps.end(),
              ssa_steps.end());
      {
        auto &gv = guards[s_it->source.thread_nr][labels[s_it->source.thread_nr]];
        if(gv.size() <= num)
          gv.resize(num + 1, true_exprt{});
        gv[num] = s_it->guard;
      }


      this->blocking_events.emplace_back(shared_event);
      shared_events.emplace_back(shared_event);
      prev = s_it;
    }

    if(s_it->is_atomic_begin())
    {
      if(getenv("LAZYPO_ACCESS_DEBUG") && s_it->source.thread_nr == 1)
      {
        exprt g = s_it->guard;
        simplify(g, ns);
        std::cerr << "ATOMIC_BEGIN thread=1 guard_false=" << s_it->guard.is_false()
                  << " simplified_false=" << g.is_false() << "\n";
      }
      labels[s_it->source.thread_nr]++;
      // Was not reset here (unlike is_atomic_end below); every new
      // label needs num reset to 0, otherwise num grows unboundedly
      // once the prologue-folding above lets several atomic sections
      // (each bumping labels[thread] once, here) share a smaller label
      // range than before. This does NOT by itself fix the
      // independent, still-open issue that atomic_begin's own guard
      // write below still occupies num 0, leaving a phantom
      // guards[...][0] entry the real first access (at num 1, since
      // accesses inside an atomic section only ever num++) never
      // reuses -- that phantom is what makes create_cs_constraint's
      // context-boundary tightening witness vacuous for every atomic
      // block. Fixing that fully needs NOT writing gv[num] here at
      // all, left as a separate, independently-regression-tested
      // change (not bundled with this one).
      num = 0;
      {
        auto &gv = guards[s_it->source.thread_nr][labels[s_it->source.thread_nr]];
        if(gv.size() <= num)
          gv.resize(num + 1, true_exprt{});
        gv[num] = s_it->guard;
      }
      atomic_sections.emplace_back(
        s_it->source.thread_nr,
        std::pair<unsigned, unsigned>(labels[s_it->source.thread_nr], 0u));
      prev = s_it;
    }

    if(s_it->is_atomic_end())
    {
      // un atomic_end senza begin corrispondente lascerebbe il vector vuoto
      if(!atomic_sections.empty())
        atomic_sections.back().second.second = labels[s_it->source.thread_nr];
      // Was: num = 0 here too. But is_atomic_end() does NOT bump
      // labels[thread] (only is_atomic_begin() does), so resetting num
      // here reuses the same (thread,label) key space an access right
      // after the atomic section would also use, colliding two distinct
      // accesses onto one (thread,label,num) key (guards[...] clobbered,
      // property search terminates one iteration too early). num must
      // keep counting within the still-open label until the next
      // is_atomic_begin() legitimately starts a fresh one.
    }

    if(s_it->is_shared_write()) {
      // TODO: this may be too restrictive
      if(can_cast_expr<symbol_exprt>(s_it->ssa_lhs))
      {
        if(getenv("LAZYPO_ACCESS_DEBUG"))
          std::cerr << "ACCESS_DEBUG W " << s_it->source.thread_nr << " "
                    << s_it->ssa_lhs.get_l1_object_identifier() << "\n";
        // Was: merged two non-atomic shared accesses into one block
        // whenever they shared source location AND guard -- which two
        // distinct accesses from the SAME GOTO instruction (the common
        // case: e.g. `c = c + 1` reads then writes c) or the same source
        // line always do, since location/guard are per-instruction, not
        // per-access. That silently made the round-robin scheduler unable
        // to interleave between them, hiding real bugs (confirmed: lost
        // updates, and the repo's own svcomp13_fib_bench_longer_unsafe
        // regression test, go undetected under --rounds/--por at every
        // bound). The paper specifies every non-atomic shared access is
        // its own singleton block; every non-atomic access must start a
        // new one, exactly like the assert/assume handling above already
        // does.
        // Base mode benefits consistently (fib_unsafe-6 base 168.2s to 36.9s,
        // elimination_backoff_stack base 60.6s to 28.6s); --por regresses
        // just as consistently on CAS/elimination-heavy benchmarks
        // (elimination_backoff_stack POR 129.4s to timeout at 300s,
        // safestack_test POR 17.5-47.2s to 100.8s) -- same "removed
        // structure --por's canonicality machinery relied on" pattern as
        // Idea 1. Gated to base mode only rather than disabled outright,
        // since unlike Idea 1 the base-mode win here is large and so far
        // exceptionless.
        const bool thread_exclusive_var = !this->por && single_thread_variables.count(
          s_it->ssa_lhs.get_l1_object_identifier()) > 0;
        if (labels[s_it->source.thread_nr] == 0
              || (s_it->atomic_section_id == 0
                  && !(s_it->source.thread_nr == 0 && in_prologue)
                  && !thread_exclusive_var))
        {
          labels[s_it->source.thread_nr]++;
          num = 0;
        }
        else
          num++;

        exprt where = from_integer(-1,size_type());
        auto next = s_it;
        next++;
        // A read/write whose value feeds an if-condition's guard update
        // (`if (arr[k] != 0) ...`) has a GOTO step between it and the
        // assignment that actually computes the guard -- the GOTO is the
        // branch instruction itself, emitted before the guard is folded in.
        // Skip exactly that one step, no further, before giving up. See
        // ~/tidrace_check/tid_ifcond_const.c.
        if(next != ssa_steps.end() && next->type == goto_trace_stept::typet::GOTO)
          next++;
        if (next != ssa_steps.end() && next->is_assignment() && next->ssa_rhs.id() == ID_with) { //ARRAY
          where = to_with_expr(next->ssa_rhs).where();
        }
        else if (next != ssa_steps.end() && next->is_assignment() &&
                 access_offset(next->ssa_rhs).is_not_nil()) { //ARRAY sotto un if
          where = access_offset(next->ssa_rhs);
        }
        else { //STRUCT
          std::string id = id2string(to_symbol_expr(s_it->ssa_lhs).get_identifier());
          auto pos = id.rfind("..");
          if(pos != std::string::npos)
          {
            std::string field = id.substr(pos + 2);
            where = from_integer(hash_string(field), size_type());
          }
        }

        shared_event shared_event{s_it, where,  labels[s_it->source.thread_nr], num, s_it->source.thread_nr};
        annotate_trace_event(
                  s_it,
                  shared_event.label,
                  shared_event.num,
                  shared_event.thread,
                  next,
                  ssa_steps.end());
        {
          auto &gv = guards[s_it->source.thread_nr][labels[s_it->source.thread_nr]];
          if(gv.size() <= num)
            gv.resize(num + 1, true_exprt{});
          gv[num] = s_it->guard;
        }

        shared_events.emplace_back(shared_event);
        {
          const irep_idt access_id =
            shared_event.s_it->ssa_lhs.get_l1_object_identifier();
          // Excused from race pairing only. Leaving the access out of
          // `writes`/`reads` altogether also removed it from the value flow:
          // the lazy chain then starts from the first *remaining* write, so a
          // post-publication `p->datum++` read its own result and could
          // never execute -- every run reaching it was pruned, with the race
          // after it and any assertion after it. See the datarace-por tests
          // publish-then-rmw-racy and publish-then-rmw-not-pruned.
          shared_event.race_exempt = pre_publication_access(
            access_id, shared_event.thread, step_ord,
            shared_event.s_it->ssa_lhs.type());
          this->writes[access_id].emplace_back(shared_event);
          this->global_variables.emplace(access_id);
        }
        prev = s_it;
      }
      else
      {
        ++skipped_writes;
      }
    }
    if(s_it->is_shared_read())
    {
      if(getenv("LAZYPO_ACCESS_DEBUG") && can_cast_expr<symbol_exprt>(s_it->ssa_lhs))
        std::cerr << "ACCESS_DEBUG R " << s_it->source.thread_nr << " "
                  << s_it->ssa_lhs.get_l1_object_identifier() << "\n";
      // TODO: this may be too restrictive
      if(can_cast_expr<symbol_exprt>(s_it->ssa_lhs))
      {
        // Was: merged two non-atomic shared accesses into one block
        // whenever they shared source location AND guard -- which two
        // distinct accesses from the SAME GOTO instruction (the common
        // case: e.g. `c = c + 1` reads then writes c) or the same source
        // line always do, since location/guard are per-instruction, not
        // per-access. That silently made the round-robin scheduler unable
        // to interleave between them, hiding real bugs (confirmed: lost
        // updates, and the repo's own svcomp13_fib_bench_longer_unsafe
        // regression test, go undetected under --rounds/--por at every
        // bound). The paper specifies every non-atomic shared access is
        // its own singleton block; every non-atomic access must start a
        // new one, exactly like the assert/assume handling above already
        // does.
        // Base mode benefits consistently (fib_unsafe-6 base 168.2s to 36.9s,
        // elimination_backoff_stack base 60.6s to 28.6s); --por regresses
        // just as consistently on CAS/elimination-heavy benchmarks
        // (elimination_backoff_stack POR 129.4s to timeout at 300s,
        // safestack_test POR 17.5-47.2s to 100.8s) -- same "removed
        // structure --por's canonicality machinery relied on" pattern as
        // Idea 1. Gated to base mode only rather than disabled outright,
        // since unlike Idea 1 the base-mode win here is large and so far
        // exceptionless.
        const bool thread_exclusive_var = !this->por && single_thread_variables.count(
          s_it->ssa_lhs.get_l1_object_identifier()) > 0;
        if (labels[s_it->source.thread_nr] == 0
              || (s_it->atomic_section_id == 0
                  && !(s_it->source.thread_nr == 0 && in_prologue)
                  && !thread_exclusive_var))
        {
          labels[s_it->source.thread_nr]++;
          num = 0;
        }
        else
          num++;

        exprt where = from_integer(-1,size_type());
        auto next = s_it;
        next++;
        // See the write-site comment above: skip exactly one GOTO step
        // between this read and the assignment that consumes it, when the
        // read feeds an if-condition's guard update directly.
        if(next != ssa_steps.end() && next->type == goto_trace_stept::typet::GOTO)
          next++;
        if (next != ssa_steps.end() && next->is_assignment() && next->ssa_rhs.id() == ID_index) { //ARRAY
          where = to_index_expr(next->ssa_rhs).index();
        }
        else if (next != ssa_steps.end() && next->is_assignment() &&
                 access_offset(next->ssa_rhs).is_not_nil()) { //ARRAY sotto un if
          where = access_offset(next->ssa_rhs);
        }
        else { //STRUCT
          std::string id = id2string(to_symbol_expr(s_it->ssa_lhs).get_identifier());
          auto pos = id.rfind("..");
          if(pos != std::string::npos)
          {
            std::string field = id.substr(pos + 2);
            where = from_integer(hash_string(field), size_type());
          }
        }

        shared_event shared_event{s_it, where,  labels[s_it->source.thread_nr], num, s_it->source.thread_nr};
        annotate_trace_event(
                  s_it,
                  shared_event.label,
                  shared_event.num,
                  shared_event.thread,
                  next,
                  ssa_steps.end());
        {
          auto &gv = guards[s_it->source.thread_nr][labels[s_it->source.thread_nr]];
          if(gv.size() <= num)
            gv.resize(num + 1, true_exprt{});
          gv[num] = s_it->guard;
        }


        shared_events.emplace_back(shared_event);

        {
          const irep_idt access_id =
            shared_event.s_it->ssa_lhs.get_l1_object_identifier();
          // See the write case above.
          shared_event.race_exempt = pre_publication_access(
            access_id, shared_event.thread, step_ord,
            shared_event.s_it->ssa_lhs.type());
          this->reads[access_id].emplace_back(shared_event);
          this->global_variables.insert(access_id);
        }
        prev = s_it;
      }
      else
      {
        ++skipped_reads;
      }
    }
  }
  for(auto global_variable : global_variables) {
    const unsigned n_ids =
      (this->writes.count(global_variable)
         ? this->writes.at(global_variable).size() * rounds
         : 0) +
      (this->reads.count(global_variable)
         ? this->reads.at(global_variable).size() * rounds
         : 0) + 1;
    this->bit_writes[global_variable] = 32 - __builtin_clz(n_ids);
    this->bit_reads[global_variable] = this->bit_writes[global_variable];
  }

  for(auto &thread_and_pending : pending_trace_steps)
  {
    unsigned thread = thread_and_pending.first;
    auto last_position_it = last_trace_positions.find(thread);

    trace_position fallback{true, 0, 0, thread, 0};
    trace_position &pos = (last_position_it != last_trace_positions.end() &&
                           last_position_it->second.valid)
                            ? last_position_it->second
                            : fallback;

    for(auto pending_step : thread_and_pending.second)
    {
      if(pending_step->round_robin_exec_symbols.empty())
        annotate_with_position(*pending_step, pos);
    }
  }

  threads_bits = 0 ? 0 : 32 - __builtin_clz(threads + 1);
  rounds_bits = 0 ? 0 : 32 - __builtin_clz(rounds + 1);

  if(getenv("LAZYPO_ACCESS_DEBUG"))
  {
    unsigned total_labels = 0;
    for(const auto &entry : labels)
    {
      std::cerr << "LABEL_COUNT thread=" << entry.first
                << " labels=" << entry.second << "\n";
      total_labels += entry.second;
    }
    std::cerr << "LABEL_COUNT total=" << total_labels << "\n";
  }
}

void lazy_pot::annotate_round_robin_trace_event(
  SSA_stept &step,
  unsigned label,
  unsigned num,
  unsigned thread,
  unsigned trace_order)
{
  step.round_robin_label = label;
  step.round_robin_num = num;
  step.round_robin_thread = thread;
  step.round_robin_trace_order = trace_order;
  if(step.is_decl())
    step.hidden = true;
  step.round_robin_exec_symbols.clear();
  step.round_robin_exec_symbols.reserve(rounds);

  for(std::size_t round = 1; round <= rounds; ++round)
    step.round_robin_exec_symbols.push_back(
      create_exec_symbol(label, num, thread, round));
}

symbol_exprt lazy_pot::create_lazy_symbol(
  unsigned label,
  unsigned thread,
  size_t round,
  ssa_exprt lhs,
  typet type)
{
  std::string suffix = "_T" + std::to_string(thread) + "_L" +
                       std::to_string(label) + "_R" + std::to_string(round);
  irep_idt lazy_variable_name =
    id2string(to_symbol_expr(lhs).get_identifier()) + suffix;
  symbol_exprt lazy_variable_exprt{lazy_variable_name, type};

  return lazy_variable_exprt;
}

symbol_exprt
lazy_pot::create_exec_symbol(unsigned label, unsigned num, unsigned thread, size_t round)
{
  const uint64_t key = chain_key(round, thread, label, num);
  auto it = exec_map.find(key);
  if(it != exec_map.end())
    return it->second;

  irep_idt exec_name = "Ex_T" + std::to_string(thread) + "_L" +
                       std::to_string(label) + "_N" + std::to_string(num) +
                       "_R" + std::to_string(round);
  symbol_exprt exec_symbol{exec_name, bool_typet{}};

  exec exec_struct{label, num, thread, round, exec_symbol};
  exec_vector.emplace_back(exec_struct);
  exec_map.emplace(key, exec_symbol);

  return exec_symbol;
}

symbol_exprt
lazy_pot::create_exec_symbol_fast(unsigned label, unsigned num, unsigned thread, size_t round)
{

  return create_exec_symbol(label, num, thread, round);
}

symbol_exprt
lazy_pot::create_exec_tot_symbol(symex_target_equationt &equation, unsigned label, unsigned num, unsigned thread)
{
  const uint64_t tot_key = chain_key(0, thread, label, num);
  {
    auto it = exec_tot_map.find(tot_key);
    if(it != exec_tot_map.end())
      return it->second;
  }

  exprt constraint = false_exprt{};
  irep_idt exec_name = "Ex_T" + std::to_string(thread) + "_L" +
                       std::to_string(label) + "_N" + std::to_string(num);
  symbol_exprt exec_symbol{exec_name, bool_typet{}};

  exec_tot exec_struct{label, num, thread, exec_symbol};
  exec_tot_vector.emplace_back(exec_struct);
  exec_tot_map.emplace(tot_key, exec_symbol);

  for (std::size_t round = 1; round <= rounds; round++) {
    constraint = or_exprt{constraint, create_exec_symbol(label,num,thread,round)};
  }
  constraint = equal_exprt{exec_symbol, constraint};
  simplify(constraint, ns);
  equation.constraint(
    constraint, "exec tot constraint", equation.SSA_steps.begin()->source);

  return exec_symbol;
}

symbol_exprt lazy_pot::create_enabled_symbol(
  unsigned label,
  unsigned thread,
  size_t round)
{
  const uint64_t en_key = chain_key(round, thread, label, 0);
  {
    auto it = enabled_map.find(en_key);
    if(it != enabled_map.end())
      return it->second;
  }
  irep_idt enabled_name = "En_T" + std::to_string(thread) + "_L" +
                          std::to_string(label) + "_R" + std::to_string(round);
  symbol_exprt enabled_symbol{enabled_name, bool_typet{}};

  enabled enabled_struct{label, thread, round, enabled_symbol};
  enabled_vector.emplace_back(enabled_struct);
  enabled_map.emplace(en_key, enabled_symbol);

  return enabled_symbol;
}

symbol_exprt lazy_pot::create_cs_symbol(size_t thread, size_t round)
{
  const uint64_t cs_key = chain_key(round, static_cast<unsigned>(thread), 0, 0);
  {
    auto it = cs_map.find(cs_key);
    if(it != cs_map.end())
      return it->second;
  }
  irep_idt cs_name =
    "cs_T" + std::to_string(thread) + "_R" + std::to_string(round);
  symbol_exprt cs_symbol{cs_name, unsignedbv_typet{n_bit[thread]}};

  cs cs_struct{thread, round, cs_symbol};
  cs_vector.emplace_back(cs_struct);
  cs_map.emplace(cs_key, cs_symbol);

  return cs_symbol;
}

symbol_exprt lazy_pot::create_ge_symbol(size_t thread, size_t round, unsigned i)
{
  // GE(thread,round,i) <=> cs(thread,round) >= i, for i in 1..labels[thread]+1.
  // Order/thermometer encoding of the context-switch counter: replaces
  // the raw n_bit-wide bitvector cs used to; a threshold comparison that
  // used to need an O(n_bit)-variable comparator circuit per (label,
  // round) pair is now a single literal read, and monotonicity in round
  // and in threshold (asserted once in create_cs_constraint) gives the
  // solver a direct implication chain instead of bitvector arithmetic to
  // propagate through. See create_cs_constraint for the (C1)-(C3)
  // defining constraints.
  const uint64_t ge_key = chain_key(round, static_cast<unsigned>(thread), i, 1);
  {
    auto it = ge_map.find(ge_key);
    if(it != ge_map.end())
      return it->second;
  }
  irep_idt ge_name = "csge_T" + std::to_string(thread) + "_R" +
                      std::to_string(round) + "_I" + std::to_string(i);
  symbol_exprt ge_symbol{ge_name, bool_typet{}};

  ge ge_struct{thread, round, i, ge_symbol};
  ge_vector.emplace_back(ge_struct);
  ge_map.emplace(ge_key, ge_symbol);

  return ge_symbol;
}

symbol_exprt lazy_pot::create_reach_symbol(unsigned label, size_t thread)
{
  const uint64_t re_key = chain_key(0, static_cast<unsigned>(thread), label, 0);
  {
    auto it = reach_map.find(re_key);
    if(it != reach_map.end())
      return it->second;
  }
  irep_idt reach_name =
    "reach_T" + std::to_string(thread) + "_L" + std::to_string(label);
  symbol_exprt reach_symbol{reach_name, bool_typet{}};

  reach reach_struct{label, thread, reach_symbol};
  reach_vector.emplace_back(reach_struct);
  reach_map.emplace(re_key, reach_symbol);

  return reach_symbol;
}

symbol_exprt lazy_pot::create_active_thread_symbol(unsigned thread)
{
  irep_idt active_thread_name = "__CPROVER_active_thread_T" + std::to_string(thread);
  symbol_exprt active_thread_expr{active_thread_name, bool_typet{}};

  active_thread active_thread_struct{thread, 1, active_thread_expr};
  active_threads_vector.emplace(thread, active_thread_struct);

  return active_thread_expr;
}

symbol_exprt lazy_pot::create_dr_thread_symbol(unsigned num)
{
  if (dr_thread.find(num) != dr_thread.end())
    return dr_thread.at(num);
  irep_idt thread_name = "t" + std::to_string(num);
  symbol_exprt thread_expr{thread_name, unsignedbv_typet{threads_bits}};

  dr_thread.emplace(num, thread_expr);
  return thread_expr;
}

symbol_exprt lazy_pot::create_dr_round_symbol(unsigned num)
{
  if (dr_round.find(num) != dr_round.end())
    return dr_round.at(num);
  irep_idt round_name = "r" + std::to_string(num);
  symbol_exprt round_expr{round_name, unsignedbv_typet{rounds_bits}};

  dr_round.emplace(num, round_expr);

  return round_expr;
}

symbol_exprt lazy_pot::create_dr_atom_symbol(unsigned num)
{
  if (dr_atom.find(num) != dr_atom.end())
    return dr_atom.at(num);
  irep_idt atom_name = "a" + std::to_string(num);
  symbol_exprt atom_expr{atom_name, bool_typet{}};

  dr_atom.emplace(num, atom_expr);

  return atom_expr;
}

symbol_exprt lazy_pot::create_dr_loc_symbol(unsigned num)
{
  if (dr_loc.find(num) != dr_loc.end())
    return dr_loc.at(num);

  irep_idt loc_name = "loc" + std::to_string(num);
  symbol_exprt loc_expr{loc_name, size_type()};

  dr_loc.emplace(num, loc_expr);

  return loc_expr;
}
void lazy_pot::create_winr_tot_symbol(
  symex_target_equationt &equation)
{
  for(auto global_variable : global_variables)
  {
    if(this->writes.count(global_variable) == 0)
      continue;

    auto sorted_writes = this->writes.at(global_variable);
    std::sort(sorted_writes.begin(), sorted_writes.end(),
      [](const shared_event &a, const shared_event &b) {
        return std::tie(a.thread, a.label, a.num) > std::tie(b.thread, b.label, b.num);
      });
    for(std::size_t round = rounds + 1; round-- > 0; )
    {
      for(const auto &write : sorted_writes)
      {
        create_WINR_symbol(global_variable, write.thread, write.label, write.num, round,equation);
      }
    }
  }
}

void lazy_pot::create_lw_tot_symbol(
  symex_target_equationt &equation) {
  for(auto global_variable : global_variables)
  {
    if(this->reads.count(global_variable) == 0)
      continue;
    // ascending lex (thread, label, num) so LW(prev_of_prev) is cached when needed
    auto sorted_reads = this->reads.at(global_variable);
    std::sort(sorted_reads.begin(), sorted_reads.end(),
      [](const shared_event &a, const shared_event &b) {
        return std::tie(a.thread, a.label, a.num) < std::tie(b.thread, b.label, b.num);
      });
    for(std::size_t round = 0; round <= rounds; ++round){
      for(const auto &read : sorted_reads)
      {
        create_LW_symbol(global_variable,read.thread, read.label,read.num, round, equation);
      }
    }
  }
}

void lazy_pot::create_nrp_tot_symbol(
  symex_target_equationt &equation)
{
  for(auto global_variable : global_variables)
  {
    if(this->reads.count(global_variable) == 0)
      continue;

    auto sorted_reads = this->reads.at(global_variable);
    std::sort(sorted_reads.begin(), sorted_reads.end(),
      [](const shared_event &a, const shared_event &b) {
        return std::tie(a.thread, a.label, a.num) > std::tie(b.thread, b.label, b.num);
      });
    for(std::size_t round = rounds + 1; round-- > 0; )
    {
      for(const auto &read : sorted_reads)
      {
        create_NRP_symbol(global_variable, read.thread, read.label, read.num, round, equation);
      }
    }
  }
}

void lazy_pot::create_low_tot_symbol(
  symex_target_equationt &equation)
{
  for(auto global_variable : global_variables)
  {
    if(this->writes.count(global_variable) == 0)
      continue;
    auto sorted_writes = this->writes.at(global_variable);
    std::sort(sorted_writes.begin(), sorted_writes.end(),
      [](const shared_event &a, const shared_event &b) {
        return std::tie(a.thread, a.label, a.num) < std::tie(b.thread, b.label, b.num);
      });
    for(std::size_t round = 0; round <= rounds; ++round)
    {
      for(const auto &write : sorted_writes)
      {
        create_LOW_symbol(global_variable, write.thread, write.label, write.num, round, equation);
      }
    }
  }
}

/// Data races are not preserved by the read-from equivalence that
/// create_atomic_canonical quotients the schedules by. ABR and ABW are built
/// from read-side witnesses only, so a write that no read observes is
/// invisible to them; two schedules that differ just in the order of two such
/// writes are read-from equivalent, yet one has a race and the other has not.
/// Under --datarace an atomic block holding a conflicting access therefore
/// cannot be pruned on those witnesses alone.
///
/// Only write/write conflicts need the exemption. A read-write pair leaves a
/// read-from edge, which is what ABR and ABW are made of, so those races
/// survive the reduction; a write/write pair leaves no edge at all. Measured:
/// `ww` recovers every reproducer and semaphore-posix-race, and `wide`
/// recovers nothing beyond it.
///
/// LAZYPO_POR_RACE_EXEMPT overrides the rule, for the ablation:
///   ww (default) only write/write, the conflict the witnesses cannot see;
///   wide         any conflicting pair, write/write or read/write;
///   off          nothing, i.e. the behaviour before this fix.
bool lazy_pot::block_can_race(const atomic_block &b) const
{
  static const std::string mode = []() -> std::string {
    const char *e = getenv("LAZYPO_POR_RACE_EXEMPT");
    return e == nullptr ? "ww" : e;
  }();
  if(mode == "off")
    return false;
  const bool ww_only = mode == "ww";

  auto other_thread_accesses =
    [&b](const std::unordered_map<irep_idt, std::vector<shared_event>> &events,
         const irep_idt &object) {
      const auto it = events.find(object);
      if(it == events.end())
        return false;
      for(const auto &e : it->second)
        if(e.thread != b.thread)
          return true;
      return false;
    };

  // A write conflicts with any other-thread access to the same object; a read
  // conflicts only with another thread's write.
  for(const auto &entry : b.writes)
    if(other_thread_accesses(writes, entry.first) ||
       (!ww_only && other_thread_accesses(reads, entry.first)))
      return true;
  if(!ww_only)
    for(const auto &entry : b.reads)
      if(other_thread_accesses(writes, entry.first))
        return true;
  return false;
}

void lazy_pot::create_atomic_canonical(
  symex_target_equationt &equation) {
  for(std::size_t round = 2; round <= rounds; ++round){
    for(const auto &entry : atomic_blocks)
    {
      const atomic_block &b = entry.second;
      if(b.label == 0)
        continue;
      if(b.reads.empty() && b.writes.empty())
        continue;
      // Canonicality is justified by read-from equivalence, which does not
      // preserve data races; see block_can_race.
      if(datarace && block_can_race(b))
        continue;
      const auto &src = !b.reads.empty()
        ? b.reads.begin()->second.front().s_it->source
        : b.writes.begin()->second.front().s_it->source;
      const exprt cs_1 = create_enabled_symbol(b.label, b.thread, round);
      // Was `cs^{r-1} == label`; cs_1 (Enabled) already conjoins
      // !GE(t,r-1,label+1), so only the remaining direction,
      // GE(t,r-1,label), is needed here (see create_cs_constraint's
      // boundary tightening for the same reasoning).
      exprt cs = create_ge_symbol(b.thread, round - 1, b.label);
      exprt fire_cond =
        and_exprt(cs_1, cs, active_at_turn(b.thread, b.label, round - 1));
      exprt abr =
        b.reads.empty()
          ? exprt(false_exprt{})
          : (bv_tags
               ? exprt(create_ABR(b.reads, round, b.label, b.thread, equation))
               : exprt(create_ABR_windows(
                   b.reads, round, b.label, b.thread, equation)));
      exprt abw =
        b.writes.empty()
          ? exprt(false_exprt{})
          : (bv_tags
               ? exprt(create_ABW(b.writes, round, b.label, b.thread, equation))
               : exprt(create_ABW_windows(
                   b.writes, round, b.label, b.thread, equation)));
      if(xcheck_tags)
      {
        // LAZYPO_TAG_XCHECK=1: prova a macchina che l'encoding a finestre
        // definisce esattamente la stessa funzione booleana degli exec di
        // quello bitvector. Si emettono ENTRAMBI i testimoni e si asserisce
        // la loro equivalenza, SENZA emettere il vincolo di canonicalita':
        // cosi' il SAT quantifica su tutti gli schedule dell'encoding base,
        // non solo su quelli gia' potati, e un solo controesempio significa
        // che le due formule differiscono. Solo per validazione: la formula
        // che ne esce non fa POR.
        if(!b.reads.empty())
          xcheck_pairs.emplace_back(
            abr, create_ABR(b.reads, round, b.label, b.thread, equation));
        if(!b.writes.empty())
          xcheck_pairs.emplace_back(
            abw, create_ABW(b.writes, round, b.label, b.thread, equation));
        continue;
      }

      exprt expression = implies_exprt(fire_cond, or_exprt(abr, abw));
      simplify(expression, ns);
      equation.constraint(expression, "atomic_block_canonical", src);
    }
  }
}

symbol_exprt lazy_pot::create_ABR(
  const std::map<irep_idt, std::vector<shared_event>> &reads, std::size_t round,
  unsigned label, unsigned thread,
  symex_target_equationt &equation) {
  // reads is already the per-block map (built by build_atomic_blocks); it's
  // typically far smaller than the full global_variables set, so iterate it
  // directly instead of scanning every shared variable in the program just
  // to test membership.
  exprt result = false_exprt{};
  const symex_targett::sourcet *src = nullptr;
  for(const auto &read_entry : reads){
    const irep_idt &global_variable = read_entry.first;
    for(const auto &rd : read_entry.second)
    {
      if(src == nullptr)
        src = &rd.s_it->source;


      std::optional<lazy_variable> pw =
        get_previous_write(rd.thread, rd.label, rd.num, round, global_variable);
      bool prev_outside =
        !pw.has_value() ||
        pw->round < round ||
        (pw->round == round && pw->thread < rd.thread) ||
        (pw->round == round && pw->thread == rd.thread && pw->label < rd.label);
      if(!prev_outside)
      {
        const auto t_it = guards.find(rd.thread);
        if(t_it != guards.end())
        {
          const auto l_it = t_it->second.find(rd.label);
          if(
            l_it != t_it->second.end() && pw->num < l_it->second.size() &&
            rd.num < l_it->second.size())
          {
            const exprt &guard_w = l_it->second.at(pw->num);
            if(guard_w.is_true() || guard_w == l_it->second.at(rd.num))
              continue;
          }
        }
      }

      exprt exec = create_exec_symbol_fast(rd.label, rd.num, rd.thread, round);

      symbol_exprt lw_r =
        create_LW_symbol(global_variable, rd.thread, rd.label, rd.num, round, equation);
      symbol_exprt lw_r1 =
        create_LW_symbol(global_variable, rd.thread, rd.label, rd.num, round - 1, equation);
      exprt disjunct = and_exprt{exec, notequal_exprt{lw_r, lw_r1}};
      tag_stats().cmp_neq++;
      tag_stats().cmp_neq_bits += bit_writes[global_variable];

      if(!prev_outside)
      {
        disjunct = and_exprt{
          disjunct,
          less_than_exprt{
            lw_r, boundary_id(global_variable, round, rd.thread, rd.label, 0)}};
        tag_stats().cmp_rel++;
        tag_stats().cmp_rel_bits += bit_writes[global_variable];
      }

      result = or_exprt{result, disjunct};
    }
  }
  irep_idt abr_r = "ABR_T" + std::to_string(thread) + "_L" + std::to_string(label) +
     "_R" + std::to_string(round) + (xcheck_tags ? "_BV" : "");
  symbol_exprt sym{abr_r, bool_typet{}};
  register_por_symbol(sym);
  simplify(result, ns);
  equation.constraint(equal_exprt{sym, result}, "abr", *src);
  atomic_block_rounds.push_back({thread, label, static_cast<unsigned>(round), sym});
  return sym;
}
symbol_exprt lazy_pot::create_ABW(
  const std::map<irep_idt, std::vector<shared_event>> &writes, std::size_t round,
  unsigned label, unsigned thread,
  symex_target_equationt &equation)
{
  exprt result = false_exprt{};
  const symex_targett::sourcet *src = nullptr;


  // eq(4) del paper: la guardia di esecuzione sta DENTRO il disgiunto su x e
  // scorre solo le write di quella x, non tutte quelle del blocco. Con la
  // guardia fattorizzata fuori bastava una write di y eseguita per abilitare un
  // testimone WC su x: ma se nessuna write di x del blocco esegue, anticipare
  // il blocco non tocca x, quindi quel testimone e' spurio e teneva in vita
  // schedule ridondanti (sound, ma rompe l'unicita' del canonico del teorema).
  // Sui blocchi che scrivono una sola variabile le due forme coincidono.
  // writes is already the per-block map (built by build_atomic_blocks); see
  // create_ABR for why iterating it directly instead of global_variables is
  // equivalent and avoids an O(|global_variables|) scan per (block, round).
  for(const auto &write_entry : writes){
    const irep_idt &global_variable = write_entry.first;
    const auto &ws = write_entry.second;
    if(src == nullptr)
      src = &ws.front().s_it->source;

    exprt var_guard = false_exprt{};
    for(const auto &write : ws)
      var_guard = or_exprt{
        var_guard,
        create_exec_symbol_fast(write.label, write.num, write.thread, round)};

    exprt id_first_r    = boundary_id(global_variable, round, thread, label, 0);
    exprt id_first_r1   = boundary_id(global_variable, round - 1, thread, label, 0);
    exprt id_first_next = boundary_id(global_variable, round, thread, label + 1, 0);
    exprt id_after_r1   = boundary_id(global_variable, round - 1, thread, label, 1);

    exprt winr_a = create_WINR_symbol(global_variable, thread, label + 1, 0, round - 1, equation);
    exprt lw_b  = create_LW_symbol(global_variable, thread, label, 0, round, equation);
    exprt gap_w = greater_than_or_equal_exprt{lw_b, id_after_r1};

    exprt nrp_a = create_NRP_symbol(global_variable, thread, label + 1, 0, round - 1, equation);
    exprt wc_a = and_exprt{
      less_than_exprt{nrp_a, id_first_r},
      less_than_exprt{winr_a, id_first_r1}};

    exprt low_b = create_LOW_symbol(global_variable, thread, label, 0, round, equation);
    exprt winr_b = create_WINR_symbol(global_variable, thread, label + 1, 0, round, equation);
    exprt b_src = and_exprt{
      greater_than_or_equal_exprt{winr_b, id_first_r},
      less_than_exprt{winr_b, id_first_next}};
    exprt gap_obs_w = greater_than_or_equal_exprt{low_b, id_after_r1};
    exprt wc_b = and_exprt{gap_w, or_exprt{b_src, gap_obs_w}};

    // 6 confronti relazionali per (blocco, round, variabile): gap_w, wc_a x2,
    // b_src x2, gap_obs_w.
    tag_stats().cmp_rel += 6;
    tag_stats().cmp_rel_bits += 6 * bit_writes[global_variable];

    result = or_exprt{result, and_exprt{var_guard, or_exprt{wc_a, wc_b}}};
  }
  irep_idt abw_r = "ABW_T" + std::to_string(thread) + "_L" + std::to_string(label) +
     "_R" + std::to_string(round) + (xcheck_tags ? "_BV" : "");
  symbol_exprt sym{abw_r, bool_typet{}};
  register_por_symbol(sym);
  simplify(result, ns);
  equation.constraint(equal_exprt{sym, result}, "abw", *src);
  atomic_block_rounds.push_back({thread, label, static_cast<unsigned>(round), sym});
  return sym;
}

void lazy_pot::build_atomic_blocks(){
  for(const auto &entry : reads)
  {
    const irep_idt &var = entry.first;
    for(const auto &rd : entry.second)
    {
      auto &b = atomic_blocks[{rd.thread, rd.label}];
      b.thread = rd.thread;
      b.label = rd.label;
      b.reads[var].push_back(rd);
    }
  }
  for(const auto &entry : writes)
  {
    const irep_idt &var = entry.first;
    for(const auto &wr : entry.second)
    {
      auto &b = atomic_blocks[{wr.thread, wr.label}];
      b.thread = wr.thread;
      b.label = wr.label;
      b.writes[var].push_back(wr);
    }
  }
}


// ===========================================================================
// Window encoding of the canonicality tags.
// ===========================================================================
//
// WHY. LW/WINR/NRP/LOW are `unsignedbv_typet(bit_writes[x])` values built by
// nested if_exprt chains, and every use of them in create_ABR/create_ABW is a
// comparison against a *constant* boundary id (or, in one case, against the
// same tag one round earlier). With bit_writes[x] = ceil(log2(#accesses to x
// over all rounds)) that is 7-12 bits on the benchmarks, so each chain node
// costs a w-bit mux and each use a w-bit ripple comparator. Measured on
// elimination_backoff_stack --rounds 8: the tag symbols alone are 1.77M of
// the 3.19M SAT variables --por adds over the plain encoding, and forcing all
// tag widths to 2 and 4 bits shows 92% of the variable overhead and 94% of
// the clause overhead is linear in w. It is bit-blasted arithmetic, and none
// of the arithmetic is actually needed.
//
// WHAT. Fix a shared variable x. enumerate_accesses() gives every access of x
// (writes from lazy_variables -- including the round-0 sentinel -- and reads
// from lazy_variables_read) a distinct id 0..n-1, strictly increasing in the
// lex order of (round, thread, label, num); validate_access_order() enforces
// exactly that. Write idx(p) for the id of the first access at or after
// position p (n if there is none) -- i.e. boundary_id, as an index. Then,
// directly from the chain definitions:
//
//   LW(p)   = max{ id(w) : w write, id(w) < idx(p), exec(w) } u {0}
//   LOW(p)  = max{ id(w) : w write, id(w) < idx(p), exec(w) & OBS(w) } u {0}
//   NRP(p)  = min{ id(r) : r read,  id(r) >= idx(p), exec(r) } u {BOT}
//   WINR(p) = LW(q), q = argmin{ id(r) : r read, id(r) >= idx(p), exec(r) },
//             BOT if no such q
//
// (the round-0 write sentinel has id 0, never executes, and every real access
// has id >= 1, so "max over the empty set = 0" is faithful; BOT = 2^w-1 is
// above every real id, which create_atomic_canonical's caller guards.)
//
// Introduce the boolean primitives
//
//   W[a,b)  = OR{ exec(w)          : w write, a <= id(w) < b }
//   R[a,b)  = OR{ exec(r)          : r read,  a <= id(r) < b }
//   OW[a,b) = OR{ OBS(w)           : w write, a <= id(w) < b }
//   FR(k)   = "the first executed access with id >= k is a read"
//             FR(n) = false; FR(k) = exec(a_k) ? is_read(a_k) : FR(k+1)
//
// and every comparison the canonicality clauses make becomes:
//
//  (E1) LW(p) >= c   <=>  W[c, idx(p))                      (c >= 1)
//  (E2) LOW(p) >= c  <=>  OW[c, idx(p))                     (c >= 1)
//  (E3) NRP(p) < c   <=>  R[idx(p), c)
//  (E4) c <= WINR(p) < idx(p)  <=>  FR(idx(p)) & W[c, idx(p))      (c<=idx(p))
//  (E5) WINR(p) < c  <=>  FR(idx(p)) & !W[c, idx(p))        (1 <= c <= idx(p))
//  (E6) OBS(w) = [WINR(p_w) = id(w)], p_w = (w.round,w.thread,w.label+1,0)
//               <=>  exec(w) & !W[id(w)+1, idx(p_w)) & FR(idx(p_w))
//  (E7) LW at (r,t,l,n) != LW at (r-1,t,l,n)
//               <=>  W[ idx(r-1,t,l,n), idx(r,t,l,n) )
//
// WHY THOSE ARE EQUIVALENCES, NOT APPROXIMATIONS.
//
// (E1)/(E2)/(E3) are immediate from the max/min characterisations: a max over
// a set of ids reaches c iff some member is >= c; a min goes below c iff some
// member is < c. Ids increase with position, so "id(w) < idx(p)" is exactly
// "pos(w) < p", which is what get_previous_write cuts on, and "id(r) >=
// idx(p)" is exactly what get_next_read cuts on. The c >= 1 side condition
// matters only because the sentinel occupies id 0 and never executes; every
// threshold the code actually passes is a boundary id at a round >= 1
// position, hence >= 1 (asserted below).
//
// (E4)/(E5). Let m = idx(p). If no read with id >= m executes then WINR = BOT,
// so "WINR < anything real" is false; and FR(m) is false too (nothing executes
// after m, or the first thing that does is a write), so both sides agree. Else
// let q be the first executed read with id >= m, WINR = LW(q) = max over
// executed writes with id < id(q).
//   * WINR < m  <=>  no executed write in [m, id(q)). Conjoined with "q is the
//     first executed *read* at or after m", that says no executed access in
//     [m, id(q)) at all and a_{id(q)} is a read -- which is precisely FR(m).
//   * given that, WINR >= c for c <= m  <=>  some executed write in [c, id(q))
//     <=>  some executed write in [c, m)  =  W[c,m).  (E4)
//   * and WINR < c for c <= m  <=>  no executed write in [c, id(q))
//     <=>  !W[c,m) & (no executed write in [m,id(q))), the second conjunct
//     being folded into FR(m).  (E5)
//   Both uses in create_ABW have c <= m by construction: the WINR anchor is
//   always the block boundary (.., label+1, 0) and the threshold a boundary
//   at (.., label, 0) of the same or an earlier round, and idx is monotone in
//   the position. Asserted below.
//
// (E6) is (E4)/(E5) specialised to an equality: WINR(p_w) = id(w) iff w is
// the last executed write before q, i.e. exec(w) and no executed write in
// (id(w), id(q)) = (id(w), idx(p_w)) u [idx(p_w), id(q)); the first half is
// !W[id(w)+1, idx(p_w)), the second is absorbed into FR(idx(p_w)) exactly as
// above. id(w) < idx(p_w) because w sits in block label and p_w is the start
// of label+1 in the same round.
//
// (E7) LW is monotone along positions (a max over a growing prefix) and ids
// follow the position order, so the two tags differ iff some write in the
// window between the two positions executed: if one did, its id exceeds every
// write id before the earlier position, so the later max strictly grows; if
// none did, the two maxima range over the same executed set.
//
// COST. The windows are contiguous id ranges, so they are materialised by a
// balanced range-OR tree over the (compacted) write/read list of x: O(n)
// shared boolean nodes per variable and kind, O(log n) literals per query,
// against O(n*w) bits plus a w-bit comparator per query before. FR is one
// boolean chain of length n per variable, shared by every query. Nothing here
// is an over- or under-approximation, so the canonicality theorem's argument
// carries over verbatim: create_ABR/create_ABW define the same boolean
// functions of the exec variables as before.
//
// LAZYPO_TAG_BV=1 restores the bitvector path for A/B comparison.

lazy_pot::tag_windowt &lazy_pot::tag_data(irep_idt variable)
{
  tag_windowt &d = tag_windows[variable];
  if(d.init)
    return d;
  d.init = true;

  const auto w_it = lazy_variables.find(variable);
  if(w_it != lazy_variables.end())
    for(const auto &lv : w_it->second)
    {
      d.write_ids.push_back(lv.id);
      // il sentinella di round 0 non ha un exec: non esegue mai.
      d.write_exec.push_back(
        lv.round == 0
          ? exprt(false_exprt{})
          : exprt(create_exec_symbol_fast(lv.label, lv.num, lv.thread, lv.round)));
    }

  const auto r_it = lazy_variables_read.find(variable);
  if(r_it != lazy_variables_read.end())
    for(const auto &lv : r_it->second)
    {
      d.read_ids.push_back(lv.id);
      d.read_exec.push_back(
        create_exec_symbol_fast(lv.label, lv.num, lv.thread, lv.round));
    }

  d.n = d.write_ids.size() + d.read_ids.size();

  // Le due liste sono gia' ordinate per posizione (create_write_constraints /
  // create_lazy_variable_read ordinano, validate_access_order lo verifica) e
  // enumerate_accesses assegna gli id nell'ordine lex unificato: quindi gli id
  // sono crescenti in ciascuna lista e la loro unione e' esattamente 0..n-1.
  // Le ricerche binarie sotto e la catena FR dipendono da entrambe le cose.
  for(std::size_t i = 1; i < d.write_ids.size(); ++i)
    DATA_INVARIANT(
      d.write_ids[i - 1] < d.write_ids[i], "lazy_po: write ids must ascend");
  for(std::size_t i = 1; i < d.read_ids.size(); ++i)
    DATA_INVARIANT(
      d.read_ids[i - 1] < d.read_ids[i], "lazy_po: read ids must ascend");
  return d;
}

std::size_t lazy_pot::boundary_index(
  irep_idt variable, std::size_t round, unsigned thread, unsigned label,
  unsigned num)
{
  const std::size_t n = tag_data(variable).n;
  std::size_t best = n;
  const auto qk = std::make_tuple(round, thread, label, num);
  const auto w_it = lazy_variables.find(variable);
  if(w_it != lazy_variables.end())
  {
    const auto &v = w_it->second;
    const auto it = std::lower_bound(
      v.begin(), v.end(), qk,
      [](const lazy_variable &lv,
         const std::tuple<std::size_t, unsigned, unsigned, unsigned> &k) {
        return std::make_tuple(lv.round, lv.thread, lv.label, lv.num) < k;
      });
    if(it != v.end() && it->id < best)
      best = it->id;
  }
  const auto r_it = lazy_variables_read.find(variable);
  if(r_it != lazy_variables_read.end())
  {
    const auto &v = r_it->second;
    const auto it = std::lower_bound(
      v.begin(), v.end(), qk,
      [](const lazy_variable_read &lv,
         const std::tuple<std::size_t, unsigned, unsigned, unsigned> &k) {
        return std::make_tuple(lv.round, lv.thread, lv.label, lv.num) < k;
      });
    if(it != v.end() && it->id < best)
      best = it->id;
  }
  return best;
}

exprt lazy_pot::range_node(
  irep_idt variable, unsigned kind, std::size_t a, std::size_t b,
  symex_target_equationt &equation)
{
  {
    tag_windowt &d = tag_data(variable);
    if(b - a == 1)
      return kind == 0 ? d.write_exec[a]
                       : (kind == 1 ? d.read_exec[a] : d.obs[a]);
    const uint64_t key = (uint64_t(a) << 32) | uint64_t(b);
    const auto it = d.nodes[kind].find(key);
    if(it != d.nodes[kind].end())
      return it->second;
  }

  const std::size_t mid = a + (b - a) / 2;
  exprt e = or_exprt{range_node(variable, kind, a, mid, equation),
                     range_node(variable, kind, mid, b, equation)};
  simplify(e, ns);

  exprt result = e;
  // Un nodo che si semplifica in una costante o in un singolo letterale non
  // merita un simbolo: lo si propaga com'e' e si risparmiano var e clausole.
  if(!e.is_constant() && e.id() != ID_symbol)
  {
    irep_idt name = "RNG_K" + std::to_string(kind) + "_A" + std::to_string(a) +
                    "_B" + std::to_string(b) + "_V" + id2string(variable);
    symbol_exprt sym{name, bool_typet{}};
    register_por_symbol(sym);
    equation.constraint(
      equal_exprt{sym, e}, "por range", equation.SSA_steps.begin()->source);
    tag_stats().range_nodes++;
    result = sym;
  }
  tag_data(variable).nodes[kind].emplace((uint64_t(a) << 32) | uint64_t(b), result);
  return result;
}

exprt lazy_pot::range_query(
  irep_idt variable, unsigned kind, std::size_t a, std::size_t b,
  std::size_t lo, std::size_t hi, symex_target_equationt &equation)
{
  if(hi <= a || b <= lo)
    return false_exprt{};
  if(lo <= a && b <= hi)
    return range_node(variable, kind, a, b, equation);
  const std::size_t mid = a + (b - a) / 2;
  return or_exprt{range_query(variable, kind, a, mid, lo, hi, equation),
                  range_query(variable, kind, mid, b, lo, hi, equation)};
}

exprt lazy_pot::window_exec(
  irep_idt variable, unsigned kind, std::size_t id_lo, std::size_t id_hi,
  symex_target_equationt &equation)
{
  if(id_hi <= id_lo)
    return false_exprt{};
  if(kind == 2)
    build_obs_literals(variable, equation);

  tag_windowt &d = tag_data(variable);
  const std::vector<unsigned> &ids = (kind == 1) ? d.read_ids : d.write_ids;
  if(ids.empty())
    return false_exprt{};

  const std::size_t lo = static_cast<std::size_t>(
    std::lower_bound(ids.begin(), ids.end(), id_lo) - ids.begin());
  const std::size_t hi = static_cast<std::size_t>(
    std::lower_bound(ids.begin(), ids.end(), id_hi) - ids.begin());
  if(hi <= lo)
    return false_exprt{};

  exprt e = range_query(variable, kind, 0, ids.size(), lo, hi, equation);
  simplify(e, ns);
  tag_stats().window_queries++;
  return e;
}

void lazy_pot::build_first_read_chain(
  irep_idt variable, symex_target_equationt &equation)
{
  if(tag_data(variable).fr_built)
    return;
  tag_windows[variable].fr_built = true;

  const std::size_t n = tag_data(variable).n;
  std::vector<char> is_read(n, 0);
  std::vector<exprt> ex(n, exprt(false_exprt{}));
  {
    const tag_windowt &d = tag_data(variable);
    for(std::size_t i = 0; i < d.write_ids.size(); ++i)
      ex[d.write_ids[i]] = d.write_exec[i];
    for(std::size_t i = 0; i < d.read_ids.size(); ++i)
    {
      ex[d.read_ids[i]] = d.read_exec[i];
      is_read[d.read_ids[i]] = 1;
    }
  }

  std::vector<exprt> fr(n + 1, exprt(false_exprt{}));
  const auto &src = equation.SSA_steps.begin()->source;
  for(std::size_t k = n; k-- > 0;)
  {
    // FR(k) = exec(a_k) ? is_read(a_k) : FR(k+1)
    exprt e = is_read[k] ? exprt(or_exprt{ex[k], fr[k + 1]})
                         : exprt(and_exprt{not_exprt{ex[k]}, fr[k + 1]});
    simplify(e, ns);
    if(!e.is_constant() && e.id() != ID_symbol)
    {
      irep_idt name =
        "FRD_I" + std::to_string(k) + "_V" + id2string(variable);
      symbol_exprt sym{name, bool_typet{}};
      register_por_symbol(sym);
      equation.constraint(equal_exprt{sym, e}, "por first-read", src);
      tag_stats().fr_nodes++;
      e = sym;
    }
    fr[k] = e;
  }
  tag_windows[variable].fr = std::move(fr);
}

exprt lazy_pot::first_read_atom(
  irep_idt variable, std::size_t k, symex_target_equationt &equation)
{
  build_first_read_chain(variable, equation);
  const tag_windowt &d = tag_data(variable);
  PRECONDITION(k <= d.n);
  return d.fr[k];
}

void lazy_pot::build_obs_literals(
  irep_idt variable, symex_target_equationt &equation)
{
  if(tag_data(variable).obs_built)
    return;
  tag_windows[variable].obs_built = true;
  build_first_read_chain(variable, equation);

  const auto &src = equation.SSA_steps.begin()->source;
  std::vector<exprt> obs;
  const auto w_it = lazy_variables.find(variable);
  if(w_it != lazy_variables.end())
  {
    // copia: window_exec puo' inserire nodi in tag_windows[variable]
    const std::vector<lazy_variable> ws = w_it->second;
    for(const auto &w : ws)
    {
      if(w.round == 0)
      {
        obs.push_back(false_exprt{});
        continue;
      }
      const std::size_t m =
        boundary_index(variable, w.round, w.thread, w.label + 1, 0);
      DATA_INVARIANT(
        std::size_t(w.id) < m,
        "lazy_po: OBS anchor must sit after its own write");
      exprt e = and_exprt{
        create_exec_symbol_fast(w.label, w.num, w.thread, w.round),
        not_exprt{window_exec(variable, 0, std::size_t(w.id) + 1, m, equation)},
        first_read_atom(variable, m, equation)};
      simplify(e, ns);
      irep_idt obs_id = "OBS_T" + std::to_string(w.thread) + "_L" +
                        std::to_string(w.label) + "_N" + std::to_string(w.num) +
                        "_R" + std::to_string(w.round) + "_V" +
                        id2string(variable);
      symbol_exprt sym{obs_id, bool_typet{}};
      register_por_symbol(sym);
      equation.constraint(equal_exprt{sym, e}, "obs canonical", src);
      tag_stats().obs++;
      obs.push_back(sym);
    }
  }
  tag_windows[variable].obs = std::move(obs);
}

symbol_exprt lazy_pot::create_ABR_windows(
  const std::map<irep_idt, std::vector<shared_event>> &reads, std::size_t round,
  unsigned label, unsigned thread, symex_target_equationt &equation)
{
  exprt result = false_exprt{};
  const symex_targett::sourcet *src = nullptr;
  for(const auto &read_entry : reads)
  {
    const irep_idt &x = read_entry.first;
    for(const auto &rd : read_entry.second)
    {
      if(src == nullptr)
        src = &rd.s_it->source;

      std::optional<lazy_variable> pw =
        get_previous_write(rd.thread, rd.label, rd.num, round, x);
      bool prev_outside =
        !pw.has_value() || pw->round < round ||
        (pw->round == round && pw->thread < rd.thread) ||
        (pw->round == round && pw->thread == rd.thread && pw->label < rd.label);
      if(!prev_outside)
      {
        const auto t_it = guards.find(rd.thread);
        if(t_it != guards.end())
        {
          const auto l_it = t_it->second.find(rd.label);
          if(
            l_it != t_it->second.end() && pw->num < l_it->second.size() &&
            rd.num < l_it->second.size())
          {
            const exprt &guard_w = l_it->second.at(pw->num);
            if(guard_w.is_true() || guard_w == l_it->second.at(rd.num))
              continue;
          }
        }
      }

      exprt exec = create_exec_symbol_fast(rd.label, rd.num, rd.thread, round);

      // LW^r != LW^{r-1}  ==  (E7)
      const std::size_t m_r =
        boundary_index(x, round, rd.thread, rd.label, rd.num);
      const std::size_t m_r1 =
        boundary_index(x, round - 1, rd.thread, rd.label, rd.num);
      DATA_INVARIANT(m_r1 <= m_r, "lazy_po: boundary index must be monotone");
      exprt disjunct =
        and_exprt{exec, window_exec(x, 0, m_r1, m_r, equation)};

      if(!prev_outside)
      {
        // LW^r < boundary(round, thread, label, 0)  ==  (E1) negated
        const std::size_t c = boundary_index(x, round, rd.thread, rd.label, 0);
        DATA_INVARIANT(c >= 1, "lazy_po: window threshold must skip id 0");
        disjunct = and_exprt{
          disjunct, not_exprt{window_exec(x, 0, c, m_r, equation)}};
      }

      result = or_exprt{result, disjunct};
    }
  }
  irep_idt abr_r = "ABR_T" + std::to_string(thread) + "_L" +
                   std::to_string(label) + "_R" + std::to_string(round);
  symbol_exprt sym{abr_r, bool_typet{}};
  register_por_symbol(sym);
  simplify(result, ns);
  equation.constraint(equal_exprt{sym, result}, "abr", *src);
  atomic_block_rounds.push_back({thread, label, static_cast<unsigned>(round), sym});
  return sym;
}

symbol_exprt lazy_pot::create_ABW_windows(
  const std::map<irep_idt, std::vector<shared_event>> &writes,
  std::size_t round, unsigned label, unsigned thread,
  symex_target_equationt &equation)
{
  exprt result = false_exprt{};
  const symex_targett::sourcet *src = nullptr;

  for(const auto &write_entry : writes)
  {
    const irep_idt &x = write_entry.first;
    const auto &ws = write_entry.second;
    if(src == nullptr)
      src = &ws.front().s_it->source;

    exprt var_guard = false_exprt{};
    for(const auto &write : ws)
      var_guard = or_exprt{
        var_guard,
        create_exec_symbol_fast(write.label, write.num, write.thread, round)};

    // stessi quattro confini di create_ABW, in spazio indice
    const std::size_t m_r = boundary_index(x, round, thread, label, 0);
    const std::size_t m_r1 = boundary_index(x, round - 1, thread, label, 0);
    const std::size_t m_nx = boundary_index(x, round, thread, label + 1, 0);
    const std::size_t m_a1 = boundary_index(x, round - 1, thread, label, 1);
    // ancore di WINR/NRP: (round-1, t, label+1, 0) e (round, t, label+1, 0)
    const std::size_t p_a = boundary_index(x, round - 1, thread, label + 1, 0);

    // Le condizioni laterali di (E1)/(E2)/(E5): le soglie sono confini di
    // posizioni con round >= 1, quindi saltano il sentinella id 0, e l'ancora
    // di WINR non precede mai la soglia.
    DATA_INVARIANT(
      m_a1 >= 1 && m_r1 >= 1, "lazy_po: window threshold must skip id 0");
    DATA_INVARIANT(
      m_r1 <= p_a && m_r <= m_nx,
      "lazy_po: WINR threshold must not follow its anchor");

    exprt gap_w = window_exec(x, 0, m_a1, m_r, equation);        // (E1)
    exprt nrp_lt = window_exec(x, 1, p_a, m_r, equation);        // (E3)
    exprt winr_a_lt = and_exprt{                                  // (E5)
      first_read_atom(x, p_a, equation),
      not_exprt{window_exec(x, 0, m_r1, p_a, equation)}};
    exprt wc_a = and_exprt{nrp_lt, winr_a_lt};

    exprt b_src = and_exprt{                                      // (E4)
      first_read_atom(x, m_nx, equation),
      window_exec(x, 0, m_r, m_nx, equation)};
    exprt gap_obs_w = window_exec(x, 2, m_a1, m_r, equation);     // (E2)
    exprt wc_b = and_exprt{gap_w, or_exprt{b_src, gap_obs_w}};

    result = or_exprt{result, and_exprt{var_guard, or_exprt{wc_a, wc_b}}};
  }

  irep_idt abw_r = "ABW_T" + std::to_string(thread) + "_L" +
                   std::to_string(label) + "_R" + std::to_string(round);
  symbol_exprt sym{abw_r, bool_typet{}};
  register_por_symbol(sym);
  simplify(result, ns);
  equation.constraint(equal_exprt{sym, result}, "abw", *src);
  atomic_block_rounds.push_back({thread, label, static_cast<unsigned>(round), sym});
  return sym;
}

symbol_exprt lazy_pot::create_LW_symbol(irep_idt variable, unsigned thread, unsigned label, unsigned num,size_t round,
  symex_target_equationt &equation)
{
  const unsignedbv_typet type(bit_writes[variable]);
  const auto &src = equation.SSA_steps.begin()->source;
  std::optional<lazy_variable> prev_op = get_previous_write(thread, label, num, round, variable);

  auto &memo = lw_variables[variable];

  auto emit = [&](unsigned t, unsigned l, unsigned n, size_t r, const exprt &rhs) {
    const uint64_t key = chain_key(r, t, l, n);
    auto m_it = memo.find(key);
    if(m_it != memo.end())
      return m_it->second;
    irep_idt lw_id = "LW_T" + std::to_string(t) + "_L" + std::to_string(l) +
      "_N" + std::to_string(n) + "_R" + std::to_string(r) + "_V" + id2string(variable);
    symbol_exprt sym{lw_id, type};
    register_por_symbol(sym);
    tag_stats().lw++;
    tag_stats().lw_bits += type.get_width();
    exprt rhs_s = rhs;
    simplify(rhs_s, ns);
    equation.constraint(equal_exprt{sym, rhs_s}, "lw canonical", src);
    memo.emplace(key, sym);
    return sym;
  };

  if(!prev_op.has_value())
    return emit(0, 0, 0, 0, from_integer(0, type));

  const lazy_variable &prev = *prev_op;

  {
    auto m_it = memo.find(chain_key(prev.round, prev.thread, prev.label, prev.num));
    if(m_it != memo.end())
      return m_it->second;
  }

  if(prev.round == 0)
    return emit(prev.thread, prev.label, prev.num, 0, from_integer(0, type));

  symbol_exprt exec = create_exec_symbol_fast(prev.label, prev.num, prev.thread, prev.round);
  std::optional<lazy_variable> prev_op_ = get_previous_write(prev.thread, prev.label, prev.num, prev.round, variable);
  exprt inner_lw_expr = from_integer(0, type);
  if(prev_op_.has_value()) {
    const lazy_variable &prev_value = *prev_op_;
    auto m_it = memo.find(chain_key(prev_value.round, prev_value.thread, prev_value.label, prev_value.num));
    if(m_it != memo.end())
      inner_lw_expr = m_it->second;
    else
      inner_lw_expr = create_LW_symbol(variable, prev.thread, prev.label, prev.num, prev.round, equation);
  }
  return emit(prev.thread, prev.label, prev.num, prev.round,
    if_exprt{exec, from_integer(prev.id, type), inner_lw_expr});
}

symbol_exprt lazy_pot::create_WINR_symbol(irep_idt variable, unsigned thread, unsigned label, unsigned num, size_t round, symex_target_equationt &equation)
{
  const unsignedbv_typet type(bit_writes[variable]);
  const auto &src = equation.SSA_steps.begin()->source;
  std::optional<lazy_variable_read> next_op = get_next_read(thread, label, num, round, variable);

  auto &memo = winr_variables[variable];

  auto emit = [&](unsigned t, unsigned l, unsigned n, size_t r, const exprt &rhs) {
    const uint64_t key = chain_key(r, t, l, n);
    auto m_it = memo.find(key);
    if(m_it != memo.end())
      return m_it->second;
    irep_idt winr_id = "WINR_T" + std::to_string(t) + "_L" + std::to_string(l) +
      "_N" + std::to_string(n) + "_R" + std::to_string(r) + "_V" + id2string(variable);
    symbol_exprt sym{winr_id, type};
    register_por_symbol(sym);
    tag_stats().winr++;
    tag_stats().winr_bits += type.get_width();
    exprt rhs_s = rhs;
    simplify(rhs_s, ns);
    equation.constraint(equal_exprt{sym, rhs_s}, "winr canonical", src);
    memo.emplace(key, sym);
    return sym;
  };

  if(!next_op.has_value()) {
    unsigned max_val = 0;
    for(const auto &[k, v] : labels)
      if(v > max_val) max_val = v;
    return emit(threads, max_val, 0, rounds,
      from_integer((1ULL << bit_writes[variable]) - 1, unsignedbv_typet(bit_writes[variable])));
  }

  const lazy_variable_read &next = *next_op;

  {
    auto m_it = memo.find(chain_key(next.round, next.thread, next.label, next.num));
    if(m_it != memo.end())
      return m_it->second;
  }
  std::optional<lazy_variable_read> next_op_ =
    get_next_read(next.thread, next.label, next.num, next.round, variable, true);

  symbol_exprt exec = create_exec_symbol_fast(next.label, next.num, next.thread, next.round);
  symbol_exprt lw   = create_LW_symbol(variable, next.thread, next.label, next.num, next.round, equation);

  exprt inner_winr_expr =
    from_integer((1ULL << bit_writes[variable]) - 1, unsignedbv_typet(bit_writes[variable]));

  if(next_op_.has_value()) {
    const lazy_variable_read &next_value = *next_op_;
    auto m_it = memo.find(chain_key(next_value.round, next_value.thread, next_value.label, next_value.num));
    if(m_it != memo.end())
      inner_winr_expr = m_it->second;
    else
      inner_winr_expr = create_WINR_symbol(
        variable, next_value.thread, next_value.label, next_value.num, next_value.round, equation);
  }

  return emit(next.thread, next.label, next.num, next.round,
              if_exprt{exec, lw, inner_winr_expr});
}

symbol_exprt lazy_pot::create_NRP_symbol(irep_idt variable, unsigned thread, unsigned label, unsigned num, size_t round, symex_target_equationt &equation)
{
  const unsignedbv_typet type(bit_reads[variable]);
  const auto &src = equation.SSA_steps.begin()->source;
  std::optional<lazy_variable_read> next_op = get_next_read(thread, label, num, round, variable);

  auto &memo = nrp_variables[variable];

  auto emit = [&](unsigned t, unsigned l, unsigned n, size_t r, const exprt &rhs) {
    const uint64_t key = chain_key(r, t, l, n);
    auto m_it = memo.find(key);
    if(m_it != memo.end())
      return m_it->second;
    irep_idt nrp_id = "NRP_T" + std::to_string(t) + "_L" + std::to_string(l) +
      "_N" + std::to_string(n) + "_R" + std::to_string(r) + "_V" + id2string(variable);
    symbol_exprt sym{nrp_id, type};
    register_por_symbol(sym);
    tag_stats().nrp++;
    tag_stats().nrp_bits += type.get_width();
    exprt rhs_s = rhs;
    simplify(rhs_s, ns);
    equation.constraint(equal_exprt{sym, rhs_s}, "nrp canonical", src);
    memo.emplace(key, sym);
    return sym;
  };

  if(!next_op.has_value()) {
    unsigned max_val = 0;
    for(const auto &[k, v] : labels)
      if(v > max_val) max_val = v;
    return emit(threads, max_val, 0, rounds,
      from_integer((1ULL << bit_reads[variable]) - 1, type));
  }

  const lazy_variable_read &next = *next_op;

  {
    auto m_it = memo.find(chain_key(next.round, next.thread, next.label, next.num));
    if(m_it != memo.end())
      return m_it->second;
  }
  std::optional<lazy_variable_read> next_op_ =
    get_next_read(next.thread, next.label, next.num, next.round, variable, true);

  symbol_exprt exec = create_exec_symbol_fast(next.label, next.num, next.thread, next.round);

  exprt inner_nrp_expr =
    from_integer((1ULL << bit_reads[variable]) - 1, type);

  if(next_op_.has_value()) {
    const lazy_variable_read &next_value = *next_op_;
    auto m_it = memo.find(chain_key(next_value.round, next_value.thread, next_value.label, next_value.num));
    if(m_it != memo.end())
      inner_nrp_expr = m_it->second;
    else
      inner_nrp_expr = create_NRP_symbol(
        variable, next_value.thread, next_value.label, next_value.num, next_value.round, equation);
  }

  return emit(next.thread, next.label, next.num, next.round,
              if_exprt{exec, from_integer(next.id, type), inner_nrp_expr});
}

symbol_exprt lazy_pot::create_OBS_symbol(irep_idt variable, const lazy_variable &w, symex_target_equationt &equation)
{
  auto &memo = obs_variables[variable];
  const uint64_t key = chain_key(w.round, w.thread, w.label, w.num);
  {
    auto m_it = memo.find(key);
    if(m_it != memo.end())
      return m_it->second;
  }

  const unsignedbv_typet type(bit_writes[variable]);
  const auto &src = equation.SSA_steps.begin()->source;

  exprt winr_anchor = create_WINR_symbol(
    variable, w.thread, w.label + 1, 0, w.round, equation);
  exprt result = equal_exprt{winr_anchor, from_integer(w.id, type)};

  // Sotto LAZYPO_TAG_XCHECK i due encoding convivono e build_obs_literals
  // battezza i suoi OBS allo stesso modo: due equazioni di definizione sullo
  // stesso nome renderebbero il confronto vacuo (la formula diventerebbe
  // insoddisfacibile invece di esibire la differenza).
  irep_idt obs_id = "OBS_T" + std::to_string(w.thread) + "_L" + std::to_string(w.label) +
    "_N" + std::to_string(w.num) + "_R" + std::to_string(w.round) + "_V" + id2string(variable) +
    (xcheck_tags ? "_BV" : "");
  symbol_exprt sym{obs_id, bool_typet{}};
  register_por_symbol(sym);
  tag_stats().obs++;
  tag_stats().cmp_eq++;
  tag_stats().cmp_eq_bits += type.get_width();
  equation.constraint(equal_exprt{sym, result}, "obs canonical", src);
  memo.emplace(key, sym);
  return sym;
}

symbol_exprt lazy_pot::create_LOW_symbol(irep_idt variable, unsigned thread, unsigned label, unsigned num, size_t round,
  symex_target_equationt &equation)
{
  const unsignedbv_typet type(bit_writes[variable]);
  const auto &src = equation.SSA_steps.begin()->source;
  std::optional<lazy_variable> prev_op = get_previous_write(thread, label, num, round, variable);

  auto &memo = low_variables[variable];

  auto emit = [&](unsigned t, unsigned l, unsigned n, size_t r, const exprt &rhs) {
    const uint64_t key = chain_key(r, t, l, n);
    auto m_it = memo.find(key);
    if(m_it != memo.end())
      return m_it->second;
    irep_idt low_id = "LOW_T" + std::to_string(t) + "_L" + std::to_string(l) +
      "_N" + std::to_string(n) + "_R" + std::to_string(r) + "_V" + id2string(variable);
    symbol_exprt sym{low_id, type};
    register_por_symbol(sym);
    tag_stats().low++;
    tag_stats().low_bits += type.get_width();
    exprt rhs_s = rhs;
    simplify(rhs_s, ns);
    equation.constraint(equal_exprt{sym, rhs_s}, "low canonical", src);
    memo.emplace(key, sym);
    return sym;
  };

  if(!prev_op.has_value())
    return emit(0, 0, 0, 0, from_integer(0, type));

  const lazy_variable &prev = *prev_op;

  {
    auto m_it = memo.find(chain_key(prev.round, prev.thread, prev.label, prev.num));
    if(m_it != memo.end())
      return m_it->second;
  }

  if(prev.round == 0)
    return emit(prev.thread, prev.label, prev.num, 0, from_integer(0, type));

  symbol_exprt exec = create_exec_symbol_fast(prev.label, prev.num, prev.thread, prev.round);
  exprt obs = create_OBS_symbol(variable, prev, equation);
  std::optional<lazy_variable> prev_op_ = get_previous_write(prev.thread, prev.label, prev.num, prev.round, variable);
  exprt inner_low_expr = from_integer(0, type);
  if(prev_op_.has_value()) {
    const lazy_variable &prev_value = *prev_op_;
    auto m_it = memo.find(chain_key(prev_value.round, prev_value.thread, prev_value.label, prev_value.num));
    if(m_it != memo.end())
      inner_low_expr = m_it->second;
    else
      inner_low_expr = create_LOW_symbol(variable, prev.thread, prev.label, prev.num, prev.round, equation);
  }
  return emit(prev.thread, prev.label, prev.num, prev.round,
    if_exprt{and_exprt{exec, obs}, from_integer(prev.id, type), inner_low_expr});
}

exprt lazy_pot::boundary_id(irep_idt variable, std::size_t round, unsigned thread, unsigned label, unsigned num)
{
  const unsignedbv_typet type(bit_writes[variable]);
  unsigned best = static_cast<unsigned>((1ULL << bit_writes[variable]) - 1);
  const auto qk = std::make_tuple(round, thread, label, num);
  const auto w_it = lazy_variables.find(variable);
  if(w_it != lazy_variables.end())
  {
    const auto &v = w_it->second;
    const auto it = std::lower_bound(
      v.begin(), v.end(), qk,
      [](const lazy_variable &lv, const std::tuple<std::size_t, unsigned, unsigned, unsigned> &k) {
        return std::make_tuple(lv.round, lv.thread, lv.label, lv.num) < k;
      });
    if(it != v.end() && it->id < best)
      best = it->id;
  }
  const auto r_it = lazy_variables_read.find(variable);
  if(r_it != lazy_variables_read.end())
  {
    const auto &v = r_it->second;
    const auto it = std::lower_bound(
      v.begin(), v.end(), qk,
      [](const lazy_variable_read &lv, const std::tuple<std::size_t, unsigned, unsigned, unsigned> &k) {
        return std::make_tuple(lv.round, lv.thread, lv.label, lv.num) < k;
      });
    if(it != v.end() && it->id < best)
      best = it->id;
  }
  return from_integer(best, type);
}
std::optional<lazy_pot::lazy_variable> lazy_pot::get_previous_write(unsigned thread, unsigned label, unsigned num, std::size_t round, irep_idt variable)
{
  const auto v_it = lazy_variables.find(variable);
  if(v_it == lazy_variables.end() || v_it->second.empty())
    return std::nullopt;
  const auto &v = v_it->second;
  const auto qk = std::make_tuple(round, thread, label, num);
  const auto it = std::lower_bound(
    v.begin(), v.end(), qk,
    [](const lazy_variable &lv, const std::tuple<std::size_t, unsigned, unsigned, unsigned> &k) {
      return std::make_tuple(lv.round, lv.thread, lv.label, lv.num) < k;
    });
  if(it == v.begin())
    return std::nullopt;
  return *std::prev(it);
}
void lazy_pot::create_lazy_variable_read() {
  for(auto global_variable : global_variables)
  {
    if(this->reads.count(global_variable) == 0)
      continue;
    for(std::size_t round = rounds; round >= 1; --round) {
      for(const auto &read : this->reads.at(global_variable)) {
        lazy_variable_read lazy_variable_read{round,read.label,read.num, read.thread};
        lazy_variables_read[global_variable].emplace_back(lazy_variable_read);
      }
    }
    auto &lvr = lazy_variables_read[global_variable];
    std::sort(lvr.begin(), lvr.end(),
      [](const lazy_variable_read &a, const lazy_variable_read &b) {
        return std::tie(a.round, a.thread, a.label, a.num)
             < std::tie(b.round, b.thread, b.label, b.num);
      });
  }
}

void lazy_pot::validate_access_order() const
{
  // Le navigazioni (get_previous_write/get_next_read/boundary_id) usano
  // lower_bound/upper_bound sui vettori per locazione: assumono ordine lex
  // stretto su (round, thread, label, num). Se l'ordine si rompe le catene
  // ancorano alla posizione sbagliata e il POR pota schedule legittimi senza
  // segnalare nulla. Stessa cosa per gli id, che devono essere unici e
  // crescenti nello spazio unificato write+read (enumerate_accesses).
  for(const auto &entry : lazy_variables)
  {
    const auto &v = entry.second;
    for(std::size_t i = 1; i < v.size(); ++i)
      DATA_INVARIANT(
        std::tie(v[i - 1].round, v[i - 1].thread, v[i - 1].label, v[i - 1].num) <
          std::tie(v[i].round, v[i].thread, v[i].label, v[i].num),
        "lazy_po: write positions must be strictly lex-ordered");
  }

  for(const auto &entry : lazy_variables_read)
  {
    const auto &v = entry.second;
    for(std::size_t i = 1; i < v.size(); ++i)
      DATA_INVARIANT(
        std::tie(v[i - 1].round, v[i - 1].thread, v[i - 1].label, v[i - 1].num) <
          std::tie(v[i].round, v[i].thread, v[i].label, v[i].num),
        "lazy_po: read positions must be strictly lex-ordered");
  }

  for(const auto &gv : global_variables)
  {
    std::unordered_set<unsigned> ids;
    const auto w_it = lazy_variables.find(gv);
    if(w_it != lazy_variables.end())
      for(const auto &lv : w_it->second)
        DATA_INVARIANT(
          ids.insert(lv.id).second, "lazy_po: duplicate write id in location");
    const auto r_it = lazy_variables_read.find(gv);
    if(r_it != lazy_variables_read.end())
      for(const auto &lv : r_it->second)
        DATA_INVARIANT(
          ids.insert(lv.id).second,
          "lazy_po: read id collides with another access id in location");
  }

  for(const auto &entry : atomic_blocks)
  {
    const atomic_block &b = entry.second;
    DATA_INVARIANT(
      entry.first.first == b.thread && entry.first.second == b.label,
      "lazy_po: atomic block key must match its thread/label");
  }
}

void lazy_pot::enumerate_accesses()
{
  for(auto global_variable : global_variables)
  {
    auto w_it = lazy_variables.find(global_variable);
    auto r_it = lazy_variables_read.find(global_variable);
    std::size_t wi = 0, ri = 0;
    const std::size_t wn = w_it != lazy_variables.end() ? w_it->second.size() : 0;
    const std::size_t rn = r_it != lazy_variables_read.end() ? r_it->second.size() : 0;
    unsigned id = 0;
    while(wi < wn || ri < rn)
    {
      const bool take_write =
        ri >= rn ||
        (wi < wn &&
         std::tie(w_it->second[wi].round, w_it->second[wi].thread,
                  w_it->second[wi].label, w_it->second[wi].num) <
         std::tie(r_it->second[ri].round, r_it->second[ri].thread,
                  r_it->second[ri].label, r_it->second[ri].num));
      if(take_write)
        w_it->second[wi++].id = id++;
      else
        r_it->second[ri++].id = id++;
    }
  }
}

std::optional<lazy_pot::lazy_variable_read>
lazy_pot::get_next_read(unsigned thread, unsigned label, unsigned num,
  std::size_t round, irep_idt variable, bool strict)
{
  const auto v_it = lazy_variables_read.find(variable);
  if(v_it == lazy_variables_read.end() || v_it->second.empty())
    return std::nullopt;
  const auto &v = v_it->second;
  const auto qk = std::make_tuple(round, thread, label, num);
  const auto it =
    strict ? std::upper_bound(
               v.begin(), v.end(), qk,
               [](const std::tuple<std::size_t, unsigned, unsigned, unsigned> &k,
                  const lazy_variable_read &lv) {
                 return k < std::make_tuple(lv.round, lv.thread, lv.label, lv.num);
               })
           : std::lower_bound(
               v.begin(), v.end(), qk,
               [](const lazy_variable_read &lv,
                  const std::tuple<std::size_t, unsigned, unsigned, unsigned> &k) {
                 return std::make_tuple(lv.round, lv.thread, lv.label, lv.num) < k;
               });
  if(it == v.end())
    return std::nullopt;
  return *it;
}
