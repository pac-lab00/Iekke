/// \file
/// LazyCSeq context-bounded concurrency SSA transformation

#include "lazy_po.h"
#include <algorithm>
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

  if(por)
  {
    build_atomic_blocks();
    phase("atomic-blocks");
  }

  create_write_constraints(equation);
  phase("base-writes");

  create_read_constraints(equation);
  phase("base-reads");

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

  if(datarace) {
    log.warning() << "Datarace Enabled " << messaget::eom;
    handling_datarace(equation);
    phase("datarace");
  }
  else
  {
    handling_guards(equation);
    phase("guards");
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

  log.statistics()
    << "lazy_po total: "
    << std::chrono::duration_cast<std::chrono::milliseconds>(
         std::chrono::steady_clock::now() - t_start)
         .count()
    << "ms" << messaget::eom;
}

void lazy_pot::create_write_constraints(
  symex_target_equationt &equation)
{
  for(auto global_variable : global_variables)
  {
    if(this->writes.count(global_variable) == 0)
      continue;
    exprt previous = this->writes.at(global_variable).front().s_it->ssa_lhs;

    irep_idt sentinel_id_name = "id_T0_L0_N0_R0_V"+id2string(global_variable);
    symbol_exprt sentinel_id_symbol{sentinel_id_name, unsignedbv_typet(bit_writes[global_variable])};
    lazy_variable first_lazy_struct = lazy_variable{
      0, 0, 0, 0, 0, this->writes.at(global_variable).front().s_it->ssa_lhs, sentinel_id_symbol};
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
          write.s_it->ssa_lhs.type());
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

        equal_exprt constraint{
          lazy_variable_exprt,
          if_exprt{exec, write.s_it->ssa_lhs,
                   typecast_exprt::conditional_cast(
                     previous, write.s_it->ssa_lhs.type())}};

        equation.constraint(constraint, "write constraint", write.s_it->source);

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
    for(const auto &read : this->reads.at(global_variable))
    {
      exprt temp_constraint = read.s_it->ssa_lhs;
      for(std::size_t round = rounds; round >= 1; --round)
      {
        const symbol_exprt exec =
          create_exec_symbol(read.label, read.num, read.thread, round);

        std::optional<symbol_exprt> previous =
          previous_shared(global_variable, read.label, read.num, read.thread, round);
        if(previous.has_value())
        {
          temp_constraint = if_exprt{exec,
            typecast_exprt::conditional_cast(
              previous.value(), read.s_it->ssa_lhs.type()),
            temp_constraint};
        }
        else {
          temp_constraint = if_exprt{exec, read.s_it->ssa_lhs, temp_constraint};
        }
      }
      equal_exprt final_constraint{read.s_it->ssa_lhs, temp_constraint};
      equation.constraint(
        final_constraint, "read constraint", read.s_it->source);
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

        const auto git = guards[thread].find(label);
        const bool has_guards = (label > 0 && git != guards[thread].end());
        unsigned nmax =
          has_guards ? static_cast<unsigned>(git->second.size()) : 1;
        for(unsigned num = 0; num < nmax; ++num)
        {
          exprt expr_5;
          if (has_guards) {
            expr_5 = and_exprt{enabled, git->second.at(num)};
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
        if(label != 0 && round > 1)
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
  equation = temp_equation;
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

  symex_target_equationt::SSA_stepst::const_iterator prev;

  for(symex_target_equationt::SSA_stepst::const_iterator s_it =
        ssa_steps.begin();
      s_it != ssa_steps.end();
      s_it++)
  {
    guard = s_it->guard;

    if(s_it->source.thread_nr > thread_current)
    {
      thread_ends[thread_current] = true;
      exprt prev_guard = prev->guard;

      unsigned int atomic_section_id = prev->atomic_section_id;

      if(prev->is_atomic_begin())
        atomic_section_id = 1;

      create_active_thread_statements(
        prev->source,
        prev_guard,
        atomic_section_id,
        thread_current,
        temp_equation,
        false_exprt{});

      thread_current = s_it->source.thread_nr;

      SSA_stept step{equation.SSA_steps.front()};
      step.type = equation.SSA_steps.front().type;

      equation.SSA_steps.pop_front();
      temp_equation.SSA_steps.emplace_back(step);

      prev = s_it;
      continue;
    }

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
        bool is_pthread = (func.rfind("pthread", 0) == 0);
        if (write.thread != thread || is_pthread)
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
        bool is_pthread = (func.rfind("pthread", 0) == 0);
        if (write.thread != thread || is_pthread)
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
        bool is_pthread = (func.rfind("pthread", 0) == 0);
        if (read.thread != thread || is_pthread)
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

void lazy_pot::handling_datarace(
  symex_target_equationt &equation) {


  irep_idt phases_name = "phases";
  symbol_exprt phases_symbl{phases_name, bool_typet{}};
  exprt phases_exp = false_exprt{};
  for (auto v : global_variables) {
    if (v.starts_with("__CPROVER"))
      continue;
    if (equation.symbol_is_atomic(ns,v))
      continue;
    symbol_exprt pha_1 = phase_1(/*log,*/ equation, v);
    symbol_exprt pha_2 = phase_2(/*log,*/ equation, v);
    exprt pha_1_2 = and_exprt{pha_1, pha_2};
    phases_exp = or_exprt{phases_exp, pha_1_2};
  }
  phases_exp = equal_exprt{phases_symbl, phases_exp};
  simplify(phases_exp, ns);
  equation.constraint(
    phases_exp, "datarace constraint", equation.SSA_steps.begin()->source);

  symbol_exprt same_round_symbl = same_round(/*log,*/ equation);

  symbol_exprt no_interf_symbl = no_interf(/*log,*/ equation);

  exprt datarace_contraint = and_exprt{phases_symbl, and_exprt{same_round_symbl, no_interf_symbl}};
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

  for(symex_target_equationt::SSA_stepst::iterator s_it =
        ssa_steps.begin();
      s_it != ssa_steps.end();
      s_it++)
  {
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
      num = 0;
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
        if (next != ssa_steps.end() && next->is_assignment() && next->ssa_rhs.id() == ID_with) { //ARRAY
          where = to_with_expr(next->ssa_rhs).where();
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
        this->writes[shared_event.s_it->ssa_lhs.get_l1_object_identifier()]
          .emplace_back(shared_event);
        this->global_variables.emplace(
          shared_event.s_it->ssa_lhs.get_l1_object_identifier());
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
        if (next != ssa_steps.end() && next->is_assignment() && next->ssa_rhs.id() == ID_index) { //ARRAY
          where = to_index_expr(next->ssa_rhs).index();
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

        this->reads[shared_event.s_it->ssa_lhs.get_l1_object_identifier()].emplace_back(shared_event);
        this->global_variables.insert(shared_event.s_it->ssa_lhs.get_l1_object_identifier());
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

  irep_idt obs_id = "OBS_T" + std::to_string(w.thread) + "_L" + std::to_string(w.label) +
    "_N" + std::to_string(w.num) + "_R" + std::to_string(w.round) + "_V" + id2string(variable);
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
