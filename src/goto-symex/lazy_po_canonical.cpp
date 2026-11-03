/// \file
/// lazy_po: POR canonicality -- atomic-block witnesses ABR/ABW and the LW/WINR/NRP/OBS/LOW tag chains

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
