/// \file
/// lazy_po: window (range-OR) encoding of the POR canonicality tags

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
