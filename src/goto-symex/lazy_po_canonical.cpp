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
/// exempting write/write conflicts recovers every reproducer and
/// semaphore-posix-race, and exempting read/write conflicts as well recovers
/// nothing beyond it.
bool lazy_pot::block_can_race(const atomic_block &b) const
{
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

  // A write of the block conflicts with another thread's write.
  for(const auto &entry : b.writes)
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
          : exprt(create_ABR_windows(
              b.reads, round, b.label, b.thread, equation));
      exprt abw =
        b.writes.empty()
          ? exprt(false_exprt{})
          : exprt(create_ABW_windows(
              b.writes, round, b.label, b.thread, equation));

      exprt expression = implies_exprt(fire_cond, or_exprt(abr, abw));
      simplify(expression, ns);
      equation.constraint(expression, "atomic_block_canonical", src);
    }
  }
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
  // Le navigazioni (get_previous_write/boundary_index) usano
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
