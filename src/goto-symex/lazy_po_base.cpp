/// \file
/// lazy_po: base round-robin encoding -- read/write values, context-switch counters, guards, active threads

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

void lazy_pot::create_write_constraints(
  symex_target_equationt &equation)
{
  if(getenv("LAZYPO_DEAD_AUDIT") != nullptr)
    dead_audit(equation);

  // Both this chain and create_read_constraints, which runs straight after,
  // are built from it.
  compute_narrowings(equation);
  compute_value_narrowings(equation);
  // Every value written fits its narrow type, so every value read does too:
  // say so, and the low bits the read constraints compare fix the whole value.
  for(const auto &vn : value_narrowings)
  {
    const auto r_it = reads.find(vn.first);
    if(r_it == reads.end())
      continue;
    for(const auto &read : r_it->second)
    {
      const exprt &r = read.s_it->ssa_lhs;
      equation.constraint(
        equal_exprt{r, typecast_exprt{typecast_exprt{r, vn.second}, r.type()}},
        "value narrowing " + id2string(vn.first),
        read.s_it->source);
    }
  }
  index_chain_summary = choose_index_chains();

  for(auto global_variable : global_variables)
  {
    if(this->writes.count(global_variable) == 0)
      continue;
    const ssa_exprt &initial =
      this->writes.at(global_variable).front().s_it->ssa_lhs;
    const typet chain_type = narrowed_type(global_variable, initial.type());

    if(index_chain_vars.count(global_variable) != 0)
    {
      // The chain carries which write was the last one, not what it wrote:
      // index 0 is the value before the first write (the same round-0 value
      // the value chain starts from), index k the k-th write.
      const unsignedbv_typet idx_type{index_chain_bits.at(global_variable)};
      const auto &ws = this->writes.at(global_variable);
      auto &vals = index_chain_values[global_variable];
      vals.push_back(narrowed_value(global_variable, initial));
      for(const auto &write : ws)
        vals.push_back(narrowed_value(global_variable, write.s_it->ssa_lhs));

      const symbol_exprt sentinel{
        id2string(initial.get_identifier()) + "_IDX_T0_L0_R0", idx_type};
      equation.constraint(
        equal_exprt{sentinel, from_integer(0, idx_type)},
        "write constraint " + id2string(global_variable),
        ws.front().s_it->source);
      irep_idt sentinel_id_name =
        "id_T0_L0_N0_R0_V" + id2string(global_variable);
      symbol_exprt sentinel_id_symbol{
        sentinel_id_name, unsignedbv_typet(bit_writes[global_variable])};
      this->lazy_variables[global_variable].emplace_back(
        lazy_variable{0, 0, 0, 0, 0, sentinel, sentinel_id_symbol});

      exprt previous = sentinel;
      for(std::size_t round = 1; round <= rounds; ++round)
      {
        for(std::size_t k = 1; k <= ws.size(); ++k)
        {
          const auto &write = ws[k - 1];
          const symbol_exprt link{
            id2string(write.s_it->ssa_lhs.get_identifier()) + "_IDX_T" +
              std::to_string(write.thread) + "_L" +
              std::to_string(write.label) + "_R" + std::to_string(round),
            idx_type};
          irep_idt id_name = "id_T" + std::to_string(write.thread) + "_L" +
                             std::to_string(write.label) + "_N" +
                             std::to_string(write.num) + "_R" +
                             std::to_string(round) + "_V" +
                             id2string(global_variable);
          symbol_exprt id_symbol{
            id_name, unsignedbv_typet(bit_writes[global_variable])};
          this->lazy_variables[global_variable].emplace_back(lazy_variable{
            round, write.label, write.num, write.thread, 0, link, id_symbol});

          const symbol_exprt exec =
            create_exec_symbol(write.label, write.num, write.thread, round);
          equation.constraint(
            equal_exprt{
              link, if_exprt{exec, from_integer(k, idx_type), previous}},
            "write constraint " + id2string(global_variable),
            write.s_it->source);
          previous = link;
        }
      }

      auto &lvs = this->lazy_variables[global_variable];
      std::sort(lvs.begin(), lvs.end(),
        [](const lazy_variable &a, const lazy_variable &b) {
          return std::tie(a.round, a.thread, a.label, a.num)
               < std::tie(b.round, b.thread, b.label, b.num);
        });
      for(std::size_t i = 0; i < lvs.size(); ++i)
        lvs[i].id = static_cast<unsigned>(i);
      continue;
    }

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
        // a narrowed object's links of round r carry that round's bits
        const auto vr = value_round_types.find(global_variable);
        const typet link_type =
          vr == value_round_types.end() ? chain_type : vr->second[round];
        const symbol_exprt lazy_variable_exprt = create_lazy_symbol(
          write.label,
          write.thread,
          round,
          write.s_it->ssa_lhs,
          link_type);
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
                     vr == value_round_types.end()
                       ? narrowed_value(global_variable, write.s_it->ssa_lhs)
                       : typecast_exprt{write.s_it->ssa_lhs, link_type},
                     typecast_exprt::conditional_cast(previous, link_type)}};

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

    if(index_chain_vars.count(global_variable) != 0)
    {
      // The read takes the index the chain holds at its position in the round
      // it runs in, as the value chain's read takes the value; the value is
      // then the one written by the write of that index. Only the indices
      // that can stand before the read are decoded (index_candidates).
      const auto &vals = index_chain_values.at(global_variable);
      const unsignedbv_typet idx_type{index_chain_bits.at(global_variable)};
      for(const auto &read : this->reads.at(global_variable))
      {
        const exprt read_value =
          narrowed_value(global_variable, read.s_it->ssa_lhs);
        const typet read_type =
          narrowed_type(global_variable, read.s_it->ssa_lhs.type());
        const symbol_exprt rf{
          "rfidx::" + id2string(read.s_it->ssa_lhs.get_identifier()),
          idx_type};
        exprt::operandst ran;
        for(std::size_t round = 1; round <= rounds; ++round)
        {
          const symbol_exprt exec =
            create_exec_symbol(read.label, read.num, read.thread, round);
          std::optional<symbol_exprt> previous = previous_shared(
            global_variable, read.label, read.num, read.thread, round);
          if(!previous.has_value())
            continue;
          ran.push_back(exec);
          equation.constraint(
            implies_exprt{exec, equal_exprt{rf, previous.value()}},
            "read constraint " + id2string(global_variable),
            read.s_it->source);
        }
        if(ran.empty())
          continue;
        const exprt ran_any = disjunction(ran);
        for(const std::size_t k : index_candidates(global_variable, read))
        {
          equation.constraint(
            implies_exprt{
              and_exprt{ran_any, equal_exprt{rf, from_integer(k, idx_type)}},
              equal_exprt{
                read_value,
                typecast_exprt::conditional_cast(vals.at(k), read_type)}},
            "read constraint " + id2string(global_variable),
            read.s_it->source);
        }
      }
      continue;
    }

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

        const auto git = guards[thread].find(label);
        const bool has_guards = (label > 0 && git != guards[thread].end());
        unsigned nmax =
          has_guards ? static_cast<unsigned>(git->second.size()) : 1;
        for(unsigned num = 0; num < nmax; ++num)
        {
          exprt expr_5;
          if (has_guards) {
            exprt g = git->second.at(num);
            if(!g.is_true() && !g.is_false())
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
    // pattern match. The spawn step names the thread it starts (several
    // spawns start the same thread under --merge-exclusive-threads), so no
    // heuristic is needed for the target thread index either. Using the spawn step's own
    // atomic_section_id (rather than a hard-coded 1, which was tuned
    // specifically for pthread_create's library wrapper) is correct for
    // both forms: a pthread_create SPAWN sits inside that library's
    // atomic section, an __CPROVER_ASYNC one does not.
    if(s_it->is_spawn())
    {
      unsigned spawned = static_cast<unsigned>(s_it->spawned_thread_nr);
      create_active_thread_statements(
        s_it->source,
        guard,
        s_it->atomic_section_id,
        spawned,
        temp_equation,
        true_exprt{});
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
  // thread (the caller's index into this map) comes from the spawn step or
  // the thread's last step; the map is populated up front from thread_current
  // in handling_active_threads. Register defensively anyway: a missing entry
  // would otherwise throw std::out_of_range below with no diagnostic.
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
