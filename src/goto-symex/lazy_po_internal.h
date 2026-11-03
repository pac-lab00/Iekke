/// \file
/// lazy_po: helpers shared by the lazy_po_*.cpp translation units. Internal
/// to goto-symex; not part of lazy_po's interface.
///
/// The functions are `inline`, not `static`: tag_stats() and
/// por_symbol_registry() hold function-local statics, and with internal
/// linkage every translation unit would get its own copy -- the POR symbol
/// registry the SAT backend reads would then miss every symbol registered
/// outside the file that clears it.

#ifndef CPROVER_GOTO_SYMEX_LAZY_PO_INTERNAL_H
#define CPROVER_GOTO_SYMEX_LAZY_PO_INTERNAL_H

#include <util/invariant.h>
#include <util/std_expr.h>

#include <cctype>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

// Campi impaccati nella chiave delle memo: num [0,20), label [20,40),
// thread [40,52), round [52,64). Un overflow silenzioso farebbe collidere
// posizioni distinte nelle cache delle catene (una LW di un thread diventa
// quella di un altro) -- stessa classe di guasto del troncamento degli id in
// bit_writes. Meglio abortire che emettere vincoli sbagliati.
static const unsigned chain_key_num_max = 1u << 20;
static const unsigned chain_key_label_max = 1u << 20;
static const unsigned chain_key_thread_max = 1u << 12;
static const std::size_t chain_key_round_max = std::size_t(1) << 12;

inline uint64_t chain_key(std::size_t round, unsigned thread, unsigned label, unsigned num)
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

inline tag_chain_statst &tag_stats()
{
  static tag_chain_statst s;
  return s;
}

// Registry della provenance POR: i simboli ausiliari introdotti dalla
// riduzione (catene dei tag e testimoni di blocco). Serve al backend SAT per
// classificare le variabili corrispondenti senza indovinare dai nomi dopo il
// bit-blasting, dove un simbolo diventa molti letterali e i nomi sparaiscono.
// Ambito processo: una run = un'equazione, ripulito a ogni costruzione.
inline std::vector<symbol_exprt> &por_symbol_registry()
{
  static std::vector<symbol_exprt> registry;
  return registry;
}

inline const symbol_exprt &register_por_symbol(const symbol_exprt &sym)
{
  por_symbol_registry().push_back(sym);
  return por_symbol_registry().back();
}

/// Memo for subtree_has: node address -> (the node, the answer).
using subtree_memot = std::unordered_map<const void *, std::pair<exprt, bool>>;

/// Whether some node of \p expr satisfies \p here, not looking inside nodes
/// \p prune accepts, computed once per shared node and without writing to
/// any. The memo holds every node it records: a held node is shared, so it is
/// never changed in place (a write detaches a shared node) nor freed, and its
/// address names the same unchanged node for as long as the memo lives.
/// Used to make a non-const rewrite descend only where it changes something:
/// a non-const walk unshares every node it visits, and over a whole equation
/// that copies its expression DAG into trees.
inline bool subtree_has(
  const exprt &expr,
  const std::function<bool(const exprt &)> &here,
  const std::function<bool(const exprt &)> &prune,
  subtree_memot &memo)
{
  if(prune(expr))
    return false;
  const void *node = &expr.read();
  const auto known = memo.find(node);
  if(known != memo.end())
    return known->second.second;
  bool found = here(expr);
  for(const auto &op : expr.operands())
  {
    if(found)
      break;
    found = subtree_has(op, here, prune, memo);
  }
  memo.emplace(node, std::make_pair(expr, found));
  return found;
}


/// Drop the L2 counter so every version of an object maps to one name. The L1
/// frame suffix stays: that is what global_variables is keyed on.
///
/// The counter is `#` followed by digits, and it is not always at the end --
/// field sensitivity appends the component after it, as in
/// `queue#1..element`. Erasing from the `#` to the end would turn that into
/// `queue`, so the object would never be recognised and every analysis keyed
/// on this name would silently decline it.
inline irep_idt narrowing_base(const exprt &expr)
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

#endif // CPROVER_GOTO_SYMEX_LAZY_PO_INTERNAL_H
