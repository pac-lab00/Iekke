/// \file
/// LazyCSeq context-bounded concurrency SSA transformation

#ifndef CPROVER_GOTO_SYMEX_lazy_po_H
#define CPROVER_GOTO_SYMEX_lazy_po_H

#include "symex_target_equation.h"

#include <cstdint>
#include <map>
#include <set>
#include <optional>
#include <vector>

// Provenance POR per il backend SAT: elenco dei simboli ausiliari creati
// dall'ultima costruzione (LW, WINR, NRP, LOW, OBS, ABR, ABW). La
// classificazione delle variabili appartiene al livello che costruisce la
// formula, non al solver.
const std::vector<symbol_exprt> &por_auxiliary_symbols();
void clear_por_auxiliary_symbols();

class lazy_pot
{
public:
  explicit lazy_pot(const namespacet &ns, const std::size_t rounds, const bool datarace, const bool por, const bool read_implication = false, const bool narrow_shared = false, const bool thread_private = false, const bool array_rf = false)
    : ns(ns), rounds(rounds), datarace(datarace), por(por),
      read_implication(read_implication), narrow_shared(narrow_shared),
      thread_private(thread_private), array_rf(array_rf)
  {
  }

  void operator()(symex_target_equationt &, message_handlert &);

private:
  const namespacet &ns;
  const std::size_t rounds;
  const bool datarace;
  /// state each read's one-hot round selection directly instead of as a mux
  /// nested `rounds` deep; see create_read_constraints
  const bool read_implication = false;
  const bool por;
  /// carry only the byte range a shared object is read through; see
  /// compute_narrowings
  const bool narrow_shared = false;

  /// The byte range of a shared object that the equation ever reads, for
  /// objects whose chain can safely carry only that range.
  struct narrowingt
  {
    std::size_t offset_bits;
    std::size_t width_bits;
  };
  std::map<irep_idt, narrowingt> narrowings;

  /// state the read-from of objects only one thread touches once, in program
  /// order, instead of once per round; see compute_private_objects
  const bool thread_private = false;
  /// answer an array element read by matching the writes, instead of carrying
  /// the whole array through the chain; see compute_array_rf
  const bool array_rf = false;

  void compute_narrowings(const symex_target_equationt &);
  /// The value the lazy chain carries for `variable`: the whole value, or the
  /// slice of it that reads observe.
  exprt narrowed_value(const irep_idt &variable, const exprt &value) const;
  /// The type that value has.
  typet narrowed_type(const irep_idt &variable, const typet &type) const;

  struct shared_event
  {
    symex_target_equationt::SSA_stepst::const_iterator s_it;
    exprt where;
    unsigned label;
    unsigned num;
    unsigned thread;
  };
  struct lazy_variable
  {
    std::size_t round;
    unsigned label;
    unsigned num;
    unsigned thread;
    unsigned id;
    symbol_exprt symbol;
    symbol_exprt exptr_id;
  };
  struct lazy_variable_read
  {
    std::size_t round;
    unsigned label;
    unsigned num;
    unsigned thread;
    unsigned id = 0;
  };
  struct active_thread
  {
    unsigned thread;
    std::size_t l2;
    symbol_exprt symbol;
  };
  struct exec
  {
    unsigned label;
    unsigned num;
    unsigned thread;
    std::size_t round;
    symbol_exprt symbol;
  };
  struct exec_tot
  {
    unsigned label;
    unsigned num;
    unsigned thread;
    symbol_exprt symbol;
  };
  struct enabled
  {
    unsigned label;
    unsigned thread;
    std::size_t round;
    symbol_exprt symbol;
  };
  struct cs
  {
    std::size_t thread;
    std::size_t round;
    symbol_exprt symbol;
  };
  // Order/thermometer encoding of cs: GE(thread,round,i) means
  // cs(thread,round) >= i. See create_ge_symbol / create_cs_constraint.
  struct ge
  {
    std::size_t thread;
    std::size_t round;
    unsigned i;
    symbol_exprt symbol;
  };
  struct reach
  {
    unsigned label;
    std::size_t thread;
    symbol_exprt symbol;
  };
  struct atomic_block
  {
    unsigned thread;
    unsigned label;
    std::map<irep_idt, std::vector<shared_event>> reads;  // x -> read events; i = event.num
    std::map<irep_idt, std::vector<shared_event>> writes; // x -> write events
  };
  struct atomic_block_round
  {
    unsigned thread;
    unsigned label;
    unsigned round;
    symbol_exprt symbol;
  };
  std::size_t threads = 0;
  std::size_t threads_bits;
  std::size_t rounds_bits;
  std::unordered_map<unsigned, symbol_exprt> dr_thread;
  std::unordered_map<unsigned, symbol_exprt> dr_round;
  std::unordered_map<unsigned, symbol_exprt> dr_atom;
  std::unordered_map<unsigned, symbol_exprt> dr_loc;
  std::unordered_set<irep_idt> global_variables;
  /// objects moved out of global_variables by compute_private_objects, with
  /// their accesses moved out of reads/writes as well -- the POR windows and
  /// the canonicality constraints look those maps up by variable and index
  /// into a lazy chain these objects no longer have
  std::set<irep_idt> private_objects;
  std::unordered_map<irep_idt, std::vector<shared_event>> private_writes;
  std::unordered_map<irep_idt, std::vector<shared_event>> private_reads;

  void dead_audit(const symex_target_equationt &);
  /// One shared write to an array object, decomposed. A point update matches a
  /// read when its index agrees; a whole-array constant initialiser matches
  /// every index, which is also how it serves as the value before it.
  struct array_writet
  {
    std::size_t event;     ///< index into writes.at(variable)
    bool whole_array;      ///< a constant initialiser rather than a point update
    exprt index;
    exprt value;
  };
  /// objects whose element reads are resolved by matching writes
  std::map<irep_idt, std::vector<array_writet>> array_rf_writes;
  /// the element value before any write, from the constant initialiser
  std::map<irep_idt, exprt> array_rf_default;

  void compute_array_rf(const symex_target_equationt &);
  void create_array_rf_constraints(symex_target_equationt &);

  void compute_private_objects();
  void create_private_constraints(symex_target_equationt &);
  exprt happens_in_any_round(const shared_event &);
  std::unordered_map<irep_idt, std::vector<shared_event>> writes;
  std::unordered_map<irep_idt, std::vector<shared_event>> reads;
  std::unordered_map<irep_idt, unsigned> bit_writes;
  std::unordered_map<irep_idt, unsigned> bit_reads;
  // memo delle catene: chiave = posizione (round, thread, label, num) impaccata
  std::unordered_map<irep_idt, std::unordered_map<uint64_t, symbol_exprt>> lw_variables;
  std::unordered_map<irep_idt, std::unordered_map<uint64_t, symbol_exprt>> winr_variables;
  std::unordered_map<irep_idt, std::unordered_map<uint64_t, symbol_exprt>> low_variables;
  std::unordered_map<irep_idt, std::unordered_map<uint64_t, symbol_exprt>> obs_variables;
  std::unordered_map<irep_idt, std::unordered_map<uint64_t, symbol_exprt>> nrp_variables;
  std::vector<shared_event> blocking_events;
  std::vector<shared_event> shared_events;
  std::unordered_map<irep_idt, std::vector<lazy_variable>> lazy_variables;
  std::unordered_map<irep_idt, std::vector<lazy_variable_read>> lazy_variables_read;
  std::unordered_map<unsigned, active_thread> active_threads_vector;
  std::size_t skipped_writes = 0, skipped_reads = 0;
  std::vector<exec> exec_vector;
  std::unordered_map<uint64_t, symbol_exprt> exec_map;
  std::vector<atomic_block_round> atomic_block_rounds;
  std::vector<exec_tot> exec_tot_vector;
  std::vector<enabled> enabled_vector;
  // --- Window encoding of the canonicality tags ------------------------
  // Per shared variable: the accesses (writes and reads) in id order, the
  // exec literal of each, the OBS literal of each write, and the FR chain
  // ("the first executed access with id >= k is a read"). Every comparison
  // the canonicality clauses make on LW/WINR/NRP/LOW is equivalent to a
  // disjunction of exec literals over a contiguous id window (see the
  // soundness argument above create_ABW_windows in lazy_po.cpp); the
  // windows are materialised through a shared balanced range-OR tree so a
  // query costs O(log n) literals instead of an n-bit comparator.
  struct tag_windowt
  {
    bool init = false;
    bool obs_built = false;
    bool fr_built = false;
    std::size_t n = 0;                 // |writes| + |reads| for this variable
    std::vector<unsigned> write_ids;   // ascending
    std::vector<exprt> write_exec;     // parallel to write_ids
    std::vector<unsigned> read_ids;    // ascending
    std::vector<exprt> read_exec;      // parallel to read_ids
    std::vector<exprt> obs;            // parallel to write_ids
    std::vector<exprt> fr;             // size n+1, fr[k] = FR(k)
    // memo dei nodi del range-OR: kind 0 = writes, 1 = reads, 2 = OBS
    std::unordered_map<uint64_t, exprt> nodes[3];
  };
  std::unordered_map<irep_idt, tag_windowt> tag_windows;
  // A/B switch during development: LAZYPO_TAG_BV=1 restores the original
  // bitvector tag chains (create_LW_symbol & co.).
  bool bv_tags = false;
  // LAZYPO_TAG_XCHECK=1: emette entrambi gli encoding e asserisce che i
  // testimoni ABR/ABW coincidano (validazione, non produzione).
  bool xcheck_tags = false;
  // coppie (finestre, bitvector) da asserire uguali; emesse a fine
  // costruzione perche' handling_guards assume che ogni assert nella
  // equazione abbia un blocking event corrispondente.
  std::vector<std::pair<exprt, exprt>> xcheck_pairs;

  std::vector<cs> cs_vector;
  std::vector<ge> ge_vector;
  std::vector<reach> reach_vector;

  std::unordered_map<uint64_t, symbol_exprt> exec_tot_map;
  std::unordered_map<uint64_t, symbol_exprt> enabled_map;
  std::unordered_map<uint64_t, symbol_exprt> cs_map;
  std::unordered_map<uint64_t, symbol_exprt> ge_map;
  std::unordered_map<uint64_t, symbol_exprt> reach_map;
  std::vector<std::pair<unsigned, std::pair<std::size_t, std::size_t>>>
    atomic_sections;
  std::map<std::pair<unsigned, unsigned>, atomic_block>
    atomic_blocks;
  std::unordered_map<unsigned, unsigned> n_bit;
  std::unordered_map<unsigned, unsigned> labels;
  std::unordered_map<unsigned,std::unordered_map<unsigned, std::vector<exprt>>> guards; // < thread, < label, < num, guard > > >

  void handling_active_threads(
    symex_target_equationt &equation);

  void check_shared_event(
    symex_target_equationt &equation);

  void handling_atomic_sections(
    symex_target_equationt &equation);

  void collect_reads_and_writes(
    symex_target_equationt::SSA_stepst &ssa_steps);

  void annotate_round_robin_trace_event(
    SSA_stept &step,
    unsigned label,
    unsigned num,
    unsigned thread,
    unsigned trace_order);

  void build_atomic_blocks();

  void validate_access_order() const;

  void create_write_constraints(
    symex_target_equationt &equation);

  void create_read_constraints(
    symex_target_equationt &equation);

  std::optional<symbol_exprt> previous_shared(
    irep_idt variable,
    unsigned label,
    unsigned num,
    unsigned thread,
    std::size_t round);

  exprt active_at_turn(unsigned thread, unsigned label, std::size_t round);

  void create_cs_constraint(
    symex_target_equationt &equation);

  void create_reach_constraint(
    symex_target_equationt &equation);

  void handling_guards(
    symex_target_equationt &equation);

  void handling_datarace(
    symex_target_equationt &equation);

  symbol_exprt phase_1(symex_target_equationt &equation, irep_idt v);
  symbol_exprt phase_2(symex_target_equationt &equation, irep_idt v);
  symbol_exprt same_round(symex_target_equationt &equation);
  symbol_exprt no_interf(symex_target_equationt &equation);
  // __SZH_DR_ADD_BEGIN__
  symbol_exprt phase_1_swap(symex_target_equationt &equation, irep_idt v);
  symbol_exprt phase_2_swap(symex_target_equationt &equation, irep_idt v);
  symbol_exprt same_round_swap(symex_target_equationt &equation);
  symbol_exprt no_interf_swap(symex_target_equationt &equation);
  // __SZH_DR_ADD_END__

  symbol_exprt create_lazy_symbol(
    unsigned label,
    unsigned thread,
    std::size_t round,
    ssa_exprt lhs,
    typet type);

  symbol_exprt
  create_exec_symbol(unsigned label, unsigned num, unsigned thread, std::size_t round);

  symbol_exprt
  create_exec_symbol_fast(unsigned label, unsigned num, unsigned thread, std::size_t round);

  symbol_exprt
  create_exec_tot_symbol(symex_target_equationt &equation, unsigned label, unsigned num, unsigned thread);

  symbol_exprt
  create_enabled_symbol(unsigned label, unsigned thread, std::size_t round);

  symbol_exprt create_cs_symbol(std::size_t thread, std::size_t round);
  symbol_exprt create_ge_symbol(std::size_t thread, std::size_t round, unsigned i);

  symbol_exprt create_reach_symbol(unsigned label, std::size_t thread);

  symbol_exprt create_active_thread_symbol(unsigned thread);

  symbol_exprt create_dr_thread_symbol(unsigned num);

  symbol_exprt create_dr_round_symbol(unsigned num);

  symbol_exprt create_dr_atom_symbol(unsigned num);

  symbol_exprt create_dr_loc_symbol(unsigned num);

  void create_lw_tot_symbol(symex_target_equationt &equation);

  void create_winr_tot_symbol(symex_target_equationt &equation);

  void create_low_tot_symbol(symex_target_equationt &equation);

  void create_nrp_tot_symbol(symex_target_equationt &equation);

  void create_atomic_canonical(symex_target_equationt &equation);

  /// True when an access of \p b conflicts with an access of another
  /// thread, so the block's position is observable to data-race detection
  /// even when it is invisible to the read-from equivalence that justifies
  /// canonicality. See create_atomic_canonical.
  bool block_can_race(const atomic_block &b) const;

  symbol_exprt create_ABR(const std::map<irep_idt, std::vector<shared_event>> &reads, std::size_t round, unsigned label, unsigned thread, symex_target_equationt &equation);

  symbol_exprt create_ABW(const std::map<irep_idt, std::vector<shared_event>> &writes, std::size_t round, unsigned label, unsigned thread, symex_target_equationt &equation);

  symbol_exprt create_LW_symbol(irep_idt variable, unsigned thread, unsigned label, unsigned num,size_t round,
  symex_target_equationt &equation);

  symbol_exprt create_WINR_symbol(irep_idt variable, unsigned thread, unsigned label, unsigned num, size_t round,
    symex_target_equationt &equation);

  symbol_exprt create_LOW_symbol(irep_idt variable, unsigned thread, unsigned label, unsigned num, size_t round,
    symex_target_equationt &equation);

  symbol_exprt create_NRP_symbol(irep_idt variable, unsigned thread, unsigned label, unsigned num, size_t round,
    symex_target_equationt &equation);

  symbol_exprt create_OBS_symbol(irep_idt variable, const lazy_variable &w,
    symex_target_equationt &equation);

  exprt boundary_id(irep_idt variable, std::size_t round, unsigned thread, unsigned label, unsigned num);

  // --- window encoding helpers ---
  tag_windowt &tag_data(irep_idt variable);

  // Integer twin of boundary_id: id of the first access of `variable` at or
  // after (round, thread, label, num), or n if there is none.
  std::size_t boundary_index(
    irep_idt variable, std::size_t round, unsigned thread, unsigned label,
    unsigned num);

  exprt range_node(
    irep_idt variable, unsigned kind, std::size_t a, std::size_t b,
    symex_target_equationt &equation);

  exprt range_query(
    irep_idt variable, unsigned kind, std::size_t a, std::size_t b,
    std::size_t lo, std::size_t hi, symex_target_equationt &equation);

  // OR of the kind-literals of the accesses whose id lies in [id_lo, id_hi).
  exprt window_exec(
    irep_idt variable, unsigned kind, std::size_t id_lo, std::size_t id_hi,
    symex_target_equationt &equation);

  exprt first_read_atom(
    irep_idt variable, std::size_t k, symex_target_equationt &equation);

  void build_first_read_chain(
    irep_idt variable, symex_target_equationt &equation);

  void build_obs_literals(irep_idt variable, symex_target_equationt &equation);

  symbol_exprt create_ABR_windows(
    const std::map<irep_idt, std::vector<shared_event>> &reads,
    std::size_t round, unsigned label, unsigned thread,
    symex_target_equationt &equation);

  symbol_exprt create_ABW_windows(
    const std::map<irep_idt, std::vector<shared_event>> &writes,
    std::size_t round, unsigned label, unsigned thread,
    symex_target_equationt &equation);

  void enumerate_accesses();

  std::optional<lazy_variable> get_previous_write(unsigned thread, unsigned label, unsigned num, std::size_t round, irep_idt variable);

  std::optional<lazy_variable_read>get_next_read(unsigned thread, unsigned label, unsigned num, std::size_t round, irep_idt variable, bool strict= false);


  void create_lazy_variable_read();
  void create_active_thread_statements(
    const symex_targett::sourcet &source,
    exprt &guard,
    unsigned int atomic_section_id,
    unsigned &thread,
    symex_target_equationt &equation,
    const exprt &value);
};

#endif //CPROVER_GOTO_SYMEX_lazy_po_H
