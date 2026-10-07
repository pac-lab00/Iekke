/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#ifndef CPROVER_GOTO_SYMEX_GOTO_SYMEX_STATE_H
#define CPROVER_GOTO_SYMEX_GOTO_SYMEX_STATE_H

#include <functional>
#include <memory>
#include <unordered_set>

#include <analyses/guard.h>

#include <util/invariant.h>
#include <util/nodiscard.h>
#include <util/ssa_expr.h>
#include <util/std_expr.h>

#include "call_stack.h"
#include "field_sensitivity.h"
#include "goto_state.h"
#include "renaming_level.h"
#include "symex_target_equation.h"

class incremental_dirtyt;

/// \brief Central data structure: state.
///
/// The state is a persistent data structure that symex maintains as it
/// executes. As we walk over each instruction, state will be updated reflecting
/// their effects until a branch occurs (such as an if), where parts of the
/// state will be copied into a \ref goto_statet, stored in a map for later
/// reference and then merged again (via merge_goto) once it reaches a
/// control-flow graph convergence.
class goto_symex_statet final : public goto_statet
{
public:
  goto_symex_statet(
    const symex_targett::sourcet &,
    std::size_t max_field_sensitive_array_size,
    bool should_simplify,
    guard_managert &manager,
    std::function<std::size_t(const irep_idt &)> fresh_l2_name_provider);
  ~goto_symex_statet();

  /// \brief Fake "copy constructor" that initializes the `symex_target` member
  explicit goto_symex_statet(
    const goto_symex_statet &other,
    symex_target_equationt *const target)
    : goto_symex_statet(other) // NOLINT
  {
    symex_target = target;
  }

  symex_targett::sourcet source;

  /// contains symbols that are minted during symbolic execution, such as
  /// dynamically created objects etc. The names in this table are needed
  /// for error traces even after symbolic execution has finished.
  symbol_tablet symbol_table;

  // Manager is required to be able to resize the thread vector
  guard_managert &guard_manager;
  symex_target_equationt *symex_target;

  symex_level1t level1;

  /// Rewrites symbol expressions in \ref exprt, applying a suffix to each
  /// symbol reflecting its most recent version, which differs depending on
  /// which level you requested. Each level also updates its predecessors, so
  /// a L1 rename will update L1 and L0. A L2 will update L2, L1 and L0.
  ///
  /// What happens at each level:
  ///     L0. Applies a suffix giving the current thread number. (Excludes
  ///         guards, dynamic objects and anything not considered thread-local)
  ///     L1. Applies a suffix giving the current loop iteration or recursive
  ///         function invocation.
  ///     L2. Applies a suffix giving the generation of this variable.
  ///
  /// Renaming will not increment any of these values, just update the
  /// expression with them. Levels matter when reading a variable, for
  /// example: reading the value of x really means reading the particular x
  /// symbol for this thread (L0 renaming, if applicable), the most recent
  /// instance of x (L1 renaming), and the most recent write to x (L2 renaming).
  ///
  /// The above example after being renamed could look like this: 'x!0@0#42'.
  /// That states it's the 42nd generation of this variable, on the first
  /// thread, in the first frame.
  ///
  /// A full explanation of SSA (which is why we do this renaming) is in
  /// the SSA section of background-concepts.md.
  template <levelt level = L2>
  NODISCARD renamedt<exprt, level> rename(exprt expr, const namespacet &ns);

  /// Version of rename which is specialized for SSA exprt.
  /// Implementation only exists for level L0 and L1.
  template <levelt level>
  NODISCARD renamedt<ssa_exprt, level>
  rename_ssa(ssa_exprt ssa, const namespacet &ns);

  template <levelt level = L2>
  void rename(typet &type, const irep_idt &l1_identifier, const namespacet &ns);

  NODISCARD exprt l2_rename_rvalues(exprt lvalue, const namespacet &ns);

  /// \return lhs renamed to level 2
  NODISCARD renamedt<ssa_exprt, L2> assignment(
    ssa_exprt lhs,    // L0/L1
    const exprt &rhs, // L2
    const namespacet &ns,
    bool rhs_is_simplified,
    bool record_value,
    bool allow_pointer_unsoundness = false);

  field_sensitivityt field_sensitivity;

protected:
  template <levelt>
  void rename_address(exprt &expr, const namespacet &ns);

  /// Update values up to \c level.
  template <levelt level>
  NODISCARD renamedt<ssa_exprt, level>
  set_indices(ssa_exprt expr, const namespacet &ns);

  // this maps L1 names to (L2) types
  typedef std::unordered_map<irep_idt, typet> l1_typest;
  l1_typest l1_types;

public:
  // guards
  static irep_idt guard_identifier()
  {
    static irep_idt id = "goto_symex::\\guard";
    return id;
  }

  call_stackt &call_stack()
  {
    PRECONDITION(source.thread_nr < threads.size());
    return threads[source.thread_nr].call_stack;
  }

  const call_stackt &call_stack() const
  {
    PRECONDITION(source.thread_nr < threads.size());
    return threads[source.thread_nr].call_stack;
  }

  /// Instantiate the object \p expr. An instance of an object is an L1-renamed
  /// SSA expression such that its L1-index has not previously been used.
  /// \param expr: Symbol to be instantiated
  /// \param index_generator: A function to produce a new index for a given name
  /// \param ns: A namespace
  /// \return L1-renamed SSA expression
  ssa_exprt add_object(
    const symbol_exprt &expr,
    std::function<std::size_t(const irep_idt &)> index_generator,
    const namespacet &ns);

  /// Add `invalid` (or a failed symbol) to the value_set if ssa is a pointer,
  /// ensure that level2 index of symbols in fields of ssa are at 1,
  /// and rename ssa to level 2
  /// \return ssa renamed to level 2
  ssa_exprt declare(ssa_exprt ssa, const namespacet &ns);

  void print_backtrace(std::ostream &) const;

  // threads
  typedef std::pair<unsigned, std::list<guardt> > a_s_r_entryt;
  typedef std::list<guardt> a_s_w_entryt;
  std::map<ssa_exprt, std::pair<a_s_r_entryt, irep_hash>>
    read_in_atomic_section;
  std::map<ssa_exprt, std::pair<a_s_w_entryt, irep_hash>>
    written_in_atomic_section;

  struct threadt
  {
    goto_programt::const_targett pc;
    irep_idt function_id;
    guardt guard;
    call_stackt call_stack;
    std::map<irep_idt, unsigned> function_frame;
    unsigned atomic_section_id = 0;
    explicit threadt(guard_managert &guard_manager)
      : guard(true_exprt(), guard_manager)
    {
    }
  };

  std::vector<threadt> threads;

  enum class write_is_shared_resultt
  {
    NOT_SHARED,
    IN_ATOMIC_SECTION,
    SHARED
  };

  bool l2_thread_read_encoding(ssa_exprt &expr, const namespacet &ns);
  bool l2_thread_write_encoding(const ssa_exprt &expr, const namespacet &ns);
  write_is_shared_resultt
  write_is_shared(const ssa_exprt &expr, const namespacet &ns) const;

  std::stack<bool> record_events;

  /// Extra condition conjoined onto the guard of the shared_write events
  /// emitted by \ref l2_thread_write_encoding (and only onto those: the SSA
  /// equality defining the new L2 symbol is left alone, as are the read
  /// events).
  ///
  /// Symbolic execution lowers a *partial* update of a composite object -- an
  /// array store at a non-constant index, or a guarded assignment -- into a
  /// read of the whole object followed by a write of the whole object, with
  /// the untouched parts framed over from the read.  Field sensitivity then
  /// splits that into one assignment per element, of the shape
  ///     a[[k]] == (i == k ? new_value : a[[k]]#read)
  /// Each of those is an unconditional *shared write* of element k, so in a
  /// concurrent program a thread storing to a[i] publishes a write to *every*
  /// element, carrying the value it read at the start of the statement.  Any
  /// element another thread updated in between is silently reset to that stale
  /// value -- a lost update that exists purely as an artefact of the whole-
  /// object read-modify-write lowering, and which shows up as spurious
  /// assertion failures (including broken mutual exclusion, since a store to
  /// a[i].datum frames a[k].mutex back to its pre-lock value).
  ///
  /// Setting this to the element-selection condition makes the write event
  /// itself conditional, so a framed (no-op) element write is not visible to
  /// the other threads at all and the round-robin write chain keeps whatever
  /// value was there.  See field_sensitivityt::field_assignments_rec.
  exprt shared_write_cond = true_exprt{};

  /// RAII helper: conjoins \p cond onto \ref shared_write_cond for its
  /// lifetime.
  class shared_write_condition_scopet
  {
  public:
    shared_write_condition_scopet(goto_symex_statet &state, const exprt &cond)
      : state(state), saved(state.shared_write_cond)
    {
      if(!cond.is_true())
      {
        state.shared_write_cond = saved.is_true()
                                    ? cond
                                    : static_cast<exprt>(and_exprt{saved, cond});
      }
    }

    ~shared_write_condition_scopet()
    {
      state.shared_write_cond = saved;
    }

    shared_write_condition_scopet(const shared_write_condition_scopet &) =
      delete;
    shared_write_condition_scopet &
    operator=(const shared_write_condition_scopet &) = delete;

  private:
    goto_symex_statet &state;
    exprt saved;
  };

  const incremental_dirtyt *dirty = nullptr;

  /// Points-to targets collected for shared pointers by an earlier symex
  /// pass, or null when there was none.
  ///
  /// Value sets are built in symex order, so a pointer published by a thread
  /// symexed later than this read is not in this read's set and the
  /// dereference resolves against a stale one -- CBMC issue #305. Only a
  /// previous pass can know what is published, so where one has run, a shared
  /// read of a pointer tops up *that object's* entry from here. Set by
  /// goto_symext while \ref goto_symext::seed_value_set_from_overall is on.
  const value_sett *published_value_set = nullptr;

  /// Top up \p expr's points-to set from \ref published_value_set, for a
  /// shared read of a pointer. Does nothing otherwise.
  void seed_published_targets(
    const ssa_exprt &expr,
    const irep_idt &l1_identifier,
    const namespacet &ns);

  /// Shared variables that a static, whole-program analysis has proven to be
  /// accessed by at most one thread over any execution (see
  /// thread_exclusivity.h). Such a variable cannot be interfered with by any
  /// other thread, so it is treated exactly like a thread-local: its value is
  /// constant-propagated and no shared read/write event is recorded for it.
  /// This lets goto-symex fold a loop induction variable that happens to be
  /// declared at file scope, and hence stop unwinding when its guard becomes
  /// false, just as it already does for a genuine local.
  ///
  /// Null unless the lazy_po/--rounds encoding is active; the default
  /// (non---rounds) CBMC behaviour is therefore completely unaffected.
  const std::unordered_set<irep_idt> *thread_exclusive = nullptr;

  /// \return true if \p identifier is provably accessed by at most one thread
  bool is_thread_exclusive(const irep_idt &identifier) const
  {
    return thread_exclusive != nullptr &&
           thread_exclusive->find(identifier) != thread_exclusive->end();
  }

  goto_programt::const_targett saved_target;

  /// \brief This state is saved, with the PC pointing to the target of a GOTO
  bool has_saved_jump_target;

  /// \brief This state is saved, with the PC pointing to the next instruction
  /// of a GOTO
  bool has_saved_next_instruction;

  /// \brief Should the additional validation checks be run?
  bool run_validation_checks;

  unsigned total_vccs = 0;
  unsigned remaining_vccs = 0;

  /// Drops an L1 name from the local L2 map
  void drop_existing_l1_name(const irep_idt &l1_identifier)
  {
    level2.current_names.erase(l1_identifier);
  }

  /// Drops an L1 name from the local L2 map
  void drop_l1_name(const irep_idt &l1_identifier)
  {
    level2.current_names.erase_if_exists(l1_identifier);
  }

  std::function<std::size_t(const irep_idt &)> get_l2_name_provider() const
  {
    return fresh_l2_name_provider;
  }

  /// Returns true if \p lvalue is a read-only object, such as the null object
  static bool is_read_only_object(const exprt &lvalue)
  {
    // Note ID_constant can occur due to a partial write to a string constant,
    // (i.e. something like byte_extract int from "hello" offset 2), which
    // simplifies to a plain constant.
    return lvalue.id() == ID_string_constant || lvalue.id() == ID_null_object ||
           lvalue.id() == "zero_string" || lvalue.id() == "is_zero_string" ||
           lvalue.id() == "zero_string_length" || lvalue.id() == ID_constant ||
           lvalue.id() == ID_array;
  }

private:
  std::function<std::size_t(const irep_idt &)> fresh_l2_name_provider;

  /// \brief Dangerous, do not use
  ///
  /// Copying a state S1 to S2 risks S2 pointing to a deallocated
  /// symex_target_equationt if S1 (and the symex_target_equationt that its
  /// `symex_target` member points to) go out of scope. If your class has a
  /// goto_symex_statet member and needs a copy constructor, copy instances
  /// of this class using the public two-argument copy constructor
  /// constructor to ensure that the copy points to an allocated
  /// symex_target_equationt. The two-argument copy constructor uses this
  /// private copy constructor as a delegate.
  goto_symex_statet(const goto_symex_statet &other) = default;
};

#endif // CPROVER_GOTO_SYMEX_GOTO_SYMEX_STATE_H
