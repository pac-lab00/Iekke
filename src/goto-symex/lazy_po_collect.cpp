/// \file
/// lazy_po: collection of shared events and assignment of atomic-block labels

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

// __SZH_DR_ADD_END__


/// Whether \p array is \p object itself (an L2 version of it). Only a `with`
/// over, or an index into, the event's own object gives the event's offset:
/// the value stored may index other arrays (`B[i] = A[j]` reads A at j), and
/// for an element field sensitivity has split off the event's object is the
/// element itself, which has no offset within it.
static bool
of_object(const exprt &array, const irep_idt &object)
{
  return is_ssa_expr(array) &&
         to_ssa_expr(array).get_l1_object_identifier() == object;
}

/// The offset of an access to \p object may be buried under an `if`: an
/// object field sensitivity does not split (of symbolic size) is stored as
/// `obj#4 == (p == &obj ? obj#3 with [k := v] : obj#2)`, a choice because
/// the pointer may point elsewhere. Collects into \p out the offset of every
/// `with` over, or index into, \p object under the if-chain (and under the
/// boolean and byte-extract wrappers below); false when two of them differ,
/// so the access keeps the default offset.
static bool with_index_under_if(
  const exprt &e,
  exprt &out,
  bool &found,
  const irep_idt &object)
{
  if(
    e.id() == ID_with && e.operands().size() == 3 &&
    of_object(to_with_expr(e).old(), object))
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
  if(e.id() == ID_index && of_object(to_index_expr(e).array(), object))
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
    return with_index_under_if(ife.true_case(), out, found, object) &&
           with_index_under_if(ife.false_case(), out, found, object);
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
      if(!with_index_under_if(op, out, found, object))
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
    return with_index_under_if(
      to_byte_extract_expr(e).op(), out, found, object);
  }
  // A read converted to another type, as `return datas[0]` converts a _Bool
  // element to the int being returned: `(int)(ptr == &obj ? obj[k] : ...)`.
  // The conversion does not change which element is read. Not looked
  // through, the read kept the default -1 while the other thread's write of
  // obj[k] had offset k, so the two never paired: a race on a heap array of
  // symbolic size was reported absent (pthread-race-challenges/
  // per-thread-array-join-counter-race-4, no-data-race, expected false).
  if(e.id() == ID_typecast)
    return with_index_under_if(to_typecast_expr(e).op(), out, found, object);
  return true;
}

/// \return l'offset dell'accesso se sotto gli `if` ce n'e' esattamente uno,
///   altrimenti nil.
/// The offset of an access to \p object read off the assignment that
/// follows its event, or nil. Two events of one variable race only at equal
/// locations, and an event whose offset is not found keeps the default -1,
/// which equals only another -1. That is needed: the read of an array's old
/// value that a store makes to build its update has no offset, and pairing
/// it with another thread's write at any offset would report races at
/// elements the program never reads. It is also a known incompleteness: a
/// genuine access at an unknown offset is not paired with an access at a
/// known one.
static exprt access_offset(const exprt &rhs, const irep_idt &object)
{
  exprt out = nil_exprt{};
  bool found = false;
  if(!with_index_under_if(rhs, out, found, object) || !found)
    return nil_exprt{};
  return out;
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
  // Whether each thread is between an atomic_begin and its atomic_end. An
  // ASSERT or ASSUME step does not carry an atomic_section_id --
  // symex_target_equationt::assertion and ::assumption never set one,
  // unlike shared_read and shared_write -- so this is the only way to tell
  // that it lies inside an atomic section.
  std::map<unsigned, bool> in_atomic_section;

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

    // For compute_round_bound: the child gets the next index in spawn order,
    // exactly as handling_active_threads numbers it (thread_created), and the
    // spawning thread is at the label that its write of the child's active
    // flag -- emitted just before this step -- was placed in.
    if(s_it->is_spawn())
      spawn_points[++spawns_seen] = {
        s_it->source.thread_nr, labels[s_it->source.thread_nr]};

    if(should_stage_trace_step(*s_it))
      pending_trace_steps[s_it->source.thread_nr].push_back(s_it);

    if(s_it->is_assert() || s_it->is_assume())
    {
      // Was `s_it->atomic_section_id == 0`, which is always true for these
      // steps (see in_atomic_section). So every check inside an atomic
      // section started a block of its own and split the section: with
      // --signed-overflow-check, the check on `count + 1` in
      // pthread_mutex_lock let another thread run between the lock's write
      // of its owner and of its count, and two threads held the mutex at once
      // (pthread-complex/workstealqueue_mutex-2, no-overflow).
      if(
        labels[s_it->source.thread_nr] == 0 ||
        !in_atomic_section[s_it->source.thread_nr])
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
      in_atomic_section[s_it->source.thread_nr] = true;
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
      in_atomic_section[s_it->source.thread_nr] = false;
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
        // an array access: the offset of the event's own object, under the
        // step's if-chain or bare (see access_offset)
        const exprt offset =
          next != ssa_steps.end() && next->is_assignment()
            ? access_offset(
                next->ssa_rhs, s_it->ssa_lhs.get_l1_object_identifier())
            : static_cast<exprt>(nil_exprt{});
        if(offset.is_not_nil())
          where = offset;
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
        // see the write site
        const exprt offset =
          next != ssa_steps.end() && next->is_assignment()
            ? access_offset(
                next->ssa_rhs, s_it->ssa_lhs.get_l1_object_identifier())
            : static_cast<exprt>(nil_exprt{});
        if(offset.is_not_nil())
          where = offset;
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
