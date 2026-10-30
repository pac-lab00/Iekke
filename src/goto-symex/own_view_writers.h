/*******************************************************************\

Module: Symbolic Execution

Author: Iekke

\*******************************************************************/

/// \file
/// --own-view-reads: read a shared object that no other thread changes after
/// the first spawn from the reading thread's own view of it.
///
/// A read of a shared object after the first spawn normally gets a fresh SSA
/// symbol, whose value the concurrency encoding picks among the writes to the
/// object, and constant propagation stops there. But when, after the first
/// spawn, the object is written by the reading thread alone, or by no thread
/// at all, the read can only see one value: the thread's own last write, or,
/// before it, the value the object had at the first spawn (every other thread
/// starts after main's prologue, and nothing writes the object between). A
/// race needs a write by another thread, and there is none. So the read is
/// renamed as a thread-local's: no shared read event, and constant
/// propagation applies.
///
/// That value is the object's L2 name (or propagated constant) in this
/// thread's state, provided three things hold for every object with at most
/// one post-spawn writer, which is what makes it a candidate:
///  - other threads' reads do not move its L2 name (they still take a fresh
///    symbol and an event, but its current name is put back afterwards), so
///    the state carries main's last value into the threads symexed after it;
///  - its writes keep the propagated constant, for the one thread that may
///    read it this way;
///  - branches are merged with phi functions, as a local's, in every thread:
///    main's prologue may have written it on one path before a spawn on that
///    path (otherwise the state after the join holds one path's value).
///
/// Who writes what after the first spawn is a property of the whole program,
/// so it comes from an earlier symex pass (the program is symexed twice when
/// it has threads, see multi_path_symex_only_checkert::generate_equation).
/// Every change of an L2 name after the first spawn is recorded with its
/// thread: assignments (a store through a pointer as the dereference resolves
/// it, a copy of a local into a new thread under the new thread's number, a
/// read inside an atomic section, which is an assignment), declarations and
/// deaths -- but not phi functions, which only name a merged value. After the
/// final pass the caller checks that every assumption it made still holds for
/// what that pass recorded, and symexes again otherwise.

#ifndef CPROVER_GOTO_SYMEX_OWN_VIEW_WRITERS_H
#define CPROVER_GOTO_SYMEX_OWN_VIEW_WRITERS_H

#include <util/irep.h>

#include <set>
#include <string>
#include <unordered_map>
#include <vector>

/// L1 object identifiers (field-sensitive leaves included) and the threads
/// that change their L2 names after the first spawn. A write to `s..a` changes
/// `s` and `s..a[[1]]..b` as well, but not `s..ab`.
class own_view_writerst
{
public:
  void record(const irep_idt &l1_identifier, unsigned thread)
  {
    auto &threads = exact[l1_identifier];
    if(!threads.insert(thread).second)
      return;
    for(const auto &prefix : prefixes(id2string(l1_identifier)))
      below[prefix].insert(thread);
  }

  void insert(const own_view_writerst &other)
  {
    for(const auto &entry : other.exact)
      for(const unsigned thread : entry.second)
        record(entry.first, thread);
  }

  /// The threads that change \p l1_identifier, a part of it, or an object
  /// enclosing it, after the first spawn.
  std::set<unsigned> writers(const irep_idt &l1_identifier) const
  {
    std::set<unsigned> result;
    const auto add = [&result](
                       const std::unordered_map<irep_idt, std::set<unsigned>> &m,
                       const irep_idt &id) {
      const auto it = m.find(id);
      if(it != m.end())
        result.insert(it->second.begin(), it->second.end());
    };
    add(exact, l1_identifier);
    add(below, l1_identifier);
    for(const auto &prefix : prefixes(id2string(l1_identifier)))
      add(exact, prefix);
    return result;
  }

  /// No thread but \p thread changes \p l1_identifier after the first spawn.
  bool only_by(const irep_idt &l1_identifier, unsigned thread) const
  {
    const std::set<unsigned> w = writers(l1_identifier);
    return w.empty() || (w.size() == 1 && *w.begin() == thread);
  }

  /// At most one thread changes \p l1_identifier after the first spawn.
  bool at_most_one(const irep_idt &l1_identifier) const
  {
    return writers(l1_identifier).size() <= 1;
  }

  void clear()
  {
    exact.clear();
    below.clear();
  }

private:
  std::unordered_map<irep_idt, std::set<unsigned>> exact;
  /// for every enclosing object of a recorded identifier
  std::unordered_map<irep_idt, std::set<unsigned>> below;

  /// The proper prefixes of \p s that end a component (before a `..member`
  /// or an `[[index]]`).
  static std::vector<std::string> prefixes(const std::string &s)
  {
    std::vector<std::string> result;
    for(std::size_t i = s.size(); i-- > 1;)
    {
      if((s[i - 1] == '.' && s[i] == '.') || (s[i - 1] == '[' && s[i] == '['))
        result.push_back(s.substr(0, i - 1));
    }
    return result;
  }
};

/// What a symex pass under --own-view-reads knows, records and assumes.
struct own_view_statet
{
  /// Post-spawn writers found by the earlier passes: what decisions use.
  own_view_writerst known;
  /// Post-spawn writers recorded by the current pass.
  own_view_writerst recorded;
  /// The threads that read each object after the first spawn, found by the
  /// earlier passes and recorded by the current one. An object is only
  /// treated if one of its readers may read it from its own view: phi
  /// functions for an object nobody reads that way cost and serve nothing
  /// (measured on pthread/stack-1, where they outweighed the reads saved).
  std::unordered_map<irep_idt, std::set<unsigned>> known_readers;
  std::unordered_map<irep_idt, std::set<unsigned>> recorded_readers;
  /// Assumptions made by the current pass: objects read from a thread's own
  /// view (with the reading threads), and objects treated as candidates
  /// (their L2 name kept across other threads' reads, phi-merged).
  std::unordered_map<irep_idt, std::set<unsigned>> read_by;
  std::set<irep_idt> candidates;
  /// Decisions are made only while this is set.
  bool active = false;
  /// Shared reads the current pass made from a thread's own view.
  std::size_t reads = 0;

  /// Some thread that reads \p l1_object after the first spawn is the only
  /// one that writes it then (or nobody writes it).
  bool useful(const irep_idt &l1_object) const
  {
    const auto it = known_readers.find(l1_object);
    if(it == known_readers.end())
      return false;
    for(const unsigned thread : it->second)
      if(known.only_by(l1_object, thread))
        return true;
    return false;
  }

  void start_pass()
  {
    reads = 0;
    recorded.clear();
    recorded_readers.clear();
    read_by.clear();
    candidates.clear();
  }

  /// Fold this pass's writers into \ref known.
  /// \return true if one of this pass's assumptions does not hold for them,
  ///   so the pass has to be repeated.
  bool finish_pass()
  {
    own_view_writerst all = known;
    all.insert(recorded);
    bool broken = false;
    for(const auto &entry : read_by)
      for(const unsigned thread : entry.second)
        if(!all.only_by(entry.first, thread))
          broken = true;
    for(const auto &id : candidates)
      if(!all.at_most_one(id))
        broken = true;
    known = std::move(all);
    for(const auto &entry : recorded_readers)
      known_readers[entry.first].insert(
        entry.second.begin(), entry.second.end());
    return broken;
  }
};

#endif // CPROVER_GOTO_SYMEX_OWN_VIEW_WRITERS_H
