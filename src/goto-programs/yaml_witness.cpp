/*******************************************************************\

Module: Violation Witnesses in the YAML Format

\*******************************************************************/

/// \file
/// Violation witnesses in the YAML format of sv-witnesses (version 2.2)
///
/// What a validator needs to replay a concurrent violation, and what this
/// writes:
///  - thread creations: a `function_enter` waypoint on every pthread_create
///    the trace executes (its SPAWN step, which carries the call site), by
///    the creating thread. The k-th of them in the
///    witness names the created thread `thread_id: k` (sv-witnesses,
///    Witness-Format.md, "Thread ID"); symex numbers threads its own way, so
///    the trace's thread numbers are mapped onto that order.
///  - the violation: one `target` waypoint at the statement that violates the
///    property -- for unreach-call the call of reach_error, not the assertion
///    inside it -- or, for a data race, the two racing accesses together in a
///    multi-follow segment, which leaves them unordered as a race is. Both
///    encodings put exactly those two accesses in the trace (under --rounds
///    build_goto_trace reads them from the phase symbols of the model).
/// No assumptions or branchings yet: a validator searches for the interleaving
/// between the waypoints. A witness the validator cannot confirm scores as an
/// unconfirmed answer, which is what a missing witness scores too.

#include "yaml_witness.h"

#include <util/optional.h>
#include <util/source_location.h>

#include "goto_trace.h"

#include <cctype>
#include <fstream>
#include <map>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

namespace
{
struct waypointt
{
  std::string type;
  source_locationt location;
  /// 0 when not known; the column is optional in the format
  std::size_t column;
  /// the line, when it is not the location's (a call over several lines)
  std::size_t line;
  std::size_t thread_id;
};
} // namespace

static bool usable(const source_locationt &location)
{
  return !location.is_nil() && !location.get_file().empty() &&
         !location.get_line().empty() && !location.is_built_in();
}

static std::string quoted(const std::string &s)
{
  std::string result = "'";
  for(const char c : s)
  {
    if(c == '\'')
      result += "''";
    else
      result += c;
  }
  return result + "'";
}

static std::string base_name(const std::string &path)
{
  const auto slash = path.find_last_of('/');
  return slash == std::string::npos ? path : path.substr(slash + 1);
}

/// Where the `)` that closes the call of \p callee on the line of
/// \p location is, which is where a `function_enter` waypoint points:
/// (line, column), both 1-based; a call can go on over the next lines. (0, 0)
/// when the call is not found.
static std::pair<std::size_t, std::size_t>
call_closing_parenthesis(const source_locationt &location, const std::string &callee)
{
  const auto path = location.full_path();
  std::ifstream in(path.has_value() ? *path : id2string(location.get_file()));
  const auto line_nr = std::stoul(id2string(location.get_line()));
  std::string line;
  for(std::size_t i = 0; i < line_nr; ++i)
  {
    if(!std::getline(in, line))
      return {0, 0};
  }
  for(auto at = line.find(callee); at != std::string::npos;
      at = line.find(callee, at + 1))
  {
    std::size_t open = at + callee.size();
    while(open < line.size() && (line[open] == ' ' || line[open] == '\t'))
      ++open;
    if(open == line.size() || line[open] != '(')
      continue;
    int depth = 0;
    std::size_t current = line_nr;
    for(std::size_t i = open;; ++i)
    {
      if(i == line.size())
      {
        // the arguments go on: a few lines at most
        if(current - line_nr == 20 || !std::getline(in, line))
          return {0, 0};
        ++current;
        i = 0;
        if(line.empty())
        {
          i = static_cast<std::size_t>(-1);
          continue;
        }
      }
      if(line[i] == '(')
        ++depth;
      else if(line[i] == ')' && --depth == 0)
        return {current, i + 1};
    }
  }
  return {0, 0};
}

/// The only call of \p callee in the file of \p location, outside its
/// definition: (line, column), both 1-based, the column that of the name.
/// (0, 0) when there is none or more than one.
static std::pair<std::size_t, std::size_t>
only_call_site(const source_locationt &location, const std::string &callee)
{
  const auto path = location.full_path();
  std::ifstream in(path.has_value() ? *path : id2string(location.get_file()));
  std::pair<std::size_t, std::size_t> found{0, 0};
  std::string line;
  for(std::size_t line_nr = 1; std::getline(in, line); ++line_nr)
  {
    for(auto at = line.find(callee); at != std::string::npos;
        at = line.find(callee, at + 1))
    {
      const bool word_start =
        at == 0 || !(std::isalnum(line[at - 1]) || line[at - 1] == '_');
      std::size_t open = at + callee.size();
      while(open < line.size() && (line[open] == ' ' || line[open] == '\t'))
        ++open;
      if(!word_start || open == line.size() || line[open] != '(')
        continue;
      // a definition or declaration: a type before the name
      const auto before = line.find_last_not_of(" \t", at == 0 ? 0 : at - 1);
      if(
        at != 0 && before != std::string::npos &&
        (std::isalnum(line[before]) || line[before] == '_' ||
         line[before] == '*'))
        continue;
      if(found.first != 0)
        return {0, 0};
      found = {line_nr, at + 1};
    }
  }
  return found;
}

/// One waypoint in flow style, so that a segment is one line of the witness
static std::string waypoint_yaml(const waypointt &waypoint)
{
  std::string result = "{waypoint: {type: " + quoted(waypoint.type) +
                       ", action: 'follow', location: {file_name: " +
                       quoted(base_name(id2string(waypoint.location.get_file()))) +
                       ", line: " +
                       (waypoint.line != 0 ? std::to_string(waypoint.line)
                                           : id2string(waypoint.location.get_line()));
  if(waypoint.column != 0)
    result += ", column: " + std::to_string(waypoint.column);
  return result + "}, thread_id: " + std::to_string(waypoint.thread_id) + "}}";
}

bool yaml_violation_content(
  const goto_tracet &goto_trace,
  const namespacet &,
  std::ostream &out)
{
  // the failing assertion: the trace ends with it
  auto failed = goto_trace.steps.end();
  for(auto it = goto_trace.steps.begin(); it != goto_trace.steps.end(); ++it)
  {
    if(it->is_assert() && !it->cond_value)
      failed = it;
  }
  if(failed == goto_trace.steps.end())
    return false;
  // Under --rounds the race assertion is made at the first step of the
  // equation (lazy_pot::handling_datarace), so its property id is whatever
  // that step's is -- `.recursion` on a plain main; only its comment names it.
  const bool data_race =
    failed->comment == "datarace" ||
    id2string(failed->property_id).find("datarace") != std::string::npos;

  // the steps the witness points to as the violation
  std::vector<goto_tracet::stepst::const_iterator> target_steps;
  // where the target goes when the trace does not show the call of
  // reach_error (line, column); (0, 0) otherwise
  std::pair<std::size_t, std::size_t> reach_error_call{0, 0};
  if(data_race)
  {
    // the two racing accesses: shared accesses reach the trace only as the
    // pair the datarace constraint blames
    auto second = goto_trace.steps.end();
    auto first = goto_trace.steps.end();
    for(auto it = goto_trace.steps.begin(); it != goto_trace.steps.end(); ++it)
    {
      if(!it->is_shared_read() && !it->is_shared_write())
        continue;
      if(second == goto_trace.steps.end() || second->thread_nr != it->thread_nr)
        first = second;
      second = it;
    }
    if(first == goto_trace.steps.end())
      return false;
    target_steps = {first, second};
  }
  else
  {
    // unreach-call fails inside reach_error, or in a function it calls --
    // assert(0) in a .c task fails in the library's __assert_fail -- and the
    // violation is the call of reach_error. The target was the assertion
    // there (line of reach_error's body), which ESBMC rejects: it confirmed
    // unreach-reachable-capacity-input-scanf with the target on the call.
    // The calls open in the failing thread, innermost last:
    std::vector<goto_tracet::stepst::const_iterator> open_calls;
    for(auto it = goto_trace.steps.begin(); it != failed; ++it)
    {
      if(it->thread_nr != failed->thread_nr)
        continue;
      if(it->type == goto_trace_stept::typet::FUNCTION_CALL)
        open_calls.push_back(it);
      else if(
        it->type == goto_trace_stept::typet::FUNCTION_RETURN &&
        !open_calls.empty())
        open_calls.pop_back();
    }
    auto at = failed;
    for(const auto &call : open_calls)
    {
      if(call->called_function == "reach_error")
      {
        at = call;
        break;
      }
    }
    target_steps = {at};
    // Under --rounds the trace can lack the calls that led to the failure
    // (unreach-reachable-capacity-input-scanf: the barrier wait, then the
    // failed assertion in reach_error): the call is then the only one in the
    // source, if there is only one.
    if(at == failed && failed->function_id == "reach_error")
      reach_error_call =
        only_call_site(failed->pc->source_location(), "reach_error");
  }

  // witness thread ids of the trace threads, assigned at their creation
  std::map<unsigned, std::size_t> thread_id{{0, 0}};

  // A thread created and joined right away runs as a plain call in the
  // thread that creates it (goto_convert_functions.cpp, the create/join
  // collapse), and the trace numbers its steps as that thread's. For the
  // witness it is a thread of its own: from the call to its return, the steps
  // of the trace thread belong to it. Per trace thread, the threads such calls
  // opened, with the call depth at which each returns.
  std::map<unsigned, std::vector<std::pair<std::size_t, std::size_t>>> inside;
  std::map<unsigned, std::size_t> depth;
  const auto id_of = [&](unsigned trace_thread) -> optionalt<std::size_t> {
    const auto &open = inside[trace_thread];
    if(!open.empty())
      return open.back().first;
    const auto id = thread_id.find(trace_thread);
    if(id == thread_id.end())
      return {};
    return id->second;
  };

  // Registrations in trace order; the creator of registration k (1-based) is
  // creator[k-1], a registration number itself (0 = main).
  std::vector<waypointt> registrations;
  std::vector<waypointt> targets;
  const auto register_thread = [&](
                                 const source_locationt &location,
                                 std::size_t creator) {
    const auto closing = call_closing_parenthesis(location, "pthread_create");
    registrations.push_back(
      {"function_enter", location, closing.second, closing.first, creator});
    return registrations.size();
  };
  for(auto it = goto_trace.steps.begin(); it != goto_trace.steps.end(); ++it)
  {
    for(const auto &target : target_steps)
    {
      if(target != it)
        continue;
      const source_locationt &location = it->pc->source_location();
      const auto id = id_of(it->thread_nr);
      if(!usable(location) || !id.has_value())
        return false;
      targets.push_back(
        {"target", location, reach_error_call.second, reach_error_call.first,
         *id});
    }

    if(it->type == goto_trace_stept::typet::SPAWN)
    {
      const source_locationt &location = it->spawn_call_location;
      const auto creator = id_of(it->thread_nr);
      if(usable(location) && creator.has_value())
        thread_id.emplace(
          it->spawned_thread_nr, register_thread(location, *creator));
      continue;
    }
    if(it->type == goto_trace_stept::typet::FUNCTION_RETURN)
    {
      auto &open = inside[it->thread_nr];
      if(!open.empty() && open.back().second == depth[it->thread_nr])
        open.pop_back();
      --depth[it->thread_nr];
      continue;
    }
    if(it->type != goto_trace_stept::typet::FUNCTION_CALL)
      continue;
    ++depth[it->thread_nr];

    const source_locationt &location = it->pc->source_location();
    if(!location.get_bool("#collapsed_pthread_create"))
      continue;
    const auto creator = id_of(it->thread_nr);
    if(!usable(location) || !creator.has_value())
      continue;
    inside[it->thread_nr].emplace_back(
      register_thread(location, *creator), depth[it->thread_nr]);
  }
  if(targets.size() != target_steps.size())
    return false;

  // Only the threads of the violation and the threads that created them are
  // registered. The time a spawn gets in the trace is not precise (it has no
  // clock of its own), so another thread's creation could be placed before
  // one it in fact follows, and a witness that demands that order describes
  // no execution; such a thread is left unnamed, which the format allows. A
  // creator is registered before what it creates.
  std::vector<bool> needed(registrations.size() + 1, false);
  for(const auto &target : targets)
  {
    for(std::size_t k = target.thread_id; k != 0 && !needed[k];
        k = registrations[k - 1].thread_id)
    {
      needed[k] = true;
    }
  }
  std::vector<std::size_t> order;
  std::vector<std::size_t> renumbered(registrations.size() + 1, 0);
  for(bool progress = true; progress;)
  {
    progress = false;
    for(std::size_t k = 1; k <= registrations.size(); ++k)
    {
      const std::size_t creator = registrations[k - 1].thread_id;
      if(
        needed[k] && renumbered[k] == 0 &&
        (creator == 0 || renumbered[creator] != 0))
      {
        order.push_back(k);
        renumbered[k] = order.size();
        progress = true;
      }
    }
  }

  for(const std::size_t k : order)
  {
    waypointt waypoint = registrations[k - 1];
    waypoint.thread_id = renumbered[waypoint.thread_id];
    out << "- segment: [" << waypoint_yaml(waypoint) << "]\n";
  }
  out << "- segment: [";
  for(std::size_t i = 0; i < targets.size(); ++i)
  {
    waypointt waypoint = targets[i];
    waypoint.thread_id = renumbered[waypoint.thread_id];
    out << (i == 0 ? "" : ", ") << waypoint_yaml(waypoint);
  }
  out << "]\n";
  return true;
}
