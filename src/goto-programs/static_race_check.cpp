/*******************************************************************\

Module: Loop-independent data-race freedom check

\*******************************************************************/

/// \file
/// A sound, incomplete check that a program has no data race, decided on
/// the goto program before any unwinding, so loops of any length are no
/// obstacle. It answers RACE-FREE only when every pair of conflicting
/// accesses to a shared object from code that can run concurrently is
/// either ordered by thread creation/join in main or protected by a common
/// lock (or both are in atomic sections). Everything it cannot decide
/// exactly makes it answer UNKNOWN:
///  - threads are created only by pthread_create called in main's own body,
///    with a constant start routine and a NULL argument; a creation inside
///    a loop of main is an unbounded number of instances, concurrent with
///    each other; a join removes a thread only when its argument is the
///    thread-id variable written by exactly one, non-looping creation and
///    nothing else writes that variable or takes its address;
///  - a shared object is a global variable (named, or an array or struct as
///    a whole), or the heap block a global pointer points to when that
///    pointer is assigned only fresh allocations (malloc/calloc, directly or
///    returned by a function) and only before the first thread is created;
///    a dereference whose target cannot be traced to such a pointer, to a
///    local object, or to memory the thread allocated itself, is UNKNOWN;
///  - locks are pthread mutexes named by a constant address; a lock taken
///    through a pointer is not counted, and an unlock through one releases
///    every lock (both only make the answer UNKNOWN more often);
///  - calls of functions without a body that take pointers, function
///    pointers, inline assembly, __CPROVER_ASYNC, pthread_once and thread
///    keys (they run code we do not follow) are UNKNOWN.
/// Accesses of main before the first creation and after every thread has
/// been joined run alone and are never part of a race.

#include "static_race_check.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/expr_util.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <analyses/natural_loops.h>

#include "goto_model.h"

#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <vector>

bool type_is_atomic(const typet &type); // symex_target_equation_deagle.cpp

namespace
{
struct statet
{
  std::set<std::string> locks; // must-held
  std::set<unsigned> alive;    // may-alive thread sites (main only)
  bool reached = false;

  bool operator==(const statet &o) const
  {
    return reached == o.reached && locks == o.locks && alive == o.alive;
  }
  bool operator<(const statet &o) const
  {
    if(locks != o.locks)
      return locks < o.locks;
    return alive < o.alive;
  }
};

statet join(const statet &a, const statet &b)
{
  if(!a.reached)
    return b;
  if(!b.reached)
    return a;
  statet r;
  r.reached = true;
  for(const auto &l : a.locks)
    if(b.locks.count(l))
      r.locks.insert(l);
  r.alive = a.alive;
  r.alive.insert(b.alive.begin(), b.alive.end());
  return r;
}

struct accesst
{
  std::string object;
  bool write;
  std::set<std::string> locks;
  int context;              // -1 main, else thread function index
  std::set<unsigned> alive; // main only
  std::string where;
};

struct unknownt
{
  std::string reason;
};

class checkert
{
public:
  checkert(const goto_modelt &m) : model(m), ns(m.symbol_table)
  {
  }

  std::string run();

private:
  const goto_modelt &model;
  namespacet ns;

  // thread sites
  struct sitet
  {
    irep_idt function;   // start routine
    bool multi = false;  // created in a loop
    irep_idt tid;        // thread-id variable, empty if not joinable
    std::set<unsigned> alive_at_create;
  };
  std::vector<sitet> sites;
  std::map<irep_idt, int> thread_index; // start routine -> context
  std::vector<irep_idt> thread_functions;
  std::map<goto_programt::const_targett, unsigned> site_of;

  std::vector<accesst> accesses;
  std::set<irep_idt> fresh_roots; // global pointers holding fresh blocks only
  std::set<irep_idt> tid_written_elsewhere;

  // per call: current context
  int context = -1;
  bool recording = false;
  std::vector<irep_idt> call_stack;
  // a pointer parameter takes the root of its argument at the call; a mutex
  // parameter, the exact lock its argument names
  struct bindingt
  {
    irep_idt function;
    std::map<irep_idt, std::string> root, lock;
    std::string key() const
    {
      std::string k;
      for(const auto &r : root)
        k += id2string(r.first) + "=" + r.second + ";";
      for(const auto &l : lock)
        k += id2string(l.first) + "~" + l.second + ";";
      return k;
    }
  };
  std::vector<bindingt> bindings;
  std::map<std::pair<std::pair<irep_idt, std::string>, statet>, statet> summary;

  // parameter identifiers from the function's type (the goto function's
  // own list can be empty)
  std::vector<irep_idt> params_of(const irep_idt &fn) const
  {
    std::vector<irep_idt> r;
    const symbolt *sym;
    if(ns.lookup(fn, sym) || sym->type.id() != ID_code)
      return r;
    for(const auto &p : to_code_type(sym->type).parameters())
      r.push_back(p.get_identifier());
    return r;
  }

  const bindingt *binding_of(const irep_idt &fn) const
  {
    if(!bindings.empty() && bindings.back().function == fn)
      return &bindings.back();
    return nullptr;
  }

  [[noreturn]] void unknown(const std::string &why)
  {
    throw unknownt{why};
  }

  const goto_functionst::goto_functiont *body(const irep_idt &f) const
  {
    auto it = model.goto_functions.function_map.find(f);
    if(it == model.goto_functions.function_map.end() || !it->second.body_available())
      return nullptr;
    return &it->second;
  }

  bool is_global(const symbol_exprt &s) const
  {
    const symbolt *sym;
    if(ns.lookup(s.get_identifier(), sym))
      return false;
    if(!sym->is_static_lifetime || sym->is_thread_local)
      return false;
    if(sym->type.id() == ID_code)
      return false;
    const std::string n = id2string(sym->name);
    if(n.rfind("__CPROVER", 0) == 0)
      return false;
    return true;
  }

  bool is_atomic_symbol(const irep_idt &id) const
  {
    const symbolt *sym;
    if(ns.lookup(id, sym))
      return false;
    return type_is_atomic(sym->type);
  }

  // --- pointer roots ------------------------------------------------------
  // "G:<name>" fresh block of global G, "LOCAL" thread-private, "" unknown
  std::map<std::pair<irep_idt, irep_idt>, std::string> local_root_cache;

  std::string root_of(const exprt &p, const irep_idt &fn, int depth = 0)
  {
    if(depth > 20)
      return "";
    if(p.id() == ID_typecast)
      return root_of(to_typecast_expr(p).op(), fn, depth + 1);
    if(p.id() == ID_plus || p.id() == ID_minus)
    {
      for(const auto &op : p.operands())
        if(op.type().id() == ID_pointer)
          return root_of(op, fn, depth + 1);
      return "";
    }
    if(p.id() == ID_address_of)
    {
      exprt o = to_address_of_expr(p).object();
      while(o.id() == ID_index || o.id() == ID_member)
        o = o.operands()[0];
      if(o.id() == ID_symbol)
      {
        const auto &s = to_symbol_expr(o);
        if(is_global(s))
          return "S:" + id2string(s.get_identifier());
        return "LOCAL";
      }
      if(o.id() == ID_string_constant)
        return "LOCAL";
      return "";
    }
    if(p.id() == ID_symbol)
    {
      const auto &s = to_symbol_expr(p);
      if(is_global(s))
        return fresh_roots.count(s.get_identifier())
                 ? "G:" + id2string(s.get_identifier())
                 : "";
      return local_root(s.get_identifier(), fn, depth);
    }
    if(p.is_constant())
      return "LOCAL"; // NULL or an integer address: no shared object
    return "";
  }

  // flow-insensitive: every assignment to the local gives the same root
  std::string local_root(const irep_idt &l, const irep_idt &fn, int depth)
  {
    // a parameter takes the root of its argument at the current call
    for(const auto &p : params_of(fn))
      if(p == l)
      {
        const bindingt *b = binding_of(fn);
        if(b == nullptr || !b->root.count(l))
          return "";
        return b->root.at(l);
      }
    auto key = std::make_pair(fn, l);
    auto c = local_root_cache.find(key);
    if(c != local_root_cache.end())
      return c->second;
    local_root_cache[key] = ""; // cycle guard
    const auto *f = body(fn);
    if(f == nullptr)
      return "";
    std::string root;
    bool any = false;
    forall_goto_program_instructions(it, f->body)
    {
      std::string r;
      bool assigns = false;
      if(it->is_assign() && it->assign_lhs().id() == ID_symbol &&
         to_symbol_expr(it->assign_lhs()).get_identifier() == l)
      {
        assigns = true;
        r = root_of(it->assign_rhs(), fn, depth + 1);
      }
      else if(it->is_function_call() && it->call_lhs().id() == ID_symbol &&
              to_symbol_expr(it->call_lhs()).get_identifier() == l)
      {
        assigns = true;
        r = call_root(*it, fn);
      }
      if(it->is_decl() || !assigns)
        continue;
      if(r.empty() || (any && r != root))
      {
        local_root_cache[key] = "";
        return "";
      }
      root = r;
      any = true;
    }
    if(!any || escapes(l, fn))
      root = "";
    local_root_cache[key] = root;
    return root;
  }

  // a fresh local block stays private unless its address leaves the function
  bool escapes(const irep_idt &l, const irep_idt &fn)
  {
    const auto *f = body(fn);
    forall_goto_program_instructions(it, f->body)
    {
      if(it->is_assign())
      {
        const exprt &lhs = it->assign_lhs();
        bool lhs_local = lhs.id() == ID_symbol &&
                         !is_global(to_symbol_expr(lhs));
        if(!lhs_local && mentions(it->assign_rhs(), l))
          return true;
      }
      if(it->is_function_call())
      {
        const exprt &fe = it->call_function();
        irep_idt callee =
          fe.id() == ID_symbol ? to_symbol_expr(fe).get_identifier() : irep_idt();
        if(callee == "free")
          continue;
        for(const auto &a : it->call_arguments())
          if(mentions(a, l))
            return true;
      }
    }
    return false;
  }

  static bool mentions(const exprt &e, const irep_idt &l)
  {
    if(e.id() == ID_symbol && to_symbol_expr(e).get_identifier() == l)
      return true;
    if(e.id() == ID_dereference || e.id() == ID_index)
    {
      // a value loaded through the pointer is not the pointer
      if(e.id() == ID_dereference)
        return false;
    }
    for(const auto &op : e.operands())
      if(mentions(op, l))
        return true;
    return false;
  }

  std::string call_root(const goto_programt::instructiont &ins, const irep_idt &fn)
  {
    const exprt &fe = ins.call_function();
    if(fe.id() != ID_symbol)
      return "";
    irep_idt callee = to_symbol_expr(fe).get_identifier();
    if(callee == "malloc" || callee == "calloc" || callee == "__builtin_alloca" ||
       callee == "alloca")
      return "FRESH";
    const auto *f = body(callee);
    if(f == nullptr)
      return "";
    // a user function returning one fresh local block
    std::string root;
    forall_goto_program_instructions(it, f->body)
      if(it->is_set_return_value())
      {
        std::string r = root_of(it->return_value(), callee);
        if(r != "LOCAL_FRESH" && r != "FRESH")
          return "";
        root = "FRESH";
      }
    return root;
  }

  // --- expression walking -------------------------------------------------
  void access(const std::string &obj, bool write, const statet &s,
              const goto_programt::instructiont &ins)
  {
    if(!recording)
      return;
    if(context == -1 && s.alive.empty())
      return; // main alone
    accesst a;
    a.object = obj;
    a.write = write;
    a.locks = s.locks;
    a.context = context;
    a.alive = s.alive;
    a.where = ins.source_location().as_string();
    accesses.push_back(a);
  }

  bool concurrent_now(const statet &s) const
  {
    return context != -1 || !s.alive.empty();
  }

  void lvalue(const exprt &e, bool write, const statet &s,
              const goto_programt::instructiont &ins, const irep_idt &fn)
  {
    if(e.id() == ID_symbol)
    {
      const auto &sy = to_symbol_expr(e);
      if(is_global(sy) && !is_atomic_symbol(sy.get_identifier()))
        access(id2string(sy.get_identifier()), write, s, ins);
      return;
    }
    if(e.id() == ID_index)
    {
      const auto &ix = to_index_expr(e);
      rvalue(ix.index(), s, ins, fn);
      lvalue(ix.array(), write, s, ins, fn);
      return;
    }
    if(e.id() == ID_member)
    {
      lvalue(to_member_expr(e).compound(), write, s, ins, fn);
      return;
    }
    if(e.id() == ID_dereference)
    {
      const exprt &p = to_dereference_expr(e).pointer();
      rvalue(p, s, ins, fn);
      if(!concurrent_now(s))
        return;
      std::string r = root_of(p, fn);
      if(r.empty())
        unknown("dereference of an untracked pointer at " +
                ins.source_location().as_string());
      if(r.rfind("G:", 0) == 0)
        access("heap@" + r.substr(2), write, s, ins);
      else if(r.rfind("S:", 0) == 0)
      {
        if(!is_atomic_symbol(r.substr(2)))
          access(r.substr(2), write, s, ins);
      }
      // LOCAL / FRESH: private
      return;
    }
    if(e.id() == ID_typecast)
    {
      lvalue(to_typecast_expr(e).op(), write, s, ins, fn);
      return;
    }
    if(e.id() == ID_byte_extract_little_endian ||
       e.id() == ID_byte_extract_big_endian)
    {
      rvalue(e.operands()[1], s, ins, fn);
      lvalue(e.operands()[0], write, s, ins, fn);
      return;
    }
    if(e.id() == ID_if)
    {
      rvalue(e.operands()[0], s, ins, fn);
      lvalue(e.operands()[1], write, s, ins, fn);
      lvalue(e.operands()[2], write, s, ins, fn);
      return;
    }
    if(e.is_constant() || e.id() == ID_string_constant || e.id() == ID_nil)
      return;
    unknown("unsupported lvalue " + id2string(e.id()));
  }

  void rvalue(const exprt &e, const statet &s,
              const goto_programt::instructiont &ins, const irep_idt &fn)
  {
    if(e.id() == ID_symbol || e.id() == ID_index || e.id() == ID_member ||
       e.id() == ID_dereference)
    {
      lvalue(e, false, s, ins, fn);
      return;
    }
    if(e.id() == ID_address_of)
    {
      address(to_address_of_expr(e).object(), s, ins, fn);
      return;
    }
    for(const auto &op : e.operands())
      rvalue(op, s, ins, fn);
  }

  // the address of an lvalue reads only the indices and pointers in it
  void address(const exprt &e, const statet &s,
               const goto_programt::instructiont &ins, const irep_idt &fn)
  {
    if(e.id() == ID_index)
    {
      rvalue(to_index_expr(e).index(), s, ins, fn);
      address(to_index_expr(e).array(), s, ins, fn);
    }
    else if(e.id() == ID_member)
      address(to_member_expr(e).compound(), s, ins, fn);
    else if(e.id() == ID_dereference)
      rvalue(to_dereference_expr(e).pointer(), s, ins, fn);
  }

  // --- lock ids -------------------------------------------------------------
  std::string lock_id(const exprt &arg, const irep_idt &fn) const
  {
    exprt a = arg;
    while(a.id() == ID_typecast)
      a = to_typecast_expr(a).op();
    if(a.id() == ID_symbol)
    {
      const bindingt *b = binding_of(fn);
      irep_idt v = to_symbol_expr(a).get_identifier();
      if(b != nullptr && b->lock.count(v))
        return b->lock.at(v);
      return "";
    }
    if(a.id() != ID_address_of)
      return "";
    exprt o = to_address_of_expr(a).object();
    std::string suffix;
    while(o.id() == ID_index || o.id() == ID_member)
    {
      if(o.id() == ID_index)
      {
        const auto &i = to_index_expr(o).index();
        if(!i.is_constant())
          return "";
        mp_integer v;
        if(to_integer(to_constant_expr(i), v))
          return "";
        suffix = "[" + integer2string(v) + "]" + suffix;
        o = to_index_expr(o).array();
      }
      else
      {
        suffix = "." + id2string(to_member_expr(o).get_component_name()) + suffix;
        o = to_member_expr(o).compound();
      }
    }
    if(o.id() != ID_symbol)
      return "";
    return id2string(to_symbol_expr(o).get_identifier()) + suffix;
  }

  // --- the transfer function ------------------------------------------------
  statet step(goto_programt::const_targett it, statet s, const irep_idt &fn,
              const goto_programt &prog, const natural_loopst *loops)
  {
    const auto &ins = *it;
    if(ins.is_assign())
    {
      rvalue(ins.assign_rhs(), s, ins, fn);
      lvalue(ins.assign_lhs(), true, s, ins, fn);
      if(ins.assign_lhs().id() == ID_symbol)
      {
        irep_idt v = to_symbol_expr(ins.assign_lhs()).get_identifier();
        if(fresh_roots.count(v) && (context != -1 || !s.alive.empty()))
          unknown("fresh pointer reassigned while threads run");
      }
    }
    else if(ins.is_goto() || ins.is_assume() || ins.is_assert())
      rvalue(ins.condition(), s, ins, fn);
    else if(ins.is_set_return_value())
      rvalue(ins.return_value(), s, ins, fn);
    else if(ins.is_atomic_begin())
      s.locks.insert("__ATOMIC__");
    else if(ins.is_atomic_end())
      s.locks.erase("__ATOMIC__");
    else if(ins.is_start_thread() || ins.is_end_thread() || ins.is_throw() ||
            ins.is_catch())
      unknown("unsupported instruction in user code");
    else if(ins.is_other())
    {
      const irep_idt st = ins.get_other().get_statement();
      if(st == ID_expression)
        rvalue(ins.get_other().op0(), s, ins, fn);
      else if(st == ID_array_set || st == ID_havoc_object)
      {
        if(!ins.get_other().operands().empty())
          lvalue(dereference_exprt(ins.get_other().op0()), true, s, ins, fn);
        for(std::size_t i = 1; i < ins.get_other().operands().size(); i++)
          rvalue(ins.get_other().operands()[i], s, ins, fn);
      }
      else if(st == ID_printf || st == ID_input || st == ID_output)
      {
        for(const auto &op : ins.get_other().operands())
          rvalue(op, s, ins, fn);
      }
      else
        unknown("unsupported statement " + id2string(st));
    }
    else if(ins.is_function_call())
      s = call(it, s, fn, loops);
    return s;
  }

  statet call(goto_programt::const_targett it, statet s, const irep_idt &fn,
              const natural_loopst *loops)
  {
    const auto &ins = *it;
    const exprt &fe = ins.call_function();
    if(fe.id() != ID_symbol)
      unknown("call through a function pointer");
    const irep_idt callee = to_symbol_expr(fe).get_identifier();
    const std::string c = id2string(callee);
    const auto &args = ins.call_arguments();
    auto read_args = [&]() {
      for(const auto &a : args)
        rvalue(a, s, ins, fn);
    };
    auto write_lhs = [&]() {
      if(ins.call_lhs().is_not_nil())
      {
        lvalue(ins.call_lhs(), true, s, ins, fn);
        if(ins.call_lhs().id() == ID_symbol &&
           fresh_roots.count(to_symbol_expr(ins.call_lhs()).get_identifier()) &&
           (context != -1 || !s.alive.empty()))
          unknown("fresh pointer reassigned while threads run");
      }
    };

    if(c == "pthread_create")
    {
      if(fn != "main" || context != -1)
        unknown("thread created outside main");
      if(args.size() != 4)
        unknown("pthread_create arity");
      exprt f = args[2];
      while(f.id() == ID_typecast)
        f = to_typecast_expr(f).op();
      if(f.id() != ID_address_of ||
         to_address_of_expr(f).object().id() != ID_symbol)
        unknown("thread start routine not constant");
      exprt arg = args[3];
      while(arg.id() == ID_typecast)
        arg = to_typecast_expr(arg).op();
      if(!arg.is_constant())
        unknown("thread argument not NULL");
      // the write to the thread-id variable happens before the thread runs
      lvalue(dereference_exprt(args[0]), true, s, ins, fn);
      rvalue(args[1], s, ins, fn);
      auto st = site_of.find(it);
      unsigned id;
      if(st == site_of.end())
      {
        id = sites.size();
        site_of[it] = id;
        sitet site;
        site.function =
          to_symbol_expr(to_address_of_expr(f).object()).get_identifier();
        for(const auto &l : loops->loop_map)
          if(l.second.contains(it))
            site.multi = true;
        exprt t = args[0];
        while(t.id() == ID_typecast)
          t = to_typecast_expr(t).op();
        if(!site.multi && t.id() == ID_address_of &&
           to_address_of_expr(t).object().id() == ID_symbol)
          site.tid = to_symbol_expr(to_address_of_expr(t).object()).get_identifier();
        sites.push_back(site);
        if(!thread_index.count(site.function))
        {
          thread_index[site.function] = thread_functions.size();
          thread_functions.push_back(site.function);
        }
      }
      else
        id = st->second;
      for(auto a : s.alive)
        sites[id].alive_at_create.insert(a);
      s.alive.insert(id);
      return s;
    }
    if(c == "pthread_join")
    {
      if(context != -1 || fn != "main")
      {
        read_args();
        if(args.size() > 1)
          lvalue(dereference_exprt(args[1]), true, s, ins, fn);
        return s;
      }
      read_args();
      if(args.size() > 1)
      {
        exprt r = args[1];
        while(r.id() == ID_typecast)
          r = to_typecast_expr(r).op();
        if(!r.is_constant())
          lvalue(dereference_exprt(args[1]), true, s, ins, fn);
      }
      exprt t = args[0];
      while(t.id() == ID_typecast)
        t = to_typecast_expr(t).op();
      if(t.id() == ID_symbol)
      {
        irep_idt v = to_symbol_expr(t).get_identifier();
        if(!tid_written_elsewhere.count(v))
          for(unsigned i = 0; i < sites.size(); i++)
            if(sites[i].tid == v)
            {
              bool in_loop = false;
              for(const auto &l : loops->loop_map)
                if(l.second.contains(it))
                  in_loop = true;
              if(!in_loop)
                s.alive.erase(i);
            }
      }
      return s;
    }
    if(c == "pthread_mutex_lock" || c == "pthread_spin_lock")
    {
      read_args();
      std::string id = lock_id(args[0], fn);
      if(!id.empty())
        s.locks.insert(id);
      return s;
    }
    if(c == "pthread_mutex_unlock" || c == "pthread_spin_unlock")
    {
      read_args();
      std::string id = lock_id(args[0], fn);
      if(id.empty())
        s.locks.clear();
      else
        s.locks.erase(id);
      return s;
    }
    if(c == "pthread_mutex_trylock" || c == "pthread_spin_trylock" ||
       c == "pthread_mutex_init" || c == "pthread_mutex_destroy" ||
       c == "pthread_cond_wait" || c == "pthread_cond_timedwait" ||
       c == "pthread_cond_signal" || c == "pthread_cond_broadcast" ||
       c == "pthread_cond_init" || c == "pthread_cond_destroy" ||
       c == "pthread_spin_init" || c == "pthread_spin_destroy" ||
       c == "pthread_self" || c == "pthread_exit" || c == "pthread_yield" ||
       c == "sched_yield" || c == "pthread_attr_init" ||
       c == "pthread_attr_destroy" || c == "pthread_attr_setdetachstate" ||
       c == "pthread_equal" || c == "usleep" || c == "sleep" ||
       c == "sem_wait" || c == "sem_post" || c == "sem_init" ||
       c == "sem_destroy" || c == "pthread_barrier_wait" ||
       c == "pthread_barrier_init" || c == "pthread_barrier_destroy" ||
       c == "pthread_detach" || c == "pthread_rwlock_rdlock" ||
       c == "pthread_rwlock_wrlock" || c == "pthread_rwlock_unlock" ||
       c == "pthread_rwlock_init" || c == "pthread_rwlock_destroy")
    {
      // synchronisation and thread bookkeeping on objects the program only
      // passes to the library; ignoring their ordering is conservative
      // (trylock and the read-write lock add no lock to the lockset; an
      // unlock of a read-write lock releases every lock)
      read_args();
      if(c == "pthread_rwlock_unlock")
        s.locks.clear();
      write_lhs();
      return s;
    }
    if(c == "malloc" || c == "calloc" || c == "alloca" ||
       c == "__builtin_alloca")
    {
      read_args();
      write_lhs();
      return s;
    }
    if(c == "free")
    {
      read_args();
      if(!args.empty())
        lvalue(dereference_exprt(args[0]), true, s, ins, fn);
      return s;
    }
    if(c == "memset")
    {
      read_args();
      lvalue(dereference_exprt(args[0]), true, s, ins, fn);
      write_lhs();
      return s;
    }
    if(c == "memcpy" || c == "memmove")
    {
      read_args();
      lvalue(dereference_exprt(args[0]), true, s, ins, fn);
      lvalue(dereference_exprt(args[1]), false, s, ins, fn);
      write_lhs();
      return s;
    }
    if(c == "pthread_once" || c == "pthread_key_create" || c == "atexit" ||
       c == "signal" || c == "setjmp" || c == "longjmp" ||
       c == "pthread_cleanup_push" || c == "pthread_setspecific" ||
       c == "pthread_getspecific")
      unknown("unsupported library call " + c);

    const auto *f = body(callee);
    if(f == nullptr)
    {
      // a function without a body: harmless only if it takes no pointer
      if(c.rfind("__VERIFIER_nondet", 0) != 0 && c != "__VERIFIER_assume" &&
         c != "__VERIFIER_error" && c != "reach_error" && c != "abort" &&
         c != "exit" && c != "__assert_fail" && c != "assert" &&
         c != "printf" && c != "puts" && c != "__CPROVER_assume" &&
         c != "__CPROVER_assert")
        for(const auto &a : args)
          if(a.type().id() == ID_pointer && !a.is_constant())
            unknown("call of " + c + " with a pointer and no body");
      read_args();
      write_lhs();
      return s;
    }
    // follow the callee; its parameters are locals
    read_args();
    for(const auto &g : call_stack)
      if(g == callee)
        unknown("recursion");
    if(call_stack.size() > 40)
      unknown("call depth");
    bindingt b;
    b.function = callee;
    const std::vector<irep_idt> prms = params_of(callee);
    for(std::size_t i = 0; i < args.size() && i < prms.size(); i++)
      if(args[i].type().id() == ID_pointer)
      {
        const irep_idt &prm = prms[i];
        std::string r = root_of(args[i], fn);
        if(!r.empty())
          b.root[prm] = r;
        std::string l = lock_id(args[i], fn);
        if(!l.empty())
          b.lock[prm] = l;
      }
    bindings.push_back(b);
    local_root_cache.clear();
    statet out = analyse(callee, s);
    bindings.pop_back();
    local_root_cache.clear();
    write_lhs();
    return out;
  }

  // --- intraprocedural fixpoint, then a recording pass ----------------------
  statet analyse(const irep_idt &fn, const statet &entry)
  {
    const auto *f = body(fn);
    INVARIANT(f != nullptr, "body");
    const goto_programt &prog = f->body;
    natural_loopst loops;
    loops(prog);

    const bindingt *bd = binding_of(fn);
    auto key = std::make_pair(std::make_pair(fn, bd ? bd->key() : std::string()), entry);
    if(!recording)
    {
      auto sm = summary.find(key);
      if(sm != summary.end())
        return sm->second;
    }

    call_stack.push_back(fn);
    std::map<goto_programt::const_targett, statet> in;
    in[prog.instructions.begin()] = entry;
    in[prog.instructions.begin()].reached = true;
    std::vector<goto_programt::const_targett> work{prog.instructions.begin()};
    statet exit_state;
    const bool was_recording = recording;
    recording = false; // fixpoint first
    std::size_t steps = 0;
    while(!work.empty())
    {
      if(++steps > 200000)
        unknown("fixpoint too long");
      auto it = work.back();
      work.pop_back();
      statet out = step(it, in[it], fn, prog, &loops);
      out.reached = true;
      if(it->is_end_function())
      {
        exit_state = join(exit_state, out);
        continue;
      }
      for(auto succ : prog.get_successors(it))
      {
        statet n = join(in[succ], out);
        if(!(n == in[succ]))
        {
          in[succ] = n;
          work.push_back(succ);
        }
      }
    }
    recording = was_recording;
    if(recording)
    {
      // every reached instruction once, with its final state
      forall_goto_program_instructions(it, prog)
        if(in.count(it) && in[it].reached)
          step(it, in[it], fn, prog, &loops);
    }
    call_stack.pop_back();
    summary[key] = exit_state;
    return exit_state;
  }

  void count_addresses(const exprt &e, std::map<irep_idt, int> &n)
  {
    if(e.id() == ID_address_of)
    {
      exprt o = to_address_of_expr(e).object();
      if(o.id() == ID_symbol)
        n[to_symbol_expr(o).get_identifier()]++;
    }
    for(const auto &op : e.operands())
      count_addresses(op, n);
  }

  void precompute()
  {
    std::map<irep_idt, int> addr;
    for(const auto &fp : model.goto_functions.function_map)
    {
      if(!fp.second.body_available())
        continue;
      forall_goto_program_instructions(it, fp.second.body)
      {
        if(it->is_assign())
        {
          count_addresses(it->assign_lhs(), addr);
          count_addresses(it->assign_rhs(), addr);
        }
        else if(it->is_function_call())
          for(const auto &a : it->call_arguments())
            count_addresses(a, addr);
        else if(it->has_condition())
          count_addresses(it->condition(), addr);
      }
    }
    for(const auto &a : addr)
      if(a.second > 1)
        tid_written_elsewhere.insert(a.first);
    // thread-id variables written other than by pthread_create
    for(const auto &fp : model.goto_functions.function_map)
    {
      if(!fp.second.body_available())
        continue;
      forall_goto_program_instructions(it, fp.second.body)
      {
        if(it->is_assign() && it->assign_lhs().id() == ID_symbol)
          tid_written_elsewhere.insert(
            to_symbol_expr(it->assign_lhs()).get_identifier());
      }
    }
    // fresh roots: global pointers whose every assignment is a fresh block
    // (or NULL), made in main; the check that main does it before creating
    // threads is in step()
    std::map<irep_idt, bool> candidate;
    for(const auto &fp : model.goto_functions.function_map)
    {
      if(!fp.second.body_available())
        continue;
      const irep_idt fn = fp.first;
      forall_goto_program_instructions(it, fp.second.body)
      {
        irep_idt v;
        std::string r;
        if(it->is_assign() && it->assign_lhs().id() == ID_symbol)
        {
          v = to_symbol_expr(it->assign_lhs()).get_identifier();
          exprt rhs = it->assign_rhs();
          while(rhs.id() == ID_typecast)
            rhs = to_typecast_expr(rhs).op();
          if(rhs.is_constant())
            r = "NULL";
          else if(rhs.id() == ID_symbol && !is_global(to_symbol_expr(rhs)))
          {
            // a local temporary holding one call result, copied into this
            // global and nowhere else
            const auto *f = body(fn);
            r = "";
            irep_idt t = to_symbol_expr(rhs).get_identifier();
            int defs = 0, uses = 0;
            std::string cr;
            forall_goto_program_instructions(jt, f->body)
            {
              if(jt->is_function_call() && jt->call_lhs().id() == ID_symbol &&
                 to_symbol_expr(jt->call_lhs()).get_identifier() == t)
              {
                defs++;
                cr = call_root(*jt, fn);
              }
              if(jt->is_assign() && jt->assign_lhs().id() == ID_symbol &&
                 to_symbol_expr(jt->assign_lhs()).get_identifier() == t)
                defs++;
              if(jt->is_assign() && mentions(jt->assign_rhs(), t))
                uses++;
              if(jt->is_function_call())
                for(const auto &a : jt->call_arguments())
                  if(mentions(a, t))
                    uses++;
            }
            if(defs == 1 && uses == 1)
              r = cr;
          }
        }
        else if(it->is_function_call() && it->call_lhs().id() == ID_symbol)
        {
          v = to_symbol_expr(it->call_lhs()).get_identifier();
          r = call_root(*it, fn);
        }
        else
          continue;
        const symbolt *sym;
        if(ns.lookup(v, sym) || !sym->is_static_lifetime ||
           sym->type.id() != ID_pointer)
          continue;
        bool ok = (r == "FRESH" || r == "NULL") &&
                  (fn == "main" || fn == "__CPROVER_initialize");
        if(!candidate.count(v))
          candidate[v] = ok;
        else
          candidate[v] = candidate[v] && ok;
      }
    }
    // a pointer copied into another global, or whose address is taken, is out
    for(auto &c : candidate)
      if(c.second)
        fresh_roots.insert(c.first);
  }

  bool conc_site(unsigned a, unsigned b) const
  {
    if(a == b)
      return sites[a].multi;
    return sites[a].alive_at_create.count(b) || sites[b].alive_at_create.count(a);
  }
};

std::string checkert::run()
{
  if(body("main") == nullptr)
    return "UNKNOWN (no main)";
  try
  {
    precompute();
    // main first: it discovers the thread sites
    context = -1;
    recording = true;
    statet entry;
    entry.reached = true;
    analyse("main", entry);
    // each start routine once, from an empty lockset
    for(std::size_t t = 0; t < thread_functions.size(); t++)
    {
      context = t;
      summary.clear();
      statet e;
      e.reached = true;
      analyse(thread_functions[t], e);
    }
  }
  catch(const unknownt &u)
  {
    return "UNKNOWN (" + u.reason + ")";
  }

  // pairs of accesses that may run at the same time
  std::map<std::string, std::vector<const accesst *>> by_object;
  for(const auto &a : accesses)
    by_object[a.object].push_back(&a);
  for(const auto &o : by_object)
  {
    const auto &v = o.second;
    for(std::size_t i = 0; i < v.size(); i++)
      for(std::size_t j = i; j < v.size(); j++)
      {
        const accesst &a = *v[i], &b = *v[j];
        if(!a.write && !b.write)
          continue;
        bool common = false;
        for(const auto &l : a.locks)
          if(b.locks.count(l))
            common = true;
        if(common)
          continue;
        bool conc = false;
        if(a.context == -1 && b.context == -1)
          conc = false; // main is one thread
        else if(a.context == -1 || b.context == -1)
        {
          const accesst &m = a.context == -1 ? a : b;
          const accesst &t = a.context == -1 ? b : a;
          for(auto s : m.alive)
            if(thread_index.at(sites[s].function) == t.context)
              conc = true;
        }
        else
        {
          for(unsigned s1 = 0; s1 < sites.size(); s1++)
            for(unsigned s2 = 0; s2 < sites.size(); s2++)
              if(thread_index.at(sites[s1].function) == a.context &&
                 thread_index.at(sites[s2].function) == b.context &&
                 conc_site(s1, s2))
                conc = true;
        }
        if(conc)
          return "UNKNOWN (possible race on " + o.first + ": " + a.where +
                 " / " + b.where + ")";
      }
  }
  return "RACE-FREE";
}
} // namespace

std::string static_race_check(const goto_modelt &goto_model)
{
  checkert c(goto_model);
  return c.run();
}
