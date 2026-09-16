/*******************************************************************\

Module: GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// GOTO Programs

#include "goto_check.h"

#include <util/cprover_prefix.h>
#include <util/options.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include "goto_model.h"
#include "remove_skip.h"

static void transform_assertions_assumptions(
  goto_programt &goto_program,
  bool enable_assertions,
  bool enable_built_in_assertions,
  bool enable_assumptions,
  const exprt *datarace_dummy_lhs)
{
  bool did_something = false;

  for(auto &instruction : goto_program.instructions)
  {
    if(instruction.is_assert())
    {
      bool is_user_provided =
        instruction.source_location().get_bool("user-provided");

      if(
        (is_user_provided && !enable_assertions &&
         instruction.source_location().get_property_class() != "error label") ||
        (!is_user_provided && !enable_built_in_assertions))
      {
        // __SZH_DR_ADD_BEGIN__
        // Under --datarace, turning a disabled user assertion into a skip
        // (the general case below) deletes its condition expression
        // outright -- silently dropping any memory read that exists only
        // inside the assertion, e.g. the SV-COMP "floating_read"
        // benchmark family, whose whole point is a read used solely by an
        // assert. Preserve those reads by evaluating the condition into a
        // dummy variable instead: the property check is still suppressed
        // (nothing ever reads the dummy back), and unlike turning it into
        // an assumption this adds no hard constraint that could rule out
        // a race-dependent value.
        if(
          is_user_provided && datarace_dummy_lhs != nullptr &&
          instruction.condition().type() == datarace_dummy_lhs->type())
        {
          exprt rhs = instruction.condition();
          instruction.turn_into_assignment(*datarace_dummy_lhs, rhs);
        }
        else
        {
          instruction.turn_into_skip();
        }
        // __SZH_DR_ADD_END__
        did_something = true;
      }
    }
    else if(instruction.is_assume())
    {
      if(!enable_assumptions)
      {
        instruction.turn_into_skip();
        did_something = true;
      }
    }
  }

  if(did_something)
    remove_skip(goto_program);
}

// __SZH_DR_ADD_BEGIN__
/// Dummy bool variable used by transform_assertions_assumptions() under
/// --datarace to keep evaluating disabled user assertions' conditions
/// (see turn_into_assignment()) without checking them. Reused across
/// every disabled assertion in the program -- its value is never read
/// back, only its evaluation (and the memory reads that may be embedded
/// in it) needs to survive into the SSA trace.
static symbol_exprt get_datarace_assert_dummy(symbol_tablet &symbol_table)
{
  const irep_idt name = CPROVER_PREFIX "datarace_assert_dummy";
  if(!symbol_table.has_symbol(name))
  {
    symbolt new_symbol;
    new_symbol.base_name = name;
    new_symbol.name = name;
    new_symbol.type = bool_typet();
    new_symbol.is_static_lifetime = true;
    new_symbol.mode = ID_C;
    symbol_table.add(new_symbol);
  }
  return symbol_table.lookup_ref(name).symbol_expr();
}
// __SZH_DR_ADD_END__

void transform_assertions_assumptions(
  const optionst &options,
  goto_modelt &goto_model)
{
  const bool enable_assertions = options.get_bool_option("assertions");
  const bool enable_built_in_assertions =
    options.get_bool_option("built-in-assertions");
  const bool enable_assumptions = options.get_bool_option("assumptions");

  // check whether there could possibly be anything to do
  if(enable_assertions && enable_built_in_assertions && enable_assumptions)
    return;

  // __SZH_DR_ADD_BEGIN__
  const bool datarace = options.get_bool_option("datarace");
  symbol_exprt dummy = datarace
                          ? get_datarace_assert_dummy(goto_model.symbol_table)
                          : symbol_exprt(irep_idt(), bool_typet());
  const exprt *datarace_dummy_lhs = datarace ? &dummy : nullptr;
  // __SZH_DR_ADD_END__

  for(auto &entry : goto_model.goto_functions.function_map)
  {
    transform_assertions_assumptions(
      entry.second.body,
      enable_assertions,
      enable_built_in_assertions,
      enable_assumptions,
      datarace_dummy_lhs);
  }
}

void transform_assertions_assumptions(
  const optionst &options,
  goto_programt &goto_program)
{
  const bool enable_assertions = options.get_bool_option("assertions");
  const bool enable_built_in_assertions =
    options.get_bool_option("built-in-assertions");
  const bool enable_assumptions = options.get_bool_option("assumptions");

  // check whether there could possibly be anything to do
  if(enable_assertions && enable_built_in_assertions && enable_assumptions)
    return;

  transform_assertions_assumptions(
    goto_program,
    enable_assertions,
    enable_built_in_assertions,
    enable_assumptions,
    nullptr);
}

// __SZH_ADD_BEGIN__
void add_dummy_assertion(goto_modelt &goto_model)
{
  auto& main_body = goto_model.goto_functions.function_map[irep_idt("main")].body;
  auto& instructions = main_body.instructions;

  auto assert_false = goto_programt::make_assertion(false_exprt());

  for(auto it = instructions.begin(); it != instructions.end(); it++)
  {
    if(it->is_set_return_value()) // add an "assert(false);" before return 0
    {
      instructions.insert(it, assert_false);
      return;
    }
  }

  *main_body.add_instruction() = assert_false;
}
// __SZH_ADD_END__