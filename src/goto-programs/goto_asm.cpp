/*******************************************************************\

Module: Assembler -> Goto

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Assembler -> Goto

#include "goto_convert_class.h"

#include <util/string_constant.h>

#include <iostream>

void goto_convertt::convert_asm(
  const code_asmt &code,
  goto_programt &dest)
{
  // Recognize and skip the GCC empty-instruction compiler-memory-barrier
  // idiom, __asm__ __volatile__("" ::: "memory"). It corresponds to zero
  // real CPU instructions -- it is a directive to the compiler's own
  // optimizer not to reorder memory operations across this point. Under
  // the sequential-consistency model this tool already assumes (symbolic
  // execution never reorders memory accesses relative to program order in
  // the first place), preventing such reordering is already trivially
  // guaranteed, so this specific construct is provably a complete no-op.
  // Any other asm -- real instructions, a non-"memory" clobber, or any
  // input/output/goto-label operand -- is left unsupported exactly as
  // before.
  if(code.get_flavor() == ID_gcc)
  {
    const auto &code_asm_gcc = to_code_asm_gcc(code);

    const bool empty_text =
      can_cast_expr<string_constantt>(code_asm_gcc.asm_text()) &&
      to_string_constant(code_asm_gcc.asm_text()).get_value().empty();

    const bool no_operands = code_asm_gcc.outputs().operands().empty() &&
                              code_asm_gcc.inputs().operands().empty() &&
                              code_asm_gcc.labels().operands().empty();

    const auto &clobber_list = code_asm_gcc.clobbers().operands();
    const bool memory_only_clobber =
      clobber_list.size() == 1 && clobber_list.front().operands().size() == 1 &&
      can_cast_expr<string_constantt>(clobber_list.front().op0()) &&
      to_string_constant(clobber_list.front().op0()).get_value() == "memory";

    if(empty_text && no_operands && memory_only_clobber)
      return; // compiler memory barrier: sound no-op, nothing to emit
  }

  // Was: print "Error: Deagle does not support asm code." and exit(1), which
  // discarded the whole benchmark at the first inline asm -- on the
  // ldv-linux-3.14 family that is every task, for asm as ordinary as Linux's
  // this_cpu_read, `movl %%gs:%P1,%0`.
  //
  // CBMC already has a pass for this. Keep the statement as OTHER so the goto
  // model is built; remove_asm(), run from
  // cbmc_parse_optionst::process_goto_program, then translates the asm it
  // recognises and havocs the outputs of the asm it does not. Exiting here
  // meant that pass was never reached.

  // copy as OTHER
  copy(code, OTHER, dest);
}
