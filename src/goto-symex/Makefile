SRC = auto_objects.cpp \
      build_goto_trace.cpp \
      expr_skeleton.cpp \
      field_sensitivity.cpp \
      goto_state.cpp \
      goto_symex.cpp \
      goto_symex_state.cpp \
      lazy_po.cpp \
      lazy_po_array_rf.cpp \
      lazy_po_base.cpp \
      lazy_po_canonical.cpp \
      lazy_po_collect.cpp \
      lazy_po_datarace.cpp \
      lazy_po_index_chain.cpp \
      lazy_po_narrowing.cpp \
      lazy_po_private.cpp \
      lazy_po_rounds.cpp \
      lazy_po_symbols.cpp \
      lazy_po_symmetry.cpp \
      lazy_po_windows.cpp \
      round_bound.cpp \
      memory_model.cpp \
      memory_model_pso.cpp \
      memory_model_sc.cpp \
      memory_model_tso.cpp \
      memory_model_general.cpp \
      memory_model_general_cutter.cpp \
      partial_order_concurrency.cpp \
      path_storage.cpp \
      postcondition.cpp \
      precondition.cpp \
      renaming_level.cpp \
      show_program.cpp \
      show_vcc.cpp \
      slice.cpp \
      solver_hardness.cpp \
      ssa_step.cpp \
      symex_assign.cpp \
      symex_atomic_section.cpp \
      symex_builtin_functions.cpp \
      symex_catch.cpp \
      symex_clean_expr.cpp \
      symex_dead.cpp \
      symex_decl.cpp \
      symex_dereference.cpp \
      symex_dereference_state.cpp \
      symex_function_call.cpp \
      symex_goto.cpp \
      symex_main.cpp \
      symex_other.cpp \
      symex_set_return_value.cpp \
      symex_start_thread.cpp \
      symex_target.cpp \
      symex_target_equation.cpp \
      symex_target_equation_deagle.cpp \
      symex_throw.cpp \
      thread_exclusivity.cpp \
      symmetric_arrays.cpp \
      thread_aware_slice.cpp \
      thread_spawn_loops.cpp \
      complexity_limiter.cpp \
      # Empty last line

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = goto-symex$(LIBEXT)

all: goto-symex$(LIBEXT)

###############################################################################

goto-symex$(LIBEXT): $(OBJ)
	$(LINKLIB)
