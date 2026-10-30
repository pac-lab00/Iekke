/*******************************************************************\

Module: Symbolic Execution Config

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#ifndef CPROVER_GOTO_SYMEX_SYMEX_CONFIG_H
#define CPROVER_GOTO_SYMEX_SYMEX_CONFIG_H

/// Configuration used for a symbolic execution
struct symex_configt final
{
  /// \brief The maximum depth to take the execution to.
  /// Depth is a count of the instructions that have been executed on any
  /// single path.
  unsigned max_depth;

  bool doing_path_exploration;

  bool allow_pointer_unsoundness;

  bool constant_propagation;

  bool self_loops_to_assumptions;

  bool simplify_opt;

  bool unwinding_assertions;

  bool partial_loops;

  bool havoc_undefined_functions;

  /// \brief Should the additional validation checks be run?
  /// If this flag is set the checks for renaming (both level1 and level2) are
  /// executed in the goto_symex_statet (in the assignment method).
  bool run_validation_checks;

  /// \brief Prints out the path that symex is actively taking during execution,
  /// includes diagnostic information about call stack and guard size.
  bool show_symex_steps;
  bool show_points_to_sets;

  /// Maximum sizes for which field sensitivity will be applied to array cells
  std::size_t max_field_sensitivity_array_size;

  /// \brief Whether this run of symex is under complexity limits. This
  /// enables certain analyses that otherwise aren't run.
  bool complexity_limits_active;

  /// \brief Whether or not to replace multiple occurrences of the same
  ///   dereference with a single symbol that contains the result of that
  ///   dereference. Can sometimes lead to a significant performance
  ///   improvement, but sometimes also makes things worse.
  ///   See https://github.com/diffblue/cbmc/pull/5964 for performance data.
  ///   Used in goto_symext::dereference_rec
  bool cache_dereferences;

  /// Number of rounds for the LazyCSeq context-bounded concurrency encoding
  std::size_t lazy_po_rounds;

  /// --dynamic-array-bound K: an array allocated with a non-constant number
  /// of elements n gets K elements, under the condition n <= K (0: off)
  std::size_t dynamic_array_bound;

  /// --summarise-guards: in a multi-threaded program, replace the guard
  /// coming out of a function by the guard at the call and a fresh guard
  /// symbol defined as the guard coming out (see symex_end_of_function)
  bool summarise_guards;

  /// --infer-alloc-types: an allocation tagged with sizeof(T) and larger
  /// than T is typed {T object; unsigned char tail[...]} rather than as bytes
  bool infer_alloc_types;

  /// --merge-exclusive-threads: a thread created by the same instruction of
  /// the same parent as a pending thread, on a path that excludes every
  /// creation of that thread, reuses it (see symex_start_thread); --rounds only
  bool merge_exclusive_threads;

  /// \brief Construct a symex_configt using options specified in an
  /// \ref optionst
  explicit symex_configt(const optionst &options);
};

#endif // CPROVER_GOTO_SYMEX_SYMEX_CONFIG_H
