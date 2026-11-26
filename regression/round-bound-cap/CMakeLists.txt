add_test_pl_tests(
    "env LAZYPO_ROUND_BOUND=only LAZYPO_ROUND_BOUND_MAX=3 $<TARGET_FILE:cbmc>"
)
