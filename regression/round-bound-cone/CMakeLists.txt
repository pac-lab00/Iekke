add_test_pl_tests(
    "env LAZYPO_ROUND_BOUND=1 LAZYPO_ROUND_BOUND_CONE=1 $<TARGET_FILE:cbmc>"
)
