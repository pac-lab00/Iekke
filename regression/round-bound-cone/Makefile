default: tests.log

test:
	@../test.pl -c "env LAZYPO_ROUND_BOUND=1 LAZYPO_ROUND_BOUND_CONE=1 cbmc"

tests.log: ../test.pl
	@../test.pl -c "env LAZYPO_ROUND_BOUND=1 LAZYPO_ROUND_BOUND_CONE=1 cbmc"

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	$(RM) tests.log
