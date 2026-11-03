default: tests.log

test:
	@../test.pl -c "env LAZYPO_ROUND_BOUND=only LAZYPO_ROUND_BOUND_MAX=3 cbmc"

tests.log: ../test.pl
	@../test.pl -c "env LAZYPO_ROUND_BOUND=only LAZYPO_ROUND_BOUND_MAX=3 cbmc"

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	$(RM) tests.log
