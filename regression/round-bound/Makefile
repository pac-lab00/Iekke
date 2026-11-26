default: tests.log

test:
	@../test.pl -c "env LAZYPO_ROUND_BOUND=only cbmc"

tests.log: ../test.pl
	@../test.pl -c "env LAZYPO_ROUND_BOUND=only cbmc"

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	$(RM) tests.log
