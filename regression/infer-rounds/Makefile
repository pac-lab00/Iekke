default: tests.log

test:
	@../test.pl -c "env cbmc"

tests.log: ../test.pl
	@../test.pl -c "env cbmc"

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	$(RM) tests.log
