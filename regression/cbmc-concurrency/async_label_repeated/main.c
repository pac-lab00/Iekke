// __CPROVER_ASYNC_n labels a statement to be run as a thread.
// goto_convertt::convert_label recognises the label by its prefix, so the
// suffix carries no meaning, and it replaces the labelled statement with a
// thread block rather than registering a goto target -- nothing can jump to
// it. Using the same label for several spawns in one function is therefore
// well defined, and is what CBMC's own concurrency tests do.
//
// typecheck_label used to reject the repeat as a duplicate label, so a program
// written this way failed with CONVERSION ERROR before reaching the solver.

#include <assert.h>

int x;

void inc(void)
{
  x = x + 1;
}

int main(void)
{
__CPROVER_ASYNC_1: inc();
__CPROVER_ASYNC_1: inc();

  // Both threads only ever increment, so x cannot go negative whichever way
  // the two interleave, and whether or not an update is lost.
  assert(x >= 0);
  return 0;
}
