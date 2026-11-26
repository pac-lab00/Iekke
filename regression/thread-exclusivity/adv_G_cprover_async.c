// ADVERSARIAL: thread creation via __CPROVER_ASYNC_1 rather than
// pthread_create. The analysis must give up on the whole program, because it
// only understands CBMC pthread model spawns.
#include <assert.h>

int g = 0;

void body(void)
{
  g = 99;
}

int main()
{
  __CPROVER_ASYNC_1: body();
  for(g = 0; g < 2; g++)
  {
  }
  assert(g == 2);
  return 0;
}
