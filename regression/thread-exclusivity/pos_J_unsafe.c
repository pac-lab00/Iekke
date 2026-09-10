// POSITIVE: p really is thread-exclusive, and the bug is only reachable if
// the loop on p is unwound to completion and p folds to 3. If exclusivity
// folding were wrong, this would wrongly report SUCCESSFUL.
#include <pthread.h>
#include <assert.h>

int p;
int i = 0;

void *t1(void *arg)
{
  for(p = 0; p < 3; p++)
    i++;
  if(p == 3)
    assert(0);
  return 0;
}

void *t2(void *arg)
{
  i = 7;
  return 0;
}

int main()
{
  pthread_t a, b;
  pthread_create(&a, 0, t1, 0);
  pthread_create(&b, 0, t2, 0);
  pthread_join(a, 0);
  pthread_join(b, 0);
  return 0;
}
