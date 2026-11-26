// the only writer after the spawn is t; a reader symexed before it must not
// change what t sees first (5), and t's own conditional write is merged
#include <assert.h>
#include <pthread.h>
int x = 5;
int nondet_int(void);
void *r(void *arg) { int v = x; (void)v; return 0; }
void *t(void *arg)
{
  assert(x == 5);
  if(nondet_int())
    x = 7;
  assert(x == 5 || x == 7);
  return 0;
}
int main(void)
{
  pthread_t a, b;
  pthread_create(&a, 0, r, 0);
  pthread_create(&b, 0, t, 0);
  return 0;
}
