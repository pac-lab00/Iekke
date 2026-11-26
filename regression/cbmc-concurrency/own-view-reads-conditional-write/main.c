// as k3, but t's write is conditional, so x == 7 is violated
#include <assert.h>
#include <pthread.h>
int x = 5;
int nondet_int(void);
void *r(void *arg) { int v = x; (void)v; return 0; }
void *t(void *arg)
{
  if(nondet_int())
    x = 7;
  assert(x == 7);
  return 0;
}
int main(void)
{
  pthread_t a, b;
  pthread_create(&a, 0, r, 0);
  pthread_create(&b, 0, t, 0);
  return 0;
}
