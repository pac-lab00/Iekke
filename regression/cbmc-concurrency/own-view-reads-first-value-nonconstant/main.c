// as k3 with a value that is not a constant: t, the only writer after the
// spawn, first sees the prologue value, whatever the reader symexed before it
// read (it may read t's own later write)
#include <assert.h>
#include <pthread.h>
int x, init;
int nondet_int(void);
void *r(void *arg) { int v = x; (void)v; return 0; }
void *t(void *arg)
{
  assert(x == init);
  x = init + 1;
  return 0;
}
int main(void)
{
  pthread_t a, b;
  x = nondet_int();
  init = x;
  pthread_create(&a, 0, r, 0);
  pthread_create(&b, 0, t, 0);
  return 0;
}
