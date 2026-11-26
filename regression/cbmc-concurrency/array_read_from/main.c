// The array is large on purpose: the lazy chain carries one copy of all 1000
// elements per (write, round), which is what --array-rf replaces by matching
// the writes. The cost model only turns it on when the array is wide enough
// for that to pay, so a small array here would leave the flag inert and the
// test would prove nothing.
//
// Discriminating in the under-constraining direction: slot can only ever hold
// 0, 1 or 2, so if a read were left free to invent a value this safe program
// would report a violation it does not have.

#include <pthread.h>

int a[1000];
int idx;
pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;

void *w1(void *arg) { (void)arg; pthread_mutex_lock(&m); a[idx] = 1; pthread_mutex_unlock(&m); return 0; }
void *w2(void *arg) { (void)arg; pthread_mutex_lock(&m); a[idx] = 2; pthread_mutex_unlock(&m); return 0; }

void *reader(void *arg)
{
  (void)arg;
  pthread_mutex_lock(&m);
  int v = a[idx];
  __CPROVER_assert(v == 0 || v == 1 || v == 2, "a[idx] holds only what was written, or its initial zero");
  pthread_mutex_unlock(&m);
  return 0;
}

int main(void)
{
  pthread_t t1, t2, t3;
  idx = 5;
  pthread_create(&t1, 0, w1, 0);
  pthread_create(&t2, 0, w2, 0);
  pthread_create(&t3, 0, reader, 0);
  pthread_join(t1, 0); pthread_join(t2, 0); pthread_join(t3, 0);
  return 0;
}
