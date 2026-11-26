// Two identical threads increment x without a lock; the one that finishes
// second can see an update lost.

#include <assert.h>
#include <pthread.h>

extern void __VERIFIER_atomic_begin(void);
extern void __VERIFIER_atomic_end(void);

int x, done;

void *inc(void *arg)
{
  (void)arg;
  int t = x;
  x = t + 1;
  __VERIFIER_atomic_begin();
  int d = ++done;
  int v = x;
  __VERIFIER_atomic_end();
  if(d == 2)
    assert(v == 2);
  return 0;
}

int main(void)
{
  pthread_t a, b;
  pthread_create(&a, 0, inc, 0);
  pthread_create(&b, 0, inc, 0);
  return 0;
}
