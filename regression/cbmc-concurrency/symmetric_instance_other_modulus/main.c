#include <assert.h>
#include <pthread.h>

extern int __VERIFIER_nondet_int(void);

int a[6];

void *worker(void *arg)
{
  (void)arg;
  int i = __VERIFIER_nondet_int() % 3;
  __CPROVER_assume(i >= 0);
  assert(a[i] == 0);
  return 0;
}

int main(void)
{
  pthread_t t;
  pthread_create(&t, 0, worker, 0);
  return 0;
}
