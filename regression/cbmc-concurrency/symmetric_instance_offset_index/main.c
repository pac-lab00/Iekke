#include <assert.h>
#include <pthread.h>

extern int __VERIFIER_nondet_int(void);

int storage[6];
int max;

void *worker(void *arg)
{
  (void)arg;
  int offset = __VERIFIER_nondet_int();
  __CPROVER_assume(offset % 2 == 0 && offset >= 0 && offset < 6);
  for(int i = offset; i < offset + 2; i++)
  {
    int e = storage[i];
    assert(e == 0);
  }
  return 0;
}

int main(void)
{
  pthread_t t;
  pthread_create(&t, 0, worker, 0);
  return 0;
}
