// Signed arithmetic in the atomic built-ins wraps around without undefined
// behaviour (C11 7.17.7.5; GCC documents the same for __atomic and __sync),
// so none of these is an overflow. They were modelled as plain signed
// additions and flagged (pthread-overflow/lost-increment-guard-fetch-add and
// four more tasks, expected no overflow).
#include <limits.h>
#include <stdatomic.h>
#include <pthread.h>
atomic_int a = INT_MAX;
int b = INT_MAX;
int c = INT_MIN;
int d = INT_MAX;
void *thr(void *arg)
{
  atomic_fetch_add(&a, 1);
  __atomic_fetch_add(&b, 1, __ATOMIC_SEQ_CST);
  __atomic_sub_fetch(&c, 1, __ATOMIC_SEQ_CST);
  __atomic_add_fetch(&d, 1, __ATOMIC_SEQ_CST);
  return 0;
}
int main(void)
{
  pthread_t t;
  pthread_create(&t, 0, thr, 0);
  pthread_join(t, 0);
  return 0;
}
