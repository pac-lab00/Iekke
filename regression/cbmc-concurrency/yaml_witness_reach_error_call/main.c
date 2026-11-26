// The target of an unreach-call witness is the call of reach_error, here the
// one in __VERIFIER_assert (line 16, column 50). The assertion fails in the
// body of reach_error (line 15), and under --rounds the trace does not show
// the calls that led there; the target was line 15, which ESBMC rejects
// (pthread-barrier/unreach-reachable-capacity-input-scanf).
#include <assert.h>
#include <pthread.h>
#include <stdio.h>

extern void abort();
extern int __VERIFIER_nondet_int();


pthread_barrier_t barrier;
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) { if(!(cond)) { reach_error(); abort(); } }

void *f1(void *ptr)
{
  pthread_barrier_wait(&barrier);
  return NULL;
}

int main(void)
{
  int top = __VERIFIER_nondet_int();
  int i = 0;
  unsigned int capacity;
  if(scanf("%u", &capacity) != 1)
    return 0;
  if(capacity < 1 || capacity > 3)
    return 0;
  pthread_barrier_init(&barrier, NULL, capacity);
  pthread_t t1;
  pthread_create(&t1, NULL, f1, NULL);
  if(top)
  {
    pthread_barrier_wait(&barrier);
    i = 1;
  }
  __VERIFIER_assert(i == 0);
  return 0;
}
