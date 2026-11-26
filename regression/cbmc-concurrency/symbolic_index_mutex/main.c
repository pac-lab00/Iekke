// Mutual exclusion through a mutex selected by a symbolic array index.
//
// Both threads pick a nondeterministic element of a[], lock that element's
// mutex, and touch that element's datum under it. Two threads that pick the
// same index are excluded by the same mutex; two threads that pick different
// indices touch different data. The assertion therefore holds.
//
// Symbolic execution lowers "p->datum++" with a symbolic p into a read of the
// whole array followed by a write of the whole array, framing every element it
// did not store to over from the value it read. Emitting those framed element
// writes as shared writes makes one thread reset another thread's a[k].mutex
// to its pre-lock value, so this used to report a spurious violation.
#include <pthread.h>

extern int __VERIFIER_nondet_int();

struct s
{
  int datum;
  pthread_mutex_t mutex;
} a[4];

void *t_fun(void *arg)
{
  int i = __VERIFIER_nondet_int();
  if(!(0 <= i && i < 4))
    __CPROVER_assume(0);
  struct s *p = &a[i];
  pthread_mutex_lock(&p->mutex);
  p->datum++;
  __CPROVER_assert(p->datum == 1, "the per-element mutex excludes");
  p->datum--;
  pthread_mutex_unlock(&p->mutex);
  return 0;
}

int main()
{
  for(int k = 0; k < 4; k++)
    pthread_mutex_init(&a[k].mutex, 0);
  pthread_t t1, t2;
  pthread_create(&t1, 0, t_fun, 0);
  pthread_create(&t2, 0, t_fun, 0);
  return 0;
}
