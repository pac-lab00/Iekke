#include <pthread.h>
#include <assert.h>
int __VERIFIER_nondet_int();
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
struct s
{
  int datum;
  pthread_mutex_t mutex;
} a[4];
void *t(void *x)
{
  int i = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= i && i < 3);
  struct s *p = &a[i];
  pthread_mutex_lock(&p->mutex);
  a[i].datum++;
  pthread_mutex_unlock(&p->mutex);
  assert(a[0].datum != 1);
  return 0;
}
int main()
{
  pthread_t h;
  pthread_create(&h, 0, t, 0);
  pthread_join(h, 0);
  return 0;
}
