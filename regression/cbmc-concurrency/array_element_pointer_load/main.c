#include <pthread.h>
extern int __VERIFIER_nondet_int(void);
struct s
{
  int datum;
  pthread_mutex_t mutex;
} a[2];
void *t(void *arg)
{
  int i = __VERIFIER_nondet_int();
  __CPROVER_assume(0 <= i && i < 2);
  struct s *p = &a[i];
  pthread_mutex_lock(&p->mutex);
  p->datum++;
  pthread_mutex_unlock(&p->mutex);
  return 0;
}
int main(void)
{
  pthread_mutex_init(&a[0].mutex, 0);
  pthread_mutex_init(&a[1].mutex, 0);
  int i = __VERIFIER_nondet_int();
  __CPROVER_assume(0 <= i && i < 2);
  pthread_t id;
  pthread_create(&id, 0, t, 0);
  pthread_mutex_lock(&a[i].mutex);
  a[i].datum++;
  pthread_mutex_unlock(&a[i].mutex);
  return 0;
}
