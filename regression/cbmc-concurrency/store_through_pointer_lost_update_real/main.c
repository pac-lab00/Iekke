#include <pthread.h>
extern int __VERIFIER_nondet_int(void);
pthread_mutex_t g = PTHREAD_MUTEX_INITIALIZER;
struct s { int datum; pthread_mutex_t mutex; } a[5];
void work(struct s *p)
{
  if(__VERIFIER_nondet_int())
  {
    pthread_mutex_lock(&g); p->datum++; pthread_mutex_unlock(&g);
    pthread_mutex_lock(&g); p->datum--; pthread_mutex_unlock(&g);
  }
  else
  {
    pthread_mutex_lock(&g); __CPROVER_assert(p->datum == 0, "protected"); pthread_mutex_unlock(&g);
  }
}
void *t(void *arg)
{
  int i = __VERIFIER_nondet_int();
  __CPROVER_assume(0 <= i && i < 5);
  struct s *p = &a[i];
  // no lock: the update of a[i] really races with main
  work(p);
  return 0;
}
int main(void)
{
  for(int k = 0; k < 5; k++)
    pthread_mutex_init(&a[k].mutex, 0);
  int i = __VERIFIER_nondet_int();
  __CPROVER_assume(0 <= i && i < 5);
  pthread_t id[10000];
  for(int k = 0; k < 10000; k++)
    pthread_create(&id[k], 0, t, 0);
  pthread_mutex_lock(&a[i].mutex);
  work(&a[i]);
  pthread_mutex_unlock(&a[i].mutex);
  return 0;
}
