#include <pthread.h>
pthread_mutex_t m;
int x;
void *t(void *arg)
{
  pthread_mutex_lock(&m);
  int v = x;
  x = v + 1;
  pthread_mutex_unlock(&m);
  return 0;
}
void *u(void *arg)
{
  int v = x;
  x = v + 1;
  return 0;
}
int main(void)
{
  pthread_mutex_init(&m, 0);
  pthread_t a, b;
  pthread_create(&a, 0, t, 0);
  pthread_create(&b, 0, u, 0);
  pthread_join(a, 0);
  pthread_join(b, 0);
  __CPROVER_assert(x == 2, "u does not take the mutex");
  return 0;
}
