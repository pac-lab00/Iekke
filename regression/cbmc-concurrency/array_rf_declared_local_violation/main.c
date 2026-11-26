// array_rf_declared_local with the assertion that the never-written element is
// 0: a local array has no initial value, so it fails.

#include <pthread.h>

int *p;
int x, y;

void *t(void *arg)
{
  (void)arg;
  p[0] = 5;
  return 0;
}

void *u(void *arg)
{
  (void)arg;
  x = p[1];
  y = p[1];
  return 0;
}

int main(void)
{
  int a[1000];
  p = a;
  pthread_t ta, ua;
  pthread_create(&ta, 0, t, 0);
  pthread_create(&ua, 0, u, 0);
  pthread_join(ta, 0);
  pthread_join(ua, 0);
  __CPROVER_assert(x == 0, "a declared array starts at zero -- false");
  return 0;
}
