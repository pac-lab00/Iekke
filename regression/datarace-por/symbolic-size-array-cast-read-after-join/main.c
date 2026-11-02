#include <pthread.h>
#include <stdlib.h>
int nondet_int();
_Bool *datas;
void *t(void *arg)
{
  int i = (int)arg;
  datas[i] = 1;
  return 0;
}
int main()
{
  int n = nondet_int();
  __CPROVER_assume(n >= 1 && n <= 4);
  datas = calloc(n, 1);
  pthread_t h;
  pthread_create(&h, 0, t, (void *)0);
  pthread_join(h, 0);
  return datas[0];
}
