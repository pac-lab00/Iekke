#include <pthread.h>
#include <stdlib.h>
int nondet_int();
_Bool *datas;
void *t(void *arg)
{
  int i = (int)arg;
#ifdef CONSTIDX
  datas[0] = 1;
#else
  datas[i] = 1;
#endif
  return 0;
}
int main()
{
#ifdef CONSTSIZE
  int n = 2;
#else
  int n = nondet_int();
  __CPROVER_assume(n >= 1 && n <= 4);
#endif
#ifdef MALLOC
  datas = malloc(n);
#else
  datas = calloc(n, 1);
#endif
  pthread_t h;
  pthread_create(&h, 0, t, (void *)0);
  return datas[0];
}
