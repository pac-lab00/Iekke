#include <pthread.h>
int nondet_int();
int flag, any, cnt;
void *t(void *a) { flag = 1; any = nondet_int(); cnt = cnt + 1; return 0; }
int main()
{
  pthread_t h;
  pthread_create(&h, 0, t, 0);
  flag = 0;
  cnt = cnt + 1;
  pthread_join(h, 0);
  __CPROVER_assert(cnt <= 2 || flag, "at most two increments");
  __CPROVER_assert(any != 123456789 || any == 123456789, "any keeps its range");
  return 0;
}
