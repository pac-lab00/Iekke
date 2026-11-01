#include <pthread.h>
int cnt, neg;
void *t(void *a) { cnt = cnt + 1; neg = neg - 3; return 0; }
int main()
{
  pthread_t h;
  pthread_create(&h, 0, t, 0);
  cnt = cnt + 1;
  neg = neg - 3;
  pthread_join(h, 0);
  __CPROVER_assert(cnt != 2 || neg != -6, "both updates seen");
  return 0;
}
