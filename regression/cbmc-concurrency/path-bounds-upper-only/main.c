#include <pthread.h>
#include <assert.h>
int __VERIFIER_nondet_int();
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
int cell[4];
int *slot[4] = {&cell[0], &cell[1], &cell[2], &cell[3]};
void *t(void *x)
{
  int j = __VERIFIER_nondet_int();
  assume_abort_if_not(j <= 3);
  if(j >= 0)
    *slot[j] = 1;
  else
    assert(j != -2);
  return 0;
}
int main()
{
  pthread_t h;
  pthread_create(&h, 0, t, 0);
  pthread_join(h, 0);
  return 0;
}
