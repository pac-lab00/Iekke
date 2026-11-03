#include <pthread.h>
#include <assert.h>
int __VERIFIER_nondet_int();
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
int slot[4];
void *t(void *x)
{
  slot[0] = 1;
  return 0;
}
int main()
{
  int j = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= j && j < 4);
  pthread_t h;
  pthread_create(&h, 0, t, 0);
  slot[j] = 2;
  pthread_join(h, 0);
  assert(slot[j] == 2);
  return 0;
}
