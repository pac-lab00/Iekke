#include <pthread.h>
#include <stdlib.h>
#include <assert.h>
int __VERIFIER_nondet_int();
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
int *slot[4];
void *t(void *x)
{
  int i = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= i && i < 4);
  int *p = malloc(sizeof(int));
  if(p)
    *p = 1;
  slot[i] = p;
  return 0;
}
int main()
{
  pthread_t h;
  pthread_create(&h, 0, t, 0);
  pthread_join(h, 0);
  assert(slot[1] == 0);
  return 0;
}
