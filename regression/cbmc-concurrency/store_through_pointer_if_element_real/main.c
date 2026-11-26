#include <pthread.h>
extern int __VERIFIER_nondet_int(void);
int items[2];
int other;
void *t(void *arg)
{
  items[0] = 1;
  return 0;
}
int main(void)
{
  int i = __VERIFIER_nondet_int();
  __CPROVER_assume(0 <= i && i < 2);
  int *r = __VERIFIER_nondet_int() ? &items[i] : &other;
  pthread_t id;
  pthread_create(&id, 0, t, 0);
  *r = 5;
  pthread_join(id, 0);
  __CPROVER_assert(items[0] == 1, "main may store to items[0]");
  return 0;
}
