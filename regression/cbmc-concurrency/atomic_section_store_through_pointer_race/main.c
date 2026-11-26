#include <pthread.h>
extern int __VERIFIER_nondet_int(void);
extern void __VERIFIER_atomic_begin(void);
extern void __VERIFIER_atomic_end(void);
int dA, dB, c;
void *t(void *arg)
{
  if(1)
    dA = 5;
  return 0;
}
int main(void)
{
  c = __VERIFIER_nondet_int();
  int *d = c ? &dA : &dB;
  pthread_t id;
  pthread_create(&id, 0, t, 0);
  __VERIFIER_atomic_begin();
  *d = 8;
  __VERIFIER_atomic_end();
  return 0;
}
