#include <pthread.h>
extern int __VERIFIER_nondet_int(void);
pthread_mutex_t mA, mB;
int dA, dB, sink;
void *t(void *arg)
{
  pthread_mutex_lock(&mA);
  dA = 5;
  pthread_mutex_unlock(&mA);
  return 0;
}
int main(void)
{
  int c = __VERIFIER_nondet_int();
  pthread_mutex_t *m = c ? &mB : &mA;
  int *d = c ? &dA : &dB;
  pthread_t id;
  pthread_create(&id, 0, t, 0);
  pthread_mutex_lock(m);
  sink = *d;
  pthread_mutex_unlock(m);
  return 0;
}
