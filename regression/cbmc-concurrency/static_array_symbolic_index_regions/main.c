// Ogni thread sceglie una regione e protegge il suo dato con il lock di
// quella regione. Due thread con indici diversi toccano dati diversi; due
// thread con lo stesso indice prendono lo stesso lock. In nessun caso c'e'
// corsa. E' lo schema della famiglia 09-regions / 06-symbeq.
#include <pthread.h>
extern int __VERIFIER_nondet_int();
#define N 2
pthread_mutex_t m[N];
int data[N];
void *t(void *a)
{
  int i = __VERIFIER_nondet_int();
  __CPROVER_assume(i >= 0 && i < N);
  pthread_mutex_lock(&m[i]);
  data[i] = data[i] + 1;
  pthread_mutex_unlock(&m[i]);
  return 0;
}
int main(void)
{
  pthread_t x, y;
  for(int k = 0; k < N; k++)
    pthread_mutex_init(&m[k], 0);
  pthread_create(&x, 0, t, 0);
  pthread_create(&y, 0, t, 0);
  pthread_join(x, 0);
  pthread_join(y, 0);
  return 0;
}
