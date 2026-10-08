// Come per-thread-array-index: numero di thread SIMBOLICO, regione malloc di
// dimensione simbolica, thread creati in un ciclo, ognuno scrive datas[i] con
// il proprio i. Nessuna corsa.
#include <pthread.h>
#include <stdlib.h>
extern int __VERIFIER_nondet_int();
int *datas;
void *thread(void *arg) {
  int i = (int)(long)arg;
  datas[i] = __VERIFIER_nondet_int();
  return 0;
}
int main(void) {
  int n = __VERIFIER_nondet_int();
  if (n < 0 || n > 3) return 0;
  pthread_t *tids = malloc(n * sizeof(pthread_t));
  datas = malloc(n * sizeof(int));
  if (tids == 0 || datas == 0) return 0;
  for (int i = 0; i < n; i++)
    pthread_create(&tids[i], 0, thread, (void *)(long)i);
  for (int i = 0; i < n; i++)
    pthread_join(tids[i], 0);
  return 0;
}
