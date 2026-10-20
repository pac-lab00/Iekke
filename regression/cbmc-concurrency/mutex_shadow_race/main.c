#include <pthread.h>
#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);
int n; pthread_mutex_t *m; int counter;
void *t(void *arg) { int i = (int)arg; pthread_mutex_lock(&m[i]); counter++; pthread_mutex_unlock(&m[i]); return 0; }
int main() { n = __VERIFIER_nondet_int(); if (n < 2 || n > 4) return 0;
  m = malloc(n * sizeof(pthread_mutex_t)); pthread_mutex_init(&m[0], 0); pthread_mutex_init(&m[1], 0);
  pthread_t a, b; pthread_create(&a, 0, t, (void *)0); pthread_create(&b, 0, t, (void *)1);
  pthread_join(a, 0); pthread_join(b, 0); return 0; }
