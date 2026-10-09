#include <pthread.h>
#include <stdlib.h>
extern int __VERIFIER_nondet_int();
pthread_t *tids;
pthread_mutex_t m[2];
void *worker(void *a) { return 0; }
void *reader(void *a) {
  pthread_mutex_lock(&m[0]);
  pthread_join(tids[0], 0);
  pthread_mutex_unlock(&m[0]);
  return 0;
}
int main() {
  int n = __VERIFIER_nondet_int();
  if (n < 1 || n > 2) return 0;
  tids = malloc(n * sizeof(pthread_t));
  pthread_mutex_init(&m[0], 0);
  pthread_t r;
  pthread_create(&r, 0, reader, 0);
  pthread_create(&tids[0], 0, worker, 0);
  pthread_join(r, 0);
  return 0;
}
