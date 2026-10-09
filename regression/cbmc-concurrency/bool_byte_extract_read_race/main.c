#include <pthread.h>
#include <stdlib.h>
extern int __VERIFIER_nondet_int();
_Bool *flags;
pthread_mutex_t m[2];
_Bool got_it;
void *reader(void *a) {
  pthread_mutex_lock(&m[0]);
  if (flags[0]) { got_it = 1; }
  pthread_mutex_unlock(&m[0]);
  return 0;
}
int main() {
  int n = __VERIFIER_nondet_int();
  if (n < 1 || n > 2) return 0;
  flags = malloc(n * sizeof(_Bool));
  flags[0] = 0;
  pthread_mutex_init(&m[0], 0);
  pthread_t r;
  pthread_create(&r, 0, reader, 0);
  flags[0] = 1;
  pthread_join(r, 0);
  return 0;
}
