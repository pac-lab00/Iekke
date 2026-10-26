// A race; a library precondition fails (free of a non-heap pointer).
#include <pthread.h>
#include <stdlib.h>
int g;
pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
void *t(void *a) { pthread_mutex_lock(&m); g = 1; pthread_mutex_unlock(&m); return 0; }
int main(void) {
  int local;
  pthread_t th; pthread_create(&th, 0, t, 0);
  g = 2;
  free(&local);
  pthread_join(th, 0);
  return 0;
}
