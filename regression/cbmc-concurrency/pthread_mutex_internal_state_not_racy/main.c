#include <pthread.h>
int shared;
pthread_mutex_t m;
void *t1(void *a) { pthread_mutex_lock(&m); shared = 1; pthread_mutex_unlock(&m); return 0; }
void *t2(void *a) { pthread_mutex_lock(&m); shared = 2; pthread_mutex_unlock(&m); return 0; }
int main() {
  pthread_mutex_init(&m, 0);
  pthread_t a, b;
  pthread_create(&a, 0, t1, 0);
  pthread_create(&b, 0, t2, 0);
  return 0;
}
