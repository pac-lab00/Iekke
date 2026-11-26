#include <pthread.h>
/* Only the thread takes the mutex; main writes x without it, so the two
   writes can be consecutive. */
int x;
pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
void *t(void *arg)
{
  pthread_mutex_lock(&m); x = 1; pthread_mutex_unlock(&m);
  return 0;
}
int main(void)
{
  pthread_t id;
  pthread_create(&id, 0, t, 0);
  x = 2;
  pthread_join(id, 0);
  return 0;
}
