#include <pthread.h>
/* Both accesses to x are under one mutex, so they are never consecutive in
   an interleaving: the unlock and the lock lie between them.  Under
   --cbmc-memory-model the race literal used to require only that both
   accesses happen, so every co-enabled pair was reported. */
int x;
pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
void *t(void *arg)
{
  pthread_mutex_lock(&m); x = x + 1; pthread_mutex_unlock(&m);
  return 0;
}
int main(void)
{
  pthread_t id;
  pthread_create(&id, 0, t, 0);
  pthread_mutex_lock(&m); x = x + 2; pthread_mutex_unlock(&m);
  pthread_join(id, 0);
  return 0;
}
