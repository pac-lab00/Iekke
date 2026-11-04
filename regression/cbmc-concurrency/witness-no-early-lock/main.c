// A violation witness must not claim a pthread_mutex_lock before the lock is
// taken: the argument binding of the call used to become an edge on its line,
// and a context switch can come between that binding and the acquisition, so
// a validator saw main holding the lock while another thread ran inside it
// (per-thread-index-bitmask-race-2, rejected by Dartagnan).
#include <assert.h>
#include <pthread.h>

pthread_mutex_t m;
int x = 0;

void *t(void *arg)
{
  pthread_mutex_lock(&m);
  x = 1;
  pthread_mutex_unlock(&m);
  return 0;
}

int main(void)
{
  pthread_t h;
  pthread_mutex_init(&m, 0);
  pthread_create(&h, 0, t, 0);
  pthread_mutex_lock(&m);
  assert(x == 0);
  pthread_mutex_unlock(&m);
  return 0;
}
