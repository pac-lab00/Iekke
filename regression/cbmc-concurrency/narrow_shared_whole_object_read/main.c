// A shared object that something reads whole must keep its full-width lazy
// chain. Narrowing is only sound because nothing observes the bits it drops,
// so the analysis bails on any use of the object outside a byte_extract or
// byte_update -- here, copying the mutex into `snapshot`.
//
// The mutex still protects the critical section, so the program is safe either
// way; what this pins down is that the bail-out happens rather than the
// narrowed chain being used for an object whose other bytes are read. With the
// bail removed the copy would see an unconstrained value.

#include <pthread.h>

pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t snapshot;
int in_cs;

void *worker(void *arg)
{
  (void)arg;
  pthread_mutex_lock(&m);
  snapshot = m; // reads every byte of the mutex, not just the lock byte
  in_cs++;
  __CPROVER_assert(in_cs == 1, "at most one thread in the critical section");
  in_cs--;
  pthread_mutex_unlock(&m);
  return 0;
}

int main(void)
{
  pthread_t a, b;

  pthread_create(&a, 0, worker, 0);
  pthread_create(&b, 0, worker, 0);
  pthread_join(a, 0);
  pthread_join(b, 0);

  return 0;
}
