#include <pthread.h>

// A legal re-acquisition of a recursive mutex must not prune the path.
//
// `mutex` is initialised PTHREAD_MUTEX_RECURSIVE, so main locking it twice is
// allowed and the second lock returns immediately. The model's active branch
// assumed the mutex was free on every acquisition, which is false here, so
// everything after the second lock became unreachable -- including main's
// unprotected write to `datum`, which races with the spawned thread's.
//
// The answer was SUCCESSFUL on a program that plainly races, and the safe
// counterparts were SUCCESSFUL for the wrong reason: their proofs were vacuous
// too. Nothing about the bound changes it; it is the model, not the depth.

int datum;
pthread_mutex_t datum_mutex;

void *thread(void *arg)
{
  pthread_mutex_lock(&datum_mutex);
  pthread_mutex_unlock(&datum_mutex);
  datum = 5; // outside the critical section
  return 0;
}

int main(void)
{
  pthread_mutexattr_t attr;

  pthread_mutexattr_init(&attr);
  pthread_mutexattr_settype(&attr, PTHREAD_MUTEX_RECURSIVE);
  pthread_mutex_init(&datum_mutex, &attr);

  pthread_mutex_lock(&datum_mutex);
  pthread_t id;
  pthread_create(&id, 0, &thread, 0);
  pthread_mutex_lock(&datum_mutex); // legal: same thread, recursive mutex
  pthread_mutex_unlock(&datum_mutex);
  pthread_mutex_unlock(&datum_mutex);

  datum = 8; // the lock is fully released here, so this races
  return 0;
}
