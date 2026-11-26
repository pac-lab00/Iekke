// A violation witness must not claim a pthread_join before the joined thread
// has run: the argument binding of the join used to become an edge on the
// line of the call, placed (without partial-order reduction) before the
// threads' steps, and CPAchecker rejected the witness (pthread/lazy01).
#include <assert.h>
#include <pthread.h>

pthread_mutex_t mutex;
int data = 0;

void *thread1(void *arg)
{
  pthread_mutex_lock(&mutex);
  data++;
  pthread_mutex_unlock(&mutex);
  return 0;
}

void *thread2(void *arg)
{
  pthread_mutex_lock(&mutex);
  data += 2;
  pthread_mutex_unlock(&mutex);
  return 0;
}

void *thread3(void *arg)
{
  pthread_mutex_lock(&mutex);
  assert(data < 3);
  pthread_mutex_unlock(&mutex);
  return 0;
}

int main(void)
{
  pthread_mutex_init(&mutex, 0);
  pthread_t t1, t2, t3;
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
  pthread_create(&t3, 0, thread3, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  pthread_join(t3, 0);
  return 0;
}
