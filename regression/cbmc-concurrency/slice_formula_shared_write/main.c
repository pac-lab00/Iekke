// A value whose only consumer is a shared write read by another thread.
//
// This is the case the sequential SSA slicer gets wrong. symex_slicet collects
// no symbols from SHARED_WRITE steps, so `t' has no intra-thread use and the
// assignments computing it look dead. Remove them and `shared' is written by a
// symbol nothing defines, the solver picks whatever it likes, and the consumer
// observes a value the program cannot produce -- a false alarm on a program
// that is safe.
//
// The assertion below therefore has to stay SUCCESSFUL with --slice-formula.

#include <assert.h>
#include <pthread.h>

int shared;
int observed;

void *producer(void *arg)
{
  (void)arg;
  int t = 1;
  t = t + 41;
  shared = t;
  return 0;
}

void *consumer(void *arg)
{
  (void)arg;
  observed = shared;
  return 0;
}

int main(void)
{
  pthread_t p, c;
  pthread_create(&p, 0, producer, 0);
  pthread_create(&c, 0, consumer, 0);
  pthread_join(p, 0);
  pthread_join(c, 0);

  // Either the consumer ran first and saw the initial value, or it saw the
  // producer's 42. Nothing else is reachable.
  assert(observed == 0 || observed == 42);
  return 0;
}
