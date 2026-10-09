#include <pthread.h>

// The thread-creation bound stops a recognised spawn loop after k threads.
// That is sound for counterexamples, but it must not cut a family the program
// could exhaust anyway: here four handles are declared, four threads are
// created, and only three are joined, so the race is between the fourth --
// never joined, still running -- and main's unguarded read of `data`.
//
// At the default bound of 2 only two threads exist, every one of them is
// joined, the unjoined-thread race cannot occur, and the tool answered
// SUCCESSFUL on a program that plainly races. The bound is now taken from the
// declared handle-array size when that is small enough to unwind in full,
// which is exactly this case; the 10000-element families the analysis was
// written for stay bounded.

int data = 0;
pthread_mutex_t data_mutex = PTHREAD_MUTEX_INITIALIZER;

void *thread(void *arg)
{
  pthread_mutex_lock(&data_mutex);
  data = 1;
  pthread_mutex_unlock(&data_mutex);
  return 0;
}

int main(void)
{
  pthread_t tids[4];

  for(int i = 0; i < 4; i++)
    pthread_create(&tids[i], 0, &thread, 0);

  // deliberately one short: tids[3] is never joined
  for(int i = 0; i < 3; i++)
    pthread_join(tids[i], 0);

  return data; // unguarded, and races with the fourth thread
}
