// Each thread reads and writes only its own element of in[], selected by a
// tid read through its argument. Under --own-view-reads main's tid is
// constant-propagated to 1, and a load at an index that renaming made
// constant read every element of the array: main's in[1] was paired with the
// other thread's write of in[0] and reported as a race
// (pthread-divine/barrier_2t named that pair).
#include <pthread.h>
volatile _Bool in[2];
typedef struct { int tid; } Arg;
void *worker_fn(void *arg)
{
  Arg *a = arg;
  const int tid = a->tid;
  if(in[tid])
    return 0;
  in[tid] = 1;
  return 0;
}
int main(void)
{
  Arg a[2];
  for(int i = 0; i < 2; ++i)
    a[i].tid = i;
  pthread_t w;
  pthread_create(&w, 0, &worker_fn, &a[0]);
  worker_fn(&a[1]);
  pthread_join(w, 0);
  return 0;
}
