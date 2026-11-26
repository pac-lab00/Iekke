// Both threads use element 0: the race on in[0] is still found once a
// constant index reads only its element (own-view-constant-index-racefree).
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
    a[i].tid = 0;
  pthread_t w;
  pthread_create(&w, 0, &worker_fn, &a[0]);
  worker_fn(&a[1]);
  pthread_join(w, 0);
  return 0;
}
