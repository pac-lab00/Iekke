// A thread uses a local of main that main never joins. Returning from main
// ends the program (C11 5.1.2.2.3), so the thread never sees that local dead;
// the model lets threads run after main has returned, so main outermost
// locals are not marked dead.
#include <pthread.h>
void *worker(void *arg)
{
  *(int *)arg = 1;
  return 0;
}
int main(void)
{
  int shared = 0;
  pthread_t t;
  pthread_create(&t, 0, worker, &shared);
  return 0;
}
