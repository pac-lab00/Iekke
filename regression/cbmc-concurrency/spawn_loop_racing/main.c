// The goblint-regression shape: spawn N threads in a loop, check a property,
// join them again in a loop. N is far beyond any reachable unwind bound, so
// without the thread-creation bound the only two outcomes are "symex never
// finishes" or "the loop is cut with assume(false) and the property below it
// becomes vacuously true".
//
// The bound recognises both loops (their bodies are nothing but pthread_create
// / pthread_join plus the counter update, the counter is dead at the loop exit,
// and t_ids is mentioned nowhere else) and leaves them after k iterations
// *keeping* the state, so the race below is found with k threads created.
#include <pthread.h>

#define N 1000

int x;

void *t_fun(void *arg)
{
  x++;
  return 0;
}

int main()
{
  pthread_t t_ids[N];
  for(int i = 0; i < N; i++)
    pthread_create(&t_ids[i], 0, t_fun, 0);

  x++;
  __CPROVER_assert(x <= 1, "must be found: x is raced on");

  for(int i = 0; i < N; i++)
    pthread_join(t_ids[i], 0);
  return 0;
}
