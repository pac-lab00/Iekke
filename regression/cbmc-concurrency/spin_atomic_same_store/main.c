#include <pthread.h>
#include <assert.h>

// the waiting loop stores the value its flag already holds on every pass:
// a pass in which the flag stays 0 changes nothing and is cut, so two
// unwindings cover the loop
int flag, mine;

void *setter(void *arg)
{
  __atomic_store_n(&flag, 1, __ATOMIC_SEQ_CST);
  return 0;
}

int main()
{
  pthread_t t;
  pthread_create(&t, 0, setter, 0);
  while(__atomic_load_n(&flag, __ATOMIC_SEQ_CST) == 0)
    __atomic_store_n(&mine, 7, __ATOMIC_SEQ_CST);
  pthread_join(t, 0);
  assert(flag == 1);
  return 0;
}
