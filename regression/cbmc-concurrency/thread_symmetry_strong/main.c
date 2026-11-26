// Two identical threads; a thread that reads fin twice and sees the other
// thread's write in between fails. At two rounds the only such schedules have
// the threads share a round, so exact keeps them and strong loses them.

#include <assert.h>
#include <pthread.h>

int fin;

void *body(void *arg)
{
  (void)arg;
  int seen = fin;
  int seen2 = fin;
  fin = 1;
  assert(!(seen == 0 && seen2 == 1));
  return 0;
}

int main(void)
{
  pthread_t a, b;
  pthread_create(&a, 0, body, 0);
  pthread_create(&b, 0, body, 0);
  return 0;
}
