#include <pthread.h>

int x;

void *thread(void *arg)
{
  x = 1;
  return 0;
}

int main(void)
{
  pthread_t id;
  pthread_create(&id, 0, thread, 0);
  int y = x;
  return y;
}
