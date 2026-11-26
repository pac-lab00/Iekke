// Creations in a loop do not exclude each other: both threads run, and they
// race on the same object.
#include <pthread.h>

int x;

void *worker(void *p)
{
  x = 1;
  return 0;
}

int main(void)
{
  pthread_t t[2];
  for(int i = 0; i < 2; i++)
    pthread_create(&t[i], 0, worker, 0);
  return 0;
}
