// One thread frees what the other then reads: a use after free (valid-deref).
// The check for a deallocated object was commented out.
#include <pthread.h>
#include <stdlib.h>
int *p;
void *worker(void *arg)
{
  free(p);
  return 0;
}
int main(void)
{
  pthread_t t;
  p = malloc(sizeof(int));
  if(!p)
    return 0;
  *p = 1;
  pthread_create(&t, 0, worker, 0);
  pthread_join(t, 0);
  return *p;
}
