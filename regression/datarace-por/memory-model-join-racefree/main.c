#include <pthread.h>
/* main reads x only after joining the writer: the thread's exit and the
   join lie between the two accesses in every interleaving. */
int x;
void *t(void *arg) { x = 1; return 0; }
int main(void)
{
  pthread_t id;
  pthread_create(&id, 0, t, 0);
  pthread_join(id, 0);
  int r = x;
  return r;
}
