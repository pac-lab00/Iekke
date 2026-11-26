// Threads created by a loop: every creation that a running thread needs
// gets its createThread edge (the edges were merged, the line repeating),
// and creations of threads that never run are left out, so unroll-bound
// counts only the loop iterations the path needs.
#include <pthread.h>
int x;
void *t(void *arg)
{
  x = 1;
  return 0;
}
int main(void)
{
  pthread_t h;
  while(1)
    pthread_create(&h, 0, t, 0);
  return 0;
}
