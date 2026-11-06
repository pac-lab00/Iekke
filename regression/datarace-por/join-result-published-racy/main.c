// A pointer to a global comes back from pthread_join, and main writes through
// it while another thread reads the global: a race. The result was read
// from an array of unbounded size whose points-to set was never topped up
// from threads symexed later, so the write went nowhere
// (pthread-join-result/shared-buffer).
#include <pthread.h>
int buf[4];
int seen;
void *reader(void *arg)
{
  seen = buf[0];
  return 0;
}
void *get_buffer(void *arg)
{
  return buf;
}
int main(void)
{
  pthread_t r, t;
  void *res = 0;
  pthread_create(&r, 0, reader, 0);
  pthread_create(&t, 0, get_buffer, 0);
  pthread_join(t, &res);
  int *p = res;
  if(p != 0)
    p[0] = 1;
  pthread_join(r, 0);
  return 0;
}
