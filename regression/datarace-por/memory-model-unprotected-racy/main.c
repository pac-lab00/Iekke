#include <pthread.h>
/* Unprotected write/write: the adjacency constraint must not hide it. */
int x;
void *t(void *arg) { x = 1; return 0; }
int main(void)
{
  pthread_t id;
  pthread_create(&id, 0, t, 0);
  x = 2;
  return 0;
}
