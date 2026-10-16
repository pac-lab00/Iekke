// The same code on different arguments is not interchangeable. The thread
// given 1 writes 2; a thread that reads 2 fails. Only the first thread can
// read after the second one's write, and only if it runs entirely later:
// an ordering that ignored the arguments would forbid exactly that.

#include <assert.h>
#include <pthread.h>

int x;

void *body(void *arg)
{
  int v = x;
  x = (int)(long)arg + 1;
  assert(v != 2);
  return 0;
}

int main(void)
{
  pthread_t a, b;
  pthread_create(&a, 0, body, (void *)0);
  pthread_create(&b, 0, body, (void *)1);
  return 0;
}
