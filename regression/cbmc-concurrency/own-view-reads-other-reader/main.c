// x has one writer, w; another thread reading it still sees w's write
#include <assert.h>
#include <pthread.h>
int x;
void *w(void *arg) { x = 1; int r = x; assert(r == 1); return 0; }
void *rd(void *arg) { int v = x; assert(v == 0); return 0; }
int main(void)
{
  pthread_t a, b;
  pthread_create(&a, 0, w, 0);
  pthread_create(&b, 0, rd, 0);
  return 0;
}
