// 40 threads each update one shared int; with the loop unwound 20 times the
// unwinding assertion must fail. Deagle's closure solver, the default without
// --rounds, reported it as holding.
#include <pthread.h>
int limit;
void *f(void *a) { int l; l = limit; limit = l + 1; return 0; }
int main()
{
  limit = 40;
  for(int i = 0; i < 40; ++i)
  {
    pthread_t t;
    pthread_create(&t, 0, f, 0);
  }
  return 0;
}
