// The width the concurrency encoding gives a mutex.
//
// The library models a mutex as { count, recursive, owner } over the front of
// pthread_mutex_t, and the encoding carries the bytes from the first field
// accessed to the last at every write. With `owner` an unsigned long at offset
// 4 that was 64 bits per write and round, and the mutex was the largest object
// in the formula of most small locking programs (45-67% of the clauses on
// pthread-ext/01b_inc, arithmetic_prog_bad, pthread-demo-datarace-1). A 16-bit
// owner next to the others makes it 32.

#include <pthread.h>
#include <assert.h>

pthread_mutex_t m;
int x;

void *t(void *arg)
{
  (void)arg;

  x = x + 1;

  return 0;
}

int main(void)
{
  pthread_t a, b;
  pthread_create(&a, 0, t, 0);
  pthread_create(&b, 0, t, 0);
  pthread_join(a, 0);
  pthread_join(b, 0);
  assert(x == 2);
  return 0;
}
