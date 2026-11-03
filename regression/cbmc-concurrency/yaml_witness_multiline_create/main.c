#include <pthread.h>
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "main.c", 3, "reach_error"); }
int x;
void *worker(void *arg) { if (x == 1) reach_error(); return 0; }
int main()
{
  pthread_t t;
  int ret = pthread_create(&t, (const pthread_attr_t *)0, worker,
                           (void *)0);
  x = 1;
  pthread_join(t, 0);
  return ret;
}
