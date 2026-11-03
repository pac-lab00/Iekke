#include <pthread.h>
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "main.c", 3, "reach_error"); }
int x = 0;
void *t1(void *arg) { x = 1; return 0; }
void *t2(void *arg) { x = 2; return 0; }
int main()
{
  pthread_t a, b;
  pthread_create(&a, 0, t1, 0);
  pthread_create(&b, 0, t2, 0);
  pthread_join(a, 0);
  pthread_join(b, 0);
  if (x == 1) { reach_error(); }
  return 0;
}
