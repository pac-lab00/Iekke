#include <pthread.h>
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "main.c", 3, "reach_error"); }
void *grandchild(void *arg) { reach_error(); return 0; }
void *child(void *arg)
{
  pthread_t g;
  pthread_create(&g, 0, grandchild, 0);
  pthread_join(g, 0);
  return 0;
}
void *other(void *arg) { return 0; }
int main()
{
  pthread_t a, b;
  pthread_create(&a, 0, child, 0);
  pthread_join(a, 0);
  pthread_create(&b, 0, other, 0);
  return 0;
}
