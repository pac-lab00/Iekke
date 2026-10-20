// Paired with mutex_shadow_destroy: a mutex destroyed and initialised again
// can be locked, so the violation is reachable (a model in which nothing
// after the destroy ran would pass mutex_shadow_destroy vacuously).
#include <pthread.h>
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "f.c", 1, "reach_error"); }
pthread_mutex_t m; int dummy;
void *t(void *x) { pthread_mutex_lock(&m); reach_error(); return 0; }
int main() { pthread_t h; pthread_mutex_init(&m, 0); pthread_mutex_destroy(&m); pthread_mutex_init(&m, 0);
  pthread_create(&h, 0, t, 0); dummy = 1; pthread_join(h, 0); return 0; }
