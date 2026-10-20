#include <pthread.h>
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "f.c", 1, "reach_error"); }
pthread_mutex_t m; int dummy;
void *t(void *x) { pthread_mutex_lock(&m); if (pthread_mutex_trylock(&m) != 16) reach_error(); return 0; }
int main() { pthread_t h; pthread_mutex_init(&m, 0); pthread_create(&h, 0, t, 0); dummy = 1; pthread_join(h, 0); return 0; }
