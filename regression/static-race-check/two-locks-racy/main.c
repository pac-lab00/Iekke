#include <pthread.h>
int x; pthread_mutex_t m1 = PTHREAD_MUTEX_INITIALIZER, m2 = PTHREAD_MUTEX_INITIALIZER;
void *t1(void *a) { pthread_mutex_lock(&m1); x++; pthread_mutex_unlock(&m1); return 0; }
void *t2(void *a) { pthread_mutex_lock(&m2); x++; pthread_mutex_unlock(&m2); return 0; }
int main() { pthread_t a, b; pthread_create(&a, 0, t1, 0); pthread_create(&b, 0, t2, 0); pthread_join(a, 0); pthread_join(b, 0); return x; }
