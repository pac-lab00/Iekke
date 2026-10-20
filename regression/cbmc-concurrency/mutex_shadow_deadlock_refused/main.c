#include <pthread.h>
pthread_mutex_t a, b; int x;
void *t1(void *arg) { pthread_mutex_lock(&a); pthread_mutex_lock(&b); x++; pthread_mutex_unlock(&b); pthread_mutex_unlock(&a); return 0; }
void *t2(void *arg) { pthread_mutex_lock(&b); pthread_mutex_lock(&a); x++; pthread_mutex_unlock(&a); pthread_mutex_unlock(&b); return 0; }
int main() { pthread_mutex_init(&a,0); pthread_mutex_init(&b,0); pthread_t h1, h2; pthread_create(&h1, 0, t1, 0); pthread_create(&h2, 0, t2, 0); pthread_join(h1, 0); pthread_join(h2, 0); return 0; }
