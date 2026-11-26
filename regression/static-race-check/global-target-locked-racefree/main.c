#include <pthread.h>
int g; int *g1, *g2; pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
void *t(void *a){ pthread_mutex_lock(&m); (*g1)++; pthread_mutex_unlock(&m); return 0; }
int main(){ g1 = g2 = &g; pthread_t a,b; pthread_create(&a,0,t,0); pthread_create(&b,0,t,0); pthread_join(a,0); pthread_join(b,0); return *g2; }
