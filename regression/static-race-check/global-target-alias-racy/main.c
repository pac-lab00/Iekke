#include <pthread.h>
int g; int *g1, *g2; pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
void *t1(void *a){ pthread_mutex_lock(&m); (*g1)++; pthread_mutex_unlock(&m); return 0; }
void *t2(void *a){ g = 5; return 0; }
int main(){ g1 = g2 = &g; pthread_t a,b; pthread_create(&a,0,t1,0); pthread_create(&b,0,t2,0); return 0; }
