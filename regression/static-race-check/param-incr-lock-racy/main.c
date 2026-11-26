#include <pthread.h>
int x, y; pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
void inc(int *p){ pthread_mutex_lock(&m); (*p)++; pthread_mutex_unlock(&m); }
void *t1(void *a){ inc(&x); return 0; }
void *t2(void *a){ x = 4; return 0; }
int main(){ pthread_t a,b; pthread_create(&a,0,t1,0); pthread_create(&b,0,t2,0); return 0; }
