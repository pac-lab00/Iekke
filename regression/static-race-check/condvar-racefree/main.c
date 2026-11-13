#include <pthread.h>
#include <stdlib.h>
int x, flag; pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER; pthread_cond_t c = PTHREAD_COND_INITIALIZER;
void *t1(void *a){ pthread_mutex_lock(&m); while(!flag) pthread_cond_wait(&c,&m); x++; pthread_mutex_unlock(&m); return 0; }
void *t2(void *a){ pthread_mutex_lock(&m); flag = 1; x++; pthread_cond_signal(&c); pthread_mutex_unlock(&m); return 0; }
int main(){ pthread_t a,b; pthread_create(&a,0,t1,0); pthread_create(&b,0,t2,0); return 0; }
