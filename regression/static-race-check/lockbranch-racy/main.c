#include <pthread.h>
#include <stdlib.h>
int x, n; pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
void *t(void *a){ if(n) pthread_mutex_lock(&m); x++; if(n) pthread_mutex_unlock(&m); return 0; }
int main(){ pthread_t a,b; pthread_create(&a,0,t,0); pthread_create(&b,0,t,0); return 0; }
