#include <pthread.h>
int x; pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
void get(pthread_mutex_t *l){ pthread_mutex_lock(l); } void put(pthread_mutex_t *l){ pthread_mutex_unlock(l); }
void *t(void *a){ get(&m); x++; put(&m); return 0; }
int main(){ pthread_t a,b; pthread_create(&a,0,t,0); pthread_create(&b,0,t,0); return 0; }
