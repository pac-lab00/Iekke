#include <pthread.h>
int x; pthread_mutex_t m[2];
void get(pthread_mutex_t *l){ pthread_mutex_lock(l); } void put(pthread_mutex_t *l){ pthread_mutex_unlock(l); }
void *t1(void *a){ get(&m[0]); x++; put(&m[0]); return 0; }
void *t2(void *a){ get(&m[1]); x++; put(&m[1]); return 0; }
int main(){ pthread_t a,b; pthread_create(&a,0,t1,0); pthread_create(&b,0,t2,0); return 0; }
