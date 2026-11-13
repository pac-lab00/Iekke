#include <pthread.h>
#include <stdlib.h>
int x; pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER; int n;
void *t(void *a){ pthread_mutex_lock(&m); for(int i=0;i<n;i++){ x++; pthread_mutex_unlock(&m); } return 0; }
int main(){ pthread_t a,b; pthread_create(&a,0,t,0); pthread_create(&b,0,t,0); return 0; }
