#include <pthread.h>
int x; void *t(void *a){ x++; return 0; }
int main(){ pthread_t a; pthread_create(&a,0,t,0); pthread_join(a,0); x = 5; pthread_create(&a,0,t,0); return 0; }
