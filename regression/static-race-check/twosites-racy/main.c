#include <pthread.h>
#include <stdlib.h>
int x; void *t(void *a){ x = 3; return 0; }
int main(){ pthread_t a, b; pthread_create(&a,0,t,0); pthread_create(&b,0,t,0); pthread_join(a,0); pthread_join(b,0); return 0; }
