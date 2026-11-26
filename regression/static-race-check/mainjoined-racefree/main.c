#include <pthread.h>
#include <stdlib.h>
int x; void *t(void *a){ int y = x; return 0; }
int main(){ pthread_t a; x = 2; pthread_create(&a,0,t,0); pthread_join(a,0); x = 1; return x; }
