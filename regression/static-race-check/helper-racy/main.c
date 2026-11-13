#include <pthread.h>
#include <stdlib.h>
int x; void inc(void){ x++; }
void *t(void *a){ inc(); return 0; }
int main(){ pthread_t a,b; pthread_create(&a,0,t,0); pthread_create(&b,0,t,0); return 0; }
