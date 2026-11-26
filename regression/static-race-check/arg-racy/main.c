#include <pthread.h>
#include <stdlib.h>
void *t(void *a){ *(int*)a = 1; return 0; }
int main(){ int v; pthread_t a,b; pthread_create(&a,0,t,&v); pthread_create(&b,0,t,&v); return 0; }
