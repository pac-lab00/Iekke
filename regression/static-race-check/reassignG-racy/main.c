#include <pthread.h>
#include <stdlib.h>
int *G;
void *t(void *a){ int v = G[0]; return 0; }
int main(){ G = malloc(4); pthread_t a; pthread_create(&a,0,t,0); G = malloc(4); G[0]=1; pthread_join(a,0); return 0; }
