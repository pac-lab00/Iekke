#include <pthread.h>
#include <stdlib.h>
int *G, *H;
void set(int **pp){ *pp = H; }
void *t1(void *a){ G[0] = 1; return 0; }
void *t2(void *a){ H[0] = 2; return 0; }
int main(){ G = malloc(4); H = malloc(4); set(&G); pthread_t a,b; pthread_create(&a,0,t1,0); pthread_create(&b,0,t2,0); return 0; }
