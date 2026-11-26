#include <pthread.h>
#include <stdlib.h>
int *G1, *G2;
void *t1(void *a){ G1[0] = 1; return 0; }
void *t2(void *a){ G2[0] = 2; return 0; }
int main(){ G1 = malloc(4); G2 = G1; pthread_t a,b; pthread_create(&a,0,t1,0); pthread_create(&b,0,t2,0); pthread_join(a,0); pthread_join(b,0); return 0; }
