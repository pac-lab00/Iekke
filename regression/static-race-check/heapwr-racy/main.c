#include <pthread.h>
#include <stdlib.h>
int *G1;
void *t1(void *a){ G1[0] = 1; return 0; }
void *t2(void *a){ G1[1] = 2; return 0; }
int main(){ G1 = malloc(8); pthread_t a,b; pthread_create(&a,0,t1,0); pthread_create(&b,0,t2,0); pthread_join(a,0); pthread_join(b,0); return 0; }
