#include <pthread.h>
#include <stdlib.h>
int * _Atomic P;
void *t1(void *a){ P[0]++; return 0; }
void *t2(void *a){ int v = P[0]; return 0; }
int main(){ P = (int*)malloc(8); pthread_t a,b; pthread_create(&a,0,t1,0); pthread_create(&b,0,t2,0); return 0; }
