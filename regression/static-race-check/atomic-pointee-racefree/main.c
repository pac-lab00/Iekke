#include <pthread.h>
#include <stdlib.h>
_Atomic int *A;
void *t1(void *a){ A[0]++; return 0; }
void *t2(void *a){ int v = A[0]; return 0; }
int main(){ A = (_Atomic int*)malloc(8); pthread_t a,b; pthread_create(&a,0,t1,0); pthread_create(&b,0,t2,0); return 0; }
