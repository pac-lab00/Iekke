#include <pthread.h>
int x; int *G = &x;
void *t1(void *a){ (*G)++; return 0; }
void *t2(void *a){ x = 5; return 0; }
int main(){ pthread_t a,b; pthread_create(&a,0,t1,0); pthread_create(&b,0,t2,0); return 0; }
