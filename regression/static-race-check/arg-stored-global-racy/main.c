#include <pthread.h>
int g; int *P;
void *t1(void *a){ P = (int*)a; return 0; }
void *t2(void *a){ if(P) (*P)++; return 0; }
int main(){ pthread_t x, y; pthread_create(&x,0,t1,&g); pthread_create(&y,0,t2,0); g = 1; return 0; }
