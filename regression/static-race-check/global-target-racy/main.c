#include <pthread.h>
int g; int *g1, *g2;
void *t(void *a){ (*g1)++; return 0; }
int main(){ g1 = g2 = &g; pthread_t a,b; pthread_create(&a,0,t,0); pthread_create(&b,0,t,0); return 0; }
