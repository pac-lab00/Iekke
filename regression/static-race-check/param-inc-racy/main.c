#include <pthread.h>
int x; void inc(int *p){ (*p)++; }
void *t(void *a){ inc(&x); return 0; }
int main(){ pthread_t a,b; pthread_create(&a,0,t,0); pthread_create(&b,0,t,0); return 0; }
