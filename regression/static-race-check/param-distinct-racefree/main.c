#include <pthread.h>
int x, y; void inc(int *p){ (*p)++; }
void *t1(void *a){ inc(&x); return 0; }
void *t2(void *a){ inc(&y); return 0; }
int main(){ pthread_t a,b; pthread_create(&a,0,t1,0); pthread_create(&b,0,t2,0); return 0; }
