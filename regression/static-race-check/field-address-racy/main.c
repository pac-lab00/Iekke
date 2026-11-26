#include <pthread.h>
struct s { int a, b; } g;
void set(int *p){ *p = 1; }
void *t1(void *x){ set(&g.a); return 0; }
void *t2(void *x){ set(&g.b); return 0; }
int main(){ pthread_t u,v; pthread_create(&u,0,t1,0); pthread_create(&v,0,t2,0); return 0; }
