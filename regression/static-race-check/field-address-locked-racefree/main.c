#include <pthread.h>
struct s { int a; pthread_mutex_t m; } g = { 0, PTHREAD_MUTEX_INITIALIZER };
struct s *P = &g;
void inc(struct s *q){ pthread_mutex_lock(&g.m); int *p = &q->a; (*p)++; pthread_mutex_unlock(&g.m); }
void *t(void *x){ inc(P); return 0; }
int main(){ pthread_t u,v; pthread_create(&u,0,t,0); pthread_create(&v,0,t,0); return 0; }
