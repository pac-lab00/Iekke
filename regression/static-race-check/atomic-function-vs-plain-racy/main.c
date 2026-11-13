#include <pthread.h>
int x; void __VERIFIER_atomic_inc(void){ x++; }
void *t1(void *a){ __VERIFIER_atomic_inc(); return 0; }
void *t2(void *a){ x = 3; return 0; }
int main(){ pthread_t a,b; pthread_create(&a,0,t1,0); pthread_create(&b,0,t2,0); return 0; }
