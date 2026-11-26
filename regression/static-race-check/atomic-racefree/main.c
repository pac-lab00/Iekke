#include <pthread.h>
#include <stdlib.h>
void __VERIFIER_atomic_begin(void); void __VERIFIER_atomic_end(void);
int x;
void *t(void *a){ __VERIFIER_atomic_begin(); x++; __VERIFIER_atomic_end(); return 0; }
int main(){ pthread_t a,b; pthread_create(&a,0,t,0); pthread_create(&b,0,t,0); return 0; }
