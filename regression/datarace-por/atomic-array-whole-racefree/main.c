#include <pthread.h>
_Atomic int a[100];
int nondet_int(void);
void *t(void *p) { int i = nondet_int(); __CPROVER_assume(0 <= i && i < 100); a[i] = 1; return 0; }
int main() { pthread_t h; pthread_create(&h, 0, t, 0); int j = nondet_int(); __CPROVER_assume(0 <= j && j < 100); int r = a[j]; pthread_join(h, 0); return r; }
