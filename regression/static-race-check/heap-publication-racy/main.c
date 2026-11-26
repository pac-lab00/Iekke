#include <pthread.h>
#include <stdlib.h>
int *p;
void *t1(void *a) { int *q = malloc(sizeof *q); *q = 0; p = q; *q = 5; return 0; }
void *t2(void *a) { int *r = p; if (r) { int v = *r; } return 0; }
int main() { pthread_t a, b; pthread_create(&a, 0, t1, 0); pthread_create(&b, 0, t2, 0); pthread_join(a, 0); pthread_join(b, 0); return 0; }
