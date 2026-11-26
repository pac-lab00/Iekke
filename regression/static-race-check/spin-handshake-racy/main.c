#include <pthread.h>
int f1, f2, x;
void *t1(void *a) { f1 = 1; while (f2 != 1); f1 = 2; while (f2 != 2); x = 1; return 0; }
void *t2(void *a) { while (f1 != 1); f2 = 1; while (f1 != 2); f2 = 2; x = 2; return 0; }
int main() { pthread_t a, b; pthread_create(&a, 0, t1, 0); pthread_create(&b, 0, t2, 0); return 0; }
