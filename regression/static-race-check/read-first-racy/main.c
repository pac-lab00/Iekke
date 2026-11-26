#include <pthread.h>
int x, y;
void *r(void *a) { int v = x; y = v; return 0; }
void *w(void *a) { x = 1; return 0; }
int main() { pthread_t a, b; pthread_create(&a, 0, r, 0); pthread_create(&b, 0, w, 0); pthread_join(a, 0); pthread_join(b, 0); return 0; }
