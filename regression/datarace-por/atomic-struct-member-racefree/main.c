#include <pthread.h>
struct S { _Atomic int f; int g; } s;
void *t(void *p) { s.f = 1; return 0; }
int main() { pthread_t h; pthread_create(&h, 0, t, 0); int r = s.f; pthread_join(h, 0); return r; }
