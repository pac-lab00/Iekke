#include <pthread.h>
_Atomic int a[3];
void *t(void *p) { a[1] = 1; return 0; }
int main() { pthread_t h; pthread_create(&h, 0, t, 0); int r = a[1]; pthread_join(h, 0); return r; }
