#include <pthread.h>
int x; pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
void *t(void *a) { for (int i = 0; i < 2; i++) { x++; } return 0; }
int main() { pthread_t a, b; pthread_create(&a, 0, t, 0); pthread_create(&b, 0, t, 0); pthread_join(a, 0); pthread_join(b, 0); return x; }
