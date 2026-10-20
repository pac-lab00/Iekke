#include <pthread.h>
struct S { int pad; pthread_mutex_t mu; } s1, s2;
int counter;
void *t1(void *arg) { pthread_mutex_lock(&s1.mu); counter++; pthread_mutex_unlock(&s1.mu); return 0; }
void *t2(void *arg) { pthread_mutex_lock(&s2.mu); counter++; pthread_mutex_unlock(&s2.mu); return 0; }
int main() { pthread_mutex_init(&s1.mu, 0); pthread_mutex_init(&s2.mu, 0);
  pthread_t a, b; pthread_create(&a, 0, t1, 0); pthread_create(&b, 0, t2, 0);
  pthread_join(a, 0); pthread_join(b, 0); return 0; }
