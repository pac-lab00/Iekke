#include <pthread.h>
int c = 0;
void *t1(void *arg) {
  int tmp = c;
  c = tmp + 1;
  return 0;
}
void *t2(void *arg) {
  int tmp = c;
  c = tmp + 1;
  return 0;
}
int main() {
  pthread_t a, b;
  pthread_create(&a, 0, t1, 0);
  pthread_create(&b, 0, t2, 0);
  pthread_join(a, 0);
  pthread_join(b, 0);
  __CPROVER_assert(c == 2, "lost update");
  return 0;
}
