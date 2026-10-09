#include <pthread.h>
#include <stdlib.h>
/* Control for publish-then-rmw-racy: the increment moves under A_mutex, the
   lock main reads under, so the two accesses are ordered and there is no
   race. The pre-publication writes are still excused from pairing; keeping
   them in the value flow must not turn them into a race. */
struct s { int datum; } *A;
pthread_mutex_t A_mutex = PTHREAD_MUTEX_INITIALIZER;
int sink;
void *t_fun(void *arg) {
  struct s *p = malloc(sizeof(struct s));
  p->datum = 7;
  pthread_mutex_lock(&A_mutex); A = p; p->datum++; pthread_mutex_unlock(&A_mutex);
  return 0;
}
int main(void) {
  pthread_t t;
  A = malloc(sizeof(struct s)); A->datum = 3;
  pthread_create(&t, 0, t_fun, 0);
  pthread_mutex_lock(&A_mutex); sink = A->datum; pthread_mutex_unlock(&A_mutex);
  return 0;
}
