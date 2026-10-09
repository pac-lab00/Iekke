#include <pthread.h>
#include <stdlib.h>
/* A thread allocates a node, initialises it, publishes it under A_mutex and
   then increments it under B_mutex. main reads the node under A_mutex: that
   orders the read after the publication but not after the increment, so the
   increment and the read race.

   The publication filter excuses the allocation and `p->datum = 7` from race
   pairing, correctly. It used to drop them from the value flow as well, and
   the lazy chain then started from the increment's own store: the
   increment's read had to equal its result, the thread could never execute
   it, and the race was never witnessed. */
struct s { int datum; } *A;
pthread_mutex_t A_mutex = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t B_mutex = PTHREAD_MUTEX_INITIALIZER;
int sink;
void *t_fun(void *arg) {
  struct s *p = malloc(sizeof(struct s));
  p->datum = 7;
  pthread_mutex_lock(&A_mutex); A = p; pthread_mutex_unlock(&A_mutex);
  pthread_mutex_lock(&B_mutex); p->datum++; pthread_mutex_unlock(&B_mutex);
  return 0;
}
int main(void) {
  pthread_t t;
  A = malloc(sizeof(struct s)); A->datum = 3;
  pthread_create(&t, 0, t_fun, 0);
  pthread_mutex_lock(&A_mutex); sink = A->datum; pthread_mutex_unlock(&A_mutex);
  return 0;
}
