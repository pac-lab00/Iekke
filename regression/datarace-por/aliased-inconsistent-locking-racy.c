#include <pthread.h>
#include <stdlib.h>
/* same shape as 09-regions_03-list2_rc but with NO pre-publication writes:
   the node reached as A->next and B->next is the same object, guarded by
   A_mutex in one place and B_mutex in the other -- a genuine race. */
struct s { int datum; struct s *next; } *A, *B;
pthread_mutex_t A_mutex = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t B_mutex = PTHREAD_MUTEX_INITIALIZER;
void *t_fun(void *arg){
  pthread_mutex_lock(&A_mutex); A->next->datum++; pthread_mutex_unlock(&A_mutex);
  pthread_mutex_lock(&B_mutex); B->next->datum++; pthread_mutex_unlock(&B_mutex);
  return 0; }
int main(void){
  pthread_t t1; int x, y;
  struct s *p = malloc(sizeof(struct s));
  A = malloc(sizeof(struct s));
  B = malloc(sizeof(struct s));
  A->next = p;
  B->next = p;
  pthread_create(&t1, 0, t_fun, 0);
  pthread_mutex_lock(&A_mutex); x = A->next->datum; pthread_mutex_unlock(&A_mutex);
  pthread_mutex_lock(&B_mutex); y = B->next->datum; pthread_mutex_unlock(&B_mutex);
  return 0; }
