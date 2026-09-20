#include <pthread.h>
int X, flag;
pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
void *t1(void *a){
  X = 1;                                  /* before the release */
  pthread_mutex_lock(&m); flag = 1; pthread_mutex_unlock(&m);
  return 0; }
void *t2(void *a){
  int f;
  pthread_mutex_lock(&m); f = flag; pthread_mutex_unlock(&m);
  if (f) X = 2;                           /* only after seeing the flag */
  return 0; }
int main(void){ pthread_t x,y;
  pthread_create(&x,0,t1,0); pthread_create(&y,0,t2,0);
  pthread_join(x,0); pthread_join(y,0); }
