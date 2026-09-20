#include <pthread.h>
int shared;
pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
void *w(void *a){ pthread_mutex_lock(&m); shared++; pthread_mutex_unlock(&m); return 0; }
int main(void){
  pthread_t x,y;
  pthread_create(&x,0,w,0);
  pthread_create(&y,0,w,0);
  pthread_join(x,0); pthread_join(y,0);
}
