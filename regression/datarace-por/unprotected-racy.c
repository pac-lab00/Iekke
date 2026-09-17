#include <pthread.h>
int shared;
void *w(void *a){ shared++; return 0; }
int main(void){
  pthread_t x,y;
  pthread_create(&x,0,w,0);
  pthread_create(&y,0,w,0);
  pthread_join(x,0); pthread_join(y,0);
}
