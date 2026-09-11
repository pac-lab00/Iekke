// EXPECT: VERIFICATION FAILED under --rounds; g rejected with "root t1 may
// be spawned more than once". Two pthread_create sites name the same start
// routine, so the single-spawn-site check must reject it even though the
// first two sites look mutually exclusive.
//
// two pthread_create sites naming the same root, under exclusive conditions
#include <pthread.h>
#include <assert.h>
int g = 0;
int c;
void *t1(void *arg){ for(g=0;g<2;g++){} assert(g==2); return 0; }
int main(){
  pthread_t a,b;
  if(c) pthread_create(&a,0,t1,0); else pthread_create(&b,0,t1,0);
  pthread_create(&b,0,t1,0);
  pthread_join(a,0); return 0;
}
