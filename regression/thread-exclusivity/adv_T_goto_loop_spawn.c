// EXPECT: VERIFICATION FAILED under --rounds; g rejected with "root t1 may
// be spawned more than once". The loop is a raw backward goto, so the
// in_loop marking (not any source-level loop structure) has to catch it.
//
// pthread_create in a loop built from a backward goto, not a for/while.
#include <pthread.h>
#include <assert.h>
int g = 0;
void *t1(void *arg) { for(g = 0; g < 2; g++) {} assert(g == 2); return 0; }
int main(){
  pthread_t a; int i = 0;
L:
  pthread_create(&a,0,t1,0);
  i++;
  if(i < 2) goto L;
  pthread_join(a,0); return 0;
}
