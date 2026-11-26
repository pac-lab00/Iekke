// EXPECT: VERIFICATION FAILED under --rounds; ar rejected with "2 roots".
// Indexed accesses must be attributed to the array's base symbol.
//
// global array: t1 loops on ar[0], t2 writes ar[1] (same base symbol)
#include <pthread.h>
#include <assert.h>
int ar[2] = {0, 0};
void *t1(void *arg){ for(ar[0]=0; ar[0]<2; ar[0]++){} assert(ar[0]==2); return 0; }
void *t2(void *arg){ ar[0] = 99; return 0; }
int main(){ pthread_t a,b; pthread_create(&a,0,t1,0); pthread_create(&b,0,t2,0); pthread_join(a,0); pthread_join(b,0); return 0; }
