// EXPECT: VERIFICATION FAILED under --rounds; g rejected with "2 roots".
// Wrapping the racing accesses in CPROVER atomic sections must not hide the
// mentions from the scan.
//
// accesses wrapped in CPROVER atomic sections
#include <pthread.h>
#include <assert.h>
int g = 0;
void *t1(void *arg){ __CPROVER_atomic_begin(); for(g=0;g<2;g++){} __CPROVER_atomic_end(); assert(g==2); return 0; }
void *t2(void *arg){ __CPROVER_atomic_begin(); g = 99; __CPROVER_atomic_end(); return 0; }
int main(){ pthread_t a,b; pthread_create(&a,0,t1,0); pthread_create(&b,0,t2,0); pthread_join(a,0); pthread_join(b,0); return 0; }
