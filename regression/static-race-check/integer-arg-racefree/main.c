#include <pthread.h>
int res[2];
void *t(void *a){ long i = (long)a; int v = (int)i; return 0; }
int main(){ pthread_t x[2]; for(long i=0;i<2;i++) pthread_create(&x[i],0,t,(void*)i); return 0; }
