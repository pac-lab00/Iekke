#include <pthread.h>
int x, n; void *t(void *a){ x = 1; return 0; }
int main(){ pthread_t a; pthread_create(&a,0,t,0); if(n) pthread_join(a,0); x = 2; return 0; }
