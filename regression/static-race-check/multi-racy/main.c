#include <pthread.h>
#include <stdlib.h>
int x; void *t(void *a){ x++; return 0; }
int main(){ pthread_t id[3]; for(int i=0;i<3;i++) pthread_create(&id[i],0,t,0); return 0; }
