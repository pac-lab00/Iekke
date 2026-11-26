#include <pthread.h>
int g;
void *t(void *a){ int *p = (int*)a; (*p)++; return 0; }
int main(){ pthread_t x, y; pthread_create(&x,0,t,&g); pthread_create(&y,0,t,&g); return 0; }
