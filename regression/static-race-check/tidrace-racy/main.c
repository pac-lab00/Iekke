#include <pthread.h>
#include <stdlib.h>
pthread_t g; int z;
void *t(void *a){ z = (int)g; return 0; }
int main(){ pthread_t a; pthread_create(&a,0,t,0); pthread_create(&g,0,t,0); return 0; }
