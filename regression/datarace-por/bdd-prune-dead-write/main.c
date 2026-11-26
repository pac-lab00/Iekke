#include <pthread.h>
int nondet_int();
int g;
void *t(void *a)
{
  int c = nondet_int();
  if(c & 1)
  {
    int d = nondet_int();
    if(d)
      d = 0;
    if(!(c & 1))
      g = 1;
  }
  return 0;
}
int main()
{
  pthread_t h;
  pthread_create(&h, 0, t, 0);
  g = 2;
  return 0;
}
