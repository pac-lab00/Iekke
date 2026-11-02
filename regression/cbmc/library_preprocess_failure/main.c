extern void abort(void);
extern int pthread_join(unsigned long th, void **ret);
int __VERIFIER_nondet_int(void);

int main()
{
  int x = __VERIFIER_nondet_int();
  if(!(x >= 0 && x < 1000))
    abort();
  // pthread_join's model includes <errno.h>, which pulls the broken header
  // below into the same library batch as abort's model
  if(x == 2000)
    pthread_join(0, 0);
  x = x * 1000000;
  return 0;
}
