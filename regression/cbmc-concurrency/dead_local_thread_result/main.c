// A thread returns the address of its own local, which is dead once the
// thread has returned: dereferencing it is invalid (valid-deref). The check
// was commented out (pthread-join-result/dangling-local answered TRUE).
#include <pthread.h>
void *worker(void *arg)
{
  int local = 42;
  return &local;
}
int main(void)
{
  void *res;
  pthread_t t;
  pthread_create(&t, 0, worker, 0);
  pthread_join(t, &res);
  return *(int *)res;
}
