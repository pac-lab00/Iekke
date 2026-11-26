#include <pthread.h>
pthread_t tid;
void *worker(void *a) { return 0; }
void *reader(void *a) { pthread_join(tid, 0); return 0; }
int main() {
  pthread_t r;
  pthread_create(&r, 0, reader, 0);
  pthread_create(&tid, 0, worker, 0);
  pthread_join(r, 0);
  return 0;
}
