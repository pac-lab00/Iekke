#include <pthread.h>
#include <stdlib.h>
struct s { int datum; struct s *next; };
struct s *slot;
struct s *new(void) {
  struct s *p = malloc(sizeof(struct s));
  if (!p) abort();
  p->next = 0;
  return p;
}
void list_add(struct s *node, struct s *list) {
  struct s *temp = list->next;
  list->next = node;
  node->next = temp;
}
void *t_fun(void *arg) {
  struct s *lost = new(); (void)lost;
  return 0;
}
int main(void) {
  pthread_t t1;
  slot = new();
  list_add(new(), slot);
  pthread_create(&t1, 0, t_fun, 0);
  return 0;
}
