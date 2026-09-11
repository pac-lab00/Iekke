// EXPECT: VERIFICATION FAILED under --rounds. Same defect as adv_L but the
// prologue path into h() is a C++ static constructor (S::S ->
// #cpp_dynamic_initialization#...) rather than a gcc constructor attribute.
//
// NEW ADVERSARIAL (C++): main writes g AFTER spawning t1, but only through
// helper h(). h() is also reachable from __CPROVER_initialize via a static
// constructor, so the analysis puts h in its "prologue" set and ignores the
// initial threads (post-spawn!) access to g through it.
extern "C" {
typedef unsigned long pthread_t;
int pthread_create(pthread_t *, const void *, void *(*)(void *), void *);
int pthread_join(pthread_t, void **);
}

int g = 0;
int other = 0;

void h(int v) { g = v; }

struct S { S(); };
S::S() { h(0); }
S global_obj;

void *t1(void *arg)
{
  for(g = 0; g < 2; g++) {}
  __CPROVER_assert(g == 2, "g==2");
  return 0;
}

void *t2(void *arg) { other = 7; return 0; }

int main()
{
  pthread_t a, b;
  pthread_create(&a, 0, t1, 0);
  pthread_create(&b, 0, t2, 0);
  h(99);
  pthread_join(a, 0);
  pthread_join(b, 0);
  return 0;
}
