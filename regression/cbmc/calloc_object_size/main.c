#include <stdlib.h>

// calloc must allocate an object of the size it was asked for.
//
// The model declared `alloc_size` and computed it only inside a line that had
// been commented out, so the variable was never assigned and
// __CPROVER_allocate received a nondeterministic size. Every calloc'd object
// then had an unconstrained size, and a bounds check on it could fail for an
// index plainly inside the array -- as here, where three elements are
// allocated and element zero is written.
//
// malloc, which does compute its size, was unaffected, and stock cbmc answers
// SUCCESSFUL on this program. The cost was real: pthread-complex/bounded_buffer
// is a safe program reported unsafe for exactly this reason.

int main(void)
{
  void **buf = calloc(3, sizeof(void *));
  if(buf == 0)
    return 0;

  buf[0] = 0; // inside the object by construction

  free(buf);
  return 0;
}
