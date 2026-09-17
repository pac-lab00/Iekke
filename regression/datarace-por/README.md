# Data-race encoding: minimal cases

Small self-contained programs isolating what the `--datarace` encoding gets
right and what it still gets wrong. Run each with

    cbmc <file> --allow-pointer-unsoundness --no-assertions --datarace \
         --unwind 2 --rounds 3 --por

## Cases that behave correctly

| file | expected | current |
|---|---|---|
| `unprotected-racy.c` | FAILED | FAILED |
| `mutex-protected-racefree.c` | SUCCESSFUL | SUCCESSFUL |
| `never-published-racefree.c` | SUCCESSFUL | SUCCESSFUL |
| `publish-no-datum-access-racefree.c` | SUCCESSFUL | SUCCESSFUL |
| `message-passing-racefree.c` | SUCCESSFUL | SUCCESSFUL |

Two of these matter as controls.

`never-published-racefree.c`: a node is allocated and written but never linked
into the shared list. It is correctly *not* reported, so the encoding does
track that an unreachable object cannot be involved in a race.

`message-passing-racefree.c`: one thread writes `X`, then sets an `int` flag
under a mutex; the other reads the flag under the same mutex and touches `X`
only if it was set. This is exactly the publication pattern of the failing
case below, except that what gets published is an `int`. It is correctly
reported race free, so lock-mediated happens-before is handled.

## The open case

`publish-then-access-racefree.c` is race free but is reported as FAILED.

    t1:  p = malloc(...);                  /* allocation writes p->datum    */
         insert(p, A);                     /* publishes p, under list_mutex */

    t2:  p = take(A);                      /* obtains p, under list_mutex   */
         lock(g); p->datum++; unlock(g);

`t2` can only obtain `p` after `insert` released `list_mutex`, so

    allocation-time write  <  insert/unlock  <  take/lock  <  p->datum++

and the two accesses to `p->datum` are ordered. There is no race.

The difference from `message-passing-racefree.c` is that what gets published
here is a **pointer**: `insert` performs `list->next = node`, a pointer-typed
write to a shared location. CBMC's concurrency encoding is unsound for exactly
that, and says so --- `src/goto-symex/goto_symex_state.cpp:108`, citing
CBMC GitHub issue #305:

    if(is_shared && lhs.type().id() == ID_pointer && !allow_pointer_unsoundness)
      throw unsupported_operation_exceptiont(
        "pointer handling for concurrency is unsound");

Without `--allow-pointer-unsoundness` the tool refuses to run these programs
at all (exit 6). The wrapper has to pass the flag, which downgrades the
refusal to a printed warning and carries on. The pointer value the reader
obtains is then not properly tied to the interleaving, so `t2` can be treated
as already holding the node pointer without `insert`'s publishing write having
been ordered before it. The pre-publication write and the post-publication
access are then free to land in the same round, and a race is reported.

Dropping the reader's access to `datum`
(`publish-no-datum-access-racefree.c`) makes the report go away, which pins
the pair to exactly those two events. No bound removes it.

This is the shape behind all nine remaining SV-COMP `no-data-race` false
alarms --- the `28-race_reach_8*` family and the libvsync lock and queue
benchmarks, which are lock-free algorithms that publish pointers into shared
structures. Every one of them prints the unsound-pointer warning.

Note this is an inherited CBMC limitation, not something the round-robin/POR
layer introduces; closing it means giving shared pointer-typed writes a sound
treatment across threads.

## Unrelated trap worth remembering

A too-small `--unwind` does not merely lose coverage, it can make the whole
program vacuous and turn a missed race into a confident "no race". The
`pthread-driver-races/char_pc8736x_gpio_*` tasks allocate through

    void *external_alloc(unsigned size) {
      char *p = malloc(size);
      for (unsigned i = 0; i < size; ++i) p[i] = nondet_char();
      return p;
    }

whose loop runs `sizeof(struct platform_device)` times. Below roughly
`--unwind 100` the loop is cut and everything after it, `pthread_create`
included, is assumed away: `__CPROVER_assert(0)` placed just before
`pthread_create` reports SUCCESS, and `--unwinding-assertions` reports
`external_alloc.unwind.0 ... FAILURE`, yet the tool still answers
VERIFICATION SUCCESSFUL.

Such a run is cheap to recognise: it never builds the datarace constraint and
never calls the solver, so its output has no `Datarace Enabled` line, no
`Adding Iekke constraints` line and no `N variables, M clauses` line. Refusing
to answer "no race" when those are absent would turn this class of wrong
answers into unknowns.
