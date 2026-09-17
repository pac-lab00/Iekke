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

`never-published-racefree.c` matters: a node that is allocated and written but
never linked into the shared list is correctly *not* reported, so the encoding
does track that an unreachable object cannot be involved in a race.

## The open case

`publish-then-access-racefree.c` is race free but is reported as FAILED.

    t1:  p = malloc(...);                  /* allocation writes p->datum   */
         insert(p, A);                     /* publishes p, under list_mutex */

    t2:  p = take(A);                      /* obtains p, under list_mutex   */
         lock(g); p->datum++; unlock(g);

Every access to `p->datum` after publication is under `g`, and `t2` can only
obtain `p` after `insert` released `list_mutex`. So

    allocation-time write  <  insert/unlock  <  take/lock  <  p->datum++

and the two accesses to `p->datum` are ordered by the lock-mediated
publication chain. There is no race.

The encoding reports one because the race condition it builds is, in effect,
"two conflicting accesses from different threads that can be placed adjacently
with no *other access to the same variable* in between". `no_interf` only
quantifies over accesses to that one variable, so the `list_mutex`
handshake -- which happens on `A->next`, a *different* variable -- never enters
the constraint. The allocation-time write and `t2`'s access are the only two
events on `<obj>..datum`, so nothing intervenes and `same_round` is free to put
them in the same round.

Removing `t2`'s access to `datum` (`publish-no-datum-access-racefree.c`) makes
the report go away, which pins the pair down to exactly those two events.

Closing this needs happens-before established through *other* variables and
through lock acquire/release to be visible to the race constraint -- i.e. the
pre-publication writes of an object have to be ordered against the accesses
that can only follow publication. Bounding does not help: the report is
present at every bound.

This is the shape behind the remaining false alarms in the SV-COMP
`no-data-race` set (the `28-race_reach_8*` family and the libvsync queue and
lock benchmarks).

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
VERIFICATION SUCCESSFUL. Checking for surviving unwinding assertions before
trusting a "no race" answer would turn these wrong answers into unknowns.
