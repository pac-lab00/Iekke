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

## The publication filter (opt-in, `LAZYPO_PUBFILTER`)

`collect_reads_and_writes` can exclude one class of the spurious pairs above.
A write to (or read of) a freshly allocated object, performed before the
allocating thread stores that object's address into a shared location, cannot
take part in a race: any other thread has to obtain the address by reading the
location it was published to, and that read is necessarily ordered after the
publishing write, which is itself ordered after the access in question. The
pointer dependence alone establishes happens-before, with or without a lock.
`never-published-racefree.c` is the degenerate case of the same argument.

Two details cost most of the implementation effort and are worth knowing before
touching it:

* after SSA renaming the publishing statement `list->next = node` carries the
  pointer *variable*, not `&dynamic_objectN`, so a small points-to map is
  needed to resolve pointer-valued symbols to the objects they may address;
* a `shared_write` SSA step is bookkeeping and carries a **nil** right-hand
  side — the value actually stored appears in the assignment step that
  *follows* it. This is the same reason the surrounding code peeks at `next` to
  recover the `with_expr`. Scanning the shared_write step's own `ssa_rhs` finds
  nothing at all.

With the filter on, `publish-then-access-racefree.c` is correctly SUCCESSFUL,
and every racy case here still reports FAILED — including `P3`-style races on
the published pointer itself, which are a different variable and keep all of
their events.

**It is off by default, and deliberately so.** Over the whole no-data-race
corpus (1030 benchmarks) it changes not one verdict in either direction: no
regressions, but no gains either. It does not rescue the nine remaining false
alarms, because those have a second, independent spurious pair that this
argument does not cover — in `28-race_reach_82`, two different `t2_fun` threads
each take a node from the list and increment `p->datum` while both hold
`data_mutex`, and that pair is still reported. Closing that needs the
*identity* of the accessed object tied to the pointer value under the
interleaving, which is the heart of CBMC issue #305.

So it earns nothing today, while the shapes it cannot yet reason about — an
object reachable by more than one path, or handed to a thread as a
`pthread_create` argument without ever being stored to a shared location —
would fail in the direction that hides a real race. That is the worst outcome
there is, so it stays opt-in until either those shapes are handled or it
actually buys something.

## Regression tests

The programs above are wired into the repo's harness, one test per directory
with a `main.c` and a `test.desc`, run by `regression/test.pl` and registered
in `regression/CMakeLists.txt`:

    cd regression/datarace-por && make test

Two of them assert on the **counterexample**, not only the verdict:
`racing-accesses-shown` and `atomic-section-race` require the trace to name
both racing accesses, via the `Racing read in thread N` /
`Racing write in thread N` lines that `--trace` emits.

That distinction is the point. Every trace defect found in this area — empty
counterexamples, counterexamples truncated mid-schedule, counterexamples
naming a single thread — left the **verdict correct**. A verdict-only test
passes throughout all of them. Checked directly: on the pre-fix binary both
tests still report `VERIFICATION FAILED` and produce zero `Racing` lines.

`publish-then-access-racefree` is recorded as `KNOWNBUG` rather than dropped.
It is race free and still reported as racing, because CBMC cannot soundly
handle a pointer-typed write to a shared location (`goto_symex_state.cpp`,
CBMC issue #305) and the wrapper must pass `--allow-pointer-unsoundness`.
Being a `KNOWNBUG` it is skipped at `CORE`, so it does not break CI, and
`test.pl -K` reports whether it still reproduces.

Note when writing new descriptors: `test.pl` rewrites a pattern that ends in
`$`, appending a line-ending suffix, and escapes backslashes — so `\d` does
not survive. Prefer unanchored patterns, or `[0-9]` over `\d`.
