# The lazy read-from encoding: where its cost is, and what has been done about it

This documents the round-robin read-from encoding in `lazy_po.cpp`, what the
formula it builds is actually made of, and the three optimisations built on top
of it -- one on by default, two held back pending evaluation. It is written to be read next to
the code.

Every number here was measured, not estimated. How to re-measure any of it is
in [Measuring](#measuring), and that section matters more than the rest: the
two results below were both invisible until the right instrument existed.

---

## 1. What the encoding costs

For each shared object the encoding builds a **lazy chain**: one link per
(write, round), in schedule order.

    lazy[w,r] = ite(exec(w,r), value_of_w, previous_link)      create_write_constraints

and ties each read to the link that precedes it, once per round
(`--read-implication`, the default form):

    exec(rd,r)  =>  rd == previous_shared(v, rd, r)            create_read_constraints

So both classes cost

> **rounds x accesses x WIDTH**

The round bound and the access counts are fixed by the semantics. **Width is
the only free multiplier**, and it is what both optimisations below attack.

### Clause share by category

Ablation on `28-race_reach_81-list_racing.i` at `--unwind 2 --rounds 8`
(695392 clauses, before either optimisation), second column
`fib_unsafe-12.i` at `u27 r13`:

| category | 81-list_racing | fib_unsafe-12 |
|---|---|---|
| read constraint | **53.5%** | **48.6%** |
| write constraint | **35.0%** | **29.1%** |
| cs constraint (exec/enabled) | 3.6% | 3.9% |
| abw | 2.2% | |
| por range | 1.2% | |
| cs order monotonicity + initial | 0.6% | 0.7% |
| abr / por first-read | 0.6% each | |
| obs canonical | 0.5% | |
| cs boundary tightening | 0.4% | 1.2% |
| atomic_block_canonical | 0.3% | |
| blocking statement | 0.0% | |
| lw / winr / nrp / low canonical | 0 constraints -- never fire | |

The shares sum to 98.5%, so this reads as a genuine partition.

> **The scheduling encoding is not where the formula is.** An older note put
> `cs`/`exec` at 40% of the formula. That figure counted **tree nodes**, and
> the `cs` expressions are about 3.5x shared, so in clauses they are 3.6%.
> Quote clause ablation, never a node count.

Grouped, and tracked against the round bound (same benchmark, `u2`):

| R | total clauses | data flow | POR + canonicality | scheduling |
|---:|---:|---:|---:|---:|
| 1 | 74 166 | 62.3% | 0.0% | 4.6% |
| 2 | 125 341 | 69.1% | 5.4% | 6.0% |
| 3 | 175 082 | 72.5% | 6.9% | 6.6% |
| 4 | 225 015 | 74.5% | 7.7% | 6.9% |
| 8 | 424 544 | 77.7% | 9.2% | 7.5% |
| 16 | 825 477 | 79.5% | 9.9% | 7.8% |

Everything is linear in R. The intercept is about **24 300 clauses** that do
not depend on the round bound (CBMC's base SSA), and each additional round
costs about **49 900 clauses**, split

| | per round |
|---|---|
| read + write | 40 600 (81%) |
| POR | 5 400 (11%) |
| scheduling | 4 100 (8%) |

So **81% of the marginal cost of a round is data flow.** POR is zero at `R=1`
and appears only from `R=2`, as expected.

---

## 2. `--narrow-shared`: carry only the bytes that are read

**Default on.** `--no-narrow-shared` restores the full-width chain.

A `pthread_mutex_t` is the real 24-byte glibc union -- **192 bits** -- but
CBMC's own model reads and writes exactly **one byte** of it:

```c
typedef signed char __CPROVER_mutex_t;            /* pthread_lib.c:108 */
__CPROVER_assume(!*((__CPROVER_mutex_t *)mutex));
*((__CPROVER_mutex_t *)mutex) = 1;
```

The access goes through a **type-punned pointer**, so it becomes a
`byte_update` on the whole object, and `field_sensitivityt` -- which splits
`ID_member` and `ID_index` only -- never separates that byte out. This is
exactly why heap objects get per-field SSA names (`..datum`, `..next`) and
mutexes do not.

Per-variable ablation on `28-race_reach_81`:

| variable | clauses | share | width |
|---|---:|---:|---:|
| `__global_lock` | 164 492 | **23.7%** | 192 bits |
| `list_mutex` | 110 658 | **15.9%** | 192 bits |
| `dynamic_object1..datum` | 49 120 | 7.1% | 32 bits |
| `main::1::t2_ids` | 42 614 | 6.1% | |
| `__CPROVER_threads_exited` | 35 833 | 5.2% | |

**Two locks, 39.6% of the formula, to carry 8 bits of state.**

### The idea

`compute_narrowings` collects, per object, the union of byte ranges that some
`byte_extract` **reads**, and narrows the chain to that slice.

**Writes do not widen the chain.** What a write produces can always be sliced
out of its full-width right-hand side, and that is paid once per write rather
than once per (write, round). This is what keeps the analysis simple: only
read ranges matter.

It bails -- keeping the full width -- on any use of the object that would
observe the dropped bits: a whole-object copy, a comparison, an argument.
`ID_address_of` is **not** such a use (taking an address does not read the
value), the same assumption `field_sensitivityt` makes.

One wrinkle worth knowing: the chain field is a `symbol_exprt`, so where
narrowing applies the round-0 sentinel has to be a fresh symbol of the slice's
type, tied to the slice by one extra constraint.

### Measured

    28-race_reach_81-list_racing   695392 -> 424544 clauses, same verdict
    76 hard no-data-race tasks     0 verdict differences
                                   43 of 76 shrink by >10%, best 4.18x
                                   (28-race_reach_42-trylock2_racefree,
                                    268375 -> 64135 clauses, 649 -> 375 ms)

---

## 3. `--thread-private`: objects only one thread touches

Pass `--thread-private` to enable it. Still off by default pending a re-run of
the unresolved tasks at the real competition timeout -- see
[Measured](#measured-1).

Sharedness is decided upstream **per program, never per object**: goto-symex
emits `shared_read`/`shared_write` for any global or heap object as soon as
more than one thread exists, and never asks which threads actually touch a
given object. So a global that only `main` reads and writes still gets the
full rounds-deep chain, for a read-from that `main`'s own program order
already fixes -- no other thread can interleave a write into it.

`LAZYPO_THREAD_TALLY` counts distinct threads per object. On
`28-race_reach_81`, **ten of thirty objects are single-thread and hold 22.5% of
the formula from 296 constraints**:

| object | threads | share |
|---|---:|---:|
| `main::1::t2_ids` | 1 | 10.0% |
| `main::1::t1_ids` | 1 | 9.4% |
| `__CPROVER_next_thread_id` | 1 | 3.2% |
| 7 others | 1 | ~0.1% |

The thread-id arrays are locals of `main`, written by `pthread_create` and read
by `pthread_join`. It is not one benchmark: over the 76 hard no-data-race
tasks **every one** has at least one such object, **70 of 75 have at least 30%
of their objects** in this class, and the mean is **60.4%**.

### The idea

Such an object is moved out of `global_variables` **and out of
`reads`/`writes`**, so POR, the canonicality constraints and data-race
detection skip it -- correctly, because an object one thread touches cannot
race. Its read-from is then stated once, over a chain in program order, each
link guarded by `happens_in_any_round` (the disjunction over rounds of that
access's `exec`) rather than by a particular round.

`create_cs_constraint` iterates threads and labels, **not** `global_variables`,
so the schedule encoding and the `exec` symbols are untouched.

**It classifies first and only then acts.** Rewriting the chain renumbers
variables, and a multi-million-clause SAT search is chaotic in that respect, so
the transformation is skipped entirely unless the private objects hold at least
**1% of all shared accesses**. See the diagnosis below for why that gate
exists and what the two measured points are.

> **Trap.** Leaving the accesses in `reads`/`writes` while removing the object
> from `global_variables` crashes `create_ABW_windows` with *"window threshold
> must skip id 0"*: the POR windows index into a lazy chain the object no
> longer has. Both have to move together.

### Measured {#measured-1}

    28-race_reach_81   424544 -> 336547 clauses (-20.7%), same verdict
    combined with --narrow-shared: 695392 -> 336547 = 2.07x smaller

On the 398 tuned tasks, as the increment on top of `--narrow-shared`:

    376 tasks solved by both:  320.5s -> 300.7s  (1.07x)
    77 tasks faster by >10%,  20 slower by >10%
    1 ANSWER LOST

**Two caveats on that "lost answer".** First, those runs used `TO=300`, and
the competition timeout is **900 s** -- `elimination_backoff_stack` answers in
408 s, so nothing is actually lost at the real limit. Second, it was a real
slowdown regardless, and worth understanding.

### Diagnosed: perturbation without benefit

In isolation, three runs each, `elimination_backoff_stack` went **283 / 283 /
321 s** to **408 / 411 / 460 s** -- a reproducible 1.44x, not a boundary flake.
Bisected: with only `--narrow-shared` it runs in 284 s, so the narrowing is
neutral there and `--thread-private` alone caused it.

The cause is that on that benchmark the change does **nothing**:

| | single-thread accesses | formula change |
|---|---:|---:|
| `elimination_backoff_stack` | 38 of 9472 = **0.4%** | 6 023 725 -> 6 018 418 = **-0.09%** |
| `28-race_reach_81-list_racing` | 37 of 276 = **13.4%** | 424 544 -> 336 547 = **-20.7%** |

It removes essentially nothing from the 6-million-clause formula, but it still
renumbers every variable after the first change, and the search lands on a
different and worse trajectory. It is search luck, not a structural cost --
which is why the aggregate goes the other way 77 times out of 97.

So the fix follows from the diagnosis: **do not perturb a formula you are not
materially improving.** With the 1% gate, `--thread-private` leaves
`elimination_backoff_stack` **byte-identical** to the baseline (1 647 137
variables, 6 023 725 clauses) while `28-race_reach_81` keeps the full 20.7%.


---

## 4. `--array-rf`: answer an element read by matching the writes

Pass `--array-rf` to enable it. Off by default pending the 398-task evaluation.

`a[i] = v` is `a#2 = with(a#1, i, v)` in the SSA, so **an array write is a
read-modify-write of the whole array**, and the chain has to carry every element
once per (write, round). Ablating the array-typed shared objects across the hard
no-data-race family:

| benchmark | total clauses | in array objects |
|---|---:|---:|
| `25_stack_longer-1` | 538 556 | **89.7%** |
| `queue_longer` / `queue_longest` | 521 479 | **89.3%** |
| `26_stack_cas` family | ~786 000 | **88.7%** |
| `queue_ok_longer` | 270 517 | 83.3% |
| `stack_longest-1` | 90 639 | 64.7% |
| `elimination_backoff_stack` | 8 525 534 | 0.2% |

The objects are `memory` (the `int memory[1921]` of pthread-ext),
`stored_elements`, `arr`, `queue..element`, and `__CPROVER_threads_exited`
everywhere.

### The chain defeats an optimisation CBMC already has

That table is measured **with `arrays-uf=auto` on**, and `--narrow-shared`
cannot reach it either -- it slices byte ranges, and an array has no fixed
width. Sequential CBMC does not have this problem at all. An `int[N]` with three
symbolic accesses:

| N | default (uf auto) | `--arrays-uf-never` |
|---:|---:|---:|
| 100 | 5 401 | 16 525 |
| 1 000 | 5 497 | 160 525 |
| 10 000 | **4 141** | 1 600 525 |

**Flat in the array size.** CBMC's array decision procedure already ties the
cost to the index set rather than the array's size. What breaks it here is the
round-robin: the chain re-materialises the array value R times, and each copy
drags the whole array back in. So this is not a new array decision procedure --
it removes what was defeating CBMC's.

### The encoding

For a read of `a[j]` at schedule position p:

    ite(exec(w_n) && i_n == j, val_n,
    ite(exec(w_{n-1}) && i_{n-1} == j, val_{n-1}, ... , default))

over the writes before p in schedule order. The cost stops depending on the
array's **size** and depends on the number of **writes**, which in these SSAs is
a single digit: 9 and 13 for `memory`, 4 for `stored_elements`, 3 for `arr`. The
honest caveat is that writes count per round -- a read in round r sees earlier
rounds too -- so the selection is W x R deep, not W.

**Preconditions, all checked and all bail-outs:** no use of the object as a
whole (a copy, a comparison, an argument has no index to match on); every write
is a `with` at a single index, or a uniform constant initialiser, which also
supplies the value before any write; and every `index()` names a shared read
event, since that is what places it in the schedule.

The chain's `lazy_variables` entries are still built. POR, the canonicality
constraints and data-race detection key on their **ids**; only
`previous_shared` consumes the **values**, so only those are dropped.

### It is not a global win, so a cost model chooses per object

A chain amortises over many reads and is the better structure for a narrow
object read often. The nested selection is better for a wide object written
rarely. Pointer fan-out is the opposite extreme -- four 32-bit objects, 24 reads
each -- where the same encoding was estimated **40x worse**, and it correctly
stays off there. The flag requires a 2x margin before firing.

### Measured

    25_stack_longer-1    538556 -> 52944 clauses (10.2x)
    26_stack_cas         786064 -> 84792        ( 9.3x)
    queue_longer         521479 -> 170182       ( 3.1x)
    stack_longest-1       90639 -> 37070        ( 2.4x)

Validated where it fires **and** values matter -- the array-heavy benchmarks
under `unreach-call`, 63 tasks, **zero verdict differences**, with the six
expected-false ones still reporting FAILED on formulas 3x to 12x smaller
(`25_stack_longer-1` 527 442 -> 41 830; `26_stack_cas_longer-1` 768 918 ->
67 646). Aggregate 20.9M -> 14.5M clauses.

### The bug this nearly shipped with

The first version **proved away a reachable violation** -- it reported
SUCCESSFUL on a program whose assertion is genuinely false. A missed bug, not a
false alarm.

The cause was an ordering slip. The selection was folded with the writes walked
backwards and the rounds forwards, which put the **first write at the last
round** outermost -- the zero initialiser -- forcing every read to 0. The
outermost `ite` is the one that wins, so candidates must be folded in
**increasing** schedule position; they are now sorted explicitly rather than
relying on loop nesting.

**An A/B over all 76 hard no-data-race tasks did not catch it.** Under
`--datarace` the verdict depends on the access **events**, not on what the
accesses read, so the whole family was blind to a value bug by construction. A
three-line hand-written test with a reachable violation caught it immediately.

> **Carry this forward.** Validate a value-encoding change on `unreach-call`,
> and write the discriminating test in **both** directions before trusting any
> sweep: a safe program catches under-constraining, a **reachable violation**
> catches over-constraining. A suite of SUCCESSFUL results cannot tell the
> second from a correct answer.

---

## 5. Measuring

Three instruments, each gated on an environment variable. **Known-answer
control every one before trusting it**: with the variable unset, and with a
setting that should match nothing, the formula must be byte-identical.

### `LAZYPO_ABLATE=<comma-separated substrings>`

Marks matching constraints `step.ignore` and reports the drop in clause count.
Matching is on the constraint's description, and the read/write constraints
**name their shared variable**, so `LAZYPO_ABLATE="constraint __global_lock"`
prices one variable and `LAZYPO_ABLATE="read constraint,write constraint"`
prices the whole data flow.

Put the marking loop at the top of `symex_target_equationt::convert()`, **not**
inside `convert_constraints`: constraints are converted in two passes, and
`convert_constraints` deliberately skips the POR/canonicality categories for a
later one.

Ablation changes what the formula means, so verdicts may move. It is an
instrument, not an optimisation. Deltas are not perfectly additive either --
removing one category changes what the rest share -- though on the benchmarks
above they summed to 98.5%.

### `LAZYPO_THREAD_TALLY=1`

Per object: distinct threads, and the read and write counts.

### `LAZYPO_DEAD_AUDIT=1`

Per object: reads whose value nothing uses, and the **fan-out** -- how many
distinct objects each goto instruction reads.

> Key the fan-out on the **goto instruction**, not on the label and not on the
> source line. Dereferencing a pointer with k targets expands into k separate
> shared accesses and gives each its own label, so by label they all look like
> distinct program points; and the preprocessed `.i` file puts whole statements
> on one line, so lines cannot separate them either.

### Pitfalls that have cost real time here

* **Tree-node counts over-state.** They said `cs`/`exec` was 40.9% of the
  formula; clause ablation says 3.6%.
* **MUX-bit share is not clause share.** `per-thread-array-join-counter-2` is
  72.3% "wide" by MUX bits and gains **2.6%** in clauses, because array axioms
  dominate it.
* **Rebuilding a benchmark with a narrower type is confounded** -- it also
  changes allocated object sizes. It suggested 17x where the honest figure was
  far smaller.
* **The competition timeout is 900 s, not 300.** Every harness here defaults
  to `TO=300`, and that alone turned `--thread-private` into a "lost answer"
  for a task that answers in 408 s. Use `TO=900` for any judgement about
  whether something costs an answer.
* **Always measure on the `.i` file.** The `.c` and `.i` forms give identical
  clause counts but different CNF and different solver paths.
* **Never sweep processes by name.** A harness that killed every process named
  `cbmc` killed a regression suite running at the same time; seven tests
  reported `Killed`, which looks exactly like a code regression.

---

## 6. Measured dead ends -- do not re-try these

| idea | result |
|---|---|
| `OPTIMAL_COMPACT_ITE` (extra implied clauses per MUX bit) | 39% slower on the `.i` file |
| removing guards from `exec` | invents a violation on `dekker`; reads-only is correct but 5% slower |
| `LAZYPO_NO_GUARD_HANDLES` | -1.2% variables, +10% time |
| guard hoisting | 0.6% |
| write-chain prefix scan | 12x slower |
| demotion | -20% clauses, 1.01x |
| CaDiCaL instead of Glucose | 0.96x bug-finding with a lost answer; 0.52x on hard proofs |
| `--refined-pointer-analysis` to cut pointer fan-out | fan-out grows 4 -> 7 objects, 336547 -> 637059 clauses (1.9x worse) |
| de-duplicating guards in the solver cache | the duplication is real but **0.95%** of converted nodes |

On the last one: `prop_conv_solvert`'s cache is keyed on the exprt, so `a&&b`
and `b&&a` get two literals. Re-keying on a canonical form finds 918 of 35971
conversions duplicated. Every worst offender is a path guard, and the
mechanism is real -- `handling_guards` stores `G && reach` unsimplified while
writing `simplify(reach => (G => c))` -- but subterms stay shared, so only the
top gate is repaid.

The MUX encoding itself is near minimal (about 2 clauses per bit), and
`--read-implication` is already on.

---

## 7. Open candidates, with measured prizes

Ranked by what they are worth on `28-race_reach_81` after both optimisations
(336 547 clauses).

1. ~~Shared arrays travel whole through the chain~~ -- **done**, see
   [`--array-rf`](#4---array-rf-answer-an-element-read-by-matching-the-writes).
   The original note read:

   **Shared arrays travel whole through the chain -- 10.6%.**
   `lazy[w,r] = ite(exec, <the entire array>, prev)`.
   `__CPROVER_threads_exited` costs **exactly the same 35 833 clauses with and
   without `--arrays-uf-never`**, so this is *not* array axioms -- it is the
   chain carrying the array as a value. Splitting such an array by index would
   fix it: here it is written at a constant index (the thread's own id) and
   read over an index set the size of the thread count, five. `--narrow-shared`
   does not reach this, because it works on byte ranges and bails on arrays.

2. **Pointer fan-out on heap objects -- 41.7%, but currently out of reach.**
   20 goto instructions produce 38 shared read objects; 5 of them read 4
   objects each, because `take(A)` can return any of the three list nodes.
   The fan-out is real, but the aliasing conditions are **already inside the
   guards**, hence inside `exec`, so the expanded accesses are already
   conditioned on the right pointer -- there is nothing to add there. The only
   lever tried, `--refined-pointer-analysis`, makes it 1.9x worse. The genuine
   fix is value-set precision, which is a project of its own.

3. **Memory-tracking globals -- 3.6%.** `__CPROVER_deallocated`,
   `__CPROVER_memory_leak`, `__CPROVER_malloc_is_new_array` and friends are
   only meaningful when the property checks them.

4. **Dead shared reads -- 12 of 172 here (7% of reads).** The SSA slicer is
   skipped entirely once the equation has threads (`bmc_util.cpp`, with a
   standing TODO for a thread-aware one). A **read** whose value nothing uses
   is dead regardless of threads -- reading is not observable to another
   thread -- so this much can be sliced thread-obliviously, outside
   `--datarace` where reads do participate in races. Small prize here.

---

## 8. Regression tests

In `regression/cbmc-concurrency/`:

| test | what it pins down |
|---|---|
| `narrow_shared_mutex` | mutual exclusion rides on the narrowed byte; mutation-checked -- remove the locks and it reports FAILED |
| `narrow_shared_mutex_full_width` | the `--no-narrow-shared` arm; the two encodings must agree |
| `narrow_shared_whole_object_read` | the bail is **observable**: copying the mutex whole gives an identical formula either way (24071 variables / 83845 clauses), against 63131 -> 26427 for the same program without the copy |
| `thread_private_object` | the read sees the last write in program order, under its guard; mutation-checked |
| `thread_private_object_shared_chain` | the `--no-thread-private` arm |
| `array_read_from` | the under-constraining direction, with the array large enough that the cost model turns `--array-rf` on |
| `array_read_from_violation` | the **over-constraining** direction -- a reachable violation that must still be found; this is the one that caught the ordering bug |
| `array_read_from_chain` | the default path, which has to agree |

`--thread-private` is off by default, so its two tests pass it explicitly.

Both `--no-` flags reproduce the pre-change formula **to the digit**
(`28-race_reach_81` at `u2 r8`: 184325 variables / 695392 clauses with both
off, 123237 / 424544 with only narrowing on), which is the control showing each
change is confined to its own path.
