# POR and data races: why canonicality dropped real races, and what fixes it

Partial-order reduction is a primary contribution of this work, so this
document records exactly what was wrong with it, how that was established,
and what the fix does. Read it before quoting any POR number.

## 1. The claim

**Before the fix, POR answered SUCCESSFUL on programs that plainly race.**
Three lines are enough:

```c
int datum;
pthread_mutex_t datum_mutex;

void *thread(void *arg) {
  pthread_mutex_lock(&datum_mutex);  datum = 5;  pthread_mutex_unlock(&datum_mutex);
  return 0;
}

int main(void) {
  pthread_t id;
  pthread_create(&id, 0, &thread, 0);
  datum = 8;              /* unprotected: races with the write in the block */
  return 0;
}
```

    --unwind 2 --rounds 3 --por      VERIFICATION SUCCESSFUL   wrong
    --unwind 2 --rounds 3 --no-por   VERIFICATION FAILED       correct

## 2. Why it happened

`create_atomic_canonical` constrains every atomic block with

    fire_cond  =>  (ABR v ABW)

so a block may occupy a schedule slot only if one of its reads observes a
value from elsewhere (`ABR`) or one of its writes is itself observed (`ABW`).

Both witnesses are built **entirely from read-side quantities** -- `NRP`,
`WINR`, `LW`, `LOW`. A write that no read ever observes is invisible to them.

The reduction therefore keeps one representative per **read-from equivalence
class**. For reachability that is exactly right: two schedules differing only
in the order of two writes nobody reads compute the same thing, so pruning one
is free.

**A data race is not preserved by that equivalence.** A race is concurrency of
conflicting accesses, not flow of values, so two schedules inside one
read-from class can disagree about whether a race occurs -- and in the program
above they do. The block holding `datum = 5` has no read, and its write is
never observed, so neither witness can be satisfied and the block is never
placed where it races.

## 3. The dividing line is write/write, and it was measured

Four variants of the same race, `--unwind 2 --rounds 3`:

| the race is between                  | `--por`      | `--no-por` |         |
| ------------------------------------ | ------------ | ---------- | ------- |
| two **writes**, object never read     | `SUCCESSFUL` | `FAILED`   | **lost** |
| two **writes**, object read after join| `SUCCESSFUL` | `FAILED`   | **lost** |
| a write and a **read**                | `FAILED`     | `FAILED`   | kept    |
| two writes, but the block also reads  | `FAILED`     | `FAILED`   | kept    |

A read/write conflict leaves a read-from edge for the witnesses to find; a
write/write conflict leaves none. Two controls confirm the shape:
a write/write race with **no lock at all** is found either way (the constraint
applies only to atomic blocks), and a program whose two accesses take the
**same** lock -- no race -- stays `SUCCESSFUL` in every mode.

## 4. What it cost on the corpus

A full 3179-pair arm with `--no-por`, everything else identical:

|                | score         | missed bugs |
| -------------- | ------------- | ----------- |
| POR on         | 5215 / 5725   | 11          |
| POR off        | 5247 / 5725   | 10          |

**Exactly two verdicts change**, net +32:

    +33  no-data-race  semaphore-posix-race-2     SUCCESSFUL -> FAILED
     -1  unreach-call  elimination_backoff_stack  FAILED -> timeout

So the unsoundness costs **one benchmark** out of 3179 -- rare enough to
explain how it survived unnoticed -- while POR's speed saves one other task
from the 900 s timeout.

**The conclusion is not "turn POR off".** Fixing the defect keeps both the
+33 and the speedup.

## 5. The fix

`lazy_pot::block_can_race` exempts from canonicality any atomic block that
writes an object another thread also writes. **Under `--datarace` only**: the
constraint is untouched for reachability, where it is sound, so the reduction
`unreach-call` benefits from is unchanged by construction.

`LAZYPO_POR_RACE_EXEMPT` selects the rule, for the ablation:

| value          | exempts                               |
| -------------- | ------------------------------------- |
| `ww` (default) | write/write conflicts                 |
| `wide`         | any conflicting pair                  |
| `off`          | nothing -- the behaviour before the fix |

`ww` recovers **every** reproducer and `semaphore-posix-race-2`; `wide`
recovers nothing further. So the narrow rule is both the cheaper one and the
one the mechanism predicts.

Regression test: `regression/cbmc-concurrency/por_write_write_race`.

## 6. Why it took so long to find

`--por` is the **default** once `--rounds` is given:

```c
if(!cmdline.isset("no-por"))
  options.set_option("por", true);
```

Only `--no-por` disables it. Every earlier ablation that "ruled POR out"
merely *omitted* `--por` -- so both arms of every such comparison ran POR, and
all of them were void. The tell was that every pair of timings came out
identical.

## 7. Verifying the flags, not assuming them

Four assumptions underpin every number here, and two of them had already been
wrong once. Each is now checked directly (`flag_audit.sh`, `plumb.sh`):

| assumption | how it is checked | result |
| --- | --- | --- |
| `off` == pre-patch behaviour | build the pre-patch binary, compare the **formula size** on the same input | 144570 vars / 460514 clauses, identical |
| the exemption actually fires | same comparison, `ww` vs `off` | 142582 / 454493 -- differs |
| `--no-por` really disables POR | compare formula size, not verdict | 140171 vs 142582 vars -- differs |
| the env var reaches the solver *through the wrapper* | run the wrapper and watch a verdict flip | `off` SUCCESSFUL, `ww` FAILED |

The last one needs the right benchmark: `semaphore-posix-race` has **no row**
in `output_unwind_rounds.csv`, so the wrapper falls back to `--unwind 2`,
which is too weak to expose that race in any mode -- both arms agree and the
test proves nothing. `semaphore-posix-race-2` is the one whose verdict
`--no-por` actually flipped through this wrapper, so it is the one that can
detect a broken plumbing.

## 8. Harness mistakes that produced believable numbers

Recorded because each of them looked like a result:

* **Timing under load.** The first timing run was started while a 12-worker
  corpus arm was still on the machine, at load 13. Nothing measured there is
  comparable. `por_timing2.sh` now refuses to measure unless the load is at
  most 2 and no solver is running, and re-checks before **every** timing, not
  once at the start. (It was dismissed at the time as "faster than the
  baseline, so impossible". That reasoning was wrong -- see section 10, the
  exemption really is faster -- and the run was void for the load alone.)
* **A wait loop that could not end.** `pgrep -c` prints `0` *and* exits
  non-zero when nothing matches, so `$(pgrep -xc iekke_exe || echo 0)` yields
  two zeros and the numeric test dies with "integer expression expected" on
  every iteration.
* **A reaping pattern that matched nothing.** Orphans were selected with
  `pgrep -f "^$D/iekke_exe "`, but the wrapper runs `./iekke_exe` -- a
  relative path. Zero matches, and the orphans ran on into the next arm.
  Selection is now by `/proc/<pid>/cwd`.
* **Killing the worker is not killing the run.** The chain is
  `timeout -> deagle (python) -> sh -c -> iekke_exe`. Killing the worker and
  the solver orphans the python wrapper, which then starts its *next*
  invocation: twelve fresh solvers appeared the moment the drivers died.
  Select every process in the run tree by cwd, and loop until none is left.
* **A regression run that executed nothing and reported success.**
  `../test.pl` is not executable, so it died with `Permission denied`; the
  grep for the word "failed" found nothing and printed "0 failed" six times.
  A suite that never ran looked exactly like a suite that passed. The runner
  is now invoked through `perl`, per-test `[OK]`/`[FAILED]` markers are
  counted rather than a summary line trusted, and **zero tests executed is a
  hard failure**.

## 9. Reproducing

    # the defect and the dividing line
    bash abw_probe.sh

    # all reproducers x {off, ww, wide, --no-por}, plus the corpus benchmarks
    bash fix_check.sh

    # the four flag assumptions
    bash flag_audit.sh
    bash plumb.sh

    # cost in time -- refuses to run on a busy machine
    bash por_timing2.sh

    # both suites, pre-patch vs patched
    bash regress2.sh

## 10. What the fix costs in time: nothing, it gains

Serial, one benchmark at a time, on an otherwise idle machine, through the
wrapper, same binary in every arm:

| benchmark | `--no-por` | POR `off` | POR `ww` | ww/off |
| --- | ---: | ---: | ---: | ---: |
| reorder_c11_bad-50              | 42.3s | 48.9s | 40.9s | 0.84x |
| reorder_c11_good-50             | 41.4s | 39.8s | 38.2s | 0.96x |
| elimination_backoff_stack-race  | 54.5s | 24.4s | 20.7s | 0.85x |
| reorder_c11_bad-40              | 21.4s | 22.1s | 19.9s | 0.90x |
| thread-join-binomial-race-2     | 18.8s | 15.7s |  7.8s | 0.49x |
| semaphore-posix-race-2          |  0.2s |  0.2s |  0.2s | 0.94x |
| per-thread-array-join-counter-race-4 | 6.0s | 6.2s | 6.1s | 0.99x |
| elimination_backoff_stack       | 23.5s | 24.5s | 24.6s | 1.00x |

**The exemption is about 13% faster, not slower.** That is not a paradox: it
*removes* constraints. Every exempted block saves an `atomic_block_canonical`
implication and the `ABR`/`ABW` witnesses behind it -- six relational
comparisons per (block, round, variable) -- so the formula shrinks.

The pattern follows the mechanism exactly. The gains are all on benchmarks
answered `FAILED`: dropping canonicality both shrinks the formula and enlarges
the space in which a racing schedule can be found. The two `SUCCESSFUL`
benchmarks, where a larger space has to be proved race-free, come out at
0.99x and 1.00x -- a wash.

So the fix is free on the data-race category and, being gated on `datarace`,
costs exactly zero elsewhere.

## 11. Result

| arm (same binary, 1029 no-data-race pairs) | score | missed bugs | false alarms |
| --- | --- | --- | --- |
| exemption `off` | 1406 / 1823 | 10 | 4 |
| exemption `ww`  | 1439 / 1823 |  9 | 4 |

Net **+33**, from a single changed verdict
(`semaphore-posix-race-2`, `SUCCESSFUL -> FAILED`), with **no new false
alarms and no correct answer lost**.

The `datarace` gate was checked rather than assumed: 150 pairs across
`unreach-call`, `valid-memsafety` and `no-overflow`, run in both modes, gave
identical verdicts on every one.
