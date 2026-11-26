# Changes, and why each one was made

A running record of what was changed in the tool and in how it is evaluated,
written so the reasoning survives without the conversation that produced it.
Newest first.

---

## 1. `pthread_create`/`pthread_join` collapse no longer swallows `pthread_exit`

**File:** `src/goto-programs/goto_convert_functions.cpp`
**Test:** `regression/cbmc-concurrency/pthread_exit_create_join_collapse`

### What was wrong

The fork rewrites

```c
pthread_create(&t, 0, f, arg);
pthread_join(t, 0);
```

into a plain call `f(arg)`. That is sound for the schedule -- nothing can
interleave between a create and its immediate join -- and it is a real
speed-up, so the optimisation is worth keeping.

It is not sound when `f` ends in `pthread_exit`. That function's model ends in
`__CPROVER_assume(0)`, which means *"this thread stops here"*. Whether it means
that depends on how many threads symex is holding:

```cpp
// symex_main.cpp, symex_assume_l2
if(state.threads.size()==1)
  target.assumption(state.guard.as_expr(), tmp, state.source);  // GLOBAL
else
  state.guard.add(rewritten_cond);                              // thread-local
```

Once the body runs as an ordinary call there is only one thread, the first
branch is taken, and *"this thread stops"* becomes *"this execution is
infeasible"*.

### Why it mattered more than a wrong answer

The cost is not a missed counterexample. Everything after the collapsed call
is dropped **before it reaches the equation**, so the properties are never
checked at all:

    list1.i, before the fix:  ASSUME(FALSE) = 1,  ASSERT steps = 0
    list1.i, after the fix:   ASSUME(FALSE) = 0,  ASSERT steps = 9

A program reported SUCCESSFUL having verified nothing. The memory-leak
assertion is the most exposed check of all, because it always sits at the end
of `__CPROVER__start`, i.e. always after the threads.

Minimal reproducer (`~/leak-probe/real1.c` on iekke-lab):

```c
int x = 0;
void *worker(void *arg) { x = 1; pthread_exit(0); }
int main(void) {
  pthread_t t;
  pthread_create(&t, 0, worker, 0);
  pthread_join(t, 0);
  assert(x == 0);            /* violated, and never even emitted */
}
```

    before:  VERIFICATION SUCCESSFUL
    after:   VERIFICATION FAILED
    stock cbmc 5.95.1: VERIFICATION FAILED   (so this was ours, not upstream)

### The fix

Refuse the rewrite when the thread body can reach `pthread_exit`, directly or
through a callee -- a transitive walk of the call graph from the thread
function, with a visited set. A thread that ends with `return` is still
collapsed, which is the case the optimisation was written for. An unresolvable
target (a function pointer) is left alone as well: skipping the optimisation
only costs time.

Also removed a stray `std::cout` from the same function. The competition
wrapper parses this process's stdout; a verifier must not print chatter there.

### Effect

    list1.i   u=2 r=1,2   SUCCESSFUL   (bound too small to reach the leak)
    list1.i   u=2 r=3,4   FAILED       correct -- the leak in build()

Worth **+33** (-32 to +1), but only at three rounds or more. The deployed
bounds table gives `list1` one round, so the name-keyed configuration still
gets it wrong; the name-blind arm, which escalates, reaches it. That was not
planned and is a point in the blind arm's favour.

---

## 2. Evaluation: name-blind arm, corpus scope, scoring

**Files:** `src/goto-symex/evaluation.md`, `deagle_blind.py`,
`corpus_enumerate.py`, `corpus_rank_losses.py`, `corpus_run.sh`

See `evaluation.md` for the full account. In brief:

* The competition wrapper decides bounds and refusals **by input file name**
  (a 1127-row table and a twelve-name decline list). Neither is derivable from
  the program, so the deployed score is a reference number, not a publishable
  one. The tool source itself is clean -- audited.
* The name-blind replacement searches for the bound instead: iterative
  deepening, stopping only on a counterexample or an exhausted budget. **No
  SUCCESSFUL is ever treated as a proof**, because the round bound is an
  under-approximation and the tool says so on every run.
* Scope is SV-COMP's own `Concurrency.set`: 1060 benchmarks, 3179
  task-property pairs, ceiling 5725 points. Enumerate with a YAML parser --
  `grep` reads commented-out properties as live ones.

---

## 3. Harness: the competition's resource limits, and reaping

**File:** `corpus_run.sh` (`par_run.sh`)

* **A 15 GB per-run memory cap**, which SV-COMP imposes and the harness did
  not. Without it three solvers passed 15 GB, two reaching 27 GB, sixteen at
  once on a 117 GB machine: it swapped, every process including `sshd` entered
  uninterruptible sleep, and the host refused logins for eight hours. Re-running
  under the cap was worth **+10 points**, all of it tasks previously recorded
  as `ERROR` that were simply dying in the thrash.
* **Orphan reaping after every task.** `timeout` kills the wrapper, never the
  solver the wrapper started, so each timed-out task left an `iekke_exe`
  running for good -- 53 had accumulated, each holding a core, causing more
  timeouts and so more orphans.
* **One directory per worker**, because the wrapper writes fixed temp
  filenames and two runs sharing a directory report each other's verdicts.

---

## Settled questions, so they are not reopened

**`--malloc-may-fail --malloc-fail-null` is wrong, by the rules.** SV-COMP
2025 and 2026 both state: *"We assume that the functions malloc and alloca
always return a valid pointer, i.e., the memory allocation never fails"*.
Enabling it turns `singleton` -- unchecked `v = malloc(...)` then `v[0] = 'X'`,
expected **true** -- into a false alarm. Note `--malloc-may-fail` alone is
inert; a check that passes only that flag wrongly concludes the fix does
nothing.

**`list1.i`'s yml subproperty is mislabelled.** Under those rules the program
has no reachable invalid dereference: `main` passes its NULL `list` by value,
so `delete` dereferences nothing. The violation that exists is the leak in
`build`, i.e. `valid-memtrack`, not `valid-deref`. The expected verdict
*false* is right; the subproperty is not.
