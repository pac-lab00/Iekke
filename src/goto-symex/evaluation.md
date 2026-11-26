# Scoring the corpus, and why the deployed configuration is not the number we publish

This document exists because a score is only worth what its configuration is
worth. Read it before quoting any number from a run.

## 1. The problem: two decisions taken by file name

The competition wrapper (`benchexec/lazypo-mono-cur/deagle`) decides two things
by looking at the **name of the input file**:

1. `output_unwind_rounds.csv` maps `(property, benchmark name)` to
   `(unwind, rounds, symmetric_instance)` -- 1127 hand-calibrated rows. A name
   that is absent falls back to `--unwind 2` with `--rounds 3` (data-race) or
   `1` (everything else).
2. `KNOWN_UNKNOWN` is a hard-coded set of twelve benchmark names. For those the
   wrapper prints `UNKNOWN` and exits **without analysing the program at all**.

The wrapper never escalates: one attempt at the table's bounds, then done.

Neither decision can be derived from the program. Both are keyed on its
identity, and a reviewer is entitled to read that as configuring the tool
against the benchmark set rather than solving the problem. So we measure two
arms and are explicit about which is which.

**The tool itself is clean.** Grepping `src/**/*.{cpp,h}` for benchmark names
returns eleven hits: ten are comments recording where a measurement came from
(`twalock`, `safestack`, `elimination_backoff_stack`), and the eleventh,
`symex_bmc.h:116 void svcomp_unsupported_library();`, is declared and never
defined or called. Every decision the binary makes comes from the program.

## 2. Scope: use SV-COMP's own category definition

`sv-benchmarks/c/Concurrency.set` -- nineteen directory globs, **1063
benchmarks, 3179 task-property pairs**, all ILP32. Ceiling if everything were
answered correctly: **5725 points**.

Do not invent the scope. Defining it as "benchmarks carrying `no-data-race`"
sounds equivalent and is not: it drops 31 pairs, **every one of them expected
false**, among them `list1` and `bounded_mpmc_check_empty` -- the two
benchmarks with the longest history of wrong answers here, invisible to the
very measurement meant to rank wrong answers.

Enumerate with a YAML parser, never with grep. SV-COMP ymls routinely carry
commented-out properties:

    properties:
    #  - property_file: ../properties/unreach-call.prp
    #    expected_verdict: false
      - property_file: ../properties/no-data-race.prp
        expected_verdict: false

`grep -A2` reads those as live. Doing so inflated the corpus and got the
expected verdict *backwards* on dozens of tasks.

## 3. Scoring

    correct true +2    correct false +1
    wrong true  -32    wrong false  -16     unknown 0

A false alarm costs sixteen times what a correct answer earns, so rank by
**points lost**, not by tasks failed, and rank **per benchmark**: one benchmark
carries up to four properties, so a systematic false alarm on it is -64, not
-16. That is precisely how four libvsync benchmarks stayed outside the measured
set while costing four times what anyone thought.

## 4. Arm A -- the deployed configuration

A reference number only. It says what the name-keyed tuning is worth; it is not
the number for the paper.

    3148 pairs   3091 correct   0 missed bugs   5 false alarms   52 unknown
    SCORE 5526 / 5694        97.0% of available points

All 80 lost points are false alarms; the tool never called a buggy program
safe.

    -16  no-data-race     bounded_mpmc_check_full    expected true, got FAILED
    -16  no-data-race     cnalock                    expected true, got FAILED
    -16  no-data-race     mcslock                    expected true, got FAILED
    -16  no-data-race     rec_mcslock                expected true, got FAILED
    -16  valid-memsafety  bounded_buffer             expected true, got FAILED

## 5. Arm B -- name-blind

Same binary, same per-property flags (the property is an argument the tool is
handed, so keying on it is legitimate). No CSV, no decline list, no
`--symmetric-instance`. What replaces the table is **iterative deepening**,
justified by the program and the time budget alone:

| run result | what it means | what we do |
|---|---|---|
| `VERIFICATION FAILED` | a counterexample, real at any bound | report FAILED, stop |
| `SUCCESSFUL`, unwinding complete | a real proof | report SUCCESSFUL, stop |
| `SUCCESSFUL`, `Unwinding incomplete` | **not a proof** | remember it, raise the bound |
| budget gone, or the tool refuses | nothing better is reachable | report the remembered bounded SUCCESSFUL, else UNKNOWN |

The third row is the one that matters, and the tool already tells us which case
it is in:

    Unwinding incomplete: N loop/recursion bound(s) hit; a counterexample is
    still real, but a safe result here is not a proof

Remembering the bounded SUCCESSFUL rather than discarding it is deliberate: a
bounded safe answer is what the deployed configuration reports anyway, so arm B
never gives up a point it would otherwise score, and spends the leftover budget
trying to turn a missed bug into a found one.

Schedule, fixed in advance and identical for every program:

    (2,2) (4,2) (8,3) (16,3) (32,4) (64,4) (128,5) (256,5) (1024,5) (4096,6) (16384,6)

Unwind climbs geometrically because the cost of too small a bound is a missed
bug; rounds climbs slowly because the formula grows linearly in it.

### It already recovers a hand-tuned answer

`bounded_mpmc_check_empty` is the benchmark the CSV was edited for: -32 at
`unwind 2`, correct at `4`, and someone wrote the `4` next to its name. Told
nothing about the file:

    try unwind=2 rounds=2  -> SUCCESSFUL (unwinding incomplete)   not a proof
    try unwind=4 rounds=2  -> FAILED                              correct

### What it costs

Measured, not guessed: arm A answered 3148 pairs in 55 minutes, arm B needs
about 15 hours for the same set -- roughly 170 s per task, because most
expected-true programs have a loop that is never fully unwound, so they climb
the whole schedule before reporting the bounded proof they already had.

### What to watch for

Escalation is not free in the safe direction. The false-alarm rate grows with
the bound -- 1 in 755 at `u2 r1` against 15 in ~700 at `u6 r3` -- and a false
alarm costs 16 times what the extra bug earns. Which arm wins is an empirical
question.

## 6. Running it

* `~/enumerate2.py` -> `~/corpus_official.tsv`, from `Concurrency.set`.
* `~/par_run.sh` -- parallel scorer; `LIST/BASE/OUT/TO/W/WRAPPER` from the
  environment. **One directory per worker is not optional**: the wrapper writes
  fixed temp filenames, so two runs sharing a directory read each other's
  output and report each other's verdicts. Three rows of an earlier evaluation
  were `ERROR` purely from that.
* `~/rank_losses.py A.tsv [B.tsv]` -- the ranking, and with two files the
  per-task deltas.

Parallelism is defensible for a *verdict* run even though it is not for a
timing run: contention can only turn an answer into a timeout, worth 0, never
into a wrong answer. The measured score is therefore conservative and every
verdict emitted is trustworthy.

Always measure through the wrapper, never by rebuilding its command line --
see `lazy_po.md` and the session notes; hand-rolled invocations have produced
wrong conclusions twice, once by reading a stale bounds table and once by
dropping `--symmetric-instance`.
