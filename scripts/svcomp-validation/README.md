# SV-COMP concurrency validation harness

Scripts for auditing the tool against the SV-COMP concurrency benchmarks and
for calibrating the per-benchmark `--unwind` / `--rounds` bounds the `deagle`
wrapper reads from `output_unwind_rounds.csv`.

The scope is the directories named by `sv-benchmarks/c/Concurrency.set`, which
is what all four benchexec rundefinitions draw from: 1063 `.yml` tasks, giving
1029 `no-data-race`, 725 `unreach-call`, 752 `valid-memsafety` and 673
`no-overflow` tasks.

## Usage

    # build the per-property task lists from Concurrency.set
    python3 build_concurrency_lists.py

    # validate one task the way the wrapper would
    python3 prop_validate.py <property> path/to/task.yml

    # find the cheapest bound that answers correctly
    python3 sweep_timeouts.py <property> path/to/task.yml

    # deploy a calibrated bound into every wrapper's CSV
    python3 upsert_prop.py <property> <benchmark> <unwind> <rounds> \
        ../../benchexec/*/output_unwind_rounds.csv

`prop_validate.py` mirrors the wrapper: the same per-property flags, the same
CSV lookup, and the same `--unwind 2` fallback (`--rounds 3` for data races,
`--rounds 1` otherwise) when a benchmark has no calibrated row.

## Four ways to get the numbers wrong

Every one of these produced a wrong conclusion before it was caught, so they
are worth stating plainly.

**Run the input the `.yml` names, from the benchmark's own directory.** The
tasks specify `input_files:`, which for 855 of the 1030 no-data-race tasks is a
preprocessed `.i`, not the `.c`. The two need *different* bounds --
`reorder_c11_bad-10` exposes its race at `--unwind 10` on the `.c` and needs
13 on the `.i`. Copying sources into a flat scratch directory additionally
breaks relative includes such as `pthread-driver-races/model/svcomp.h`.

**Sweep both bounds, cost-ordered.** A one-dimensional search that escalates
`--unwind` with `--rounds` pinned walks straight past the cheap corner of the
grid. It has produced badly wrong calibrations twice: benchmarks needing
`rounds 4` at `unwind 3`, and four `28-race_reach_8*` tasks carrying
`unwind=10001` -- a full unroll of a 10000-iteration `pthread_create` loop --
that actually answer at `2/1`. Thread-management loops are recognised and
truncated anyway, so a huge unwind buys nothing but a huge formula.

**Time a benchmark singly, at the real limit.** Running many benchmarks
concurrently under a short cap manufactures timeouts: two tasks written off
that way answer correctly in 247s and 569s against the competition's 900s.

**Trust only the wrapper for timings.** These scripts invoke the binary
directly, which is fine for verdicts but not for time: the wrapper adds witness
generation, and `lazydeagle-ciuccio` formerly handed every query to an external
glucose. `elimination_backoff_stack` measured 287s here and 816s through that
wrapper, against a 900s limit. Verdicts carried over; margins did not.

## A vacuous "no bug" is not a proof

Too small an `--unwind` does not merely lose coverage, it can make the program
vacuous. In the `pthread-driver-races/char_pc8736x_gpio_*` tasks the byte-init
loop in `external_alloc` runs `sizeof(struct platform_device)` times; below
roughly `--unwind 100` it is truncated and everything after it, `pthread_create`
included, is assumed away -- yet the answer is still VERIFICATION SUCCESSFUL.
Such a run never builds the datarace constraint and never calls the solver, so
its output carries no `Datarace Enabled` line and no `N variables, M clauses`.

## Configuration

Paths default to the development checkout and can be overridden:

| variable | used by | meaning |
|---|---|---|
| `IEKKE_BIN` | `prop_validate.py`, `sweep_timeouts.py` | the binary to run |
| `IEKKE_CSV` | `prop_validate.py` | the calibration CSV to read bounds from |
| `SVBENCH_ROOT` | `build_concurrency_lists.py` | `sv-benchmarks/c` |
| `TASKLIST_DIR` | `build_concurrency_lists.py` | where to write `tasks_<property>.txt` |
