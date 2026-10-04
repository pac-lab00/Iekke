#! /usr/bin/python3
# Name-blind wrapper: same tool, same property flags, no decision that depends
# on which file it was handed.
#
# The deployed wrapper decides two things by benchmark *name*: it reads
# (unwind, rounds, symmetric_instance) out of output_unwind_rounds.csv keyed on
# the name, and it refuses to analyse twelve names at all via KNOWN_UNKNOWN.
# Neither is justifiable from the program, so a score measured with them is not
# one anyone can defend. This arm removes both and searches for the bound
# instead.
#
# ---------------------------------------------------------------------------
# Two corrections, both paid for in a wasted run. Do not undo either.
#
# 1. NEVER STOP ON A SUCCESSFUL. The first version treated "SUCCESSFUL with no
#    'Unwinding incomplete' line" as a real proof and returned it. That is
#    wrong: complete unwinding only says the *loops* were not cut. The *round*
#    bound is an under-approximation too, and the tool warns about it on every
#    single run -- "Context-bounded analysis may yield unsound verification
#    results". In a round-bounded tool no SUCCESSFUL is ever a proof, so the
#    only sound stopping condition is a counterexample or an exhausted budget.
#    That bug cost 11 missed bugs in the first 303 pairs, against zero for the
#    deployed configuration: fib_unsafe-6/10/12, triangular-longest-2 and
#    singleton all came back SUCCESSFUL in under a second, at (2,2), on
#    programs with real reachable violations.
#
# 2. ROUNDS HAVE TO CLIMB AS HIGH AS THE HAND TUNING DOES. The schedule topped
#    out at 6 rounds. The calibrated table uses 7 for fib_unsafe-6, 11 for
#    fib_unsafe-10, 13 for fib_unsafe-12 and 21 for triangular-longest-2. A
#    name-blind arm has to be able to reach the bounds the name-keyed one was
#    handed, or it is not a fair replacement -- it is just a worse tool.
# ---------------------------------------------------------------------------
#
# What is left is a plain search for violations under a time budget:
#
#   FAILED at any bound          -> report FAILED and stop. A counterexample
#                                   found under a bound is still real; the tool
#                                   says so itself.
#   SUCCESSFUL                   -> remember it and keep climbing.
#   timeout, refusal, crash      -> that bound failed, not the search. Move to
#                                   the next one.
#   budget gone                  -> report the remembered SUCCESSFUL, else
#                                   UNKNOWN.
#
# Reporting the remembered SUCCESSFUL at the end, rather than UNKNOWN, is
# deliberate and is NOT the vacuity rule that was measured and rejected
# earlier: that rule *suppressed* bounded safe answers and cost -0.98 per task,
# because 65% of correct SUCCESSFULs on expected-true tasks have incomplete
# unwinding. Here the bounded safe answer is still reported -- it is simply
# reported last, after the budget has been spent trying to refute it.
import os
import re
import subprocess
import sys
import time

BUDGET = float(os.environ.get("DEAGLE_BUDGET", "900"))
MIN_SLICE = 3.0
# No single bound may eat the whole budget. The schedule deliberately mixes two
# regimes -- deep unwind at few rounds, and deep rounds at modest unwind -- and
# one slow attempt in the first regime must not starve the second.
SLICE = BUDGET / 3.0

# Declared up front, identical for every program, ordered by rising cost.
# Two regimes have to be covered, because the benchmark set contains both:
# concurrency bugs that need many context switches at a modest unwind (the
# fib/triangular family, up to 21 rounds), and bugs behind long loops that need
# a huge unwind at very few rounds (the race_reach family, calibrated at
# unwind 10001).
#
# The deep-rounds entries come before the deep-unwind ones. Cost order put
# (256,3) and (1024,3) in the middle, and a bound that large can exhaust
# --object-bits and return no verdict at all; with the old "stop when the tool
# refuses" rule that aborted the search before (32,21) was ever tried. The
# rounds the hand tuning uses -- 7, 11, 13, 21 -- must all be reachable.
SCHEDULE = [
    (2, 2), (4, 3), (8, 3), (16, 4), (32, 4), (8, 7), (16, 9),
    (32, 13), (32, 21), (64, 4), (256, 3), (1024, 3), (4096, 3),
    (16384, 3),
]

if len(sys.argv) < 2 or sys.argv[1] in ("-v", "--version"):
    print("4.1.0")
    sys.exit(0)

if sys.argv[1] == "--witness":
    print("Deagle is not a validator!")
    sys.exit(0)

if len(sys.argv) < 3:
    print("Usage: ./deagle property_path program_path")
    sys.exit(0)

property_path = sys.argv[1]
program_path = sys.argv[2]

flags = "--allow-pointer-unsoundness --graphml-witness error-witness.graphml "
if "unreach-call.prp" in property_path:
    flags += ""
elif "no-data-race.prp" in property_path:
    flags += "--no-assertions --datarace "
elif "no-overflow.prp" in property_path:
    flags += "--no-assertions --signed-overflow-check --unsigned-overflow-check "
elif "valid-memsafety.prp" in property_path:
    flags += "--no-assertions --pointer-check --alloc-check --memory-leak-check"
else:
    print("Unknown property: %s" % property_path)
    sys.exit(0)


def verdict_of(text):
    """The verdict on the run's last line, or None if it produced none.

    Only the last line counts: the tool prints its own verdict vocabulary
    inside diagnostics, and a crashed or killed run that emitted a warning
    containing "VERIFICATION SUCCESSFUL" has been scored as a successful
    verification before now.
    """
    lines = [l for l in text.splitlines() if l.strip()]
    if not lines:
        return None
    last = lines[-1]
    if "VERIFICATION FAILED" in last:
        return "FAILED"
    if "VERIFICATION SUCCESSFUL" in last:
        return "SUCCESSFUL"
    return None


started = time.time()
bounded_safe = None

for unwind, rounds in SCHEDULE:
    left = BUDGET - (time.time() - started)
    if left <= MIN_SLICE:
        break

    slice_ = min(left, SLICE)
    cmd = ("./iekke_exe %s %s --unwind %d --rounds %d --por --verbosity 8 --glucose"
           % (program_path, flags, unwind, rounds))
    print("try unwind=%d rounds=%d (%.0fs for this bound, %.0fs left)"
          % (unwind, rounds, slice_, left))
    try:
        # Merged, not concatenated: the verdict is the last line of the run,
        # and stdout + stderr glued end to end puts every warning after it, so
        # the verdict stops being last and every run reads as "no verdict".
        proc = subprocess.run(cmd, shell=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT,
                              text=True, errors="replace", timeout=slice_)
        out = proc.stdout
    except subprocess.TimeoutExpired:
        # Out of reach at this bound -- but not necessarily at the next one,
        # which may be cheaper on the axis that matters for this program. Keep
        # going; the budget check at the top of the loop ends the search.
        print("  -> timeout")
        continue

    verdict = verdict_of(out)
    print("  -> %s" % verdict)

    if verdict == "FAILED":
        print(out)
        print("FAILED")
        sys.exit(0)
    if verdict == "SUCCESSFUL":
        bounded_safe = out
    # No verdict means a refusal or a crash at *this* bound -- most often
    # --object-bits exhaustion, which only the very large unwinds provoke. It
    # says nothing about a bound that is smaller on that axis and deeper on
    # rounds, so it must not end the search.

if bounded_safe is not None:
    print(bounded_safe)
    print("SUCCESSFUL")
    sys.exit(0)

print("UNKNOWN")
sys.exit(1)
