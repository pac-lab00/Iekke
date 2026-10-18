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
import signal
import subprocess
import sys
import time

# Line by line, not in blocks. Under BenchExec stdout is a file, and a run
# killed from outside loses whatever was still in the buffer -- every
# "try ..." line included, so the log cannot say which bound it died in.
sys.stdout.reconfigure(line_buffering=True)

# Below the 900 s CPU limit on purpose. The budget is measured in wall time,
# and a bounded SUCCESSFUL is only reported once it is spent, so a budget of
# 900 reports it at about 900 s of CPU -- which SV-COMP scores as a timeout.
BUDGET = float(os.environ.get("DEAGLE_BUDGET", "870"))
MIN_SLICE = 3.0
# No single bound may eat the whole budget. The schedule deliberately mixes two
# regimes -- deep unwind at few rounds, and deep rounds at modest unwind -- and
# one slow attempt in the first regime must not starve the second.
SLICE = BUDGET / 3.0
# How often a running bound's memory is checked, in seconds.
POLL = 0.25

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

# Tried before the schedule: the program with its symmetric array families
# instantiated at two slots (--symmetric-instance, which recognises them from
# the program, not from its name, and refuses when it finds none). A setup
# loop over 256 slots is then two iterations long and runs to completion at a
# small unwind, where unreduced it is cut and every bound below 256 answers
# vacuously. The reduced program is an under-approximation, so only its
# FAILED is believed; a SUCCESSFUL from it is not a bounded answer for the
# original and is never reported.
REDUCED = (4, 2, "--symmetric-instance 2")
REDUCED_SLICE = 30.0

if len(sys.argv) < 2 or sys.argv[1] in ("-v", "--version"):
    print("4.1.0")
    sys.exit(0)

if sys.argv[1] == "--witness":
    print("Deagle is not a validator!")
    sys.exit(0)

if len(sys.argv) < 3:
    print("Usage: ./deagle property_path program_path [--32|--64]")
    sys.exit(0)

property_path = sys.argv[1]
program_path = sys.argv[2]

# The data model comes from the task's yml, and BenchExec passes it as the
# third argument. Dropping it runs every task in the tool's default model,
# which Deagle fixes at ILP32 (config.cpp, "default --32") -- so an LP64 task
# is analysed with 4-byte longs and pointers, which changes overflows, offsets
# and sizes in the program.
data_model = sys.argv[3] if len(sys.argv) > 3 else ""
if data_model not in ("", "--32", "--64"):
    print("Unknown data model: %s" % data_model)
    sys.exit(0)

flags = "--allow-pointer-unsoundness --graphml-witness error-witness.graphml "
flags += data_model + " "
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


def generated_vccs(text):
    """The number of verification conditions the run generated, or None."""
    m = re.findall(r"Generated (\d+) VCC\(s\)", text)
    return int(m[-1]) if m else None


def kill_bound(proc):
    """Kill everything one bound started: the shell, the tool, its solver.

    Killing only the shell -- what subprocess.run does on a timeout -- leaves
    the tool and the external glucose it spawned running. They then overlap
    the next bound and outlive the wrapper, spending CPU that SV-COMP charges
    to this run (seen at 1.85x wall time). Each bound therefore gets its own
    process group, and the group is what is killed.
    """
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass


current = None


def on_signal(signum, frame):
    # The bound's group is no longer ours, so a signal that ends the wrapper
    # would not reach it. Pass it on before going.
    if current is not None:
        kill_bound(current)
    sys.exit(128 + signum)


for s in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
    signal.signal(s, on_signal)


def memory_limit():
    """The memory this run may use, in bytes.

    DEAGLE_MEMLIMIT if set, else the tightest cgroup limit on the way up from
    this process's cgroup (where BenchExec puts its limit, often on a parent),
    else the machine's RAM. Both cgroup versions occur: the cluster nodes keep
    memory on v1, iekke-lab is v2.
    """
    if os.environ.get("DEAGLE_MEMLIMIT"):
        return int(os.environ["DEAGLE_MEMLIMIT"])
    limits = []
    try:
        with open("/proc/self/cgroup") as f:
            entries = [l.rstrip("\n").split(":", 2) for l in f]
    except OSError:
        entries = []
    for _, controllers, path in entries:
        if controllers == "":
            root, name = "/sys/fs/cgroup", "memory.max"
        elif "memory" in controllers.split(","):
            root, name = "/sys/fs/cgroup/memory", "memory.limit_in_bytes"
        else:
            continue
        while True:
            try:
                with open("%s%s/%s" % (root, path.rstrip("/"), name)) as f:
                    v = f.read().strip()
                # v2 writes "max" for no limit, v1 a number near 2**63.
                if v != "max" and int(v) < 1 << 60:
                    limits.append(int(v))
            except (OSError, ValueError):
                pass
            if path in ("/", ""):
                break
            path = os.path.dirname(path.rstrip("/")) or "/"
    if limits:
        return min(limits)
    try:
        return os.sysconf("SC_PAGE_SIZE") * os.sysconf("SC_PHYS_PAGES")
    except (ValueError, OSError):
        return None


def group_rss(pgid):
    """Resident memory of every process in group pgid, in bytes."""
    total = 0
    page = os.sysconf("SC_PAGE_SIZE")
    try:
        pids = os.listdir("/proc")
    except OSError:          # no /proc: memory cannot be watched
        return 0
    for pid in pids:
        if not pid.isdigit():
            continue
        try:
            with open("/proc/%s/stat" % pid) as f:
                fields = f.read().rsplit(")", 1)[1].split()
            if int(fields[2]) != pgid:
                continue
            with open("/proc/%s/statm" % pid) as f:
                total += int(f.read().split()[1]) * page
        except (OSError, IndexError, ValueError):
            pass
    return total


# One bound that outgrows the run's memory gets the whole run killed from
# outside, and with it every answer the earlier bounds found: a remembered
# SUCCESSFUL is lost, and the run scores as a memory-out. On the 40-node
# cluster that was 150 of the first 190 unknowns. So each bound is held below
# the run's limit, with room left for the wrapper and for growth between two
# checks, and a bound that crosses it fails alone, as a timed-out one does.
limit = memory_limit()
CAP = limit - max(256 << 20, limit // 10) if limit else None
print("memory cap per bound: %s"
      % ("%.0f MB" % (CAP / 2**20) if CAP else "none (limit unknown)"))

started = time.time()
bounded_safe = None

for unwind, rounds, extra in [REDUCED] + [(u, r, "") for u, r in SCHEDULE]:
    left = BUDGET - (time.time() - started)
    if left <= MIN_SLICE:
        break

    slice_ = min(left, REDUCED_SLICE if extra else SLICE)
    cmd = ("./iekke_exe %s %s --unwind %d --rounds %d --por --verbosity 8 --glucose %s"
           % (program_path, flags, unwind, rounds, extra))
    print("try unwind=%d rounds=%d %s(%.0fs for this bound, %.0fs left)"
          % (unwind, rounds, extra + " " if extra else "", slice_, left))
    # Merged, not concatenated: the verdict is the last line of the run,
    # and stdout + stderr glued end to end puts every warning after it, so
    # the verdict stops being last and every run reads as "no verdict".
    current = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, text=True,
                               errors="replace", start_new_session=True)
    deadline = time.time() + slice_
    out = None
    stop = None
    while out is None:
        try:
            # A timed-out communicate() keeps what it has read so far.
            out, _ = current.communicate(
                timeout=max(0.01, min(POLL, deadline - time.time())))
        except subprocess.TimeoutExpired:
            if time.time() >= deadline:
                stop = "timeout"
            elif CAP and group_rss(current.pid) > CAP:
                stop = "memory"
            if stop:
                # Out of reach at this bound -- but not necessarily at the
                # next one, which may be cheaper on the axis that matters for
                # this program. Keep going; the budget check at the top of the
                # loop ends the search.
                kill_bound(current)
                current.communicate()
                break
    current = None
    if stop:
        print("  -> %s" % stop)
        continue

    verdict = verdict_of(out)
    print("  -> %s" % verdict)

    if verdict == "FAILED":
        print(out)
        print("FAILED")
        sys.exit(0)
    # For unreach-call a SUCCESSFUL from a bound that generated no verification
    # condition and cut a loop reached no reach_error() call at all: every path
    # to one was cut by the unwinding, typically a setup loop longer than the
    # bound. It says nothing about the program, so it is not kept as a bounded
    # answer. Without a cut loop, no VCC means symbolic execution discharged
    # every assertion itself, which is a real bounded answer and is kept.
    # Measured on ciuccio on the 27 unreach-call tasks whose answer was such a
    # SUCCESSFUL: 3 wrong trues become unknown (+96), 10 right answers become
    # unknown (-20), the other 14 are unchanged. For the other properties no
    # VCC is not a sign of vacuity -- data races are not VCCs at all -- and on
    # the 14 October arm every such answer was right (memsafety 53, overflow
    # 5), so the rule would only lose answers there.
    vacuous = ("unreach-call.prp" in property_path
               and generated_vccs(out) == 0 and "Not unwinding" in out)
    if vacuous:
        print("  (no verification condition generated, a loop cut: not kept)")
    if verdict == "SUCCESSFUL" and not extra and not vacuous:
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
