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
import datetime
import hashlib
import os
import re
import signal
import shutil
import subprocess
import tempfile
import sys
import time
import uuid

# Line by line, not in blocks. Under BenchExec stdout is a file, and a run
# killed from outside loses whatever was still in the buffer -- every
# "try ..." line included, so the log cannot say which bound it died in.
sys.stdout.reconfigure(line_buffering=True)

# Below the 900 s CPU limit on purpose. The budget is measured in wall time,
# and a bounded SUCCESSFUL is only reported once it is spent, so a budget of
# 900 reports it at about 900 s of CPU -- which SV-COMP scores as a timeout.
BUDGET = float(os.environ.get("DEAGLE_BUDGET", "870"))
# Once a bounded SUCCESSFUL is held, the search stops at STOP_AFTER seconds:
# no further bound is started, and a running one is cut. Measured on the
# 21 October cluster run (3176 tasks, the bound trails replayed, the replay
# agreeing with the run on every task): with the stop at 360 s or later no
# answer changes, at 340 s the bug in triangular-longest-2 (found by the
# 21-round bound at about 350 s on the ARM nodes) is lost. 400 s keeps a
# margin and cuts a third of the CPU time, nearly all of it spent on safe
# tasks that the old rule kept refuting until the budget was gone.
STOP_AFTER = float(os.environ.get("DEAGLE_STOP", "400"))
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
#
# (8,4) was added after the Huawei challenge tasks: the race in twalock needs
# 4 rounds and is found at unwind 8 in 7 s, while (16,4) takes 298 s. A (4,2)
# added at the same time was taken out again: on 128 tasks rerun with and
# without it, it changed one answer, safestack_relacy (unreach-call), from
# no answer to a wrong TRUE -- a quick bounded SUCCESSFUL, its bug needing
# (3,4) in over 300 s -- and hclhlock, which it had been added for, is answered
# at (4,3) in time once --thread-symmetry is off.
#
# (3,4) comes right after the first bound: safestack_relacy_racy has a race
# that needs 4 rounds and is found at (3,4) in 213 s on x86; behind (4,3), which
# answers safe at that point, the stop rule ended the search first and the task
# was answered with a wrong TRUE (-32). At (2,4) the program gives no verdict.
SCHEDULE = [
    (2, 2), (3, 4), (4, 3), (8, 3), (8, 4), (16, 4), (32, 4), (8, 7), (16, 9),
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

# Tried next: every loop at the limit the tool suggests for it
# (--unwind-suggest, Deagle's analysis of the loop's text: counter, bound,
# step, assumed upper bounds), the others at UNSUGGESTED. One bound for all
# loops unrolls short loops as far as the longest needs, and symex cannot
# always see where they exit: on reorder_c11_good-20 Deagle's per-loop limits
# give 4.9M clauses where --unwind 32 gives 36.8M. The suggestion is a
# heuristic -- a body that also changes the counter makes it too small -- so a
# SUCCESSFUL from this step is a bounded answer, like one from any bound of
# the schedule, and is kept as one. It is often the only bound that runs a
# long setup loop to completion: every bound of the schedule cuts it and
# answers nothing, as on the goblint list programs (09-regions_21: safe at
# this step in 19 s on x86, then UNKNOWN after 871 s). Replayed over the 3346
# logs of two cluster runs: no task found FAILED after the stop rule's mark
# with this step safe or timed out, so holding its answer cuts no bug.
UNSUGGESTED = 3
SUGGEST_ROUNDS = 3
# Bounds with at least this many rounds run with --por, the others without:
# 7 is the smallest round count in the ladder at which bugs that need many
# rounds appear (see the deep-rounds rungs above), and that is where partial-
# order reduction pays; at fewer rounds it only adds constraints. One setting
# per bound: SV-COMP limits CPU time over all cores, so running both settings
# in parallel spends the budget twice as fast.
POR_MIN_ROUNDS = 7
SUGGEST_CAP = 1024
SUGGEST_SLICE = 60.0
SUGGEST_TIMEOUT = 30.0

# An array allocated with a non-constant number of elements n gets a constant
# number K, under the condition n <= K (--dynamic-array-bound): field
# sensitivity then splits it into scalars, where an array of symbolic size goes
# to the array theory whole -- 34x fewer clauses on the per-thread-array
# family. It cuts the executions that ask for more than K, as the unwinding
# bound cuts loops, so K climbs with the unwind: a loop over the array is cut
# there anyway. Field sensitivity splits arrays of up to 64 elements. Not for
# memory safety: the array has K elements, so an access between n and K would
# not be out of bounds.
def array_bound(unwind):
    return min(max(unwind, 4), 64)


# Arrays read byte-wise (through a pointer to an element's member, by memcpy)
# are answered byte by byte from the writes in schedule order
# (--array-rf-bytes) instead of carrying the whole array on every access: on
# twalock (__twa_array[4096] at a computed index) 41M variables become 64k.
# On by default only together with (8,4) above: alone it made the small
# bounds of twalock fast and safe, and the stop rule then reported a wrong TRUE.
ARRAY_RF_BYTES = "--array-rf-bytes "

# Two encoding options that change only how the program is written into the
# formula. --summarise-guards: after a call, the path condition is "condition
# at the call AND one fresh symbol" instead of the whole exit condition, so it
# stops growing with the call depth (cafe_ccic: 85000 nodes -> about 300).
# --infer-alloc-types: a block allocated with a constant size and cast at once
# is typed by the cast, so pointer analysis keeps one entry per member.
# Full corpus on the cluster (2026-10-29): no answer changed apart from tasks
# near the time limit (+2 correct, -1).
# --merge-exclusive-threads: thread creations on paths that exclude each other
# share one thread. On 55 driver tasks (2026-10-30) no answer changed; it fires
# on the large ldv drivers only (nsc-ircc: 23.4M -> 17.0M clauses, 8.1 -> 5.9 GB).
# --index-chain is NOT passed. It gives 10-46% fewer clauses from 3 rounds up
# with the same verdicts at u2, but the solver can be far slower on it:
# triangular-longer-2 at (32,13) took 168 s instead of 3.7 s with 38% fewer
# clauses, so on the cluster (2026-10-31) the bugs of fib_unsafe-10/11,
# triangular-longer-2/longest-2 and unwind3-100 were no longer found in the
# slice and the stop rule reported five wrong TRUEs.
# --own-view-reads: a shared read of an object no other thread writes after
# the first spawn is read from the thread own view, so constants propagate
# through it. Timed 2026-11-01 (Release build, one run at a time): never slower
# on 58 runs, same verdicts; adutux 297 -> 100 s, nsc-ircc 140 -> 106 s,
# array-eq-symm 18.2 -> 0.7 s, unwind3-100 19.8 -> 8.6 s.
ENCODING_FLAGS = ("--summarise-guards --infer-alloc-types --merge-exclusive-threads "
                  "--own-view-reads ")

# --thread-symmetry is NOT passed. It was, from 2026-10-21, without a corpus
# measurement; on unwind3-100 at (256,3) it made the solver 8x slower (42 s ->
# 344 s, past the 290 s slice), so the bug was no longer found and the stop
# rule reported a wrong TRUE. On 176 tasks measured earlier it changed no
# verdict.

# The version alone: BenchExec shows it next to the name of the tool.
if len(sys.argv) < 2 or sys.argv[1] in ("-v", "--version"):
    print("2.0")
    sys.exit(0)

if sys.argv[1] == "--witness":
    print("Iekke is not a validator!")
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
# SV-COMP conventions since 2026: malloc, calloc and realloc may return NULL
# (sv-benchmarks c/CONVENTIONS.md); CBMC assumes they succeed unless told
# otherwise. pthread/bigshot_s2 (valid-memsafety, relabelled false) needs it.
flags += "--malloc-may-fail --malloc-fail-null "
if "unreach-call.prp" in property_path:
    flags += ""
elif "no-data-race.prp" in property_path:
    flags += "--no-assertions --datarace "
elif "no-overflow.prp" in property_path:
    flags += "--no-assertions --signed-overflow-check --unsigned-overflow-check "
    # the values read from __VERIFIER_nondet_* in the violation witness: one
    # more confirmed overflow witness (ConcurrentWitness2Test), none lost;
    # for unreach-call UAutomizer rejected 5 it confirmed without them
    flags += "--yaml-witness-values "
elif "valid-memsafety.prp" in property_path:
    flags += "--no-assertions --pointer-check --bounds-check --alloc-check --memory-leak-check"
else:
    print("Unknown property: %s" % property_path)
    sys.exit(0)


# Witnesses in the YAML format of sv-witnesses: since 2027 a TRUE or FALSE
# answer for unreach-call and no-overflow without one scores nothing ("witness
# missing"), and the validators look for witness.yml in the working
# directory. A TRUE gets a correctness witness without invariants, which the
# validators confirmed for Theta in 2027 (pthread/bigshot_s and 157 more); a
# FALSE gets the violation sequence the tool writes from its counterexample
# (--yaml-witness: thread creations and the violation), wrapped here in the
# metadata only the wrapper knows. Memory safety scored without witnesses, so
# none is written there: an unconfirmed one could only lose the points.
# No-data-race in 2027 scored a TRUE without a witness (Iekke: 688 correct at
# +2) but a FALSE only with a confirmed one (209 "correct-unconfirmed" at 0;
# Theta's YAML race witnesses -- the two racing accesses as targets of one
# segment -- were confirmed): there only the violation witness is written.
WITNESS = "witness.yml"
WITNESS_CONTENT = "witness-content.yml"
WANTS_CORRECTNESS_WITNESS = ("unreach-call.prp" in property_path
                             or "no-overflow.prp" in property_path)
WANTS_WITNESS = (WANTS_CORRECTNESS_WITNESS
                 or "no-data-race.prp" in property_path)
if WANTS_WITNESS:
    flags += "--yaml-witness %s " % WITNESS_CONTENT


def quoted(s):
    return "'" + s.replace("'", "''") + "'"


def write_witness(entry_type, format_version, content):
    """Write witness.yml: one entry of entry_type around the given content
    (YAML list lines, or None for an empty list)."""
    with open(program_path, "rb") as f:
        sha256 = hashlib.sha256(f.read()).hexdigest()
    with open(property_path) as f:
        specification = " ".join(l.strip() for l in f if l.strip())
    lines = [
        "- entry_type: %s" % quoted(entry_type),
        "  metadata:",
        "    format_version: %s" % quoted(format_version),
        "    uuid: %s" % quoted(str(uuid.uuid4())),
        "    creation_time: %s" % quoted(datetime.datetime.now(
            datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")),
        "    producer:",
        "      name: 'Iëkke'",
        "      version: '2.0'",
        "    task:",
        "      input_files:",
        "      - %s" % quoted(os.path.basename(program_path)),
        "      input_file_hashes:",
        "        %s: %s" % (quoted(program_path), quoted(sha256)),
        "      specification: %s" % quoted(specification),
        "      data_model: %s" % quoted("LP64" if data_model == "--64" else "ILP32"),
        "      language: 'C'",
    ]
    if content:
        lines.append("  content:")
        lines += ["  " + l for l in content.splitlines()]
    else:
        lines.append("  content: []")
    with open(WITNESS, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")


def write_violation_witness():
    """The violation witness of the last run, if the tool wrote one."""
    try:
        with open(WITNESS_CONTENT, encoding="utf-8", errors="replace") as f:
            content = f.read()
    except OSError:
        return
    if content.strip():
        write_witness("violation_sequence", "2.2", content)


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


def loop_bounds(left):
    """[(loop id, suggested limit or None)] from --unwind-suggest; [] if none."""
    global current
    cmd = "./iekke_exe %s %s --unwind-suggest" % (program_path, flags)
    current = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, text=True,
                               errors="replace", start_new_session=True)
    try:
        out, _ = current.communicate(timeout=max(0.01, min(SUGGEST_TIMEOUT, left)))
    except subprocess.TimeoutExpired:
        kill_bound(current)
        current.communicate()
        out = ""
    current = None
    loops = []
    for line in out.splitlines():
        m = re.match(r"Loop (\S+):$", line.strip())
        if m:
            loops.append([m.group(1), None])
            continue
        m = re.match(r"Suggested unwind limit: (\d+)$", line.strip())
        if m and loops:
            loops[-1][1] = int(m.group(1))
    return loops


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

def bounds():
    """The bounds in the order they are tried. The loop limits are asked for
    only once the reduced program has had its try, so that a slow suggestion
    does not delay the first bound."""
    yield REDUCED
    loops = loop_bounds(BUDGET - (time.time() - started))
    if any(limit for _, limit in loops):
        unwindset = ",".join("%s:%d" % (loop, min(limit or UNSUGGESTED, SUGGEST_CAP))
                             for loop, limit in loops)
        print("suggested loop limits: %s" % unwindset)
        yield (UNSUGGESTED, SUGGEST_ROUNDS, "--unwindset " + unwindset)
    for u, r in SCHEDULE:
        yield (u, r, "")


# A violation found with more rounds than needed gives a longer witness, and a
# validator has 90 s to follow it: on pthread-divine/one_time_barrier_3t the
# race found at 3 rounds (lines 743/759, after a second pass through the
# barrier) was never confirmed by Dartagnan, the one found at 2 rounds (lines
# 715/717, at the first entry) twice out of two. A violation at fewer rounds is
# one at more rounds too, so the answer does not change: the run is repeated at
# SHORT_ROUNDS for a short while, and its witness kept if it finds one. Only
# for data races: over the 620 correct FALSE answers (2027 validators, each
# change repeated three times) it gained two races (one_time_barrier_3t,
# reorder_5-race) and lost one reachability task, whose shorter witness
# UAutomizer rejects (goblint 28-race_reach_77-tricky_address4_racing).
SHORT_ROUNDS = 2
SHORT_SLICE = 30


def shorter_witness(cmd, rounds):
    """Replace the witness of a violation found at `rounds` by one found at
    SHORT_ROUNDS with the same flags, when that run finds one in time."""
    left = BUDGET - (time.time() - started)
    if left <= MIN_SLICE or not os.path.exists(WITNESS_CONTENT):
        return
    shutil.copyfile(WITNESS_CONTENT, WITNESS_CONTENT + ".long")
    os.remove(WITNESS_CONTENT)
    short = (cmd.replace("--rounds %d " % rounds, "--rounds %d " % SHORT_ROUNDS)
                .replace(" --por ", " --no-por "))
    proc = subprocess.Popen(short, shell=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True,
                            errors="replace", start_new_session=True)
    try:
        out, _ = proc.communicate(timeout=min(SHORT_SLICE, left - MIN_SLICE))
    except subprocess.TimeoutExpired:
        kill_bound(proc)
        proc.communicate()
        out = ""
    if verdict_of(out) == "FAILED" and os.path.exists(WITNESS_CONTENT):
        print("  shorter witness: violation at rounds=%d" % SHORT_ROUNDS)
        os.remove(WITNESS_CONTENT + ".long")
    else:
        os.replace(WITNESS_CONTENT + ".long", WITNESS_CONTENT)


# SV-COMP counts an array access out of bounds as valid-deref. The tool-info
# module it runs (benchexec/tools/iekke.py) recognises valid-deref only by
# "pointer_dereference." or "alloc.assertion." on a FAILURE line, and CBMC
# names its --bounds-check properties "array_bounds.": alone, such a failure
# is read as false(unreach-call), a wrong answer for a memory-safety task
# (pthread-array-bounds/global-histogram, valid-deref).
def deref_reading(out):
    failed = [l for l in out.splitlines()
              if l.startswith("[") and l.rstrip().endswith(": FAILURE")]
    others = ("pointer_dereference.", "alloc.assertion.", "memory-leak.")
    if (any(".array_bounds." in l for l in failed)
            and not any(k in l for l in failed for k in others)):
        return ("valid-deref: an array access out of bounds, "
                "a pointer_dereference. FAILURE for SV-COMP")
    return None


# The concrete guard. A SUCCESSFUL from bounded model checking is only as deep
# as the bound, and a bug deeper than the bound makes it a wrong TRUE (-32):
# pthread-overflow/deep-* need 14 to 36 context switches, and
# weaver-mutants/popl20-nonblocking-cntr-v2 overflows after 2^31 iterations,
# which a native run reaches in seconds. Before a SUCCESSFUL is reported, the
# program is compiled with the sanitizer of the property and run, with
# extreme and random values for __VERIFIER_nondet_* and random delays at
# thread creation and around locks. A run that shows the violation is a
# concrete execution of the bug, so the answer is FAILED instead.
GUARD_HARNESS = r"""
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <limits.h>
#include <unistd.h>
#include <pthread.h>
#include <sched.h>
#include <time.h>
static unsigned long long g_state = 88172645463325252ULL;
static int g_seed = -1;
static pthread_mutex_t g_lock = PTHREAD_MUTEX_INITIALIZER;
static unsigned long long g_rand(void)
{ g_state ^= g_state << 13; g_state ^= g_state >> 7; g_state ^= g_state << 17; return g_state; }
static int g_kind(void)
{
  if(g_seed < 0) { const char *s = getenv("GUARD_SEED"); g_seed = s ? atoi(s) : 0;
                   g_state += (unsigned long long)g_seed * 0x9E3779B97F4A7C15ULL; }
  if(g_seed <= 3) return g_seed;
  unsigned long long r = g_rand() % 10;
  return r < 2 ? 0 : r < 3 ? 1 : r < 4 ? 2 : r < 5 ? 3 : r < 6 ? 4 : r < 8 ? 5 : 6;
}
#define NONDET(name, T, MAX, MIN) T name(void) { \
  int k; T v; real_lock(&g_lock); k = g_kind(); \
  v = k == 0 ? (T)(MAX) : k == 1 ? (T)(MIN) : k == 2 ? (T)0 : k == 3 ? (T)-1 \
    : k == 5 ? (T)(1 + g_rand() % 16) : k == 6 ? (T)(1 + g_rand() % 64) : (T)g_rand(); \
  real_unlock(&g_lock); return v; }
#undef pthread_mutex_lock
#undef pthread_mutex_unlock
#undef pthread_create
#undef pthread_cond_wait
#undef pthread_join
static int real_lock(pthread_mutex_t *m) { return pthread_mutex_lock(m); }
static int real_unlock(pthread_mutex_t *m) { return pthread_mutex_unlock(m); }
NONDET(__VERIFIER_nondet_int, int, INT32_MAX, INT32_MIN)
NONDET(__VERIFIER_nondet_uint, unsigned int, UINT32_MAX, 0)
NONDET(__VERIFIER_nondet_unsigned, unsigned int, UINT32_MAX, 0)
NONDET(__VERIFIER_nondet_long, long, LONG_MAX, LONG_MIN)
NONDET(__VERIFIER_nondet_ulong, unsigned long, ULONG_MAX, 0)
NONDET(__VERIFIER_nondet_short, short, INT16_MAX, INT16_MIN)
NONDET(__VERIFIER_nondet_ushort, unsigned short, UINT16_MAX, 0)
NONDET(__VERIFIER_nondet_char, char, 127, -128)
NONDET(__VERIFIER_nondet_uchar, unsigned char, 255, 0)
NONDET(__VERIFIER_nondet_bool, _Bool, 1, 0)
NONDET(__VERIFIER_nondet_longlong, long long, INT64_MAX, INT64_MIN)
NONDET(__VERIFIER_nondet_ulonglong, unsigned long long, UINT64_MAX, 0)
NONDET(__VERIFIER_nondet_size_t, size_t, SIZE_MAX, 0)
static pthread_mutex_t g_atomic = PTHREAD_MUTEX_INITIALIZER;
void __VERIFIER_atomic_begin(void) { pthread_mutex_lock(&g_atomic); }
void __VERIFIER_atomic_end(void) { pthread_mutex_unlock(&g_atomic); }
void __guard_abort(void) { _exit(0); }
void __assert_fail(const char *a, const char *f, unsigned l, const char *fn)
{ fprintf(stderr, "GUARD_REACH %s:%u\n", f, l); _exit(99); }
static __thread unsigned long long t_state;
static int quiet = -1, turns = -1;
static void noise(void)
{
  if(quiet < 0) quiet = getenv("GUARD_QUIET") != 0;
  if(turns < 0) turns = getenv("GUARD_TURNS") != 0;
  if(quiet) return;
  /* on one core, giving the processor up at every synchronisation makes
     the threads take turns, step by step */
  if(turns) { sched_yield(); return; }
  if(!t_state) t_state = (unsigned long long)pthread_self() ^ (unsigned long long)getpid() * 0x9E3779B97F4A7C15ULL ^ (unsigned long long)clock();
  t_state ^= t_state << 13; t_state ^= t_state >> 7; t_state ^= t_state << 17;
  unsigned r = t_state % 8;
  if(r == 0) usleep(t_state % 2000); else if(r < 3) sched_yield();
}
void __guard_noise(void) { noise(); }
int __guard_lock(pthread_mutex_t *m) { noise(); return pthread_mutex_lock(m); }
int __guard_unlock(pthread_mutex_t *m) { int r = pthread_mutex_unlock(m); noise(); return r; }
int __guard_cond_wait(pthread_cond_t *c, pthread_mutex_t *m) { noise(); return pthread_cond_wait(c, m); }
int __guard_join(pthread_t t, void **r) { noise(); return pthread_join(t, r); }
struct guard_start { void *(*f)(void *); void *a; };
static void *trampoline(void *p)
{ struct guard_start s = *(struct guard_start *)p; free(p); noise(); return s.f(s.a); }
int __guard_create(pthread_t *t, const pthread_attr_t *at, void *(*f)(void *), void *a)
{
  struct guard_start *s = malloc(sizeof *s); int r;
  if(!s) return 11;
  s->f = f; s->a = a; r = pthread_create(t, at, trampoline, s); noise(); return r;
}
"""

# Only the evidence that is the property itself: reach_error() reached, a
# signed arithmetic overflow, an out-of-bounds or freed access. Not data
# races: ThreadSanitizer reported races on 40 of 264 no-data-race tasks
# expected TRUE (the pthread-atomic-qualifier _Atomic accesses, CAS loops).
# Force-included into a .c task: the C11 atomic operations yield like the
# locks do, so that threads synchronising through atomics alone take turns
# too. Not a store: a step that loads and then stores would take turns
# between the two, not between steps. A .i task has them expanded
# already, and including stdatomic.h before it would clash.
GUARD_ATOMICS = r"""
#include <stdatomic.h>
void __guard_noise(void);
#undef atomic_load
#define atomic_load(p) (__guard_noise(), atomic_load_explicit((p), memory_order_seq_cst))
#undef atomic_store
#define atomic_store(p, v) atomic_store_explicit((p), (v), memory_order_seq_cst)
#undef atomic_exchange
#define atomic_exchange(p, v) (__guard_noise(), atomic_exchange_explicit((p), (v), memory_order_seq_cst))
#undef atomic_fetch_add
#define atomic_fetch_add(p, v) (__guard_noise(), atomic_fetch_add_explicit((p), (v), memory_order_seq_cst))
#undef atomic_fetch_sub
#define atomic_fetch_sub(p, v) (__guard_noise(), atomic_fetch_sub_explicit((p), (v), memory_order_seq_cst))
#undef atomic_compare_exchange_strong
#define atomic_compare_exchange_strong(p, e, v) (__guard_noise(), atomic_compare_exchange_strong_explicit((p), (e), (v), memory_order_seq_cst, memory_order_seq_cst))
#undef atomic_compare_exchange_weak
#define atomic_compare_exchange_weak(p, e, v) (__guard_noise(), atomic_compare_exchange_weak_explicit((p), (e), (v), memory_order_seq_cst, memory_order_seq_cst))
"""

GUARD_EVIDENCE = {
    "unreach-call.prp": r"GUARD_REACH",
    "no-overflow.prp": r"runtime error: signed integer overflow",
    "valid-memsafety.prp": r"ERROR: AddressSanitizer: (heap-buffer-overflow|stack-buffer-overflow|global-buffer-overflow|heap-use-after-free|stack-use-after-return|stack-use-after-scope|dynamic-stack-buffer-overflow)",
}
# Measured 2026-11-07, 20 s per task, on the 1378 unreach-call, no-overflow
# and valid-memsafety answers SUCCESSFUL with expected TRUE: one FAILED,
# goblint-regression/28-race_reach_07-cond_racing2, whose "if (i+1)" with
# i = INT_MAX does overflow (label question); on the expected FALSE ones it
# found deep-asymmetric, deep-fib-mutex, deep-fib-nondet-start,
# deep-scaled-feedback, sssc12_variant-v1 (and popl20-nonblocking-cntr-v2
# with more time). DEAGLE_GUARD=0 turns it off.
GUARD_BUDGET = float(os.environ.get("DEAGLE_GUARD", "300"))


def one_core():
    # On one core each thread runs whole time slices without contending for
    # its locks: popl20-nonblocking-cntr-v2 overflowed after 106 s on one
    # core and not in 150 s on several. SV-COMP gives a run one core anyway.
    try:
        os.sched_setaffinity(0, {min(os.sched_getaffinity(0))})
    except (AttributeError, OSError):
        pass


def concrete_violation(budget):
    """The first line of evidence of a violation in a concrete run, or None."""
    kind = [k for k in GUARD_EVIDENCE if k in property_path]
    if not kind or budget < 10 or not shutil.which("gcc"):
        return None
    kind = kind[0]
    lp64 = data_model == "--64"
    mflag = "-m64" if lp64 else "-m32"
    san = {"unreach-call.prp": [],
           "no-overflow.prp": ["-fsanitize=signed-integer-overflow",
                               "-fno-sanitize-recover=all"],
           "valid-memsafety.prp": ["-fsanitize=address"],
           "no-data-race.prp": ["-fsanitize=thread"]}[kind]
    env = dict(os.environ, ASAN_OPTIONS="detect_leaks=0",
               TSAN_OPTIONS="halt_on_error=1 exitcode=66")
    run_prefix = []
    if kind == "no-data-race.prp":
        # ThreadSanitizer needs 64 bits; whether a race exists does not
        # depend on the data model. It cannot start under the address
        # randomisation of recent kernels.
        mflag = "-m64"
        if shutil.which("setarch"):
            run_prefix = ["setarch", os.uname().machine, "-R"]
    d = tempfile.mkdtemp(prefix="guard_", dir=".")
    try:
        with open(os.path.join(d, "harness.c"), "w") as f:
            f.write(GUARD_HARNESS)
        with open(os.path.join(d, "atomics.h"), "w") as f:
            f.write(GUARD_ATOMICS)
        exe = os.path.join(d, "a.out")
        harness_o = os.path.join(d, "harness.o")
        # The harness on its own, without the renaming of the calls of the
        # task: renamed in its own pthread.h too, its calls of the real
        # functions had no declaration, an error for the GCC 15 of the
        # SV-COMP 2027 image (only a warning for older ones).
        steps = [["gcc", mflag, "-w", "-O0", "-g", "-c"] + san +
                 ["-o", harness_o, os.path.join(d, "harness.c")],
                 ["gcc", mflag, "-w", "-O0", "-g", "-fno-builtin",
                  "-Dabort=__guard_abort",
                  "-Dpthread_mutex_lock=__guard_lock",
                  "-Dpthread_mutex_unlock=__guard_unlock",
                  "-Dpthread_create=__guard_create",
                  "-Dpthread_cond_wait=__guard_cond_wait",
                  "-Dpthread_join=__guard_join"] + san +
                 ["-o", exe, program_path, harness_o, "-lpthread"]]
        if program_path.endswith(".c"):
            steps.insert(1, steps[1][:-5] + ["-include", os.path.join(d, "atomics.h")]
                         + steps[1][-5:])
        built = False
        for i, cc in enumerate(steps):
            if built:
                break
            try:
                rc = subprocess.run(cc, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                                    timeout=min(60, budget)).returncode
            except subprocess.TimeoutExpired:
                rc = 1
            if i == 0 and rc != 0:
                return None
            # the task with the atomics header, else without it
            built = i > 0 and rc == 0
        if not built:
            return None
        end = time.time() + budget
        seed = 0
        while time.time() < end - 1:
            # Runs without the delays: a bug after 2^31 iterations of a
            # locked loop is out of reach with a delay at every lock. The
            # first run (largest values, no delays) may take 60% of the budget.
            # A third kind of run takes turns at every lock: the deep-fib
            # tasks overflow only when two threads alternate step by step.
            env["GUARD_SEED"] = str(seed // 3)
            env.pop("GUARD_QUIET", None)
            env.pop("GUARD_TURNS", None)
            if seed % 3 == 0:
                env["GUARD_QUIET"] = "1"
            elif seed % 3 == 1:
                env["GUARD_TURNS"] = "1"
            cap = budget * 0.6 if seed == 0 else 10
            seed += 1
            try:
                r = subprocess.run(run_prefix + [exe], env=env, stdout=subprocess.DEVNULL,
                                   stderr=subprocess.PIPE, text=True, errors="replace",
                                   timeout=max(1, min(cap, end - time.time())),
                                   start_new_session=True, preexec_fn=one_core)
            except subprocess.TimeoutExpired:
                continue
            m = re.search(GUARD_EVIDENCE[kind] + ".*", r.stderr)
            if m and (kind != "unreach-call.prp" or r.returncode == 99):
                return m.group(0)[:200]
        return None
    finally:
        shutil.rmtree(d, ignore_errors=True)


def report_concrete(evidence):
    print("concrete run: %s" % evidence)
    # the lines the tool-info module of BenchExec reads the property from
    if "valid-memsafety.prp" in property_path:
        print("valid-deref: a concrete run, a pointer_dereference. FAILURE")
    if "no-overflow.prp" in property_path:
        print("no-overflow: a concrete run, an arithmetic overflow. FAILURE")
    print("FAILED")
    sys.exit(0)


# Without an answer the bounds take the whole budget, and the guard would
# have none left: it keeps GUARD_RESERVE seconds (120 of SV-COMP 900). Of
# the 449 FAILED answers of the full run of 2026-11-06 one came later than
# 700 s.
GUARD_RESERVE = (min(120, 0.15 * BUDGET)
                 if GUARD_BUDGET > 0 and any(k in property_path for k in GUARD_EVIDENCE)
                 else 0)

for unwind, rounds, extra in bounds():
    left = BUDGET - (time.time() - started)
    if left <= MIN_SLICE + (GUARD_RESERVE if bounded_safe is None else 0):
        break
    if bounded_safe is not None and time.time() - started >= STOP_AFTER:
        print("stop rule: a safe answer is held and %.0fs have passed" % STOP_AFTER)
        break

    slice_ = min(left, SLICE if not extra else
                 SUGGEST_SLICE if extra.startswith("--unwindset") else REDUCED_SLICE)
    bound_flags = ARRAY_RF_BYTES + ENCODING_FLAGS
    if "valid-memsafety.prp" not in property_path:
        bound_flags += "--dynamic-array-bound %d " % array_bound(unwind)
    por = "--por" if rounds >= POR_MIN_ROUNDS else "--no-por"
    cmd = ("./iekke_exe %s %s --unwind %d --rounds %d %s --verbosity 8 --glucose %s%s"
           % (program_path, flags, unwind, rounds, por, bound_flags, extra))
    print("try unwind=%d rounds=%d %s(%.0fs for this bound, %.0fs left)"
          % (unwind, rounds, extra + " " if extra else "", slice_, left))
    # Merged, not concatenated: the verdict is the last line of the run,
    # and stdout + stderr glued end to end puts every warning after it, so
    # the verdict stops being last and every run reads as "no verdict".
    if WANTS_WITNESS and os.path.exists(WITNESS_CONTENT):
        os.remove(WITNESS_CONTENT)
    current = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, text=True,
                               errors="replace", start_new_session=True)
    deadline = time.time() + slice_
    stop_at = started + STOP_AFTER if bounded_safe is not None else float("inf")
    out = None
    stop = None
    while out is None:
        try:
            # A timed-out communicate() keeps what it has read so far.
            out, _ = current.communicate(
                timeout=max(0.01, min(POLL, deadline - time.time())))
        except subprocess.TimeoutExpired:
            if time.time() >= stop_at:
                stop = "stop rule"
            elif time.time() >= deadline:
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
        if stop == "stop rule":
            break
        continue

    verdict = verdict_of(out)
    # Not the verdict word itself: the tool-info module of BenchExec that
    # SV-COMP uses (benchexec/tools/iekke.py) answers TRUE if "SUCCESSFUL"
    # appears on ANY line of the output, before it looks for "FAILED". A
    # progress line "-> SUCCESSFUL" ahead of a bug found at a later bound would
    # turn that bug into a wrong TRUE (-32), and an UNKNOWN into a TRUE. Only
    # the last line of the output may carry a verdict word.
    print("  -> %s" % {"SUCCESSFUL": "safe at this bound",
                       "FAILED": "violation at this bound"}.get(verdict, "no verdict"))

    if verdict == "FAILED":
        if WANTS_WITNESS:
            if rounds > SHORT_ROUNDS and "no-data-race.prp" in property_path:
                shorter_witness(cmd, rounds)
            write_violation_witness()
        print(out)
        if "valid-memsafety.prp" in property_path and deref_reading(out):
            print(deref_reading(out))
        # The tool-info module recognises a data race only by
        # "nodatarace.assertion." on a FAILURE line; the tool prints
        # "datarace: FAILURE", read as false(unreach-call). In the SV-COMP 2027
        # pre-run none of 231 such answers was validated, while answers read
        # as false(no-data-race) were.
        if "no-data-race.prp" in property_path:
            print("no-data-race: a data race, a nodatarace.assertion. FAILURE")
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
    if (verdict == "SUCCESSFUL" and not vacuous
            and (not extra or extra.startswith("--unwindset"))):
        bounded_safe = out
    # No verdict means a refusal or a crash at *this* bound -- most often
    # --object-bits exhaustion, which only the very large unwinds provoke. It
    # says nothing about a bound that is smaller on that axis and deeper on
    # rounds, so it must not end the search.


# Before a SUCCESSFUL, and before an UNKNOWN: a violation a concrete run
# shows is the answer either way.
left = BUDGET - (time.time() - started)
evidence = concrete_violation(min(GUARD_BUDGET, left - 30))
if evidence:
    report_concrete(evidence)
if bounded_safe is not None:
    if WANTS_CORRECTNESS_WITNESS:
        write_witness("invariant_set", "2.1", None)
    print(bounded_safe)
    print("SUCCESSFUL")
    sys.exit(0)

print("UNKNOWN")
sys.exit(1)
