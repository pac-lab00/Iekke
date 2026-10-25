#! /usr/bin/python3
# Regression test for deagle_blind.py's process handling. No real analysis is
# run: a fake iekke_exe stands in for the tool, starts a child the way the tool
# starts external glucose, and either hangs or prints a verdict.
#
#   python3 deagle_blind_test.py [path/to/deagle_blind.py]
#
# Exit 0 if every check passes, 1 otherwise.
#
# Case "hang": every bound times out. Nothing the wrapper started may still be
# running once it has exited. Before the fix a timeout killed only /bin/sh, so
# the tool and its solver kept running into the next bound and past the end.
# Case "fail": a verdict on the last line still reaches the wrapper's output.
# Case "term": a SIGTERM to the wrapper mid-bound must also end that bound.
# Case "model": the --32/--64 BenchExec passes as the third argument reaches
# the tool. Before the fix it was dropped, so every task ran in the host's
# default data model (ILP32) whatever its yml said.
# Case "memory": a bound that outgrows the run's memory is stopped on its own,
# and the SUCCESSFUL an earlier bound found is still reported. Before the fix
# the bound grew until the run's limit killed the whole run from outside,
# taking that answer with it.
# Case "flags": no bound passes --thread-symmetry (measured slowdown), and
# --dynamic-array-bound min(max(unwind, 4), 64) for every property but memory
# safety, where an array cut to K elements would hide an out-of-bounds access;
# a bound with 7 or more rounds passes --por, any other --no-por.
# Case "suggest": the per-loop limits from --unwind-suggest reach the tool as
# --unwindset (a loop without a suggestion at 3), a FAILED from that step is
# reported, and a SUCCESSFUL from it is not: with every other bound giving no
# verdict the answer must stay UNKNOWN.
# Case "stop": once a SUCCESSFUL is held, the search ends at DEAGLE_STOP
# seconds, cutting the running bound, and reports it; without one it goes on.
# Case "official": the output read the way SV-COMP's tool-info module reads
# it (TRUE if "SUCCESSFUL" is on any line, else FALSE if "FAILED" is) must
# give the wrapper's answer: a bug found after a safe bound is FALSE, and an
# answer of UNKNOWN is not TRUE.
# Case "buffer": a wrapper killed from outside still leaves its "try" lines
# in the log. Before the fix they sat in a block buffer and were lost.
import os
import signal
import subprocess
import sys
import tempfile
import time

WRAPPER = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else
                          os.path.join(os.path.dirname(__file__), "deagle_blind.py"))

FAKE_TOOL = r'''#! /usr/bin/env python3
import os, subprocess, sys, time
here = os.path.dirname(os.path.abspath(__file__))
mode = open(os.path.join(here, "mode")).read().strip()
with open(os.path.join(here, "args"), "a") as f:
    f.write(" ".join(sys.argv[1:]) + "\n")
calls = len([l for l in open(os.path.join(here, "args")).read().splitlines()
             if "--unwind-suggest" not in l])          # bounds, not the limit request
if mode == "safe":
    print("VERIFICATION SUCCESSFUL")
    sys.exit(0)
if mode == "late_bug":
    # no verdict for the reduced program, safe at the first bound, the bug at the second
    if "--unwind-suggest" in sys.argv or calls == 1:
        sys.exit(0)
    print("VERIFICATION SUCCESSFUL" if calls == 2 else "VERIFICATION FAILED")
    sys.exit(0 if calls == 2 else 10)
if mode == "safe_then_nothing":
    # safe only for the reduced program (never reported), no verdict otherwise
    if calls == 1:
        print("VERIFICATION SUCCESSFUL")
    sys.exit(0)
if mode == "stop":
    if "--unwind-suggest" in sys.argv or calls == 1:
        sys.exit(0)                        # no limits suggested; reduced program: no verdict
    if calls == 2:                         # the first bound of the schedule
        print("VERIFICATION SUCCESSFUL")
        sys.exit(0)
    with open(os.path.join(here, "pids"), "a") as f:
        f.write("%d\n" % os.getpid())
    time.sleep(120)
if mode.startswith("suggest"):
    if "--unwind-suggest" in sys.argv:
        print("Loop main.0:\n  file prog.c line 5\nSuggested unwind limit: 21")
        print("Loop main.1:\n  file prog.c line 9\nNo suggested unwind limit")
    elif "--unwindset" in sys.argv:
        print("VERIFICATION " + ("FAILED" if mode == "suggest_fail" else "SUCCESSFUL"))
    sys.exit(0)
if mode == "hog":
    # The first bound is the reduced program, whose SUCCESSFUL is never kept;
    # the second is the first bound of the schedule.
    if calls <= 2:
        print("VERIFICATION SUCCESSFUL")
        sys.exit(0)
    with open(os.path.join(here, "pids"), "a") as f:
        f.write("%d\n" % os.getpid())
    held = []
    for mb in range(50, 1250, 50):        # 1.2 GB, touched, in 50 MB steps
        held.append(b"\x01" * (50 << 20))
        with open(os.path.join(here, "peak"), "w") as f:
            f.write(str(mb))
        time.sleep(0.2)
    time.sleep(120)
solver = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(120)"])
with open(os.path.join(here, "pids"), "a") as f:
    f.write("%d\n%d\n" % (os.getpid(), solver.pid))
if mode == "fail":
    solver.kill(); solver.wait()
    print("VERIFICATION FAILED")
    sys.exit(10)
time.sleep(120)
'''


def alive(pid):
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    # A zombie still answers kill(0); it is not running.
    try:
        with open("/proc/%d/stat" % pid) as f:
            return f.read().split(")")[-1].split()[0] != "Z"
    except FileNotFoundError:
        return True


def run(mode, budget, term_after=None, extra=(), env_extra=None,
        kill_after=None, prop="no-data-race.prp"):
    d = tempfile.mkdtemp(prefix="deagle_blind_test_")
    tool = os.path.join(d, "iekke_exe")
    with open(tool, "w") as f:
        f.write(FAKE_TOOL)
    os.chmod(tool, 0o755)
    with open(os.path.join(d, "mode"), "w") as f:
        f.write(mode)
    env = dict(os.environ, DEAGLE_BUDGET=str(budget), **(env_extra or {}))
    log = open(os.path.join(d, "wrapper.log"), "w")
    w = subprocess.Popen([sys.executable, WRAPPER, prop, "prog.c"]
                         + list(extra),
                         cwd=d, env=env, stdout=log,
                         stderr=subprocess.STDOUT, text=True)
    if term_after is not None:
        time.sleep(term_after)
        w.send_signal(signal.SIGTERM)
    if kill_after is not None:
        time.sleep(kill_after)
        w.kill()
    w.wait(timeout=budget + 30)
    log.close()
    out = open(os.path.join(d, "wrapper.log")).read()
    time.sleep(0.5)
    pids = [int(p) for p in open(os.path.join(d, "pids")).read().split()] \
        if os.path.exists(os.path.join(d, "pids")) else []
    survivors = [p for p in pids if alive(p)]
    for p in survivors:               # clean up by exact PID
        try:
            os.kill(p, signal.SIGKILL)
        except ProcessLookupError:
            pass
    args = open(os.path.join(d, "args")).read().splitlines() \
        if os.path.exists(os.path.join(d, "args")) else []
    run.args = args
    run.peak = int(open(os.path.join(d, "peak")).read()) \
        if os.path.exists(os.path.join(d, "peak")) else 0
    return out, pids, survivors


ok = True

out, pids, survivors = run("hang", 8)
if not pids:
    print("FAIL hang: the fake tool never ran (no pids recorded)")
    ok = False
elif survivors:
    print("FAIL hang: %d of %d processes outlived the wrapper: %s"
          % (len(survivors), len(pids), survivors))
    ok = False
elif out.strip().splitlines()[-1] != "UNKNOWN":
    print("FAIL hang: expected UNKNOWN, got %r" % out.strip().splitlines()[-1])
    ok = False
else:
    print("ok   hang: %d processes started over %d bounds, none survived"
          % (len(pids), len(pids) // 2))

out, pids, survivors = run("fail", 30)
last = out.strip().splitlines()[-1] if out.strip() else ""
if not pids:
    print("FAIL fail: the fake tool never ran")
    ok = False
elif last != "FAILED" or survivors:
    print("FAIL fail: last line %r, survivors %s" % (last, survivors))
    ok = False
else:
    print("ok   fail: verdict FAILED reported, nothing left running")

out, pids, survivors = run("hang", 60, term_after=2)
if not pids:
    print("FAIL term: the fake tool never ran")
    ok = False
elif survivors:
    print("FAIL term: %d of %d processes outlived a SIGTERM to the wrapper: %s"
          % (len(survivors), len(pids), survivors))
    ok = False
else:
    print("ok   term: SIGTERM to the wrapper took its bound down with it")

for model in ("--32", "--64"):
    out, pids, survivors = run("fail", 30, extra=(model,))
    if not run.args:
        print("FAIL model %s: the fake tool never ran" % model)
        ok = False
    elif any(model not in a.split() for a in run.args):
        print("FAIL model %s: the tool was called without it: %r"
              % (model, run.args[0]))
        ok = False
    else:
        print("ok   model %s: reached the tool on all %d calls"
              % (model, len(run.args)))

out, pids, survivors = run("hog", 30, env_extra={"DEAGLE_MEMLIMIT": str(600 << 20)})
last = out.strip().splitlines()[-1] if out.strip() else ""
if len(run.args) < 2:
    print("FAIL memory: the growing bound never ran")
    ok = False
elif run.peak >= 600 or last != "SUCCESSFUL" or survivors:
    print("FAIL memory: bound reached %d MB of a 600 MB limit, last line %r, "
          "survivors %s" % (run.peak, last, survivors))
    ok = False
else:
    print("ok   memory: bound stopped at %d MB of 600, SUCCESSFUL kept"
          % run.peak)

for prop in ("no-data-race.prp", "valid-memsafety.prp"):
    out, pids, survivors = run("safe", 10, prop=prop)
    bad = []
    for a in run.args:
        if "--unwind-suggest" in a:
            continue
        w = a.split()
        unwind = int(w[w.index("--unwind") + 1])
        want = [] if prop == "valid-memsafety.prp" else \
            ["--dynamic-array-bound", str(min(max(unwind, 4), 64))]
        got = w[w.index("--dynamic-array-bound"):][:2] \
            if "--dynamic-array-bound" in w else []
        rounds = int(w[w.index("--rounds") + 1])
        por = "--por" if rounds >= 7 else "--no-por"
        if (got != want or "--thread-symmetry" in a or "--array-rf-bytes" not in a
                or por not in w):
            bad.append(a)
    ladder = [(int(a.split()[a.split().index("--unwind") + 1]), int(a.split()[a.split().index("--rounds") + 1]))
              for a in run.args if "--unwind-suggest" not in a and "--unwindset" not in a and "--symmetric-instance" not in a]
    if ladder[:4] != [(2, 2), (4, 3), (8, 3), (8, 4)]:
        bad.append("ladder starts %s" % ladder[:4])
    if len(run.args) < 10:
        print("FAIL flags %s: only %d bounds ran" % (prop, len(run.args)))
        ok = False
    elif bad:
        print("FAIL flags %s: %d of %d calls wrong, first %r"
              % (prop, len(bad), len(run.args), bad[0]))
        ok = False
    else:
        print("ok   flags %s: right on all %d calls" % (prop, len(run.args)))

out, pids, survivors = run("suggest_fail", 20)
last = out.strip().splitlines()[-1] if out.strip() else ""
sets = [a for a in run.args if "--unwindset" in a]
if last != "FAILED" or not sets or "--unwindset main.0:21,main.1:3" not in sets[0]:
    print("FAIL suggest: last line %r, unwindset calls %r" % (last, sets[:1]))
    ok = False
else:
    print("ok   suggest: per-loop limits reached the tool, its FAILED reported")
out, pids, survivors = run("suggest_safe", 20)
last = out.strip().splitlines()[-1] if out.strip() else ""
if not any("--unwindset" in a for a in run.args):
    print("FAIL suggest: the suggested limits never reached the tool")
    ok = False
elif last != "UNKNOWN":
    print("FAIL suggest: a SUCCESSFUL from the suggested limits was reported (%r)" % last)
    ok = False
else:
    print("ok   suggest: its SUCCESSFUL was not reported")

t0 = time.time()
out, pids, survivors = run("stop", 60, env_extra={"DEAGLE_STOP": "5"})
took = time.time() - t0
last = out.strip().splitlines()[-1] if out.strip() else ""
if last != "SUCCESSFUL" or took > 20 or survivors or "stop rule" not in out:
    print("FAIL stop: last line %r after %.0fs, survivors %s" % (last, took, survivors))
    ok = False
else:
    print("ok   stop: SUCCESSFUL reported after %.0fs of a 60s budget, nothing left running" % took)

def official(out, rc):
    """benchexec/tools/iekke.py determine_result, as SV-COMP runs it"""
    if any("SUCCESSFUL" in l for l in out.splitlines()):
        return "true"
    if any("FAILED" in l for l in out.splitlines()):
        return "false"
    return "unknown" if rc == 1 else "error"

for mode, want in (("late_bug", "false"), ("safe_then_nothing", "unknown")):
    d = tempfile.mkdtemp(prefix="deagle_blind_test_")
    with open(os.path.join(d, "iekke_exe"), "w") as f:
        f.write(FAKE_TOOL)
    os.chmod(os.path.join(d, "iekke_exe"), 0o755)
    with open(os.path.join(d, "mode"), "w") as f:
        f.write(mode)
    p = subprocess.run([sys.executable, WRAPPER, "no-data-race.prp", "prog.c"], cwd=d,
                       env=dict(os.environ, DEAGLE_BUDGET="20"), capture_output=True, text=True)
    got = official(p.stdout + p.stderr, p.returncode)
    if got != want:
        print("FAIL official %s: SV-COMP would read %r, the answer is %r" % (mode, got, want))
        ok = False
    else:
        print("ok   official %s: read as %r" % (mode, got))

out, pids, survivors = run("hang", 60, kill_after=2)
if not pids:
    print("FAIL buffer: the fake tool never ran")
    ok = False
elif "try unwind=" not in out:
    print("FAIL buffer: the killed wrapper left no 'try' line in its log")
    ok = False
else:
    print("ok   buffer: the killed wrapper's log still shows its bound")

sys.exit(0 if ok else 1)
