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


def run(mode, budget, term_after=None):
    d = tempfile.mkdtemp(prefix="deagle_blind_test_")
    tool = os.path.join(d, "iekke_exe")
    with open(tool, "w") as f:
        f.write(FAKE_TOOL)
    os.chmod(tool, 0o755)
    with open(os.path.join(d, "mode"), "w") as f:
        f.write(mode)
    env = dict(os.environ, DEAGLE_BUDGET=str(budget))
    w = subprocess.Popen([sys.executable, WRAPPER, "no-data-race.prp", "prog.c"],
                         cwd=d, env=env, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, text=True)
    if term_after is not None:
        time.sleep(term_after)
        w.send_signal(signal.SIGTERM)
    out = w.communicate(timeout=budget + 30)[0]
    time.sleep(0.5)
    pids = [int(p) for p in open(os.path.join(d, "pids")).read().split()] \
        if os.path.exists(os.path.join(d, "pids")) else []
    survivors = [p for p in pids if alive(p)]
    for p in survivors:               # clean up by exact PID
        try:
            os.kill(p, signal.SIGKILL)
        except ProcessLookupError:
            pass
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

sys.exit(0 if ok else 1)
