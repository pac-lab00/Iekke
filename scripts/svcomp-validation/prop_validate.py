"""Faithful validation for any of the four SV-COMP concurrency properties.

Mirrors what the deagle wrapper does -- same per-property flags, same
calibration CSV lookup, same unwind 2 / rounds 1 (rounds 3 for no-data-race)
fallback when a benchmark has no calibrated row -- but runs each task on the
input file its .yml actually names, from the benchmark's own directory.

Usage: prop_validate.py <property> <path/to/task.yml>
"""
import csv
import os
import re
import subprocess
import sys

# Both overridable from the environment; the defaults suit the dev checkout.
BIN = os.environ.get("IEKKE_BIN", "/home/gennaro/fix-bugs-AB/build/cbmc/cbmc")
CSV = os.environ.get(
    "IEKKE_CSV",
    "/home/gennaro/iekke-sms-eval/benchexec/lazydeagle-ciuccio/"
    "output_unwind_rounds.csv")

FLAGS = {
    "unreach-call": [],
    "no-data-race": ["--no-assertions", "--datarace"],
    "no-overflow": ["--no-assertions", "--signed-overflow-check",
                    "--unsigned-overflow-check"],
    "valid-memsafety": ["--no-assertions", "--pointer-check", "--alloc-check",
                        "--memory-leak-check"],
}

KNOWN_UNKNOWN = {
    "indexer", "semaphore-posix-race", "semaphore-posix-race-2",
    "thread-join-array-const-race", "09-regions_23-evilcollapse_rc",
    "09-regions_26-alloc_region_rc", "09-regions_20-arrayloop2_rc",
    "per-thread-array-join-counter-race",
    "per-thread-array-join-counter-race-2",
    "per-thread-array-join-counter-race-3",
    "per-thread-array-join-counter-race-4",
}


def load_bounds(prop):
    b = {}
    with open(CSV, newline="") as f:
        for row in csv.DictReader(f):
            if row["property"].strip() == prop:
                b[row["benchmark"].strip()] = (row["unwind"].strip(),
                                               row["rounds"].strip())
    return b


def main():
    prop, ymlpath = sys.argv[1], sys.argv[2]
    extra = sys.argv[3:]          # optional additional cbmc flags to evaluate
    text = open(ymlpath, encoding="utf-8", errors="replace").read()
    m = re.search(prop + r"\.prp\s*\n\s*expected_verdict:\s*(true|false)", text)
    if not m:
        return
    expected = m.group(1)
    mi = re.search(r"^input_files:\s*['\"]?([^'\"\n]+)['\"]?", text, re.M)
    if not mi:
        return
    infile = mi.group(1).strip()
    d = os.path.dirname(ymlpath)
    base = os.path.splitext(os.path.basename(ymlpath))[0]
    if not os.path.isfile(os.path.join(d, infile)):
        print(f"{base}\t{expected}\tMISSING_INPUT\t-\t-", flush=True)
        return
    if prop == "no-data-race" and base in KNOWN_UNKNOWN:
        print(f"{base}\t{expected}\tUNKNOWN\t-\t-", flush=True)
        return

    bounds = load_bounds(prop)
    if base in bounds:
        u, r = bounds[base]
        src = "calibrated"
    else:
        u, r = "2", ("3" if prop == "no-data-race" else "1")
        src = "fallback"

    cmd = ([BIN, infile, "--allow-pointer-unsoundness"] + FLAGS[prop] + extra +
           ["--unwind", u, "--rounds", r, "--por", "--verbosity", "8"])
    try:
        p = subprocess.run(cmd, cwd=d, capture_output=True, text=True,
                           timeout=300)
        out, rc = p.stdout, p.returncode
    except subprocess.TimeoutExpired:
        print(f"{base}\t{expected}\tTIMEOUT\t{src}\t{u}/{r}", flush=True)
        return
    if rc in (139, 134):
        v = f"CRASH(rc={rc})"
    elif "VERIFICATION SUCCESSFUL" in out:
        v = "SUCCESSFUL"
    elif "VERIFICATION FAILED" in out:
        v = "FAILED"
    else:
        v = f"NOVERDICT(rc={rc})"
    print(f"{base}\t{expected}\t{v}\t{src}\t{u}/{r}", flush=True)


main()
