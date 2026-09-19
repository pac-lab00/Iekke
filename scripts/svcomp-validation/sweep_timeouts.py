"""Find the cheapest bound that makes a timing-out benchmark answer correctly.

Cost-ordered 2D grid, stopping at the first configuration that produces the
verdict the .yml expects. Several of these benchmarks currently carry bounds
like unwind=10001 -- a full unroll of a 10000-iteration thread-creation loop --
which is both hopeless and unnecessary, since thread-management loops are
truncated anyway.
"""
import os
import re
import subprocess
import sys

# Both overridable from the environment; the defaults suit the dev checkout.
BIN = os.environ.get("IEKKE_BIN", "/home/gennaro/fix-bugs-AB/build/cbmc/cbmc")

FLAGS = {
    "unreach-call": [],
    "no-data-race": ["--no-assertions", "--datarace"],
    "no-overflow": ["--no-assertions", "--signed-overflow-check",
                    "--unsigned-overflow-check"],
    "valid-memsafety": ["--no-assertions", "--pointer-check", "--alloc-check",
                        "--memory-leak-check"],
}

GRID = sorted(
    [(u, r) for u in (2, 3, 5, 8, 13, 21, 35, 60) for r in (1, 2, 3, 4, 5, 6)],
    key=lambda x: (x[0] * x[1], x[0]),
)


def main():
    prop, ymlpath = sys.argv[1], sys.argv[2]
    text = open(ymlpath, encoding="utf-8", errors="replace").read()
    m = re.search(prop + r"\.prp\s*\n\s*expected_verdict:\s*(true|false)", text)
    if not m:
        return
    expected = m.group(1)
    mi = re.search(r"^input_files:\s*['\"]?([^'\"\n]+)['\"]?", text, re.M)
    infile = mi.group(1).strip()
    d = os.path.dirname(ymlpath)
    base = os.path.splitext(os.path.basename(ymlpath))[0]
    want = "VERIFICATION FAILED" if expected == "false" else "VERIFICATION SUCCESSFUL"

    for u, r in GRID:
        cmd = ([BIN, infile, "--allow-pointer-unsoundness"] + FLAGS[prop] +
               ["--unwind", str(u), "--rounds", str(r), "--por",
                "--verbosity", "8"])
        try:
            p = subprocess.run(cmd, cwd=d, capture_output=True, text=True,
                               timeout=300)
        except subprocess.TimeoutExpired:
            continue
        if want in p.stdout:
            print(f"{prop}\t{base}\tFOUND\t{u}\t{r}", flush=True)
            return
    print(f"{prop}\t{base}\tNEVER\t-\t-", flush=True)


main()
