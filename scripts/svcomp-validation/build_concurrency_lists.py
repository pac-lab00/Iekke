"""Build the per-property task lists for the exact SV-COMP scope the tool
competes in: the directories named by Concurrency.set, one list per property
file that the benchexec rundefinitions use."""
import collections
import glob
import os
import re

ROOT = os.environ.get(
    "SVBENCH_ROOT", "/home/gennaro/iekke-sms-eval/sv-benchmarks/c")
PROPS = ("unreach-call", "no-data-race", "no-overflow", "valid-memsafety")

patterns = []
with open(os.path.join(ROOT, "Concurrency.set")) as f:
    for line in f:
        line = line.strip()
        if line and not line.startswith("#"):
            patterns.append(line)

ymls = []
for pat in patterns:
    ymls.extend(sorted(glob.glob(os.path.join(ROOT, pat))))

print(f"Concurrency.set resolves to {len(ymls)} .yml tasks")

per = collections.defaultdict(list)
verdicts = collections.Counter()
exts = collections.Counter()
for path in ymls:
    text = open(path, encoding="utf-8", errors="replace").read()
    mi = re.search(r"^input_files:\s*['\"]?([^'\"\n]+)['\"]?", text, re.M)
    ext = mi.group(1).strip().rsplit(".", 1)[-1] if mi else "?"
    for prop in PROPS:
        m = re.search(prop + r"\.prp\s*\n\s*expected_verdict:\s*(true|false)", text)
        if m:
            per[prop].append(path)
            verdicts[(prop, m.group(1))] += 1
            exts[(prop, ext)] += 1

for prop in PROPS:
    n = len(per[prop])
    out_dir = os.environ.get("TASKLIST_DIR", "/home/gennaro")
    with open(os.path.join(out_dir, f"tasks_{prop}.txt"), "w") as f:
        f.write("\n".join(per[prop]) + "\n")
    print(f"  {prop:16s} {n:5d} tasks  "
          f"(true={verdicts[(prop,'true')]:4d} false={verdicts[(prop,'false')]:4d}) "
          f".i={exts[(prop,'i')]:5d} .c={exts[(prop,'c')]:5d}")
