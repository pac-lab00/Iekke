#!/usr/bin/python3
# Enumerate the concurrency corpus from SV-COMP's own category definition.
#
# The first attempt scoped it as "every benchmark carrying no-data-race", which
# sounded like the concurrency set and is not: list1 and
# bounded_mpmc_check_empty live in pthread-memsafety, declare only
# valid-memsafety, and so fell outside -- the two benchmarks with the longest
# history of wrong answers, invisible to the measurement meant to rank wrong
# answers. sv-benchmarks/c/Concurrency.set is the authoritative list and is not
# ours to argue with: nineteen directory globs.
import glob
import os
import sys
import yaml

SVB = "/home/gennaro/iekke-sms-eval/sv-benchmarks/c"
PROPS = ("no-data-race", "unreach-call", "valid-memsafety", "no-overflow")

patterns = []
with open(os.path.join(SVB, "Concurrency.set")) as fh:
    for line in fh:
        line = line.strip()
        if line and not line.startswith("#"):
            patterns.append(line)

ymls = []
for pat in patterns:
    ymls.extend(sorted(glob.glob(os.path.join(SVB, pat))))

rows, dms, skipped = [], {}, 0
for y in ymls:
    with open(y) as fh:
        doc = yaml.safe_load(fh)
    if not doc:
        continue
    src = doc.get("input_files")
    if isinstance(src, list):
        src = src[0]
    prog = os.path.join(os.path.dirname(y), src) if src else None
    if not prog or not os.path.isfile(prog):
        skipped += 1
        continue
    dm = (doc.get("options") or {}).get("data_model", "ILP32")
    dms[dm] = dms.get(dm, 0) + 1
    for p in doc.get("properties") or []:
        exp = p.get("expected_verdict")
        if exp is None:
            continue
        name = os.path.splitext(os.path.basename(p.get("property_file", "")))[0]
        if name in PROPS:
            rows.append((name, prog, "true" if exp else "false", dm))

out = sys.argv[1] if len(sys.argv) > 1 else "/home/gennaro/corpus_official.tsv"
with open(out, "w") as fh:
    for r in rows:
        fh.write("\t".join(r) + "\n")

print("directories:", len(patterns))
print("benchmarks: %d  (missing source: %d)" % (len(dms and ymls) - skipped, skipped))
print("pairs:", len(rows))
print("data models:", dms)
ceiling = sum(2 if r[2] == "true" else 1 for r in rows)
print("ceiling:", ceiling)
for p in PROPS:
    t = sum(1 for r in rows if r[0] == p and r[2] == "true")
    f = sum(1 for r in rows if r[0] == p and r[2] == "false")
    print("  %-18s true=%-5d false=%d" % (p, t, f))
