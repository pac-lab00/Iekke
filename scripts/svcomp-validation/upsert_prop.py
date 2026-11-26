"""Upsert a single (property, benchmark) calibration row into a wrapper CSV."""
import csv
import os
import sys

prop, bench, unwind, rounds = sys.argv[1:5]
csvs = sys.argv[5:]

for path in csvs:
    with open(path, newline="") as f:
        rdr = csv.reader(f)
        header = next(rdr)
        rows = list(rdr)
    out, replaced = [], 0
    for r in rows:
        if len(r) >= 4 and r[0].strip() == prop and r[1].strip() == bench:
            out.append([r[0], r[1], unwind, rounds, r[4] if len(r) > 4 else "0"])
            replaced += 1
        else:
            out.append(r)
    if not replaced:
        out.append([prop, bench, unwind, rounds, "0"])
    with open(path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(header)
        w.writerows(out)
    print(f"  {os.path.basename(os.path.dirname(path))}: "
          f"{'replaced' if replaced else 'added'} {prop}/{bench} -> {unwind}/{rounds}")
