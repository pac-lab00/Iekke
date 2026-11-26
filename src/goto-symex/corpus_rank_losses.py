#!/usr/bin/python3
# Turn a scored run into the thing decisions get made from: a ranking by points
# lost, per benchmark and per directory.
#
# Ranking by benchmark rather than by task-property pair matters here. One
# benchmark carries up to four properties, so a systematic false alarm on it is
# not -16, it is -64; looking only at no-data-race is how four libvsync
# benchmarks sat outside the measured set while costing four times what anyone
# thought.
import collections
import os
import sys

PTS = {"T": None, "WRONG_TRUE": -32, "WRONG_FALSE": -16, "U": 0}


def load(path):
    rows = []
    with open(path) as fh:
        for i, line in enumerate(fh):
            f = line.rstrip("\n").split("\t")
            if i == 0 and f[0] == "property":
                continue
            if len(f) < 7:
                continue
            rows.append({"prop": f[0], "bm": f[1], "exp": f[2], "verdict": f[3],
                         "cls": f[4], "pts": int(f[5]), "ms": int(f[6])})
    return rows


def report(rows, label):
    total = sum(r["pts"] for r in rows)
    cls = collections.Counter(r["cls"] for r in rows)
    lost = -sum(r["pts"] for r in rows if r["cls"].startswith("WRONG"))

    print("## %s" % label)
    print("  %d task-property pairs over %d benchmarks"
          % (len(rows), len({r["bm"] for r in rows})))
    print("  correct %d   wrong-true %d   wrong-false %d   unknown %d"
          % (cls["T"], cls["WRONG_TRUE"], cls["WRONG_FALSE"], cls["U"]))
    print("  SCORE %d      thrown away by wrong answers: %d" % (total, lost))

    # The ceiling, so the score has something to be a fraction of.
    best = sum(2 if r["exp"] == "true" else 1 for r in rows)
    print("  ceiling %d   (%.1f%% of available points)"
          % (best, 100.0 * total / best if best else 0.0))

    print("\n  by property")
    for p in ("no-data-race", "unreach-call", "valid-memsafety", "no-overflow"):
        sub = [r for r in rows if r["prop"] == p]
        if not sub:
            continue
        c = collections.Counter(r["cls"] for r in sub)
        print("    %-16s n=%-5d score=%-7d correct=%-5d wrong=%-4d unknown=%d"
              % (p, len(sub), sum(r["pts"] for r in sub), c["T"],
                 c["WRONG_TRUE"] + c["WRONG_FALSE"], c["U"]))

    wrong = [r for r in rows if r["cls"].startswith("WRONG")]
    if not wrong:
        print("\n  no wrong answers")
        return

    per_bm = collections.defaultdict(list)
    for r in wrong:
        per_bm[r["bm"]].append(r)

    print("\n  benchmarks ranked by points lost")
    ranked = sorted(per_bm.items(), key=lambda kv: sum(r["pts"] for r in kv[1]))
    for bm, rs in ranked:
        loss = sum(r["pts"] for r in rs)
        kinds = ", ".join("%s(%s->%s)" % (r["prop"], r["exp"], r["verdict"])
                          for r in sorted(rs, key=lambda x: x["pts"]))
        print("    %6d  %-44s %s" % (loss, bm[:44], kinds))

    print("\n  wrong answers by kind")
    mt = sum(1 for r in wrong if r["cls"] == "WRONG_TRUE")
    fa = sum(1 for r in wrong if r["cls"] == "WRONG_FALSE")
    print("    missed bugs  %3d  x -32 = %d" % (mt, -32 * mt))
    print("    false alarms %3d  x -16 = %d" % (fa, -16 * fa))

    print("\n  slowest correct answers (where the time goes)")
    for r in sorted((r for r in rows if r["cls"] == "T"),
                    key=lambda x: -x["ms"])[:10]:
        print("    %7.1fs  %-16s %s" % (r["ms"] / 1000.0, r["prop"], r["bm"][:46]))


def main():
    a = sys.argv[1]
    rows = load(a)
    report(rows, os.path.basename(a))

    if len(sys.argv) > 2:
        b = sys.argv[2]
        rows_b = load(b)
        print()
        report(rows_b, os.path.basename(b))

        ka = {(r["prop"], r["bm"]): r for r in rows}
        kb = {(r["prop"], r["bm"]): r for r in rows_b}
        both = set(ka) & set(kb)
        delta = sum(kb[k]["pts"] - ka[k]["pts"] for k in both)
        print("\n## %s vs %s, on the %d pairs both ran"
              % (os.path.basename(b), os.path.basename(a), len(both)))
        print("  net %+d points" % delta)
        moved = [(kb[k]["pts"] - ka[k]["pts"], k) for k in both
                 if kb[k]["pts"] != ka[k]["pts"]]
        for d, k in sorted(moved):
            print("    %+5d  %-16s %-44s %s -> %s"
                  % (d, k[0], k[1][:44], ka[k]["verdict"], kb[k]["verdict"]))


main()
