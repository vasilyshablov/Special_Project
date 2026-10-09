"""Robustness checks on data/visible.tsv: typeclass plumbing removed, and within-module
comparisons (a labelled constant against unlabelled constants of the same kind in the
same file), which controls for 'advanced files simply contain deeper results'."""
import csv, json, math, re
from collections import defaultdict
rows = list(csv.DictReader(open("data/visible.tsv"), delimiter="\t"))
for r in rows:
    r["s"] = int(r["s"]); r["k"] = int(r["k"]); r["U"] = float(r["log10U"])
    r["kd"] = "def" if r["kind"] in ("def", "ind") else r["kind"]
PLUMB = re.compile(r"(^|\.)inst|(^|\.)to[A-Z]|Class\b|_self$|smulCommClass|IsScalarTower|"
                   r"SMulCommClass|Mathlib\.(Tactic|Meta)|\.ids$")
rows = [r for r in rows if not PLUMB.search(r["name"])]
lab = json.load(open("data/labels.json"))
SETS = {"famous": {n for n, v in lab.items() if any(s in ("100", "1000") for s, _ in v)},
        "curriculum": {n for n, v in lab.items() if any(s in ("undergrad", "overview") for s, _ in v)}}
M = {"k": lambda r: r["k"], "U": lambda r: r["U"], "s": lambda r: math.log10(r["s"]),
     "leverage k/s": lambda r: math.log10(1 + r["k"]) - math.log10(r["s"])}

def auc(pos, neg):
    allv = sorted([(x, 1) for x in pos] + [(x, 0) for x in neg])
    rs, r, i = 0.0, 1, 0
    while i < len(allv):
        j = i
        while j < len(allv) and allv[j][0] == allv[i][0]:
            j += 1
        rs += (r + (j - i - 1) / 2) * sum(t[1] for t in allv[i:j]); r += j - i; i = j
    P, Q = len(pos), len(neg)
    return (rs - P * (P + 1) / 2) / (P * Q)

bymod = defaultdict(list)
for r in rows:
    bymod[(r["module"], r["kd"])].append(r)
res = {}
for lname, L in SETS.items():
    for kd in ("thm", "def"):
        pool = [r for r in rows if r["kd"] == kd]
        pos = [r for r in pool if r["name"] in L]; neg = [r for r in pool if r["name"] not in L]
        if len(pos) < 10:
            continue
        line = {}
        for m, f in M.items():
            g = auc([f(r) for r in pos], [f(r) for r in neg])
            # within-module: average over labelled constants of P(beats a same-file peer)
            wins, tot = 0.0, 0
            for p in pos:
                peers = [q for q in bymod[(p["module"], kd)] if q["name"] not in L]
                if not peers:
                    continue
                fp = f(p)
                wins += sum(1 if fp > f(q) else 0.5 if fp == f(q) else 0 for q in peers) / len(peers)
                tot += 1
            line[m] = (round(g, 3), round(wins / tot, 3) if tot else None)
        res[f"{lname}|{kd}"] = {"n": len(pos), **line}
        print(f"{lname:10s} {kd}: n={len(pos):4d}  " +
              "  ".join(f"{m}: {a}/{w}" for m, (a, w) in line.items()))
json.dump(res, open("data/robustness.json", "w"), indent=1)
print("(global AUC / within-module win rate; 0.5 = chance)")
