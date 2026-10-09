"""Statistics and figure data for the paper, from data/visible.tsv and data/flags.tsv.

Glue is classified structurally (instance declarations and structure projections), not
by name. Writes data/paper_stats.json and data/fig_*.dat (pgfplots tables)."""
import csv, json, math, re
from collections import defaultdict

flags = {}
with open("data/flags.tsv") as f:
    for line in f:
        n, inst, proj, cls, tobjs = line.rstrip("\n").split("\t")
        flags[n] = (inst == "1", proj == "1", cls == "1", max(1, int(tobjs)))
rows = list(csv.DictReader(open("data/visible.tsv"), delimiter="\t"))
for r in rows:
    r["s"] = int(r["s"]); r["k"] = int(r["k"]); r["U"] = float(r["log10U"]); r["h"] = int(r["height"])
    r["kd"] = "def" if r["kind"] in ("def", "ind") else r["kind"]
    inst, proj, cls, t = flags.get(r["name"], (False, False, False, 1))
    r["glue"] = inst or proj
    r["cls"] = cls
    r["t"] = t  # statement size
lab = json.load(open("data/labels.json"))
FAM = {n for n, v in lab.items() if any(s in ("100", "1000") for s, _ in v)}
CUR = {n for n, v in lab.items() if any(s in ("undergrad", "overview") for s, _ in v)}
out = {}

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

def rank(x):
    o = sorted(range(len(x)), key=lambda i: x[i]); rk = [0.0] * len(x); i = 0
    while i < len(o):
        j = i
        while j < len(o) and x[o[j]] == x[o[i]]:
            j += 1
        for t in range(i, j):
            rk[o[t]] = (i + j - 1) / 2
        i = j
    return rk

def spearman(a, b):
    ra, rb = rank(a), rank(b); n = len(a); ma = sum(ra) / n; mb = sum(rb) / n
    c = sum((x - ma) * (y - mb) for x, y in zip(ra, rb))
    return c / math.sqrt(sum((x - ma) ** 2 for x in ra) * sum((y - mb) ** 2 for y in rb))

# 1. Glue layer
tot_k = sum(r["k"] for r in rows)
glue_k = sum(r["k"] for r in rows if r["glue"])
top100 = sorted(rows, key=lambda r: -r["k"])[:100]
out["glue"] = {
    "n_glue": sum(r["glue"] for r in rows), "n": len(rows),
    "share_of_constants": round(sum(r["glue"] for r in rows) / len(rows), 3),
    "share_of_citations": round(glue_k / tot_k, 3),
    "share_of_top100": sum(r["glue"] for r in top100) / 100,
    "labelled_glue": sum(r["glue"] for r in rows if r["name"] in FAM | CUR),
    "labelled": sum(1 for r in rows if r["name"] in FAM | CUR),
}
clean = [r for r in rows if not r["glue"]]

# 2. Two axes of taste, structural glue removed, with depth relative to statement size
bymod = defaultdict(list)
for r in clean:
    bymod[(r["module"], r["kd"])].append(r)
M = {"reuse k": lambda r: r["k"],
     "unfolded U": lambda r: r["U"],
     "depth U/statement": lambda r: r["U"] - math.log10(r["t"]),
     "statement size": lambda r: math.log10(r["t"])}
out["auc"] = {}
for lname, L in (("famous", FAM), ("curriculum", CUR)):
    for kd in ("thm", "def"):
        pool = [r for r in clean if r["kd"] == kd]
        pos = [r for r in pool if r["name"] in L]; neg = [r for r in pool if r["name"] not in L]
        if len(pos) < 10:
            continue
        row = {"n": len(pos)}
        for m, f in M.items():
            g = auc([f(r) for r in pos], [f(r) for r in neg])
            wins, tot = 0.0, 0
            for p in pos:
                peers = [q for q in bymod[(p["module"], kd)] if q["name"] not in L]
                if peers:
                    fp = f(p)
                    wins += sum(1 if fp > f(q) else 0.5 if fp == f(q) else 0 for q in peers) / len(peers)
                    tot += 1
            row[m] = [round(g, 3), round(wins / tot, 3)]
        out["auc"][f"{lname}|{kd}"] = row

# 3. Top concepts, glue removed
out["top_def"] = [(r["name"], r["k"]) for r in sorted([r for r in clean if r["kd"] == "def"],
                                                      key=lambda r: -r["k"])[:30]]
out["top_thm"] = [(r["name"], r["k"]) for r in sorted([r for r in clean if r["kd"] == "thm"],
                                                      key=lambda r: -r["k"])[:30]]

# 4. Heavy tail: discrete power-law MLE (Clauset et al. approximation) for several k_min
ks = [r["k"] for r in rows if r["k"] > 0]
out["tail"] = {}
for kmin in (10, 30, 100):
    t = [x for x in ks if x >= kmin]
    alpha = 1 + len(t) / sum(math.log(x / (kmin - 0.5)) for x in t)
    out["tail"][kmin] = {"n": len(t), "alpha_pdf": round(alpha, 3)}
with open("data/fig_ccdf.dat", "w") as f:
    f.write("k ccdf\n")
    sk = sorted(ks)
    n = len(sk)
    grid = sorted({int(round(10 ** (e / 20))) for e in range(0, 101)})
    import bisect
    for g in grid:
        c = n - bisect.bisect_left(sk, g)
        if c > 0:
            f.write(f"{g} {c}\n")

# 5. Law of abbreviation (glue removed)
out["abbrev"] = {}
for kd in ("thm", "def"):
    P = [r for r in clean if r["kd"] == kd]
    k = [r["k"] for r in P]
    out["abbrev"][kd] = {
        "rho_name_len": round(spearman(k, [len(r["name"].split(".")[-1]) for r in P]), 3),
        "rho_statement": round(spearman(k, [r["t"] for r in P]), 3),
        "rho_body": round(spearman(k, [r["s"] for r in P]), 3),
        "mean_name_len_by_decade": {},
    }
    b = defaultdict(list)
    for r in P:
        b[0 if r["k"] == 0 else int(math.log10(r["k"])) + 1].append(len(r["name"].split(".")[-1]))
    out["abbrev"][kd]["mean_name_len_by_decade"] = {t: [len(v), round(sum(v) / len(v), 1)]
                                                    for t, v in sorted(b.items())}

# 6. Growth law figure data
byh = defaultdict(list)
for r in rows:
    byh[r["h"]].append(r["U"])
with open("data/fig_growth.dat", "w") as f:
    f.write("h mean max n\n")
    for h in sorted(byh):
        v = byh[h]
        f.write(f"{h} {sum(v)/len(v):.3f} {max(v):.3f} {len(v)}\n")

json.dump(out, open("data/paper_stats.json", "w"), indent=1)
print(json.dumps({k: out[k] for k in ("glue", "auc", "tail", "abbrev")}, indent=1))
print("top defs:", [n for n, _ in out["top_def"][:20]])
print("top thms:", [n for n, _ in out["top_thm"][:20]])
