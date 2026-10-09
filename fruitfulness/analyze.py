"""Fruitfulness measures on the Mathlib constant graph, compared with human-curated labels.

Input: data/graph.tsv (from Export.lean), data/labels.json (from Mathlib's docs/*.yaml).
Every named constant (definition or theorem) is treated as a named concept; its body is
what naming it saves us from writing out at each use.

Measures for a named constant c:
  s(c)  own size: DAG size of its body (at least 1)
  k(c)  direct uses: number of constants whose body or statement cites c
  LV(c) local value  (k-1)(s-1)-1: exact symbols saved by naming c (Fruitfulness.naming_saves)
  U(c)  unfolded size: s(c) + sum of U over cited constants (everything re-proved in place)
  depth log10 U(c) - log10 s(c): how much hidden work c rests on
"""
import json, math, re, sys
from collections import defaultdict

GRAPH = sys.argv[1] if len(sys.argv) > 1 else "data/graph.tsv"

names, kind, mod, size = [], [], [], []
idx = {}
raw_deps = []
with open(GRAPH) as f:
    for line in f:
        parts = line.rstrip("\n").split("\t")
        if len(parts) < 6:
            continue
        n, kd, md, objs, vd, td = parts
        idx[n] = len(names)
        names.append(n); kind.append(kd); mod.append(md); size.append(max(1, int(objs)))
        raw_deps.append((vd, td))
N = len(names)
deps = []
for i, (vd, td) in enumerate(raw_deps):
    ds = set()
    for x in (vd.split() + td.split()):
        j = idx.get(x)
        if j is not None and j != i:
            ds.add(j)
    deps.append(list(ds))
del raw_deps
print(f"{N} constants, {sum(map(len, deps))} edges")

# Topological order (dependencies first); edges closing a cycle (unsafe/partial defs) are dropped.
order, state = [], bytearray(N)  # 0 new, 1 on stack, 2 done
dropped = 0
for r in range(N):
    if state[r]:
        continue
    stack = [(r, 0)]
    state[r] = 1
    while stack:
        v, p = stack[-1]
        if p < len(deps[v]):
            stack[-1] = (v, p + 1)
            w = deps[v][p]
            if state[w] == 0:
                state[w] = 1
                stack.append((w, 0))
            elif state[w] == 1:
                deps[v][p] = -1
                dropped += 1
        else:
            state[v] = 2
            order.append(v)
            stack.pop()
for v in range(N):
    deps[v] = [w for w in deps[v] if w >= 0]
print(f"dropped {dropped} cycle edges")

k = [0] * N
for v in range(N):
    for w in deps[v]:
        k[w] += 1

# Unfolded size, kept in log10 (values reach far beyond float range).
logU = [0.0] * N
for v in order:
    terms = [math.log10(size[v])] + [logU[w] for w in deps[v]]
    m = max(terms)
    logU[v] = m + math.log10(sum(10 ** (t - m) for t in terms))

INTERNAL = re.compile(r"(^_|\._|\.proof_|\.match_|\.eq_\d+$|\.eq_def$|\.injEq$|\.inj$|"
                      r"\.sizeOf_spec$|\.rec$|\.recOn$|\.casesOn$|\.noConfusion|\.below$|"
                      r"\.brecOn$|\.binductionOn$|\.ibelow$|\.ctorIdx|_def$|\.mk\.|\.ext_iff$|"
                      r"\._simp|_aux|\.induct$|\.go\b)")
def visible(i):
    return mod[i].startswith("Mathlib") and not INTERNAL.search(names[i]) \
        and kind[i] in ("thm", "def", "ind")

labels = json.load(open("data/labels.json"))
FAMOUS = {n for n, v in labels.items() if any(s in ("100", "1000") for s, _ in v)}
CURRIC = {n for n, v in labels.items() if any(s in ("undergrad", "overview") for s, _ in v)}
SURNAMES = """abel archimedes banach bernoulli bezout bolzano borel cantor cauchy cayley
chebyshev chinese dedekind dirichlet euclid euler fermat fourier frobenius galois gauss
gram hahn hall hausdorff heine hensel hilbert holder jacobi jensen jordan konig kronecker
lagrange laplace lebesgue legendre leibniz liouville markov minkowski mobius noether
pascal peano poincare pythagoras ramsey riemann riesz rolle schroder bernstein schur
schwarz stokes sylow taylor tychonoff urysohn vandermonde vitali weierstrass wilson
young zorn baire banach steinhaus krull nakayama sard fubini tonelli kuratowski cramer
dickson erdos hilbert gelfand stone wedderburn burnside zsigmondy ostrowski""".split()
SURN = re.compile(r"(^|[._])(" + "|".join(SURNAMES) + r")($|[._])", re.I)
EPON = {names[i] for i in range(N) if visible(i) and SURN.search(names[i])}

vis = [i for i in range(N) if visible(i)]
print(f"{len(vis)} visible Mathlib constants; labelled: famous "
      f"{sum(names[i] in FAMOUS for i in vis)}, curriculum {sum(names[i] in CURRIC for i in vis)}, "
      f"eponymous {len(EPON)}")

def LV(i): return (k[i] - 1) * (size[i] - 1) - 1
def slv(i):  # signed log of local value
    x = LV(i); return math.copysign(math.log10(1 + abs(x)), x)
MEASURES = {
    "k (direct uses)": lambda i: k[i],
    "LV (local value)": slv,
    "s (own size)": lambda i: math.log10(size[i]),
    "U (unfolded size)": lambda i: logU[i],
    "depth (U/s)": lambda i: logU[i] - math.log10(size[i]),
}

def auc(pos, neg):
    """Probability a random positive outscores a random negative (ties count 1/2)."""
    allv = sorted([(x, 1) for x in pos] + [(x, 0) for x in neg])
    r, i, rank_sum = 1, 0, 0.0
    while i < len(allv):
        j = i
        while j < len(allv) and allv[j][0] == allv[i][0]:
            j += 1
        avg = (r + r + (j - i) - 1) / 2
        rank_sum += avg * sum(1 for t in range(i, j) if allv[t][1])
        r += j - i; i = j
    P, Q = len(pos), len(neg)
    return (rank_sum - P * (P + 1) / 2) / (P * Q) if P and Q else float("nan")

out = {"N": N, "visible": len(vis), "auc": {}}
for lname, L in [("famous (100/1000)", FAMOUS), ("curriculum (undergrad/overview)", CURRIC),
                 ("eponymous", EPON)]:
    for kd in ("thm", "def", "all"):
        pool = [i for i in vis if kd == "all" or kind[i] == kd or (kd == "def" and kind[i] == "ind")]
        pos = [i for i in pool if names[i] in L]
        neg = [i for i in pool if names[i] not in L]
        if len(pos) < 5:
            continue
        row = {m: round(auc([f(i) for i in pos], [f(i) for i in neg]), 3) for m, f in MEASURES.items()}
        row["n_pos"] = len(pos)
        out["auc"][f"{lname} | {kd}"] = row
        print(f"\n{lname} | {kd}: n+={len(pos)} n-={len(neg)}")
        for m, a in row.items():
            if m != "n_pos":
                print(f"   AUC {m:20s} {a}")

def top(key, pool, n=40):
    return [(names[i], kind[i], k[i], size[i], LV(i), round(logU[i], 1)) for i in
            sorted(pool, key=key, reverse=True)[:n]]
thms = [i for i in vis if kind[i] == "thm"]
defs = [i for i in vis if kind[i] in ("def", "ind")]
out["top_LV_thm"] = top(LV, thms)
out["top_LV_def"] = top(LV, defs)
out["top_k_thm"] = top(lambda i: k[i], thms)
out["unsung_thm"] = top(LV, [i for i in thms if names[i] not in FAMOUS | CURRIC | EPON])
out["deepest_thm"] = top(lambda i: logU[i], thms)
fam = [i for i in vis if names[i] in FAMOUS]
out["famous"] = sorted([(names[i], kind[i], k[i], size[i], LV(i), round(logU[i], 1)) for i in fam],
                       key=lambda t: t[2])
out["famous_unused_frac"] = round(sum(k[i] == 0 for i in fam) / max(1, len(fam)), 3)
out["all_thm_unused_frac"] = round(sum(k[i] == 0 for i in thms) / len(thms), 3)

# Heavy tail of direct uses: complementary CDF on a log grid.
ks = sorted((k[i] for i in vis), reverse=True)
ccdf = []
for t in [1, 2, 5, 10, 20, 50, 100, 200, 500, 1000, 2000, 5000, 10000]:
    c = sum(1 for x in ks if x >= t)
    ccdf.append((t, c))
out["ccdf_k"] = ccdf
# Growth of unfolded size with dependency height.
height = [0] * N
for v in order:
    height[v] = 1 + max((height[w] for w in deps[v]), default=0)
byh = defaultdict(list)
for i in vis:
    byh[height[i]].append(logU[i])
out["logU_by_height"] = [(h, len(v), round(sum(v) / len(v), 2), round(max(v), 1))
                         for h, v in sorted(byh.items())]
out["max_height"] = max(height)
json.dump(out, open("data/results.json", "w"), indent=1)
print("\nfamous with k=0:", out["famous_unused_frac"], " all thms with k=0:", out["all_thm_unused_frac"])
print("max height", out["max_height"])

# Per-constant table of the visible Mathlib constants, for follow-up analysis.
import csv
with open("data/visible.tsv", "w", newline="") as f:
    w = csv.writer(f, delimiter="\t")
    w.writerow(["name", "kind", "module", "s", "k", "log10U", "height"])
    for i in vis:
        w.writerow([names[i], kind[i], mod[i], size[i], k[i], round(logU[i], 3), height[i]])
