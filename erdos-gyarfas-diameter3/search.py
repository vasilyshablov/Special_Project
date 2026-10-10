"""Exhaustive embedding search for the Erdos-Gyarfas conjecture on graphs of small diameter.

Claim checked (defaults): no graph with minimum degree >= 3 and diameter <= 3 avoids cycles of
lengths 4 and 8.

Method. Suppose G is a counterexample. We grow a finite graph H together with an injective
embedding of H into G. At each step we pick a requirement that H violates but G satisfies:
  * ('deg', v):     deg_H(v) < MINDEG, so v has a further neighbour in G;
  * ('dist', a, b): dist_H(a, b) > D, so G has an a-b path of length 1..D.
We branch over every way the witness can sit relative to H: each new neighbour or path vertex is
either an existing vertex of H or a fresh one. A branch dies as soon as H contains a forbidden
cycle, because G would contain it too. If every branch dies, no counterexample exists.

Usage: python3 search.py [D=3] [FORB=4,8] [MINDEG=3] [MAXV=18] [--tree out.json]
"""
import sys, json
sys.setrecursionlimit(100000)
args = [a for a in sys.argv[1:] if not a.startswith("--")]
D = int(args[0]) if len(args) > 0 else 3
FORB = [int(x) for x in args[1].split(",")] if len(args) > 1 else [4, 8]
MINDEG = int(args[2]) if len(args) > 2 else 3
MAXV = int(args[3]) if len(args) > 3 else 18
TREE = sys.argv[sys.argv.index("--tree") + 1] if "--tree" in sys.argv else None

def cycle_through(adj, u, v, L):
    """Is there a cycle of length L through the edge uv?"""
    seen = {u, v}
    def dfs(x, k):
        if k == L - 2: return u in adj[x]
        for y in adj[x]:
            if y not in seen:
                seen.add(y)
                if dfs(y, k + 1): return True
                seen.discard(y)
        return False
    return dfs(v, 0)

def killed(adj, new_edges):
    return any(cycle_through(adj, u, v, L) for (u, v) in new_edges for L in FORB)

def dist_from(adj, s):
    d = {s: 0}; frontier = [s]
    while frontier:
        nxt = []
        for x in frontier:
            for y in adj[x]:
                if y not in d: d[y] = d[x] + 1; nxt.append(y)
        frontier = nxt
    return d

def requirements(adj):
    n = len(adj)
    dist = []
    for a in range(n):
        d = dist_from(adj, a)
        dist += [('dist', a, b) for b in range(a + 1, n) if d.get(b, 10**9) > D]
    if dist: return dist                      # distance requirements first: they close cycles
    return [('deg', v) for v in range(n) if len(adj[v]) < MINDEG]

def witnesses(adj, req):
    n = len(adj); out = []
    if req[0] == 'deg':
        v = req[1]
        out = [[(v, u)] for u in range(n) if u != v and u not in adj[v]] + [[(v, n)]]
    else:
        a, b = req[1], req[2]
        def build(prefix, fresh, k):
            if len(prefix) == k - 1:
                pts = [a] + prefix + [b]
                out.append([(pts[i], pts[i + 1]) for i in range(k)]); return
            for x in list(range(n)) + [fresh]:
                if x in (a, b) or x in prefix: continue
                build(prefix + [x], fresh + 1 if x == fresh else fresh, k)
        for k in range(1, D + 1): build([], n, k)
    return out

def extend(adj, edges):
    adj2 = [set(s) for s in adj]; new = []
    for (u, v) in edges:
        while max(u, v) >= len(adj2): adj2.append(set())
        if v not in adj2[u]:
            adj2[u].add(v); adj2[v].add(u); new.append((u, v))
    return adj2, new

stats = {"nodes": 0, "dead": 0, "maxv": 0}

def solve(adj):
    """Return a proof tree (dict) if every branch dies, else raise with the open configuration."""
    stats["nodes"] += 1; stats["maxv"] = max(stats["maxv"], len(adj))
    reqs = requirements(adj)
    if not reqs: raise RuntimeError(("COUNTEREXAMPLE", [sorted(s) for s in adj]))
    best = None
    for r in reqs:                            # choose the requirement with fewest live branches
        kids = []
        for w in witnesses(adj, r):
            adj2, new = extend(adj, w)
            kids.append((w, adj2, killed(adj2, new)))
        live = sum(not k[2] for k in kids)
        if best is None or live < best[0]: best = (live, r, kids)
        if live <= 1: break
    _, r, kids = best
    node = {"req": list(r), "branches": []}
    for w, adj2, dead in kids:
        if dead:
            stats["dead"] += 1; node["branches"].append({"add": w, "dead": True})
        else:
            if len(adj2) > MAXV: raise RuntimeError(("SIZE LIMIT", len(adj2)))
            node["branches"].append({"add": w, "sub": solve(adj2)})
    return node

try:
    tree = solve([set()])
    print("PROVED: D=%d, forbidden cycles %s, min degree %d" % (D, FORB, MINDEG), stats)
    if TREE: json.dump(tree, open(TREE, "w"))
except RuntimeError as e:
    print("NOT PROVED:", e.args[0][0], e.args[0][1], stats)
