"""Independent checker for proof_tree.json (written separately from the search).
Claim: no graph has min degree >= 3, diameter <= 3, and no cycle of length 4 or 8."""
import json, sys, networkx as nx
from collections import deque
sys.setrecursionlimit(100000)
tree = json.load(open(sys.argv[1]))
stats = {"nodes": 0, "dead": 0}

def bfs_dist(G, a, b):
    seen = {a: 0}; q = deque([a])
    while q:
        x = q.popleft()
        for y in G[x]:
            if y not in seen: seen[y] = seen[x] + 1; q.append(y)
    return seen.get(b, 10**9)

def has_C4_or_C8(G):
    for c in nx.simple_cycles(G, length_bound=8):
        if len(c) in (4, 8): return True
    return False

def witnesses(G, req):
    """All ways the requirement can be met in a supergraph, up to naming of fresh vertices.
    Returned as frozensets of edges, fresh vertices labelled n, n+1 in order of appearance along the path."""
    n = G.number_of_nodes(); out = set()
    if req[0] == "deg":
        v = req[1]
        for u in range(n):
            if u != v and not G.has_edge(u, v): out.add(frozenset([frozenset((v, u))]))
        out.add(frozenset([frozenset((v, n))]))
    else:
        a, b = req[1], req[2]
        for k in (1, 2, 3):                      # path length
            def build(prefix, fresh):
                if len(prefix) == k - 1:
                    pts = [a] + prefix + [b]
                    out.add(frozenset(frozenset((pts[i], pts[i+1])) for i in range(k))); return
                for x in list(range(n)) + [fresh]:
                    if x in (a, b) or x in prefix: continue
                    build(prefix + [x], fresh + 1 if x == fresh else fresh)
            build([], n)
    return out

def check(edges, nverts, node):
    stats["nodes"] += 1
    G = nx.Graph(); G.add_nodes_from(range(nverts)); G.add_edges_from(edges)
    req = node["req"]
    if req[0] == "deg": assert G.degree(req[1]) < 3, "deg requirement not violated"
    else: assert bfs_dist(G, req[1], req[2]) > 3, "dist requirement not violated"
    have = {}
    for br in node["branches"]:
        key = frozenset(frozenset(e) for e in br["add"]); have[key] = br
    need = witnesses(G, req)
    # edges already present are harmless: normalise by removing them from keys of 'have'
    norm = {}
    for key, br in have.items():
        norm[frozenset(e for e in key if not G.has_edge(*tuple(e)))] = br
    for w in need:
        wn = frozenset(e for e in w if not G.has_edge(*tuple(e)))
        assert wn in norm, ("uncovered witness", req, sorted(map(sorted, w)))
        br = norm[wn]
        E2 = list(edges) + [tuple(e) for e in wn]
        nv2 = max([nverts] + [max(e) + 1 for e in E2])
        if br.get("dead"):
            H = nx.Graph(); H.add_nodes_from(range(nv2)); H.add_edges_from(E2)
            assert has_C4_or_C8(H), "dead branch without C4/C8"
            stats["dead"] += 1
        else:
            check(E2, nv2, br["sub"])

check([], 1, tree)
print("VERIFIED", stats)
