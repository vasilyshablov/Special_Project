# Erdős–Gyárfás conjecture for graphs of diameter at most 3

**Theorem.** Every graph, finite or infinite, with minimum degree ≥ 3 and diameter ≤ 3 contains a
cycle of length 4 or 8. Hence the Erdős–Gyárfás conjecture (Erdős problem #64) holds for all graphs of
diameter ≤ 3.

This extends Carr's diameter-2 result (arXiv:2508.19302). As of 10 Oct 2026, no prior result on
diameter 3 was found on erdosproblems.com, on arXiv (2024–2026), or in `github.com/openai/math`.

## Proof (computer-assisted)

The proof is an exhaustive embedding search.
1. Assume a counterexample G.
2. Grow a finite graph H embedded in G.
3. At each step, branch over every way a missing neighbour or a path of length ≤ 3 can attach to H.
4. Every branch ends with a 4-cycle or 8-cycle in H, and hence in G.

The soundness argument is Lemma 2 of `paper.pdf`.

| | internal nodes | dead branches | max \|V(H)\| | time |
|---|---|---|---|---|
| diameter 2 (reproduces Carr) | 38 | 180 | 8 | < 1 s |
| **diameter 3 (new)** | **3,169** | **183,943** | **15** | 6 s |

- `search.py`: builds the proof tree.
  `python3 search.py 3 4,8 3 18 --tree proof_tree.json`
- `checker.py`: independent verifier that shares no code with the search. It re-checks every
  requirement, regenerates all witnesses, and confirms every dead branch with networkx's cycle
  enumerator. Run `python3 checker.py proof_tree.json` (≈ 35 s); the output is
  `VERIFIED {'nodes': 3169, 'dead': 183943}`.
- `proof_tree.json.gz`: the certificate (394 KB; unzip before checking).
- `paper.pdf`: write-up. It includes a short human proof of the bipartite case and the control
  experiments:
  - with only C4 forbidden, the search finds a real 10-vertex graph;
  - with min degree 2, it finds a triangle;
  - with diameter 4 and only C4, C8 forbidden, it does not terminate.
