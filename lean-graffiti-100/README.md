# Graffiti (WOWII) Conjecture 100: a Lean 4 proof

**Statement** (DeLaVina, *Written on the Wall II*, Conjecture 100, listed as open):
for every connected graph `G` on at least two vertices,

    α(G) ≤ ⌈( max_v l(v) + ½ · ‖deg(Ḡ)‖₂ ) / 2⌉

- `α(G)` is the independence number.
- `l(v)` is the independence number of the subgraph induced by the neighbourhood of `v`.
- `‖deg(Ḡ)‖₂ = √(Σ_v deg_Ḡ(v)²)` is the "length" of the complement graph.

`GraphConjecture100.lean` is DeepMind's
[`formal-conjectures`](https://github.com/google-deepmind/formal-conjectures) file
`FormalConjectures/WrittenOnTheWallII/GraphConjecture100.lean`. Its `sorry` is
replaced by a complete proof. The statement is unchanged; only the category
moves from `research open` to `research solved`. `formal-conjectures.patch` is the
same change as a diff against upstream commit `b3f26411f06b0b0ec1923da80b62585f23288d39`.
`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.

## Proof sketch

Let `I` be a maximum independent set (`|I| = a`), `O` its complement (`|O| = m`),
`K = max_v l(v)`, and let `y(w) = |N(w) ∩ I|` for `w ∈ O`.

1. `N(w) ∩ I` is independent inside `N(w)`, so `y(w) ≤ l(w) ≤ K`.
2. `G` is connected and nontrivial, so every `u ∈ I` has a neighbour, and all of
   them lie in `O`. Double counting the edges `E` between `I` and `O` gives
   `a ≤ E ≤ K·m`.
3. Complement degrees:
   - for `u ∈ I`, `deg_Ḡ(u) ≥ (a−1) + (m − deg(u))`;
   - for `w ∈ O`, `deg_Ḡ(w) ≥ a − y(w)`.
4. With `S = Σ deg_Ḡ²`:
   - If `K ≥ a`, then `S ≥ a(a−1)² > 4(2a−2−K)²` (whenever `2a−2−K ≥ 0`).
   - If `K < a`, let `t = a−K`. Then `S ≥ a(a−1)² + (2a−2+t)·t·m`, and with `Km ≥ a`,
     `K·S − 4K(2a−2−K)² ≥ P(K,t)`, where

         P(k,t) = k(k³−6k²+17k−16) + tk(3k²−18k+31) + t²(3k²−13k−2) + t³(k+3) > 0

     for all integers `k ≥ 1`, `t ≥ 1`. Each term is positive for `k ≥ 5`; for
     `k ≤ 4` the polynomial is an explicit cubic in `t`.
5. So `√S > 2(2a−2−K)`, i.e. `(K + √S/2)/2 > a − 1`, and the ceiling is at least `a`.

## Checking it

```sh
git clone https://github.com/google-deepmind/formal-conjectures && cd formal-conjectures
git checkout b3f26411f06b0b0ec1923da80b62585f23288d39
git apply ../formal-conjectures.patch
lake exe cache get
lake build FormalConjectures.WrittenOnTheWallII.GraphConjecture100
```

`brute_force_check.py` was used beforehand to test this and five other open WOWII
conjectures (19, 40, 61, 133, 198a) on all connected graphs with at most 9 vertices.
No counterexamples were found (it needs `networkx` and nauty's `geng`).

Caveat: no literature search has been done to check whether this conjecture was
resolved after WOWII listed it as open.
