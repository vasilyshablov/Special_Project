# What is fruitfulness? Measuring it on all of Mathlib

**Paper:** [`paper/paper.pdf`](paper/paper.pdf), *Fruitfulness as Compression*, 10 pages.
**Working notes:** [`notes/thoughts.pdf`](notes/thoughts.pdf).

This started from a debate claim: AI can't handle open "why / what is" questions, because
there is nothing to optimize. So we posed one such question ourselves:

> **What is the fruitfulness of a mathematical idea, and can it be measured?**

Our answer is a precise definition, theorems about it proved in Lean, a measurement over
all 771,129 constants of Mathlib, a test against human judgments of importance, and
falsifiable conjectures.

## 1. The definition: a concept is a compression

Naming a concept (a definition or a lemma) means writing its body once and citing it
afterwards. The *unfolded size* of a result is the size of its proof with every cited
result re-proved in place:

    unfold(i) = size(i) + Σ_{j cited by i} unfold(j)

The fruitfulness of a concept is what naming it saves.

## 2. Theorems (Lean 4 + Mathlib, `Fruitfulness.lean`, no `sorry`)

Every theorem below uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

| Lean name | Statement |
|---|---|
| `naming_saves` | Naming a sub-proof of size `b` used `k` times saves exactly `(k-1)(b-1) - 1` symbols. |
| `naming_pays_iff`, `naming_pays_of` | So naming pays off iff `(k-1)(b-1) > 1`. It always pays when `k ≥ 2` and `b ≥ 3`. |
| `naming_once` | A concept used only once never pays: naming it costs one extra symbol. |
| `Library.unfold_le` | With own sizes `≤ S` and `≤ d` citations per result, `unfold i ≤ S (d+1)^(i+1)`. |
| `Library.unfold_le_two_pow` | Sharper, and independent of `d`: `unfold i ≤ S · 2^i`. Unfolding at most doubles per result. |
| `completeLib_unfold` | The bound is attained: if every result cites all earlier ones, `unfold i = 2^i`. |
| `fibLib_unfold`, `fibLib_unfold_ge` | If each result cites the two before it, `unfold i = Fib(i+3) - 1 ≥ 2^(i/2)`. That is golden-ratio growth from a library of linear size. |

So named concepts can make mathematics exponentially shorter, never more than exponentially
shorter, and the exact value of a single concept is the explicit number `(k-1)(b-1) - 1`.

## 3. Measurement on Mathlib

`Export.lean` loads all of Mathlib, including proof bodies, and writes out every
constant. For each one it records the size of its body and the constants it cites.

- **Graph:** 771,129 constants and 20.4 M citation edges.
- **Analysed:** 315,085 user-facing Mathlib constants.
- **Longest citation chain:** 362 levels.

For each constant `c` we measure:
- `k`: its direct uses;
- `s`: its own size;
- `U`: its unfolded size;
- its height in the dependency DAG.

### Finding A: fully unfolded, Mathlib does not fit in the universe

The largest unfolded proof is `CompletelyPositiveMap.map_cstarMatrix_nonneg`, at about
10^65.6 symbols. For scale, the observable universe has about 10^80 atoms.

Unfolded size grows exponentially with dependency height:

    log10 U ≈ 1.22 + 0.189 · height     (R² = 0.979 over 315k constants)

That is a factor of about **1.5 per level**: 1.45, 1.64 and 1.41 on the three thirds of
the height range. The idealised Fibonacci library from the Lean file grows by the golden
ratio, 1.618, per result.

**Consequence for "what is a human?":** named concepts are not a crutch for human working
memory. Any finite mind needs them, AI included, because otherwise the objects are
physically too large to write down. The open question is *which* concepts get named.

### Finding B: the most-reused concepts are the textbook ones

After removing typeclass plumbing (instance and coercion lemmas, about 12% of constants),
the most-used definitions are:

> `DFunLike.coe` (applying a function), `Set`, `Category`, `Quiver.Hom` (morphisms),
> `Functor`, `TopologicalSpace`, `Real`, `Module`, `CommRing`, `Finset`, `Semiring`,
> `RingHom`, `AddCommGroup`, `Algebra`, `LinearMap`, `Equiv`, ...

The most-used theorems are the axioms of algebra and order:

> `mul_one`, `add_zero`, `le_trans`, `zero_add`, `one_mul`, `mul_comm`, `Set.ext`,
> `le_antisymm`, `mul_assoc`, `Functor.map_comp`, ...

Nobody told the measure what is fundamental. A pure reuse count rediscovers the first
chapter of every algebra and topology textbook.

The reuse distribution is heavy-tailed:
- 215k constants are used at least once;
- 8,090 are used at least 100 times;
- 165 are used at least 10,000 times;
- the tail is roughly `P(k ≥ x) ∝ x^-0.8`.

### Finding C: humans have two kinds of taste, and each one is computable

The human labels come from Mathlib's own curated lists, all written by humans:
- Freek Wiedijk's *100 theorems* and the *1000+ theorems* project: 294 declarations, here
  called **famous**;
- the undergraduate curriculum and the Mathlib overview: 686 declarations, here called
  **curriculum**.

For each label set we ask whether a mechanical measure ranks the labelled constants above
the rest. The score is AUC, where 0.5 means chance and 1.0 means perfect. We give it two
ways:
- **global:** against all other constants of the same kind;
- **same-file:** only against peers in the same source file, to control for "advanced
  files contain deeper things".

| Human label | Reuse `k` | Depth `U` | Leverage `k/s` |
|---|---|---|---|
| curriculum **definitions** (n=435) | **0.87** / **0.86** | 0.47 / 0.36 | 0.84 / 0.84 |
| curriculum theorems (n=219) | 0.57 / 0.59 | **0.82** / **0.67** | 0.32 / 0.53 |
| famous theorems (n=266) | 0.54 / 0.55 | **0.78** / **0.66** | 0.30 / 0.49 |

(Each cell is global AUC / same-file win rate. Plumbing removed. Source: `robustness.py`.)

So humans call a **concept** important when it is *reused* a lot and is small. They call
a **theorem** important when it is *deep*, i.e. rests on a lot. Whether a famous theorem
gets used much afterwards is close to irrelevant (0.54). And 28.6% of famous theorems are
never cited anywhere else in Mathlib.

## 4. Conjectures (falsifiable, open)

1. **Growth law.** As Mathlib keeps growing, the per-level unfolding factor will stay
   between 1.4 and 1.7, and the fit stays at R² > 0.95. You can check this on any future
   Mathlib with `Export.lean` and `analyze.py`.
2. **Two-axis taste.** On other large formal libraries (Isabelle's AFP, Rocq's
   MathComp), human-curated concept lists are predicted by reuse, and famous-theorem lists
   by depth, both with AUC > 0.75. Reuse will not predict fame (AUC < 0.6).
3. **Concepts are forced, not chosen (Q1).** Strip the names from Mathlib's proofs and run
   automated library learning (compression-driven abstraction discovery). The top
   abstractions it recovers will substantially overlap with Finding B's list. If that
   holds, the core of human mathematical vocabulary is a compression optimum, not an
   artifact of the human brain.
4. ~~Sharp bound for bounded citation.~~ **Now proved in Lean:** `Library.unfold_le_tb`
   and `windowLib_unfold`. With at most `d` citations, `unfold i ≤ S · T_d(i)`, where
   `T_d(i) = 1 + T_d(i-1) + ... + T_d(i-d)`, and this is attained. The growth rate is
   the `d`-bonacci constant.
5. **Glue share** (added after the structural glue classification). Instance declarations
   and structure projections are 12.3% of constants but receive 59.5% of all citations,
   including 77 of the top 100. That is the profile of function words in language and of
   currency metabolites in metabolism. Conjecture: this holds in any mature formal library
   with typeclass-style inference.

## 5. What this says about "AI can't do open questions"

- **The question we posed was open-ended.** "What is fruitfulness?" is not a yes/no task.
- **It led to new things:** a definition, Lean theorems, a law that fits Mathlib with
  R² = 0.98, and falsifiable conjectures.
- **It produced a "nothing to optimize" counterexample.** The reuse measure recovers
  human concept taste at AUC 0.87, and the depth measure recovers theorem taste at about
  0.8. So there *is* something to optimize. It is delayed, as Lobachevsky's case shows,
  because these numbers exist only after a library has been built on top of an idea. But
  it is computable.

**Honest limits:**
- **The labels are biased.** They are what formalizers chose to record.
- **The plumbing filter is a name heuristic.**
- **`U` counts each citation once per citing result.** It does not track the number of
  occurrences inside a proof.
- **AUC around 0.8 is strong but not perfect**, and part of human taste remains
  unexplained.

## Reproduce

```bash
# in a Lean project that depends on Mathlib (here: formal-conjectures)
lake env lean --run Export.lean Mathlib data/graph.tsv   # ~11 min, ~660 MB
python3 analyze.py data/graph.tsv                        # ~1 min
python3 robustness.py
lake env lean Fruitfulness.lean                          # the theorems
```

`data/labels.json` is extracted from Mathlib's `docs/{100,1000,undergrad,overview}.yaml`.
The two large generated files, `graph.tsv` and `visible.tsv`, are not committed.
