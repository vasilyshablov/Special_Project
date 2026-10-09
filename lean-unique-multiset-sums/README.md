# Unique multiset sums: |G| ≥ 2^(n-1) (independent Lean proof)

**Setting.** This is Open Problem 4 of J. A. R. Fonollosa, *Minimum modulus for the unique
multiset-sum problem* (arXiv:2607.08366). Elements g₁,…,gₙ of a finite abelian group G have
*unique multiset sums* if the all-ones multiset is the only size-n multiset drawn from them
whose sum equals g₁+…+gₙ.

**Result (already known, see below).** Such a family forces |G| ≥ 2ⁿ⁻¹. This is tight:
(ℤ₂)ⁿ⁻¹ with (0, e₁, …, eₙ₋₁) attains it (Fonollosa, Prop. 2). In particular every valid set
of n residues mod N has N ≥ 2ⁿ⁻¹.

**Proof (anchor argument).** Fix an index j. For S ⊆ [n]∖{j}, the 2ⁿ⁻¹ elements
t + Σ_{i∈S}(g_j − g_i) are pairwise distinct. Suppose two coincide for S ≠ T with
|S| ≥ |T|. Then 𝟏 − 𝟏_S + 𝟏_T + (|S|−|T|)·e_j is a second size-n multiset with sum t,
which contradicts uniqueness.

**Lean.** `AbelianLowerBound.lean` (about 90 lines, built inside google-deepmind/formal-conjectures
at commit b3f2641) proves two theorems:

- `two_pow_le_card`: the general abelian-group bound.
- `two_pow_le_of_isValidMod`: the cyclic corollary, stated against formal-conjectures' own
  `IsValidMod`.

`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.

## Prior work: this is NOT the first proof

The question had already been resolved by **Michael Inal**, *The Exact Minimum Order for
Unique Multiset Sums in Finite Abelian Groups*, OSF preprint, doi:10.17605/OSF.IO/C58Q9
(2026). It is formalized, together with a classification of the equality cases, in
`MinModulus/AbelianMin.lean` of the author's repository
<https://github.com/jarfo/min-modulus>. We found that only after completing this proof.
Our argument was found independently. Its only claim is brevity.

Fonollosa's main Conjecture 1 (the cyclic minimum is exactly 2ⁿ − 2^⌊log₂ n⌋) remains open.
The bound here is about a factor of 2 below it.
