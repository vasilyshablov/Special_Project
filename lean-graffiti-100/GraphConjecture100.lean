/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 100

**Verbatim statement (WOWII #100, status O):**
> If G is a simple connected graph, then α(G) ≤ CEIL[(maximum of λ(v) + 0.5*length(Ḡ))/2]

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj100

The WOWII HTML uses `length(Ḡ)` (the bar denotes graph complement); the
extracted JSON in our private repo previously dropped the overline. The
formal statement below uses the Euclidean norm of the degree sequence of `Gᶜ`.

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definition of graph length

The WOWII definitions popup defines `length(H)` as the square root of the sum
of the squares of the vertex degrees. This is `degreeL2Norm H` in Lean.
Combined with the overline above, the inequality reads:
  `α(G) ≤ ⌈(max_v l(v) + 0.5 · degreeL2Norm(Gᶜ)) / 2⌉`
where `l(v) = indepNeighbors G v`.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture100

open SimpleGraph Finset

/-- The arithmetic core: `k a (a-1)^2 + (2a - 2 + t) a t > 4 k (a - 2 + t)^2` where `a = k + t`. -/
@[category API, AMS 5]
private lemma key_poly (k t : ℤ) (hk : 1 ≤ k) (ht : 1 ≤ t) :
    4 * k * (k + 2 * t - 2) ^ 2 < k * (k + t) * (k + t - 1) ^ 2 + (2 * (k + t) - 2 + t) * (k + t) * t := by
  rcases le_or_gt k 4 with hk4 | hk4
  · have h0 : 0 ≤ t - 1 := by linarith
    interval_cases k <;> nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0,
      mul_nonneg (mul_nonneg h0 h0) (by linarith : (0:ℤ) ≤ t)]
  · have h5 : 0 ≤ k - 5 := by linarith
    have ht0 : 0 ≤ t := by linarith
    nlinarith [mul_nonneg h5 h5, mul_nonneg (mul_nonneg h5 h5) h5, mul_nonneg ht0 ht0,
      mul_nonneg (mul_nonneg ht0 ht0) ht0, mul_nonneg (mul_nonneg ht0 ht0) h5,
      mul_nonneg (mul_nonneg ht0 ht0) (mul_nonneg h5 h5), mul_nonneg (mul_nonneg ht0 h5) h5,
      mul_nonneg (mul_nonneg (mul_nonneg ht0 h5) h5) h5, mul_nonneg ht0 h5,
      mul_nonneg (mul_nonneg ht0 ht0) (mul_nonneg ht0 h5)]

/-- Case `K < a`. -/
@[category API, AMS 5]
private lemma arith_lt (a K m E X Y : ℤ) (hK0 : 0 ≤ K) (_hm : 0 ≤ m) (hK : K < a) (hE1 : a ≤ E)
    (hE2 : E ≤ K * m) (hX : a * (a - 1) ^ 2 + 2 * (a - 1) * (a * m - E) ≤ X)
    (hY : (a - K) * (a * m - E) ≤ Y) (ha : 1 ≤ a) : 4 * (2 * a - 2 - K) ^ 2 < X + Y := by
  have hK1 : 1 ≤ K := by
    by_contra hc
    have : K = 0 := by omega
    subst this; simp at hE2; omega
  obtain ⟨t, rfl⟩ : ∃ t, a = K + t := ⟨a - K, by ring⟩
  have ht : 1 ≤ t := by omega
  have hamE : t * m ≤ (K + t) * m - E := by nlinarith
  have hS : (K + t) * (K + t - 1) ^ 2 + (2 * (K + t) - 2 + t) * (t * m) ≤ X + Y := by
    have h2 : 0 ≤ 2 * (K + t) - 2 + t := by omega
    nlinarith [mul_le_mul_of_nonneg_left hamE h2]
  have hkey := key_poly K t hK1 ht
  have hKm : K + t ≤ K * m := le_trans hE1 hE2
  have h3 : K * ((K + t) * (K + t - 1) ^ 2 + (2 * (K + t) - 2 + t) * (t * m)) ≥
      K * (K + t) * (K + t - 1) ^ 2 + (2 * (K + t) - 2 + t) * (K + t) * t := by
    have h4 : 0 ≤ (2 * (K + t) - 2 + t) * t := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hKm h4]
  have h5 : K * (4 * (2 * (K + t) - 2 - K) ^ 2) < K * (X + Y) := by
    have : 2 * (K + t) - 2 - K = K + 2 * t - 2 := by ring
    rw [this]; nlinarith [mul_le_mul_of_nonneg_left hS hK0]
  exact lt_of_mul_lt_mul_left h5 hK0

/-- Case `a ≤ K`. -/
@[category API, AMS 5]
private lemma arith_ge (a K X : ℤ) (hK : a ≤ K) (hX : a * (a - 1) ^ 2 ≤ X)
    (hnn : 0 ≤ 2 * a - 2 - K) : 4 * (2 * a - 2 - K) ^ 2 < X := by
  have ha2 : 2 ≤ a := by omega
  have h1 : 2 * a - 2 - K ≤ a - 2 := by omega
  have h2 : (2 * a - 2 - K) ^ 2 ≤ (a - 2) ^ 2 := by nlinarith
  rcases (show a = 2 ∨ a = 3 ∨ 4 ≤ a by omega) with h | h | h
  · subst h; nlinarith
  · subst h; nlinarith
  · nlinarith [mul_le_mul_of_nonneg_right h (sq_nonneg (a - 1))]

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 100](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj100)
(status O):

For a simple connected graph `G`,
`α(G) ≤ ⌈(max_v l(v) + 0.5 · degreeL2Norm(Gᶜ)) / 2⌉`
where `α(G) = G.indepNum` is the independence number,
`max_v l(v)` is the maximum over all vertices of the independence number of
the neighbourhood (in `G`), and `degreeL2Norm(Gᶜ)` is the square root of the
sum of the squares of the degrees in the complement `Gᶜ`.
-/
@[category research solved, AMS 5]
theorem conjecture100 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    (G.indepNum : ℝ) ≤ ⌈((maxL : ℝ) + (1 / 2) * (degreeL2Norm Gᶜ : ℝ)) / 2⌉ := by
  intro maxL
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  set a := G.indepNum with ha
  set O : Finset α := Iᶜ with hO
  set K := maxL with hK
  -- number of neighbours of `w` inside `I`
  let y : α → ℕ := fun w => #(I.filter (fun u => G.Adj u w))
  -- (1) every `y w` is at most `maxL`
  have hy : ∀ w, y w ≤ K := by
    intro w
    have hind : (G.induce (G.neighborSet w)).IsIndepSet
        (((I.filter (fun u => G.Adj u w)).subtype (· ∈ G.neighborSet w) : Finset _) : Set _) := by
      intro x hx z hz hxz
      simp only [mem_coe, mem_subtype, mem_filter] at hx hz
      simp only [comap_adj, Function.Embedding.subtype_apply]
      exact hI.isIndepSet hx.1 hz.1 (fun e => hxz (Subtype.ext e))
    have h1 := hind.card_le_indepNum
    rw [card_subtype] at h1
    have h2 : (I.filter (fun u => G.Adj u w)).filter (· ∈ G.neighborSet w) =
        I.filter (fun u => G.Adj u w) := by
      apply filter_true_of_mem; intro u hu
      simpa [mem_neighborSet] using (mem_filter.1 hu).2.symm
    rw [h2] at h1
    calc y w ≤ indepNeighborsCard G w := h1
      _ ≤ K := Finset.le_max' _ _ (mem_image_of_mem _ (mem_univ w))
  -- (2) degrees are positive
  have hdeg : ∀ u, 0 < G.degree u := fun u => h.preconnected.degree_pos_of_nontrivial u
  -- (3) neighbours of `u ∈ I` lie in `O`
  have hdegI : ∀ u ∈ I, G.degree u = #(O.filter (G.Adj u)) := by
    intro u hu
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
    congr 1; ext v
    simp only [mem_filter, mem_univ, true_and, hO, mem_compl]
    constructor
    · intro hv; exact ⟨fun hvI => hI.isIndepSet hu hvI (G.ne_of_adj hv) hv, hv⟩
    · exact fun h => h.2
  -- (4) double counting
  have hE : ∑ u ∈ I, #(O.filter (G.Adj u)) = ∑ w ∈ O, y w :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (r := G.Adj) (s := I) (t := O)
  -- (5) complement degree lower bounds
  have hcI : ∀ u ∈ I, (a - 1) + #(O.filter (fun v => ¬ G.Adj u v)) ≤ Gᶜ.degree u := by
    intro u hu
    rw [← card_neighborFinset_eq_degree, neighborFinset_compl]
    have hsub : I.erase u ∪ O.filter (fun v => ¬ G.Adj u v) ⊆ (G.neighborFinset u)ᶜ \ {u} := by
      intro v hv
      simp only [mem_union, mem_erase, mem_filter, hO, mem_compl] at hv
      simp only [mem_sdiff, mem_compl, mem_neighborFinset, mem_singleton]
      rcases hv with ⟨hvu, hvI⟩ | ⟨hvI, hnadj⟩
      · exact ⟨fun hadj => hI.isIndepSet hu hvI (Ne.symm hvu) hadj, hvu⟩
      · exact ⟨hnadj, fun e => hvI (e ▸ hu)⟩
    have hdisj : Disjoint (I.erase u) (O.filter (fun v => ¬ G.Adj u v)) := by
      rw [Finset.disjoint_left]; intro v hv hv'
      simp only [mem_erase, mem_filter, hO, mem_compl] at hv hv'
      exact hv'.1 hv.2
    have := card_le_card hsub
    rw [card_union_of_disjoint hdisj, card_erase_of_mem hu, hI.card_eq] at this
    exact this
  have hcO : ∀ w ∈ O, a - y w ≤ Gᶜ.degree w := by
    intro w hw
    rw [← card_neighborFinset_eq_degree, neighborFinset_compl]
    have hsub : I.filter (fun u => ¬ G.Adj u w) ⊆ (G.neighborFinset w)ᶜ \ {w} := by
      intro v hv
      simp only [mem_filter] at hv
      simp only [mem_sdiff, mem_compl, mem_neighborFinset, mem_singleton]
      refine ⟨fun hadj => hv.2 hadj.symm, fun e => ?_⟩
      simp only [hO, mem_compl] at hw
      exact hw (e ▸ hv.1)
    have h1 := card_le_card hsub
    have h2 := card_filter_add_card_filter_not (s := I) (p := fun u => G.Adj u w)
    rw [hI.card_eq] at h2
    simp only [y]; omega
  have ha1 : 1 ≤ a := by
    obtain ⟨v⟩ := (inferInstance : Nonempty α)
    have hv : G.IsIndepSet (({v} : Finset α) : Set α) := by
      rw [coe_singleton]; exact Set.pairwise_singleton _ _
    simpa using hv.card_le_indepNum
  have hdm : ∀ u, #(O.filter (G.Adj u)) ≤ #O := fun u => card_filter_le _ _
  have hE1 : a ≤ ∑ u ∈ I, #(O.filter (G.Adj u)) := by
    have : ∑ u ∈ I, 1 ≤ ∑ u ∈ I, #(O.filter (G.Adj u)) := sum_le_sum fun u hu => by
      have := hdeg u; rw [hdegI u hu] at this; omega
    simpa [hI.card_eq] using this
  have hE2 : ∑ u ∈ I, #(O.filter (G.Adj u)) ≤ K * #O := by
    rw [hE]
    calc ∑ w ∈ O, y w ≤ ∑ w ∈ O, K := sum_le_sum fun w _ => hy w
      _ = K * #O := by rw [sum_const, smul_eq_mul, mul_comm]
  have hEm : ∑ u ∈ I, #(O.filter (G.Adj u)) ≤ a * #O := by
    calc _ ≤ ∑ u ∈ I, #O := sum_le_sum fun u _ => hdm u
      _ = a * #O := by rw [sum_const, smul_eq_mul, hI.card_eq]
  have hcI' : ∀ u ∈ I, ((a:ℤ) - 1) + (#O - #(O.filter (G.Adj u))) ≤ (Gᶜ.degree u : ℤ) := by
    intro u hu
    have h1 := hcI u hu
    have h2 := card_filter_add_card_filter_not (s := O) (p := G.Adj u)
    omega
  have hX : (a:ℤ) * (a - 1) ^ 2 + 2 * (a - 1) * (a * #O - ∑ u ∈ I, #(O.filter (G.Adj u)))
      ≤ ∑ u ∈ I, (Gᶜ.degree u : ℤ) ^ 2 := by
    have hpt : ∀ u ∈ I, ((a:ℤ) - 1) ^ 2 + 2 * ((a:ℤ) - 1) * (#O - #(O.filter (G.Adj u)))
        ≤ (Gᶜ.degree u : ℤ) ^ 2 := by
      intro u hu
      have h := hcI' u hu
      have h0 : (0:ℤ) ≤ #O - #(O.filter (G.Adj u)) := by have := hdm u; omega
      have ha0 : (0:ℤ) ≤ a - 1 := by omega
      nlinarith
    calc _ = ∑ u ∈ I, (((a:ℤ) - 1) ^ 2 + 2 * ((a:ℤ) - 1) * (#O - #(O.filter (G.Adj u)))) := by
          simp only [sum_add_distrib, sum_const, ← mul_sum, sum_sub_distrib, hI.card_eq,
            nsmul_eq_mul]
          push_cast; ring
      _ ≤ _ := sum_le_sum hpt
  have hYnn : 0 ≤ ∑ w ∈ O, (Gᶜ.degree w : ℤ) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hsplit : ∑ v, (Gᶜ.degree v : ℤ) ^ 2 =
      ∑ u ∈ I, (Gᶜ.degree u : ℤ) ^ 2 + ∑ w ∈ O, (Gᶜ.degree w : ℤ) ^ 2 :=
    (sum_add_sum_compl I _).symm
  have hS : 2 * (a:ℤ) - 2 - K < 0 ∨ 4 * (2 * (a:ℤ) - 2 - K) ^ 2 < ∑ v, (Gᶜ.degree v : ℤ) ^ 2 := by
    rcases lt_or_ge (2 * (a:ℤ) - 2 - K) 0 with hneg | hnn
    · exact Or.inl hneg
    right
    rw [hsplit]
    rcases lt_or_ge (K:ℤ) a with hKa | hKa
    · have hY : ((a:ℤ) - K) * (a * #O - ∑ u ∈ I, #(O.filter (G.Adj u)))
          ≤ ∑ w ∈ O, (Gᶜ.degree w : ℤ) ^ 2 := by
        have hpt : ∀ w ∈ O, ((a:ℤ) - K) * (a - y w) ≤ (Gᶜ.degree w : ℤ) ^ 2 := by
          intro w hw
          have h1 := hcO w hw
          have h2 := hy w
          have h3 : (a:ℤ) - y w ≤ Gᶜ.degree w := by omega
          have h4 : (0:ℤ) ≤ a - K := by omega
          have h5 : (a:ℤ) - K ≤ a - y w := by omega
          have h6 : (0:ℤ) ≤ Gᶜ.degree w := by positivity
          nlinarith [mul_le_mul_of_nonneg_left h3 h4, mul_le_mul_of_nonneg_right (h5.trans h3) h6]
        calc _ = ∑ w ∈ O, ((a:ℤ) - K) * (a - y w) := by
              rw [← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul]
              congr 1; push_cast [hE]; ring
          _ ≤ _ := sum_le_sum hpt
      exact arith_lt a K #O _ _ _ (by positivity) (by positivity) hKa (by exact_mod_cast hE1)
        (by exact_mod_cast hE2) hX hY (by exact_mod_cast ha1)
    · have hamE : (0:ℤ) ≤ 2 * (a - 1) * (a * #O - ∑ u ∈ I, #(O.filter (G.Adj u))) := by
        have : ((∑ u ∈ I, #(O.filter (G.Adj u)) : ℕ) : ℤ) ≤ a * #O := by exact_mod_cast hEm
        have h0 : (0:ℤ) ≤ a - 1 := by omega
        exact mul_nonneg (mul_nonneg (by norm_num) h0) (by linarith)
      have := arith_ge a K (∑ u ∈ I, (Gᶜ.degree u : ℤ) ^ 2) hKa (by linarith) hnn
      linarith
  -- conclude
  have hz : (a:ℤ) ≤ ⌈((K : ℝ) + (1 / 2) * (degreeL2Norm Gᶜ : ℝ)) / 2⌉ := by
    rw [Int.le_ceil_iff]
    have hsq : 0 ≤ degreeL2Norm Gᶜ := Real.sqrt_nonneg _
    rcases hS with hneg | hlt
    · have : ((2 * (a:ℤ) - 2 - K : ℤ) : ℝ) < 0 := by exact_mod_cast hneg
      push_cast at this ⊢; linarith
    · have hlt' : ((2 * (2 * (a:ℝ) - 2 - K)) ^ 2) < ∑ v, (Gᶜ.degree v : ℝ) ^ 2 := by
        have : ((4 * (2 * (a:ℤ) - 2 - K) ^ 2 : ℤ) : ℝ) < ((∑ v, (Gᶜ.degree v : ℤ) ^ 2 : ℤ) : ℝ) := by
          exact_mod_cast hlt
        push_cast at this; nlinarith
      have := Real.lt_sqrt_of_sq_lt hlt'
      unfold degreeL2Norm at hsq ⊢
      push_cast; linarith
  exact_mod_cast hz

-- Sanity checks

/-- The independence number is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.indepNum := Nat.zero_le _

/-- The Euclidean norm of the degree sequence is nonnegative. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 2)) [DecidableRel G.Adj] : 0 ≤ degreeL2Norm G :=
  Real.sqrt_nonneg _

end WrittenOnTheWallII.GraphConjecture100
