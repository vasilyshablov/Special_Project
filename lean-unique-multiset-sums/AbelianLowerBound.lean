module

public import FormalConjecturesUtil
public import FormalConjectures.Arxiv.«2607.08366».MinModulus

@[expose] public section

open Finset

namespace AbelianLowerBound

variable {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `g` has *unique multiset sums*: the all-ones multiset is the only multiset of size
`card ι` drawn from the family `g` whose sum is `∑ i, g i`. -/
def UniqueMultisetSums (g : ι → G) : Prop :=
  ∀ m : ι → ℕ, ∑ i, m i = Fintype.card ι → ∑ i, m i • g i = ∑ i, g i → ∀ i, m i = 1

/-- The anchored subset sums `∑_{i ∈ S} (g j - g i)`. -/
def F (g : ι → G) (j : ι) (S : Finset ι) : G := ∑ i ∈ S, (g j - g i)

lemma key {g : ι → G} (h : UniqueMultisetSums g) (j : ι) {S T : Finset ι}
    (hS : j ∉ S) (hT : j ∉ T) (hcard : T.card ≤ S.card) (heq : F g j S = F g j T) :
    S = T := by
  classical
  -- the rival multiset `1 - 1_S + 1_T + (|S| - |T|) e_j`
  let m : ι → ℕ := fun i =>
    if i = j then 1 + (S.card - T.card) else (if i ∈ S then 0 else 1) + (if i ∈ T then 1 else 0)
  -- integer form of `m`
  have hmZ : ∀ i, (m i : ℤ) = 1 - (if i ∈ S then 1 else 0) + (if i ∈ T then 1 else 0) +
      (if i = j then ((S.card : ℤ) - T.card) else 0) := by
    intro i
    by_cases hij : i = j
    · subst hij; simp [m, hS, hT, Nat.cast_sub hcard]
    · by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T <;> simp [m, hij, hiS, hiT]
  have hsum : ∑ i, m i = Fintype.card ι := by
    have : (∑ i, (m i : ℤ)) = Fintype.card ι := by
      simp only [hmZ, sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
        mul_one, sum_ite_mem, univ_inter, sum_ite_eq', mem_univ, if_true]
      ring
    exact_mod_cast this
  have hval : ∑ i, m i • g i = ∑ i, g i := by
    have e : ∀ i, m i • g i = ((m i : ℤ)) • g i := fun i => (natCast_zsmul _ _).symm
    simp only [e, hmZ, add_smul, sub_smul, one_smul, sum_add_distrib, sum_sub_distrib,
      ite_smul, zero_smul, sum_ite_mem, univ_inter, sum_ite_eq', mem_univ, if_true]
    have hF : ∀ U : Finset ι, F g j U = (U.card : ℤ) • g j - ∑ i ∈ U, g i := by
      intro U; simp [F, sum_sub_distrib, sum_const, natCast_zsmul]
    have := heq; rw [hF, hF] at this
    rw [show ∑ x, g x - ∑ x ∈ S, g x + ∑ x ∈ T, g x + ((S.card : ℤ) • g j - (T.card : ℤ) • g j)
        = ∑ x, g x + (((S.card : ℤ) • g j - ∑ i ∈ S, g i) - ((T.card : ℤ) • g j - ∑ i ∈ T, g i))
        by abel, this, sub_self, add_zero]
  have hall := h m hsum hval
  ext i
  by_cases hij : i = j
  · subst hij; simp [hS, hT]
  have := hall i
  simp only [m, if_neg hij] at this
  by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T <;> simp [hiS, hiT] at this ⊢

/-- **Lower bound.** A family of `n` elements of a finite abelian group with unique multiset
sums forces `|G| ≥ 2^(n-1)`. -/
theorem two_pow_le_card [Fintype G] (g : ι → G) (h : UniqueMultisetSums g) (j : ι) :
    2 ^ (Fintype.card ι - 1) ≤ Fintype.card G := by
  classical
  have hinj : Set.InjOn (F g j) ((univ.erase j).powerset : Set (Finset ι)) := by
    intro S hS T hT heq
    simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset,
      subset_erase] at hS hT
    rcases le_total T.card S.card with hc | hc
    · exact key h j hS.2 hT.2 hc heq
    · exact (key h j hT.2 hS.2 hc heq.symm).symm
  have := card_le_card_of_injOn (F g j) (fun _ _ => mem_univ _) hinj
  simpa [card_powerset, card_erase_of_mem (mem_univ j)] using this

/-- **Corollary (cyclic case).** If `A` is a valid set of `n ≥ 1` residues mod `N`, then
`2^(n-1) ≤ N`. -/
theorem two_pow_le_of_isValidMod {N : ℕ} [NeZero N] (A : Finset (ZMod N))
    (hA : Arxiv.«2607.08366».IsValidMod A) (hn : A.Nonempty) : 2 ^ (A.card - 1) ≤ N := by
  classical
  let g : A → ZMod N := Subtype.val
  have hU : UniqueMultisetSums g := by
    intro m hm hsum i
    let m' : ZMod N → ℕ := fun a => if h : a ∈ A then m ⟨a, h⟩ else 0
    have hm' : ∀ x : A, m' x.1 = m x := fun x => by simp [m', x.2]
    have h1 : ∑ a ∈ A, m' a = A.card := by
      rw [← Finset.sum_coe_sort A]; simp only [hm']; simpa using hm
    have h2 : ∑ a ∈ A, (m' a : ZMod N) * a = ∑ a ∈ A, a := by
      rw [← Finset.sum_coe_sort A, ← Finset.sum_coe_sort A]
      simp only [hm']
      simpa [g, nsmul_eq_mul] using hsum
    simpa [hm'] using hA m' h1 h2 i.1 i.2
  obtain ⟨a, ha⟩ := hn
  have := two_pow_le_card g hU ⟨a, ha⟩
  simpa [ZMod.card] using this

end AbelianLowerBound

#print axioms AbelianLowerBound.two_pow_le_card
#print axioms AbelianLowerBound.two_pow_le_of_isValidMod
