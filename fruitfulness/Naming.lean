import Mathlib

/-!
# A calculus of naming: exact value, rank-one updates, and diminishing returns

A *library* has results `0, 1, 2, …`; result `x` has an own proof of size `size x` and
cites results `deps x`, all with smaller index. A *naming* is a finite set `N` of results
whose bodies are written once and cited by a one-symbol reference; every other result is
inlined wherever it is used. A distinguished result `r` (the goal) is always written.

* `W N x`: the inlined size of `x`'s body, given the names `N`.
* `P N x v`: the number of times `v` occurs in that inlined body of `x`.
* `cost N = W N r + ∑ x ∈ N, W N x`: total size of the written library.
* `occ N v = P N r v + ∑ x ∈ N, P N x v`: total occurrences of `v` in the written library.

Main results.

1. `cost_add_occ`, `gain_eq` (**exact value**). Naming one more result `v` saves exactly
   `(occ N v - 1) * (W N v - 1) - 1`. This is the library-wide form of
   `(k - 1)(b - 1) - 1`: the value of a concept is the product of an *external* factor
   (how often it occurs) and an *internal* factor (how much it hides).
2. `W_insert`, `P_insert`, `occ_insert` (**rank-one updates**). Naming `u` changes inlined
   sizes and occurrence counts by rank-one corrections:
   `W' x = W x - P x u * (W u - 1)` and `P' x v = P x v - P x u * P u v`. These are the
   Schur-complement (Sherman–Morrison) updates of Gaussian elimination: inlining a result
   is eliminating a variable, and naming it is keeping it as an interface.
3. `substitutes` (**diminishing returns**). If every result is used, then the value of
   naming `v` can only decrease when another result `u` is named. The savings function
   `N ↦ cost ∅ - cost N` is submodular: concepts are substitutes, never complements, as
   far as compression is concerned.
4. `comprehension_complements` (**bounded minds see complements**). For an agent that can
   only hold results whose inlined size is at most a capacity `B`, two names can be
   individually useless and jointly decisive. Comprehension is not submodular.

So increasing returns from concepts, where one idea makes others valuable, cannot come from
compression of a fixed body of mathematics. In this model they come from bounded capacity.
-/

namespace Naming

structure Lib where
  size : ℕ → ℕ
  deps : ℕ → Finset ℕ
  acyclic : ∀ i, ∀ j ∈ deps i, j < i

variable (L : Lib)

/-- Inlined size of the body of `x` when the results in `N` are named. -/
def Lib.W (N : Finset ℕ) (x : ℕ) : ℕ :=
  L.size x + ∑ j ∈ L.deps x, if h : j < x then (if j ∈ N then 1 else Lib.W N j) else 0
termination_by x
decreasing_by exact h

/-- Number of occurrences of `v` in the inlined body of `x` when `N` is named. -/
def Lib.P (N : Finset ℕ) (x v : ℕ) : ℕ :=
  ∑ j ∈ L.deps x,
    if _h : j < x then (if j = v then 1 else if j ∈ N then 0 else Lib.P N j v) else 0
termination_by x
decreasing_by assumption

theorem Lib.W_eq (N : Finset ℕ) (x : ℕ) :
    L.W N x = L.size x + ∑ j ∈ L.deps x, (if j ∈ N then 1 else L.W N j) := by
  rw [Lib.W]
  congr 1
  exact Finset.sum_congr rfl fun j hj => dif_pos (L.acyclic x j hj)

theorem Lib.P_eq (N : Finset ℕ) (x v : ℕ) :
    L.P N x v = ∑ j ∈ L.deps x, (if j = v then 1 else if j ∈ N then 0 else L.P N j v) := by
  rw [Lib.P]
  exact Finset.sum_congr rfl fun j hj => dif_pos (L.acyclic x j hj)

/-- The written size of the library. -/
def Lib.cost (r : ℕ) (N : Finset ℕ) : ℕ := L.W N r + ∑ x ∈ N, L.W N x

/-- Occurrences of `v` across the written library. -/
def Lib.occ (r : ℕ) (N : Finset ℕ) (v : ℕ) : ℕ := L.P N r v + ∑ x ∈ N, L.P N x v

/-- Saving from additionally naming `v`. -/
def Lib.gain (r : ℕ) (N : Finset ℕ) (v : ℕ) : ℤ :=
  (L.cost r N : ℤ) - L.cost r (insert v N)

/-! ### Basic facts -/

/-- Nothing below `v` (or `v` itself) contains `v`. -/
theorem Lib.P_eq_zero_of_le (N : Finset ℕ) (v : ℕ) : ∀ x, x ≤ v → L.P N x v = 0 := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx
    rw [L.P_eq]
    apply Finset.sum_eq_zero
    intro j hj
    have hjx := L.acyclic x j hj
    rw [if_neg (by omega)]
    split_ifs
    · rfl
    · exact ih j hjx (by omega)

theorem Lib.size_le_W (N : Finset ℕ) (x : ℕ) : L.size x ≤ L.W N x := by
  rw [L.W_eq]; omega

/-! ### Rank-one update of inlined sizes -/

/-- Naming `v` changes inlined sizes by `P · (W v - 1)` (stated without subtraction). -/
theorem Lib.W_insert (N : Finset ℕ) (v : ℕ) (hv : v ∉ N) :
    ∀ x, L.W N x + L.P N x v = L.W (insert v N) x + L.P N x v * L.W N v := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    have key : ∀ j ∈ L.deps x,
        (if j ∈ N then 1 else L.W N j) + (if j = v then 1 else if j ∈ N then 0 else L.P N j v)
          = (if j ∈ insert v N then 1 else L.W (insert v N) j)
            + (if j = v then 1 else if j ∈ N then 0 else L.P N j v) * L.W N v := by
      intro j hj
      by_cases hjv : j = v
      · subst hjv; simp [hv]; ring
      · by_cases hjN : j ∈ N
        · simp [hjv, hjN]
        · have hins : j ∉ insert v N := by simp [hjv, hjN]
          simp only [hjv, hjN, hins, if_false]
          exact ih j (L.acyclic x j hj)
    have hsum := Finset.sum_congr rfl key
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
    rw [L.W_eq N x, L.W_eq (insert v N) x, L.P_eq N x v]
    nlinarith [hsum]

/-- Naming `v` does not change `v`'s own inlined body. -/
theorem Lib.W_insert_self (N : Finset ℕ) (v : ℕ) (hv : v ∉ N) :
    L.W (insert v N) v = L.W N v := by
  have h := L.W_insert N v hv v
  rw [L.P_eq_zero_of_le N v v le_rfl] at h
  simpa using h.symm

/-- Naming never increases inlined sizes (when own sizes are positive). -/
theorem Lib.W_insert_le (hsize : ∀ i, 1 ≤ L.size i) (N : Finset ℕ) (u : ℕ) (hu : u ∉ N)
    (x : ℕ) : L.W (insert u N) x ≤ L.W N x := by
  have h := L.W_insert N u hu x
  have h1 : 1 ≤ L.W N u := le_trans (hsize u) (L.size_le_W N u)
  have : L.P N x u ≤ L.P N x u * L.W N u := Nat.le_mul_of_pos_right _ h1
  omega

/-! ### Exact value of a name -/

theorem Lib.cost_add_occ (r : ℕ) (N : Finset ℕ) (v : ℕ) (hv : v ∉ N) :
    L.cost r N + L.occ r N v + L.W N v = L.cost r (insert v N) + L.occ r N v * L.W N v := by
  have hr := L.W_insert N v hv r
  have hN : ∑ x ∈ N, (L.W N x + L.P N x v) = ∑ x ∈ N, (L.W (insert v N) x + L.P N x v * L.W N v) :=
    Finset.sum_congr rfl fun x _ => L.W_insert N v hv x
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul] at hN
  unfold Lib.cost Lib.occ
  rw [Finset.sum_insert hv, L.W_insert_self N v hv]
  nlinarith [hr, hN]

/-- **Exact value theorem.** Naming `v` saves `(occ - 1) * (W - 1) - 1` symbols. -/
theorem Lib.gain_eq (r : ℕ) (N : Finset ℕ) (v : ℕ) (hv : v ∉ N) :
    L.gain r N v = ((L.occ r N v : ℤ) - 1) * ((L.W N v : ℤ) - 1) - 1 := by
  have h := L.cost_add_occ r N v hv
  unfold Lib.gain
  have h' : (L.cost r N : ℤ) + L.occ r N v + L.W N v
      = L.cost r (insert v N) + (L.occ r N v : ℤ) * L.W N v := by exact_mod_cast h
  linarith

/-! ### Rank-one update of occurrence counts -/

theorem Lib.P_mul_P_eq_zero (N : Finset ℕ) (u v : ℕ) (huv : u ≠ v) :
    L.P N v u * L.P N u v = 0 := by
  rcases lt_or_gt_of_ne huv with h | h
  · rw [L.P_eq_zero_of_le N v u (le_of_lt h)]; ring
  · rw [L.P_eq_zero_of_le N u v (le_of_lt h)]; ring

/-- Naming `u` removes exactly the occurrences routed through `u`:
`P' x v = P x v - P x u * P u v`. -/
theorem Lib.P_insert (N : Finset ℕ) (u v : ℕ) (hu : u ∉ N) (huv : u ≠ v) :
    ∀ x, L.P N x v = L.P (insert u N) x v + L.P N x u * L.P N u v := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    have key : ∀ j ∈ L.deps x,
        (if j = v then 1 else if j ∈ N then 0 else L.P N j v)
          = (if j = v then 1 else if j ∈ insert u N then 0 else L.P (insert u N) j v)
            + (if j = u then 1 else if j ∈ N then 0 else L.P N j u) * L.P N u v := by
      intro j hj
      by_cases hjv : j = v
      · subst hjv
        have hne : j ≠ u := fun h => huv h.symm
        by_cases hjN : j ∈ N
        · simp [hne, hjN]
        · simp only [hne, hjN, if_true, if_false]
          rw [L.P_mul_P_eq_zero N u j huv]
      · by_cases hju : j = u
        · subst hju; simp [hjv, hu]
        · by_cases hjN : j ∈ N
          · simp [hjv, hju, hjN]
          · have hins : j ∉ insert u N := by simp [hju, hjN]
            simp only [hjv, hju, hjN, hins, if_false]
            exact ih j (L.acyclic x j hj)
    rw [L.P_eq N x v, L.P_eq (insert u N) x v, L.P_eq N x u, Finset.sum_mul,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl key

theorem Lib.P_insert_self (N : Finset ℕ) (u v : ℕ) (hu : u ∉ N) (huv : u ≠ v) :
    L.P (insert u N) u v = L.P N u v := by
  have h := L.P_insert N u v hu huv u
  rw [L.P_eq_zero_of_le N u u le_rfl] at h
  simpa using h.symm

/-- Occurrence update: `occ' v + occ u * P u v = occ v + P u v`. -/
theorem Lib.occ_insert (r : ℕ) (N : Finset ℕ) (u v : ℕ) (hu : u ∉ N) (huv : u ≠ v) :
    L.occ r (insert u N) v + L.occ r N u * L.P N u v = L.occ r N v + L.P N u v := by
  have hr := L.P_insert N u v hu huv r
  have hN : ∑ x ∈ N, L.P N x v = ∑ x ∈ N, (L.P (insert u N) x v + L.P N x u * L.P N u v) :=
    Finset.sum_congr rfl fun x _ => L.P_insert N u v hu huv x
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hN
  unfold Lib.occ
  rw [Finset.sum_insert hu, L.P_insert_self N u v hu huv]
  nlinarith [hr, hN]

theorem Lib.occ_insert_le (r : ℕ) (N : Finset ℕ) (u v : ℕ) (hu : u ∉ N) (huv : u ≠ v)
    (hocc : 1 ≤ L.occ r N u) : L.occ r (insert u N) v ≤ L.occ r N v := by
  have h := L.occ_insert r N u v hu huv
  have : L.P N u v ≤ L.occ r N u * L.P N u v := Nat.le_mul_of_pos_left _ hocc
  omega

/-! ### Every used result occurs -/

/-- If `v` is cited by an unnamed `p`, then `v` occurs wherever `p` does. -/
theorem Lib.P_le_of_child (N : Finset ℕ) (p v : ℕ) (hp : p ∉ N) (hvp : v ∈ L.deps p) :
    ∀ x, L.P N x p ≤ L.P N x v := by
  have hv_lt := L.acyclic p v hvp
  have hpv : 1 ≤ L.P N p v := by
    rw [L.P_eq]
    have := Finset.single_le_sum (f := fun j => if j = v then 1 else if j ∈ N then 0 else L.P N j v)
      (fun _ _ => Nat.zero_le _) hvp
    simpa using this
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rw [L.P_eq N x p, L.P_eq N x v]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hjp : j = p
    · subst hjp
      have hne : j ≠ v := by omega
      simp [hne, hp, hpv]
    · by_cases hjv : j = v
      · subst hjv
        have h0 : L.P N j p = 0 := L.P_eq_zero_of_le N p j (le_of_lt hv_lt)
        simp [hjp, h0]
      · by_cases hjN : j ∈ N
        · simp [hjp, hjv, hjN]
        · simp only [hjp, hjv, hjN, if_false]
          exact ih j (L.acyclic x j hj)

/-- If every result below the goal is cited by something at or below the goal, then every
result below the goal occurs at least once, whatever is named. -/
theorem Lib.one_le_occ (r : ℕ) (hpar : ∀ x < r, ∃ p, x ∈ L.deps p ∧ p ≤ r) (N : Finset ℕ) :
    ∀ v, v < r → 1 ≤ L.occ r N v := by
  have main : ∀ n v, r - v = n → v < r → 1 ≤ L.occ r N v := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hn hv
      obtain ⟨p, hvp, hpr⟩ := hpar v hv
      have hvlt := L.acyclic p v hvp
      have hdirect : 1 ≤ L.P N p v := by
        rw [L.P_eq]
        have := Finset.single_le_sum
          (f := fun j => if j = v then 1 else if j ∈ N then 0 else L.P N j v)
          (fun _ _ => Nat.zero_le _) hvp
        simpa using this
      unfold Lib.occ
      rcases eq_or_lt_of_le hpr with hpr | hpr
      · subst hpr; omega
      · by_cases hpN : p ∈ N
        · have := Finset.single_le_sum (f := fun x => L.P N x v) (fun _ _ => Nat.zero_le _) hpN
          omega
        · have hp := ih (r - p) (by omega) p rfl hpr
          unfold Lib.occ at hp
          have h1 := L.P_le_of_child N p v hpN hvp r
          have h2 : ∑ x ∈ N, L.P N x p ≤ ∑ x ∈ N, L.P N x v :=
            Finset.sum_le_sum fun x _ => L.P_le_of_child N p v hpN hvp x
          omega
  exact fun v hv => main (r - v) v rfl hv

/-! ### Concepts are substitutes -/

/-- **Diminishing returns.** In a library where every result is used, naming another result
`u` can only lower the value of naming `v`. Equivalently, the savings function is
submodular. -/
theorem Lib.substitutes (hsize : ∀ i, 1 ≤ L.size i) (r : ℕ)
    (hpar : ∀ x < r, ∃ p, x ∈ L.deps p ∧ p ≤ r) (N : Finset ℕ) (u v : ℕ)
    (hu : u < r) (hv : v < r) (huN : u ∉ N) (hvN : v ∉ N) (huv : u ≠ v) :
    L.gain r (insert u N) v ≤ L.gain r N v := by
  have hvN' : v ∉ insert u N := by simp [hvN, Ne.symm huv]
  rw [L.gain_eq r N v hvN, L.gain_eq r (insert u N) v hvN']
  have ho := L.occ_insert_le r N u v huN huv (L.one_le_occ r hpar N u hu)
  have ho1 := L.one_le_occ r hpar (insert u N) v hv
  have hw := L.W_insert_le hsize N u huN v
  have hw1 : 1 ≤ L.W (insert u N) v := le_trans (hsize v) (L.size_le_W _ v)
  have a : (0 : ℤ) ≤ (L.occ r (insert u N) v : ℤ) - 1 := by
    have : (1 : ℤ) ≤ L.occ r (insert u N) v := by exact_mod_cast ho1
    linarith
  have b : (0 : ℤ) ≤ (L.W (insert u N) v : ℤ) - 1 := by
    have : (1 : ℤ) ≤ L.W (insert u N) v := by exact_mod_cast hw1
    linarith
  have c : (L.occ r (insert u N) v : ℤ) - 1 ≤ (L.occ r N v : ℤ) - 1 := by
    have : (L.occ r (insert u N) v : ℤ) ≤ L.occ r N v := by exact_mod_cast ho
    linarith
  have d : (L.W (insert u N) v : ℤ) - 1 ≤ (L.W N v : ℤ) - 1 := by
    have : (L.W (insert u N) v : ℤ) ≤ L.W N v := by exact_mod_cast hw
    linarith
  have := mul_le_mul c d b (le_trans a c)
  linarith

/-! ### Bounded minds see complements -/

/-- Two lemmas of size 3 cited by a goal of size 1. -/
def pair : Lib where
  size i := if i = 2 then 1 else 3
  deps i := if i = 2 then {0, 1} else ∅
  acyclic i j hj := by
    split_ifs at hj with h
    · subst h; simp at hj; omega
    · simp at hj

theorem pair_W (N : Finset ℕ) :
    pair.W N 2 = 1 + (if 0 ∈ N then 1 else 3) + (if 1 ∈ N then 1 else 3) := by
  have hs : pair.size 2 = 1 := rfl
  have hd : pair.deps 2 = {0, 1} := rfl
  have h0 : pair.W N 0 = 3 := by
    rw [pair.W_eq, show pair.deps 0 = ∅ from rfl, Finset.sum_empty]; rfl
  have h1 : pair.W N 1 = 3 := by
    rw [pair.W_eq, show pair.deps 1 = ∅ from rfl, Finset.sum_empty]; rfl
  rw [pair.W_eq, hs, hd, Finset.sum_pair (by norm_num), h0, h1]
  ring

/-- An agent of capacity `3` can hold the goal only when **both** lemmas are named. Each
name alone is useless to it, while both together are decisive. Comprehension, unlike
compression, has complementarities. -/
theorem comprehension_complements :
    ¬ pair.W ∅ 2 ≤ 3 ∧ ¬ pair.W {0} 2 ≤ 3 ∧ ¬ pair.W {1} 2 ≤ 3 ∧ pair.W {0, 1} 2 ≤ 3 := by
  simp only [pair_W]
  decide

end Naming
