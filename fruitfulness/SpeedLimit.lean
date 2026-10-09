import Mathlib

/-!
# The speed limit of compression

A library of unit-size results: result `i` cites the results `deps i` (all of smaller
index), and its unfolded size is `u i = 1 + ∑ j ∈ deps i, u j`, i.e. the number of paths
starting at `i` in the citation DAG. The *named cost* of the first `n` results is
`cost n = ∑ i < n, (1 + #deps i)`: one symbol per result and one per citation.

How large can an unfolded size be, given the named cost?

* Lower bound (`fibLib_u`, `fibLib_cost`). The Fibonacci library reaches
  `u = F (n + 3) - 1` at cost `3 n`, so about `φ ^ (cost / 3) ≈ 1.174 ^ cost`.
* Upper bound (`u_le`). Every unfolded size satisfies `u i ≤ 28 * (5 / 4) ^ cost n`,
  stated without division as `4 ^ cost n * u i ≤ 28 * 5 ^ cost n`.

The proof uses a potential on *top-`j` sums*. `S j n` is the largest total unfolded size
of at most `j` distinct results among the first `n`. Then
`Φ = 4 S₁ + 2 S₂ + S₃ + 28` grows by at most a factor `(5/4) ^ (1 + d)` when a result
citing `d` others is added. The weights `(4, 2, 1)` were found by linear programming. The
inequalities they must satisfy reduce to the elementary facts that `S` is monotone,
subadditive (`S (a + b) ≤ S a + S b`) and convex on average (`j S (j+1) ≤ (j+1) S j`).

We conjecture that the true speed limit is `φ ^ (1/3)` per symbol. Exact search
(see the paper) finds that the maximum at cost `3 m` is exactly `2 L m - 2`
(`L` = Lucas numbers) for `4 ≤ m ≤ 15`.
-/

namespace SpeedLimit

open Finset

structure ULib where
  deps : ℕ → Finset ℕ
  acyclic : ∀ i, ∀ j ∈ deps i, j < i

variable (L : ULib)

/-- Unfolded size: the number of citation paths starting at `i`. -/
def ULib.u (i : ℕ) : ℕ := 1 + ∑ j ∈ L.deps i, if _h : j < i then ULib.u j else 0
termination_by i
decreasing_by assumption

theorem ULib.u_eq (i : ℕ) : L.u i = 1 + ∑ j ∈ L.deps i, L.u j := by
  rw [ULib.u]
  congr 1
  exact Finset.sum_congr rfl fun j hj => dif_pos (L.acyclic i j hj)

/-- Named cost of the first `n` results. -/
def ULib.cost (n : ℕ) : ℕ := ∑ i ∈ range n, (1 + (L.deps i).card)

/-- Largest total unfolded size of at most `j` distinct results among the first `n`. -/
def ULib.S (j n : ℕ) : ℕ :=
  ((range n).powerset.filter (fun A => A.card ≤ j)).sup (fun A => ∑ i ∈ A, L.u i)

theorem ULib.le_S {j n : ℕ} {A : Finset ℕ} (hA : A ⊆ range n) (hc : A.card ≤ j) :
    ∑ i ∈ A, L.u i ≤ L.S j n :=
  Finset.le_sup (f := fun A => ∑ i ∈ A, L.u i) (by simp [hA, hc])

theorem ULib.S_le {j n c : ℕ} (h : ∀ A ⊆ range n, A.card ≤ j → ∑ i ∈ A, L.u i ≤ c) :
    L.S j n ≤ c :=
  Finset.sup_le fun A hA => by
    simp only [mem_filter, mem_powerset] at hA
    exact h A hA.1 hA.2

theorem ULib.S_mono {j k n : ℕ} (hjk : j ≤ k) : L.S j n ≤ L.S k n :=
  L.S_le fun _ hA hc => L.le_S hA (le_trans hc hjk)

theorem ULib.S_zero (n : ℕ) : L.S 0 n = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply L.S_le
  intro A _ hc
  rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hc)]; simp

/-- Subadditivity. -/
theorem ULib.S_add (a b n : ℕ) : L.S (a + b) n ≤ L.S a n + L.S b n := by
  apply L.S_le
  intro A hA hc
  obtain ⟨B, hBA, hBc⟩ := Finset.exists_subset_card_eq (show min a A.card ≤ A.card from min_le_right _ _)
  rw [← Finset.sum_sdiff hBA]
  have h1 : ∑ i ∈ B, L.u i ≤ L.S a n := L.le_S (hBA.trans hA) (by omega)
  have h2 : ∑ i ∈ A \ B, L.u i ≤ L.S b n := by
    apply L.le_S (sdiff_subset.trans hA)
    rw [Finset.card_sdiff_of_subset hBA]
    omega
  omega

/-- Averaging: a top-`(j+1)` sum exceeds a top-`j` sum by at most its average. -/
theorem ULib.S_avg (j n : ℕ) : j * L.S (j + 1) n ≤ (j + 1) * L.S j n := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  have key : ∀ A ⊆ range n, A.card ≤ j + 1 → j * ∑ i ∈ A, L.u i ≤ (j + 1) * L.S j n := by
    intro A hA hc
    rcases Nat.lt_or_ge A.card (j + 1) with hlt | hge
    · have := L.le_S hA (show A.card ≤ j by omega)
      nlinarith
    · have hcard : A.card = j + 1 := le_antisymm hc hge
      have hne : A.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image A L.u hne
      have hB : (A.erase m).card = j := by rw [Finset.card_erase_of_mem hm]; omega
      have hBS := L.le_S ((Finset.erase_subset m A).trans hA) (le_of_eq hB)
      have hlow : (A.erase m).card • L.u m ≤ ∑ i ∈ A.erase m, L.u i :=
        Finset.card_nsmul_le_sum _ _ _ fun i hi => hmin i (Finset.mem_of_mem_erase hi)
      rw [hB, smul_eq_mul] at hlow
      rw [← Finset.add_sum_erase A L.u hm]
      nlinarith
  obtain ⟨A, hA, hAeq⟩ := Finset.exists_mem_eq_sup
    ((range n).powerset.filter (fun A => A.card ≤ j + 1)) ⟨∅, by simp⟩
    (fun A => ∑ i ∈ A, L.u i)
  unfold ULib.S
  rw [hAeq]
  simp only [mem_filter, mem_powerset] at hA
  exact key A hA.1 hA.2

/-- A new result is worth at most one more than the best sum of as many results as it cites. -/
theorem ULib.u_le_S (n : ℕ) : L.u n ≤ 1 + L.S (L.deps n).card n := by
  rw [L.u_eq]
  have : ∑ j ∈ L.deps n, L.u j ≤ L.S (L.deps n).card n :=
    L.le_S (fun j hj => mem_range.2 (L.acyclic n j hj)) le_rfl
  omega

/-- Adding result `n`: a top-`(j+1)` sum either avoids `n` or uses it. -/
theorem ULib.S_succ (j n : ℕ) :
    L.S (j + 1) (n + 1) ≤ max (L.S (j + 1) n) (L.u n + L.S j n) := by
  apply L.S_le
  intro A hA hc
  by_cases hn : n ∈ A
  · rw [← Finset.add_sum_erase A L.u hn]
    have : ∑ i ∈ A.erase n, L.u i ≤ L.S j n := by
      apply L.le_S
      · intro i hi
        have h1 := hA (Finset.mem_of_mem_erase hi)
        have h2 := Finset.ne_of_mem_erase hi
        rw [mem_range] at h1 ⊢; omega
      · rw [Finset.card_erase_of_mem hn]; omega
    omega
  · have : ∑ i ∈ A, L.u i ≤ L.S (j + 1) n := by
      apply L.le_S _ hc
      intro i hi
      have h1 := hA hi
      rw [mem_range] at h1 ⊢
      have : i ≠ n := fun h => hn (h ▸ hi)
      omega
    omega

/-- The potential. -/
def ULib.Φ (n : ℕ) : ℕ := 4 * L.S 1 n + 2 * L.S 2 n + L.S 3 n + 28

theorem pow_ineq (d : ℕ) (hd : 1 ≤ d) : 4 ^ (d + 1) * 35 ≤ 5 ^ (d + 1) * 28 := by
  induction d with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num
    · have h := ih hk
      calc 4 ^ (k + 1 + 1) * 35 = 4 * (4 ^ (k + 1) * 35) := by ring
        _ ≤ 4 * (5 ^ (k + 1) * 28) := Nat.mul_le_mul_left _ h
        _ ≤ 5 * (5 ^ (k + 1) * 28) := Nat.mul_le_mul_right _ (by norm_num)
        _ = 5 ^ (k + 1 + 1) * 28 := by ring

theorem pow_ineq2 (d : ℕ) (hd : 10 ≤ d) : 4 ^ (d + 1) * (7 * d + 4) ≤ 7 * 5 ^ (d + 1) := by
  induction d with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 10 with hk | hk
    · have : k = 9 := by omega
      subst this; norm_num
    · have h := ih hk
      have hp : 0 < 4 ^ (k + 1) := by positivity
      calc 4 ^ (k + 1 + 1) * (7 * (k + 1) + 4) = 4 ^ (k + 1) * (4 * (7 * k + 11)) := by ring
        _ ≤ 4 ^ (k + 1) * (5 * (7 * k + 4)) := Nat.mul_le_mul_left _ (by omega)
        _ = 5 * (4 ^ (k + 1) * (7 * k + 4)) := by ring
        _ ≤ 5 * (7 * 5 ^ (k + 1)) := Nat.mul_le_mul_left _ h
        _ = 7 * 5 ^ (k + 1 + 1) := by ring

/-- The linear inequalities behind the potential, for `1 ≤ d ≤ 9` (certificates found by
`omega`). -/
theorem key_small (d : ℕ) (S : ℕ → ℕ) (hd1 : 1 ≤ d) (hd9 : d ≤ 9)
    (m12 : S 1 ≤ S 2) (m23 : S 2 ≤ S 3) (a11 : S 2 ≤ S 1 + S 1) (a21 : S 3 ≤ S 2 + S 1)
    (av2 : 2 * S 3 ≤ 3 * S 2) (a31 : S 4 ≤ S 3 + S 1) (a32 : S 5 ≤ S 3 + S 2)
    (a33 : S 6 ≤ S 3 + S 3) (a61 : S 7 ≤ S 6 + S 1) (a62 : S 8 ≤ S 6 + S 2)
    (a63 : S 9 ≤ S 6 + S 3) :
    4 ^ (d + 1) * (7 * S d + 2 * S 1 + S 2) ≤ 5 ^ (d + 1) * (4 * S 1 + 2 * S 2 + S 3) := by
  interval_cases d <;> norm_num <;> omega

/-- **One step.** Adding a result that cites `d` others multiplies the potential by at most
`(5/4)^(1+d)`. -/
theorem ULib.Φ_step (n : ℕ) :
    4 ^ (1 + (L.deps n).card) * L.Φ (n + 1) ≤ 5 ^ (1 + (L.deps n).card) * L.Φ n := by
  set d := (L.deps n).card with hd
  have hu := L.u_le_S n
  rw [← hd] at hu
  -- the three top sums after adding `n`
  have s1 : L.S 1 (n + 1) ≤ max (L.S 1 n) (L.u n + L.S 0 n) := L.S_succ 0 n
  have s2 : L.S 2 (n + 1) ≤ max (L.S 2 n) (L.u n + L.S 1 n) := L.S_succ 1 n
  have s3 : L.S 3 (n + 1) ≤ max (L.S 3 n) (L.u n + L.S 2 n) := L.S_succ 2 n
  rw [L.S_zero] at s1
  -- elementary facts about the old top sums
  have m12 := L.S_mono (j := 1) (k := 2) (n := n) (by norm_num)
  have m23 := L.S_mono (j := 2) (k := 3) (n := n) (by norm_num)
  have a11 : L.S 2 n ≤ L.S 1 n + L.S 1 n := L.S_add 1 1 n
  have a21 : L.S 3 n ≤ L.S 2 n + L.S 1 n := L.S_add 2 1 n
  have av2 : 2 * L.S 3 n ≤ 3 * L.S 2 n := L.S_avg 2 n
  unfold ULib.Φ
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · -- a leaf: `u n = 1`
    rw [h0, L.S_zero] at hu
    rw [h0]
    have b1 : L.S 1 (n + 1) ≤ L.S 1 n + 1 := le_trans s1 (max_le (by omega) (by omega))
    have b2 : L.S 2 (n + 1) ≤ L.S 2 n + 1 := le_trans s2 (max_le (by omega) (by omega))
    have b3 : L.S 3 (n + 1) ≤ L.S 3 n + 1 := le_trans s3 (max_le (by omega) (by omega))
    norm_num
    omega
  · -- the new sums are at most `1 + S d + S (j-1)`
    have md1 := L.S_mono (j := 1) (k := d) (n := n) hpos
    have t1 : L.S 1 (n + 1) ≤ 1 + L.S d n := le_trans s1 (max_le (by omega) (by omega))
    have t2 : L.S 2 (n + 1) ≤ 1 + L.S d n + L.S 1 n :=
      le_trans s2 (max_le (by omega) (by omega))
    have t3 : L.S 3 (n + 1) ≤ 1 + L.S d n + L.S 2 n :=
      le_trans s3 (max_le (by omega) (by omega))
    have hc := pow_ineq d hpos
    rw [add_comm 1 d]
    -- reduce to a linear inequality in the old top sums
    have key : 4 ^ (d + 1) * (7 * L.S d n + 2 * L.S 1 n + L.S 2 n) ≤
        5 ^ (d + 1) * (4 * L.S 1 n + 2 * L.S 2 n + L.S 3 n) := by
      rcases Nat.lt_or_ge d 10 with hlt | hge
      · exact key_small d (fun j => L.S j n) hpos (by omega) m12 m23 a11 a21 av2
          (L.S_add 3 1 n) (L.S_add 3 2 n) (L.S_add 3 3 n) (L.S_add 6 1 n) (L.S_add 6 2 n)
          (L.S_add 6 3 n)
      · have hsd : L.S d n ≤ d * L.S 1 n := by
          have : ∀ k, L.S k n ≤ k * L.S 1 n := by
            intro k
            induction k with
            | zero => rw [L.S_zero]; simp
            | succ k ih => have := L.S_add k 1 n; nlinarith
          exact this d
        have h2 := pow_ineq2 d hge
        have hp : 0 < 4 ^ (d + 1) := by positivity
        nlinarith
    have e1 : 4 ^ (d + 1) * (4 * L.S 1 (n + 1) + 2 * L.S 2 (n + 1) + L.S 3 (n + 1) + 28)
        ≤ 4 ^ (d + 1) * (7 * L.S d n + 2 * L.S 1 n + L.S 2 n + 35) := by
      apply Nat.mul_le_mul_left; omega
    nlinarith

theorem ULib.Φ_le (n : ℕ) : 4 ^ L.cost n * L.Φ n ≤ 28 * 5 ^ L.cost n := by
  induction n with
  | zero =>
    unfold ULib.Φ ULib.cost
    simp [ULib.S]
  | succ n ih =>
    have hs := L.Φ_step n
    have hcost : L.cost (n + 1) = L.cost n + (1 + (L.deps n).card) := by
      unfold ULib.cost; rw [Finset.sum_range_succ]
    rw [hcost, pow_add (4 : ℕ) (L.cost n), pow_add (5 : ℕ) (L.cost n)]
    calc 4 ^ L.cost n * 4 ^ (1 + (L.deps n).card) * L.Φ (n + 1)
        = 4 ^ L.cost n * (4 ^ (1 + (L.deps n).card) * L.Φ (n + 1)) := by ring
      _ ≤ 4 ^ L.cost n * (5 ^ (1 + (L.deps n).card) * L.Φ n) := Nat.mul_le_mul_left _ hs
      _ = 5 ^ (1 + (L.deps n).card) * (4 ^ L.cost n * L.Φ n) := by ring
      _ ≤ 5 ^ (1 + (L.deps n).card) * (28 * 5 ^ L.cost n) := Nat.mul_le_mul_left _ ih
      _ = 28 * (5 ^ L.cost n * 5 ^ (1 + (L.deps n).card)) := by ring

/-- **Speed limit.** Every unfolded size among the first `n` results is at most
`28 · (5/4)^(cost n)`. -/
theorem ULib.u_le (n i : ℕ) (hi : i < n) : 4 ^ L.cost n * L.u i ≤ 28 * 5 ^ L.cost n := by
  have h1 : L.u i ≤ L.S 1 n := by
    have := L.le_S (j := 1) (n := n) (A := {i}) (by simp [hi]) (by simp)
    simpa using this
  have h2 : L.u i ≤ L.Φ n := by unfold ULib.Φ; omega
  calc 4 ^ L.cost n * L.u i ≤ 4 ^ L.cost n * L.Φ n := Nat.mul_le_mul_left _ h2
    _ ≤ 28 * 5 ^ L.cost n := L.Φ_le n

/-! ### The golden lower bound -/

/-- Each result cites the two before it. -/
def fibLib : ULib where
  deps i := if i = 0 then ∅ else if i = 1 then {0} else {i - 1, i - 2}
  acyclic i j hj := by
    split_ifs at hj with h0 h1
    · simp at hj
    · simp at hj; omega
    · simp at hj; omega

theorem fibLib_deps (i : ℕ) : fibLib.deps (i + 2) = {i + 1, i} := by
  show (if i + 2 = 0 then ∅ else if i + 2 = 1 then {0} else {i + 2 - 1, i + 2 - 2}) = _
  rw [if_neg (by omega), if_neg (by omega)]
  congr 1

theorem fibLib_u : ∀ i, fibLib.u i = Nat.fib (i + 3) - 1
  | 0 => by rw [fibLib.u_eq, show fibLib.deps 0 = ∅ from rfl]; decide
  | 1 => by
    rw [fibLib.u_eq, show fibLib.deps 1 = {0} from rfl, Finset.sum_singleton, fibLib.u_eq,
      show fibLib.deps 0 = ∅ from rfl]
    decide
  | i + 2 => by
    rw [fibLib.u_eq, fibLib_deps, Finset.sum_pair (by omega), fibLib_u (i + 1), fibLib_u i]
    have h1 := Nat.fib_add_two (n := i + 3)
    have p1 : 1 ≤ Nat.fib (i + 3) := Nat.fib_pos.2 (by omega)
    have p2 : 1 ≤ Nat.fib (i + 4) := Nat.fib_pos.2 (by omega)
    rw [show i + 2 + 3 = i + 3 + 2 by ring, h1, show i + 1 + 3 = i + 4 by ring,
      show i + 3 + 1 = i + 4 by ring]
    omega

theorem fibLib_cost (n : ℕ) : fibLib.cost (n + 2) = 3 * (n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
    unfold ULib.cost at ih ⊢
    rw [Finset.sum_range_succ, ih, fibLib_deps, Finset.card_pair (by omega)]
    ring

/-- **Bounded readers reach exponentially far.** Every result of the Fibonacci library can be
read by an agent that holds only three symbols at a time (itself and two citations), yet the
`n`-th result unfolds to `F (n + 3) - 1` symbols. By `ULib.u_le`, no library can do better than
`28 · (5/4) ^ cost`. -/
theorem fibLib_readable (i : ℕ) : 1 + (fibLib.deps i).card ≤ 3 := by
  rcases Nat.lt_or_ge i 2 with h | h
  · interval_cases i <;> decide
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
    rw [fibLib_deps, Finset.card_pair (by omega)]

/-! ### The Lucas library: the conjectured extremum is attained -/

/-- Lucas numbers `2, 1, 3, 4, 7, 11, 18, …`. -/
def luc : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (n + 2) => luc (n + 1) + luc n

/-- A leaf, a two-step chain, a Fibonacci core, and a final result citing the top three. -/
def lucasLib (m : ℕ) : ULib where
  deps i := if i = 0 then ∅ else if i ≤ 2 then {i - 1} else if i < m then {i - 1, i - 2}
    else if i = m then {m - 1, m - 2, m - 3} else ∅
  acyclic i j hj := by
    split_ifs at hj with h0 h2 hm hm' <;> simp at hj <;> omega

theorem lucasLib_u (m : ℕ) : ∀ i, 1 ≤ i → i < m → (lucasLib m).u i = luc (i + 1) - 1 := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro h1 him
    have hu0 : (lucasLib m).u 0 = 1 := by
      rw [ULib.u_eq, show (lucasLib m).deps 0 = ∅ from rfl]; rfl
    rcases Nat.lt_or_ge i 3 with hi | hi
    · interval_cases i
      · rw [ULib.u_eq, show (lucasLib m).deps 1 = {0} by simp [lucasLib], Finset.sum_singleton, hu0]
        rfl
      · rw [ULib.u_eq, show (lucasLib m).deps 2 = {1} by simp [lucasLib], Finset.sum_singleton,
          ih 1 (by norm_num) le_rfl (by omega)]
        rfl
    · have hd : (lucasLib m).deps i = {i - 1, i - 2} := by
        simp only [lucasLib]
        rw [if_neg (by omega), if_neg (by omega), if_pos him]
      rw [ULib.u_eq, hd, Finset.sum_pair (by omega), ih (i - 1) (by omega) (by omega) (by omega),
        ih (i - 2) (by omega) (by omega) (by omega)]
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 3 := ⟨i - 3, by omega⟩
      simp only [show k + 3 - 1 + 1 = k + 3 by omega, show k + 3 - 2 + 1 = k + 2 by omega,
        show k + 3 + 1 = (k + 2) + 2 by omega]
      have hl : luc (k + 2 + 2) = luc (k + 3) + luc (k + 2) := rfl
      have p1 : 1 ≤ luc (k + 3) := by
        have : ∀ n, 1 ≤ luc n := by
          intro n
          induction n using Nat.strong_induction_on with
          | _ n ihn =>
            match n with
            | 0 => decide
            | 1 => decide
            | n + 2 => show 1 ≤ luc (n + 1) + luc n; have := ihn (n + 1) (by omega); omega
        exact this _
      have p2 : 1 ≤ luc (k + 2) := by
        have : ∀ n, 1 ≤ luc n := by
          intro n
          induction n using Nat.strong_induction_on with
          | _ n ihn =>
            match n with
            | 0 => decide
            | 1 => decide
            | n + 2 => show 1 ≤ luc (n + 1) + luc n; have := ihn (n + 1) (by omega); omega
        exact this _
      rw [hl, show k + 2 + 1 = k + 3 by omega]
      omega

/-- **The Lucas library reaches `2 L_m - 2` at named cost `3 m`.** We conjecture this is the
maximum possible unfolded size at that cost, for every `m ≥ 4`. -/
theorem lucasLib_top (m : ℕ) (hm : 4 ≤ m) : (lucasLib m).u m = 2 * luc m - 2 := by
  have hd : (lucasLib m).deps m = {m - 1, m - 2, m - 3} := by
    simp only [lucasLib]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp
  rw [ULib.u_eq, hd, Finset.sum_insert (by simp; omega), Finset.sum_pair (by omega),
    lucasLib_u m (m - 1) (by omega) (by omega), lucasLib_u m (m - 2) (by omega) (by omega),
    lucasLib_u m (m - 3) (by omega) (by omega)]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
  simp only [show k + 4 - 1 + 1 = k + 4 by omega, show k + 4 - 2 + 1 = k + 3 by omega,
    show k + 4 - 3 + 1 = k + 2 by omega]
  have h4 : luc (k + 4) = luc (k + 3) + luc (k + 2) := rfl
  have pos : ∀ n, 1 ≤ luc n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
      match n with
      | 0 => decide
      | 1 => decide
      | n + 2 => show 1 ≤ luc (n + 1) + luc n; have := ihn (n + 1) (by omega); omega
  have := pos (k + 2); have := pos (k + 3)
  omega

theorem lucasLib_cost (m : ℕ) (hm : 4 ≤ m) : (lucasLib m).cost (m + 1) = 3 * m := by
  have hc : ∀ i, (lucasLib m).deps i = (if i = 0 then ∅ else if i ≤ 2 then {i - 1}
      else if i < m then {i - 1, i - 2} else if i = m then {m - 1, m - 2, m - 3} else ∅) :=
    fun _ => rfl
  have step : ∀ n, 3 ≤ n → n ≤ m → (lucasLib m).cost n = 3 * n - 4 := by
    intro n h3 hn
    induction n with
    | zero => omega
    | succ k ih =>
      rcases Nat.lt_or_ge k 3 with hk | hk
      · have : k = 2 := by omega
        subst this
        unfold ULib.cost
        simp [Finset.sum_range_succ, hc]
      · unfold ULib.cost at ih ⊢
        rw [Finset.sum_range_succ, ih hk (by omega), hc k, if_neg (by omega), if_neg (by omega),
          if_pos (by omega), Finset.card_pair (by omega)]
        omega
  unfold ULib.cost
  rw [Finset.sum_range_succ]
  have := step m (by omega) le_rfl
  unfold ULib.cost at this
  rw [this, hc m, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl,
    Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (by omega)]
  omega

end SpeedLimit
