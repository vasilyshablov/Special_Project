import Mathlib

/-!
# Fruitfulness as compression: what naming a concept buys

Model: a *library* is a set of named results indexed by `ℕ`. Result `i` has its own
proof of size `size i` and cites the earlier results `deps i` (every `j ∈ deps i` has
`j < i`). The *unfolded size* of `i` is the size of its proof if every result it cites
were re-proved in place instead of named:

  `unfold i = size i + ∑ j ∈ deps i, unfold j`.

Main results:

* `naming_saves`, `naming_pays_iff`: naming a sub-proof of size `b` used `k` times saves
  exactly `(k - 1) * (b - 1) - 1` symbols, so it pays off iff `(k - 1) * (b - 1) > 1`.
* `unfold_le`: unfolding is at most exponential: with sizes `≤ S` and at most `d`
  citations per result, `unfold i ≤ S * (d + 1) ^ (i + 1)`.
* `fibLib_unfold`, `fibLib_unfold_ge`: this exponential gap is really attained. In the
  Fibonacci library, where each result cites the two before it, the named library has
  linear total size, but `unfold i = fib (i + 3) - 1 ≥ 2 ^ (i / 2)`.

The upshot: named concepts can make mathematics exponentially shorter, and never by more
than exponentially. The value of a single named concept is the explicit quantity
`(k - 1) * (b - 1) - 1`.
-/

namespace Fruitfulness

/-! ## 1. The accounting of a single named concept -/

/-- Inlining a sub-proof of size `b` at `k` places costs `k * b`. Naming it costs `b` for
the definition plus `1` per reference. The saving is `(k - 1)(b - 1) - 1`. -/
theorem naming_saves (k b : ℤ) : k * b - (b + k) = (k - 1) * (b - 1) - 1 := by ring

theorem naming_pays_iff (k b : ℤ) : b + k < k * b ↔ 1 < (k - 1) * (b - 1) := by
  have := naming_saves k b
  constructor <;> intro h <;> linarith

/-- A concept used at least twice whose proof has size at least three always pays. -/
theorem naming_pays_of (k b : ℕ) (hk : 2 ≤ k) (hb : 3 ≤ b) : b + k < k * b := by
  have h := (naming_pays_iff (k : ℤ) (b : ℤ)).2 (by
    have h1 : (1 : ℤ) ≤ (k : ℤ) - 1 := by omega
    have h2 : (2 : ℤ) ≤ (b : ℤ) - 1 := by omega
    nlinarith)
  exact_mod_cast h

/-- A concept used once never pays: naming it costs exactly one extra symbol. -/
theorem naming_once (b : ℤ) : (b + 1) - 1 * b = 1 := by ring

/-! ## 2. Libraries and unfolded size -/

/-- A library of named results. -/
structure Library where
  size : ℕ → ℕ
  deps : ℕ → Finset ℕ
  acyclic : ∀ i, ∀ j ∈ deps i, j < i

/-- Size of the proof of result `i` with every citation re-proved in place. -/
def Library.unfold (L : Library) (i : ℕ) : ℕ :=
  L.size i + ∑ j ∈ L.deps i, if j < i then L.unfold j else 0
termination_by i
decreasing_by assumption

theorem Library.unfold_eq (L : Library) (i : ℕ) :
    L.unfold i = L.size i + ∑ j ∈ L.deps i, L.unfold j := by
  rw [Library.unfold]
  congr 1
  exact Finset.sum_congr rfl fun j hj => if_pos (L.acyclic i j hj)

theorem Library.size_le_unfold (L : Library) (i : ℕ) : L.size i ≤ L.unfold i := by
  rw [L.unfold_eq]; omega

/-- Unfolding blows up at most exponentially. -/
theorem Library.unfold_le (L : Library) (S d : ℕ) (hS : ∀ i, L.size i ≤ S)
    (hd : ∀ i, (L.deps i).card ≤ d) : ∀ i, L.unfold i ≤ S * (d + 1) ^ (i + 1) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rw [L.unfold_eq]
    have hsum : ∑ j ∈ L.deps i, L.unfold j ≤ ∑ _j ∈ L.deps i, S * (d + 1) ^ i := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' := L.acyclic i j hj
      calc L.unfold j ≤ S * (d + 1) ^ (j + 1) := ih j hj'
        _ ≤ S * (d + 1) ^ i :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hj')
    rw [Finset.sum_const, smul_eq_mul] at hsum
    have hcard := Nat.mul_le_mul_right (S * (d + 1) ^ i) (hd i)
    calc L.size i + ∑ j ∈ L.deps i, L.unfold j
        ≤ S + d * (S * (d + 1) ^ i) := by have := hS i; omega
      _ ≤ S * (d + 1) ^ i + d * (S * (d + 1) ^ i) := by
          have : S ≤ S * (d + 1) ^ i :=
            Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
          omega
      _ = S * (d + 1) ^ (i + 1) := by ring

/-! ## 3. The Fibonacci library: the exponential gap is attained -/

/-- Each result cites the two results before it; every own proof has size one. -/
def fibLib : Library where
  size _ := 1
  deps i := if i = 0 then ∅ else if i = 1 then {0} else {i - 1, i - 2}
  acyclic i j hj := by
    split_ifs at hj with h0 h1
    · simp at hj
    · simp at hj; omega
    · simp at hj; omega

@[simp] theorem fibLib_size (i : ℕ) : fibLib.size i = 1 := rfl
theorem fibLib_deps0 : fibLib.deps 0 = ∅ := rfl
theorem fibLib_deps1 : fibLib.deps 1 = {0} := rfl
theorem fibLib_deps (i : ℕ) : fibLib.deps (i + 2) = {i + 1, i} := by
  simp only [fibLib]
  rw [if_neg (by omega), if_neg (by omega)]
  congr 1

theorem fibLib_rec (i : ℕ) :
    fibLib.unfold (i + 2) = 1 + fibLib.unfold (i + 1) + fibLib.unfold i := by
  rw [fibLib.unfold_eq, fibLib_deps, Finset.sum_pair (by omega), fibLib_size]; ring

theorem fibLib_unfold : ∀ i, fibLib.unfold i = Nat.fib (i + 3) - 1
  | 0 => by rw [fibLib.unfold_eq, fibLib_deps0]; decide
  | 1 => by
    rw [fibLib.unfold_eq, fibLib_deps1, Finset.sum_singleton, fibLib.unfold_eq, fibLib_deps0]
    decide
  | i + 2 => by
    rw [fibLib_rec, fibLib_unfold (i + 1), fibLib_unfold i]
    have h1 := Nat.fib_add_two (n := i + 3)
    have p1 : 1 ≤ Nat.fib (i + 3) := Nat.fib_pos.2 (by omega)
    have p2 : 1 ≤ Nat.fib (i + 4) := Nat.fib_pos.2 (by omega)
    rw [show i + 2 + 3 = i + 3 + 2 by ring, h1, show i + 1 + 3 = i + 4 by ring,
      show i + 3 + 1 = i + 4 by ring]
    omega

/-- The named Fibonacci library up to `n` has total size `n + 1` (one symbol per result),
plus at most two references per result; unfolded, result `n` alone has size at least
`2 ^ (n / 2)`. -/
theorem fibLib_unfold_ge : ∀ i, 2 ^ (i / 2) ≤ fibLib.unfold i
  | 0 => by rw [fibLib_unfold]; decide
  | 1 => by rw [fibLib_unfold]; decide
  | i + 2 => by
    have ih := fibLib_unfold_ge i
    have hmono : fibLib.unfold i ≤ fibLib.unfold (i + 1) := by
      rw [fibLib_unfold, fibLib_unfold]
      have := Nat.fib_mono (show i + 3 ≤ i + 1 + 3 by omega)
      omega
    have hrec := fibLib_rec i
    rw [show (i + 2) / 2 = i / 2 + 1 by omega, pow_succ]
    omega

end Fruitfulness
