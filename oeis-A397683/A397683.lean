module

public import FormalConjecturesUtil

/-!
# OEIS A397683: when do consecutive residues with equal order exist?

For `m ≥ 2` let `f(m)` count the `x` with `1 ≤ x < m`, `gcd(x, m) = gcd(x+1, m) = 1` and
`ord_m(x) = ord_m(x+1)`. The OEIS entry conjectures that for odd `m > 1`, `f(m) = 0` if and
only if `m` is a power of 3 or a power of 7.

We prove this conjecture, assuming **Cohen's theorem** (S. D. Cohen, 1985): for every prime
`p > 7` there are consecutive primitive roots modulo `p`. That theorem rests on character-sum
estimates that are not in Mathlib, so it enters as an explicit hypothesis `CohenConsecutive`.
-/

@[expose] public section

namespace OeisA397683

open Nat

/-- `x^k ≡ 1 (mod n)`. -/
abbrev E (n x k : ℕ) : Prop := x ^ k ≡ 1 [MOD n]

lemma modEq_one_iff {q x : ℕ} (hx : 1 ≤ x) : x ≡ 1 [MOD q] ↔ q ∣ x - 1 :=
  Nat.ModEq.comm.trans (Nat.modEq_iff_dvd' hx)

/-- Bridge between `ZMod` and congruences. -/
lemma zmod_pow_eq_one_iff (n x k : ℕ) : ((x : ZMod n)) ^ k = 1 ↔ E n x k := by
  rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]

/-- **Profile lemma (lifting the exponent).** If `z` has order `d` modulo the odd prime `p`
and `p² ∤ z^d - 1`, then `z^k ≡ 1 (mod p^n)` iff `d * p^(n-1) ∣ k`. -/
lemma profile {p z d : ℕ} [hp : Fact p.Prime] (hodd : Odd p) (hz : ¬ p ∣ z) (hd : 0 < d)
    (hbase : ∀ k, E p z k ↔ d ∣ k) (hsq : ¬ E (p ^ 2) z d) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    E (p ^ n) z k ↔ d * p ^ (n - 1) ∣ k := by
  have hz0 : z ≠ 0 := by rintro rfl; exact hz (dvd_zero p)
  have hz1 : z ≠ 1 := by rintro rfl; exact hsq (by simp [E, Nat.ModEq.refl])
  have hz2 : 2 ≤ z := by omega
  have hzd : 1 < z ^ d := Nat.one_lt_pow hd.ne' (by omega)
  have hpd : p ∣ z ^ d - 1 := (modEq_one_iff hzd.le).1 ((hbase d).2 dvd_rfl)
  have hv1 : padicValNat p (z ^ d - 1) = 1 := by
    have hne : z ^ d - 1 ≠ 0 := by omega
    have h1 : 1 ≤ padicValNat p (z ^ d - 1) := (padicValNat_dvd_iff_le hne).1 (by simpa using hpd)
    have h2 : ¬ 2 ≤ padicValNat p (z ^ d - 1) := fun h =>
      hsq ((modEq_one_iff hzd.le).2 ((padicValNat_dvd_iff_le hne).2 h))
    omega
  have hpz : ¬ p ∣ z ^ d := fun h => hz (hp.out.dvd_of_dvd_pow h)
  -- the statement for `k = d * j`
  have hj : ∀ j, E (p ^ n) z (d * j) ↔ d * p ^ (n - 1) ∣ d * j := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [E, Nat.ModEq.refl]
    have hlt : 1 < (z ^ d) ^ j := Nat.one_lt_pow hj0.ne' hzd
    have hne : (z ^ d) ^ j - 1 ≠ 0 := by omega
    have hlte := padicValNat.pow_sub_pow (p := p) (x := z ^ d) (y := 1) hodd hzd
      (by simpa using hpd) hpz hj0.ne'
    simp only [one_pow] at hlte
    rw [E, pow_mul, modEq_one_iff hlt.le, padicValNat_dvd_iff_le hne, hlte, hv1,
      Nat.mul_dvd_mul_iff_left hd, padicValNat_dvd_iff_le hj0.ne']
    omega
  by_cases hdk : d ∣ k
  · obtain ⟨j, rfl⟩ := hdk; exact hj j
  · constructor
    · intro h
      exact absurd ((hbase k).1 (h.of_dvd (dvd_pow_self p (by omega)))) hdk
    · intro h; exact absurd (dvd_trans (dvd_mul_right d _) h) hdk

/-! ### Concrete profiles modulo powers of 3 and 7 -/

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

lemma orderOf_three_zmod7 : orderOf (3 : ZMod 7) = 6 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

lemma orderOf_four_zmod7 : orderOf (4 : ZMod 7) = 3 :=
  orderOf_eq_prime (by decide) (by decide)

lemma base_of_orderOf {p z d : ℕ} (h : orderOf (z : ZMod p) = d) (k : ℕ) : E p z k ↔ d ∣ k := by
  rw [← zmod_pow_eq_one_iff, ← h, orderOf_dvd_iff_pow_eq_one]

lemma prof3_4 {a : ℕ} (ha : 1 ≤ a) (k : ℕ) : E (3 ^ a) 4 k ↔ 3 ^ (a - 1) ∣ k := by
  have := profile (p := 3) (z := 4) (d := 1) (by decide) (by decide) one_pos
    (fun k => by
      simp only [one_dvd, iff_true]
      exact (Nat.ModEq.pow k (show 4 ≡ 1 [MOD 3] by decide)).trans (by simp [Nat.ModEq.refl]))
    (by decide) ha k
  simpa using this

lemma prof3_5 {a : ℕ} (ha : 1 ≤ a) (k : ℕ) : E (3 ^ a) 5 k ↔ 2 * 3 ^ (a - 1) ∣ k :=
  profile (p := 3) (z := 5) (d := 2) (by decide) (by decide) two_pos
    (fun k => by
      rw [← zmod_pow_eq_one_iff]
      have : ((5 : ℕ) : ZMod 3) = -1 := by decide
      rw [this, neg_one_pow_eq_one_iff_even (by decide), even_iff_two_dvd])
    (by decide) ha k

lemma prof7_3 {b : ℕ} (hb : 1 ≤ b) (k : ℕ) : E (7 ^ b) 3 k ↔ 6 * 7 ^ (b - 1) ∣ k :=
  profile (p := 7) (z := 3) (d := 6) (by decide) (by decide) (by norm_num)
    (base_of_orderOf (by exact_mod_cast orderOf_three_zmod7)) (by decide) hb k

lemma prof7_4 {b : ℕ} (hb : 1 ≤ b) (k : ℕ) : E (7 ^ b) 4 k ↔ 3 * 7 ^ (b - 1) ∣ k :=
  profile (p := 7) (z := 4) (d := 3) (by decide) (by decide) (by norm_num)
    (base_of_orderOf (by exact_mod_cast orderOf_four_zmod7)) (by decide) hb k


/-! ### Lifting consecutive primitive roots from `p` to `p^2` -/

/-- For fixed `y` with `p ∤ y`, at most one `t ∈ {0, 1, 2}` has `(y + t p)^(p-1) ≡ 1 (mod p²)`. -/
lemma lift_unique {p y t₁ t₂ : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hy : ¬ p ∣ y)
    (ht₁ : t₁ < 3) (ht₂ : t₂ < 3)
    (h₁ : E (p ^ 2) (y + t₁ * p) (p - 1)) (h₂ : E (p ^ 2) (y + t₂ * p) (p - 1)) : t₁ = t₂ := by
  set n := p - 1 with hn
  have hexp : ∀ t : ℕ, ((p : ℤ) ^ 2) ∣
      ((y : ℤ) + t * p) ^ n - (y : ℤ) ^ (n - 1) * (t * p) * n - (y : ℤ) ^ n := by
    intro t
    have := sq_dvd_add_pow_sub_sub ((t : ℤ) * p) (y : ℤ) n
    exact dvd_trans (by rw [mul_pow]; exact dvd_mul_left _ _) this
  have hz : ∀ t : ℕ, E (p ^ 2) (y + t * p) n → ((p : ℤ) ^ 2) ∣ ((y : ℤ) + t * p) ^ n - 1 := by
    intro t h
    have := (Nat.modEq_iff_dvd.1 h.symm)
    push_cast at this; exact this
  have hd : ((p : ℤ) ^ 2) ∣ (y : ℤ) ^ (n - 1) * p * n * ((t₁ : ℤ) - t₂) := by
    have e := dvd_sub (dvd_sub (hz t₁ h₁) (hz t₂ h₂)) (dvd_sub (hexp t₁) (hexp t₂))
    have key : (y : ℤ) ^ (n - 1) * p * n * ((t₁ : ℤ) - t₂) =
        (((y : ℤ) + t₁ * p) ^ n - 1 - (((y : ℤ) + t₂ * p) ^ n - 1)) -
        ((((y : ℤ) + t₁ * p) ^ n - (y : ℤ) ^ (n - 1) * (t₁ * p) * n - (y : ℤ) ^ n) -
         (((y : ℤ) + t₂ * p) ^ n - (y : ℤ) ^ (n - 1) * (t₂ * p) * n - (y : ℤ) ^ n)) := by ring
    rw [key]; exact e
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hd' : (p : ℤ) ∣ (y : ℤ) ^ (n - 1) * n * ((t₁ : ℤ) - t₂) := by
    have : (p : ℤ) * p ∣ (p : ℤ) * ((y : ℤ) ^ (n - 1) * n * ((t₁ : ℤ) - t₂)) := by
      convert hd using 1 <;> ring
    exact (mul_dvd_mul_iff_left (by exact_mod_cast hp.out.ne_zero)).1 this
  rcases hpz.dvd_or_dvd hd' with h | h
  · rcases hpz.dvd_or_dvd h with h | h
    · exact absurd (Int.natCast_dvd_natCast.1 (by exact_mod_cast hpz.dvd_of_dvd_pow h)) hy
    · have : p ∣ n := Int.natCast_dvd_natCast.1 h
      exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  · have h3 : ((t₁ : ℤ) - t₂).natAbs < p := by omega
    have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h (by simpa using h3)
    omega

lemma exists_good_lift {p y : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hy : ¬ p ∣ y)
    (hy1 : ¬ p ∣ y + 1) :
    ∃ t < 3, ¬ E (p ^ 2) (y + t * p) (p - 1) ∧ ¬ E (p ^ 2) (y + 1 + t * p) (p - 1) := by
  by_contra hcon
  push Not at hcon
  have key : ∀ t < 3, E (p ^ 2) (y + t * p) (p - 1) ∨ E (p ^ 2) (y + 1 + t * p) (p - 1) := by
    intro t ht; by_cases h : E (p ^ 2) (y + t * p) (p - 1)
    · exact Or.inl h
    · exact Or.inr (hcon t ht h)
  have U := fun {t₁ t₂ : ℕ} => @lift_unique p y t₁ t₂ _ hp5 hy
  have U1 := fun {t₁ t₂ : ℕ} => @lift_unique p (y + 1) t₁ t₂ _ hp5 hy1
  rcases key 0 (by norm_num) with h0 | h0 <;> rcases key 1 (by norm_num) with h1 | h1 <;>
    rcases key 2 (by norm_num) with h2 | h2 <;>
    first
    | exact absurd (U (by norm_num) (by norm_num) h0 h1) (by norm_num)
    | exact absurd (U (by norm_num) (by norm_num) h0 h2) (by norm_num)
    | exact absurd (U (by norm_num) (by norm_num) h1 h2) (by norm_num)
    | exact absurd (U1 (by norm_num) (by norm_num) h0 h1) (by norm_num)
    | exact absurd (U1 (by norm_num) (by norm_num) h0 h2) (by norm_num)
    | exact absurd (U1 (by norm_num) (by norm_num) h1 h2) (by norm_num)

/-! ### Prime-power components -/

lemma not_dvd_of_orderOf {p y : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (h : orderOf (y : ZMod p) = p - 1) : ¬ p ∣ y := by
  intro hd
  have h0 : (y : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff y p).2 hd
  rw [h0, orderOf_eq_zero_iff'.2 (fun n hn => by simp [zero_pow hn.ne'])] at h
  omega

lemma ppow_component {p n y₀ : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hn : 1 ≤ n)
    (h₀ : orderOf (y₀ : ZMod p) = p - 1) (h₁ : orderOf ((y₀ : ZMod p) + 1) = p - 1) :
    ∃ y, Coprime y (p ^ n) ∧ Coprime (y + 1) (p ^ n) ∧
      ∀ k, (E (p ^ n) y k ↔ (p - 1) * p ^ (n - 1) ∣ k) ∧
        (E (p ^ n) (y + 1) k ↔ (p - 1) * p ^ (n - 1) ∣ k) := by
  have h₁' : orderOf (((y₀ + 1 : ℕ)) : ZMod p) = p - 1 := by push_cast; exact h₁
  have hy := not_dvd_of_orderOf hp5 h₀
  have hy1 := not_dvd_of_orderOf hp5 h₁'
  obtain ⟨t, -, ht, ht'⟩ := exists_good_lift hp5 hy hy1
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  have hcast : ∀ z : ℕ, ((z + t * p : ℕ) : ZMod p) = (z : ZMod p) := by
    intro z; push_cast; simp
  have hnd : ∀ z : ℕ, ¬ p ∣ z → ¬ p ∣ z + t * p := fun z hz h =>
    hz ((Nat.dvd_add_right (dvd_mul_left p t)).1 (by simpa [add_comm] using h))
  have base : ∀ z : ℕ, orderOf (z : ZMod p) = p - 1 → ∀ k, E p (z + t * p) k ↔ (p - 1) ∣ k := by
    intro z hz k
    rw [← zmod_pow_eq_one_iff, hcast, ← hz, orderOf_dvd_iff_pow_eq_one]
  have P0 := fun k => profile hodd (hnd y₀ hy) (by omega) (base y₀ h₀) ht hn k
  have P1 := fun k => profile hodd (hnd (y₀ + 1) hy1) (by omega) (base (y₀ + 1) h₁') ht' hn k
  have cop : ∀ z : ℕ, ¬ p ∣ z → Coprime z (p ^ n) := fun z hz =>
    Nat.Coprime.pow_right n ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hz).symm
  refine ⟨y₀ + t * p, cop _ (hnd y₀ hy), ?_, fun k => ⟨P0 k, ?_⟩⟩
  · have := cop _ (hnd (y₀ + 1) hy1); rwa [show y₀ + 1 + t * p = y₀ + t * p + 1 by ring] at this
  · have := P1 k; rwa [show y₀ + 1 + t * p = y₀ + t * p + 1 by ring] at this

/-! ### Gluing with the Chinese remainder theorem -/

lemma E_congr {n x y : ℕ} (h : x ≡ y [MOD n]) (k : ℕ) : E n x k ↔ E n y k :=
  ⟨fun h' => (h.pow k).symm.trans h', fun h' => (h.pow k).trans h'⟩

lemma E_mul {a b x k : ℕ} (co : Coprime a b) : E (a * b) x k ↔ E a x k ∧ E b x k :=
  (Nat.modEq_and_modEq_iff_modEq_mul co).symm

lemma coprime_of_modEq {n x y : ℕ} (h : x ≡ y [MOD n]) (hy : Coprime y n) : Coprime x n := by
  unfold Nat.Coprime; rw [h.gcd_eq]; exact hy

/-- **Cohen's theorem** (1985), taken as a hypothesis: for every prime `p > 7` there are
consecutive primitive roots modulo `p`. -/
def CohenConsecutive : Prop :=
  ∀ p : ℕ, p.Prime → 7 < p → ∃ y : ZMod p, orderOf y = p - 1 ∧ orderOf (y + 1) = p - 1

lemma orderOf_two_zmod5 : orderOf (2 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

lemma orderOf_three_zmod5 : orderOf (3 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

/-- The part of the modulus coprime to `2·3·7`: an `x` exists for each such `r > 1`, and in
fact one whose common order is even. -/
lemma r_component (hC : CohenConsecutive) : ∀ r : ℕ, Odd r → Coprime r 21 → 1 < r →
    ∃ y, Coprime y r ∧ Coprime (y + 1) r ∧ ∀ k, (E r y k ↔ E r (y + 1) k) ∧ (E r y k → 2 ∣ k) := by
  intro r
  induction r using Nat.recOnPrimeCoprime with
  | zero => intro h; exact absurd h (by decide)
  | prime_pow p n hp =>
    intro hodd hco h1
    have : Fact p.Prime := ⟨hp⟩
    have hn : 1 ≤ n := by
      rcases n with _ | n
      · simp at h1
      · omega
    have hpd : p ∣ p ^ n := dvd_pow_self p (by omega)
    have hp2 : p ≠ 2 := by
      rintro rfl; exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hpd)
    have hp3 : p ≠ 3 := by
      rintro rfl; exact absurd (Nat.Coprime.coprime_dvd_left hpd hco) (by decide)
    have hp7 : p ≠ 7 := by
      rintro rfl; exact absurd (Nat.Coprime.coprime_dvd_left hpd hco) (by decide)
    have hp5 : 5 ≤ p := by
      have := hp.two_le
      rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
      · exact absurd h hp2
      · exact absurd h hp3
      · exact absurd (h ▸ hp) (by decide)
      · exact h
    obtain ⟨y₀, h₀, h₁⟩ : ∃ y₀ : ℕ, orderOf (y₀ : ZMod p) = p - 1 ∧
        orderOf ((y₀ : ZMod p) + 1) = p - 1 := by
      have hp6 : p ≠ 6 := by rintro rfl; exact absurd hp (by decide)
      rcases (show p = 5 ∨ 7 < p by omega) with rfl | hgt
      · exact ⟨2, by exact_mod_cast orderOf_two_zmod5, by
          have : ((2 : ℕ) : ZMod 5) + 1 = 3 := rfl
          rw [this]; exact orderOf_three_zmod5⟩
      · obtain ⟨y, hy, hy'⟩ := hC p hp hgt
        exact ⟨y.val, by simpa using hy, by simpa using hy'⟩
    obtain ⟨y, c0, c1, hy⟩ := ppow_component hp5 hn h₀ h₁
    refine ⟨y, c0, c1, fun k => ⟨(hy k).1.trans (hy k).2.symm, fun h => ?_⟩⟩
    have h2 : 2 ∣ p - 1 := by
      have := hp.odd_of_ne_two hp2
      obtain ⟨j, hj⟩ := this; exact ⟨j, by omega⟩
    exact dvd_trans (dvd_trans h2 (dvd_mul_right _ _)) ((hy k).1.1 h)
  | coprime a b ha hb hab iha ihb =>
    intro hodd hco _
    have hoa : Odd a := (Nat.odd_mul.1 hodd).1
    have hob : Odd b := (Nat.odd_mul.1 hodd).2
    have hca : Coprime a 21 := Nat.Coprime.coprime_dvd_left (dvd_mul_right a b) hco
    have hcb : Coprime b 21 := Nat.Coprime.coprime_dvd_left (dvd_mul_left b a) hco
    obtain ⟨ya, ca0, ca1, hya⟩ := iha hoa hca ha
    obtain ⟨yb, cb0, cb1, hyb⟩ := ihb hob hcb hb
    obtain ⟨y, hya', hyb'⟩ := Nat.chineseRemainder hab ya yb
    have hya1 : y + 1 ≡ ya + 1 [MOD a] := hya'.add_right 1
    have hyb1 : y + 1 ≡ yb + 1 [MOD b] := hyb'.add_right 1
    refine ⟨y, Nat.Coprime.mul_right (coprime_of_modEq hya' ca0) (coprime_of_modEq hyb' cb0),
      Nat.Coprime.mul_right (coprime_of_modEq hya1 ca1) (coprime_of_modEq hyb1 cb1),
      fun k => ⟨?_, ?_⟩⟩
    · rw [E_mul hab, E_mul hab, E_congr hya', E_congr hyb', E_congr hya1, E_congr hyb1,
        (hya k).1, (hyb k).1]
    · intro h
      rw [E_mul hab, E_congr hya'] at h
      exact (hya k).2 h.1

/-! ### Pure powers of 3 and 7 have no such `x` -/

lemma E_of_dvd_sub {p n z d : ℕ} (hn : 1 ≤ n) (h : z ^ d ≡ 1 [MOD p]) :
    E (p ^ n) z (d * p ^ (n - 1)) := by
  have h' : ((p : ℤ)) ∣ ((z : ℤ) ^ d) - 1 := by
    have := Nat.modEq_iff_dvd.1 h.symm; push_cast at this; exact this
  have := dvd_sub_pow_of_dvd_sub h' (n - 1)
  rw [one_pow, ← pow_mul, show n - 1 + 1 = n by omega] at this
  refine (Nat.modEq_iff_dvd.2 ?_).symm
  push_cast; exact this

lemma not_E_of_mod {p n z K : ℕ} (hn : 1 ≤ n) (h : ¬ ((z : ZMod p)) ^ K = 1) : ¬ E (p ^ n) z K := by
  intro hE
  apply h
  rw [zmod_pow_eq_one_iff]
  exact hE.of_dvd (dvd_pow_self p (by omega))

lemma no_three {a x : ℕ} (ha : 1 ≤ a) (c0 : Coprime x (3 ^ a)) (c1 : Coprime (x + 1) (3 ^ a)) :
    ¬ ∀ k, E (3 ^ a) x k ↔ E (3 ^ a) (x + 1) k := by
  have d3 : (3 : ℕ) ∣ 3 ^ a := dvd_pow_self 3 (by omega)
  have n0 : ¬ 3 ∣ x := fun h => absurd (Nat.Coprime.coprime_dvd_right d3 c0)
    (by rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by norm_num)]; simpa using h)
  have n1 : ¬ 3 ∣ x + 1 := fun h => absurd (Nat.Coprime.coprime_dvd_right d3 c1)
    (by rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by norm_num)]; simpa using h)
  have hx : x % 3 = 1 := by omega
  intro H
  have htrue : E (3 ^ a) x (1 * 3 ^ (a - 1)) :=
    E_of_dvd_sub ha (by simpa [Nat.ModEq] using hx)
  have hfalse : ¬ E (3 ^ a) (x + 1) (1 * 3 ^ (a - 1)) := by
    apply not_E_of_mod ha
    have : ((x + 1 : ℕ) : ZMod 3) = -1 := by
      rw [← ZMod.natCast_mod, show (x + 1) % 3 = 2 by omega]; decide
    rw [this, one_mul, Odd.neg_one_pow (Odd.pow (by decide))]; decide
  exact hfalse ((H _).1 htrue)

lemma pow_exp_mod_six (c : ZMod 7) (hc : c ^ 6 = 1) (d b : ℕ) : c ^ (d * 7 ^ b) = c ^ d := by
  rw [pow_eq_pow_mod _ hc, pow_eq_pow_mod d hc, Nat.mul_mod, Nat.pow_mod]
  norm_num

lemma no_seven {b x : ℕ} (hb : 1 ≤ b) (c0 : Coprime x (7 ^ b)) (c1 : Coprime (x + 1) (7 ^ b)) :
    ¬ ∀ k, E (7 ^ b) x k ↔ E (7 ^ b) (x + 1) k := by
  have d7 : (7 : ℕ) ∣ 7 ^ b := dvd_pow_self 7 (by omega)
  have n0 : ¬ 7 ∣ x := fun h => absurd (Nat.Coprime.coprime_dvd_right d7 c0)
    (by rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by norm_num)]; simpa using h)
  have n1 : ¬ 7 ∣ x + 1 := fun h => absurd (Nat.Coprime.coprime_dvd_right d7 c1)
    (by rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by norm_num)]; simpa using h)
  intro H
  have cx : ((x : ℕ) : ZMod 7) = ((x % 7 : ℕ) : ZMod 7) := (ZMod.natCast_mod x 7).symm
  have cx1 : ((x + 1 : ℕ) : ZMod 7) = (((x + 1) % 7 : ℕ) : ZMod 7) := (ZMod.natCast_mod _ 7).symm
  -- generic shape: one side has `z^d ≡ 1 (mod 7)`, the other side does not
  have side : ∀ (z w d : ℕ), (z % 7 : ℕ) ^ d % 7 = 1 → ((((w % 7 : ℕ)) : ZMod 7)) ^ 6 = 1 →
      ¬ ((((w % 7 : ℕ)) : ZMod 7)) ^ d = 1 →
      E (7 ^ b) z (d * 7 ^ (b - 1)) ∧ ¬ E (7 ^ b) w (d * 7 ^ (b - 1)) := by
    intro z w d hz hw6 hwd
    refine ⟨E_of_dvd_sub hb ?_, not_E_of_mod hb ?_⟩
    · show z ^ d % 7 = 1 % 7; rw [Nat.pow_mod]; simpa using hz
    · rw [← ZMod.natCast_mod w 7, pow_exp_mod_six _ hw6]; exact hwd
  have hr : x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 3 ∨ x % 7 = 4 ∨ x % 7 = 5 := by omega
  rcases hr with h | h | h | h | h
  · obtain ⟨t, f⟩ := side x (x + 1) 1 (by simp [h]) (by rw [show (x+1) % 7 = 2 by omega]; decide)
      (by rw [show (x+1) % 7 = 2 by omega]; decide)
    exact f ((H _).1 t)
  · obtain ⟨t, f⟩ := side x (x + 1) 3 (by simp [h]) (by rw [show (x+1) % 7 = 3 by omega]; decide)
      (by rw [show (x+1) % 7 = 3 by omega]; decide)
    exact f ((H _).1 t)
  · obtain ⟨t, f⟩ := side (x + 1) x 3 (by rw [show (x+1) % 7 = 4 by omega]; norm_num) (by rw [h]; decide)
      (by rw [h]; decide)
    exact f ((H _).2 t)
  · obtain ⟨t, f⟩ := side x (x + 1) 3 (by simp [h]) (by rw [show (x+1) % 7 = 5 by omega]; decide)
      (by rw [show (x+1) % 7 = 5 by omega]; decide)
    exact f ((H _).1 t)
  · obtain ⟨t, f⟩ := side (x + 1) x 2 (by rw [show (x+1) % 7 = 6 by omega]; norm_num) (by rw [h]; decide)
      (by rw [h]; decide)
    exact f ((H _).2 t)

/-! ### Assembly -/

lemma E_one (x k : ℕ) : E 1 x k := Nat.modEq_one

lemma E3_4 (a k : ℕ) : E (3 ^ a) 4 k ↔ (a = 0 ∨ 3 ^ (a - 1) ∣ k) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [E_one]
  · rw [prof3_4 ha]; simp [ha.ne']

lemma E3_5 (a k : ℕ) : E (3 ^ a) 5 k ↔ (a = 0 ∨ 2 * 3 ^ (a - 1) ∣ k) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [E_one]
  · rw [prof3_5 ha]; simp [ha.ne']

lemma E7_3 (b k : ℕ) : E (7 ^ b) 3 k ↔ (b = 0 ∨ 6 * 7 ^ (b - 1) ∣ k) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [E_one]
  · rw [prof7_3 hb]; simp [hb.ne']

lemma E7_4 (b k : ℕ) : E (7 ^ b) 4 k ↔ (b = 0 ∨ 3 * 7 ^ (b - 1) ∣ k) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [E_one]
  · rw [prof7_4 hb]; simp [hb.ne']

lemma two_mul_dvd_iff {c k : ℕ} (hc : Odd c) : 2 * c ∣ k ↔ 2 ∣ k ∧ c ∣ k :=
  ⟨fun h => ⟨dvd_trans (dvd_mul_right 2 c) h, dvd_trans (dvd_mul_left c 2) h⟩,
    fun h => Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.coprime_two_left.2 hc) h.1 h.2⟩

/-- Existence of `x` for every odd `m > 1` that is not a power of 3 or of 7. -/
theorem exists_of_not_pow (hC : CohenConsecutive) {m : ℕ} (hm : 1 < m) (hodd : Odd m)
    (h3 : ¬ ∃ a, m = 3 ^ a) (h7 : ¬ ∃ b, m = 7 ^ b) :
    ∃ x, Coprime x m ∧ Coprime (x + 1) m ∧ ∀ k, E m x k ↔ E m (x + 1) k := by
  set a := m.factorization 3
  set m₁ := m / 3 ^ a
  set b := m₁.factorization 7
  set r := m₁ / 7 ^ b
  have hm0 : m ≠ 0 := by omega
  have e1 : 3 ^ a * m₁ = m := Nat.ordProj_mul_ordCompl_eq_self m 3
  have hm₁0 : m₁ ≠ 0 := by rintro h; rw [h, mul_zero] at e1; omega
  have e2 : 7 ^ b * r = m₁ := Nat.ordProj_mul_ordCompl_eq_self m₁ 7
  have co3 : Coprime 3 m₁ := Nat.coprime_ordCompl Nat.prime_three hm0
  have co7 : Coprime 7 r := Nat.coprime_ordCompl (by norm_num) hm₁0
  have hrm₁ : r ∣ m₁ := ⟨7 ^ b, by rw [← e2, mul_comm]⟩
  have hrm : r ∣ m := dvd_trans hrm₁ ⟨3 ^ a, by rw [← e1, mul_comm]⟩
  have hr0 : r ≠ 0 := by rintro h; rw [h, mul_zero] at e2; exact hm₁0 e2.symm
  have coA : Coprime (3 ^ a) (7 ^ b * r) := by rw [e2]; exact co3.pow_left a
  have coB : Coprime (7 ^ b) r := co7.pow_left b
  have co3r : Coprime 3 r := Nat.Coprime.coprime_dvd_right hrm₁ co3
  have cor21 : Coprime r 21 := Nat.Coprime.mul_right co3r.symm co7.symm
  have hoddr : Odd r := Odd.of_dvd_nat hodd hrm
  have hmeq : m = 3 ^ a * (7 ^ b * r) := by rw [e2, e1]
  -- the component modulo `r`
  obtain ⟨yr, cr0, cr1, hR, hev⟩ : ∃ yr, Coprime yr r ∧ Coprime (yr + 1) r ∧
      (∀ k, E r yr k ↔ E r (yr + 1) k) ∧ (1 < r → ∀ k, E r yr k → 2 ∣ k) := by
    rcases (show r = 1 ∨ 1 < r from (Nat.one_le_iff_ne_zero.2 hr0).eq_or_lt') with h | h
    · exact ⟨0, by simp [h], by simp [h], fun k => by simp [h, E_one], fun h' => absurd (h ▸ h') (lt_irrefl 1)⟩
    · obtain ⟨y, c0, c1, hy⟩ := r_component hC r hoddr cor21 h
      exact ⟨y, c0, c1, fun k => (hy k).1, fun _ k => (hy k).2⟩
  -- glue
  obtain ⟨y, hy7, hyr⟩ := Nat.chineseRemainder coB 3 yr
  obtain ⟨x, hx3, hxy⟩ := Nat.chineseRemainder coA 4 y
  have hx3' : x + 1 ≡ 5 [MOD 3 ^ a] := hx3.add_right 1
  have hxy' : x + 1 ≡ y + 1 [MOD 7 ^ b * r] := hxy.add_right 1
  have hy7' : y + 1 ≡ 4 [MOD 7 ^ b] := hy7.add_right 1
  have hyr' : y + 1 ≡ yr + 1 [MOD r] := hyr.add_right 1
  have c3 : ∀ z : ℕ, Coprime z 3 → Coprime z (3 ^ a) := fun z h => h.pow_right a
  have c7 : ∀ z : ℕ, Coprime z 7 → Coprime z (7 ^ b) := fun z h => h.pow_right b
  refine ⟨x, ?_, ?_, fun k => ?_⟩
  · rw [hmeq]
    exact Nat.Coprime.mul_right (coprime_of_modEq hx3 (c3 4 (by decide)))
      (coprime_of_modEq hxy (Nat.Coprime.mul_right (coprime_of_modEq hy7 (c7 3 (by decide)))
        (coprime_of_modEq hyr cr0)))
  · rw [hmeq]
    exact Nat.Coprime.mul_right (coprime_of_modEq hx3' (c3 5 (by decide)))
      (coprime_of_modEq hxy' (Nat.Coprime.mul_right (coprime_of_modEq hy7' (c7 4 (by decide)))
        (coprime_of_modEq hyr' cr1)))
  rw [hmeq, E_mul coA, E_mul coA, E_congr hx3, E_congr hx3', E_congr hxy, E_congr hxy',
    E_mul coB, E_mul coB, E_congr hy7, E_congr hy7', E_congr hyr, E_congr hyr',
    E3_4, E3_5, E7_3, E7_4, ← hR k]
  have o3 : Odd (3 ^ (a - 1)) := Odd.pow (by decide)
  have o7 : Odd (3 * 7 ^ (b - 1)) := Odd.mul (by decide) (Odd.pow (by decide))
  rw [two_mul_dvd_iff o3, show 6 * 7 ^ (b - 1) = 2 * (3 * 7 ^ (b - 1)) by ring,
    two_mul_dvd_iff o7]
  -- remaining propositional reasoning, by cases on `a`, `b`
  rcases Nat.eq_zero_or_pos a with ha | ha <;> rcases Nat.eq_zero_or_pos b with hb | hb
  · have hr1 : 1 < r := by rw [hmeq, ha, hb] at hm; simpa using hm
    have := hev hr1 k; simp only [ha, hb, true_or, true_and]
  · have hr1 : 1 < r := by
      by_contra hr; apply h7
      have hr1 : r = 1 := le_antisymm (not_lt.1 hr) (Nat.pos_of_ne_zero hr0)
      exact ⟨b, by rw [hmeq, ha, hr1]; simp⟩
    have := hev hr1 k; simp only [ha, hb.ne', true_or, false_or, true_and]; tauto
  · have hr1 : 1 < r := by
      by_contra hr; apply h3
      have hr1 : r = 1 := le_antisymm (not_lt.1 hr) (Nat.pos_of_ne_zero hr0)
      exact ⟨a, by rw [hmeq, hb, hr1]; simp⟩
    have := hev hr1 k; simp only [ha.ne', hb, true_or, false_or]; tauto
  · simp only [ha.ne', hb.ne', false_or]; tauto

/-- Orders agree iff the sets of exponents killing them agree. -/
lemma orderOf_eq_iff_E (m x : ℕ) :
    orderOf (x : ZMod m) = orderOf ((x : ZMod m) + 1) ↔ ∀ k, E m x k ↔ E m (x + 1) k := by
  rw [orderOf_eq_orderOf_iff]
  have : (x : ZMod m) + 1 = ((x + 1 : ℕ) : ZMod m) := by push_cast; rfl
  rw [this]; simp only [zmod_pow_eq_one_iff]

/-- The OEIS function: `f(m)` counts `1 ≤ x < m` with `x`, `x+1` units of equal order. -/
noncomputable def f (m : ℕ) : ℕ :=
  ((Finset.range m).filter (fun x => 1 ≤ x ∧ Coprime x m ∧ Coprime (x + 1) m ∧
    orderOf (x : ZMod m) = orderOf ((x : ZMod m) + 1))).card

/-- **Main theorem** (the conjecture of OEIS A397683, assuming Cohen's theorem): for odd
`m > 1`, `f(m) = 0` iff `m` is a power of 3 or a power of 7. -/
theorem conjecture (hC : CohenConsecutive) {m : ℕ} (hm : 1 < m) (hodd : Odd m) :
    f m = 0 ↔ (∃ a, m = 3 ^ a) ∨ (∃ b, m = 7 ^ b) := by
  rw [f, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    by_contra hpow
    push Not at hpow
    obtain ⟨x, c0, c1, hx⟩ := exists_of_not_pow hC hm hodd
      (fun ⟨a, ha⟩ => hpow.1 a ha) (fun ⟨b, hb⟩ => hpow.2 b hb)
    have hxm : x % m ≡ x [MOD m] := Nat.mod_modEq x m
    have c0' : Coprime (x % m) m := coprime_of_modEq hxm c0
    have c1' : Coprime (x % m + 1) m := coprime_of_modEq (hxm.add_right 1) c1
    have hpos : 1 ≤ x % m := by
      by_contra h0
      have : x % m = 0 := by omega
      rw [this, Nat.coprime_zero_left] at c0'; omega
    apply h (Finset.mem_range.2 (Nat.mod_lt x (by omega)))
    refine ⟨hpos, c0', c1', ?_⟩
    rw [orderOf_eq_iff_E]
    intro k
    rw [E_congr hxm, E_congr (hxm.add_right 1)]
    exact hx k
  · rintro hpow x - ⟨-, c0, c1, hord⟩
    rw [orderOf_eq_iff_E] at hord
    rcases hpow with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · have ha : 1 ≤ a := by
        rcases Nat.eq_zero_or_pos a with rfl | h
        · simp at hm
        · exact h
      exact no_three ha c0 c1 hord
    · have hb : 1 ≤ b := by
        rcases Nat.eq_zero_or_pos b with rfl | h
        · simp at hm
        · exact h
      exact no_seven hb c0 c1 hord

end OeisA397683

