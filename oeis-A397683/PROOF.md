# Proof of the conjecture in OEIS A397683

**Setting.** For m ≥ 2 let f(m) be the number of x with 1 ≤ x < m such that
gcd(x, m) = gcd(x+1, m) = 1 and ord_m(x) = ord_m(x+1). Every unit modulo an even m is odd,
so f(m) = 0 for even m.

**Conjecture** (D. S. González May, OEIS A397683, Sep 2026). For odd m > 1, f(m) = 0 if and
only if m is a power of 3 or a power of 7.

**Status of prior work (checked 9 Oct 2026).**
- *OEIS:* the entry history shows the last edit on 20 Sep 2026, with no proof. Only the case
  gcd(m, 21) = 1 is settled in the entry's comments.
- *Other sources, with no matches:* formal-conjectures, the-omega-institute/trureturing (issues
  and PRs) and a web search.

**Input used.** S. D. Cohen (1985): F_q contains two consecutive primitive elements for every
q > 7. This is restated in Cohen–Oliveira e Silva–Trudgian, arXiv:1410.6210, introduction.

## Proof

**(⇐) Pure powers.**
- *m = 3^a, a ≥ 1:* x and x+1 are units mod 3 only if x ≡ 1 (mod 3). Then ord(x) divides
  3^{a−1}, which is odd. But (x+1)^odd ≡ 2 (mod 3), so ord(x+1) is even.
- *m = 7^b, b ≥ 1:* the units mod 7^b form a cyclic group, and the prime-to-7 part of
  ord_{7^b}(x) equals ord_7(x). Mod 7, the consecutive pairs (x, x+1) for x = 1, …, 5 have
  orders (1,3), (3,6), (6,3), (3,6), (6,2). These are never equal, so f(7^b) = 0.

**(⇒) Every other odd m > 1.** Write m = 3^a · 7^b · r with gcd(r, 21) = 1, where
(a ≥ 1 and b ≥ 1) or r > 1. Choose x by CRT as follows.

- *Modulo 3^a (if a ≥ 1):* take x ≡ 4. Then ord(4) = 3^{a−1} and ord(5) = 2·3^{a−1}. Indeed,
  4 = 1+3 and 5² = 1 + 3·8, so both have the full 3-power order.
- *Modulo 7^b (if b ≥ 1):* take x ≡ 3. Since 3 is a primitive root mod 49 (3⁶ ≢ 1), it is a
  primitive root mod 7^b, so ord(3) = 6·7^{b−1}. Since 4³ = 64 ≢ 1 (mod 49),
  ord(4) = 3·7^{b−1}.
- *Modulo p^k for each p^k ∥ r (p ≥ 5, p ≠ 7):*
  - By Cohen (p > 7), or the pair (2, 3) for p = 5, there are consecutive primitive roots
    y, y+1 mod p.
  - Among the p lifts y + tp, at most one fails to be a primitive root mod p², and at most one
    fails for y+1. Since p ≥ 5 > 2, some lift gives consecutive primitive roots mod p², hence
    mod p^k.
  - Both orders equal φ(p^k), which is even.

Let Φ = lcm of the φ(p^k) (Φ = 1 if r = 1). Then ord_m(x) = ord_m(x+1) in every case:
- *a, b ≥ 1:* lcm(3^{a−1}, 6·7^{b−1}, Φ) = lcm(2·3^{a−1}, 3·7^{b−1}, Φ). Both sides have 2-part
  2·(2-part of Φ), 3-part 3^{max(a−1,1)}·…, and 7-part 7^{b−1}.
- *a ≥ 1, b = 0, r > 1:* lcm(3^{a−1}, Φ) = lcm(2·3^{a−1}, Φ), since Φ is even.
- *a = 0, b ≥ 1, r > 1:* lcm(6·7^{b−1}, Φ) = lcm(3·7^{b−1}, Φ), since Φ is even.
- *a = b = 0:* both sides equal Φ.

So f(m) ≥ 1. ∎

(m = 1 is excluded, since f(1) = 1 by definition.)

`verify_construction.py` checks that this explicit construction produces a valid x for every
odd m ≤ 30000 that is not a pure power of 3 or 7, and that f = 0 on small pure powers.

## Lean 4 verification

`A397683.lean` (about 520 lines, Lean 4 v4.33.1 + Mathlib) formalizes the whole proof. Its
main theorem is

```lean
theorem conjecture (hC : CohenConsecutive) {m : ℕ} (hm : 1 < m) (hodd : Odd m) :
    f m = 0 ↔ (∃ a, m = 3 ^ a) ∨ (∃ b, m = 7 ^ b)
```

Here `f` is the OEIS function, defined literally: the number of `1 ≤ x < m` with
`gcd(x, m) = gcd(x+1, m) = 1` and `orderOf (x : ZMod m) = orderOf (x + 1)`.

Cohen's theorem is the one input not proved in Lean. It enters as the explicit hypothesis

```lean
def CohenConsecutive : Prop :=
  ∀ p : ℕ, p.Prime → 7 < p → ∃ y : ZMod p, orderOf y = p - 1 ∧ orderOf (y + 1) = p - 1
```

It is a published theorem (S. D. Cohen, 1985) whose proof uses character-sum estimates that
Mathlib does not have. Everything else is machine-checked:
- the lifting-the-exponent profiles mod 3^a and 7^b;
- the lift of consecutive primitive roots from p to p^n;
- the CRT gluing and the case analysis;
- the impossibility for pure powers of 3 and 7;
- the reduction from x to x mod m.

`#print axioms OeisA397683.conjecture` reports only `propext`, `Classical.choice` and
`Quot.sound`, with no `sorryAx`.

**To check:** put the file at `FormalConjectures/OEIS/A397683Proof.lean` inside a checkout of
google-deepmind/formal-conjectures (commit b3f2641), then run
`lake exe cache get && lake build FormalConjectures.OEIS.A397683Proof`.
