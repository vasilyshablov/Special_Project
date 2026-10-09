import Mathlib

/-!
# Producer-independence of mathematical validity and evidential trust transfer

A Lean-checked model of the following thesis.

1. (Formalism) Whether an artifact is valid mathematics does not depend on who produced it
   or on whether any human understands it.
2. (Humanism depends on a boundary) A Thurston-style definition ("valid *and* understood by
   a human") is only as precise as the predicate `IsHuman`, and as that predicate widens the
   definition collapses to the formalist one.
3. (Trusted base) Trusting a checked proof requires trusting the checker, the logic and the
   faithfulness of the statement, but never the producer.
4. (Trust transfer) Under a two-type Bayesian model, a run of verified successes eventually
   pushes the posterior trust in a superhumanly reliable agent above any threshold `t < 1`,
   and its expected accuracy above any fixed reliability `r` of a human community; but it
   never reaches certainty.
5. (Limits) Evidence gathered on checkable tasks is blind to behaviour on uncheckable tasks.
6. (What is a human) Along any gradual-replacement chain from a human to a synthetic agent,
   either the end point is human or some single step crosses a sharp boundary.

Everything here is a theorem *about the model*: it shows the conclusions follow from the
stated assumptions; whether the assumptions describe the world is a philosophical question.
-/

open Filter Topology

namespace TrustThesis

/-! ## 1. Two definitions of mathematics -/

/-- An abstract deductive system in the sense of Hilbert: formulas, proofs and a
proof-checking relation. -/
structure ProofSystem where
  Formula : Type
  Proof : Type
  Proves : Proof → Formula → Prop

variable {S : ProofSystem} {Agent : Type}

/-- A proof artifact: a proof together with whoever (or whatever) produced it. -/
structure Artifact (S : ProofSystem) (Agent : Type) where
  producer : Agent
  proof : S.Proof

/-- **Formalist (Hilbert) definition.** An artifact is mathematics for `φ` iff its proof
derives `φ`. -/
def FormalMath (φ : S.Formula) (a : Artifact S Agent) : Prop :=
  S.Proves a.proof φ

/-- **Humanist (Thurston) definition.** Valid, *and* understood by some agent in the class
`IsHuman`. -/
def HumanistMath (IsHuman : Agent → Prop) (Understands : Agent → S.Proof → S.Formula → Prop)
    (φ : S.Formula) (a : Artifact S Agent) : Prop :=
  S.Proves a.proof φ ∧ ∃ h, IsHuman h ∧ Understands h a.proof φ

/-- **Theorem 1 (producer irrelevance).** Under the formalist definition, the producer of a
proof plays no role. -/
theorem formalMath_producer_irrelevant (φ : S.Formula) (π : S.Proof) (x y : Agent) :
    FormalMath φ (⟨x, π⟩ : Artifact S Agent) ↔ FormalMath φ (⟨y, π⟩ : Artifact S Agent) :=
  Iff.rfl

/-- **Theorem 2.** Humanist mathematics is a subclass of formalist mathematics. -/
theorem formalMath_of_humanistMath {H : Agent → Prop} {U : Agent → S.Proof → S.Formula → Prop}
    {φ : S.Formula} {a : Artifact S Agent} (h : HumanistMath H U φ a) : FormalMath φ a :=
  h.1

/-- **Theorem 3 (monotonicity).** Widening the class of "humans" can only enlarge humanist
mathematics. -/
theorem humanistMath_mono {H₁ H₂ : Agent → Prop} (hle : ∀ x, H₁ x → H₂ x)
    {U : Agent → S.Proof → S.Formula → Prop} {φ : S.Formula} {a : Artifact S Agent}
    (h : HumanistMath H₁ U φ a) : HumanistMath H₂ U φ a := by
  obtain ⟨hv, x, hx, hu⟩ := h
  exact ⟨hv, x, hle x hx, hu⟩

/-- **Theorem 4 (collapse).** If every agent counts and every producer understands its own
valid proofs, the humanist definition coincides with the formalist one. -/
theorem humanistMath_univ_iff {U : Agent → S.Proof → S.Formula → Prop}
    (hprod : ∀ (a : Artifact S Agent) φ, S.Proves a.proof φ → U a.producer a.proof φ)
    (φ : S.Formula) (a : Artifact S Agent) :
    HumanistMath (fun _ => True) U φ a ↔ FormalMath φ a :=
  ⟨fun h => h.1, fun h => ⟨h, a.producer, trivial, hprod a φ h⟩⟩

/-- **Theorem 5 (boundary dependence).** If a valid proof is understood by exactly one agent
`s`, and two candidate definitions of "human" disagree about `s`, then they disagree about
whether the proof is mathematics. The humanist definition inherits every open question about
the boundary of `IsHuman`. -/
theorem humanistMath_depends_on_boundary {H₁ H₂ : Agent → Prop}
    {U : Agent → S.Proof → S.Formula → Prop} {φ : S.Formula} {a : Artifact S Agent} {s : Agent}
    (hvalid : S.Proves a.proof φ) (hsU : U s a.proof φ) (honly : ∀ x, U x a.proof φ → x = s)
    (hs₁ : ¬ H₁ s) (hs₂ : H₂ s) :
    ¬ HumanistMath H₁ U φ a ∧ HumanistMath H₂ U φ a := by
  refine ⟨?_, hvalid, s, hs₂, hsU⟩
  rintro ⟨-, x, hx, hxU⟩
  obtain rfl := honly x hxU
  exact hs₁ hx

/-! ## 2. The trusted base of a checked proof -/

/-- A checker is sound if everything it accepts is derivable. -/
def Sound (check : S.Proof → S.Formula → Bool) : Prop :=
  ∀ π φ, check π φ = true → S.Proves π φ

/-- **Theorem 6 (trusted base).** To conclude the intended claim `Q` from an accepted
artifact one needs exactly three things: a sound checker, a sound logic (derivable formulas
are true under the intended `Meaning`), and a faithful statement (`Meaning φ ↔ Q`).
The producer does not appear among the hypotheses. -/
theorem trusted_base {check : S.Proof → S.Formula → Bool} (hcheck : Sound check)
    (Meaning : S.Formula → Prop) (hlogic : ∀ π φ, S.Proves π φ → Meaning φ)
    {Q : Prop} {φ : S.Formula} (hfaith : Meaning φ ↔ Q)
    (a : Artifact S Agent) (hacc : check a.proof φ = true) : Q :=
  hfaith.1 (hlogic _ _ (hcheck _ _ hacc))

/-- **Theorem 7 (independent statement audits).** If `n` auditors independently miss an
unfaithful statement with probabilities `ε i ≤ e`, the probability that all of them miss it is
at most `e ^ n`. (Independence is built into the model by multiplying the miss rates.) -/
theorem audit_miss_le {n : ℕ} (ε : Fin n → ℝ) (e : ℝ) (h0 : ∀ i, 0 ≤ ε i)
    (h : ∀ i, ε i ≤ e) : ∏ i, ε i ≤ e ^ n := by
  calc ∏ i, ε i ≤ ∏ _i : Fin n, e := Finset.prod_le_prod (fun i _ => h0 i) (fun i _ => h i)
    _ = e ^ n := by simp

/-- **Theorem 8.** With independent auditors of miss rate `e < 1`, the residual risk of an
unfaithful statement can be pushed below any `δ > 0`. -/
theorem audit_risk_eventually_lt {e δ : ℝ} (he0 : 0 ≤ e) (he1 : e < 1) (hδ : 0 < δ) :
    ∃ N, ∀ n ≥ N, e ^ n < δ :=
  eventually_atTop.1 ((tendsto_order.1 (tendsto_pow_atTop_nhds_zero_of_lt_one he0 he1)).2 δ hδ)

/-! ## 3. Evidential trust transfer -/

/-- Two-type model. With prior `p` the agent is of the *high* type (accuracy `aHi` on each
independent verified task), otherwise of the *low* type (accuracy `aLo`). This is the
posterior probability of the high type after `n` consecutive verified successes. -/
noncomputable def posterior (p aHi aLo : ℝ) (n : ℕ) : ℝ :=
  p * aHi ^ n / (p * aHi ^ n + (1 - p) * aLo ^ n)

lemma posterior_eq {p aHi aLo : ℝ} (haHi : 0 < aHi) (n : ℕ) :
    posterior p aHi aLo n = p / (p + (1 - p) * (aLo / aHi) ^ n) := by
  have hn : aHi ^ n ≠ 0 := pow_ne_zero n haHi.ne'
  have key : p + (1 - p) * (aLo / aHi) ^ n = (p * aHi ^ n + (1 - p) * aLo ^ n) / aHi ^ n := by
    rw [div_pow, eq_div_iff hn, add_mul, mul_assoc, div_mul_cancel₀ _ hn]
  rw [posterior, key, div_div_eq_mul_div]

/-- **Theorem 9.** Verified successes drive the posterior to certainty in the limit. -/
theorem posterior_tendsto_one {p aHi aLo : ℝ} (hp : 0 < p) (haLo : 0 ≤ aLo) (hlt : aLo < aHi) :
    Tendsto (posterior p aHi aLo) atTop (𝓝 1) := by
  have haHi : 0 < aHi := haLo.trans_lt hlt
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg haLo haHi.le)
    ((div_lt_one haHi).2 hlt)
  have hden : Tendsto (fun n : ℕ => p + (1 - p) * (aLo / aHi) ^ n) atTop (𝓝 p) := by
    simpa using (tendsto_const_nhds (x := p)).add ((tendsto_const_nhds (x := 1 - p)).mul hpow)
  have hlim := (tendsto_const_nhds (x := p)).div hden hp.ne'
  rw [div_self hp.ne'] at hlim
  exact hlim.congr fun n => (posterior_eq haHi n).symm

/-- **Theorem 10 (the boundary is crossed).** For every trust threshold `t < 1` there is a
finite number of verified successes after which the posterior exceeds `t` forever. -/
theorem trust_threshold_crossed {p aHi aLo t : ℝ} (hp : 0 < p) (haLo : 0 ≤ aLo)
    (hlt : aLo < aHi) (ht : t < 1) : ∃ N, ∀ n ≥ N, t < posterior p aHi aLo n :=
  eventually_atTop.1 ((tendsto_order.1 (posterior_tendsto_one hp haLo hlt)).1 t ht)

/-- **Theorem 11 (never certainty).** If the low type is possible and can succeed, no finite
record makes the posterior equal to `1`. A threshold of exactly `1` ("zero risk") is never
crossed by evidence alone. -/
theorem posterior_lt_one {p aHi aLo : ℝ} (hp : 0 < p) (hp1 : p < 1) (haLo : 0 < aLo)
    (haHi : 0 < aHi) (n : ℕ) : posterior p aHi aLo n < 1 := by
  have h1 : 0 < p * aHi ^ n := mul_pos hp (pow_pos haHi n)
  have h2 : 0 < (1 - p) * aLo ^ n := mul_pos (by linarith) (pow_pos haLo n)
  rw [posterior, div_lt_one (by linarith)]
  linarith

/-- Posterior expected accuracy of the agent on the next task. -/
noncomputable def expectedAccuracy (p aHi aLo : ℝ) (n : ℕ) : ℝ :=
  posterior p aHi aLo n * aHi + (1 - posterior p aHi aLo n) * aLo

/-- **Theorem 12 (outweighing a community).** Model the aggregated judgement of a human
community as a fixed reliability `r`. If the high type is more reliable than the community,
then after finitely many verified successes the agent's expected accuracy exceeds `r`. -/
theorem outweighs_community {p aHi aLo r : ℝ} (hp : 0 < p) (haLo : 0 ≤ aLo)
    (hlt : aLo < aHi) (hr : r < aHi) : ∃ N, ∀ n ≥ N, r < expectedAccuracy p aHi aLo n := by
  have h := posterior_tendsto_one hp haLo hlt
  have hlim : Tendsto (expectedAccuracy p aHi aLo) atTop (𝓝 (1 * aHi + (1 - 1) * aLo)) :=
    (h.mul_const aHi).add (((tendsto_const_nhds (x := (1 : ℝ))).sub h).mul_const aLo)
  rw [one_mul, sub_self, zero_mul, add_zero] at hlim
  exact eventually_atTop.1 ((tendsto_order.1 hlim).1 r hr)

/-! ## 4. The limits of transfer -/

/-- What an observer can see of an agent: its correctness on checkable tasks only. -/
def observe {Task : Type} (checkable : Task → Prop) (correct : Task → Prop) :
    ∀ t, checkable t → Prop :=
  fun t _ => correct t

/-- **Theorem 13 (evidence is blind off the checkable set).** Any evidence computed from
checkable tasks is identical for two agents that agree there, however they differ elsewhere. -/
theorem evidence_blind {Task α : Type} (checkable : Task → Prop)
    (E : (∀ t, checkable t → Prop) → α) {c₁ c₂ : Task → Prop}
    (h : ∀ t, checkable t → (c₁ t ↔ c₂ t)) :
    E (observe checkable c₁) = E (observe checkable c₂) := by
  congr 1
  funext t ht
  exact propext (h t ht)

/-- **Corollary 14.** There is always an agent that is wrong on *every* uncheckable task yet
produces exactly the same evidence as a perfect agent. Extending trust beyond verifiable
domains therefore needs an extra assumption (no distribution shift, no deception). -/
theorem exists_indistinguishable_failure {Task α : Type} (checkable : Task → Prop)
    (E : (∀ t, checkable t → Prop) → α) :
    ∃ c : Task → Prop, (∀ t, ¬ checkable t → ¬ c t) ∧
      E (observe checkable c) = E (observe checkable fun _ => True) :=
  ⟨checkable, fun _ h => h, evidence_blind checkable E fun _ ht => ⟨fun _ => trivial, fun _ => ht⟩⟩

/-! ## 5. What is a human? -/

/-- Gradual replacement: a chain `f 0, f 1, …, f n` of agents in which each step changes
little (e.g. one neuron replaced by a synthetic one). If membership is preserved by each
step, the end point is a member. -/
theorem sorites {A : Type} (P : A → Prop) (f : ℕ → A) (n : ℕ) (h0 : P (f 0))
    (hstep : ∀ i < n, P (f i) → P (f (i + 1))) : P (f n) := by
  induction n with
  | zero => exact h0
  | succ k ih =>
    exact hstep k (Nat.lt_succ_self k) (ih fun i hi => hstep i (Nat.lt_succ_of_lt hi))

/-- **Theorem 15 (replacement dilemma).** If a chain starts at a human and ends at a
non-human, some *single* step crosses a sharp boundary. Either the fully synthetic 1:1 brain
is human, or there is a specific neuron whose replacement makes the difference. -/
theorem replacement_dilemma {A : Type} (IsHuman : A → Prop) (f : ℕ → A) (n : ℕ)
    (h0 : IsHuman (f 0)) (hn : ¬ IsHuman (f n)) :
    ∃ i < n, IsHuman (f i) ∧ ¬ IsHuman (f (i + 1)) := by
  by_contra hcon
  push Not at hcon
  exact hn (sorites IsHuman f n h0 hcon)

/-- **Theorem 16 (functional duplicates).** If understanding is behavioural (depends only on
input–output behaviour), a behavioural duplicate of a human understands whatever that human
understands. -/
theorem duplicate_understands {Behavior : Type} (behav : Agent → Behavior)
    (U : Agent → S.Proof → S.Formula → Prop)
    (hU : ∀ a b, behav a = behav b → ∀ π φ, (U a π φ ↔ U b π φ))
    {h s : Agent} (hdup : behav s = behav h) {π : S.Proof} {φ : S.Formula}
    (hu : U h π φ) : U s π φ :=
  (hU s h hdup π φ).2 hu

end TrustThesis

#print axioms TrustThesis.humanistMath_depends_on_boundary
#print axioms TrustThesis.trusted_base
#print axioms TrustThesis.trust_threshold_crossed
#print axioms TrustThesis.posterior_lt_one
#print axioms TrustThesis.outweighs_community
#print axioms TrustThesis.exists_indistinguishable_failure
#print axioms TrustThesis.replacement_dilemma
