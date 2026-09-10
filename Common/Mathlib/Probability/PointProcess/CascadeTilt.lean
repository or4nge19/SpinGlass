/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.PointProcess.CascadeProduct

/-!
# The tilting weights of a cascade recursion, and the tilted averages

Talagrand's fundamental identities of Vol. II, §14.3 are all expressed through the weights

`W_p = (R_{p+1} / R_p) ^ m_p`   (14.22)

where `R_p = exp F_p` is the value at level `p` of the recursion (14.5) computing `cascadeRec`.
Their defining property is `𝔼_p W_p = 1` (14.23) (`lintegral_cascadeW`), which holds because
`R_p ^ m_p = ∫ R_{p+1} ^ m_p dμ_p` is exactly the recursion.

Nesting them gives the **tilted average** `𝔼(W₁ ⋯ W_k A)` of (14.24)–(14.26) (`cascadeTilt`); it is
the average of `A` against a probability measure on `T^k` (`cascadeTilt_one`), reducing to the plain
product average when the recursion is run on a constant (`cascadeTilt_const`), which is the case
`F = 0` of §14.3. Talagrand's (14.26)–(14.27),
`𝔼⟨A/G⟩ = 𝔼(W₁ ⋯ W_k (A/G))`, identifies this with the cascade Gibbs average with weights
`u*_α G(z_α)`; it is not proved here (see the note at the end of the file).

The hypotheses are exactly Talagrand's: `G = exp F` is positive, and satisfies his (14.4),
`∫ G d(μ₁ ⊗ ⋯ ⊗ μ_k) < ∞`. Positivity makes every `R_p` nonzero (`cascadeRec_pos`) and (14.4)
makes `R_p` finite by Jensen (`cascadeRec_le_lintegral_pi`); along a branch the hypothesis is
inherited only almost everywhere, which is why the recursive proofs go through
`lintegral_congr_ae`.
-/

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace ProbabilityTheory

open ENNReal

universe u

variable {T : Type u} [MeasurableSpace T]

/-! ### Bounds on the recursion -/

/-- The recursion of a constant is that constant. -/
theorem cascadeRec_const (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] (hpos : ∀ i, 0 < ms i) (c : ℝ≥0∞) :
    cascadeRec k ms μs (fun _ => c) = c := by
  have h := cascadeRec_const_mul k ms μs (G := fun _ : Fin k → T => (1 : ℝ≥0∞))
    measurable_const hpos c
  rw [cascadeRec_one k ms μs hpos, mul_one] at h
  simpa using h

/-- An upper bound on `G` is an upper bound on the recursion. -/
theorem cascadeRec_le_of_le (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] (hpos : ∀ i, 0 < ms i) {G : (Fin k → T) → ℝ≥0∞} {C : ℝ≥0∞}
    (hG : ∀ zs, G zs ≤ C) : cascadeRec k ms μs G ≤ C := by
  have h := cascadeRec_mono k ms μs (G := G) (G' := fun _ => C) hG fun i => (hpos i).le
  rwa [cascadeRec_const k ms μs hpos] at h

/-- A lower bound on `G` is a lower bound on the recursion. -/
theorem le_cascadeRec_of_le (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] (hpos : ∀ i, 0 < ms i) {G : (Fin k → T) → ℝ≥0∞} {c : ℝ≥0∞}
    (hG : ∀ zs, c ≤ G zs) : c ≤ cascadeRec k ms μs G := by
  have h := cascadeRec_mono k ms μs (G := fun _ => c) (G' := G) hG fun i => (hpos i).le
  rwa [cascadeRec_const k ms μs hpos] at h

/-- `R_p ^ m_p = ∫ R_{p+1} ^ m_p dμ_p`: the recursion (14.5) read as a moment identity. -/
theorem cascadeRec_rpow_eq_lintegral (k : ℕ) (ms : Fin (k + 1) → ℝ) (μs : Fin (k + 1) → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] (G : (Fin (k + 1) → T) → ℝ≥0∞) (hm : 0 < ms 0) :
    cascadeRec (k + 1) ms μs G ^ ms 0
      = ∫⁻ z, cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
          ∂μs 0 := by
  rw [cascadeRec_succ, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hm.ne', ENNReal.rpow_one]

/-! ### Talagrand's hypothesis (14.4) along a branch -/

/-- Talagrand's (14.4) is inherited by the tail of the cascade for almost every first mark. -/
theorem ae_lintegral_pi_cons_ne_top (k : ℕ) (μs : Fin (k + 1) → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G : (Fin (k + 1) → T) → ℝ≥0∞} (hG : Measurable G)
    (hfin : ∫⁻ zs, G zs ∂Measure.pi μs ≠ ∞) :
    ∀ᵐ z ∂μs 0, ∫⁻ zs, G (Fin.cons z zs) ∂Measure.pi (Fin.tail μs) ≠ ∞ := by
  have hm : Measurable fun z => ∫⁻ zs, G (Fin.cons z zs) ∂Measure.pi (Fin.tail μs) :=
    Measurable.lintegral_prod_right' (ν := Measure.pi (Fin.tail μs))
      (f := fun p : T × (Fin k → T) => G (Fin.cons p.1 p.2)) (hG.comp measurable_fin_cons)
  have hne : ∫⁻ z, (∫⁻ zs, G (Fin.cons z zs) ∂Measure.pi (Fin.tail μs)) ∂μs 0 ≠ ∞ := by
    rw [← lintegral_pi_fin_succ μs hG]
    exact hfin
  filter_upwards [ae_lt_top hm hne] with z hz
  exact hz.ne

/-- Under (14.4) the recursion is finite. -/
theorem cascadeRec_ne_top (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G : (Fin k → T) → ℝ≥0∞} (hG : Measurable G)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (hfin : ∫⁻ zs, G zs ∂Measure.pi μs ≠ ∞) : cascadeRec k ms μs G ≠ ∞ :=
  ne_top_of_le_ne_top hfin (cascadeRec_le_lintegral_pi k ms μs hG hpos hle)

/-! ### The weights `W_p` -/

/-- **Talagrand's weight (14.22)** at the top level of the recursion:
`W = (R₁(z) / R₀) ^ m₀`, where `R₀ = cascadeRec (k+1) ms μs G` and `R₁(z)` is the recursion of the
remaining levels with the first mark set to `z`. -/
noncomputable def cascadeW (k : ℕ) (ms : Fin (k + 1) → ℝ) (μs : Fin (k + 1) → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] (G : (Fin (k + 1) → T) → ℝ≥0∞) (z : T) : ℝ≥0∞ :=
  (cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
    / cascadeRec (k + 1) ms μs G) ^ ms 0

lemma measurable_cascadeW (k : ℕ) (ms : Fin (k + 1) → ℝ) (μs : Fin (k + 1) → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G : (Fin (k + 1) → T) → ℝ≥0∞} (hG : Measurable G) :
    Measurable (cascadeW k ms μs G) :=
  ((measurable_cascadeRec_cons k _ _ hG).div measurable_const).pow_const _

/-- Joint measurability of the weights in a parameter and the mark. -/
lemma measurable_cascadeW_prod (k : ℕ) (ms : Fin (k + 1) → ℝ) (μs : Fin (k + 1) → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {α : Type u} [MeasurableSpace α]
    {Gs : α → (Fin (k + 1) → T) → ℝ≥0∞} (hGs : Measurable (uncurry Gs)) :
    Measurable fun q : α × T => cascadeW k ms μs (Gs q.1) q.2 := by
  unfold cascadeW
  have hcons : Measurable (uncurry fun q : α × T => fun zs : Fin k → T =>
      Gs q.1 (Fin.cons q.2 zs)) :=
    hGs.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_fin_cons.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
  have h1 : Measurable fun q : α × T => cascadeRec k (Fin.tail ms) (Fin.tail μs)
      (fun zs => Gs q.1 (Fin.cons q.2 zs)) :=
    measurable_cascadeRec_prod k (Fin.tail ms) (Fin.tail μs) hcons
  have h2 : Measurable fun q : α × T => cascadeRec (k + 1) ms μs (Gs q.1) :=
    (measurable_cascadeRec_prod (k + 1) ms μs hGs).comp measurable_fst
  exact (h1.div h2).pow_const _

/-- **Talagrand's (14.23)**: `𝔼_p W_p = 1`, under his (14.4). -/
theorem lintegral_cascadeW (k : ℕ) (ms : Fin (k + 1) → ℝ) (μs : Fin (k + 1) → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G : (Fin (k + 1) → T) → ℝ≥0∞} (hG : Measurable G)
    (hGpos : ∀ zs, 0 < G zs) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (hfin : ∫⁻ zs, G zs ∂Measure.pi μs ≠ ∞) : ∫⁻ z, cascadeW k ms μs G z ∂μs 0 = 1 := by
  have hm : 0 < ms 0 := hpos 0
  set R : ℝ≥0∞ := cascadeRec (k + 1) ms μs G with hR
  have hR0 : R ≠ 0 := (cascadeRec_pos (k + 1) ms μs hG hGpos hpos).ne'
  have hRtop : R ≠ ∞ := cascadeRec_ne_top (k + 1) ms μs hG hpos hle hfin
  have hRm0 : R ^ ms 0 ≠ 0 := by
    simpa using (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 hR0) hm.le).ne'
  have hRmtop : R ^ ms 0 ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hm.le hRtop
  have hdiv : ∀ z, cascadeW k ms μs G z
      = cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
        / R ^ ms 0 := by
    intro z
    rw [cascadeW, ENNReal.div_rpow_of_nonneg _ _ hm.le]
  simp_rw [hdiv, div_eq_mul_inv]
  rw [lintegral_mul_const _ (((measurable_cascadeRec_cons k _ _ hG).pow_const _)),
    ← cascadeRec_rpow_eq_lintegral k ms μs G hm, ENNReal.mul_inv_cancel hRm0 hRmtop]

/-! ### The tilted averages `𝔼(W₁ ⋯ W_k A)` -/

/-- **Talagrand's tilted average (14.24)–(14.26)**: `𝔼(W₁ ⋯ W_k A)`, defined by the nesting
`𝔼_p(W_p · 𝔼_{p+1}(W_{p+1} ⋯))` that (14.21) produces. -/
noncomputable def cascadeTilt : (k : ℕ) → (ms : Fin k → ℝ) → (μs : Fin k → Measure T) →
    [∀ i, IsProbabilityMeasure (μs i)] → ((Fin k → T) → ℝ≥0∞) → ((Fin k → T) → ℝ≥0∞) → ℝ≥0∞
  | 0, _, _, _, _, A => A Fin.elim0
  | k + 1, ms, μs, _, G, A =>
      ∫⁻ z, cascadeW k ms μs G z
        * cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
            (fun zs => A (Fin.cons z zs)) ∂μs 0

@[simp] lemma cascadeTilt_zero (ms : Fin 0 → ℝ) (μs : Fin 0 → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] (G A : (Fin 0 → T) → ℝ≥0∞) :
    cascadeTilt 0 ms μs G A = A Fin.elim0 := rfl

lemma cascadeTilt_succ (k : ℕ) (ms : Fin (k + 1) → ℝ) (μs : Fin (k + 1) → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] (G A : (Fin (k + 1) → T) → ℝ≥0∞) :
    cascadeTilt (k + 1) ms μs G A
      = ∫⁻ z, cascadeW k ms μs G z
          * cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
              (fun zs => A (Fin.cons z zs)) ∂μs 0 := rfl

/-- **Joint measurability of the tilted average** in a parameter of both `G` and `A`. -/
theorem measurable_cascadeTilt_prod : ∀ (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {α : Type u} [MeasurableSpace α]
    {Gs As : α → (Fin k → T) → ℝ≥0∞}, Measurable (uncurry Gs) → Measurable (uncurry As) →
    Measurable fun a => cascadeTilt k ms μs (Gs a) (As a) := by
  intro k
  induction k with
  | zero =>
    intro ms μs _ α _ Gs As _ hAs
    exact hAs.comp (measurable_id.prodMk measurable_const)
  | succ k ih =>
    intro ms μs _ α _ Gs As hGs hAs
    have hconsG : Measurable (uncurry fun q : α × T => fun zs : Fin k → T =>
        Gs q.1 (Fin.cons q.2 zs)) :=
      hGs.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fin_cons.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
    have hconsA : Measurable (uncurry fun q : α × T => fun zs : Fin k → T =>
        As q.1 (Fin.cons q.2 zs)) :=
      hAs.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fin_cons.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
    have hprod : Measurable fun q : α × T => cascadeW k ms μs (Gs q.1) q.2
        * cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => Gs q.1 (Fin.cons q.2 zs))
            (fun zs => As q.1 (Fin.cons q.2 zs)) :=
      (measurable_cascadeW_prod k ms μs hGs).mul
        (ih (Fin.tail ms) (Fin.tail μs) hconsG hconsA)
    exact Measurable.lintegral_prod_right' (ν := μs 0) hprod

/-- **The tilted average is an average against a probability measure**: `𝔼(W₁ ⋯ W_k) = 1`,
under Talagrand's (14.4). -/
theorem cascadeTilt_one (k : ℕ) : ∀ (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G : (Fin k → T) → ℝ≥0∞}, Measurable G →
    (∀ zs, 0 < G zs) → (∀ i, 0 < ms i) → (∀ i, ms i ≤ 1) →
    ∫⁻ zs, G zs ∂Measure.pi μs ≠ ∞ → cascadeTilt k ms μs G (fun _ => 1) = 1 := by
  induction k with
  | zero => intro ms μs _ G _ _ _ _ _; rfl
  | succ k ih =>
    intro ms μs _ G hG hGpos hpos hle hfin
    rw [cascadeTilt_succ]
    have hinner : ∀ᵐ z ∂μs 0, cascadeW k ms μs G z
        * cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) (fun _ => 1)
        = cascadeW k ms μs G z := by
      filter_upwards [ae_lintegral_pi_cons_ne_top k μs hG hfin] with z hz
      rw [ih (Fin.tail ms) (Fin.tail μs) (G := fun zs => G (Fin.cons z zs))
        (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (fun zs => hGpos _) (fun i => hpos i.succ) (fun i => hle i.succ) hz, mul_one]
    rw [lintegral_congr_ae hinner]
    exact lintegral_cascadeW k ms μs hG hGpos hpos hle hfin

/-- The tilted average is monotone in the averaged function. -/
theorem cascadeTilt_mono (k : ℕ) : ∀ (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] (G : (Fin k → T) → ℝ≥0∞) {A A' : (Fin k → T) → ℝ≥0∞},
    (∀ zs, A zs ≤ A' zs) → cascadeTilt k ms μs G A ≤ cascadeTilt k ms μs G A' := by
  induction k with
  | zero => intro ms μs _ G A A' h; exact h _
  | succ k ih =>
    intro ms μs _ G A A' h
    rw [cascadeTilt_succ, cascadeTilt_succ]
    exact lintegral_mono fun z => mul_le_mul' le_rfl
      (ih (Fin.tail ms) (Fin.tail μs) _ fun zs => h _)

/-- **The case `F = 0` of §14.3**: when the recursion is run on a positive finite constant every
`W_p` is `1`, and the tilted average is the plain product average. -/
theorem cascadeTilt_const (k : ℕ) : ∀ (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {c : ℝ≥0∞}, c ≠ 0 → c ≠ ∞ → (∀ i, 0 < ms i) →
    ∀ {A : (Fin k → T) → ℝ≥0∞}, Measurable A →
    cascadeTilt k ms μs (fun _ => c) A = ∫⁻ zs, A zs ∂Measure.pi μs := by
  induction k with
  | zero =>
    intro ms μs _ c _ _ _ A hA
    rw [cascadeTilt_zero, Measure.pi_of_empty, lintegral_dirac' _ hA]
    exact congrArg A (Subsingleton.elim _ _)
  | succ k ih =>
    intro ms μs _ c hc0 hctop hpos A hA
    have hm : 0 < ms 0 := hpos 0
    have hW : ∀ z, cascadeW k ms μs (fun _ => c) z = 1 := by
      intro z
      rw [cascadeW, cascadeRec_const k (Fin.tail ms) (Fin.tail μs) (fun i => hpos i.succ) c,
        cascadeRec_const (k + 1) ms μs hpos c, ENNReal.div_self hc0 hctop, ENNReal.one_rpow]
    rw [cascadeTilt_succ]
    simp_rw [hW, one_mul]
    have hinner : ∀ z, cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun _ => c)
        (fun zs => A (Fin.cons z zs))
        = ∫⁻ zs, A (Fin.cons z zs) ∂Measure.pi (Fin.tail μs) := by
      intro z
      exact ih (Fin.tail ms) (Fin.tail μs) hc0 hctop (fun i => hpos i.succ)
        (hA.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
    simp_rw [hinner]
    exact (lintegral_pi_fin_succ μs hA).symm

/-! ### The frontier

Talagrand's (14.26)–(14.27) states that the tilted average computes the cascade Gibbs average,

`∫ (cascadeSum k A ω / cascadeSum k G ω) d(cascadeLaw k ms μs)(ω) = cascadeTilt k ms μs G A`,

of which the case `G` constant is `lintegral_cascadeSum_div_cascadeSum_one_prod` (the marks of a
branch chosen according to the cascade weights have the law of the marks) together with
`cascadeTilt_const`. Talagrand derives it by differentiating (14.8) in the direction `A`; the
route that stays inside the `ℝ≥0∞` calculus of this development is induction on `k` from the
one-level identity `lintegral_pdSum_mul_inv_pdSum`, whose induction step needs the *one-insertion
moment* of a cascade,

`∫ cascadeSum k A ω * (cascadeSum k G ω) ^ (a - 1) d(cascadeLaw k ms μs)(ω)`,

the analogue with a numerator of Proposition 14.2.2 (`lintegral_cascadeSum_rpow`). At one level
that is `∫ pdSum A N * (pdSum V N) ^ (a - 1) d(pdProcess m η)(N)`, the missing companion of
`lintegral_pdSumSq_mul_rpow_pdSum`. Once (14.27) is available, the random-sign trick of (14.33)
— a cascade whose marks are `T × {-1, 1}`, which the marking layer already supports — gives
Proposition 14.3.2 (14.37), and the coupled construction (14.44)–(14.46) gives Theorem 14.3.5
(14.47) and Corollary 14.3.7 (14.52), the entry point of §14.5.
-/

end ProbabilityTheory
