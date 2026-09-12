/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.PointProcess.CascadeTilt

/-!
# The tilted probability measure of a cascade recursion

Talagrand's tilted averages `𝔼(W₁ ⋯ W_k A)` (Vol. II, (14.24)–(14.26); `cascadeTilt`) are the
integrals of `A` against the probability measure on `T^k` whose density with respect to the
product law of the marks is `W₁(z₁) W₂(z₁, z₂) ⋯ W_k(z₁, …, z_k)` (`cascadeTiltDensity`,
`cascadeTiltMeasure`, `lintegral_cascadeTiltMeasure`, `isProbabilityMeasure_cascadeTiltMeasure`).
Being a `Measure`, it also averages signed functions (`integral_cascadeTiltMeasure`), which is
what the derivative of the recursion in a parameter needs — `Y'_p = 𝔼_p(W_p Y'_{p+1})`,
Talagrand's (14.185) and (14.215) — and Talagrand's nesting `𝔼_p(W_p 𝔼_{p+1}(⋯))` is
`integral_cascadeTiltMeasure_succ`. Fubini for `Measure.pi` over `Fin (n + 1)` in Bochner form is
`integral_pi_fin_succ`.
-/

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace ProbabilityTheory

open ENNReal

universe u

variable {T : Type u} [MeasurableSpace T]

/-! ### Bochner integrals over `T^(n+1)`, split at the first coordinate -/

/-- Fubini for `Measure.pi` over `Fin (n + 1)`, in Bochner form. -/
lemma integral_pi_fin_succ {n : ℕ} (μs : Fin (n + 1) → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : (Fin (n + 1) → T) → E} (hg : Integrable g (Measure.pi μs)) :
    ∫ zs, g zs ∂Measure.pi μs
      = ∫ z, (∫ zs, g (Fin.cons z zs) ∂Measure.pi (Fin.tail μs)) ∂μs 0 := by
  have hmp := (measurePreserving_piFinSuccAbove μs 0).symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => T) 0)
  have hge : Integrable (fun q : T × (Fin n → T) =>
      g ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => T) 0).symm q))
      ((μs 0).prod (Measure.pi fun j => μs ((0 : Fin (n + 1)).succAbove j))) :=
    (hmp.integrable_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => T) 0).symm.measurableEmbedding).2 hg
  rw [← hmp.integral_comp' g, integral_prod _ hge]
  simp only [Fin.succAbove_zero]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z =>
    integral_congr_ae (Filter.Eventually.of_forall fun zs => ?_))
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero]
  rfl

/-- Fubini for `Measure.pi` over `Fin (n+1)`: the sections of an integrable function are
integrable for a.e. first coordinate. -/
lemma ae_integrable_pi_fin_succ {n : ℕ} (μs : Fin (n + 1) → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {E : Type*} [NormedAddCommGroup E]
    {g : (Fin (n + 1) → T) → E} (hg : Integrable g (Measure.pi μs)) :
    ∀ᵐ z ∂μs 0, Integrable (fun zs => g (Fin.cons z zs)) (Measure.pi (Fin.tail μs)) := by
  have hmp := (measurePreserving_piFinSuccAbove μs 0).symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => T) 0)
  have hge : Integrable (fun q : T × (Fin n → T) =>
      g ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => T) 0).symm q))
      ((μs 0).prod (Measure.pi fun j => μs ((0 : Fin (n + 1)).succAbove j))) :=
    (hmp.integrable_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => T) 0).symm.measurableEmbedding).2 hg
  simp only [Fin.succAbove_zero] at hge
  filter_upwards [hge.prod_right_ae] with z hz
  refine hz.congr (Filter.Eventually.of_forall fun zs => ?_)
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero]
  rfl

/-- Fubini for `Measure.pi` over `Fin (n+1)`: the partial integral over the tail coordinates of an
integrable function is integrable in the first coordinate. -/
lemma integrable_integral_pi_fin_succ {n : ℕ} (μs : Fin (n + 1) → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : (Fin (n + 1) → T) → E} (hg : Integrable g (Measure.pi μs)) :
    Integrable (fun z => ∫ zs, g (Fin.cons z zs) ∂Measure.pi (Fin.tail μs)) (μs 0) := by
  have hmp := (measurePreserving_piFinSuccAbove μs 0).symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => T) 0)
  have hge : Integrable (fun q : T × (Fin n → T) =>
      g ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => T) 0).symm q))
      ((μs 0).prod (Measure.pi fun j => μs ((0 : Fin (n + 1)).succAbove j))) :=
    (hmp.integrable_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => T) 0).symm.measurableEmbedding).2 hg
  simp only [Fin.succAbove_zero] at hge
  refine hge.integral_prod_left.congr (Filter.Eventually.of_forall fun z => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun zs => ?_)
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero]
  rfl

/-! ### The density `W₁ ⋯ W_k` -/

/-- **The density of Talagrand's tilted average** with respect to the product law of the marks:
`W₁(z₁) W₂(z₁, z₂) ⋯ W_k(z₁, …, z_k)`, each `W_p` being the weight (14.22) of level `p` of the
recursion started with the marks `z₁, …, z_{p-1}` fixed. -/
noncomputable def cascadeTiltDensity : (k : ℕ) → (ms : Fin k → ℝ) → (μs : Fin k → Measure T) →
    [∀ i, IsProbabilityMeasure (μs i)] → ((Fin k → T) → ℝ≥0∞) → (Fin k → T) → ℝ≥0∞
  | 0, _, _, _, _, _ => 1
  | k + 1, ms, μs, _, G, zs =>
      cascadeW k ms μs G (zs 0)
        * cascadeTiltDensity k (Fin.tail ms) (Fin.tail μs) (fun ys => G (Fin.cons (zs 0) ys))
            (Fin.tail zs)

@[simp] lemma cascadeTiltDensity_zero (ms : Fin 0 → ℝ) (μs : Fin 0 → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] (G : (Fin 0 → T) → ℝ≥0∞) (zs : Fin 0 → T) :
    cascadeTiltDensity 0 ms μs G zs = 1 := rfl

lemma cascadeTiltDensity_cons (k : ℕ) (ms : Fin (k + 1) → ℝ) (μs : Fin (k + 1) → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] (G : (Fin (k + 1) → T) → ℝ≥0∞) (z : T) (ys : Fin k → T) :
    cascadeTiltDensity (k + 1) ms μs G (Fin.cons z ys)
      = cascadeW k ms μs G z
        * cascadeTiltDensity k (Fin.tail ms) (Fin.tail μs) (fun ys => G (Fin.cons z ys)) ys := by
  simp only [cascadeTiltDensity, Fin.cons_zero, Fin.tail_cons]

/-- Joint measurability of the density in a parameter of `G` and the marks. -/
theorem measurable_cascadeTiltDensity_prod : ∀ (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {α : Type u} [MeasurableSpace α]
    {Gs : α → (Fin k → T) → ℝ≥0∞}, Measurable (uncurry Gs) →
    Measurable fun q : α × (Fin k → T) => cascadeTiltDensity k ms μs (Gs q.1) q.2 := by
  intro k
  induction k with
  | zero =>
    intro ms μs _ α _ Gs _
    exact measurable_const
  | succ k ih =>
    intro ms μs _ α _ Gs hGs
    have h1 : Measurable fun q : α × (Fin (k + 1) → T) => cascadeW k ms μs (Gs q.1) (q.2 0) :=
      (measurable_cascadeW_prod k ms μs hGs).comp
        (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
    have hGs' : Measurable (uncurry fun (p : α × T) (ys : Fin k → T) =>
        Gs p.1 (Fin.cons p.2 ys)) :=
      hGs.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fin_cons.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
    have htail : Measurable fun zs : Fin (k + 1) → T => Fin.tail zs :=
      measurable_pi_lambda _ fun j => measurable_pi_apply j.succ
    have h2 : Measurable fun q : α × (Fin (k + 1) → T) =>
        cascadeTiltDensity k (Fin.tail ms) (Fin.tail μs) (fun ys => Gs q.1 (Fin.cons (q.2 0) ys))
          (Fin.tail q.2) := by
      have h := (ih (Fin.tail ms) (Fin.tail μs) (α := α × T) hGs').comp
        ((measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd)).prodMk
          (htail.comp measurable_snd) :
          Measurable fun q : α × (Fin (k + 1) → T) => ((q.1, q.2 0), Fin.tail q.2))
      exact h
    exact h1.mul h2

lemma measurable_cascadeTiltDensity (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G : (Fin k → T) → ℝ≥0∞} (hG : Measurable G) :
    Measurable (cascadeTiltDensity k ms μs G) := by
  have h := (measurable_cascadeTiltDensity_prod k ms μs (α := PUnit.{u + 1})
    (Gs := fun _ => G) (hG.comp measurable_snd)).comp
    (measurable_const.prodMk measurable_id :
      Measurable fun zs : Fin k → T => (PUnit.unit, zs))
  exact h

/-- **The tilted average is the integral against the density**:
`𝔼(W₁ ⋯ W_k A) = ∫ W₁ ⋯ W_k · A d(μ₁ ⊗ ⋯ ⊗ μ_k)`. -/
theorem cascadeTilt_eq_lintegral_density : ∀ (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G A : (Fin k → T) → ℝ≥0∞}, Measurable G → Measurable A →
    cascadeTilt k ms μs G A = ∫⁻ zs, cascadeTiltDensity k ms μs G zs * A zs ∂Measure.pi μs := by
  intro k
  induction k with
  | zero =>
    intro ms μs _ G A _ hA
    have hm : Measurable fun zs : Fin 0 → T => cascadeTiltDensity 0 ms μs G zs * A zs :=
      measurable_const.mul hA
    rw [cascadeTilt_zero, Measure.pi_of_empty, lintegral_dirac' _ hm, cascadeTiltDensity_zero,
      one_mul]
    exact congrArg A (Subsingleton.elim _ _)
  | succ k ih =>
    intro ms μs _ G A hG hA
    have hm : Measurable fun zs : Fin (k + 1) → T =>
        cascadeTiltDensity (k + 1) ms μs G zs * A zs :=
      (measurable_cascadeTiltDensity (k + 1) ms μs hG).mul hA
    rw [cascadeTilt_succ, lintegral_pi_fin_succ μs hm]
    refine lintegral_congr fun z => ?_
    have hGz : Measurable fun ys : Fin k → T => G (Fin.cons z ys) :=
      hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id))
    have hAz : Measurable fun ys : Fin k → T => A (Fin.cons z ys) :=
      hA.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id))
    have hm' : Measurable fun ys : Fin k → T =>
        cascadeTiltDensity k (Fin.tail ms) (Fin.tail μs) (fun ys => G (Fin.cons z ys)) ys
          * A (Fin.cons z ys) :=
      (measurable_cascadeTiltDensity k _ _ hGz).mul hAz
    rw [ih (Fin.tail ms) (Fin.tail μs) hGz hAz, ← lintegral_const_mul _ hm']
    refine lintegral_congr fun ys => ?_
    rw [cascadeTiltDensity_cons, mul_assoc]

/-! ### The tilted measure -/

/-- **Talagrand's tilted probability measure**: the law on `T^k` with density `W₁ ⋯ W_k` with
respect to the product law of the marks, against which the tilted averages `𝔼(W₁ ⋯ W_k A)` of
(14.24)–(14.26) are integrals. -/
noncomputable def cascadeTiltMeasure (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] (G : (Fin k → T) → ℝ≥0∞) : Measure (Fin k → T) :=
  (Measure.pi μs).withDensity (cascadeTiltDensity k ms μs G)

theorem lintegral_cascadeTiltMeasure (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G A : (Fin k → T) → ℝ≥0∞} (hG : Measurable G)
    (hA : Measurable A) :
    ∫⁻ zs, A zs ∂cascadeTiltMeasure k ms μs G = cascadeTilt k ms μs G A := by
  rw [cascadeTiltMeasure, lintegral_withDensity_eq_lintegral_mul _
    (measurable_cascadeTiltDensity k ms μs hG) hA, cascadeTilt_eq_lintegral_density k ms μs hG hA]
  rfl

/-- Under Talagrand's (14.4) the tilted measure is a probability measure. -/
theorem cascadeTiltMeasure_univ (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G : (Fin k → T) → ℝ≥0∞} (hG : Measurable G)
    (hGpos : ∀ zs, 0 < G zs) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (hfin : ∫⁻ zs, G zs ∂Measure.pi μs ≠ ∞) :
    cascadeTiltMeasure k ms μs G univ = 1 := by
  rw [← lintegral_one, lintegral_cascadeTiltMeasure k ms μs hG measurable_const,
    cascadeTilt_one k ms μs hG hGpos hpos hle hfin]

theorem isProbabilityMeasure_cascadeTiltMeasure (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G : (Fin k → T) → ℝ≥0∞} (hG : Measurable G)
    (hGpos : ∀ zs, 0 < G zs) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (hfin : ∫⁻ zs, G zs ∂Measure.pi μs ≠ ∞) :
    IsProbabilityMeasure (cascadeTiltMeasure k ms μs G) :=
  IsProbabilityMeasure.mk (cascadeTiltMeasure_univ k ms μs hG hGpos hpos hle hfin)

/-- Under (14.4) the density is almost everywhere finite. -/
theorem ae_cascadeTiltDensity_lt_top (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G : (Fin k → T) → ℝ≥0∞} (hG : Measurable G)
    (hGpos : ∀ zs, 0 < G zs) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (hfin : ∫⁻ zs, G zs ∂Measure.pi μs ≠ ∞) :
    ∀ᵐ zs ∂Measure.pi μs, cascadeTiltDensity k ms μs G zs < ∞ := by
  refine ae_lt_top (measurable_cascadeTiltDensity k ms μs hG) ?_
  have h := cascadeTilt_one k ms μs hG hGpos hpos hle hfin
  rw [cascadeTilt_eq_lintegral_density k ms μs hG measurable_const] at h
  simp only [mul_one] at h
  rw [h]
  exact one_ne_top

/-- **Signed tilted averages**: the Bochner integral against the tilted measure is the integral of
`W₁ ⋯ W_k · f` against the product law. -/
theorem integral_cascadeTiltMeasure (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G : (Fin k → T) → ℝ≥0∞} (hG : Measurable G)
    (hGpos : ∀ zs, 0 < G zs) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (hfin : ∫⁻ zs, G zs ∂Measure.pi μs ≠ ∞) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : (Fin k → T) → E) :
    ∫ zs, f zs ∂cascadeTiltMeasure k ms μs G
      = ∫ zs, (cascadeTiltDensity k ms μs G zs).toReal • f zs ∂Measure.pi μs :=
  integral_withDensity_eq_integral_toReal_smul (measurable_cascadeTiltDensity k ms μs hG)
    (ae_cascadeTiltDensity_lt_top k ms μs hG hGpos hpos hle hfin) f

/-- The density is integrable (it has integral `1`). -/
theorem integrable_toReal_cascadeTiltDensity (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G : (Fin k → T) → ℝ≥0∞} (hG : Measurable G)
    (hGpos : ∀ zs, 0 < G zs) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (hfin : ∫⁻ zs, G zs ∂Measure.pi μs ≠ ∞) :
    Integrable (fun zs => (cascadeTiltDensity k ms μs G zs).toReal) (Measure.pi μs) := by
  refine integrable_toReal_of_lintegral_ne_top
    (measurable_cascadeTiltDensity k ms μs hG).aemeasurable ?_
  have h := cascadeTilt_one k ms μs hG hGpos hpos hle hfin
  rw [cascadeTilt_eq_lintegral_density k ms μs hG measurable_const] at h
  simp only [mul_one] at h
  rw [h]
  exact one_ne_top

/-- **Talagrand's nesting `𝔼(W₁ ⋯ W_{k+1} f) = 𝔼₁(W₁ 𝔼(W₂ ⋯ W_{k+1} f))`** for bounded
measurable `f`: the tilted average over `k + 1` levels is the `W₁`-weighted average over the
first mark of the tilted averages over the remaining levels. -/
theorem integral_cascadeTiltMeasure_succ (k : ℕ) (ms : Fin (k + 1) → ℝ)
    (μs : Fin (k + 1) → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
    {G : (Fin (k + 1) → T) → ℝ≥0∞} (hG : Measurable G) (hGpos : ∀ zs, 0 < G zs)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) (hfin : ∫⁻ zs, G zs ∂Measure.pi μs ≠ ∞)
    {f : (Fin (k + 1) → T) → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ zs, |f zs| ≤ C) :
    ∫ zs, f zs ∂cascadeTiltMeasure (k + 1) ms μs G
      = ∫ z, (cascadeW k ms μs G z).toReal
          * ∫ ys, f (Fin.cons z ys) ∂cascadeTiltMeasure k (Fin.tail ms) (Fin.tail μs)
              (fun ys => G (Fin.cons z ys)) ∂μs 0 := by
  rw [integral_cascadeTiltMeasure (k + 1) ms μs hG hGpos hpos hle hfin]
  have hint : Integrable (fun zs => (cascadeTiltDensity (k + 1) ms μs G zs).toReal • f zs)
      (Measure.pi μs) := by
    have h := (integrable_toReal_cascadeTiltDensity (k + 1) ms μs hG hGpos hpos hle hfin).bdd_mul
      hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun zs => by rw [Real.norm_eq_abs]; exact hC zs)
    refine h.congr (Filter.Eventually.of_forall fun zs => ?_)
    simp only [smul_eq_mul, mul_comm]
  rw [integral_pi_fin_succ μs hint]
  refine integral_congr_ae ?_
  filter_upwards [ae_lintegral_pi_cons_ne_top k μs hG hfin] with z hz
  have hGz : Measurable fun ys : Fin k → T => G (Fin.cons z ys) :=
    hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id))
  rw [integral_cascadeTiltMeasure k (Fin.tail ms) (Fin.tail μs) hGz (fun ys => hGpos _)
    (fun i => hpos i.succ) (fun i => hle i.succ) hz, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ys => ?_)
  show (cascadeTiltDensity (k + 1) ms μs G (Fin.cons z ys)).toReal • f (Fin.cons z ys)
    = (cascadeW k ms μs G z).toReal * ((cascadeTiltDensity k (Fin.tail ms) (Fin.tail μs)
        (fun ys => G (Fin.cons z ys)) ys).toReal • f (Fin.cons z ys))
  rw [cascadeTiltDensity_cons, ENNReal.toReal_mul, smul_eq_mul, smul_eq_mul, mul_assoc]

end ProbabilityTheory
