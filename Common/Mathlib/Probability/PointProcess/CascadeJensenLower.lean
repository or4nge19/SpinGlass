/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.MeasureTheory.Integral.LogJensen
import Common.Mathlib.Probability.PointProcess.CascadeTiltMeasure

/-!
# The lower Jensen bound for the cascade recursion

Talagrand's `F₁ = parisiRec k ms μs F` (Vol. II, (14.5)) satisfies the two-sided Jensen bound
`𝔼 F ≤ F₁ ≤ log 𝔼 exp F` for exponents `0 < m_p ≤ 1`: the upper half is
`cascadeRec_le_lintegral_pi`, and the lower half `integral_le_parisiRec` is proved here, level by
level from `(1/m) log 𝔼 exp (m X) ≥ 𝔼 X` (`integral_log_le_log_integral`). The bound is uniform
in the exponents, which is what makes `log cascadeRec` integrable in a parameter without any
strict-monotonicity assumption on the `m_p` (`SpinGlass.integrable_log_cascadeRec`).
-/

open MeasureTheory Set Filter Function
open scoped ENNReal

namespace ProbabilityTheory

open ENNReal

universe u

noncomputable section

variable {T : Type u} [MeasurableSpace T]

/-- **The recursion dominates the mean**: `∫ F d(μ₁ ⊗ ⋯ ⊗ μ_k) ≤ F₁` for `0 < m_p ≤ 1`, when `F`
is integrable and satisfies Talagrand's (14.4). -/
theorem integral_le_parisiRec (k : ℕ) :
    ∀ (ms : Fin k → ℝ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
      {F : (Fin k → T) → ℝ}, Measurable F → (∀ i, 0 < ms i) → (∀ i, ms i ≤ 1) →
      ∫⁻ zs, ENNReal.ofReal (Real.exp (F zs)) ∂Measure.pi μs ≠ ∞ →
      Integrable F (Measure.pi μs) →
      ∫ zs, F zs ∂Measure.pi μs ≤ parisiRec k ms μs F := by
  induction k with
  | zero =>
    intro ms μs _ F hF _ _ _ _
    rw [parisiRec_zero, Measure.pi_of_empty, integral_dirac' _ _ hF.stronglyMeasurable]
    exact le_of_eq (congrArg F (Subsingleton.elim _ _))
  | succ k ih =>
    intro ms μs _ F hF hpos hle hfin hFi
    have hm : 0 < ms 0 := hpos 0
    have hG : Measurable fun zs : Fin (k + 1) → T => ENNReal.ofReal (Real.exp (F zs)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hF)
    have hFz : ∀ z, Measurable fun zs => F (Fin.cons z zs) := fun z =>
      hF.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id))
    have hGz : ∀ z, Measurable fun zs => ENNReal.ofReal (Real.exp (F (Fin.cons z zs))) :=
      fun z => ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hFz z))
    -- `X z = F₂(z)`, the recursion of the tail, and `E z = 𝔼 exp F(z, ·)`
    set X : T → ℝ := fun z =>
      parisiRec k (Fin.tail ms) (Fin.tail μs) (fun zs => F (Fin.cons z zs)) with hX
    set E : T → ℝ≥0∞ := fun z =>
      ∫⁻ zs, ENNReal.ofReal (Real.exp (F (Fin.cons z zs))) ∂Measure.pi (Fin.tail μs) with hE
    have hEm : Measurable E := Measurable.lintegral_prod_right' (hG.comp measurable_fin_cons)
    have hEfin : ∫⁻ z, E z ∂μs 0 ≠ ∞ := by rwa [lintegral_pi_fin_succ μs hG] at hfin
    have hEint : Integrable (fun z => (E z).toReal) (μs 0) :=
      integrable_toReal_of_lintegral_ne_top hEm.aemeasurable hEfin
    have hEae : ∀ᵐ z ∂μs 0, E z < ∞ := ae_lt_top hEm hEfin
    have hR : Measurable fun z => cascadeRec k (Fin.tail ms) (Fin.tail μs)
        (fun zs => ENNReal.ofReal (Real.exp (F (Fin.cons z zs)))) :=
      measurable_cascadeRec_cons k _ _ hG
    have hRpos : ∀ z, 0 < cascadeRec k (Fin.tail ms) (Fin.tail μs)
        (fun zs => ENNReal.ofReal (Real.exp (F (Fin.cons z zs)))) := fun z =>
      cascadeRec_pos k _ _ (hGz z) (fun zs => ENNReal.ofReal_pos.2 (Real.exp_pos _))
        (fun i => hpos i.succ)
    have hRle : ∀ z, cascadeRec k (Fin.tail ms) (Fin.tail μs)
        (fun zs => ENNReal.ofReal (Real.exp (F (Fin.cons z zs)))) ≤ E z := fun z =>
      cascadeRec_le_lintegral_pi k (Fin.tail ms) (Fin.tail μs) (hGz z) (fun i => hpos i.succ)
        (fun i => hle i.succ)
    have hXm : Measurable X := hR.ennreal_toReal.log
    -- `exp X = cascadeRec.toReal ≤ E.toReal` where `E < ∞`
    have hexpX : ∀ᵐ z ∂μs 0, Real.exp (X z) ≤ (E z).toReal := by
      filter_upwards [hEae] with z hz
      have h1 : (cascadeRec k (Fin.tail ms) (Fin.tail μs)
          (fun zs => ENNReal.ofReal (Real.exp (F (Fin.cons z zs))))).toReal ≤ (E z).toReal :=
        ENNReal.toReal_mono hz.ne (hRle z)
      have h2 : 0 < (cascadeRec k (Fin.tail ms) (Fin.tail μs)
          (fun zs => ENNReal.ofReal (Real.exp (F (Fin.cons z zs))))).toReal :=
        ENNReal.toReal_pos (hRpos z).ne' (ne_top_of_le_ne_top hz.ne (hRle z))
      simp only [hX, parisiRec]
      rw [Real.exp_log h2]
      exact h1
    -- the lower bound at a.e. `z` (induction hypothesis) and the upper bound `X ≤ E.toReal`
    have hlow : ∀ᵐ z ∂μs 0, ∫ zs, F (Fin.cons z zs) ∂Measure.pi (Fin.tail μs) ≤ X z := by
      filter_upwards [hEae, ae_integrable_pi_fin_succ μs hFi] with z hz hzi
      exact ih (Fin.tail ms) (Fin.tail μs) (hFz z) (fun i => hpos i.succ) (fun i => hle i.succ)
        hz.ne hzi
    have hup : ∀ᵐ z ∂μs 0, X z ≤ (E z).toReal := by
      filter_upwards [hexpX] with z hz
      linarith [Real.add_one_le_exp (X z)]
    have hIi := integrable_integral_pi_fin_succ μs hFi
    have hbd : Integrable (fun z => |∫ zs, F (Fin.cons z zs) ∂Measure.pi (Fin.tail μs)|
        + (E z).toReal) (μs 0) := hIi.abs.add hEint
    have hXi : Integrable X (μs 0) := by
      refine Integrable.mono' hbd hXm.aestronglyMeasurable ?_
      filter_upwards [hlow, hup] with z h1 h2
      rw [Real.norm_eq_abs]
      have := abs_nonneg (∫ zs, F (Fin.cons z zs) ∂Measure.pi (Fin.tail μs))
      have := ENNReal.toReal_nonneg (a := E z)
      refine abs_le.2 ⟨?_, ?_⟩
      · linarith [neg_abs_le (∫ zs, F (Fin.cons z zs) ∂Measure.pi (Fin.tail μs))]
      · linarith
    -- `exp (m X) ≤ 1 + E.toReal`
    have hbd2 : Integrable (fun z => 1 + (E z).toReal) (μs 0) := (integrable_const 1).add hEint
    have hexpi : Integrable (fun z => Real.exp (ms 0 * X z)) (μs 0) := by
      refine Integrable.mono' hbd2
        (Real.measurable_exp.comp (hXm.const_mul _)).aestronglyMeasurable ?_
      filter_upwards [hexpX] with z hz
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rcases le_or_gt (X z) 0 with h | h
      · have : Real.exp (ms 0 * X z) ≤ 1 :=
          Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos hm.le h)
        linarith [ENNReal.toReal_nonneg (a := E z)]
      · have : Real.exp (ms 0 * X z) ≤ Real.exp (X z) :=
          Real.exp_le_exp.2 (mul_le_of_le_one_left h.le (hle 0))
        linarith
    -- Jensen at the top level: `m ∫ X ≤ log ∫ exp (m X)`
    have hJ : ms 0 * ∫ z, X z ∂μs 0 ≤ Real.log (∫ z, Real.exp (ms 0 * X z) ∂μs 0) := by
      have h := integral_log_le_log_integral (f := fun z => Real.exp (ms 0 * X z))
        (Eventually.of_forall fun z => Real.exp_pos _) hexpi (by
          simp only [Real.log_exp]
          exact hXi.const_mul _)
      simpa only [Real.log_exp, integral_const_mul] using h
    have hcfin : cascadeRec (k + 1) ms μs (fun zs => ENNReal.ofReal (Real.exp (F zs))) ≠ ∞ :=
      ne_top_of_le_ne_top hfin (cascadeRec_le_lintegral_pi (k + 1) ms μs hG hpos hle)
    rw [parisiRec_succ k ms μs hF hpos hcfin, integral_pi_fin_succ μs hFi]
    calc ∫ z, (∫ zs, F (Fin.cons z zs) ∂Measure.pi (Fin.tail μs)) ∂μs 0
        ≤ ∫ z, X z ∂μs 0 := integral_mono_ae hIi hXi hlow
      _ ≤ (1 / ms 0) * Real.log (∫ z, Real.exp (ms 0 * X z) ∂μs 0) := by
          rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hm, mul_comm]
          exact hJ

/-- **The two-sided Jensen bound** `𝔼 F ≤ F₁ ≤ log 𝔼 exp F` for `0 < m_p ≤ 1`. -/
theorem parisiRec_le_log_integral_exp (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {F : (Fin k → T) → ℝ} (hF : Measurable F)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (hfin : ∫⁻ zs, ENNReal.ofReal (Real.exp (F zs)) ∂Measure.pi μs ≠ ∞) :
    parisiRec k ms μs F
      ≤ Real.log (∫⁻ zs, ENNReal.ofReal (Real.exp (F zs)) ∂Measure.pi μs).toReal := by
  have hG : Measurable fun zs : Fin k → T => ENNReal.ofReal (Real.exp (F zs)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hF)
  have h1 := cascadeRec_le_lintegral_pi k ms μs hG hpos hle
  have h2 : 0 < cascadeRec k ms μs (fun zs => ENNReal.ofReal (Real.exp (F zs))) :=
    cascadeRec_pos k ms μs hG (fun zs => ENNReal.ofReal_pos.2 (Real.exp_pos _)) hpos
  exact Real.log_le_log (ENNReal.toReal_pos h2.ne' (ne_top_of_le_ne_top hfin h1))
    (ENNReal.toReal_mono hfin h1)

end

end ProbabilityTheory
