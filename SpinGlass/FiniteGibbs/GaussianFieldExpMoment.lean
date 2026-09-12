/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.Distributions.Gaussian_Concentration
import SpinGlass.FiniteGibbs.GaussianInterpolation

/-!
# Exponential moments of a Gaussian field

For a Gaussian field `U` on a finite set and coefficients `c`, `exp (∑_x c_x U_x)` is integrable
(`GaussianField.integrable_exp_sum_mul`), by Fernique's theorem through
`IsGaussian.integrable_exp_mul_norm`. This is the integrability behind Talagrand's hypothesis
(14.4) for branch partition functions involving the disorder.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SpinGlass.FiniteGibbs

variable {α : Type*} [Fintype α] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {K : α → α → ℝ}

/-- **Exponential moments of linear functionals of a Gaussian field.** -/
lemma GaussianField.integrable_exp_sum_mul (G : GaussianField (α := α) P K) (c : α → ℝ) :
    Integrable (fun ω => Real.exp (∑ x, c x * G.U ω x)) P := by
  have hG : IsGaussian (P.map G.U) := G.hU.isGaussian_map
  have h1 : Integrable (fun H : EnergySpace α => Real.exp ((∑ x, |c x|) * ‖H‖)) (P.map G.U) :=
    IsGaussian.integrable_exp_mul_norm (μ := P.map G.U) _
  have hcont : Continuous fun H : EnergySpace α => Real.exp (∑ x, c x * H x) :=
    Real.continuous_exp.comp (continuous_finsetSum _ fun x _ => continuous_const.mul
      ((continuous_apply x).comp (PiLp.continuous_ofLp 2 (fun _ : α => ℝ))))
  have h2 : Integrable (fun H : EnergySpace α => Real.exp (∑ x, c x * H x)) (P.map G.U) := by
    refine h1.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun H => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    calc ∑ x, c x * H x ≤ ∑ x, |c x| * ‖H‖ := Finset.sum_le_sum fun x _ => by
          calc c x * H x ≤ |c x * H x| := le_abs_self _
            _ = |c x| * |H x| := abs_mul _ _
            _ ≤ |c x| * ‖H‖ := mul_le_mul_of_nonneg_left
                (by rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le H x) (abs_nonneg _)
      _ = (∑ x, |c x|) * ‖H‖ := (Finset.sum_mul _ _ _).symm
  exact (integrable_map_measure h2.aestronglyMeasurable G.measU.aemeasurable).1 h2

/-- `exp (-(s U(x₁) + s U(x₂)))` has finite expectation. -/
lemma GaussianField.integrable_exp_neg_smul_add (G : GaussianField (α := α) P K) (s : ℝ)
    (x₁ x₂ : α) :
    Integrable (fun ω => Real.exp (-((s • G.U ω) x₁ + (s • G.U ω) x₂))) P := by
  have hG : IsGaussian (P.map G.U) := G.hU.isGaussian_map
  have h1 : Integrable (fun H : EnergySpace α => Real.exp ((2 * |s|) * ‖H‖)) (P.map G.U) :=
    IsGaussian.integrable_exp_mul_norm (μ := P.map G.U) _
  have hcont : Continuous fun H : EnergySpace α => Real.exp (-((s • H) x₁ + (s • H) x₂)) := by
    refine Real.continuous_exp.comp (Continuous.neg (Continuous.add ?_ ?_))
    · exact ((continuous_apply x₁).comp (PiLp.continuous_ofLp 2 (fun _ : α => ℝ))).comp
        (continuous_const_smul s)
    · exact ((continuous_apply x₂).comp (PiLp.continuous_ofLp 2 (fun _ : α => ℝ))).comp
        (continuous_const_smul s)
  have h2 : Integrable (fun H : EnergySpace α => Real.exp (-((s • H) x₁ + (s • H) x₂)))
      (P.map G.U) := by
    refine h1.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun H => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    have hb : ∀ x : α, |(s • H) x| ≤ |s| * ‖H‖ := fun x => by
      rw [PiLp.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left
        (by rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le H x) (abs_nonneg _)
    have h₁ := hb x₁
    have h₂ := hb x₂
    have := neg_abs_le ((s • H) x₁)
    have := neg_abs_le ((s • H) x₂)
    linarith
  exact (integrable_map_measure h2.aestronglyMeasurable G.measU.aemeasurable).1 h2

lemma GaussianField.lintegral_ofReal_exp_neg_smul_add_ne_top (G : GaussianField (α := α) P K)
    (s : ℝ) (x₁ x₂ : α) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-((s • G.U ω) x₁ + (s • G.U ω) x₂))) ∂P ≠ ∞ := by
  have h := (G.integrable_exp_neg_smul_add s x₁ x₂).lintegral_lt_top
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun ω => ?_) h)
  exact le_rfl

/-- The exponential moments, in `ℝ≥0∞`. -/
lemma GaussianField.lintegral_ofReal_exp_sum_mul_ne_top (G : GaussianField (α := α) P K)
    (c : α → ℝ) : ∫⁻ ω, ENNReal.ofReal (Real.exp (∑ x, c x * G.U ω x)) ∂P ≠ ∞ := by
  have h := (G.integrable_exp_sum_mul c).lintegral_lt_top
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun ω => ?_) h)
  exact le_rfl

end SpinGlass.FiniteGibbs
