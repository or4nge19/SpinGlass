/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.Distributions.Gaussian_IBP_Hilbert

/-!
# First-order Gaussian integration by parts along a linear substitution

`ProbabilityTheory.IsGaussian.integral_inner_mul_eq_integral_fderiv_covarianceOperator` is
Gaussian integration by parts for a functional of the Gaussian vector itself. In applications the
functional depends on the vector only through a **linear image** of it: the Hamiltonian of a spin
glass is a linear function `A x` of an underlying Gaussian vector `x`, and one wants to
differentiate with respect to a *component* of `x` that is not the Hamiltonian.

The substituted formula

`∫ ⟪x, h⟫ G(A x) ∂P = ∫ (DG (A x)) (A (C_P h)) ∂P`

is the first-order companion of the second-order two-map trace identity
`ProbabilityTheory.IsGaussian.integral_fderiv_clm_add_apply_clm`. Note that the direction in which
`G` is differentiated is `A (C_P h)` — the *cross-covariance* between the tested direction `h` and
the image — which is exactly what makes it possible to isolate one summand of a mixed Hamiltonian.

## Main statements

- `ProbabilityTheory.IsGaussian.integral_inner_mul_comp_clm`: the substituted formula.
-/

open scoped Filter BigOperators Topology ProbabilityTheory ENNReal InnerProductSpace NNReal
open MeasureTheory Filter Set

noncomputable section

namespace ProbabilityTheory

variable {Ω : Type*} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω] [CompleteSpace Ω]
variable [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {P : Measure Ω} [IsGaussian P]

namespace IsGaussian

variable (P)

/-- **First-order Gaussian integration by parts along a linear substitution.** For a centered
Gaussian `P` on `Ω`, a continuous linear `A : Ω →L[ℝ] E` and a `C¹` functional `G` of polynomial
growth on `E`,

`∫ ⟪x, h⟫ G(A x) ∂P = ∫ (DG (A x)) (A (C_P h)) ∂P`.

The case `A = id` is
`ProbabilityTheory.IsGaussian.integral_inner_mul_eq_integral_fderiv_covarianceOperator`. -/
theorem integral_inner_mul_comp_clm
    (hmean0 : (∫ x : Ω, x ∂P) = 0) (A : Ω →L[ℝ] E) (h : Ω)
    (G : E → ℝ) (hG_c1 : ContDiff ℝ 1 G)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hG_growth : ∀ y : E, |G y| ≤ C * (1 + ‖y‖) ^ m)
    (hG'_growth : ∀ y : E, ‖fderiv ℝ G y‖ ≤ C * (1 + ‖y‖) ^ m) :
    (∫ x : Ω, ⟪x, h⟫_ℝ * G (A x) ∂P)
      = ∫ x : Ω, (fderiv ℝ G (A x)) (A (covarianceOperator P h)) ∂P := by
  have hA0 : (0 : ℝ) ≤ ‖A‖ := norm_nonneg A
  -- the composed functional
  have hFmeas : Measurable fun x : Ω => G (A x) :=
    (hG_c1.continuous.comp A.continuous).measurable
  have hFc1 : ContDiff ℝ 1 fun x : Ω => G (A x) := hG_c1.comp A.contDiff
  have hFderiv : ∀ x : Ω,
      fderiv ℝ (fun y : Ω => G (A y)) x = (fderiv ℝ G (A x)).comp A := by
    intro x
    have h := fderiv_comp (𝕜 := ℝ) x (hG_c1.differentiable (by norm_num) (A x)) A.differentiableAt
    simpa [Function.comp_def, ContinuousLinearMap.fderiv] using h
  -- the polynomial-growth transfer
  have hstep : ∀ x : Ω, (1 + ‖A x‖) ^ m ≤ (1 + ‖A‖) ^ m * (1 + ‖x‖) ^ m := by
    intro x
    have h1 : (1 : ℝ) + ‖A x‖ ≤ (1 + ‖A‖) * (1 + ‖x‖) := by
      have := A.le_opNorm x
      nlinarith [norm_nonneg x, norm_nonneg (A x), hA0]
    calc (1 + ‖A x‖) ^ m ≤ ((1 + ‖A‖) * (1 + ‖x‖)) ^ m :=
          pow_le_pow_left₀ (by positivity) h1 m
      _ = (1 + ‖A‖) ^ m * (1 + ‖x‖) ^ m := by rw [mul_pow]
  set C' : ℝ := C * (1 + ‖A‖) ^ (m + 1) with hC'
  have hC'0 : 0 ≤ C' := by positivity
  have hA1 : (1 : ℝ) ≤ 1 + ‖A‖ := by linarith
  have hCm0 : (0 : ℝ) ≤ C * (1 + ‖A‖) ^ m := by positivity
  have hCeq : C * (1 + ‖A‖) ^ m * (1 + ‖A‖) = C' := by rw [hC', pow_succ]; ring
  have hFg : ∀ x : Ω, |G (A x)| ≤ C' * (1 + ‖x‖) ^ m := by
    intro x
    calc |G (A x)| ≤ C * (1 + ‖A x‖) ^ m := hG_growth (A x)
      _ ≤ C * ((1 + ‖A‖) ^ m * (1 + ‖x‖) ^ m) := mul_le_mul_of_nonneg_left (hstep x) hC
      _ ≤ C' * (1 + ‖x‖) ^ m := by
          have hpos : (0 : ℝ) ≤ (1 + ‖x‖) ^ m := by positivity
          have hkey : C * (1 + ‖A‖) ^ m ≤ C' := by
            rw [← hCeq]
            exact le_mul_of_one_le_right hCm0 hA1
          calc C * ((1 + ‖A‖) ^ m * (1 + ‖x‖) ^ m)
              = (C * (1 + ‖A‖) ^ m) * (1 + ‖x‖) ^ m := by ring
            _ ≤ C' * (1 + ‖x‖) ^ m := mul_le_mul_of_nonneg_right hkey hpos
  have hFg' : ∀ x : Ω,
      ‖fderiv ℝ (fun x : Ω => G (A x)) x‖ ≤ C' * (1 + ‖x‖) ^ m := by
    intro x
    have hop : ‖(fderiv ℝ G (A x)).comp A‖ ≤ ‖fderiv ℝ G (A x)‖ * ‖A‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    rw [hFderiv x]
    calc ‖(fderiv ℝ G (A x)).comp A‖ ≤ ‖fderiv ℝ G (A x)‖ * ‖A‖ := hop
      _ ≤ (C * (1 + ‖A x‖) ^ m) * ‖A‖ :=
          mul_le_mul_of_nonneg_right (hG'_growth (A x)) hA0
      _ ≤ (C * ((1 + ‖A‖) ^ m * (1 + ‖x‖) ^ m)) * ‖A‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hstep x) hC) hA0
      _ ≤ C' * (1 + ‖x‖) ^ m := by
          have hpos : (0 : ℝ) ≤ (1 + ‖x‖) ^ m := by positivity
          have hkey : C * (1 + ‖A‖) ^ m * ‖A‖ ≤ C' := by
            rw [← hCeq]
            exact mul_le_mul_of_nonneg_left (by linarith) hCm0
          calc C * ((1 + ‖A‖) ^ m * (1 + ‖x‖) ^ m) * ‖A‖
              = (C * (1 + ‖A‖) ^ m * ‖A‖) * (1 + ‖x‖) ^ m := by ring
            _ ≤ C' * (1 + ‖x‖) ^ m := mul_le_mul_of_nonneg_right hkey hpos
  have hbase := integral_inner_mul_eq_integral_fderiv_covarianceOperator (μ := P) hmean0 h
    (fun x : Ω => G (A x)) hFmeas hFc1 hC'0 hFg hFg'
  rw [hbase]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hFderiv x, ContinuousLinearMap.coe_comp, Function.comp_apply]

end IsGaussian

end ProbabilityTheory
