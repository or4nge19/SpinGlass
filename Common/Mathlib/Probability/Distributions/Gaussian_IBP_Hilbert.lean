

import Mathlib.Probability.Moments.CovarianceBilin
import Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinThm
import Common.Mathlib.Probability.Distributions.Gaussian.IntegrationByParts

/-!
# Gaussian integration by parts on a real Hilbert space (covariance-operator form)

This file provides the **intrinsic** (coordinate-free) integration-by-parts identity for a
Gaussian measure `μ` on a real Hilbert space `H`, phrased using Mathlib's intrinsic covariance
operator `ProbabilityTheory.covarianceOperator`.

The proof is a corollary of the Cameron–Martin integration-by-parts theorem
(`ProbabilityTheory.cameronMartin_integral_by_parts_polyGrowth`) together with an identification
of the Cameron–Martin direction `cmCoe (cmOfDual (innerSL ℝ h))` with `covarianceOperator μ h` in
the centered case.

## Main results

- `ProbabilityTheory.IsGaussian.integral_inner_mul_eq_integral_fderiv_covarianceOperator_polyGrowth`
- `ProbabilityTheory.cmCoe_cmOfDual_innerSL_eq_covarianceOperator`
-/

open scoped Filter BigOperators Topology ProbabilityTheory ENNReal InnerProductSpace NNReal
open MeasureTheory Filter Set

noncomputable section

namespace ProbabilityTheory

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {μ : Measure H} [IsGaussian μ]

private lemma memLp_id_two : MeasureTheory.MemLp (fun x : H => x) 2 μ := by
  simpa using (IsGaussian.memLp_id (μ := μ) 2 (by norm_num))

private lemma integral_innerSL_eq_zero_of_integral_eq_zero
    (hmean0 : (∫ x : H, x ∂μ) = 0) (v : H) :
    μ[(innerSL ℝ v : StrongDual ℝ H)] = 0 := by
  have hint : Integrable (fun x : H => x) μ := (memLp_id_two (μ := μ)).integrable (by norm_num)
  have hmean :
      μ[(innerSL ℝ v : StrongDual ℝ H)] = (innerSL ℝ v) (∫ x : H, x ∂μ) := by
    simpa using ((innerSL ℝ v : StrongDual ℝ H).integral_comp_comm hint)
  simpa [hmean0] using hmean

private lemma inner_cmCoe_cmOfDual_eq_covarianceBilinDual (u h : H) :
    ⟪(cmCoe (μ := μ))
        ((cmOfDual (E := H) (μ := μ) (innerSL ℝ h : StrongDual ℝ H) : cameronMartin μ)),
      u⟫_ℝ
      =
      covarianceBilinDual μ (innerSL ℝ u : StrongDual ℝ H) (innerSL ℝ h : StrongDual ℝ H) := by
  have h_eval :
      (innerSL ℝ u : StrongDual ℝ H)
            ((cmCoe (μ := μ))
              ((cmOfDual (E := H) (μ := μ) (innerSL ℝ h : StrongDual ℝ H) : cameronMartin μ)))
        =
      ⟪cmOfDual (E := H) (μ := μ) (innerSL ℝ u : StrongDual ℝ H),
        (cmOfDual (E := H) (μ := μ) (innerSL ℝ h : StrongDual ℝ H) : cameronMartin μ)⟫_ℝ := by
    simpa using
      (apply_cmCoe_eq_inner (μ := μ)
        (x := (cmOfDual (E := H) (μ := μ) (innerSL ℝ h : StrongDual ℝ H) : cameronMartin μ))
        (L := (innerSL ℝ u : StrongDual ℝ H)))
  have h_inner :
      ⟪cmOfDual (E := H) (μ := μ) (innerSL ℝ u : StrongDual ℝ H),
        (cmOfDual (E := H) (μ := μ) (innerSL ℝ h : StrongDual ℝ H) : cameronMartin μ)⟫_ℝ
        =
      covarianceBilinDual μ (innerSL ℝ u : StrongDual ℝ H) (innerSL ℝ h : StrongDual ℝ H) := by
    simpa using
      (cmOfDual_inner (E := H) (μ := μ)
        (innerSL ℝ u : StrongDual ℝ H) (innerSL ℝ h : StrongDual ℝ H))
  simpa [real_inner_comm, h_inner] using h_eval

private lemma covarianceBilinDual_innerSL_eq_integral_mul
    (hmean0 : (∫ x : H, x ∂μ) = 0) (hLp2 : MeasureTheory.MemLp (fun x : H => x) 2 μ)
    (u h : H) :
    covarianceBilinDual μ (innerSL ℝ u : StrongDual ℝ H) (innerSL ℝ h : StrongDual ℝ H)
      = ∫ z : H, ⟪h, z⟫_ℝ * ⟪u, z⟫_ℝ ∂μ := by
  have hμ_inner (v : H) :
      μ[(innerSL ℝ v : StrongDual ℝ H)] = 0 :=
    integral_innerSL_eq_zero_of_integral_eq_zero (μ := μ) hmean0 v
  have hmean_inner (v : H) : (∫ x : H, ⟪v, x⟫_ℝ ∂μ) = 0 := by
    simpa [innerSL_apply_apply] using (hμ_inner v)
  have hcov' :=
    covarianceBilinDual_apply (μ := μ) (h := hLp2)
      (innerSL ℝ u : StrongDual ℝ H) (innerSL ℝ h : StrongDual ℝ H)
  simpa [hmean_inner u, hmean_inner h, innerSL_apply_apply, mul_comm, mul_left_comm, mul_assoc] using hcov'

/-- Identify `cmCoe (cmOfDual (innerSL ℝ h))` with the covariance operator in the centered case. -/
lemma cmCoe_cmOfDual_innerSL_eq_covarianceOperator
    (hmean0 : (∫ x : H, x ∂μ) = 0) (h : H) :
    (cmCoe (μ := μ))
        ((cmOfDual (E := H) (μ := μ) (innerSL ℝ h : StrongDual ℝ H) : cameronMartin μ))
      = covarianceOperator μ h := by
  classical
  have hLp2 : MeasureTheory.MemLp (fun x : H => x) 2 μ := memLp_id_two (μ := μ)
  refine ext_inner_right ℝ (fun u => ?_)
  have h1 := inner_cmCoe_cmOfDual_eq_covarianceBilinDual (μ := μ) u h
  have h2 := covarianceBilinDual_innerSL_eq_integral_mul (μ := μ) hmean0 hLp2 u h
  have h3 : ⟪covarianceOperator μ h, u⟫_ℝ = ∫ z : H, ⟪h, z⟫_ℝ * ⟪u, z⟫_ℝ ∂μ := by
    simpa using (covarianceOperator_inner (μ := μ) hLp2 h u)
  simpa [h3] using h1.trans (h2.trans h3.symm)

private lemma cmOfDual_innerSL_aeEq_inner
    (hmean0 : (∫ x : H, x ∂μ) = 0) (h : H) :
    ((cmOfDual (E := H) (μ := μ) (innerSL ℝ h : StrongDual ℝ H) : cameronMartin μ) : H → ℝ)
      =ᵐ[μ] fun x => ⟪h, x⟫_ℝ := by
  have hLp2 : MeasureTheory.MemLp (fun x : H => x) 2 μ := memLp_id_two (μ := μ)
  have hcent :=
    (StrongDual.centeredToLp_apply (μ := μ) (E := H) (h := hLp2)
      (innerSL ℝ h : StrongDual ℝ H))
  have hLmean : (innerSL ℝ h : StrongDual ℝ H) (∫ x : H, x ∂μ) = 0 := by
    simp [hmean0]
  simpa [cmOfDual_apply, innerSL_apply_apply, hLmean] using hcent

namespace IsGaussian

variable (μ)

/-- **Gaussian IBP on Hilbert spaces (covariance-operator form, polynomial growth).**

For a centered Gaussian measure `μ` on a real Hilbert space `H`, we have
\[
  \int \langle x, h\rangle\, F(x)\, d\mu(x)
  = \int D F(x)\,(\mathrm{covarianceOperator}\ \mu\ h)\, d\mu(x),
\]
under polynomial growth assumptions on `F` and `fderiv F`. -/
theorem integral_inner_mul_eq_integral_fderiv_covarianceOperator_polyGrowth
    (hmean0 : (∫ x : H, x ∂μ) = 0) (h : H)
    (F : H → ℝ) (hF_meas : Measurable F) (hF_c1 : ContDiff ℝ 1 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ x, |F x| ≤ C * (1 + ‖x‖) ^ m)
    (hF'_growth : ∀ x, ‖fderiv ℝ F x‖ ≤ C * (1 + ‖x‖) ^ m) :
    (∫ x : H, ⟪x, h⟫_ℝ * F x ∂μ)
      = ∫ x : H, (fderiv ℝ F x) (covarianceOperator μ h) ∂μ := by
  have hIBP :=
    (cameronMartin_integral_by_parts_polyGrowth (μ := μ)
        (x := (cmOfDual (E := H) (μ := μ) (innerSL ℝ h : StrongDual ℝ H) : cameronMartin μ))
        (F := F) hF_meas hF_c1 hC hF_growth hF'_growth)
  have hcm :
      (cmCoe (μ := μ))
          ((cmOfDual (E := H) (μ := μ) (innerSL ℝ h : StrongDual ℝ H) : cameronMartin μ))
        = covarianceOperator μ h :=
    cmCoe_cmOfDual_innerSL_eq_covarianceOperator (μ := μ) hmean0 h
  have hLHS :
      (∫ x : H,
          ((cmOfDual (E := H) (μ := μ) (innerSL ℝ h : StrongDual ℝ H) : cameronMartin μ) x) * F x ∂μ)
        = ∫ x : H, ⟪x, h⟫_ℝ * F x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [cmOfDual_innerSL_aeEq_inner (μ := μ) hmean0 h] with x hx
    simp [hx, real_inner_comm]
  calc
    (∫ x : H, ⟪x, h⟫_ℝ * F x ∂μ)
        = ∫ x : H,
            ((cmOfDual (E := H) (μ := μ) (innerSL ℝ h : StrongDual ℝ H) : cameronMartin μ) x) * F x ∂μ := by
              simpa using hLHS.symm
    _ = ∫ x : H,
          (fderiv ℝ F x)
            ((cmCoe (μ := μ))
              ((cmOfDual (E := H) (μ := μ) (innerSL ℝ h : StrongDual ℝ H) : cameronMartin μ))) ∂μ := hIBP
    _ = ∫ x : H, (fderiv ℝ F x) (covarianceOperator μ h) ∂μ := by simp [hcm]

end IsGaussian

end Hilbert

end ProbabilityTheory
