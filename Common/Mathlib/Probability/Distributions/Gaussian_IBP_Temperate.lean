/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Analysis.Distribution.TemperateGrowthFDeriv
import Common.Mathlib.Probability.Distributions.Gaussian_Divergence
import Common.Mathlib.Probability.Distributions.Gaussian_IBP2_Hilbert

/-!
# Gaussian integration by parts under `HasTemperateGrowth`

The second-order Gaussian formulae are stated in `Gaussian_IBP2_Hilbert` and
`Gaussian_Divergence` with explicit polynomial-growth constants for `F`, `DF` and `D²F`. That is
the weakest hypothesis, but it is not the ergonomic one: Mathlib already has the class of smooth
functions with polynomially bounded derivatives, `Function.HasTemperateGrowth`, together with a
full closure calculus (`.add`, `.mul`, `.comp`, `.smul`, `hasTemperateGrowth_inner_left`, …).

This file restates the formulae with that single hypothesis, and then proves the identity the
Gaussian interpolation method actually consumes:

`∫ (DF (a • x + c)) x ∂μ = a • ∑ i, ∫ ((D²F (a • x + c)) (C bᵢ)) bᵢ ∂μ`.

Applied with `a = √t`, `c = √(1-t) y` (and symmetrically) this is what converts
`d/dt 𝔼 F(√t X + √(1-t) Y)` into a covariance-weighted Hessian trace — Talagrand Vol. I, §1.3
(Eq. (1.65)) and Vol. II, §8.2.

## Main statements

- `IsGaussian.integral_inner_mul_inner_mul_of_temperate`: Price's theorem, one hypothesis.
- `IsGaussian.integral_fderiv_apply_self_of_temperate`: the divergence identity, one hypothesis.
- `IsGaussian.integral_fderiv_affine_apply_self`: the affine trace identity.
- `IsGaussian.integral_fderiv_clm_add_apply_clm`: **the two-map trace identity**, the interpolation
  engine.
-/

open scoped Filter BigOperators Topology ProbabilityTheory ENNReal InnerProductSpace NNReal
open scoped ContDiff
open MeasureTheory Filter Set

noncomputable section

namespace ProbabilityTheory

section Hilbert

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {μ : Measure E} [IsGaussian μ]

namespace IsGaussian

variable (μ)

/-- **Price's theorem** (second-order Gaussian integration by parts) with the single Mathlib-native
hypothesis `Function.HasTemperateGrowth`. -/
theorem integral_inner_mul_inner_mul_of_temperate
    (hmean0 : (∫ x : E, x ∂μ) = 0) (h k : E)
    (F : E → ℝ) (hF : Function.HasTemperateGrowth F) :
    (∫ x : E, ⟪x, h⟫_ℝ * (⟪x, k⟫_ℝ * F x) ∂μ)
      = ⟪covarianceOperator μ h, k⟫_ℝ * (∫ x : E, F x ∂μ)
        + ∫ x : E, ((fderiv ℝ (fderiv ℝ F) x) (covarianceOperator μ k))
            (covarianceOperator μ h) ∂μ := by
  obtain ⟨C, m, hC, h0, h1, h2⟩ := hF.exists_bound_fderiv_two
  exact integral_inner_mul_inner_mul_eq_covariance_add_integral_fderiv2 (μ := μ) hmean0 h k F
    hF.1.continuous.measurable (hF.1.of_le (by simp)) hC
    (fun x => by simpa [Real.norm_eq_abs] using h0 x) h1 h2

/-- **The Gaussian divergence identity** with the single hypothesis
`Function.HasTemperateGrowth`. -/
theorem integral_fderiv_apply_self_of_temperate
    (hmean0 : (∫ x : E, x ∂μ) = 0) (b : OrthonormalBasis ι ℝ E)
    (F : E → ℝ) (hF : Function.HasTemperateGrowth F) :
    (∫ x : E, (fderiv ℝ F x) x ∂μ)
      = ∑ i : ι, ∫ x : E,
          ((fderiv ℝ (fderiv ℝ F) x) (covarianceOperator μ (b i))) (b i) ∂μ := by
  obtain ⟨C, m, hC, _h0, h1, h2⟩ := hF.exists_bound_fderiv_two
  exact integral_fderiv_apply_self_eq_sum_integral_fderiv2 (μ := μ) hmean0 b F
    (hF.1.of_le (by simp)) hC h1 h2

/-! ### Affine and linear substitutions

Thin corollaries of the explicit-constant versions in `Gaussian_Divergence`: temperate growth
supplies the constants via `HasTemperateGrowth.exists_bound_fderiv_two`. -/

/-- **The affine Gaussian trace identity** with the single hypothesis
`Function.HasTemperateGrowth`:
`∫ (DF (a • x + c)) x ∂μ = a * ∑ i, ∫ ((D²F (a • x + c)) (C bᵢ)) bᵢ ∂μ`.
Talagrand Vol. I, §1.3, Eq. (1.65). -/
theorem integral_fderiv_affine_apply_self
    (hmean0 : (∫ x : E, x ∂μ) = 0) (b : OrthonormalBasis ι ℝ E)
    (F : E → ℝ) (hF : Function.HasTemperateGrowth F) (a : ℝ) (c : E) :
    (∫ x : E, (fderiv ℝ F (a • x + c)) x ∂μ)
      = a * ∑ i : ι, ∫ x : E,
          ((fderiv ℝ (fderiv ℝ F) (a • x + c)) (covarianceOperator μ (b i))) (b i) ∂μ := by
  obtain ⟨C, m, hC, _h0, h1, h2⟩ := hF.exists_bound_fderiv_two
  exact integral_fderiv_affine_apply_self_eq_sum (μ := μ) hmean0 b F
    (hF.1.of_le (by simp)) hC h1 h2 a c

section Substitution

variable {κ : Type*} [Fintype κ]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

omit [CompleteSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
/-- **The two-map Gaussian trace identity** with the single hypothesis
`Function.HasTemperateGrowth`:
`∫ (DF (A x + c)) (B x) ∂μ = ∑ i, ∫ ((D²F (A x + c)) (A (C bᵢ))) (B bᵢ) ∂μ`.
Talagrand Vol. I, §1.3, Eq. (1.65). -/
theorem integral_fderiv_clm_add_apply_clm
    (hmean0 : (∫ x : E, x ∂μ) = 0) (b : OrthonormalBasis ι ℝ E)
    (A B : E →L[ℝ] G) (c : G) (F : G → ℝ) (hF : Function.HasTemperateGrowth F) :
    (∫ x : E, (fderiv ℝ F (A x + c)) (B x) ∂μ)
      = ∑ i : ι, ∫ x : E,
          ((fderiv ℝ (fderiv ℝ F) (A x + c)) (A (covarianceOperator μ (b i))))
            (B (b i)) ∂μ := by
  obtain ⟨C, m, hC, _h0, h1, h2⟩ := hF.exists_bound_fderiv_two
  exact integral_fderiv_clm_add_apply_clm_eq_sum (μ := μ) hmean0 b A B c F
    (hF.1.of_le (by simp)) hC h1 h2

/-- **The Gaussian trace identity along a linear substitution** with the single hypothesis
`Function.HasTemperateGrowth`. The trace is taken against the pushforward covariance
`covarianceOperator (μ.map A)`. Talagrand Vol. I, §1.3, Eq. (1.65). -/
theorem integral_fderiv_comp_clm_apply_self
    (hmean0 : (∫ x : E, x ∂μ) = 0) (A : E →L[ℝ] G) (c : G) (bG : OrthonormalBasis κ ℝ G)
    (F : G → ℝ) (hF : Function.HasTemperateGrowth F) :
    (∫ x : E, (fderiv ℝ F (A x + c)) (A x) ∂μ)
      = ∑ j : κ, ∫ x : E,
          ((fderiv ℝ (fderiv ℝ F) (A x + c))
            (covarianceOperator (μ.map A) (bG j))) (bG j) ∂μ := by
  obtain ⟨C, m, hC, _h0, h1, h2⟩ := hF.exists_bound_fderiv_two
  exact integral_fderiv_comp_clm_apply_self_eq_sum (μ := μ) hmean0 A c bG F
    (hF.1.of_le (by simp)) hC h1 h2

end Substitution

end IsGaussian

end Hilbert

end ProbabilityTheory
