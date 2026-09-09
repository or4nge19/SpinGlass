/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Common.Mathlib.Probability.Distributions.Gaussian.MultivariateCovariance

/-!
# A product of real Gaussians is a multivariate Gaussian with diagonal covariance

`⊗ᵢ N(mᵢ, vᵢ)`, viewed in `EuclideanSpace ℝ ι`, is the multivariate Gaussian with mean `m` and
covariance matrix `diagonal v` (`ProbabilityTheory.map_pi_gaussianReal_eq_multivariateGaussian`,
by characteristic functions). Consequently it is a Gaussian measure with covariance operator
`diagonal v`; this is the law of any finite family of independent real Gaussians — e.g. the marks
of a finite set of nodes of a Poisson–Dirichlet cascade.
-/

open MeasureTheory ProbabilityTheory Complex Matrix
open scoped NNReal InnerProductSpace

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A product of real Gaussians is a multivariate Gaussian with diagonal covariance.** -/
theorem map_pi_gaussianReal_eq_multivariateGaussian (m : ι → ℝ) (v : ι → ℝ≥0) :
    (Measure.pi fun i => gaussianReal (m i) (v i)).map (WithLp.toLp 2)
      = multivariateGaussian (WithLp.toLp 2 m) (Matrix.diagonal fun i => (v i : ℝ)) := by
  have hS : (Matrix.diagonal fun i => (v i : ℝ)).PosSemidef :=
    Matrix.PosSemidef.diagonal fun i => (v i).2
  apply Measure.ext_of_charFun (E := EuclideanSpace ℝ ι)
  ext t
  rw [charFun_pi, charFun_multivariateGaussian hS]
  simp_rw [charFun_gaussianReal]
  rw [← Complex.exp_sum]
  congr 1
  have hinner : ⟪t, WithLp.toLp 2 m⟫_ℝ = ∑ i, t i * m i := by
    rw [EuclideanSpace.real_inner_eq_dotProduct]
    rfl
  have hquad : (WithLp.ofLp t) ⬝ᵥ (Matrix.diagonal fun i => (v i : ℝ)) *ᵥ (WithLp.ofLp t)
      = ∑ i, (v i : ℝ) * t i ^ 2 := by
    simp only [dotProduct, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hinner, hquad]
  push_cast
  rw [Finset.sum_mul, Finset.sum_div, ← Finset.sum_sub_distrib]

/-- The product of real Gaussians, viewed in `EuclideanSpace ℝ ι`, is a Gaussian measure. -/
instance isGaussian_map_pi_gaussianReal (m : ι → ℝ) (v : ι → ℝ≥0) :
    IsGaussian ((Measure.pi fun i => gaussianReal (m i) (v i)).map (WithLp.toLp 2)) := by
  rw [map_pi_gaussianReal_eq_multivariateGaussian]
  infer_instance

/-- The covariance operator of a centered product of real Gaussians is the diagonal matrix of the
variances. -/
theorem inner_covarianceOperator_map_pi_gaussianReal (v : ι → ℝ≥0)
    (x y : EuclideanSpace ℝ ι) :
    ⟪covarianceOperator ((Measure.pi fun i => gaussianReal 0 (v i)).map (WithLp.toLp 2)) x, y⟫_ℝ
      = ∑ i, (v i : ℝ) * x i * y i := by
  have h := map_pi_gaussianReal_eq_multivariateGaussian (fun _ : ι => (0 : ℝ)) v
  have h0 : (WithLp.toLp 2 fun _ : ι => (0 : ℝ)) = (0 : EuclideanSpace ℝ ι) := rfl
  rw [h0] at h
  rw [h]
  refine (inner_covarianceOperator_multivariateGaussian
    (Matrix.PosSemidef.diagonal fun i => (v i).2) x y).trans ?_
  simp only [dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => (mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm

end ProbabilityTheory
