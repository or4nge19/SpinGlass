/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.CovarianceBilin

/-!
# The covariance operator of a centered multivariate Gaussian is its matrix

Mathlib evaluates the *bilinear form* `covarianceBilin (multivariateGaussian μ S)` as the quadratic
form of `S` (`ProbabilityTheory.covarianceBilin_multivariateGaussian`), and separately provides the
covariance **operator** `covarianceOperator` — the uncentered second-moment operator. For a
centered Gaussian the two agree, and the resulting statement — *the covariance operator of
`multivariateGaussian 0 S` is multiplication by `S`* — is what every computation with a Gaussian
disorder needs, since it is the operator (not the bilinear form) that appears in Gaussian
integration by parts.

## Main statements

- `Matrix.PosSemidef.apply_symm`, `Matrix.PosSemidef.transpose_eq`: a real positive semidefinite
  matrix is symmetric.
- `EuclideanSpace.real_inner_eq_dotProduct`: the inner product is the dot product.
- `ProbabilityTheory.inner_covarianceOperator_multivariateGaussian`: the bilinear form of the
  covariance operator is the quadratic form of the matrix.
- `ProbabilityTheory.covarianceOperator_multivariateGaussian_apply`: **the covariance operator is
  `S *ᵥ ·`.**
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace Matrix

namespace Matrix

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- A real positive semidefinite matrix is symmetric. -/
theorem PosSemidef.apply_symm {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (i j : ι) :
    S i j = S j i := by
  simpa using (hS.isHermitian.apply i j).symm

omit [Fintype ι] in
/-- A real positive semidefinite matrix equals its transpose. -/
theorem PosSemidef.transpose_eq {S : Matrix ι ι ℝ} (hS : S.PosSemidef) : Sᵀ = S := by
  ext i j
  simpa using PosSemidef.apply_symm hS j i

end Matrix

namespace EuclideanSpace

/-- The real inner product on `EuclideanSpace ℝ ι` is the dot product of the underlying tuples. -/
theorem real_inner_eq_dotProduct {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℝ ι) :
    ⟪x, y⟫_ℝ = (WithLp.ofLp x) ⬝ᵥ (WithLp.ofLp y) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end EuclideanSpace

namespace ProbabilityTheory

section Bridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasure μ]

/-- **The covariance bilinear form of a centered measure is the bilinear form of its covariance
operator.** Mathlib's `covarianceOperator` is the *uncentered* second-moment operator, so the two
agree exactly when the mean vanishes. -/
theorem covarianceBilin_eq_inner_covarianceOperator (hmem : MemLp (id : E → E) 2 μ)
    (hmean0 : (∫ z, z ∂μ) = 0) (x y : E) :
    covarianceBilin μ x y = ⟪covarianceOperator μ x, y⟫_ℝ := by
  rw [covarianceBilin_apply hmem, covarianceOperator_inner hmem]
  simp [hmean0]

end Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The bilinear form of the covariance operator of a centered multivariate Gaussian is the
quadratic form of its matrix**, at every pair of vectors. -/
theorem inner_covarianceOperator_multivariateGaussian {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (x y : EuclideanSpace ℝ ι) :
    ⟪covarianceOperator (multivariateGaussian (0 : EuclideanSpace ℝ ι) S) x, y⟫_ℝ
      = (WithLp.ofLp x) ⬝ᵥ S *ᵥ (WithLp.ofLp y) := by
  classical
  set μ : Measure (EuclideanSpace ℝ ι) := multivariateGaussian (0 : EuclideanSpace ℝ ι) S with hμ
  have hmem : MemLp (id : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) 2 μ :=
    ProbabilityTheory.IsGaussian.memLp_two_id
  have hmean : (∫ z : EuclideanSpace ℝ ι, z ∂μ) = 0 := by simp [hμ]
  rw [← covarianceBilin_eq_inner_covarianceOperator hmem hmean x y]
  simpa [hμ] using
    ProbabilityTheory.covarianceBilin_multivariateGaussian
      (μ := (0 : EuclideanSpace ℝ ι)) hS x y

/-- **The covariance operator of a centered multivariate Gaussian is multiplication by its
matrix.** -/
theorem covarianceOperator_multivariateGaussian_apply {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (x : EuclideanSpace ℝ ι) :
    covarianceOperator (multivariateGaussian (0 : EuclideanSpace ℝ ι) S) x
      = WithLp.toLp 2 (S *ᵥ WithLp.ofLp x) := by
  refine ext_inner_right (𝕜 := ℝ) fun v => ?_
  rw [inner_covarianceOperator_multivariateGaussian hS x v,
    EuclideanSpace.real_inner_eq_dotProduct, WithLp.ofLp_toLp, Matrix.dotProduct_mulVec]
  congr 1
  have h := Matrix.vecMul_transpose S (WithLp.ofLp x)
  rwa [Matrix.PosSemidef.transpose_eq hS] at h

end ProbabilityTheory
