/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.Distributions.Gaussian.MultivariateCovariance
import Common.Mathlib.Topology.Algebra.Module.BilinearBasis
import Mathlib.LinearAlgebra.SesquilinearForm.Star
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Every Gaussian measure on a Euclidean space is a multivariate Gaussian

Mathlib constructs `multivariateGaussian m S` for a positive semidefinite matrix `S` and proves
`IsGaussian.ext`: two Gaussian measures with the same mean and the same covariance bilinear form
are equal. It does not record the consequence that matters for finite-dimensional modelling:
**a Gaussian measure on `EuclideanSpace ℝ ι` is the multivariate Gaussian of its mean and of its
covariance matrix**, so that a Gaussian law is identified as soon as its covariance kernel in the
standard basis is.

The covariance matrix is Mathlib's `LinearMap.toMatrix₂` of the covariance bilinear form in the
standard orthonormal basis; its positive semidefiniteness is
`LinearMap.isPosSemidef_iff_posSemidef_toMatrix` applied to `isPosSemidef_covarianceBilin`.

## Main statements

- `ProbabilityTheory.covMatrix`: the covariance matrix of a measure on `EuclideanSpace ℝ ι`, as
  `LinearMap.toMatrix₂` of `covarianceBilin` in the standard basis.
- `ProbabilityTheory.posSemidef_covMatrix`: it is positive semidefinite.
- `ProbabilityTheory.IsGaussian.eq_multivariateGaussian`: **`μ = multivariateGaussian μ[id]
  (covMatrix μ)`** for every Gaussian `μ` — no hypotheses.
- `ProbabilityTheory.IsGaussian.eq_multivariateGaussian_of_covarianceBilin`,
  `..._of_inner_covarianceOperator`: the identification from a covariance kernel given on the
  standard basis, in the two forms in which such kernels arise.
-/

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace Matrix

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The covariance matrix** of a measure on `EuclideanSpace ℝ ι`: the matrix of its covariance
bilinear form in the standard basis, `covMatrix μ i j = Cov(xᵢ, xⱼ)`. -/
noncomputable def covMatrix (μ : Measure (EuclideanSpace ℝ ι)) : Matrix ι ι ℝ :=
  LinearMap.toMatrix₂ (EuclideanSpace.basisFun ι ℝ).toBasis (EuclideanSpace.basisFun ι ℝ).toBasis
    (covarianceBilin μ).toBilinForm

@[simp] lemma covMatrix_apply (μ : Measure (EuclideanSpace ℝ ι)) (i j : ι) :
    covMatrix μ i j
      = covarianceBilin μ (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  simp [covMatrix, LinearMap.toMatrix₂_apply, EuclideanSpace.basisFun_apply]

/-- The quadratic form of the covariance matrix is the covariance bilinear form: the standard-basis
expansion `apply_eq_dotProduct_toMatrix₂_mulVec` read on `EuclideanSpace`. -/
theorem dotProduct_covMatrix_mulVec (μ : Measure (EuclideanSpace ℝ ι)) (v w : ι → ℝ) :
    v ⬝ᵥ covMatrix μ *ᵥ w = covarianceBilin μ (WithLp.toLp 2 v) (WithLp.toLp 2 w) := by
  have key := apply_eq_dotProduct_toMatrix₂_mulVec
    (EuclideanSpace.basisFun ι ℝ).toBasis (EuclideanSpace.basisFun ι ℝ).toBasis
    (covarianceBilin μ).toBilinForm (WithLp.toLp 2 v) (WithLp.toLp 2 w)
  have hrepr : ∀ u : ι → ℝ,
      (RingHom.id ℝ) ∘ ⇑((EuclideanSpace.basisFun ι ℝ).toBasis.repr (WithLp.toLp 2 u)) = u := by
    intro u; ext i
    simp [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
  rw [ContinuousLinearMap.toBilinForm_apply, hrepr, hrepr] at key
  exact key.symm

/-- The covariance matrix is positive semidefinite. -/
theorem posSemidef_covMatrix (μ : Measure (EuclideanSpace ℝ ι)) : (covMatrix μ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v => ?_⟩
  · ext i j
    simp [covMatrix_apply, covarianceBilin_comm]
  · rw [star_trivial, dotProduct_covMatrix_mulVec]
    exact covarianceBilin_self_nonneg _

/-- The covariance matrix of a centered multivariate Gaussian is its matrix. -/
theorem covMatrix_multivariateGaussian {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (m : EuclideanSpace ℝ ι) : covMatrix (multivariateGaussian m S) = S := by
  ext i j
  simp [covMatrix_apply, covarianceBilin_multivariateGaussian hS]

/-- **Every Gaussian measure on a Euclidean space is the multivariate Gaussian of its mean and its
covariance matrix.** -/
theorem IsGaussian.eq_multivariateGaussian (μ : Measure (EuclideanSpace ℝ ι)) [IsGaussian μ] :
    μ = multivariateGaussian (∫ x, x ∂μ) (covMatrix μ) := by
  refine IsGaussian.ext ?_ ?_
  · simp
  · refine ContinuousLinearMap.ext_basis₂ (EuclideanSpace.basisFun ι ℝ).toBasis
      (EuclideanSpace.basisFun ι ℝ).toBasis fun i j => ?_
    rw [covarianceBilin_multivariateGaussian (posSemidef_covMatrix μ)]
    simp [EuclideanSpace.basisFun_apply]

/-- **A Gaussian measure is identified by its mean and its covariance kernel on the standard
basis**, the kernel given through `covarianceBilin`. -/
theorem IsGaussian.eq_multivariateGaussian_of_covarianceBilin (μ : Measure (EuclideanSpace ℝ ι))
    [IsGaussian μ] {m : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ} (hmean : (∫ x, x ∂μ) = m)
    (hcov : ∀ i j,
      covarianceBilin μ (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = S i j) :
    μ = multivariateGaussian m S := by
  have hS : covMatrix μ = S := by ext i j; rw [covMatrix_apply, hcov]
  rw [IsGaussian.eq_multivariateGaussian μ, hmean, hS]

/-- **A centered Gaussian measure is identified by its covariance kernel on the standard basis**,
the kernel given through the covariance operator (Mathlib's *uncentered* second-moment operator,
which is the covariance precisely because the mean vanishes). -/
theorem IsGaussian.eq_multivariateGaussian_of_inner_covarianceOperator
    (μ : Measure (EuclideanSpace ℝ ι)) [IsGaussian μ] {S : Matrix ι ι ℝ}
    (hmean0 : (∫ x, x ∂μ) = 0)
    (hcov : ∀ i j, ⟪covarianceOperator μ (EuclideanSpace.single i 1),
      EuclideanSpace.single j (1 : ℝ)⟫ = S i j) :
    μ = multivariateGaussian 0 S :=
  IsGaussian.eq_multivariateGaussian_of_covarianceBilin μ hmean0 fun i j => by
    rw [covarianceBilin_eq_inner_covarianceOperator IsGaussian.memLp_two_id hmean0, hcov]

end ProbabilityTheory
