/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Scaling a multivariate Gaussian

A centred Gaussian vector scaled by `c` is again Gaussian, with covariance scaled by `c²`. Mathlib
records how `multivariateGaussian` behaves under linear isometries and under restriction to a
sub-family of coordinates, but not under the simplest transformation of all, a dilation. This is
what turns a one-parameter family of Gaussian Hamiltonians whose covariance is `β²` times a fixed
kernel — every mean-field spin glass at inverse temperature `β` — into a *single* Gaussian field
scaled by `β`, and hence what makes the free energy a convex function of `β`.

## Main statements

- `Matrix.PosSemidef.smul_sq`: `c² • A` is positive semidefinite when `A` is.
- `ProbabilityTheory.multivariateGaussian_map_smul`:
  `(multivariateGaussian m S).map (c • ·) = multivariateGaussian (c • m) (c² • S)`.
-/

open MeasureTheory Complex
open scoped RealInnerProductSpace Matrix

namespace Matrix

/-- A nonnegative square multiple of a positive semidefinite matrix is positive semidefinite. -/
theorem PosSemidef.smul_sq {n : Type*} [Finite n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) (c : ℝ) : ((c ^ 2) • A).PosSemidef := by
  classical
  have := Fintype.ofFinite n
  have h := hA.mul_mul_conjTranspose_same (c • (1 : Matrix n n ℝ))
  have heq : (c • (1 : Matrix n n ℝ)) * A * (c • (1 : Matrix n n ℝ))ᴴ = (c ^ 2) • A := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul]
    simp [sq]
  rwa [heq] at h

end Matrix

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A multivariate Gaussian scales**: dilating by `c` scales the mean by `c` and the covariance
matrix by `c²`. -/
theorem multivariateGaussian_map_smul (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    (hS : S.PosSemidef) (c : ℝ) :
    (multivariateGaussian m S).map (fun x => c • x)
      = multivariateGaussian (c • m) ((c ^ 2) • S) := by
  have hS' : ((c ^ 2) • S).PosSemidef := hS.smul_sq c
  refine Measure.ext_of_charFun (E := EuclideanSpace ℝ ι) ?_
  funext t
  rw [show (fun x : EuclideanSpace ℝ ι => c • x) = (c • ·) from rfl, charFun_map_smul,
    charFun_multivariateGaussian hS, charFun_multivariateGaussian hS']
  congr 1
  have h1 : (⟪c • t, m⟫ : ℝ) = ⟪t, c • m⟫ := by
    rw [real_inner_smul_left, real_inner_smul_right]
  have h2 : ((c • t : EuclideanSpace ℝ ι)).ofLp ⬝ᵥ S *ᵥ ((c • t : EuclideanSpace ℝ ι)).ofLp
      = t.ofLp ⬝ᵥ ((c ^ 2) • S) *ᵥ t.ofLp := by
    have hofLp : ((c • t : EuclideanSpace ℝ ι)).ofLp = c • (t.ofLp) := rfl
    rw [hofLp]
    simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, Matrix.smul_mulVec,
      smul_eq_mul]
    ring
  rw [h1, h2]

end ProbabilityTheory
