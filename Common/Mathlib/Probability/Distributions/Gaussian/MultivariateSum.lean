/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.Distributions.Gaussian.MultivariateScaling
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Sums of independent multivariate Gaussians

Mathlib knows that characteristic functions multiply under convolution
(`ProbabilityTheory.charFun_map_add_prod_eq_mul`) and evaluates the characteristic function of a
`multivariateGaussian` (`ProbabilityTheory.charFun_multivariateGaussian`), but does not record the
consequence: **the sum of two independent centered multivariate Gaussians is the centered
multivariate Gaussian whose covariance is the sum**.

Together with `ProbabilityTheory.multivariateGaussian_map_smul` this identifies the law of the
interpolating field `x + t y`, which is the standard device for isolating one summand of a
Hamiltonian built from independent pieces: the covariance is `S + t² T`, so differentiating in `t`
differentiates in the coupling of the second piece alone.

## Main statements

- `ProbabilityTheory.multivariateGaussian_map_add_prod`:
  `(mvG 0 S ×ₘ mvG 0 T).map (· + ·) = mvG 0 (S + T)`.
- `ProbabilityTheory.multivariateGaussian_map_add_smul_prod`:
  `(mvG 0 S ×ₘ mvG 0 T).map (fun p ↦ p.1 + t • p.2) = mvG 0 (S + t² • T)`.
-/

open MeasureTheory Complex
open scoped InnerProductSpace Matrix

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The sum of two independent centered multivariate Gaussians is a centered multivariate
Gaussian, with the sum of the covariances.** -/
theorem multivariateGaussian_map_add_prod {S T : Matrix ι ι ℝ}
    (hS : S.PosSemidef) (hT : T.PosSemidef) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ ι) S).prod
        (multivariateGaussian (0 : EuclideanSpace ℝ ι) T)).map (fun p => p.1 + p.2)
      = multivariateGaussian (0 : EuclideanSpace ℝ ι) (S + T) := by
  have hST : (S + T).PosSemidef := hS.add hT
  have hmeas : Measurable fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => p.1 + p.2 := by
    fun_prop
  have : IsProbabilityMeasure
      (((multivariateGaussian (0 : EuclideanSpace ℝ ι) S).prod
        (multivariateGaussian (0 : EuclideanSpace ℝ ι) T)).map
          (fun p => p.1 + p.2)) :=
    MeasureTheory.Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine Measure.ext_of_charFun (E := EuclideanSpace ℝ ι) ?_
  rw [charFun_map_add_prod_eq_mul]
  funext t
  rw [Pi.mul_apply, charFun_multivariateGaussian hS, charFun_multivariateGaussian hT,
    charFun_multivariateGaussian hST, ← Complex.exp_add]
  congr 1
  have hadd : ((S + T) *ᵥ (WithLp.ofLp t)) = S *ᵥ (WithLp.ofLp t) + T *ᵥ (WithLp.ofLp t) :=
    Matrix.add_mulVec _ _ _
  simp only [inner_zero_right, hadd, dotProduct_add]
  push_cast
  ring

/-- **The law of the interpolating field.** For independent centered Gaussians with covariances
`S` and `T`, the field `x + t y` is centered Gaussian with covariance `S + t² T`. -/
theorem multivariateGaussian_map_add_smul_prod {S T : Matrix ι ι ℝ}
    (hS : S.PosSemidef) (hT : T.PosSemidef) (t : ℝ) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ ι) S).prod
        (multivariateGaussian (0 : EuclideanSpace ℝ ι) T)).map (fun p => p.1 + t • p.2)
      = multivariateGaussian (0 : EuclideanSpace ℝ ι) (S + (t ^ 2) • T) := by
  have hT' : ((t ^ 2) • T).PosSemidef := hT.smul_sq t
  have hsmul : Measurable fun y : EuclideanSpace ℝ ι => t • y := by fun_prop
  have hadd : Measurable fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => p.1 + p.2 := by
    fun_prop
  have hpm : Measurable
      fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => (p.1, t • p.2) := by fun_prop
  have hstep : ((multivariateGaussian (0 : EuclideanSpace ℝ ι) S).prod
        (multivariateGaussian (0 : EuclideanSpace ℝ ι) T)).map
          (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => (p.1, t • p.2))
      = (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).prod
          (multivariateGaussian (0 : EuclideanSpace ℝ ι) ((t ^ 2) • T)) := by
    have h := MeasureTheory.Measure.map_prod_map
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) S)
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) T)
      (measurable_id (α := EuclideanSpace ℝ ι)) hsmul
    have hy : (multivariateGaussian (0 : EuclideanSpace ℝ ι) T).map
          (fun y : EuclideanSpace ℝ ι => t • y)
        = multivariateGaussian (0 : EuclideanSpace ℝ ι) ((t ^ 2) • T) := by
      rw [multivariateGaussian_map_smul (0 : EuclideanSpace ℝ ι) hT t, smul_zero]
    rw [show (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => (p.1, t • p.2))
        = Prod.map (id : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
            (fun y : EuclideanSpace ℝ ι => t • y) from rfl,
      ← h, Measure.map_id, hy]
  calc ((multivariateGaussian (0 : EuclideanSpace ℝ ι) S).prod
        (multivariateGaussian (0 : EuclideanSpace ℝ ι) T)).map (fun p => p.1 + t • p.2)
      = (((multivariateGaussian (0 : EuclideanSpace ℝ ι) S).prod
            (multivariateGaussian (0 : EuclideanSpace ℝ ι) T)).map
              (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => (p.1, t • p.2))).map
          (fun p => p.1 + p.2) := by
        rw [Measure.map_map hadd hpm]
        rfl
    _ = ((multivariateGaussian (0 : EuclideanSpace ℝ ι) S).prod
          (multivariateGaussian (0 : EuclideanSpace ℝ ι) ((t ^ 2) • T))).map
            (fun p => p.1 + p.2) := by rw [hstep]
    _ = multivariateGaussian (0 : EuclideanSpace ℝ ι) (S + (t ^ 2) • T) :=
        multivariateGaussian_map_add_prod hS hT'

end ProbabilityTheory
