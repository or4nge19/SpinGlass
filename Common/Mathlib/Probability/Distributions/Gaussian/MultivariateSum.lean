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

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The multivariate Gaussian with zero covariance is the Dirac mass at its mean. -/
@[simp] lemma multivariateGaussian_zero (m : EuclideanSpace ℝ ι) :
    multivariateGaussian m (0 : Matrix ι ι ℝ) = Measure.dirac m := by
  simp [multivariateGaussian, CFC.sqrt, Measure.map_const]

/-- **A linear combination of independent centered multivariate Gaussians is the centered
multivariate Gaussian with the corresponding combination of covariances**:
`∑ i, c i • xᵢ ∼ mvG 0 (∑ i, (c i)² • S i)` for independent `xᵢ ∼ mvG 0 (S i)`. -/
theorem multivariateGaussian_map_sum_smul_pi {n : ℕ} {S : Fin n → Matrix ι ι ℝ}
    (hS : ∀ i, (S i).PosSemidef) (c : Fin n → ℝ) :
    (Measure.pi fun i => multivariateGaussian (0 : EuclideanSpace ℝ ι) (S i)).map
        (fun x : Fin n → EuclideanSpace ℝ ι => ∑ i, c i • x i)
      = multivariateGaussian (0 : EuclideanSpace ℝ ι) (∑ i, (c i) ^ 2 • S i) := by
  induction n with
  | zero =>
    have hmeas : Measurable fun x : Fin 0 → EuclideanSpace ℝ ι => ∑ i, c i • x i :=
      Subsingleton.measurable
    rw [Measure.pi_of_empty, Measure.map_dirac' hmeas]
    simp
  | succ n ih =>
    set μ : Fin (n + 1) → Measure (EuclideanSpace ℝ ι) :=
      fun i => multivariateGaussian (0 : EuclideanSpace ℝ ι) (S i) with hμ
    have hpres := measurePreserving_piFinSuccAbove μ 0
    -- the sum splits as `c 0 • x 0 + ∑ j, c j.succ • x j.succ`
    have hsplit : (fun x : Fin (n + 1) → EuclideanSpace ℝ ι => ∑ i, c i • x i)
        = (fun p : EuclideanSpace ℝ ι × (Fin n → EuclideanSpace ℝ ι) =>
            c 0 • p.1 + ∑ j, c j.succ • p.2 j)
          ∘ (MeasurableEquiv.piFinSuccAbove (fun _ => EuclideanSpace ℝ ι) 0) := by
      funext x
      simp [MeasurableEquiv.piFinSuccAbove, Fin.sum_univ_succ, Fin.insertNthEquiv,
        Fin.zero_succAbove, Fin.tail]
    have hmeas_g : Measurable (fun p : EuclideanSpace ℝ ι × (Fin n → EuclideanSpace ℝ ι) =>
        c 0 • p.1 + ∑ j, c j.succ • p.2 j) := by fun_prop
    rw [hsplit, ← Measure.map_map hmeas_g (MeasurableEquiv.piFinSuccAbove _ 0).measurable,
      hpres.map_eq]
    -- the pair `(c 0 • y, ∑ j, c j.succ • z j)` has the product law of the two pieces
    have hpair : ((μ 0).prod (Measure.pi fun j => μ ((0 : Fin (n + 1)).succAbove j))).map
          (fun p : EuclideanSpace ℝ ι × (Fin n → EuclideanSpace ℝ ι) =>
            (c 0 • p.1, ∑ j, c j.succ • p.2 j))
        = (multivariateGaussian (0 : EuclideanSpace ℝ ι) ((c 0) ^ 2 • S 0)).prod
            (multivariateGaussian (0 : EuclideanSpace ℝ ι)
              (∑ j : Fin n, (c j.succ) ^ 2 • S j.succ)) := by
      have h := Measure.map_prod_map (μ 0) (Measure.pi fun j => μ ((0 : Fin (n + 1)).succAbove j))
        (by fun_prop : Measurable fun y : EuclideanSpace ℝ ι => c 0 • y)
        (by fun_prop : Measurable fun z : Fin n → EuclideanSpace ℝ ι => ∑ j, c j.succ • z j)
      rw [show (fun p : EuclideanSpace ℝ ι × (Fin n → EuclideanSpace ℝ ι) =>
          (c 0 • p.1, ∑ j, c j.succ • p.2 j))
          = Prod.map (fun y : EuclideanSpace ℝ ι => c 0 • y)
              (fun z : Fin n → EuclideanSpace ℝ ι => ∑ j, c j.succ • z j) from rfl, ← h]
      congr 1
      · rw [hμ]
        simpa [smul_zero] using multivariateGaussian_map_smul (0 : EuclideanSpace ℝ ι) (hS 0) (c 0)
      · simp only [hμ, Fin.zero_succAbove]
        exact ih (S := fun j => S j.succ) (fun j => hS j.succ) (fun j => c j.succ)
    have hadd : Measurable fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => p.1 + p.2 := by
      fun_prop
    have hpm : Measurable (fun p : EuclideanSpace ℝ ι × (Fin n → EuclideanSpace ℝ ι) =>
        (c 0 • p.1, ∑ j, c j.succ • p.2 j)) := by fun_prop
    have hsumPSD : (∑ j : Fin n, (c j.succ) ^ 2 • S j.succ).PosSemidef :=
      Finset.sum_induction _ Matrix.PosSemidef (fun _ _ ha hb => ha.add hb) Matrix.PosSemidef.zero
        (fun j _ => (hS j.succ).smul_sq (c j.succ))
    rw [show (fun p : EuclideanSpace ℝ ι × (Fin n → EuclideanSpace ℝ ι) =>
        c 0 • p.1 + ∑ j, c j.succ • p.2 j)
        = (fun q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => q.1 + q.2)
          ∘ (fun p : EuclideanSpace ℝ ι × (Fin n → EuclideanSpace ℝ ι) =>
            (c 0 • p.1, ∑ j, c j.succ • p.2 j)) from rfl,
      ← Measure.map_map hadd hpm, hpair,
      multivariateGaussian_map_add_prod ((hS 0).smul_sq (c 0)) hsumPSD, Fin.sum_univ_succ]

end ProbabilityTheory
