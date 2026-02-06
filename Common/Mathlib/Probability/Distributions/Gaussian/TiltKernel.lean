/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Order.Ring.Abs

/-!
# 1D Gaussian tilt kernel: bounds and derivatives

This file isolates the purely one-dimensional analytic lemmas about the exponential tilt kernel

`tiltKernel v t x = exp (t * x - v * t^2 / 2)`,

used to justify dominated differentiation in the Cameron–Martin IBP analytic layer.

## Main definitions

- `MeasureTheory.tiltKernel`: the 1D exponential tilt kernel.

## Main results

- `MeasureTheory.hasDerivAt_tiltKernel`: derivative in the tilt parameter.
- `MeasureTheory.gaussianTilt_deriv_dom_bound`: a uniform domination bound for the derivative
  integrand (for bounded `|t|`).

## Implementation notes

This file deliberately contains no integration-by-parts statements and no bespoke “test function”
structures; those live in the intrinsic Cameron–Martin IBP development.
-/

open MeasureTheory Real
open scoped NNReal

namespace MeasureTheory

/-! ### The tilt kernel -/

/-- The (centered) 1D Gaussian exponential tilt kernel (no prefactor `F x`). -/
@[simp] noncomputable def tiltKernel (v : ℝ≥0) (t x : ℝ) : ℝ :=
  Real.exp (t * x - (v : ℝ) * t ^ 2 / 2)

lemma tiltKernel_nonneg (v : ℝ≥0) (t x : ℝ) : 0 ≤ tiltKernel v t x := by
  have : 0 < Real.exp (t * x - (v : ℝ) * t ^ 2 / 2) := Real.exp_pos _
  simpa [tiltKernel] using this.le

/-! ### Derivatives in the tilt parameter -/

private lemma hasDerivAt_tiltExponent (v : ℝ≥0) (x t : ℝ) :
    HasDerivAt (fun s : ℝ => s * x - (v : ℝ) * s ^ 2 / 2) (x - (v : ℝ) * t) t := by
  have h1 : HasDerivAt (fun s : ℝ => s * x) x t := by
    simpa [mul_comm] using (hasDerivAt_id t).const_mul x
  have h2 : HasDerivAt (fun s : ℝ => (v : ℝ) * s ^ 2 / 2) ((v : ℝ) * t) t := by
    have : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      simpa [pow_two, two_mul, add_comm, add_left_comm, add_assoc] using
        (hasDerivAt_id t).mul (hasDerivAt_id t)
    have := this.const_mul ((v : ℝ) / 2)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  simpa [sub_eq_add_neg, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, pow_two] using
    h1.sub h2

lemma hasDerivAt_tiltKernel (v : ℝ≥0) (x t : ℝ) :
    HasDerivAt (fun s => tiltKernel v s x) ((x - (v : ℝ) * t) * tiltKernel v t x) t := by
  have hExp := hasDerivAt_tiltExponent (v := v) (x := x) t
  simpa [tiltKernel, mul_assoc, mul_left_comm, mul_comm] using (Real.hasDerivAt_exp _).comp t hExp

lemma hasDerivAt_F_mul_tiltKernel (v : ℝ≥0) (F : ℝ → ℝ) (x t : ℝ) :
    HasDerivAt (fun s => F x * tiltKernel v s x)
      (F x * (x - (v : ℝ) * t) * tiltKernel v t x) t := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using (hasDerivAt_tiltKernel (v := v) x t).const_mul
    (F x)

/-! ### Simple exponential bound -/

lemma tiltKernel_le_exp_abs (v : ℝ≥0) (t x : ℝ) :
    tiltKernel v t x ≤ Real.exp (|t| * |x|) := by
  have hdrop : t * x - (v : ℝ) * t ^ 2 / 2 ≤ t * x := by
    have : 0 ≤ (v : ℝ) * t ^ 2 / 2 := by positivity
    linarith
  have habs : t * x ≤ |t| * |x| := by
    simpa [abs_mul] using (le_abs_self (t * x))
  have : t * x - (v : ℝ) * t ^ 2 / 2 ≤ |t| * |x| := le_trans hdrop habs
  simpa [tiltKernel] using (Real.exp_le_exp.mpr this)

/-! ### Domination bound for the derivative integrand -/

private lemma abs_sub_mul_le_abs_add_abs_mul
    (v : ℝ≥0) {δ : ℝ} {t : ℝ} (ht : |t| ≤ δ) (x : ℝ) :
    |x - (v : ℝ) * t| ≤ |x| + |(v : ℝ)| * δ := by
  have h1 : |x - (v : ℝ) * t| ≤ |x| + |(v : ℝ)| * |t| := by
    have := abs_add_le x (-(v : ℝ) * t)
    simpa [sub_eq_add_neg, abs_mul, abs_neg, mul_assoc, mul_left_comm, mul_comm] using this
  have hvabs : 0 ≤ |(v : ℝ)| := abs_nonneg _
  have hvt : |(v : ℝ)| * |t| ≤ |(v : ℝ)| * δ := mul_le_mul_of_nonneg_left ht hvabs
  exact le_trans h1 (by linarith)

private lemma tiltKernel_le_exp_abs_mul
    (v : ℝ≥0) {δ t x : ℝ} (ht : |t| ≤ δ) :
    tiltKernel v t x ≤ Real.exp (δ * |x|) := by
  have h0 : tiltKernel v t x ≤ Real.exp (|t| * |x|) := tiltKernel_le_exp_abs v t x
  have hmul : |t| * |x| ≤ δ * |x| := mul_le_mul_of_nonneg_right ht (abs_nonneg _)
  exact le_trans h0 (by simpa [mul_comm] using (Real.exp_le_exp.mpr (by simpa [mul_comm] using hmul)))

private lemma abs_add_abs_mul_le_mul_one_add
    (v : ℝ≥0) (δ : ℝ) (hδ_pos : 0 < δ) (x : ℝ) :
    (|x| + |(v : ℝ)| * δ) ≤ ((|(v : ℝ)| * δ) + 1) * (|x| + 1) := by
  have hx : 0 ≤ |x| := abs_nonneg _
  have hvδ : 0 ≤ |(v : ℝ)| * δ := mul_nonneg (abs_nonneg _) (le_of_lt hδ_pos)
  nlinarith

lemma gaussianTilt_deriv_dom_bound
    {v : ℝ≥0} (δ : ℝ) (hδ_pos : 0 < δ)
    {F : ℝ → ℝ} (t : ℝ) (ht : |t| ≤ δ) (x : ℝ) :
    |F x * (x - (v : ℝ) * t) * tiltKernel v t x|
      ≤ |F x| * ((|(v : ℝ)| * δ) + 1) * (|x| + 1) * Real.exp (δ * |x|) := by
  have hlin : |x - (v : ℝ) * t| ≤ |x| + |(v : ℝ)| * δ :=
    abs_sub_mul_le_abs_add_abs_mul (v := v) (δ := δ) ht x
  have hker : tiltKernel v t x ≤ Real.exp (δ * |x|) :=
    tiltKernel_le_exp_abs_mul (v := v) (δ := δ) (t := t) (x := x) ht
  have habsorb : (|x| + |(v : ℝ)| * δ) ≤ ((|(v : ℝ)| * δ) + 1) * (|x| + 1) :=
    abs_add_abs_mul_le_mul_one_add (v := v) δ hδ_pos x
  have hF0 : 0 ≤ |F x| := abs_nonneg _
  have hK0 : 0 ≤ tiltKernel v t x := tiltKernel_nonneg v t x
  calc
    |F x * (x - (v : ℝ) * t) * tiltKernel v t x|
        = |F x| * |x - (v : ℝ) * t| * tiltKernel v t x := by
            simp [abs_mul, mul_assoc, mul_comm]
    _ ≤ |F x| * (|x| + |(v : ℝ)| * δ) * tiltKernel v t x := by
          have : |F x| * |x - (v : ℝ) * t| ≤ |F x| * (|x| + |(v : ℝ)| * δ) :=
            mul_le_mul_of_nonneg_left hlin hF0
          exact mul_le_mul_of_nonneg_right this hK0
    _ ≤ |F x| * (|x| + |(v : ℝ)| * δ) * Real.exp (δ * |x|) := by
          have hfac : 0 ≤ |F x| * (|x| + |(v : ℝ)| * δ) := by positivity
          have := mul_le_mul_of_nonneg_left hker hfac
          simpa [mul_assoc, mul_left_comm, mul_comm] using this
    _ ≤ |F x| * (((|(v : ℝ)| * δ) + 1) * (|x| + 1)) * Real.exp (δ * |x|) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habsorb hF0) (by positivity)
    _ = |F x| * ((|(v : ℝ)| * δ) + 1) * (|x| + 1) * Real.exp (δ * |x|) := by ring

end MeasureTheory
