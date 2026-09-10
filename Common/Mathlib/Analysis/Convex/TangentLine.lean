/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Convex.Deriv

/-!
# The supporting-line inequality for differentiable convex functions

A convex function that is differentiable at `q` lies above its tangent line at `q`:

`f q + f'(q) (x - q) ≤ f x`   (`ConvexOn.add_deriv_mul_sub_le`)

and symmetrically a concave function lies below its tangent lines
(`ConcaveOn.le_add_deriv_mul_sub`). Mathlib has the two halves of this as bounds on the secant
slopes (`ConvexOn.deriv_le_slope`, `ConvexOn.slope_le_deriv`); this is the standard form in which
convexity is used, the one-dimensional case of the gradient inequality.
-/

open Set

variable {S : Set ℝ} {f : ℝ → ℝ}

/-- **The supporting-line (gradient) inequality**: a convex function differentiable on `S` lies
above its tangent line at any `q ∈ S`. -/
theorem ConvexOn.add_deriv_mul_sub_le (hfc : ConvexOn ℝ S f)
    (hfd : ∀ y ∈ S, DifferentiableAt ℝ f y) {q x : ℝ} (hq : q ∈ S) (hx : x ∈ S) :
    f q + deriv f q * (x - q) ≤ f x := by
  rcases lt_trichotomy q x with hqx | rfl | hxq
  · have hs := hfc.deriv_le_slope hq hx hqx (hfd q hq)
    have hmul := mul_le_mul_of_nonneg_right hs (sub_pos.2 hqx).le
    have hsl : slope f q x * (x - q) = f x - f q := by
      rw [mul_comm, ← smul_eq_mul]
      exact sub_smul_slope f q x
    rw [hsl] at hmul
    linarith
  · simp
  · have hs := hfc.slope_le_deriv hx hq hxq (hfd q hq)
    have hmul := mul_le_mul_of_nonneg_right hs (sub_pos.2 hxq).le
    have hsl : slope f x q * (q - x) = f q - f x := by
      rw [mul_comm, ← smul_eq_mul]
      exact sub_smul_slope f x q
    rw [hsl] at hmul
    have he : deriv f q * (q - x) = -(deriv f q * (x - q)) := by ring
    rw [he] at hmul
    linarith

/-- The supporting-line inequality for a convex function differentiable everywhere. -/
theorem ConvexOn.add_deriv_mul_sub_le_univ (hfc : ConvexOn ℝ univ f) (hfd : Differentiable ℝ f)
    (q x : ℝ) : f q + deriv f q * (x - q) ≤ f x :=
  hfc.add_deriv_mul_sub_le (fun y _ => hfd y) (mem_univ q) (mem_univ x)

/-- **The supporting-line inequality for concave functions**: a concave function differentiable
on `S` lies below its tangent line at any `q ∈ S`. -/
theorem ConcaveOn.le_add_deriv_mul_sub (hfc : ConcaveOn ℝ S f)
    (hfd : ∀ y ∈ S, DifferentiableAt ℝ f y) {q x : ℝ} (hq : q ∈ S) (hx : x ∈ S) :
    f x ≤ f q + deriv f q * (x - q) := by
  have hneg : ConvexOn ℝ S (-f) := hfc.neg
  have hnd : ∀ y ∈ S, DifferentiableAt ℝ (-f) y := fun y hy => (hfd y hy).neg
  have h := hneg.add_deriv_mul_sub_le hnd hq hx
  rw [Pi.neg_apply, Pi.neg_apply, deriv.neg] at h
  linarith
