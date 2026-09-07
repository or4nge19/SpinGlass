/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Linear growth and `Lᵖ` membership from a bounded derivative

A differentiable map whose Fréchet derivative is bounded in norm by `K` is `K`-Lipschitz
(`lipschitzWith_of_nnnorm_fderiv_le`), hence grows at most linearly. This file records the growth
form of that statement, and the measure-theoretic consequence it exists for: such a map lies in
every `Lᵖ` space in which the identity lies. For a Gaussian measure the identity lies in every
`Lᵖ` with `p ≠ ∞` (Fernique, `ProbabilityTheory.IsGaussian.memLp_id`), so every function with
bounded derivative is square-integrable there — the standing hypothesis of the Gaussian Poincaré
and covariance inequalities.

## Main statements

- `norm_le_add_mul_norm_of_norm_fderiv_le`: `‖f x‖ ≤ ‖f 0‖ + K * ‖x‖`.
- `MeasureTheory.MemLp.of_norm_fderiv_le`: `Lᵖ` membership.
-/

open MeasureTheory
open scoped ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A differentiable map whose derivative is bounded in norm by `K` grows at most linearly:
`‖f x‖ ≤ ‖f 0‖ + K * ‖x‖`. -/
theorem norm_le_add_mul_norm_of_norm_fderiv_le {f : E → F} (hf : Differentiable ℝ f) {K : ℝ}
    (hK : ∀ x, ‖fderiv ℝ f x‖ ≤ K) (x : E) : ‖f x‖ ≤ ‖f 0‖ + K * ‖x‖ := by
  have h : ‖f x - f 0‖ ≤ K * ‖x - 0‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le (f := f) (s := Set.univ) (C := K)
      (fun y _ => hf y) (fun y _ => hK y) convex_univ (Set.mem_univ 0) (Set.mem_univ x)
  have h' : ‖f x - f 0‖ ≤ K * ‖x‖ := by simpa using h
  calc ‖f x‖ = ‖f 0 + (f x - f 0)‖ := by rw [add_sub_cancel]
    _ ≤ ‖f 0‖ + ‖f x - f 0‖ := norm_add_le _ _
    _ ≤ ‖f 0‖ + K * ‖x‖ := by linarith

/-- A differentiable map with derivative bounded in norm lies in every `Lᵖ` space in which the
identity lies. -/
theorem MeasureTheory.MemLp.of_norm_fderiv_le [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology F] {μ : Measure E} [IsFiniteMeasure μ]
    {f : E → F} (hf : Differentiable ℝ f) {K : ℝ} (hK : ∀ x, ‖fderiv ℝ f x‖ ≤ K)
    {p : ℝ≥0∞} (hid : MemLp (id : E → E) p μ) : MemLp f p μ := by
  refine MemLp.mono' (g := fun x => ‖f 0‖ + K * ‖x‖) ?_ hf.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => norm_le_add_mul_norm_of_norm_fderiv_le hf hK x)
  have h1 : MemLp (fun _ : E => ‖f 0‖) p μ := memLp_const _
  have h2 : MemLp (fun x : E => K * ‖x‖) p μ := by
    simpa using _root_.MeasureTheory.MemLp.const_mul (_root_.MeasureTheory.MemLp.norm hid) K
  exact _root_.MeasureTheory.MemLp.add h1 h2
