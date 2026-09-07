/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Distribution.TemperateGrowth

/-!
# Derivatives of functions of temperate growth

`Function.HasTemperateGrowth` is Mathlib's class of smooth functions all of whose iterated
derivatives are polynomially bounded. Mathlib provides `HasTemperateGrowth.of_fderiv` (build
temperate growth from that of the derivative) but not the converse, which is what one needs in
order to *iterate*: to feed a derivative into a statement that itself demands temperate growth.

This file supplies the converse and the two consequences that make the class usable as the
hypothesis of a second-order integration-by-parts formula:

* `Function.HasTemperateGrowth.fderiv`: `f` of temperate growth ⟹ `fderiv ℝ f` of temperate
  growth.
* `Function.HasTemperateGrowth.exists_bound_fderiv_two`: a *single* constant and degree bounding
  `f`, `fderiv ℝ f` and `fderiv ℝ (fderiv ℝ f)` simultaneously.
* `Function.hasTemperateGrowth_affine`: affine maps have temperate growth.
* `Function.HasTemperateGrowth.comp_affine`: temperate growth is stable under an affine change of
  variable `x ↦ a • x + c`.
-/

open scoped ContDiff

namespace Function

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The derivative of a function of temperate growth has temperate growth.** This is the
converse of `Function.HasTemperateGrowth.of_fderiv`, and is what allows the class to be iterated. -/
@[fun_prop]
theorem HasTemperateGrowth.fderiv {f : E → F} (hf : HasTemperateGrowth f) :
    HasTemperateGrowth (_root_.fderiv ℝ f) := by
  refine ⟨hf.1.fderiv_right (by simp), fun n => ?_⟩
  obtain ⟨k, C, hbound⟩ := hf.2 (n + 1)
  refine ⟨k, C, fun x => ?_⟩
  rw [norm_iteratedFDeriv_fderiv]
  exact hbound x

/-- A single polynomial bound for `f`, `Df` and `D²f`. This is the form in which temperate growth
feeds a second-order integration-by-parts formula. -/
theorem HasTemperateGrowth.exists_bound_fderiv_two {f : E → F} (hf : HasTemperateGrowth f) :
    ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ (∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ m)
      ∧ (∀ x, ‖_root_.fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ m)
      ∧ (∀ x, ‖_root_.fderiv ℝ (_root_.fderiv ℝ f) x‖ ≤ C * (1 + ‖x‖) ^ m) := by
  obtain ⟨k, C, hC, hbound⟩ := hf.norm_iteratedFDeriv_le_uniform 2
  refine ⟨C, k, hC, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · simpa [norm_iteratedFDeriv_zero] using hbound 0 (by norm_num) x
  · simpa [norm_iteratedFDeriv_one] using hbound 1 (by norm_num) x
  · have h2 := hbound 2 (by norm_num) x
    rwa [show (2 : ℕ) = 1 + 1 from rfl, ← norm_iteratedFDeriv_fderiv,
      norm_iteratedFDeriv_one] at h2

/-- An affine map has temperate growth. -/
@[fun_prop]
theorem hasTemperateGrowth_affine (a : ℝ) (c : E) :
    HasTemperateGrowth (fun x : E => a • x + c) := by
  have hlin : HasTemperateGrowth (fun x : E => a • x) :=
    (a • ContinuousLinearMap.id ℝ E).hasTemperateGrowth
  exact hlin.add (HasTemperateGrowth.const c)

/-- Temperate growth is stable under an affine change of variable. -/
theorem HasTemperateGrowth.comp_affine {f : E → F} (hf : HasTemperateGrowth f) (a : ℝ) (c : E) :
    HasTemperateGrowth (fun x : E => f (a • x + c)) := by
  simpa [Function.comp_def] using hf.comp (hasTemperateGrowth_affine a c)

end Function
