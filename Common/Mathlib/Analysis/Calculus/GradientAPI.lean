/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Norm and continuity of the gradient

`gradient f x` is the Riesz representative of `fderiv 𝕜 f x`, and `InnerProductSpace.toDual` is a
(conjugate-)linear isometry, so the two have the same norm and the same regularity. Mathlib's
gradient API records the defining identities but neither of these two facts, which are what one
needs to transfer a bound on `‖fderiv 𝕜 f x‖`, or the continuity of `fderiv 𝕜 f`, to the gradient.

## Main statements

- `norm_gradient`: `‖∇ f x‖ = ‖fderiv 𝕜 f x‖`.
- `ContDiff.continuous_gradient`: the gradient of a `C¹` function is continuous.
-/

open scoped Gradient

variable {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The gradient and the Fréchet derivative have the same norm: `toDual` is an isometry. -/
@[simp] theorem norm_gradient (f : F → 𝕜) (x : F) : ‖∇ f x‖ = ‖fderiv 𝕜 f x‖ := by
  rw [gradient]
  exact (InnerProductSpace.toDual 𝕜 F).symm.norm_map _

/-- The gradient of a `C¹` function is continuous. -/
theorem ContDiff.continuous_gradient {f : F → 𝕜} (hf : ContDiff 𝕜 1 f) :
    Continuous (∇ f) := by
  have hfd : Continuous (fderiv 𝕜 f) := hf.continuous_fderiv one_ne_zero
  unfold gradient
  simpa [Function.comp_def] using ((InnerProductSpace.toDual 𝕜 F).symm.continuous).comp hfd
