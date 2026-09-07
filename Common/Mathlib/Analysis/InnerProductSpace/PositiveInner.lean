/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import Common.Mathlib.Analysis.MeanInequalities.WeightedAMGM

/-!
# Cauchy–Schwarz for a positive operator

A positive operator `T` on a real inner product space defines a positive semidefinite symmetric
bilinear form `(x, y) ↦ ⟪T x, y⟫`, and therefore satisfies the Cauchy–Schwarz inequality

`⟪T x, y⟫² ≤ ⟪T x, x⟫ * ⟪T y, y⟫`

in its equivalent forms `|⟪T x, y⟫| ≤ √⟪T x, x⟫ √⟪T y, y⟫` and, for every weight `λ > 0`,
`|⟪T x, y⟫| ≤ (λ ⟪T x, x⟫ + ⟪T y, y⟫ / λ) / 2`. These are degenerate forms of Cauchy–Schwarz — the
form need not be definite, so it is not an inner product and Mathlib's
`inner_mul_le_norm_mul_norm` does not apply. The proof is the classical discriminant argument on
`t ↦ ⟪T (x + t • y), x + t • y⟫ ≥ 0`.

The weighted form is the one an integral argument wants: it survives being integrated in `x` and
`y` separately, and the weight can be optimised at the very end
(`Real.le_sqrt_mul_sqrt_of_forall_pos`), which recovers the Cauchy–Schwarz constant without ever
needing Cauchy–Schwarz for the integral.

## Main statements

- `LinearMap.IsPositive.sq_inner_le`: Cauchy–Schwarz.
- `LinearMap.IsPositive.abs_inner_le_sqrt_mul_sqrt`: its square-root form.
- `LinearMap.IsPositive.abs_inner_le_half_add_smul`: the weighted arithmetic–geometric form.
- `LinearMap.IsPositive.abs_inner_le_half_add`: its unweighted case.
-/

open scoped RealInnerProductSpace

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic expansion behind Cauchy–Schwarz: for a positive operator `T`,
`⟪T (x + t • y), x + t • y⟫ = ⟪T y, y⟫ t² + 2⟪T x, y⟫ t + ⟪T x, x⟫`. -/
theorem IsPositive.inner_add_smul {T : E →ₗ[ℝ] E} (hT : T.IsPositive) (x y : E) (t : ℝ) :
    ⟪T (x + t • y), x + t • y⟫
      = ⟪T y, y⟫ * (t * t) + 2 * ⟪T x, y⟫ * t + ⟪T x, x⟫ := by
  have hsymm : ⟪T y, x⟫ = ⟪T x, y⟫ := by
    rw [hT.isSymmetric y x, real_inner_comm]
  simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, hsymm]
  ring

/-- **Cauchy–Schwarz for a positive operator**: `⟪T x, y⟫² ≤ ⟪T x, x⟫ * ⟪T y, y⟫`. -/
theorem IsPositive.sq_inner_le {T : E →ₗ[ℝ] E} (hT : T.IsPositive) (x y : E) :
    ⟪T x, y⟫ ^ 2 ≤ ⟪T x, x⟫ * ⟪T y, y⟫ := by
  have hquad : ∀ t : ℝ, 0 ≤ ⟪T y, y⟫ * (t * t) + 2 * ⟪T x, y⟫ * t + ⟪T x, x⟫ := by
    intro t
    rw [← hT.inner_add_smul x y t]
    exact hT.inner_nonneg_left _
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  nlinarith [hdisc]

/-- **Cauchy–Schwarz for a positive operator**, square-root form:
`|⟪T x, y⟫| ≤ √⟪T x, x⟫ * √⟪T y, y⟫`. -/
theorem IsPositive.abs_inner_le_sqrt_mul_sqrt {T : E →ₗ[ℝ] E} (hT : T.IsPositive) (x y : E) :
    |⟪T x, y⟫| ≤ Real.sqrt ⟪T x, x⟫ * Real.sqrt ⟪T y, y⟫ := by
  have hA : 0 ≤ ⟪T x, x⟫ := hT.inner_nonneg_left x
  have hB : 0 ≤ ⟪T y, y⟫ := hT.inner_nonneg_left y
  calc |⟪T x, y⟫| = Real.sqrt (⟪T x, y⟫ ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (⟪T x, x⟫ * ⟪T y, y⟫) := Real.sqrt_le_sqrt (hT.sq_inner_le x y)
    _ = Real.sqrt ⟪T x, x⟫ * Real.sqrt ⟪T y, y⟫ := Real.sqrt_mul hA _

/-- The **weighted** arithmetic–geometric form of Cauchy–Schwarz for a positive operator: for every
`λ > 0`, `|⟪T x, y⟫| ≤ (λ ⟪T x, x⟫ + ⟪T y, y⟫ / λ) / 2`. -/
theorem IsPositive.abs_inner_le_half_add_smul {T : E →ₗ[ℝ] E} (hT : T.IsPositive) (x y : E)
    {lam : ℝ} (hlam : 0 < lam) :
    |⟪T x, y⟫| ≤ (lam * ⟪T x, x⟫ + ⟪T y, y⟫ / lam) / 2 := by
  have hA : 0 ≤ ⟪T x, x⟫ := hT.inner_nonneg_left x
  have hB : 0 ≤ ⟪T y, y⟫ := hT.inner_nonneg_left y
  have := Real.two_mul_sqrt_mul_sqrt_le hA hB hlam
  have := hT.abs_inner_le_sqrt_mul_sqrt x y
  linarith

/-- The arithmetic–geometric form of Cauchy–Schwarz for a positive operator:
`|⟪T x, y⟫| ≤ (⟪T x, x⟫ + ⟪T y, y⟫) / 2`. The weight-`1` case of
`LinearMap.IsPositive.abs_inner_le_half_add_smul`. -/
theorem IsPositive.abs_inner_le_half_add {T : E →ₗ[ℝ] E} (hT : T.IsPositive) (x y : E) :
    |⟪T x, y⟫| ≤ (⟪T x, x⟫ + ⟪T y, y⟫) / 2 := by
  simpa using hT.abs_inner_le_half_add_smul x y (lam := 1) one_pos

end LinearMap
