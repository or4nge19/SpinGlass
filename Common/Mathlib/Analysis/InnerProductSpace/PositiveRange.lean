/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Ranges of positive semidefinite operators in the Loewner order

Mathlib has `LinearMap.IsPositive`, the symmetric-plus-nonnegative-form notion of a positive
semidefinite operator, and `LinearMap.IsSymmetric.orthogonal_range : (range T)ᗮ = ker T`. What it
does not have is the comparison statement that makes the Loewner order usable:

`0 ≤ T ≤ S ⟹ range T ≤ range S`,

the finite-dimensional form of **Douglas' lemma**. It is the statement that lets a *component* of a
Gaussian vector be recovered as a linear function of the whole: if `S` is the covariance of `H` and
`T` the cross-covariance with a component, then `T ≤ S` and each column of `T` is `S` applied to
something — the conditional expectation of the component given `H`.

The route is elementary: for positive semidefinite `T`, the form `x ↦ ⟪T x, x⟫` is a positive
semidefinite quadratic form, so it vanishes at `x` exactly when `T x = 0`
(`LinearMap.IsPositive.apply_eq_zero_of_inner_self_eq_zero`); hence `T ≤ S` forces
`ker S ≤ ker T`, and orthogonal complements turn that into the range inclusion.

## Main statements

- `LinearMap.IsPositive.apply_eq_zero_of_inner_self_eq_zero`: `⟪T x, x⟫ = 0 → T x = 0`.
- `LinearMap.IsPositive.ker_le_ker_of_le`: `T ≤ S → ker S ≤ ker T`.
- `LinearMap.IsSymmetric.range_le_range_of_ker_le_ker`: `ker S ≤ ker T → range T ≤ range S`.
- `LinearMap.IsPositive.range_le_range_of_le`: **Douglas' lemma**, `0 ≤ T ≤ S → range T ≤ range S`.
- `ContinuousLinearMap.exists_apply_eq_of_isPositive_of_le`: the bundled-continuous form.
- `Matrix.PosSemidef.exists_mulVec_eq_of_sub_posSemidef`: the matrix form — every `T *ᵥ y` is an
  `S *ᵥ z`.
-/

open scoped InnerProductSpace

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **A positive semidefinite quadratic form vanishes only on the kernel.** If `T` is positive
semidefinite and `⟪T x, x⟫ = 0`, then `T x = 0`: Cauchy–Schwarz for the semidefinite form
`(x, y) ↦ ⟪T x, y⟫`. -/
theorem IsPositive.apply_eq_zero_of_inner_self_eq_zero
    {T : E →ₗ[ℝ] E} (hT : T.IsPositive) {x : E} (hx : ⟪T x, x⟫_ℝ = 0) : T x = 0 := by
  have hsym := hT.isSymmetric
  have hnn : ∀ y : E, 0 ≤ ⟪T y, y⟫_ℝ := fun y => hT.inner_nonneg_left y
  -- the quadratic expansion at `x + t • y`
  have hquad : ∀ (y : E) (t : ℝ), 0 ≤ 2 * t * ⟪T x, y⟫_ℝ + t ^ 2 * ⟪T y, y⟫_ℝ := by
    intro y t
    have h := hnn (x + t • y)
    have hexp : ⟪T (x + t • y), x + t • y⟫_ℝ
        = ⟪T x, x⟫_ℝ + 2 * t * ⟪T x, y⟫_ℝ + t ^ 2 * ⟪T y, y⟫_ℝ := by
      rw [map_add, map_smul, inner_add_left, inner_add_right, inner_add_right,
        real_inner_smul_left, real_inner_smul_left, real_inner_smul_right,
        real_inner_smul_right, hsym y x, real_inner_comm y (T x)]
      ring
    rw [hexp, hx] at h
    linarith
  -- hence the form pairs `T x` to zero against every vector
  have hzero : ∀ y : E, ⟪T x, y⟫_ℝ = 0 := by
    intro y
    have hb : 0 ≤ ⟪T y, y⟫_ℝ := hnn y
    rcases eq_or_lt_of_le hb with hb0 | hb0
    · have h1 := hquad y 1
      have h2 := hquad y (-1)
      rw [← hb0] at h1 h2
      linarith
    · have h := hquad y (-⟪T x, y⟫_ℝ / ⟪T y, y⟫_ℝ)
      have harith : 2 * (-⟪T x, y⟫_ℝ / ⟪T y, y⟫_ℝ) * ⟪T x, y⟫_ℝ
            + (-⟪T x, y⟫_ℝ / ⟪T y, y⟫_ℝ) ^ 2 * ⟪T y, y⟫_ℝ
          = -(⟪T x, y⟫_ℝ ^ 2) / ⟪T y, y⟫_ℝ := by
        field_simp
        ring
      rw [harith] at h
      have hsq : ⟪T x, y⟫_ℝ ^ 2 ≤ 0 := by
        by_contra hc
        rw [not_le] at hc
        have hneg : -(⟪T x, y⟫_ℝ ^ 2) / ⟪T y, y⟫_ℝ < 0 :=
          div_neg_of_neg_of_pos (by linarith) hb0
        linarith
      have : ⟪T x, y⟫_ℝ ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  exact inner_self_eq_zero.1 (hzero (T x))

/-- **In the Loewner order, a smaller positive semidefinite operator has a larger kernel.** -/
theorem IsPositive.ker_le_ker_of_le {S T : E →ₗ[ℝ] E} (hT : T.IsPositive)
    (hle : ∀ x : E, ⟪T x, x⟫_ℝ ≤ ⟪S x, x⟫_ℝ) :
    LinearMap.ker S ≤ LinearMap.ker T := by
  intro x hx
  have hSx : S x = 0 := hx
  have h0 : ⟪T x, x⟫_ℝ ≤ 0 := by
    have := hle x
    rwa [hSx, inner_zero_left] at this
  have hzero : ⟪T x, x⟫_ℝ = 0 := le_antisymm h0 (hT.inner_nonneg_left x)
  exact hT.apply_eq_zero_of_inner_self_eq_zero hzero

/-- **A larger kernel means a smaller range, for symmetric operators.** -/
theorem IsSymmetric.range_le_range_of_ker_le_ker [FiniteDimensional ℝ E]
    {S T : E →ₗ[ℝ] E} (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (h : LinearMap.ker S ≤ LinearMap.ker T) :
    LinearMap.range T ≤ LinearMap.range S := by
  have h1 : (LinearMap.range T)ᗮ = LinearMap.ker T := hT.orthogonal_range
  have h2 : (LinearMap.range S)ᗮ = LinearMap.ker S := hS.orthogonal_range
  have h3 : (LinearMap.ker T)ᗮ ≤ (LinearMap.ker S)ᗮ := Submodule.orthogonal_le h
  rw [← h1, ← h2, Submodule.orthogonal_orthogonal, Submodule.orthogonal_orthogonal] at h3
  exact h3

/-- **Douglas' lemma in finite dimensions.** If `0 ≤ T ≤ S` in the Loewner order then
`range T ≤ range S`: every column of `T` is `S` applied to something. -/
theorem IsPositive.range_le_range_of_le [FiniteDimensional ℝ E]
    {S T : E →ₗ[ℝ] E} (hS : S.IsPositive) (hT : T.IsPositive)
    (hle : ∀ x : E, ⟪T x, x⟫_ℝ ≤ ⟪S x, x⟫_ℝ) :
    LinearMap.range T ≤ LinearMap.range S :=
  IsSymmetric.range_le_range_of_ker_le_ker hS.isSymmetric hT.isSymmetric
    (hT.ker_le_ker_of_le hle)

end LinearMap

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Douglas' lemma in finite dimensions**, for bundled continuous operators: if `0 ≤ T ≤ S` in
the Loewner order then every vector in the range of `T` is in the range of `S`. -/
theorem exists_apply_eq_of_isPositive_of_le {S T : E →L[ℝ] E}
    (hS : (S : E →ₗ[ℝ] E).IsPositive) (hT : (T : E →ₗ[ℝ] E).IsPositive)
    (hle : ∀ x : E, ⟪T x, x⟫_ℝ ≤ ⟪S x, x⟫_ℝ) (y : E) :
    ∃ z : E, S z = T y :=
  LinearMap.IsPositive.range_le_range_of_le hS hT hle ⟨y, rfl⟩

end ContinuousLinearMap

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Douglas' lemma for matrices.** If `0 ≤ T ≤ S` in the Loewner order, then every vector
`T *ᵥ y` is of the form `S *ᵥ z`.

This is the algebraic content of "a component of a Gaussian vector is a linear function of the
whole": with `S` the covariance of `H` and `T` the cross-covariance of a component with `H`, one has
`0 ≤ T ≤ S`, and the `z` produced here is the coefficient vector of the conditional expectation of
the component given `H`. -/
theorem PosSemidef.exists_mulVec_eq_of_sub_posSemidef {S T : Matrix n n ℝ}
    (hS : S.PosSemidef) (hT : T.PosSemidef) (hle : (S - T).PosSemidef) (y : n → ℝ) :
    ∃ z : n → ℝ, S *ᵥ z = T *ᵥ y := by
  classical
  have hSpos : (Matrix.toEuclideanLin S).IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr hS
  have hTpos : (Matrix.toEuclideanLin T).IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr hT
  have hDpos : (Matrix.toEuclideanLin (S - T)).IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr hle
  have hle' : ∀ x : EuclideanSpace ℝ n,
      ⟪Matrix.toEuclideanLin T x, x⟫_ℝ ≤ ⟪Matrix.toEuclideanLin S x, x⟫_ℝ := by
    intro x
    have h := hDpos.inner_nonneg_left x
    rw [map_sub, LinearMap.sub_apply, inner_sub_left] at h
    linarith
  have hrange : LinearMap.range (Matrix.toEuclideanLin T)
      ≤ LinearMap.range (Matrix.toEuclideanLin S) :=
    LinearMap.IsPositive.range_le_range_of_le hSpos hTpos hle'
  obtain ⟨z, hz⟩ := hrange (LinearMap.mem_range_self _ (WithLp.toLp 2 y))
  refine ⟨WithLp.ofLp z, ?_⟩
  have h1 : Matrix.toEuclideanLin S z = WithLp.toLp 2 (S *ᵥ WithLp.ofLp z) := rfl
  have h2 : Matrix.toEuclideanLin T (WithLp.toLp 2 y) = WithLp.toLp 2 (T *ᵥ y) := rfl
  rw [h1, h2] at hz
  simpa using congrArg (WithLp.ofLp (p := 2)) hz

end Matrix
