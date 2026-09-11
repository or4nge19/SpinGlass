/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Data.ENNReal.Inv

/-!
# Quotients and powers in `ℝ≥0∞`

`ℝ≥0∞` is not a `DivisionMonoid`: `(0 * ∞)⁻¹ = 0⁻¹ = ∞` while `∞⁻¹ * 0⁻¹ = 0`. So the generic
lemmas `div_pow` and `div_mul_div_comm` do not apply. Both identities are nevertheless available:

* `ENNReal.div_pow` holds **unconditionally**, because `(b⁻¹)^n = (b^n)⁻¹` does
  (`ENNReal.inv_pow`) even though `(b * c)⁻¹ = b⁻¹ * c⁻¹` does not;
* `ENNReal.div_mul_div_comm` holds under exactly the hypotheses of `ENNReal.mul_inv`, and in
  particular whenever both denominators are nonzero.
-/

open scoped ENNReal

namespace ENNReal

/-- **`(a / b) ^ n = a ^ n / b ^ n` in `ℝ≥0∞`, unconditionally.** The generic `div_pow` needs a
`DivisionMonoid`, which `ℝ≥0∞` is not; but `ENNReal.inv_pow` is unconditional, and that is all
the identity uses. -/
protected theorem div_pow (a b : ℝ≥0∞) (n : ℕ) : (a / b) ^ n = a ^ n / b ^ n := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow]

/-- **`(a₁ / b₁) * (a₂ / b₂) = (a₁ a₂) / (b₁ b₂)` in `ℝ≥0∞`**, under the hypotheses of
`ENNReal.mul_inv`. -/
protected theorem div_mul_div_comm {a₁ a₂ b₁ b₂ : ℝ≥0∞} (h : b₁ ≠ 0 ∨ b₂ ≠ ∞)
    (h' : b₁ ≠ ∞ ∨ b₂ ≠ 0) : a₁ / b₁ * (a₂ / b₂) = a₁ * a₂ / (b₁ * b₂) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv h h']
  ring

/-- The form of `ENNReal.div_mul_div_comm` used when both denominators are nonzero. -/
protected theorem div_mul_div_comm_of_ne_zero {a₁ a₂ b₁ b₂ : ℝ≥0∞} (h₁ : b₁ ≠ 0)
    (h₂ : b₂ ≠ 0) : a₁ / b₁ * (a₂ / b₂) = a₁ * a₂ / (b₁ * b₂) :=
  ENNReal.div_mul_div_comm (Or.inl h₁) (Or.inr h₂)

end ENNReal
