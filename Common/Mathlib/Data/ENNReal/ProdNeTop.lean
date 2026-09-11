/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Data.ENNReal.BigOperators

/-!
# A finite product in `ℝ≥0∞` is finite only if its factors are

`ENNReal.prod_ne_top` says that a product of finite factors is finite; the converse needs the
factors to be nonzero (`0 * ∞ = 0`).
-/

open scoped ENNReal

namespace ENNReal

/-- A finite product of nonzero values of `ℝ≥0∞` is finite only if every factor is. -/
lemma ne_top_of_prod_ne_top {ι : Type*} [Fintype ι] {f : ι → ℝ≥0∞}
    (h0 : ∀ j, f j ≠ 0) (h : ∏ j, f j ≠ ∞) (i : ι) : f i ≠ ∞ := by
  classical
  intro hi
  apply h
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i), hi]
  exact ENNReal.top_mul (Finset.prod_ne_zero_iff.2 fun j _ => h0 j)

end ENNReal
