/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FinCases

/-!
# Sedrakyan's lemma for two terms

Mathlib's `Finset.sq_sum_div_le_sum_sq_div` is Sedrakyan's (Engel's, Titu's) form of the
Cauchy–Schwarz inequality, `(∑ fᵢ)² / ∑ gᵢ ≤ ∑ fᵢ²/gᵢ`. This file records the two-term case, which
is the one that appears in subadditivity arguments: splitting a system of `x + y` sites into two
blocks replaces `(a+b)²/(x+y)` by `a²/x + b²/y`, and the inequality is exactly what makes the
split system's covariance dominate the whole system's.
-/

namespace Real

/-- **Sedrakyan's lemma, two terms**: `(a + b)² / (x + y) ≤ a²/x + b²/y` for positive `x`, `y`.
The two-term case of `Finset.sq_sum_div_le_sum_sq_div`. -/
theorem sq_add_div_add_le {a b x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (a + b) ^ 2 / (x + y) ≤ a ^ 2 / x + b ^ 2 / y := by
  have h := Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset (Fin 2))
    (f := ![a, b]) (g := ![x, y]) (fun i _ => by fin_cases i <;> simpa)
  simpa [Fin.sum_univ_two] using h

end Real
