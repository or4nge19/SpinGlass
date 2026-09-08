/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A polynomial with nonnegative coefficients is maximised at the endpoint of the unit interval

For `P : ℝ[X]` with `0 ≤ P.coeff n` for every `n`, the evaluation on the closed unit disc is
dominated by its value at `1`:

`|r| ≤ 1 → |P.eval r| ≤ P.eval 1`.

Mathlib records that such polynomials are monotone on `[0, ∞)` but not this two-sided bound, which
is what identifies `P.eval 1` as the *diagonal* of an overlap-driven covariance kernel: for a mixed
`p`-spin model the covariance is `N ξ(R_{στ})` with `ξ = P.eval` and `|R| ≤ 1`, so the kernel is
bounded by its diagonal `N ξ(1)` — exactly the hypothesis the self-averaging theory needs
(Talagrand, *Mean Field Models for Spin Glasses*, Vol. II, Eq. (14.57)).

## Main statements

- `Polynomial.eval_one_nonneg_of_nonneg_coeff`.
- `Polynomial.abs_eval_le_eval_one_of_nonneg_coeff`.
-/

namespace Polynomial

variable {P : ℝ[X]}

/-- A polynomial with nonnegative coefficients has nonnegative value at `1`. -/
theorem eval_one_nonneg_of_nonneg_coeff (hP : ∀ n, 0 ≤ P.coeff n) : 0 ≤ P.eval 1 := by
  rw [eval_eq_sum_range]
  exact Finset.sum_nonneg fun i _ => by simpa using hP i

/-- **A polynomial with nonnegative coefficients is bounded on the unit disc by its value at
`1`.** -/
theorem abs_eval_le_eval_one_of_nonneg_coeff (hP : ∀ n, 0 ≤ P.coeff n) {r : ℝ} (hr : |r| ≤ 1) :
    |P.eval r| ≤ P.eval 1 := by
  rw [eval_eq_sum_range, eval_eq_sum_range]
  calc |∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * r ^ i|
      ≤ ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i * r ^ i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * 1 ^ i := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (hP i), abs_pow, one_pow, mul_one]
        have h1 : |r| ^ i ≤ 1 := pow_le_one₀ (abs_nonneg r) hr
        calc P.coeff i * |r| ^ i ≤ P.coeff i * 1 :=
              mul_le_mul_of_nonneg_left h1 (hP i)
          _ = P.coeff i := mul_one _

end Polynomial
