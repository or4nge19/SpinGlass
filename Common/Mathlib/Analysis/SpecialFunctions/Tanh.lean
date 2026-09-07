/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Derivatives of `tanh` and of `log ∘ cosh`

Mathlib defines `Real.tanh` and knows `logDeriv Real.cosh = Real.tanh`, but has no derivative
lemma for `Real.tanh` itself. This file supplies

`(tanh)' x = 1 - tanh x ^ 2`  and  `(log ∘ cosh)' x = tanh x`,

in `HasDerivAt` form. The second is the free energy of a single spin in a field, and the first is
its magnetization, so both are the basic one-dimensional input to mean-field computations.

## Main statements

- `Real.hasDerivAt_tanh`
- `Real.hasDerivAt_log_cosh`
-/

namespace Real

/-! ## One-dimensional calculus -/

/-- Derivative of `Real.tanh`: \( (\tanh)'(x) = 1 - \tanh(x)^2\). -/
theorem hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  -- Use `tanh = sinh / cosh` and the quotient rule.
  have hcosh_ne : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have hs : HasDerivAt Real.sinh (Real.cosh x) x := Real.hasDerivAt_sinh x
  have hc : HasDerivAt Real.cosh (Real.sinh x) x := Real.hasDerivAt_cosh x
  have hdiv :
      HasDerivAt (fun t : ℝ => Real.sinh t / Real.cosh t)
        ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2) x :=
    (hs.fun_div hc hcosh_ne)
  have htanh₀ :
      HasDerivAt Real.tanh
        ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2) x := by
    -- change the differentiated function using `tanh = sinh / cosh`
    refine hdiv.congr_of_eventuallyEq ?_
    refine Filter.Eventually.of_forall (fun t => ?_)
    simpa using (Real.tanh_eq_sinh_div_cosh t)
  have hnum : Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x = (1 : ℝ) := by
    simpa [pow_two] using (Real.cosh_sq_sub_sinh_sq x)
  have htanh₁ : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
    -- rewrite the quotient-rule numerator using `cosh^2 - sinh^2 = 1`
    simpa [hnum, div_eq_mul_inv, one_div] using htanh₀
  have hcosh2_ne : (Real.cosh x ^ 2) ≠ 0 := by
    exact pow_ne_zero 2 hcosh_ne
  have hrewrite : (1 / Real.cosh x ^ 2) = (1 - Real.tanh x ^ 2) := by
    -- `1 - tanh^2 = (cosh^2 - sinh^2)/cosh^2 = 1/cosh^2`.
    have haux : (1 - Real.tanh x ^ 2) = (1 / Real.cosh x ^ 2) := by
      calc
        (1 - Real.tanh x ^ 2)
            = 1 - (Real.sinh x / Real.cosh x) ^ 2 := by
                simp [Real.tanh_eq_sinh_div_cosh]
        _ = 1 - (Real.sinh x ^ 2 / Real.cosh x ^ 2) := by
              simp [div_pow]
        _ = 1 / Real.cosh x ^ 2 := by
              -- `1 - a/b = (b-a)/b = 1/b` using `cosh^2 - sinh^2 = 1`
              simp [one_sub_div (a := Real.sinh x ^ 2) (b := Real.cosh x ^ 2) hcosh2_ne,
                Real.cosh_sq_sub_sinh_sq, one_div]
    simpa using haux.symm
  simpa [hrewrite] using htanh₁

/-- Derivative of `x ↦ log (cosh x)`: \( (\log\cosh)'(x) = \tanh(x)\). -/
theorem hasDerivAt_log_cosh (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.log (Real.cosh t)) (Real.tanh x) x := by
  have hcosh : HasDerivAt Real.cosh (Real.sinh x) x := Real.hasDerivAt_cosh x
  have hlog : HasDerivAt Real.log (Real.cosh x)⁻¹ (Real.cosh x) :=
    Real.hasDerivAt_log (ne_of_gt (Real.cosh_pos x))
  have hcomp :
      HasDerivAt (fun t : ℝ => Real.log (Real.cosh t)) ((Real.cosh x)⁻¹ * Real.sinh x) x := by
    simpa [Function.comp_def] using hlog.comp x hcosh
  simpa [Real.tanh_eq_sinh_div_cosh, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hcomp

end Real
