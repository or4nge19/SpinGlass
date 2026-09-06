import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# `log ∘ cosh` / `tanh` calculus

One-dimensional derivatives of `Real.tanh` and `x ↦ log (cosh x)`, and Fréchet/Hessian formulas
for `z ↦ log (cosh (β * L z + h))`. Backend for Hopfield `ψ`.
-/

open scoped BigOperators

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
    (hs.div hc hcosh_ne)
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
    simpa [Function.comp] using hlog.comp x hcosh
  simpa [Real.tanh_eq_sinh_div_cosh, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hcomp

end Real

namespace SpinGlass

/-! ## CLM compositions -/

namespace LogCosh

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The single-site contribution `z ↦ log(cosh(β * L z + h))`. -/
noncomputable def term (β h : ℝ) (L : V →L[ℝ] ℝ) (z : V) : ℝ :=
  Real.log (Real.cosh (β * L z + h))

/-- Fréchet derivative of `term`. -/
noncomputable def termFDeriv (β h : ℝ) (L : V →L[ℝ] ℝ) (z : V) : V →L[ℝ] ℝ :=
  (Real.tanh (β * L z + h) * β) • L

/-- Hessian (second Fréchet derivative) of `term`. -/
noncomputable def termFDeriv2 (β h : ℝ) (L : V →L[ℝ] ℝ) (z : V) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  ((1 - Real.tanh (β * L z + h) ^ 2) * β ^ 2) • (L.smulRight L)

@[fun_prop] theorem hasFDerivAt_term (β h : ℝ) (L : V →L[ℝ] ℝ) (z : V) :
    HasFDerivAt (term (V := V) β h L) (termFDeriv (V := V) β h L z) z := by
  -- `u(z) = β * L z + h`
  let u : V → ℝ := fun z => β * L z + h
  have hu : HasFDerivAt u (β • L) z := by
    -- linear part + constant
    simpa [u, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      (L.hasFDerivAt.const_smul β).add_const h
  -- compose `log ∘ cosh` with `u`
  simpa [term, termFDeriv, u, smul_smul, mul_assoc, mul_left_comm, mul_comm] using
    (HasDerivAt.comp_hasFDerivAt z (Real.hasDerivAt_log_cosh (u z)) hu)

@[fun_prop] theorem hasFDerivAt_termFDeriv (β h : ℝ) (L : V →L[ℝ] ℝ) (z : V) :
    HasFDerivAt (termFDeriv (V := V) β h L) (termFDeriv2 (V := V) β h L z) z := by
  -- `u(z) = β * L z + h`
  let u : V → ℝ := fun z => β * L z + h
  have hu : HasFDerivAt u (β • L) z := by
    simpa [u, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      (L.hasFDerivAt.const_smul β).add_const h
  have htanh :
      HasFDerivAt (fun z => Real.tanh (u z))
        ((1 - Real.tanh (u z) ^ 2) • (β • L)) z := by
    simpa [u] using
      (HasDerivAt.comp_hasFDerivAt z (Real.hasDerivAt_tanh (u z)) hu)
  have hcoeff :
      HasFDerivAt (fun z => Real.tanh (u z) * β)
        (β • ((1 - Real.tanh (u z) ^ 2) • (β • L))) z := by
    simpa [mul_assoc, smul_eq_mul] using (htanh.mul_const β)
  have hsmul :
      HasFDerivAt (fun z => (Real.tanh (u z) * β) • L)
        ((β • ((1 - Real.tanh (u z) ^ 2) • (β • L))).smulRight L) z :=
    hcoeff.smul_const L
  -- rewrite the derivative in the rank-one form used in `termFDeriv2`
  refine hsmul.congr_fderiv ?_
  ext v w
  simp [termFDeriv2, u, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, pow_two,
    ContinuousLinearMap.smulRight_apply]

variable {ι : Type*} [Fintype ι]

/-- `∑ i, log(cosh(β * L i z + h))`, written as a `Finset.univ` sum for calculus. -/
noncomputable def sum (β h : ℝ) (L : ι → V →L[ℝ] ℝ) (z : V) : ℝ :=
  ∑ i : ι, term (V := V) β h (L i) z

/-- Fréchet derivative of `sum`. -/
noncomputable def sumFDeriv (β h : ℝ) (L : ι → V →L[ℝ] ℝ) (z : V) : V →L[ℝ] ℝ :=
  ∑ i : ι, termFDeriv (V := V) β h (L i) z

/-- Hessian (second Fréchet derivative) of `sum`. -/
noncomputable def sumFDeriv2 (β h : ℝ) (L : ι → V →L[ℝ] ℝ) (z : V) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  ∑ i : ι, termFDeriv2 (V := V) β h (L i) z

@[fun_prop] theorem hasFDerivAt_sum (β h : ℝ) (L : ι → V →L[ℝ] ℝ) (z : V) :
    HasFDerivAt (sum (V := V) β h L) (sumFDeriv (V := V) β h L z) z := by
  classical
  -- termwise derivatives + finite sum
  simpa [sum, sumFDeriv] using
    (HasFDerivAt.fun_sum (u := (Finset.univ : Finset ι))
      (A := fun i : ι => term (V := V) β h (L i))
      (A' := fun i : ι => termFDeriv (V := V) β h (L i) z)
      (x := z)
      (by
        intro i _hi
        simpa using hasFDerivAt_term (V := V) (β := β) (h := h) (L := L i) (z := z)))

@[fun_prop] theorem hasFDerivAt_sumFDeriv (β h : ℝ) (L : ι → V →L[ℝ] ℝ) (z : V) :
    HasFDerivAt (sumFDeriv (V := V) β h L) (sumFDeriv2 (V := V) β h L z) z := by
  classical
  simpa [sumFDeriv, sumFDeriv2] using
    (HasFDerivAt.fun_sum (u := (Finset.univ : Finset ι))
      (A := fun i : ι => termFDeriv (V := V) β h (L i))
      (A' := fun i : ι => termFDeriv2 (V := V) β h (L i) z)
      (x := z)
      (by
        intro i _hi
        simpa using hasFDerivAt_termFDeriv (V := V) (β := β) (h := h) (L := L i) (z := z)))

end LogCosh

end SpinGlass

