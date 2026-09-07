import Common.Mathlib.Analysis.SpecialFunctions.Tanh
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
    simpa [u, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, Pi.smul_def] using
      (L.hasFDerivAt.fun_const_smul β).add_const h
  -- compose `log ∘ cosh` with `u`
  -- compose `log ∘ cosh` with `u`
  convert! HasDerivAt.comp_hasFDerivAt z (Real.hasDerivAt_log_cosh (u z)) hu
  ext x
  simp [termFDeriv, u, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

@[fun_prop] theorem hasFDerivAt_termFDeriv (β h : ℝ) (L : V →L[ℝ] ℝ) (z : V) :
    HasFDerivAt (termFDeriv (V := V) β h L) (termFDeriv2 (V := V) β h L z) z := by
  -- `u(z) = β * L z + h`
  let u : V → ℝ := fun z => β * L z + h
  have hu : HasFDerivAt u (β • L) z := by
    simpa [u, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, Pi.smul_def] using
      (L.hasFDerivAt.fun_const_smul β).add_const h
  have htanh :
      HasFDerivAt (fun z => Real.tanh (u z))
        ((1 - Real.tanh (u z) ^ 2) • (β • L)) z := by
    simpa [u, Function.comp_def] using
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
  unfold sum sumFDeriv
  exact HasFDerivAt.fun_sum (u := (Finset.univ : Finset ι))
      (A := fun i : ι => term (V := V) β h (L i))
      (A' := fun i : ι => termFDeriv (V := V) β h (L i) z)
      (x := z)
      (fun i _hi => hasFDerivAt_term (V := V) (β := β) (h := h) (L := L i) (z := z))

@[fun_prop] theorem hasFDerivAt_sumFDeriv (β h : ℝ) (L : ι → V →L[ℝ] ℝ) (z : V) :
    HasFDerivAt (sumFDeriv (V := V) β h L) (sumFDeriv2 (V := V) β h L z) z := by
  classical
  unfold sumFDeriv sumFDeriv2
  exact HasFDerivAt.fun_sum (u := (Finset.univ : Finset ι))
      (A := fun i : ι => termFDeriv (V := V) β h (L i))
      (A' := fun i : ι => termFDeriv2 (V := V) β h (L i) z)
      (x := z)
      (fun i _hi => hasFDerivAt_termFDeriv (V := V) (β := β) (h := h) (L := L i) (z := z))

end LogCosh

end SpinGlass

