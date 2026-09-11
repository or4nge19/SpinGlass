/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Analysis.SpecialFunctions.ExpPiSum
import SpinGlass.Parisi.CoupledScheme

/-!
# The endpoint `s = 0` of the coupled interpolation: the sites decouple

Talagrand, Vol. II, (14.140)–(14.143). Once the constraint `R_{1,2} = u` is dropped (the `λ`-trick,
`wZ_mul_le_exp_mul_wZ_sub`), the partition function of the pair `(σ¹, σ²)` for a Hamiltonian of
the form `∑ᵢ (σ¹ᵢ aᵢ + σ²ᵢ bᵢ + λ σ¹ᵢ σ²ᵢ)` factorizes over the sites (`Fintype.sum_exp_sum_pi`),
with the site partition function

`∑_{ε₁,ε₂ = ±1} exp (ε₁ x₁ + ε₂ x₂ + ε₁ ε₂ λ) = 4 (ch x₁ ch x₂ ch λ + sh x₁ sh x₂ sh λ)`   (14.142).
-/

open Finset
open scoped BigOperators

namespace SpinGlass

noncomputable section

/-- **Talagrand's (14.142)**: the partition function of one site of the coupled pair. -/
lemma sum_exp_pairSpin (x₁ x₂ lam : ℝ) :
    ∑ ε : Fin 2 → Bool, Real.exp (isingSpin (ε 0) * x₁ + isingSpin (ε 1) * x₂
        + isingSpin (ε 0) * isingSpin (ε 1) * lam)
      = 4 * (Real.cosh x₁ * Real.cosh x₂ * Real.cosh lam
          + Real.sinh x₁ * Real.sinh x₂ * Real.sinh lam) := by
  rw [← (piFinTwoEquiv fun _ : Fin 2 => Bool).symm.sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, piFinTwoEquiv_symm_apply, Fin.cons_zero,
    Fin.cons_one, isingSpin_true, isingSpin_false, Real.cosh_eq, Real.sinh_eq]
  simp only [one_mul, mul_neg, neg_neg, mul_one, neg_mul, Real.exp_add, Real.exp_neg]
  have h1 := Real.exp_pos x₁
  have h2 := Real.exp_pos x₂
  have h3 := Real.exp_pos lam
  field_simp
  ring

/-- **The partition function of the unconstrained pair factorizes over the sites** (Talagrand
Vol. II, (14.142) summed over the sites): for `H(σ¹,σ²) = -∑ᵢ (σ¹ᵢ aᵢ + σ²ᵢ bᵢ + λ σ¹ᵢ σ²ᵢ)`,

`∑_{σ¹,σ²} exp (-H) = ∏ᵢ 4 (ch aᵢ ch bᵢ ch λ + sh aᵢ sh bᵢ sh λ)`. -/
theorem sum_pairConfig_exp (N : ℕ) (a b : Fin N → ℝ) (lam : ℝ) :
    ∑ σ : Fin 2 → Config N, Real.exp (∑ i, (isingSpin (σ 0 i) * a i + isingSpin (σ 1 i) * b i
        + isingSpin (σ 0 i) * isingSpin (σ 1 i) * lam))
      = ∏ i, 4 * (Real.cosh (a i) * Real.cosh (b i) * Real.cosh lam
          + Real.sinh (a i) * Real.sinh (b i) * Real.sinh lam) := by
  classical
  rw [← (Equiv.piComm fun (_ : Fin 2) (_ : Fin N) => Bool).symm.sum_comp]
  change ∑ s : Fin N → Fin 2 → Bool, Real.exp (∑ i, (isingSpin (s i 0) * a i
    + isingSpin (s i 1) * b i + isingSpin (s i 0) * isingSpin (s i 1) * lam)) = _
  rw [Fintype.sum_exp_sum_pi (fun i (ε : Fin 2 → Bool) => isingSpin (ε 0) * a i
    + isingSpin (ε 1) * b i + isingSpin (ε 0) * isingSpin (ε 1) * lam)]
  exact Finset.prod_congr rfl fun i _ => sum_exp_pairSpin (a i) (b i) lam

end

end SpinGlass
