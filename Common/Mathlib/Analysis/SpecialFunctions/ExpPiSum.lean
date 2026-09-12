/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Pi

/-!
# Sums of exponentials of sums over sites factorize

`∑_{σ ∈ ∏ᵢ Sᵢ} exp (∑ᵢ fᵢ(σᵢ)) = ∏ᵢ ∑_{s ∈ Sᵢ} exp (fᵢ s)`: the partition function of a system of
independent sites is the product of the site partition functions. This is `Fintype.prod_sum`
after `Real.exp_sum`; it is the algebraic content of every site factorization of a mean-field
partition function without interaction between the sites (Talagrand, Vol. II, (14.80), (14.142)).
-/

open Finset

/-- `∑_{σ} exp (∑ᵢ fᵢ(σᵢ)) = ∏ᵢ ∑_{s} exp (fᵢ s)`. -/
theorem Fintype.sum_exp_sum_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] (f : ∀ i, κ i → ℝ) :
    ∑ σ : ∀ i, κ i, Real.exp (∑ i, f i (σ i)) = ∏ i, ∑ s, Real.exp (f i s) := by
  simp_rw [Real.exp_sum]
  exact (Fintype.prod_sum fun i s => Real.exp (f i s)).symm
