/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.Function

/-!
# Convexity of log-sum-exp

`x ↦ log ∑ᵢ exp (xᵢ)` is convex. This is the structural fact behind almost every convexity
statement in statistical mechanics: the free energy `β ↦ (1/N) log ∑_σ exp(-β H(σ))` is convex in
every parameter entering the Hamiltonian linearly (Talagrand, *Mean Field Models for Spin Glasses*,
Vol. I, §1.3, equation (1.81); Vol. II, equation (12.8)), and convexity is what makes Griffiths'
lemma — hence the whole theory of derivatives of the free energy — available.

Mathlib knows that `x ↦ log ∑ exp xᵢ` is smooth and computes its Hessian, but does not record its
convexity. The proof below is the classical one: after normalising, the inequality is the weighted
arithmetic–geometric mean inequality `p₁^a p₂^b ≤ a p₁ + b p₂` applied coordinatewise
(`Real.geom_mean_le_arith_mean2_weighted`), which is Hölder's inequality in disguise.

## Main statements

- `Real.sum_exp_add_le_rpow_mul_rpow`: the multiplicative form, `∑ exp(a uᵢ + b vᵢ) ≤ U^a V^b`.
- `Real.log_sum_exp_le`: the two-point convexity inequality.
- `convexOn_log_sum_exp`: `ConvexOn ℝ univ fun x => log ∑ exp (x i)`.
-/

open Finset

namespace Real

variable {α : Type*} [Fintype α]

private lemma exp_rpow (t a : ℝ) : (Real.exp t) ^ a = Real.exp (a * t) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp, mul_comm]

/-- **Hölder's inequality for exponential sums.** -/
theorem sum_exp_add_le_rpow_mul_rpow (u v : α → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ∑ i, Real.exp (a * u i + b * v i)
      ≤ (∑ i, Real.exp (u i)) ^ a * (∑ i, Real.exp (v i)) ^ b := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · simp only [Finset.univ_eq_empty, Finset.sum_empty]
    positivity
  set U := ∑ i, Real.exp (u i) with hU
  set V := ∑ i, Real.exp (v i) with hV
  have hUpos : 0 < U :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) ⟨hα.some, Finset.mem_univ _⟩
  have hVpos : 0 < V :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) ⟨hα.some, Finset.mem_univ _⟩
  -- Coordinatewise weighted AM–GM after normalising.
  have key : ∀ i : α, Real.exp (a * u i + b * v i)
      ≤ U ^ a * V ^ b * (a * (Real.exp (u i) / U) + b * (Real.exp (v i) / V)) := by
    intro i
    have hgm := Real.geom_mean_le_arith_mean2_weighted ha hb
      (le_of_lt (div_pos (Real.exp_pos (u i)) hUpos))
      (le_of_lt (div_pos (Real.exp_pos (v i)) hVpos)) hab
    have hsplit : Real.exp (a * u i + b * v i)
        = U ^ a * V ^ b * ((Real.exp (u i) / U) ^ a * (Real.exp (v i) / V) ^ b) := by
      rw [Real.div_rpow (Real.exp_pos _).le hUpos.le,
        Real.div_rpow (Real.exp_pos _).le hVpos.le, exp_rpow, exp_rpow, Real.exp_add]
      field_simp
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hgm (by positivity)
  calc ∑ i, Real.exp (a * u i + b * v i)
      ≤ ∑ i, U ^ a * V ^ b * (a * (Real.exp (u i) / U) + b * (Real.exp (v i) / V)) :=
        Finset.sum_le_sum fun i _ => key i
    _ = U ^ a * V ^ b := by
        rw [← Finset.mul_sum]
        have h1 : ∑ i, (a * (Real.exp (u i) / U) + b * (Real.exp (v i) / V)) = 1 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            ← Finset.sum_div, ← Finset.sum_div, ← hU, ← hV,
            div_self hUpos.ne', div_self hVpos.ne']
          simpa using hab
        rw [h1, mul_one]

/-- **The two-point convexity inequality for log-sum-exp.** -/
theorem log_sum_exp_le (u v : α → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    Real.log (∑ i, Real.exp (a * u i + b * v i))
      ≤ a * Real.log (∑ i, Real.exp (u i)) + b * Real.log (∑ i, Real.exp (v i)) := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · simp
  have hUpos : 0 < ∑ i, Real.exp (u i) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) ⟨hα.some, Finset.mem_univ _⟩
  have hVpos : 0 < ∑ i, Real.exp (v i) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) ⟨hα.some, Finset.mem_univ _⟩
  have hLpos : 0 < ∑ i, Real.exp (a * u i + b * v i) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) ⟨hα.some, Finset.mem_univ _⟩
  have hle := sum_exp_add_le_rpow_mul_rpow u v ha hb hab
  calc Real.log (∑ i, Real.exp (a * u i + b * v i))
      ≤ Real.log ((∑ i, Real.exp (u i)) ^ a * (∑ i, Real.exp (v i)) ^ b) :=
        Real.log_le_log hLpos hle
    _ = a * Real.log (∑ i, Real.exp (u i)) + b * Real.log (∑ i, Real.exp (v i)) := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hUpos,
          Real.log_rpow hVpos]

end Real

/-- **Log-sum-exp is convex.** -/
theorem convexOn_log_sum_exp {α : Type*} [Fintype α] :
    ConvexOn ℝ (Set.univ : Set (α → ℝ)) fun x => Real.log (∑ i, Real.exp (x i)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simpa using Real.log_sum_exp_le x y ha hb hab
