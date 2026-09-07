/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The geometric mean as the infimum of weighted arithmetic means

For `a, b ≥ 0`, the family of weighted arithmetic means `λ ↦ λ a + b / λ`, `λ > 0`, has infimum
`2 √a √b`, attained at `λ = √b / √a` when both are positive. This file records the two halves of
that statement:

* `Real.two_mul_sqrt_mul_sqrt_le`: `2 √a √b ≤ λ a + b / λ` — the weighted AM–GM inequality;
* `Real.le_sqrt_mul_sqrt_of_forall_pos`: if `2 c` is below every member of the family then
  `c ≤ √a √b`.

The second is the useful direction in practice: a quantity bounded by every weighted arithmetic
mean of two nonnegative quantities is bounded by their geometric mean. It is what upgrades an
arithmetic–geometric estimate (which is what a "complete the square" argument produces directly)
to a Cauchy–Schwarz estimate, without any optimisation being visible in the intermediate
statements.
-/

namespace Real

/-- **Weighted AM–GM**: `2 √a √b ≤ λ a + b / λ` for every `λ > 0`. -/
theorem two_mul_sqrt_mul_sqrt_le {a b lam : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hlam : 0 < lam) :
    2 * (Real.sqrt a * Real.sqrt b) ≤ lam * a + b / lam := by
  have hw0 : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hu : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hv : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  have hw : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam.le
  have hexp : (Real.sqrt lam * Real.sqrt a - Real.sqrt b / Real.sqrt lam) ^ 2
      = Real.sqrt lam ^ 2 * Real.sqrt a ^ 2 + Real.sqrt b ^ 2 / Real.sqrt lam ^ 2
        - 2 * (Real.sqrt a * Real.sqrt b) := by
    field_simp
    ring
  have hnn : (0 : ℝ) ≤ (Real.sqrt lam * Real.sqrt a - Real.sqrt b / Real.sqrt lam) ^ 2 :=
    sq_nonneg _
  rw [hexp, hu, hv, hw] at hnn
  linarith

/-- If `2 c` is at most every weighted arithmetic mean `λ a + b / λ` of two nonnegative reals,
then `c` is at most their geometric mean. -/
theorem le_sqrt_mul_sqrt_of_forall_pos {c a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ lam : ℝ, 0 < lam → 2 * c ≤ lam * a + b / lam) :
    c ≤ Real.sqrt a * Real.sqrt b := by
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · -- `a = 0`: the family tends to `0`, so `c ≤ 0 = √a √b`.
    have hc0 : c ≤ 0 := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hlam : (0 : ℝ) < (b + 1) / ε := by positivity
      have hle := h _ hlam
      have hb' : b / ((b + 1) / ε) ≤ ε := by
        rw [div_div_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      have haz : a = 0 := ha0.symm
      rw [haz] at hle
      simp at hle
      linarith
    calc c ≤ 0 := hc0
      _ = Real.sqrt a * Real.sqrt b := by rw [← ha0]; simp
  · rcases eq_or_lt_of_le hb with hb0 | hb0
    · -- `b = 0`: the family tends to `0` as `λ → 0`.
      have hc0 : c ≤ 0 := by
        refine le_of_forall_pos_le_add fun ε hε => ?_
        have hlam : (0 : ℝ) < ε / a := by positivity
        have hle := h _ hlam
        have : ε / a * a = ε := div_mul_cancel₀ ε ha0.ne'
        rw [this, ← hb0] at hle
        simp at hle
        linarith
      calc c ≤ 0 := hc0
        _ = Real.sqrt a * Real.sqrt b := by rw [← hb0]; simp
    · -- both positive: evaluate at `λ = √b / √a`.
      have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
      have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb0
      have hlam : (0 : ℝ) < Real.sqrt b / Real.sqrt a := by positivity
      have hle := h _ hlam
      have h1 : Real.sqrt b / Real.sqrt a * a = Real.sqrt a * Real.sqrt b := by
        field_simp
        nlinarith [Real.mul_self_sqrt ha]
      have h2 : b / (Real.sqrt b / Real.sqrt a) = Real.sqrt a * Real.sqrt b := by
        field_simp
        nlinarith [Real.mul_self_sqrt hb]
      rw [h1, h2] at hle
      linarith

end Real
