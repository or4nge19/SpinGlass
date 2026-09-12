/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# The fundamental theorem of calculus for a bounded interior derivative

`intervalIntegral_eq_sub_of_hasDerivAt_of_bounded`: for `f` continuous on `[a, b]` and
differentiable on `(a, b)` with `|f'| ≤ C` there, `∫_a^b f' = f b - f a`. Mathlib's
`intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le` asks for interval integrability of
`f'`, which here comes for free: on the open interval `f'` agrees with `deriv f`, and `deriv f`
is measurable (`measurable_deriv`), so a bounded `f'` is integrable with no further hypotheses.
-/

open MeasureTheory Filter Topology Set intervalIntegral

/-- **Fundamental theorem of calculus with an interior derivative and a bound**: if `f` is
continuous on `[a, b]` and differentiable on the open interval with `|f'| ≤ C` there, then
`∫_a^b f' = f b - f a`. No measurability of `f'` is assumed: on the open interval it agrees with
`deriv f`, which is measurable. -/
theorem intervalIntegral_eq_sub_of_hasDerivAt_of_bounded {f f' : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Icc a b)) (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hbound : ∀ x ∈ Ioo a b, |f' x| ≤ C) :
    ∫ t in a..b, f' t = f b - f a := by
  have hae : ∀ᵐ x ∂(volume.restrict (Ioc a b)), f' x = deriv f x ∧ |f' x| ≤ C := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    have hnull : ∀ᵐ x : ℝ, x ≠ b := by
      have : volume ({b} : Set ℝ) = 0 := measure_singleton b
      filter_upwards [(ae_iff (p := fun x => x ≠ b)).2 (by simp [this])] with x hx using hx
    filter_upwards [hnull] with x hx hmem
    have hxo : x ∈ Ioo a b := ⟨hmem.1, lt_of_le_of_ne hmem.2 hx⟩
    exact ⟨((hderiv x hxo).deriv).symm, hbound x hxo⟩
  have hint : IntervalIntegrable f' volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    refine Integrable.mono' (g := fun _ => C) (integrable_const C) ?_ ?_
    · refine AEStronglyMeasurable.congr (measurable_deriv f).aestronglyMeasurable ?_
      filter_upwards [hae] with x hx using hx.1.symm
    · filter_upwards [hae] with x hx
      rw [Real.norm_eq_abs]
      exact hx.2
  exact integral_eq_sub_of_hasDeriv_right_of_le hab hcont
    (fun x hx => (hderiv x hx).hasDerivWithinAt) hint
