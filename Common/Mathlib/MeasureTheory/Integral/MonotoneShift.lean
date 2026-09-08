/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The integrated increment of a monotone function

For a monotone `g` and a shift `δ > 0`, the integral of the increment `g(x+δ) - g(x-δ)` over
`[a, b]` telescopes: shifting the two integrals to a common variable leaves only the two end
windows, each of width `2δ`. Hence

`∫_a^b (g(x+δ) - g(x-δ)) dx ≤ 2δ (g(b+δ) - g(a-δ))`.

The bound is uniform in `b - a`: however long the interval, the total increment is at most `2δ`
times the *global* increment of `g` across the enlarged interval. That is what makes the
quantitative Griffiths estimate integrable in the parameter — Talagrand, *Mean Field Models for
Spin Glasses*, Vol. II, §12.1, in the passage from (12.14) to (12.7).

## Main statements

- `intervalIntegral.integral_sub_shift_le_of_monotone`.
-/

open MeasureTheory Set

namespace intervalIntegral

variable {g : ℝ → ℝ} {a b δ : ℝ}

/-- **The integrated increment of a monotone function across a window of width `2δ` is at most
`2δ` times its global increment.** No ordering of `a` and `b` is needed: interval integrals are
signed and the telescoping identity is unconditional. -/
theorem integral_sub_shift_le_of_monotone (hg : Monotone g) (hδ : 0 < δ) :
    (∫ x in a..b, (g (x + δ) - g (x - δ))) ≤ 2 * δ * (g (b + δ) - g (a - δ)) := by
  have hint : ∀ p q : ℝ, IntervalIntegrable g volume p q := fun p q =>
    (hg.monotoneOn (uIcc p q)).intervalIntegrable
  have hshift : ∀ p q d : ℝ, IntervalIntegrable (fun x => g (x + d)) volume p q := by
    intro p q d
    have := hint (p + d) (q + d)
    simpa using this.comp_add_right d
  have hsplit : (∫ x in a..b, (g (x + δ) - g (x - δ)))
      = (∫ x in a + δ..b + δ, g x) - ∫ x in a - δ..b - δ, g x := by
    rw [intervalIntegral.integral_sub (hshift a b δ) (by
      simpa [sub_eq_add_neg] using hshift a b (-δ)),
      intervalIntegral.integral_comp_add_right (a := a) (b := b) (f := g) δ,
      intervalIntegral.integral_comp_sub_right (a := a) (b := b) (f := g) δ]
  -- Telescoping: the two shifted intervals share `[a+δ, b-δ]`.
  have htel : (∫ x in a + δ..b + δ, g x) - ∫ x in a - δ..b - δ, g x
      = (∫ x in b - δ..b + δ, g x) - ∫ x in a - δ..a + δ, g x := by
    have h1 : (∫ x in a + δ..b - δ, g x) + ∫ x in b - δ..b + δ, g x
        = ∫ x in a + δ..b + δ, g x :=
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
    have h2 : (∫ x in a - δ..a + δ, g x) + ∫ x in a + δ..b - δ, g x
        = ∫ x in a - δ..b - δ, g x :=
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
    rw [← h1, ← h2]
    ring
  -- The two end windows are bounded by the values of `g` at the outer endpoints.
  have hupper : (∫ x in b - δ..b + δ, g x) ≤ 2 * δ * g (b + δ) := by
    have hle : b - δ ≤ b + δ := by linarith
    have := intervalIntegral.integral_mono_on hle (hint _ _)
      (intervalIntegrable_const (c := g (b + δ)))
      (fun x hx => hg (by simpa using hx.2 : x ≤ b + δ))
    rw [intervalIntegral.integral_const] at this
    calc (∫ x in b - δ..b + δ, g x) ≤ ((b + δ) - (b - δ)) • g (b + δ) := this
      _ = 2 * δ * g (b + δ) := by
          rw [show (b + δ) - (b - δ) = 2 * δ by ring, smul_eq_mul]
  have hlower : 2 * δ * g (a - δ) ≤ ∫ x in a - δ..a + δ, g x := by
    have hle : a - δ ≤ a + δ := by linarith
    have := intervalIntegral.integral_mono_on hle
      (intervalIntegrable_const (c := g (a - δ))) (hint _ _)
      (fun x hx => hg (by simpa using hx.1 : a - δ ≤ x))
    rw [intervalIntegral.integral_const] at this
    calc 2 * δ * g (a - δ) = ((a + δ) - (a - δ)) • g (a - δ) := by
          rw [show (a + δ) - (a - δ) = 2 * δ by ring, smul_eq_mul]
      _ ≤ ∫ x in a - δ..a + δ, g x := this
  rw [hsplit, htel]
  linarith

end intervalIntegral
