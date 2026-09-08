/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Analysis.Convex.GriffithsLemma
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Griffiths' lemma in mean

`ConvexOn.abs_rightDeriv_sub_le` bounds the distance between the derivative of a convex function
`θ` and that of a comparison convex function `p` by the increment of `p`'s one-sided derivatives
across a window plus the sup-distance of `θ` to `p` at the three window points, divided by the
window width. When `θ` is *random* and `p` is its mean, integrating that bound turns a bound on the
fluctuation of the function into a bound on the fluctuation of its derivative:

`𝔼|θ'(x) - p'(x)| ≤ (p'(x+b) - p'(x-b))`
`  + (1/b)(𝔼|θ(x+b)-p(x+b)| + 𝔼|θ(x-b)-p(x-b)| + 𝔼|θ(x)-p(x)|)`.

This is Talagrand, *Mean Field Models for Spin Glasses*, Vol. II, Lemmas 12.1.5–12.1.6 combined,
and it is the step that converts concentration of the free energy into self-averaging of the
energy. It is stated here in full generality: no differentiability, no Gaussianity, only convexity
of each sample path and integrability of the three fluctuations.

## Main statements

- `ConvexOn.integral_abs_rightDeriv_sub_le`.
-/

open Set Filter MeasureTheory

namespace ConvexOn

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {S : Set ℝ} {θ : Ω → ℝ → ℝ} {p : ℝ → ℝ} {x b : ℝ}

/-- **Griffiths' lemma in mean**, Talagrand Vol. II, Lemmas 12.1.5–12.1.6: the mean fluctuation of
the derivative is controlled by the increment of the mean derivative across a window of width `b`
plus `1/b` times the mean fluctuation of the function at the three window points. -/
theorem integral_abs_rightDeriv_sub_le
    (hθ : ∀ w, ConvexOn ℝ S (θ w)) (hp : ConvexOn ℝ S p) (hb : 0 < b)
    (hxi : x ∈ interior S) (hli : x - b ∈ interior S) (hri : x + b ∈ interior S)
    (hI0 : Integrable (fun w => |θ w x - p x|) P)
    (hIm : Integrable (fun w => |θ w (x - b) - p (x - b)|) P)
    (hIp : Integrable (fun w => |θ w (x + b) - p (x + b)|) P) :
    (∫ w, |derivWithin (θ w) (Ioi x) x - derivWithin p (Ioi x) x| ∂P)
      ≤ (derivWithin p (Iio (x + b)) (x + b) - derivWithin p (Ioi (x - b)) (x - b))
        + ((∫ w, |θ w (x + b) - p (x + b)| ∂P) + (∫ w, |θ w (x - b) - p (x - b)| ∂P)
            + ∫ w, |θ w x - p x| ∂P) / b := by
  set D : ℝ := derivWithin p (Iio (x + b)) (x + b) - derivWithin p (Ioi (x - b)) (x - b) with hD
  have hbound : ∀ w, |derivWithin (θ w) (Ioi x) x - derivWithin p (Ioi x) x|
      ≤ D + (|θ w (x + b) - p (x + b)| + |θ w (x - b) - p (x - b)| + |θ w x - p x|) / b :=
    fun w => (hθ w).abs_rightDeriv_sub_le hp hxi hli hri hb
  have hsum : Integrable (fun w =>
      |θ w (x + b) - p (x + b)| + |θ w (x - b) - p (x - b)| + |θ w x - p x|) P :=
    (hIp.add hIm).add hI0
  have hInt : Integrable (fun w => D + (|θ w (x + b) - p (x + b)|
      + |θ w (x - b) - p (x - b)| + |θ w x - p x|) / b) P :=
    (integrable_const D).add (hsum.div_const b)
  refine (integral_mono_of_nonneg (Eventually.of_forall fun w => abs_nonneg _) hInt
    (Eventually.of_forall hbound)).trans_eq ?_
  rw [integral_add (integrable_const D) (hsum.div_const b), integral_const, integral_div]
  have hsplit : (∫ w, (|θ w (x + b) - p (x + b)| + |θ w (x - b) - p (x - b)|
        + |θ w x - p x|) ∂P)
      = (∫ w, |θ w (x + b) - p (x + b)| ∂P) + (∫ w, |θ w (x - b) - p (x - b)| ∂P)
        + ∫ w, |θ w x - p x| ∂P := by
    have hIpm : Integrable
        (fun w => |θ w (x + b) - p (x + b)| + |θ w (x - b) - p (x - b)|) P := hIp.add hIm
    rw [integral_add hIpm hI0, integral_add hIp hIm]
  rw [hsplit]
  simp

/-- **Griffiths' lemma in mean, differentiable form** — Talagrand Vol. II, Lemmas 12.1.5–12.1.6
for the two-sided derivative. -/
theorem integral_abs_deriv_sub_le
    (hθ : ∀ w, ConvexOn ℝ S (θ w)) (hp : ConvexOn ℝ S p) (hb : 0 < b)
    (hxi : x ∈ interior S) (hli : x - b ∈ interior S) (hri : x + b ∈ interior S)
    (hθd : ∀ w, DifferentiableAt ℝ (θ w) x) (hpd : DifferentiableAt ℝ p x)
    (hpl : DifferentiableAt ℝ p (x - b)) (hpr : DifferentiableAt ℝ p (x + b))
    (hI0 : Integrable (fun w => |θ w x - p x|) P)
    (hIm : Integrable (fun w => |θ w (x - b) - p (x - b)|) P)
    (hIp : Integrable (fun w => |θ w (x + b) - p (x + b)|) P) :
    (∫ w, |deriv (θ w) x - deriv p x| ∂P)
      ≤ (deriv p (x + b) - deriv p (x - b))
        + ((∫ w, |θ w (x + b) - p (x + b)| ∂P) + (∫ w, |θ w (x - b) - p (x - b)| ∂P)
            + ∫ w, |θ w x - p x| ∂P) / b := by
  set D : ℝ := deriv p (x + b) - deriv p (x - b) with hD
  have hbound : ∀ w, |deriv (θ w) x - deriv p x|
      ≤ D + (|θ w (x + b) - p (x + b)| + |θ w (x - b) - p (x - b)| + |θ w x - p x|) / b :=
    fun w => (hθ w).abs_deriv_sub_le hp hxi hli hri hb (hθd w).hasDerivAt hpd.hasDerivAt
      hpl.hasDerivAt hpr.hasDerivAt
  have hsum : Integrable (fun w =>
      |θ w (x + b) - p (x + b)| + |θ w (x - b) - p (x - b)| + |θ w x - p x|) P :=
    (hIp.add hIm).add hI0
  have hInt : Integrable (fun w => D + (|θ w (x + b) - p (x + b)|
      + |θ w (x - b) - p (x - b)| + |θ w x - p x|) / b) P :=
    (integrable_const D).add (hsum.div_const b)
  refine (integral_mono_of_nonneg (Eventually.of_forall fun w => abs_nonneg _) hInt
    (Eventually.of_forall hbound)).trans_eq ?_
  rw [integral_add (integrable_const D) (hsum.div_const b), integral_const, integral_div]
  have hsplit : (∫ w, (|θ w (x + b) - p (x + b)| + |θ w (x - b) - p (x - b)|
        + |θ w x - p x|) ∂P)
      = (∫ w, |θ w (x + b) - p (x + b)| ∂P) + (∫ w, |θ w (x - b) - p (x - b)| ∂P)
        + ∫ w, |θ w x - p x| ∂P := by
    have hIpm : Integrable
        (fun w => |θ w (x + b) - p (x + b)| + |θ w (x - b) - p (x - b)|) P := hIp.add hIm
    rw [integral_add hIpm hI0, integral_add hIp hIm]
  rw [hsplit]
  simp

end ConvexOn
