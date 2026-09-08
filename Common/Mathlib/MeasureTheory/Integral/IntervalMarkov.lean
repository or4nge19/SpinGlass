/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Markov's inequality on a set, and on an interval

Mathlib's `MeasureTheory.mul_meas_ge_le_integral_of_nonneg` is Markov's inequality for the whole
space. Applying it to a restricted measure is the ubiquitous "the level set inside `s` is small"
statement, but the restriction bookkeeping (`Measure.restrict_apply`, `measureReal_def`) has to be
redone every time. This file does it once, and specialises to interval integrals — the form used
whenever a bound on `∫_a^b f` is upgraded from "at some point of `[a,b]`" (the mean value theorem)
to "outside a set of small measure".

## Main statements

- `MeasureTheory.measureReal_setOf_le_inter_le_of_integrableOn`: `μ({f ≥ t} ∩ s) ≤ (∫_s f)/t`.
- `intervalIntegral.measureReal_setOf_le_le`: `volume({f ≥ t} ∩ Ioc a b) ≤ (∫_a^b f)/t`.
-/

open MeasureTheory Set

namespace MeasureTheory

/-- **Markov's inequality on a set.** For a nonnegative function integrable on `s`, the part of `s`
on which `f ≥ t` has measure at most `(∫_s f)/t`. -/
theorem measureReal_setOf_le_inter_le_of_integrableOn {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} {f : α → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hfi : IntegrableOn f s μ) {t : ℝ} (ht : 0 < t) :
    μ.real ({x | t ≤ f x} ∩ s) ≤ (∫ x in s, f x ∂μ) / t := by
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := μ.restrict s) (f := f)
    (Filter.Eventually.of_forall hf0) hfi t
  rw [measureReal_def, Measure.restrict_apply (measurableSet_le measurable_const hf),
    ← measureReal_def] at hmk
  rw [le_div_iff₀ ht]
  linarith

end MeasureTheory

namespace intervalIntegral

/-- **Markov's inequality for an interval integral.** A bound on `∫_a^b f` for a nonnegative `f`
bounds the measure of the set where `f` is large: `volume({f ≥ t} ∩ Ioc a b) ≤ (∫_a^b f)/t`. This
is the quantitative strengthening of "there is a point of `[a,b]` where `f` is small". -/
theorem measureReal_setOf_le_le {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {a b : ℝ} (hab : a ≤ b) (hfi : IntervalIntegrable f MeasureTheory.volume a b)
    {t : ℝ} (ht : 0 < t) :
    MeasureTheory.volume.real ({x : ℝ | t ≤ f x} ∩ Set.Ioc a b) ≤ (∫ x in a..b, f x) / t := by
  rw [intervalIntegral.integral_of_le hab]
  exact MeasureTheory.measureReal_setOf_le_inter_le_of_integrableOn hf hf0
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hfi) ht

/-- **Markov's inequality for an interval integral, continuous case.** -/
theorem measureReal_setOf_le_le_of_continuous {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) {a b : ℝ} (hab : a ≤ b) {t : ℝ} (ht : 0 < t) :
    MeasureTheory.volume.real ({x : ℝ | t ≤ f x} ∩ Set.Ioc a b) ≤ (∫ x in a..b, f x) / t :=
  measureReal_setOf_le_le hf.measurable hf0 hab (hf.intervalIntegrable a b) ht

end intervalIntegral
