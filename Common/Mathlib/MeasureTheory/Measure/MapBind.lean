/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Pushing a mixture forward

`Measure.bind` and `Measure.map` are the two operations of the Giry monad that every mixture
argument uses together, and Mathlib records `bind_bind`, `bind_dirac`, `dirac_bind` and
`bind_dirac_eq_map` but not the exchange law between them. It says that pushing a mixture forward
is the mixture of the pushforwards, and it is what makes an invariance property of a kernel pass to
the mixture.

## Main statements

- `MeasureTheory.Measure.map_bind`: `(m.bind f).map g = m.bind (fun a ↦ (f a).map g)`.
- `MeasureTheory.Measure.isProbabilityMeasure_bind`: a mixture of probability measures under a
  probability measure is a probability measure.
-/

open MeasureTheory

namespace MeasureTheory.Measure

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- **Pushing a mixture forward is the mixture of the pushforwards.** -/
theorem map_bind {m : Measure α} {f : α → Measure β} (hf : Measurable f)
    {g : β → γ} (hg : Measurable g) :
    (m.bind f).map g = m.bind fun a => (f a).map g := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hg hs, Measure.bind_apply (hg hs) hf.aemeasurable,
    Measure.bind_apply hs ((Measure.measurable_map g hg).comp hf).aemeasurable]
  exact lintegral_congr fun a => (Measure.map_apply hg hs).symm

/-- A mixture of probability measures under a probability measure is a probability measure. -/
theorem isProbabilityMeasure_bind {m : Measure α} [IsProbabilityMeasure m] {f : α → Measure β}
    (hf : Measurable f) (hprob : ∀ a, IsProbabilityMeasure (f a)) :
    IsProbabilityMeasure (m.bind f) := by
  constructor
  rw [Measure.bind_apply MeasurableSet.univ hf.aemeasurable]
  simp [(hprob _).measure_univ]

end MeasureTheory.Measure
