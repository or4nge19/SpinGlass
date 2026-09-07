/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Invariance under a continuous map is a closed condition

Mathlib knows that pushing forward along a continuous map is continuous for the topology of
convergence in distribution (`MeasureTheory.ProbabilityMeasure.continuous_map`). What is missing is
the consequence that every limit argument in ergodic theory and in statistical mechanics rests on:
the set of probability measures **invariant** under a continuous map is *closed*, so a weak limit
of invariant measures is invariant.

This is the mechanism behind Krylov–Bogolyubov, behind the construction of infinite-volume Gibbs
states as limits of finite-volume ones, and — the use here — behind the fact that a limit of
exchangeable laws is exchangeable, which is what makes de Finetti's theorem applicable to the
asymptotic replica law of a spin glass.

## Main statements

- `MeasureTheory.ProbabilityMeasure.isClosed_setOf_map_eq`: the invariance locus of a continuous
  self-map is closed in the topology of convergence in distribution.
- `MeasureTheory.ProbabilityMeasure.map_eq_of_tendsto`: hence a weak limit of invariant probability
  measures is invariant.
- `MeasureTheory.Measure.map_eq_of_tendsto_probabilityMeasure`: the same, stated for the underlying
  measures, which is the form a `Measure`-valued invariance predicate consumes.
-/

open Filter Topology

namespace MeasureTheory

namespace ProbabilityMeasure

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [HasOuterApproxClosed Ω]
  [BorelSpace Ω]

/-- **Invariance under a continuous map is a closed condition.** The set of probability measures
fixed by the pushforward along a continuous self-map is closed in the topology of convergence in
distribution: it is the equaliser of two continuous maps into a Hausdorff space. -/
theorem isClosed_setOf_map_eq {g : Ω → Ω} (hg : Continuous g) :
    IsClosed {μ : ProbabilityMeasure Ω | μ.map hg.measurable.aemeasurable = μ} :=
  isClosed_eq (continuous_map hg) continuous_id

/-- **A weak limit of measures invariant under a continuous map is invariant.** -/
theorem map_eq_of_tendsto {ι : Type*} {L : Filter ι} [L.NeBot]
    {μs : ι → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
    (hlim : Tendsto μs L (𝓝 μ)) {g : Ω → Ω} (hg : Continuous g)
    (hinv : ∀ᶠ i in L, (μs i).map hg.measurable.aemeasurable = μs i) :
    μ.map hg.measurable.aemeasurable = μ :=
  (isClosed_setOf_map_eq hg).mem_of_tendsto hlim hinv

end ProbabilityMeasure

/-- **A weak limit of measures invariant under a continuous map is invariant**, stated for the
underlying measures. -/
theorem Measure.map_eq_of_tendsto_probabilityMeasure {Ω : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Ω] [HasOuterApproxClosed Ω] [BorelSpace Ω]
    {ι : Type*} {L : Filter ι} [L.NeBot]
    {μs : ι → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
    (hlim : Tendsto μs L (𝓝 μ)) {g : Ω → Ω} (hg : Continuous g)
    (hinv : ∀ᶠ i in L, (μs i : Measure Ω).map g = (μs i : Measure Ω)) :
    (μ : Measure Ω).map g = (μ : Measure Ω) := by
  have hinv' : ∀ᶠ i in L, (μs i).map hg.measurable.aemeasurable = μs i := by
    filter_upwards [hinv] with i hi
    exact Subtype.ext (by simpa using hi)
  simpa using congrArg (fun ν : ProbabilityMeasure Ω => (ν : Measure Ω))
    (ProbabilityMeasure.map_eq_of_tendsto hlim hg hinv')

end MeasureTheory
