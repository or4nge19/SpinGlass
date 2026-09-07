/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import GibbsMeasure.Specification.DeFinetti
import Common.Mathlib.MeasureTheory.Measure.InvariantWeakLimit
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Metrizable.Urysohn

/-!
# Exchangeability in the limit, and de Finetti for limit laws

The exchangeability / Hewitt–Savage / de Finetti layer of the `GibbsMeasure` package
(`MeasureTheory.GibbsMeasure.IsExchangeable`,
`MeasureTheory.GibbsMeasure.existsUnique_mixing_of_isExchangeable`) is stated for a *fixed*
measure. Every use of it in spin-glass theory is for a measure obtained as a **limit**: Talagrand's
asymptotic Gibbs measure (Vol. II, Ch. 12–15; Panchenko) is a limit point of the laws of the
i.i.d. replica arrays of the finite-volume Gibbs measures, and the whole point is that
exchangeability survives that limit so that de Finetti applies to it.

This file supplies exactly that step, at the general level: exchangeability is a closed condition
in the topology of convergence in distribution, because permuting coordinates is continuous
(`Common.Mathlib.MeasureTheory.Measure.InvariantWeakLimit`). On a compact state space it then
combines with Prokhorov's compactness of the space of probability measures to give limit points
unconditionally.

## Main statements

- `MeasureTheory.GibbsMeasure.continuous_permute`: coordinate permutation is continuous.
- `MeasureTheory.GibbsMeasure.isExchangeable_bind`: a **mixture** of exchangeable laws is
  exchangeable.
- `MeasureTheory.GibbsMeasure.isExchangeable_of_tendsto`: **exchangeability passes to weak
  limits**.
- `MeasureTheory.GibbsMeasure.existsUnique_mixing_of_tendsto`: de Finetti applied to a limit law.
- `MeasureTheory.GibbsMeasure.exists_subseq_tendsto_mixing`: on a compact standard Borel state
  space, **every** sequence of exchangeable laws has a subsequence converging to a unique de
  Finetti mixture.
-/

open Filter Topology MeasureTheory

namespace MeasureTheory.GibbsMeasure

section Continuity

variable {E : Type*} [TopologicalSpace E]

/-- Permuting the coordinates of a sequence is continuous. -/
theorem continuous_permute (σ : Equiv.Perm ℕ) : Continuous (permute (E := E) σ) :=
  continuous_pi fun i => continuous_apply (σ i)

end Continuity

section Mixture

variable {E : Type*} [MeasurableSpace E]

/-- **A mixture of exchangeable laws is exchangeable.** Pushing the mixture forward is the mixture
of the pushforwards (`Measure.map_bind`), and each of those is unchanged. This is what makes the
*disorder-averaged* replica law of a random Hamiltonian exchangeable, so that de Finetti's mixing
measure is the law of the random asymptotic Gibbs measure. -/
theorem isExchangeable_bind {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : Ω → Measure (ℕ → E)} (hκ : Measurable κ) (hex : ∀ ω, IsExchangeable (κ ω)) :
    IsExchangeable (P.bind κ) := by
  intro σ hσ
  have h : (fun ω => (κ ω).map (permute σ)) = κ := funext fun ω => hex ω σ hσ
  rw [Measure.map_bind hκ (measurable_permute σ), h]

end Mixture

section Limits

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [TopologicalSpace.MetrizableSpace E]

/-- **Exchangeability passes to weak limits.** A limit, in the topology of convergence in
distribution, of exchangeable probability measures on `E^ℕ` is exchangeable. -/
theorem isExchangeable_of_tendsto {ι : Type*} {L : Filter ι} [L.NeBot]
    {μs : ι → ProbabilityMeasure (ℕ → E)} {μ : ProbabilityMeasure (ℕ → E)}
    (hlim : Tendsto μs L (𝓝 μ))
    (hex : ∀ᶠ i in L, IsExchangeable (μs i : Measure (ℕ → E))) :
    IsExchangeable (μ : Measure (ℕ → E)) := fun σ hσ =>
  Measure.map_eq_of_tendsto_probabilityMeasure hlim (continuous_permute σ)
    (hex.mono fun _ hi => hi σ hσ)

variable [StandardBorelSpace E]

/-- **De Finetti's theorem for a limit law.** A limit of exchangeable probability measures on `E^ℕ`
is the mixture `∫ λ^ℕ m(dλ)` of i.i.d. product measures under a *unique* probability measure `m` on
`𝒫(E)`. Georgii (7.31) applied along a weak limit. -/
theorem existsUnique_mixing_of_tendsto {ι : Type*} {L : Filter ι} [L.NeBot]
    {μs : ι → ProbabilityMeasure (ℕ → E)} {μ : ProbabilityMeasure (ℕ → E)}
    (hlim : Tendsto μs L (𝓝 μ))
    (hex : ∀ᶠ i in L, IsExchangeable (μs i : Measure (ℕ → E))) :
    ∃! m : Measure (Measure E), IsProbabilityMeasure m
      ∧ m {lam : Measure E | IsProbabilityMeasure lam}ᶜ = 0
      ∧ m.bind (fun lam => Measure.infinitePi fun _ : ℕ => lam) = (μ : Measure (ℕ → E)) := by
  have : IsProbabilityMeasure (μ : Measure (ℕ → E)) := μ.2
  exact existsUnique_mixing_of_isExchangeable (isExchangeable_of_tendsto hlim hex)

/-- **Every sequence of exchangeable laws on a compact state space has a de Finetti limit.**
Prokhorov compactness supplies the limit point, `isExchangeable_of_tendsto` keeps it exchangeable,
and de Finetti represents it. Nothing is assumed about the sequence beyond exchangeability. -/
theorem exists_subseq_tendsto_mixing [CompactSpace E]
    (μs : ℕ → ProbabilityMeasure (ℕ → E))
    (hex : ∀ n, IsExchangeable (μs n : Measure (ℕ → E))) :
    ∃ (μ : ProbabilityMeasure (ℕ → E)) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun k => μs (φ k)) atTop (𝓝 μ) ∧
      ∃! m : Measure (Measure E), IsProbabilityMeasure m
        ∧ m {lam : Measure E | IsProbabilityMeasure lam}ᶜ = 0
        ∧ m.bind (fun lam => Measure.infinitePi fun _ : ℕ => lam) = (μ : Measure (ℕ → E)) := by
  obtain ⟨μ, φ, hφ, hlim⟩ := SeqCompactSpace.tendsto_subseq μs
  refine ⟨μ, φ, hφ, hlim, existsUnique_mixing_of_tendsto hlim ?_⟩
  exact Filter.Eventually.of_forall fun k => hex (φ k)

end Limits

end MeasureTheory.GibbsMeasure
