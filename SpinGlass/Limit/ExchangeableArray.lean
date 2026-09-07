/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Limit.Exchangeability

/-!
# Jointly exchangeable arrays

De Finetti's theorem is about exchangeable *sequences*; the objects of Talagrand Vol. II Ch. 12–15
and of Panchenko's book are exchangeable **arrays** — the overlap array `R_{l,l'}` of a system of
replicas, invariant under the *diagonal* action of a finitary permutation of the replica index.
That invariance is the hypothesis of the Aldous–Hoover representation and of the Dovbysh–Sudakov
theorem, and it is the shape in which a spin-glass limit is taken.

This file introduces the notion and proves everything that is upstream of Aldous–Hoover:

* it is produced from an exchangeable sequence by *any* two-variable measurable function
  (`isJointlyExchangeable_map_of_isExchangeable`) — this is how the overlap array acquires it;
* it is stable under mixtures and under weak limits, and on a compact state space Prokhorov then
  gives limit points unconditionally.

## Main statements

- `MeasureTheory.GibbsMeasure.permuteArray`, `MeasureTheory.GibbsMeasure.IsJointlyExchangeable`.
- `MeasureTheory.GibbsMeasure.isJointlyExchangeable_map_of_isExchangeable`: the array of pairwise
  values of an exchangeable sequence is jointly exchangeable.
- `MeasureTheory.GibbsMeasure.isJointlyExchangeable_bind`: mixtures.
- `MeasureTheory.GibbsMeasure.isJointlyExchangeable_of_tendsto`: weak limits.
- `MeasureTheory.GibbsMeasure.exists_subseq_tendsto_jointlyExchangeable`: on a compact metrizable
  state space every sequence of jointly exchangeable array laws has a jointly exchangeable limit
  point.
-/

open Filter Topology MeasureTheory

namespace MeasureTheory.GibbsMeasure

/-! ### The diagonal action on arrays -/

/-- The **diagonal action** of a permutation of `ℕ` on a doubly indexed array. -/
def permuteArray {F : Type*} (σ : Equiv.Perm ℕ) (R : ℕ → ℕ → F) : ℕ → ℕ → F :=
  fun l l' => R (σ l) (σ l')

@[simp] lemma permuteArray_apply {F : Type*} (σ : Equiv.Perm ℕ) (R : ℕ → ℕ → F) (l l' : ℕ) :
    permuteArray σ R l l' = R (σ l) (σ l') := rfl

lemma measurable_permuteArray {F : Type*} [MeasurableSpace F] (σ : Equiv.Perm ℕ) :
    Measurable (permuteArray (F := F) σ) :=
  measurable_pi_lambda _ fun l =>
    measurable_pi_lambda _ fun l' => (measurable_pi_apply (σ l')).comp (measurable_pi_apply (σ l))

lemma continuous_permuteArray {F : Type*} [TopologicalSpace F] (σ : Equiv.Perm ℕ) :
    Continuous (permuteArray (F := F) σ) :=
  continuous_pi fun l =>
    continuous_pi fun l' => (continuous_apply (σ l')).comp (continuous_apply (σ l))

/-- **Joint (weak) exchangeability of an array**: invariance under the diagonal action of every
finitary permutation of the index. This is the hypothesis of the Aldous–Hoover representation and
of the Dovbysh–Sudakov theorem. -/
def IsJointlyExchangeable {F : Type*} [MeasurableSpace F] (μ : Measure (ℕ → ℕ → F)) : Prop :=
  ∀ σ ∈ finitaryPerm, μ.map (permuteArray σ) = μ

/-! ### Arrays of pairwise values -/

section Map

variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]

/-- The array of pairwise values `(l, l') ↦ f (ω l) (ω l')` of a sequence. -/
def pairArray (f : E → E → F) (ω : ℕ → E) : ℕ → ℕ → F := fun l l' => f (ω l) (ω l')

omit [MeasurableSpace E] [MeasurableSpace F] in
@[simp] lemma pairArray_apply (f : E → E → F) (ω : ℕ → E) (l l' : ℕ) :
    pairArray f ω l l' = f (ω l) (ω l') := rfl

lemma measurable_pairArray {f : E → E → F} (hf : Measurable fun p : E × E => f p.1 p.2) :
    Measurable (pairArray f) := by
  refine measurable_pi_lambda _ fun l => measurable_pi_lambda _ fun l' => ?_
  change Measurable fun ω : ℕ → E => f (ω l) (ω l')
  fun_prop

omit [MeasurableSpace E] [MeasurableSpace F] in
lemma permuteArray_comp_pairArray (f : E → E → F) (σ : Equiv.Perm ℕ) :
    permuteArray σ ∘ pairArray f = pairArray f ∘ permute σ := rfl

/-- **The array of pairwise values of an exchangeable sequence is jointly exchangeable.** This is
how the overlap array of a system of replicas acquires the hypothesis of Aldous–Hoover and
Dovbysh–Sudakov: it is the array of pairwise overlaps of an exchangeable sequence of replicas. -/
theorem isJointlyExchangeable_map_of_isExchangeable {μ : Measure (ℕ → E)}
    (hμ : IsExchangeable μ) {f : E → E → F} (hf : Measurable fun p : E × E => f p.1 p.2) :
    IsJointlyExchangeable (μ.map (pairArray f)) := by
  intro σ hσ
  rw [Measure.map_map (measurable_permuteArray σ) (measurable_pairArray hf),
    permuteArray_comp_pairArray f σ,
    ← Measure.map_map (measurable_pairArray hf) (measurable_permute σ), hμ σ hσ]

end Map

/-! ### Mixtures -/

/-- A mixture of jointly exchangeable array laws is jointly exchangeable. -/
theorem isJointlyExchangeable_bind {F : Type*} [MeasurableSpace F] {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {κ : Ω → Measure (ℕ → ℕ → F)} (hκ : Measurable κ)
    (hex : ∀ ω, IsJointlyExchangeable (κ ω)) : IsJointlyExchangeable (P.bind κ) := by
  intro σ hσ
  have h : (fun ω => (κ ω).map (permuteArray σ)) = κ := funext fun ω => hex ω σ hσ
  rw [Measure.map_bind hκ (measurable_permuteArray σ), h]

/-! ### Limits -/

section Limits

variable {F : Type*} [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F] [TopologicalSpace.MetrizableSpace F]

/-- **Joint exchangeability passes to weak limits.** -/
theorem isJointlyExchangeable_of_tendsto {ι : Type*} {L : Filter ι} [L.NeBot]
    {μs : ι → ProbabilityMeasure (ℕ → ℕ → F)} {μ : ProbabilityMeasure (ℕ → ℕ → F)}
    (hlim : Tendsto μs L (𝓝 μ))
    (hex : ∀ᶠ i in L, IsJointlyExchangeable (μs i : Measure (ℕ → ℕ → F))) :
    IsJointlyExchangeable (μ : Measure (ℕ → ℕ → F)) := fun σ hσ =>
  Measure.map_eq_of_tendsto_probabilityMeasure hlim (continuous_permuteArray σ)
    (hex.mono fun _ hi => hi σ hσ)

/-- **Every sequence of jointly exchangeable array laws on a compact state space has a jointly
exchangeable limit point.** Prokhorov supplies the limit point; joint exchangeability survives. -/
theorem exists_subseq_tendsto_jointlyExchangeable [CompactSpace F]
    (μs : ℕ → ProbabilityMeasure (ℕ → ℕ → F))
    (hex : ∀ n, IsJointlyExchangeable (μs n : Measure (ℕ → ℕ → F))) :
    ∃ (μ : ProbabilityMeasure (ℕ → ℕ → F)) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun k => μs (φ k)) atTop (𝓝 μ) ∧
      IsJointlyExchangeable (μ : Measure (ℕ → ℕ → F)) := by
  obtain ⟨μ, φ, hφ, hlim⟩ := SeqCompactSpace.tendsto_subseq μs
  exact ⟨μ, φ, hφ, hlim,
    isJointlyExchangeable_of_tendsto hlim (Filter.Eventually.of_forall fun k => hex (φ k))⟩

end Limits

end MeasureTheory.GibbsMeasure
