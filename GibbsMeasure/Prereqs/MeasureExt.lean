import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.PiSystem

/-!
# Measure ext lemmas for generated σ-algebras

This file packages the most common “π-system + generateFrom + finiteness-on-univ” ext arguments
used in the Gibbs/Specification development.
-/

open Set

namespace MeasureTheory.Measure

variable {α : Type*} {m : MeasurableSpace α}
variable (C : Set (Set α))

/-- A convenient wrapper around `Measure.ext_of_generateFrom_of_iUnion` for the common case
`B n = univ`. -/
lemma ext_of_generateFrom_of_iUnion_univ
    {μ ν : Measure[m] α}
    (hA : m = MeasurableSpace.generateFrom C)
    (hC : IsPiSystem C)
    (huniv : (Set.univ : Set α) ∈ C)
    (hμ_univ : μ Set.univ ≠ ⊤)
    (h : ∀ s ∈ C, μ s = ν s) :
    μ = ν := by
  classical
  let B : ℕ → Set α := fun _ => Set.univ
  have h1B : (⋃ n, B n) = (Set.univ : Set α) := by
    ext x
    simp [B]
  have h2B : ∀ n, B n ∈ C := by
    intro n; simpa [B] using huniv
  have hμB : ∀ n, μ (B n) ≠ ⊤ := by
    intro n; simpa [B] using hμ_univ
  refine ext_of_generateFrom_of_iUnion (μ := μ) (ν := ν)
    (C := C) (B := B) (hA := hA) (hC := hC)
    (h1B := h1B) (h2B := h2B) (hμB := hμB) ?_
  intro s hs
  exact h s hs

/-! ### `ext_of_generate_finite` under probability hypotheses -/

/-- A convenient wrapper around `MeasureTheory.ext_of_generate_finite` when both measures are
probability measures: the `univ`-equality hypothesis becomes `by simp`. -/
lemma ext_of_generate_finite_of_isProbabilityMeasure
    {m0 : MeasurableSpace α} {μ ν : Measure[m0] α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hA : m0 = MeasurableSpace.generateFrom C)
    (hC : IsPiSystem C)
    (hμν : ∀ s ∈ C, μ s = ν s) :
    μ = ν := by
  haveI : IsFiniteMeasure μ := by infer_instance
  exact MeasureTheory.ext_of_generate_finite (m0 := m0) (μ := μ) (ν := ν) C hA hC hμν (by simp)

end MeasureTheory.Measure

