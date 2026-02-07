import SpinGlass.Lattice.Zd
import GibbsMeasure.Observables.Correlations

/-!
# Diagrammatic quantities on `ℤ^d` boxes

This file specializes the model-agnostic correlation/diagram layer in
`GibbsMeasure.Observables.Correlations` to the `ℤ^d` box geometry from `SpinGlass.Lattice.Zd`.

It provides the “paper-facing” quantities
- `bubbleRaw (L : ℕ)`, `bubble (L : ℕ)`, `chi (L : ℕ)`
where the underlying region is `box d L` and the basepoint is the origin `0`.
-/

open scoped BigOperators

open MeasureTheory ProbabilityTheory

namespace SpinGlass

namespace Lattice

namespace Zd

namespace BoxDiagrams

variable {d : ℕ} {S : Type*} [MeasurableSpace S]
variable (spin : S → ℝ)
variable (μ : Measure (ZLattice d → S))

/-- Bubble diagram truncated at distance `L`: `∑_{x∈Λ_L} ⟨σ_0 σ_x⟩^2`. -/
noncomputable def bubbleRaw (L : ℕ) : ℝ :=
  GibbsMeasure.Observables.Correlations.Diagrams.bubbleRaw
    (ι := ZLattice d) (spin := spin) (μ := μ) (Λ := box d L) (o := (0 : ZLattice d))

/-- GS-normalized bubble diagram over `Λ_L`, i.e. `bubbleRaw / ⟨σ_0^2⟩`. -/
noncomputable def bubble (L : ℕ) : ℝ :=
  GibbsMeasure.Observables.Correlations.Diagrams.bubble
    (ι := ZLattice d) (spin := spin) (μ := μ) (Λ := box d L) (o := (0 : ZLattice d))

/-- Truncated susceptibility `χ_L := ∑_{x∈Λ_L} ⟨σ_0 σ_x⟩`. -/
noncomputable def chi (L : ℕ) : ℝ :=
  GibbsMeasure.Observables.Correlations.Diagrams.chi
    (ι := ZLattice d) (spin := spin) (μ := μ) (Λ := box d L) (o := (0 : ZLattice d))

/-! ### Core API: bubble diagram on boxes -/

lemma bubbleRaw_nonneg (L : ℕ) : 0 ≤ bubbleRaw (d := d) spin μ L := by
  simpa [bubbleRaw] using
    (GibbsMeasure.Observables.Correlations.Diagrams.bubbleRaw_nonneg
      (ι := ZLattice d) (spin := spin) (μ := μ) (Λ := box d L) (o := (0 : ZLattice d)))

lemma bubbleRaw_mono {L L' : ℕ} (hLL' : L ≤ L') :
    bubbleRaw (d := d) spin μ L ≤ bubbleRaw (d := d) spin μ L' := by
  have hsub : box d L ⊆ box d L' := box_mono (d := d) hLL'
  simpa [bubbleRaw] using
    (GibbsMeasure.Observables.Correlations.Diagrams.bubbleRaw_mono
      (ι := ZLattice d) (spin := spin) (μ := μ) (o := (0 : ZLattice d)) (Λ := box d L)
      (Λ' := box d L') hsub)

lemma bubble_nonneg (L : ℕ)
    (h00 : 0 ≤ GibbsMeasure.Observables.Correlations.twoPoint
      (ι := ZLattice d) spin μ (0 : ZLattice d) (0 : ZLattice d)) :
    0 ≤ bubble (d := d) spin μ L := by
  simpa [bubble] using
    (GibbsMeasure.Observables.Correlations.Diagrams.bubble_nonneg
      (ι := ZLattice d) (spin := spin) (μ := μ) (Λ := box d L) (o := (0 : ZLattice d)) h00)

lemma bubble_mono {L L' : ℕ} (hLL' : L ≤ L')
    (h00 : 0 ≤ GibbsMeasure.Observables.Correlations.twoPoint
      (ι := ZLattice d) spin μ (0 : ZLattice d) (0 : ZLattice d)) :
    bubble (d := d) spin μ L ≤ bubble (d := d) spin μ L' := by
  have hsub : box d L ⊆ box d L' := box_mono (d := d) hLL'
  simpa [bubble] using
    (GibbsMeasure.Observables.Correlations.Diagrams.bubble_mono
      (ι := ZLattice d) (spin := spin) (μ := μ) (o := (0 : ZLattice d)) (Λ := box d L)
      (Λ' := box d L') hsub h00)

@[simp]
lemma bubbleRaw_zero (d : ℕ) (spin : S → ℝ) (μ : Measure (ZLattice d → S)) :
    bubbleRaw (d := d) spin μ 0 =
      (GibbsMeasure.Observables.Correlations.twoPoint
        (ι := ZLattice d) spin μ (0 : ZLattice d) (0 : ZLattice d)) ^ (2 : ℕ) := by
  simp [bubbleRaw, GibbsMeasure.Observables.Correlations.Diagrams.bubbleRaw, box_zero]

@[simp]
lemma bubble_zero (d : ℕ) (spin : S → ℝ) (μ : Measure (ZLattice d → S)) :
    bubble (d := d) spin μ 0 =
      GibbsMeasure.Observables.Correlations.twoPoint
        (ι := ZLattice d) spin μ (0 : ZLattice d) (0 : ZLattice d) := by
  by_cases h00 :
      GibbsMeasure.Observables.Correlations.twoPoint
        (ι := ZLattice d) spin μ (0 : ZLattice d) (0 : ZLattice d) = 0
  · simp [bubble, GibbsMeasure.Observables.Correlations.Diagrams.bubble,
      GibbsMeasure.Observables.Correlations.Diagrams.bubbleRaw, box_zero, h00]
  · simp [bubble, GibbsMeasure.Observables.Correlations.Diagrams.bubble,
      GibbsMeasure.Observables.Correlations.Diagrams.bubbleRaw, box_zero, pow_two, h00]

lemma bubble_eq_bubbleRaw_of_twoPoint00_eq_one
    {d : ℕ} {S : Type*} [MeasurableSpace S] {spin : S → ℝ} {μ : Measure (ZLattice d → S)}
    (h00 :
      GibbsMeasure.Observables.Correlations.twoPoint
        (ι := ZLattice d) spin μ (0 : ZLattice d) (0 : ZLattice d) = 1)
    (L : ℕ) : bubble (d := d) spin μ L = bubbleRaw (d := d) spin μ L := by
  simpa [bubble, bubbleRaw] using
    (GibbsMeasure.Observables.Correlations.Diagrams.bubble_eq_bubbleRaw_of_twoPoint00_eq_one
      (ι := ZLattice d) (spin := spin) (μ := μ) (Λ := box d L) (o := (0 : ZLattice d)) h00)

/-! ### Core API: susceptibility on boxes -/

@[simp]
lemma chi_zero (d : ℕ) (spin : S → ℝ) (μ : Measure (ZLattice d → S)) :
    chi (d := d) spin μ 0 =
      GibbsMeasure.Observables.Correlations.twoPoint
        (ι := ZLattice d) spin μ (0 : ZLattice d) (0 : ZLattice d) := by
  simp [chi, GibbsMeasure.Observables.Correlations.Diagrams.chi, box_zero]

lemma chi_mono {d : ℕ} {S : Type*} [MeasurableSpace S] (spin : S → ℝ)
    (μ : Measure (ZLattice d → S)) {L L' : ℕ} (hLL' : L ≤ L')
    (hnonneg :
      ∀ x : ZLattice d,
        0 ≤ GibbsMeasure.Observables.Correlations.twoPoint
          (ι := ZLattice d) spin μ (0 : ZLattice d) x) :
    chi (d := d) spin μ L ≤ chi (d := d) spin μ L' := by
  have hsub : box d L ⊆ box d L' := box_mono (d := d) hLL'
  simpa [chi] using
    (GibbsMeasure.Observables.Correlations.Diagrams.chi_mono
      (ι := ZLattice d) (spin := spin) (μ := μ) (o := (0 : ZLattice d)) (Λ := box d L)
      (Λ' := box d L') hsub hnonneg)

end BoxDiagrams

end Zd

end Lattice

end SpinGlass
