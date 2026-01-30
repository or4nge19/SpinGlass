import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import SpinGlass.Defs
import SpinGlass.SKModel

/-!
## Talagrand ↔ Georgii bridge (finite `N`)

Talagrand (Vol. I/II) works with a finite-volume Gibbs distribution on `Config N` given by the
weights `gibbs_pmf`.

For later “Vol. II structure” work (bracket notation, replicas, conditional kernels), it is
convenient to package these weights as an actual `ProbabilityMeasure` on configurations.

This file provides that packaging in a way that is purely finite-volume and does **not** introduce
any additional (topological) hypotheses.
-/

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ENNReal NNReal

namespace SpinGlass

variable {N : ℕ}

section FiniteVolume

variable (N)

/-- The Gibbs weight as a nonnegative real. -/
noncomputable def gibbsWeightNNReal (H : EnergySpace N) (σ : Config N) : ℝ≥0 :=
  ⟨gibbs_pmf N H σ, gibbs_pmf_nonneg (N := N) (H := H) σ⟩

/-- The finite-volume Gibbs measure (as a `Measure`) with atoms weighted by `gibbs_pmf`. -/
noncomputable def gibbsMeasure (H : EnergySpace N) : Measure (Config N) :=
  (Finset.univ : Finset (Config N)).sum fun σ =>
    ((gibbsWeightNNReal (N := N) H σ : ℝ≥0∞) • Measure.dirac σ)

lemma gibbsMeasure_univ (H : EnergySpace N) : gibbsMeasure (N := N) H Set.univ = 1 := by
  have h_univ :
      gibbsMeasure (N := N) H Set.univ
        =
        ∑ σ : Config N, (gibbsWeightNNReal (N := N) H σ : ℝ≥0∞) := by
    simp [gibbsMeasure, gibbsWeightNNReal]
  have hsumNNReal :
      (∑ σ : Config N, gibbsWeightNNReal (N := N) H σ) = (1 : ℝ≥0) := by
    apply NNReal.coe_injective
    simpa [gibbsWeightNNReal] using (sum_gibbs_pmf (N := N) (H := H))
  have hsumENNReal :
      (∑ σ : Config N, (gibbsWeightNNReal (N := N) H σ : ℝ≥0∞)) = (1 : ℝ≥0∞) := by
    simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) hsumNNReal
  simpa [h_univ] using hsumENNReal

instance (H : EnergySpace N) : IsProbabilityMeasure (gibbsMeasure (N := N) H) :=
  ⟨gibbsMeasure_univ (N := N) (H := H)⟩

end FiniteVolume

/-! ### Bracket notation -/

section Bracket

variable {N : ℕ}

/-- Talagrand's bracket notation: `⟪f⟫_H` is the Gibbs average of `f` under energy `H`. -/
notation3 (prettyPrint := false) "⟪" f "⟫_" H:70 =>
  gibbs_average H f

end Bracket

end SpinGlass
