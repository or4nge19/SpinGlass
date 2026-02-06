import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import SpinGlass.Defs
import SpinGlass.FiniteGibbs.GibbsMeasure
import SpinGlass.SKModel

/-!
## Talagrand ↔ Georgii bridge (finite `N`)

Talagrand (Vol. I/II) works with a finite-volume Gibbs distribution on `Config N` given by the
weights `gibbs_pmf`.

For later “Vol. II structure” work (bracket notation, replicas, conditional kernels), it is
convenient to bundle these weights as an actual `ProbabilityMeasure` on configurations.

This file provides that in a way that is purely finite-volume and does **not** introduce
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
  FiniteGibbs.gibbsWeightNNReal (α := Config N) (H := H) σ

/-- The finite-volume Gibbs measure (as a `Measure`) with atoms weighted by `gibbs_pmf`. -/
noncomputable def gibbsMeasure (H : EnergySpace N) : Measure (Config N) :=
  FiniteGibbs.gibbsMeasure (α := Config N) H

lemma lintegral_gibbsMeasure
    (H : EnergySpace N) (f : Config N → ℝ≥0∞) : (∫⁻ σ, f σ ∂gibbsMeasure (N := N) H) = ∑ σ :
      Config N, (gibbsWeightNNReal (N := N) H σ : ℝ≥0∞) * f σ := by
  classical
  simp [gibbsMeasure, gibbsWeightNNReal, FiniteGibbs.lintegral_gibbsMeasure]

lemma gibbsMeasure_univ (H : EnergySpace N) : gibbsMeasure (N := N) H Set.univ = 1 := by
  simpa [gibbsMeasure, FiniteGibbs.gibbsMeasure] using (FiniteGibbs.gibbsMeasure_univ (α := Config N) (H := H))

lemma integral_gibbsMeasure_eq_gibbs_average (H : EnergySpace N) (f : Config N → ℝ) :
    (∫ σ, f σ ∂gibbsMeasure (N := N) H) = gibbs_average (N := N) H f := by
  -- Delegate to the generic finite-volume Gibbs measure lemma.
  simpa [gibbs_average, gibbsMeasure, FiniteGibbs.gibbsMeasure,
    gibbs_pmf, FiniteGibbs.gibbs_pmf, Z, FiniteGibbs.Z] using
    (FiniteGibbs.integral_gibbsMeasure (α := Config N) (H := H) (f := f))

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
