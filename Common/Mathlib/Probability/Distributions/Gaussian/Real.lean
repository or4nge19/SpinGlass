/-
Vendored auxiliary lemmas for Gaussian measures.

This file contains small API additions used by the Cameron–Martin development, extracted from
mathlib4 PR #26291 (Cameron–Martin theorem).
-/

import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ProbabilityTheory

/-- If `X` has Gaussian law `N(μ,v)`, then `X - y` has Gaussian law `N(μ - y, v)`.

This lemma is stated for an arbitrary measure `m` (not necessarily a probability measure). -/
lemma gaussianReal_sub_const' {Ω : Type*} {mΩ : MeasurableSpace Ω} {m : Measure Ω} {X : Ω → ℝ}
    {μ : ℝ} {v : ℝ≥0} (hX : Measure.map X m = gaussianReal μ v) (y : ℝ) :
    Measure.map (fun ω ↦ X ω - y) m = gaussianReal (μ - y) v := by
  have hXm : AEMeasurable X m := aemeasurable_of_map_neZero (by rw [hX]; infer_instance)
  change Measure.map ((fun ω ↦ ω - y) ∘ X) m = gaussianReal (μ - y) v
  rw [← AEMeasurable.map_map_of_aemeasurable (measurable_id'.sub_const _).aemeasurable hXm, hX,
    gaussianReal_map_sub_const y]

end ProbabilityTheory

