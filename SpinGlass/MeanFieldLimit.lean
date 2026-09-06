import SpinGlass.Cascades.GhirlandaGuerra
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Mean-field replica-law limits

Infinite replica law with GG₁ identities on finite-dimensional marginals. Main: `MeanFieldLimit`.
Talagrand Vol. II.
-/

open MeasureTheory ProbabilityTheory

namespace SpinGlass

universe u
variable {β : Type u} [MeasurableSpace β]

/-! ### Finite marginals of an infinite replica law -/

/-- Restrict an infinite replica sequence to its first `k` coordinates. -/
def takeReplicas (k : ℕ) (σs : ℕ → β) : Fin k → β :=
  fun i => σs i

@[simp] lemma takeReplicas_apply (k : ℕ) (σs : ℕ → β) (i : Fin k) :
    takeReplicas (β := β) k σs i = σs i := rfl

/-- The `k`-replica marginal law of a measure on infinite replica sequences. -/
noncomputable def replicaMarginal (μ : Measure (ℕ → β)) (k : ℕ) : Measure (Fin k → β) :=
  μ.map (takeReplicas (β := β) k)

/-! ### Mean-field limit interface -/

/-- Infinite replica law with GG₁ on all finite-dimensional marginals. -/
structure MeanFieldLimit (β : Type u) [MeasurableSpace β] where
  /-- Law of an infinite replica sequence. -/
  μ : Measure (ℕ → β)
  /-- `μ` is a probability measure. -/
  [isProbabilityMeasure_μ : IsProbabilityMeasure μ]
  /-- Overlap kernel. -/
  R : β → β → ℝ
  /-- GG₁ holds for every finite marginal induced by `μ`. -/
  GG1 : ∀ n : ℕ,
    SpinGlass.Cascades.GG1 (β := β) n (replicaMarginal (β := β) μ (n + 1)) R

attribute [instance] MeanFieldLimit.isProbabilityMeasure_μ

namespace MeanFieldLimit

variable (L : MeanFieldLimit (β := β))

/-- The `(n+1)`-replica marginal law associated to `L`. -/
noncomputable abbrev μn (n : ℕ) : Measure (Fin (n + 1) → β) :=
  replicaMarginal (β := β) L.μ (n + 1)

lemma GG1_marginal (n : ℕ) :
    SpinGlass.Cascades.GG1 (β := β) n (L.μn n) L.R := by
  simpa [MeanFieldLimit.μn] using L.GG1 n

end MeanFieldLimit

end SpinGlass
