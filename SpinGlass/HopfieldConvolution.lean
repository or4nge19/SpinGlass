import SpinGlass.Hopfield
import SpinGlass.GibbsBridge

/-!
# Hopfield: overlap pushforward and Gaussian convolution (Talagrand §4.2)

This file sets up the **measure-level objects** behind Talagrand’s Lemma 4.2.1:

- `G'`: the image of the Gibbs measure under `σ ↦ m(σ)` (Hopfield overlap vector).
- `Ḡ = G' * γ`: the convolution of `G'` with a (centered) Gaussian `γ` on `ℝ^M`.

We implement this in a Mathlib-idiomatic way using a pushforward of a product measure, so that
later computations reduce to `lintegral_map` and `lintegral_prod`.

At this stage we keep the Gaussian `γ` abstract: any measure on `Fin M → ℝ` can be used. The
specialization to Talagrand’s Gaussian (variance \(1/(N\beta)\) per coordinate) is done in the
next step when deriving the explicit density.
-/

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ENNReal NNReal

namespace SpinGlass

variable {N M : ℕ}

/-! ## The pushforward `G'` -/

/-- The image of a Gibbs measure under the Hopfield overlap vector map `σ ↦ m(σ)`. -/
noncomputable def hopfieldOverlapImageMeasure
    (Ξ : Patterns N M) (H : EnergySpace N) : Measure (Fin M → ℝ) :=
  (gibbsMeasure (N := N) H).map (hopfieldOverlapVec (N := N) (M := M) Ξ)

/-! ## Convolution as a pushforward of a product measure -/

/-- Translate a measure `γ` on `Fin M → ℝ` by a vector `m`. -/
noncomputable def translateMeasure (γ : Measure (Fin M → ℝ)) (m : Fin M → ℝ) : Measure (Fin M → ℝ) :=
  γ.map (fun z : Fin M → ℝ => fun k => z k + m k)

/-- The convolution `Ḡ = G' * γ` as the pushforward of `G'.prod γ` by `(m,z) ↦ z + m`. -/
noncomputable def hopfieldConvolution
    (G' : Measure (Fin M → ℝ)) (γ : Measure (Fin M → ℝ)) : Measure (Fin M → ℝ) :=
  (G'.prod γ).map (fun p : (Fin M → ℝ) × (Fin M → ℝ) => fun k => p.2 k + p.1 k)

/-! ## The fundamental `lintegral` formula for `hopfieldConvolution` -/

theorem lintegral_hopfieldConvolution
    (G' : Measure (Fin M → ℝ)) (γ : Measure (Fin M → ℝ))
    (F : (Fin M → ℝ) → ℝ≥0∞) (hF : Measurable F)
    [SigmaFinite G'] [SigmaFinite γ] :
    (∫⁻ z, F z ∂hopfieldConvolution (M := M) G' γ)
      =
      ∫⁻ m, ∫⁻ z, F (fun k => z k + m k) ∂γ ∂G' := by
  classical
  -- Start by rewriting the LHS as a `lintegral` over the product measure via `lintegral_map`.
  let T : (Fin M → ℝ) × (Fin M → ℝ) → (Fin M → ℝ) := fun p => fun k => p.2 k + p.1 k
  have hT : Measurable T := by
    -- pointwise addition is measurable
    fun_prop
  have hL :
      (∫⁻ z, F z ∂hopfieldConvolution (M := M) G' γ)
        =
        ∫⁻ p, F (T p) ∂(G'.prod γ) := by
    simpa [hopfieldConvolution, T] using (lintegral_map hF hT)
  -- Now apply Fubini (`lintegral_prod`) and recognize the inner integral as a pushforward integral.
  have hR :
      (∫⁻ p, F (T p) ∂(G'.prod γ))
        =
        ∫⁻ m, ∫⁻ z, F (fun k => z k + m k) ∂γ ∂G' := by
    -- `lintegral_prod` gives `∫⁻ m, ∫⁻ z, ...`.
    simpa [T, add_comm, add_left_comm, add_assoc] using
      (lintegral_prod (μ := G') (ν := γ) (f := fun p => F (T p)) (by fun_prop))
  exact hL.trans hR

end SpinGlass

