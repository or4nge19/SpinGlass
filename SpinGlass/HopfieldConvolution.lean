import SpinGlass.Hopfield
import SpinGlass.GibbsBridge
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.WithDensity

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

/-! ## Probability-measure structure -/

instance (G' : Measure (Fin M → ℝ)) (γ : Measure (Fin M → ℝ))
    [IsProbabilityMeasure G'] [IsProbabilityMeasure γ] :
    IsProbabilityMeasure (hopfieldConvolution (M := M) G' γ) := by
  let T : (Fin M → ℝ) × (Fin M → ℝ) → (Fin M → ℝ) := fun p => fun k => p.2 k + p.1 k
  have hT : AEMeasurable T (G'.prod γ) := by
    exact (by
      have : Measurable T := by fun_prop
      exact this.aemeasurable)
  simpa [hopfieldConvolution, T] using
    (Measure.isProbabilityMeasure_map (μ := (G'.prod γ)) (f := T) hT)

/-! ## The fundamental `lintegral` formula for `hopfieldConvolution` -/

theorem lintegral_hopfieldConvolution
    (G' : Measure (Fin M → ℝ)) (γ : Measure (Fin M → ℝ))
    (F : (Fin M → ℝ) → ℝ≥0∞) (hF : Measurable F)
    [SFinite G'] [SFinite γ] :
    (∫⁻ z, F z ∂hopfieldConvolution (M := M) G' γ) = ∫⁻ m, ∫⁻ z, F (fun k => z k + m k) ∂γ ∂G' := by
  let T : (Fin M → ℝ) × (Fin M → ℝ) → (Fin M → ℝ) := fun p => fun k => p.2 k + p.1 k
  have hT : Measurable T := by
    fun_prop
  have hL : (∫⁻ z, F z ∂hopfieldConvolution (M := M) G' γ) = ∫⁻ p, F (T p) ∂(G'.prod γ) := by
    simpa [hopfieldConvolution, T] using (lintegral_map hF hT)
  have hR : (∫⁻ p, F (T p) ∂(G'.prod γ)) = ∫⁻ m, ∫⁻ z, F (fun k => z k + m k) ∂γ ∂G' := by
    simpa [T, add_comm, add_left_comm, add_assoc] using
      (lintegral_prod (μ := G') (ν := γ) (f := fun p => F (T p)) (by fun_prop))
  exact hL.trans hR

/-! ## Specialization: convolution of the overlap pushforward `G'` -/

theorem lintegral_hopfieldConvolution_overlapImage
    (Ξ : Patterns N M) (H : EnergySpace N) (γ : Measure (Fin M → ℝ))
    (F : (Fin M → ℝ) → ℝ≥0∞) (hF : Measurable F)
    [SFinite γ] : (∫⁻ z, F z ∂hopfieldConvolution (M := M) (hopfieldOverlapImageMeasure (N := N)
    (M := M) Ξ H) γ) = ∫⁻ σ : Config N, ∫⁻ z, F (fun k => z k + hopfieldOverlapVec (N := N)
    (M := M) Ξ σ k) ∂γ ∂(gibbsMeasure (N := N) H) := by
  -- `G'` is a finite (in fact probability) measure, hence σ-finite and s-finite.
  haveI : IsFiniteMeasure (hopfieldOverlapImageMeasure (N := N) (M := M) Ξ H) := by
    dsimp [hopfieldOverlapImageMeasure]; infer_instance
  haveI : SigmaFinite (hopfieldOverlapImageMeasure (N := N) (M := M) Ξ H) := by infer_instance
  haveI : SFinite (hopfieldOverlapImageMeasure (N := N) (M := M) Ξ H) := by infer_instance
  have hbase := lintegral_hopfieldConvolution (M := M)
      (G' := hopfieldOverlapImageMeasure (N := N) (M := M) Ξ H) (γ := γ) (F := F) hF
  let f : (Fin M → ℝ) → ℝ≥0∞ := fun m => ∫⁻ z, F (fun k => z k + m k) ∂γ
  have hf : Measurable f := by
    have : Measurable (Function.uncurry fun m z : Fin M → ℝ => F (fun k => z k + m k)) := by
      fun_prop
    simpa [f] using (Measurable.lintegral_prod_right (ν := γ) this)
  have hmap : (∫⁻ m, f m ∂hopfieldOverlapImageMeasure (N := N) (M := M) Ξ H) = ∫⁻ σ : Config N, f
      (hopfieldOverlapVec (N := N) (M := M) Ξ σ) ∂(gibbsMeasure (N := N) H) := by
    have hmeas : Measurable (hopfieldOverlapVec (N := N) (M := M) Ξ) := by fun_prop
    simpa [hopfieldOverlapImageMeasure, f] using (lintegral_map hf hmeas)
  simpa [f] using hbase.trans hmap

/-! ## Convolution against a `withDensity` measure (Haar/Lebesgue reference) -/

theorem lintegral_hopfieldConvolution_withDensity
    (G' : Measure (Fin M → ℝ)) (F : (Fin M → ℝ) → ℝ≥0∞)
    (hF : Measurable F)
    (g : (Fin M → ℝ) → ℝ≥0∞) (hg : Measurable g)
    [SFinite G'] : (∫⁻ z, F z ∂hopfieldConvolution (M := M) G' (volume.withDensity g)) =
      ∫⁻ m : (Fin M → ℝ), ∫⁻ z, (g z) * F (fun k => z k + m k) ∂volume ∂G' := by
  have hbase :=
    lintegral_hopfieldConvolution (M := M) (G' := G') (γ := (volume.withDensity g)) (F := F) hF
  have hinter : (fun m : (Fin M → ℝ) => ∫⁻ z, F (fun k => z k + m k) ∂(volume.withDensity g)) =
      fun m : (Fin M → ℝ) => ∫⁻ z, (g z) * F (fun k => z k + m k) ∂volume := by
    funext m
    have hFm : Measurable (fun z : (Fin M → ℝ) => F (fun k => z k + m k)) := by fun_prop
    simpa [Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm] using
      (MeasureTheory.lintegral_withDensity_eq_lintegral_mul (μ := (volume : Measure (Fin M → ℝ)))
        (f := g) hg (g := fun z => F (fun k => z k + m k)) hFm)
  simpa [hinter] using hbase

end SpinGlass
