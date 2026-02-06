import SpinGlass.Hopfield
import SpinGlass.GibbsBridge
import SpinGlass.ReplicaKernel
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Defs

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

open SpinGlass.KernelBridge

/-! ## The pushforward `G'` -/

/-- The image of a Gibbs measure under the Hopfield overlap vector map `σ ↦ m(σ)`. -/
noncomputable def hopfieldOverlapImageMeasure
    (Ξ : Patterns N M) (H : EnergySpace N) : Measure (Fin M → ℝ) :=
  (gibbsMeasure (N := N) H).map (hopfieldOverlapVec (N := N) (M := M) Ξ)

lemma hopfieldOverlapImageMeasure_Icc_compl (Ξ : Patterns N M) (H : EnergySpace N) :
    hopfieldOverlapImageMeasure (N := N) (M := M) Ξ H
        (Set.Icc (fun _ : Fin M => (-1 : ℝ)) (fun _ : Fin M => (1 : ℝ)))ᶜ
      = 0 := by
  have hm : Measurable (hopfieldOverlapVec (N := N) (M := M) Ξ) := by
    simpa using measurable_of_finite (hopfieldOverlapVec (N := N) (M := M) Ξ)
  have hpre :
      (hopfieldOverlapVec (N := N) (M := M) Ξ) ⁻¹'
          (Set.Icc (fun _ : Fin M => (-1 : ℝ)) (fun _ : Fin M => (1 : ℝ)))ᶜ
        = (∅ : Set (Config N)) := by
    ext σ
    simp [hopfieldOverlapVec_mem_Icc (Ξ := Ξ) (σ := σ)]
  simp [hopfieldOverlapImageMeasure, Measure.map_apply, hm, hpre]

/-!
### Kernel-level API boundary

To make Hopfield compatible with the Vol II “prove statements for samplers/kernels” approach, we
also package the overlap pushforward as a `Kernel (EnergySpace N) (Fin M → ℝ)`.
-/

/-- Kernel sending an energy function `H` to the overlap-image law `(gibbsMeasure H).map m`. -/
noncomputable def hopfieldOverlapKernel (Ξ : Patterns N M) :
    ProbabilityTheory.Kernel (EnergySpace N) (Fin M → ℝ) :=
  (KernelBridge.gibbsKernel (N := N)).map (hopfieldOverlapVec (N := N) (M := M) Ξ)

instance (Ξ : Patterns N M) : ProbabilityTheory.IsMarkovKernel (hopfieldOverlapKernel (N := N) (M := M) Ξ) := by
  have hm : Measurable (hopfieldOverlapVec (N := N) (M := M) Ξ) := by fun_prop
  simpa [hopfieldOverlapKernel] using
    (ProbabilityTheory.Kernel.IsMarkovKernel.map
      (κ := KernelBridge.gibbsKernel (N := N)) (f := hopfieldOverlapVec (N := N) (M := M) Ξ) hm)

@[simp] lemma hopfieldOverlapKernel_apply (Ξ : Patterns N M) (H : EnergySpace N) :
    hopfieldOverlapKernel (N := N) (M := M) Ξ H = hopfieldOverlapImageMeasure (N := N) (M := M) Ξ H := by
  have hm : Measurable (hopfieldOverlapVec (N := N) (M := M) Ξ) := by fun_prop
  ext s hs
  simp [hopfieldOverlapKernel, hopfieldOverlapImageMeasure, ProbabilityTheory.Kernel.map_apply,
    Kernel.map_apply, KernelBridge.gibbsKernel, FiniteGibbs.gibbsKernel, gibbsMeasure, hm, hs]

lemma hopfieldOverlapKernel_Icc_compl (Ξ : Patterns N M) (H : EnergySpace N) :
    hopfieldOverlapKernel (N := N) (M := M) Ξ H
        (Set.Icc (fun _ : Fin M => (-1 : ℝ)) (fun _ : Fin M => (1 : ℝ)))ᶜ
      = 0 := by
  simpa [hopfieldOverlapKernel_apply] using
    hopfieldOverlapImageMeasure_Icc_compl (N := N) (M := M) (Ξ := Ξ) (H := H)

/-! ### `n` replicas: Hopfield overlap arrays (Vol II shape) -/

variable {n : ℕ}

/-- The Hopfield overlap *array* on `n` replicas: `ℓ ↦ m(σ^ℓ) ∈ ℝ^M`. -/
noncomputable def hopfieldOverlapArray (Ξ : Patterns N M) (σs : ReplicaSpace N n) :
    Fin n → (Fin M → ℝ) :=
  fun ℓ => hopfieldOverlapVec (N := N) (M := M) Ξ (σs ℓ)

@[simp] lemma hopfieldOverlapArray_apply (Ξ : Patterns N M) (σs : ReplicaSpace N n) (ℓ : Fin n) :
    hopfieldOverlapArray (N := N) (M := M) (n := n) Ξ σs ℓ
      =
      hopfieldOverlapVec (N := N) (M := M) Ξ (σs ℓ) := rfl

/-- Pushforward of the `n`-replica Gibbs law by the overlap array map. -/
noncomputable def hopfieldOverlapArrayImageMeasure (Ξ : Patterns N M) (H : EnergySpace N) :
    Measure (Fin n → (Fin M → ℝ)) :=
  (replicaGibbsMeasure (N := N) (n := n) H).map (hopfieldOverlapArray (N := N) (M := M) (n := n) Ξ)

/-- Kernel sending an energy function `H` to the overlap-array law on `n` replicas. -/
noncomputable def hopfieldOverlapArrayKernel (Ξ : Patterns N M) :
    ProbabilityTheory.Kernel (EnergySpace N) (Fin n → (Fin M → ℝ)) :=
  (KernelBridge.replicaGibbsKernel (N := N) (n := n)).map (hopfieldOverlapArray (N := N) (M := M) (n := n) Ξ)

instance (Ξ : Patterns N M) : ProbabilityTheory.IsMarkovKernel (hopfieldOverlapArrayKernel (N := N) (M := M) (n := n) Ξ) := by
  have hm : Measurable (hopfieldOverlapArray (N := N) (M := M) (n := n) Ξ) := by fun_prop
  simpa [hopfieldOverlapArrayKernel] using
    (ProbabilityTheory.Kernel.IsMarkovKernel.map
      (κ := KernelBridge.replicaGibbsKernel (N := N) (n := n))
      (f := hopfieldOverlapArray (N := N) (M := M) (n := n) Ξ) hm)

@[simp] lemma hopfieldOverlapArrayKernel_apply (Ξ : Patterns N M) (H : EnergySpace N) :
    hopfieldOverlapArrayKernel (N := N) (M := M) (n := n) Ξ H
      =
      hopfieldOverlapArrayImageMeasure (N := N) (M := M) (n := n) Ξ H := by
  have hm : Measurable (hopfieldOverlapArray (N := N) (M := M) (n := n) Ξ) := by fun_prop
  ext s hs
  simp [hopfieldOverlapArrayKernel, hopfieldOverlapArrayImageMeasure,
    ProbabilityTheory.Kernel.map_apply, Kernel.map_apply, KernelBridge.replicaGibbsKernel,
    FiniteGibbs.replicaGibbsKernel, replicaGibbsMeasure, hm, hs]

/-! ## Convolution as a pushforward of a product measure -/

/-- Translate a measure `γ` on `Fin M → ℝ` by a vector `m`. -/
noncomputable def translateMeasure (γ : Measure (Fin M → ℝ)) (m : Fin M → ℝ) : Measure (Fin M → ℝ) :=
  γ.map (fun z : Fin M → ℝ => fun k => z k + m k)

/-- The convolution `Ḡ = G' * γ` as the pushforward of `G'.prod γ` by `(m,z) ↦ z + m`. -/
noncomputable def hopfieldConvolution
    (G' : Measure (Fin M → ℝ)) (γ : Measure (Fin M → ℝ)) : Measure (Fin M → ℝ) :=
  (G'.prod γ).map (fun p : (Fin M → ℝ) × (Fin M → ℝ) => fun k => p.2 k + p.1 k)

/-! ## Kernel-level convolution (Vol II-friendly) -/

/-- Convolution kernel: sample `m` from the overlap law, sample `z` from `γ`, output `z + m`. -/
noncomputable def hopfieldConvolutionKernel
    (Ξ : Patterns N M) (γ : Measure (Fin M → ℝ)) :
    ProbabilityTheory.Kernel (EnergySpace N) (Fin M → ℝ) :=
  (ProbabilityTheory.Kernel.map
    (hopfieldOverlapKernel (N := N) (M := M) Ξ ×ₖ ProbabilityTheory.Kernel.const (EnergySpace N) γ)
    (fun p : (Fin M → ℝ) × (Fin M → ℝ) => fun k => p.2 k + p.1 k))

instance (Ξ : Patterns N M) (γ : Measure (Fin M → ℝ)) [IsProbabilityMeasure γ] :
    ProbabilityTheory.IsMarkovKernel (hopfieldConvolutionKernel (N := N) (M := M) Ξ γ) := by
  have ht : Measurable (fun p : (Fin M → ℝ) × (Fin M → ℝ) => fun k => p.2 k + p.1 k) := by fun_prop
  simpa [hopfieldConvolutionKernel] using
    (ProbabilityTheory.Kernel.IsMarkovKernel.map
      (κ := (hopfieldOverlapKernel (N := N) (M := M) Ξ ×ₖ ProbabilityTheory.Kernel.const (EnergySpace N) γ))
      (f := fun p : (Fin M → ℝ) × (Fin M → ℝ) => fun k => p.2 k + p.1 k) ht)

@[simp] lemma hopfieldConvolutionKernel_apply
    (Ξ : Patterns N M) (γ : Measure (Fin M → ℝ)) [SFinite γ] (H : EnergySpace N) :
    hopfieldConvolutionKernel (N := N) (M := M) Ξ γ H
      =
      hopfieldConvolution (M := M) (hopfieldOverlapImageMeasure (N := N) (M := M) Ξ H) γ := by
  let T : (Fin M → ℝ) × (Fin M → ℝ) → (Fin M → ℝ) := fun p => fun k => p.2 k + p.1 k
  have hT : Measurable T := by
    dsimp [T]; fun_prop
  haveI : ProbabilityTheory.IsSFiniteKernel (hopfieldOverlapKernel (N := N) (M := M) Ξ) := by
    infer_instance
  haveI : ProbabilityTheory.IsSFiniteKernel (ProbabilityTheory.Kernel.const (EnergySpace N) γ) := by
    infer_instance
  ext s hs
  simp [hopfieldConvolutionKernel, ProbabilityTheory.Kernel.map_apply' _ hT _ hs, T, hopfieldConvolution,
    Measure.map_apply hT hs, ProbabilityTheory.Kernel.prod_apply, hopfieldOverlapKernel_apply]

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
  have hT : Measurable T := by fun_prop
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

/-! ## Convolution against `volume.withDensity g` has a `withDensity` description -/

/-- If `γ = volume.withDensity g`, then `G' * γ` is also absolutely continuous w.r.t. `volume`,
with density given by the (additive) convolution formula
\[
z \mapsto \int g(z-m)\,dG'(m).
\]

This is the measure-theoretic core behind Talagrand’s Lemma 4.2.1. -/
theorem hopfieldConvolution_withDensity_eq_withDensity
    (G' : Measure (Fin M → ℝ)) [SFinite G']
    (g : (Fin M → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    hopfieldConvolution (M := M) G' (volume.withDensity g)
      =
      (volume.withDensity fun z : Fin M → ℝ =>
        ∫⁻ m : Fin M → ℝ, g (fun k => z k - m k) ∂G') := by
  ext s hs
  let ρ : Measure (Fin M → ℝ) := hopfieldConvolution (M := M) G' (volume.withDensity g)
  let dens : (Fin M → ℝ) → ℝ≥0∞ := fun z => ∫⁻ m : Fin M → ℝ, g (fun k => z k - m k) ∂G'
  have hρ :
      ρ s = ∫⁻ z, (s.indicator (fun _ : (Fin M → ℝ) => (1 : ℝ≥0∞)) z) ∂ρ := by
    simp [ρ, hs]
  have hF : Measurable (s.indicator fun _ : (Fin M → ℝ) => (1 : ℝ≥0∞)) := by
    exact measurable_const.indicator hs
  have hlin :
      (∫⁻ z, (s.indicator (fun _ : (Fin M → ℝ) => (1 : ℝ≥0∞)) z) ∂ρ) =
        ∫⁻ m : (Fin M → ℝ), ∫⁻ z, g z * (s.indicator (fun _ : (Fin M → ℝ) => (1 : ℝ≥0∞))
          (fun k => z k + m k)) ∂volume ∂G' := by
    simpa [ρ] using
      (lintegral_hopfieldConvolution_withDensity (M := M) (G' := G')
        (F := s.indicator (fun _ : (Fin M → ℝ) => (1 : ℝ≥0∞))) hF g hg)
  have hmap_add (m : Fin M → ℝ) :
      Measure.map (fun z : Fin M → ℝ => fun k => z k + m k) (volume : Measure (Fin M → ℝ))
        = volume := by
    simpa [Pi.add_apply] using
      (MeasureTheory.Measure.IsAddRightInvariant.map_add_right_eq_self
        (μ := (volume : Measure (Fin M → ℝ))) m)
  have hinner (m : Fin M → ℝ) :
      (∫⁻ z, g z * (s.indicator (fun _ : (Fin M → ℝ) => (1 : ℝ≥0∞))
        (fun k => z k + m k)) ∂volume) =
        ∫⁻ z, (s.indicator (fun _ : (Fin M → ℝ) => (1 : ℝ≥0∞)) z) * g (fun k => z k - m k) ∂volume := by
    let T : (Fin M → ℝ) → (Fin M → ℝ) := fun z => fun k => z k + m k
    have hT : Measurable T := by fun_prop
    have hTm : Measure.map T (volume : Measure (Fin M → ℝ)) = volume := by
      simpa [T] using hmap_add m
    let H : (Fin M → ℝ) → ℝ≥0∞ :=
      fun z => (s.indicator (fun _ : (Fin M → ℝ) => (1 : ℝ≥0∞)) z) * g (fun k => z k - m k)
    have hH : Measurable H := by
      fun_prop [H, hg]
    have hmap :
        (∫⁻ z, H z ∂(Measure.map T (volume : Measure (Fin M → ℝ)))) = ∫⁻ z, H (T z) ∂volume := by
      simpa [H] using (lintegral_map hH hT)
    have hmap' : (∫⁻ z, H z ∂volume) = ∫⁻ z, H (T z) ∂volume := by
      simpa [hTm] using hmap
    have : (∫⁻ z, (s.indicator (fun _ : (Fin M → ℝ) => (1 : ℝ≥0∞)) z) * g (fun k => z k - m k) ∂volume)
        =
        (∫⁻ z, g z * (s.indicator (fun _ : (Fin M → ℝ) => (1 : ℝ≥0∞)) (fun k => z k + m k)) ∂volume) := by
      simpa [H, T, Pi.add_apply, Pi.sub_apply, mul_assoc, mul_left_comm, mul_comm] using hmap'
    simpa [mul_assoc, mul_left_comm, mul_comm] using this.symm
  have hswap :
      (∫⁻ m : (Fin M → ℝ),
          ∫⁻ z, (s.indicator (fun _ : (Fin M → ℝ) => (1 : ℝ≥0∞)) z) * g (fun k => z k - m k)
            ∂volume ∂G')
        =
        ∫⁻ z, (s.indicator (fun _ : (Fin M → ℝ) => (1 : ℝ≥0∞)) z) * dens z ∂volume := by
    let f : (Fin M → ℝ) → (Fin M → ℝ) → ℝ≥0∞ :=
      fun m z => (s.indicator (fun _ => (1 : ℝ≥0∞)) z) * g (fun k => z k - m k)
    have hf : AEMeasurable (Function.uncurry f) (G'.prod (volume : Measure (Fin M → ℝ))) := by
      have : Measurable (Function.uncurry f) := by
        fun_prop [f, hg]
      exact this.aemeasurable
    have hswap' :
        (∫⁻ m, ∫⁻ z, f m z ∂(volume : Measure (Fin M → ℝ)) ∂G')
          =
          ∫⁻ z, ∫⁻ m, f m z ∂G' ∂(volume : Measure (Fin M → ℝ)) := by
      simpa [f] using
        (MeasureTheory.lintegral_lintegral_swap (μ := G') (ν := (volume : Measure (Fin M → ℝ))) hf)
    have hpull :
        (fun z : Fin M → ℝ => ∫⁻ m, f m z ∂G')
          =
          fun z : Fin M → ℝ => (s.indicator (fun _ => (1 : ℝ≥0∞)) z) * dens z := by
      funext z
      have hgm : Measurable (fun m : Fin M → ℝ => g (fun k => z k - m k)) := by fun_prop [hg]
      simpa [f, dens] using
        (MeasureTheory.lintegral_const_mul
          (μ := G') (r := (s.indicator (fun _ => (1 : ℝ≥0∞)) z))
          (f := fun m : Fin M → ℝ => g (fun k => z k - m k)) hgm)
    calc
      (∫⁻ m, ∫⁻ z, f m z ∂(volume : Measure (Fin M → ℝ)) ∂G')
          =
          ∫⁻ z, ∫⁻ m, f m z ∂G' ∂(volume : Measure (Fin M → ℝ)) := hswap'
      _ = ∫⁻ z, (s.indicator (fun _ => (1 : ℝ≥0∞)) z) * dens z ∂(volume : Measure (Fin M → ℝ)) := by
          refine lintegral_congr_ae (ae_of_all _ (fun z => ?_))
          have hz := congrArg (fun h : (Fin M → ℝ) → ℝ≥0∞ => h z) hpull
          simpa using hz
  calc
    ρ s = ∫⁻ z, (s.indicator (fun _ : (Fin M → ℝ) => (1 : ℝ≥0∞)) z) ∂ρ := hρ
    _ = ∫⁻ m : (Fin M → ℝ),
          ∫⁻ z, g z * (s.indicator (fun _ : (Fin M → ℝ) => (1 : ℝ≥0∞))
            (fun k => z k + m k)) ∂volume ∂G' := hlin
    _ = ∫⁻ m : (Fin M → ℝ),
          ∫⁻ z, (s.indicator (fun _ : (Fin M → ℝ) => (1 : ℝ≥0∞)) z) * g (fun k => z k - m k)
            ∂volume ∂G' := by
          refine lintegral_congr_ae (ae_of_all _ (fun m => ?_))
          simpa using (hinner m)
    _ = ∫⁻ z, (s.indicator (fun _ : (Fin M → ℝ) => (1 : ℝ≥0∞)) z) * dens z ∂volume := hswap
    _ = (volume.withDensity dens) s := by
          -- `∫ 1_s * dens dvol = ∫_s dens dvol = (vol.withDensity dens) s`
          have hind :
              (fun z : Fin M → ℝ =>
                  (s.indicator (fun _ : (Fin M → ℝ) => (1 : ℝ≥0∞)) z) * dens z)
                =
                s.indicator dens := by
            funext z
            by_cases hz : z ∈ s <;> simp [hz]
          simp [MeasureTheory.withDensity_apply, hs, hind, lintegral_indicator]

/-! ## Talagrand’s Gaussian density and the `ψ`-representation (Lemma 4.2.1 core) -/

/-- Talagrand’s normalization constant \(W = (N\beta/(2\pi))^{M/2}\), written as
`(sqrt (Nβ/(2π)))^M` to avoid fractional exponents. -/
noncomputable def talagrandW (N M : ℕ) (β : ℝ) : ℝ :=
  (Real.sqrt ((β * (N : ℝ)) / (2 * Real.pi))) ^ M

/-- Talagrand’s Gaussian density on `ℝ^M` (modeled as `Fin M → ℝ`) w.r.t. Lebesgue `volume`:
\[
g(z) = W \exp\left(-\frac{N\beta}{2}\|z\|^2\right).
\]
We package it as an `ℝ≥0∞` function suitable for `volume.withDensity`. -/
noncomputable def talagrandGaussianDensity (N M : ℕ) (β : ℝ) : (Fin M → ℝ) → ℝ≥0∞ :=
  fun z =>
    ENNReal.ofReal
      (talagrandW (N := N) (M := M) β
        * Real.exp (-((β * (N : ℝ)) / 2) * finVecNormSq M z))

@[fun_prop]
lemma measurable_talagrandGaussianDensity (N M : ℕ) (β : ℝ) :
    Measurable (talagrandGaussianDensity (N := N) (M := M) β) := by
  unfold talagrandGaussianDensity
  apply ENNReal.measurable_ofReal.comp
  have hnorm : Measurable (fun z : Fin M → ℝ => finVecNormSq M z) :=
      measurable_finVecNormSq (M := M)
  fun_prop [talagrandW, hnorm]

/-- Talagrand’s auxiliary Gaussian measure `γ` on `ℝ^M` as `volume.withDensity g`. -/
noncomputable def talagrandGaussianMeasureDensity (N M : ℕ) (β : ℝ) : Measure (Fin M → ℝ) :=
  (volume : Measure (Fin M → ℝ)).withDensity (talagrandGaussianDensity (N := N) (M := M) β)

/-! ### Factorized form of Talagrand’s density -/

/-- One-dimensional Talagrand Gaussian density factor (at inverse variance `β * N`). -/
noncomputable def talagrandGaussianDensity1 (N : ℕ) (β : ℝ) : ℝ → ℝ≥0∞ :=
  fun x =>
    ENNReal.ofReal
      (Real.sqrt ((β * (N : ℝ)) / (2 * Real.pi))
        * Real.exp (-((β * (N : ℝ)) / 2) * x ^ 2))

@[fun_prop] lemma measurable_talagrandGaussianDensity1 (N : ℕ) (β : ℝ) :
    Measurable (talagrandGaussianDensity1 (N := N) β) := by
  unfold talagrandGaussianDensity1
  apply ENNReal.measurable_ofReal.comp
  fun_prop

lemma talagrandGaussianDensity_eq_prod_density1 (N M : ℕ) (β : ℝ) (z : Fin M → ℝ) :
    talagrandGaussianDensity (N := N) (M := M) β z
      =
      ∏ k : Fin M, talagrandGaussianDensity1 (N := N) β (z k) := by
  set c : ℝ := Real.sqrt ((β * (N : ℝ)) / (2 * Real.pi))
  set a : ℝ := (β * (N : ℝ)) / 2
  have hc : 0 ≤ c := by
    dsimp [c]; exact Real.sqrt_nonneg _
  have hterm_nonneg :
      ∀ k : Fin M, 0 ≤ c * Real.exp (-(a * (z k) ^ 2)) := by
    intro k; exact mul_nonneg hc (Real.exp_pos _).le
  have hprod_ofReal :
      (∏ k : Fin M, ENNReal.ofReal (c * Real.exp (-(a * (z k) ^ 2))))
        =
        ENNReal.ofReal (∏ k : Fin M, (c * Real.exp (-(a * (z k) ^ 2)))) := by
    simpa using (ENNReal.ofReal_prod_of_nonneg (s := (Finset.univ : Finset (Fin M)))
      (f := fun k : Fin M => c * Real.exp (-(a * (z k) ^ 2)))
      (by intro k hk; simpa using hterm_nonneg k)).symm
  have hprod_real :
      (∏ k : Fin M, (c * Real.exp (-(a * (z k) ^ 2))))
        =
        (c ^ M) * Real.exp (-(a * finVecNormSq M z)) := by
    have hcprod :
        (∏ k : Fin M, (c * Real.exp (-(a * (z k) ^ 2))))
          =
          (∏ k : Fin M, c) * (∏ k : Fin M, Real.exp (-(a * (z k) ^ 2))) := by
      exact
        (Finset.prod_mul_distrib :
          (∏ k : Fin M, c * Real.exp (-(a * (z k) ^ 2)))
            = (∏ k : Fin M, c) * (∏ k : Fin M, Real.exp (-(a * (z k) ^ 2))))
    have hc_const : (∏ k : Fin M, c) = c ^ M := by
      simp
    have hexp :
        (∏ k : Fin M, Real.exp (-(a * (z k) ^ 2)))
          =
          Real.exp (∑ k : Fin M, (-(a * (z k) ^ 2))) := by
      simpa using (Real.exp_sum (s := (Finset.univ : Finset (Fin M)))
        (f := fun k : Fin M => (-(a * (z k) ^ 2)))).symm
    have hsum :
        (∑ k : Fin M, (-(a * (z k) ^ 2)))
          =
          -(a * finVecNormSq M z) := by
      simp [finVecNormSq, Finset.mul_sum]
    calc
      (∏ k : Fin M, (c * Real.exp (-(a * (z k) ^ 2))))
          = (∏ k : Fin M, c) * (∏ k : Fin M, Real.exp (-(a * (z k) ^ 2))) := hcprod
      _ = (c ^ M) * Real.exp (∑ k : Fin M, (-(a * (z k) ^ 2))) := by simp [hc_const, hexp]
      _ = (c ^ M) * Real.exp (-(a * finVecNormSq M z)) := by simp [hsum]
  have hW : talagrandW (N := N) (M := M) β = c ^ M := by
    simp [talagrandW, c]
  have hexp2 :
      Real.exp (-((β * (N : ℝ)) / 2) * finVecNormSq M z) = Real.exp (-(a * finVecNormSq M z)) := by
    simp [a]
  calc
    talagrandGaussianDensity (N := N) (M := M) β z
        =
        ENNReal.ofReal (talagrandW (N := N) (M := M) β
          * Real.exp (-((β * (N : ℝ)) / 2) * finVecNormSq M z)) := by
          simp [talagrandGaussianDensity]
    _ =
        ENNReal.ofReal ((c ^ M) * Real.exp (-(a * finVecNormSq M z))) := by
          simp [hW, a]
    _ =
        ENNReal.ofReal (∏ k : Fin M, (c * Real.exp (-(a * (z k) ^ 2)))) := by
          exact congrArg ENNReal.ofReal hprod_real.symm
    _ =
        ∏ k : Fin M, ENNReal.ofReal (c * Real.exp (-(a * (z k) ^ 2))) := by
          simpa using hprod_ofReal.symm
    _ =
        ∏ k : Fin M, talagrandGaussianDensity1 (N := N) β (z k) := by
          simp [talagrandGaussianDensity1, c, a]

/-! ### Identifying the one-dimensional factor with `gaussianPDF` -/

lemma talagrandGaussianDensity1_eq_gaussianPDF
    (N : ℕ) (β : ℝ) (hβ : 0 ≤ β) (hβN : β * (N : ℝ) ≠ 0) (x : ℝ) :
    talagrandGaussianDensity1 (N := N) β x
      =
      ProbabilityTheory.gaussianPDF 0 (talagrandGaussianVar (N := N) β hβ) x := by
  set t : ℝ := β * (N : ℝ)
  have ht : 0 < t := lt_of_le_of_ne (mul_nonneg hβ (by exact_mod_cast (Nat.zero_le N))) (Ne.symm hβN)
  have ht0 : t ≠ 0 := ne_of_gt ht
  set v : ℝ≥0 := talagrandGaussianVar (N := N) β hβ
  have hL : 0 ≤ Real.sqrt (t / (2 * Real.pi)) * Real.exp (-(t / 2) * x ^ 2) := by
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  have hR : 0 ≤ ProbabilityTheory.gaussianPDFReal 0 v x := by
    simpa using ProbabilityTheory.gaussianPDFReal_nonneg 0 v x
  refine (ENNReal.ofReal_eq_ofReal_iff hL hR).2 ?_
  have hv : (v : ℝ) = t⁻¹ := by simp [v, talagrandGaussianVar, t]
  have hcoeff :
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ = Real.sqrt (t / (2 * Real.pi)) := by
    have hpos : 0 ≤ (2 * Real.pi * (v : ℝ)) := by
      have : 0 ≤ (v : ℝ) := by exact_mod_cast (show (0 : ℝ≥0) ≤ v from bot_le)
      nlinarith [Real.pi_pos]
    calc
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
          = Real.sqrt ((2 * Real.pi * (v : ℝ))⁻¹) := by
              simp
      _ = Real.sqrt (t / (2 * Real.pi)) := by
            simp [hv, div_eq_mul_inv]
  have hexponent :
      (-(x - (0 : ℝ)) ^ 2 / (2 * (v : ℝ)))
        =
      (-(t / 2) * x ^ 2) := by
    simp [hv, sub_eq_add_neg, div_eq_mul_inv, pow_two]
    ring_nf
  have :
      Real.sqrt (t / (2 * Real.pi)) * Real.exp (-(t / 2) * x ^ 2)
        =
        ProbabilityTheory.gaussianPDFReal 0 v x := by
    dsimp [ProbabilityTheory.gaussianPDFReal]
    rw [hcoeff, hexponent]
  exact this

lemma lintegral_talagrandGaussianDensity1_eq_one
    (N : ℕ) (β : ℝ) (hβ : 0 ≤ β) (hβN : β * (N : ℝ) ≠ 0) :
    (∫⁻ x : ℝ, talagrandGaussianDensity1 (N := N) β x ∂(volume : Measure ℝ)) = 1 := by
  have hv : talagrandGaussianVar (N := N) β hβ ≠ 0 := by
    intro hv0
    have hcoe : ((talagrandGaussianVar (N := N) β hβ : ℝ≥0) : ℝ) = 0 := by simpa [hv0]
    have : ((talagrandGaussianVar (N := N) β hβ : ℝ≥0) : ℝ) = (β * (N : ℝ))⁻¹ := by
      simp [talagrandGaussianVar]
    have : (β * (N : ℝ))⁻¹ = 0 := by simpa [this] using hcoe
    exact (inv_ne_zero hβN) this
  simpa [talagrandGaussianDensity1_eq_gaussianPDF (N := N) (β := β) hβ hβN] using
    (ProbabilityTheory.lintegral_gaussianPDF_eq_one (μ := (0 : ℝ)) (v := talagrandGaussianVar (N := N) β hβ) hv)

theorem lintegral_talagrandGaussianDensity_eq_one
    (N M : ℕ) (β : ℝ) (hβ : 0 ≤ β) (hβN : β * (N : ℝ) ≠ 0) :
    (∫⁻ z : Fin M → ℝ, talagrandGaussianDensity (N := N) (M := M) β z
        ∂(volume : Measure (Fin M → ℝ))) = 1 := by
  induction M with
  | zero =>
      have huniv : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
        calc
          (volume : Measure (Fin 0 → ℝ)) Set.univ
              = Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) Set.univ := rfl
          _ = (∏ _i : Fin 0, (volume : Measure ℝ) Set.univ) := by
                simpa using (MeasureTheory.pi_univ (μ := fun _ : Fin 0 => (volume : Measure ℝ)))
          _ = 1 := by simp
      simpa [talagrandGaussianDensity_eq_prod_density1, talagrandGaussianDensity1, huniv]
  | succ n ih =>
      let e :
          (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (0 : Fin (n + 1))
      have hmp : MeasurePreserving e := by
        simpa [e] using
          (MeasureTheory.volume_preserving_piFinSuccAbove (α := fun _ : Fin (n + 1) => ℝ)
            (i := (0 : Fin (n + 1))))
      let f : ℝ × (Fin n → ℝ) → ℝ≥0∞ :=
        fun p =>
          talagrandGaussianDensity1 (N := N) β p.1
            * ∏ j : Fin n, talagrandGaussianDensity1 (N := N) β (p.2 j)
      have hf : Measurable f := by
        -- finite product of measurable factors
        fun_prop [f, measurable_talagrandGaussianDensity1]
      have hcomp :
          (fun z : Fin (n + 1) → ℝ => talagrandGaussianDensity (N := N) (M := n + 1) β z)
            =
            fun z => f (e z) := by
        funext z
        -- Rewrite the density as a product over coordinates and split off coordinate `0`.
        rw [talagrandGaussianDensity_eq_prod_density1 (N := N) (M := n + 1) (β := β) z]
        -- split the product at `0` (so the remainder is indexed by `Fin n` via `succ`)
        rw [Fin.prod_univ_succ (f := fun k : Fin (n + 1) => talagrandGaussianDensity1 (N := N) β (z k))]
        -- `e z` is `(z 0, Fin.tail z)` at `i = 0`
        simp [f, e, Fin.tail, mul_assoc, mul_left_comm, mul_comm]
      calc
        (∫⁻ z : Fin (n + 1) → ℝ, talagrandGaussianDensity (N := N) (M := n + 1) β z
            ∂(volume : Measure (Fin (n + 1) → ℝ)))
            =
            ∫⁻ z : Fin (n + 1) → ℝ, f (e z) ∂(volume : Measure (Fin (n + 1) → ℝ)) := by
              simp [hcomp]
        _ = ∫⁻ p : ℝ × (Fin n → ℝ), f p ∂(volume : Measure (ℝ × (Fin n → ℝ))) := by
              simpa using (MeasurePreserving.lintegral_comp (hg := hmp) (f := f) hf)
        _ = ∫⁻ p : ℝ × (Fin n → ℝ), f p ∂((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
              simpa [MeasureTheory.Measure.volume_eq_prod]
        _ =
            (∫⁻ x : ℝ, talagrandGaussianDensity1 (N := N) β x ∂(volume : Measure ℝ))
              *
              ∫⁻ y : Fin n → ℝ, (∏ j : Fin n, talagrandGaussianDensity1 (N := N) β (y j))
                ∂(volume : Measure (Fin n → ℝ)) := by
              -- apply `lintegral_prod_mul` to `f p = f₁ p.1 * f₂ p.2`
              have hf1 : AEMeasurable (fun x : ℝ => talagrandGaussianDensity1 (N := N) β x) (volume : Measure ℝ) :=
                (measurable_talagrandGaussianDensity1 (N := N) β).aemeasurable
              have hf2 :
                  AEMeasurable (fun y : Fin n → ℝ => ∏ j : Fin n, talagrandGaussianDensity1 (N := N) β (y j))
                    (volume : Measure (Fin n → ℝ)) := by
                have : Measurable (fun y : Fin n → ℝ => ∏ j : Fin n, talagrandGaussianDensity1 (N := N) β (y j)) := by
                  fun_prop [measurable_talagrandGaussianDensity1]
                exact this.aemeasurable
              simpa [f, mul_assoc, mul_left_comm, mul_comm] using
                (MeasureTheory.lintegral_prod_mul (μ := (volume : Measure ℝ))
                  (ν := (volume : Measure (Fin n → ℝ))) hf1 hf2)
        _ = 1 := by
              -- First factor is `1`; second factor is the `n`-dimensional normalization (IH).
              have h1 :
                  (∫⁻ x : ℝ, talagrandGaussianDensity1 (N := N) β x ∂(volume : Measure ℝ)) = 1 :=
                lintegral_talagrandGaussianDensity1_eq_one (N := N) (β := β) hβ hβN
              have h2 :
                  (∫⁻ y : Fin n → ℝ, (∏ j : Fin n, talagrandGaussianDensity1 (N := N) β (y j))
                      ∂(volume : Measure (Fin n → ℝ))) = 1 := by
                -- rewrite the integrand using the factorization lemma, then apply IH
                have hfacn :
                    (fun y : Fin n → ℝ => (∏ j : Fin n, talagrandGaussianDensity1 (N := N) β (y j)))
                      =
                      fun y : Fin n → ℝ => talagrandGaussianDensity (N := N) (M := n) β y := by
                  funext y
                  simpa [talagrandGaussianDensity_eq_prod_density1 (N := N) (M := n) (β := β) y]
                simpa [hfacn] using ih
              simpa [h1, h2]

instance instIsProbabilityMeasure_talagrandGaussianMeasureDensity
    (N M : ℕ) (β : ℝ) (hβ : 0 ≤ β) (hβN : β * (N : ℝ) ≠ 0) :
    IsProbabilityMeasure (talagrandGaussianMeasureDensity (N := N) (M := M) β) := by
  refine ⟨?_⟩
  -- total mass = lintegral of the density
  simp [talagrandGaussianMeasureDensity, MeasureTheory.withDensity_apply, MeasurableSet.univ,
    lintegral_talagrandGaussianDensity_eq_one (N := N) (M := M) (β := β) hβ hβN]

/-! ### Hopfield convolution against Talagrand Gaussian, as a kernel -/

/-- Convolution kernel specialized to Talagrand’s Gaussian input measure. -/
noncomputable def hopfieldConvolutionTalagrandKernel
    {N M : ℕ} (Ξ : Patterns N M) (β : ℝ) :
    ProbabilityTheory.Kernel (EnergySpace N) (Fin M → ℝ) :=
  hopfieldConvolutionKernel (N := N) (M := M) Ξ
    (talagrandGaussianMeasureDensity (N := N) (M := M) β)

instance instIsMarkovKernel_hopfieldConvolutionTalagrandKernel
    {N M : ℕ} (Ξ : Patterns N M) (β : ℝ) (hβ : 0 ≤ β) (hβN : β * (N : ℝ) ≠ 0) :
    ProbabilityTheory.IsMarkovKernel (hopfieldConvolutionTalagrandKernel (N := N) (M := M) Ξ β) := by
  haveI : IsProbabilityMeasure (talagrandGaussianMeasureDensity (N := N) (M := M) β) :=
    instIsProbabilityMeasure_talagrandGaussianMeasureDensity (N := N) (M := M) (β := β) hβ hβN
  simpa [hopfieldConvolutionTalagrandKernel] using
    (show ProbabilityTheory.IsMarkovKernel
        (hopfieldConvolutionKernel (N := N) (M := M) Ξ
          (talagrandGaussianMeasureDensity (N := N) (M := M) β)) from
      (by infer_instance))

@[simp] lemma hopfieldConvolutionTalagrandKernel_apply
    {N M : ℕ} (Ξ : Patterns N M) (β : ℝ) (hβ : 0 ≤ β) (hβN : β * (N : ℝ) ≠ 0) (H : EnergySpace N) :
    hopfieldConvolutionTalagrandKernel (N := N) (M := M) Ξ β H
      =
      hopfieldConvolution (M := M) (hopfieldOverlapImageMeasure (N := N) (M := M) Ξ H)
        (talagrandGaussianMeasureDensity (N := N) (M := M) β) := by
  haveI : IsProbabilityMeasure (talagrandGaussianMeasureDensity (N := N) (M := M) β) :=
    instIsProbabilityMeasure_talagrandGaussianMeasureDensity (N := N) (M := M) (β := β) hβ hβN
  haveI : SFinite (talagrandGaussianMeasureDensity (N := N) (M := M) β) := by infer_instance
  simpa [hopfieldConvolutionTalagrandKernel] using
    (hopfieldConvolutionKernel_apply (N := N) (M := M) (Ξ := Ξ)
      (γ := talagrandGaussianMeasureDensity (N := N) (M := M) β) (H := H))

/-! ### Talagrand Gaussian as a constant kernel (Vol II style) -/

/-- Talagrand’s Gaussian measure packaged as a constant kernel. -/
noncomputable def talagrandGaussianKernelDensity
    (N M : ℕ) (β : ℝ) : ProbabilityTheory.Kernel (EnergySpace N) (Fin M → ℝ) :=
  ProbabilityTheory.Kernel.const (EnergySpace N) (talagrandGaussianMeasureDensity (N := N) (M := M) β)

instance instIsMarkovKernel_talagrandGaussianKernelDensity
    (N M : ℕ) (β : ℝ) (hβ : 0 ≤ β) (hβN : β * (N : ℝ) ≠ 0) :
    ProbabilityTheory.IsMarkovKernel (talagrandGaussianKernelDensity (N := N) (M := M) β) := by
  haveI :
      IsProbabilityMeasure (talagrandGaussianMeasureDensity (N := N) (M := M) β) :=
    instIsProbabilityMeasure_talagrandGaussianMeasureDensity (N := N) (M := M) (β := β) hβ hβN
  -- `Kernel.const` is Markov iff the underlying measure is a probability measure.
  simpa [talagrandGaussianKernelDensity] using
    (show ProbabilityTheory.IsMarkovKernel
        (ProbabilityTheory.Kernel.const (EnergySpace N)
          (talagrandGaussianMeasureDensity (N := N) (M := M) β)) from
      (by infer_instance))

lemma hopfieldConvolution_talagrandGaussian_eq_withDensity
    (N M : ℕ) (G' : Measure (Fin M → ℝ)) [SFinite G'] (β : ℝ) :
    hopfieldConvolution (M := M) G' (talagrandGaussianMeasureDensity (N := N) (M := M) β) =
      (volume.withDensity fun z : Fin M → ℝ => ∫⁻ m : Fin M → ℝ,
      talagrandGaussianDensity (N := N) (M := M) β (fun k => z k - m k) ∂G') := by
  simpa [talagrandGaussianMeasureDensity] using
    (hopfieldConvolution_withDensity_eq_withDensity (M := M) (G' := G')
        (g := talagrandGaussianDensity (N := N) (M := M) β)
        (measurable_talagrandGaussianDensity (N := N) (M := M) β))

lemma hopfieldConvolution_overlapImage_talagrandGaussian_eq_withDensity
    (Ξ : Patterns N M) (H : EnergySpace N) (β : ℝ) :
    hopfieldConvolution (M := M)
        (hopfieldOverlapImageMeasure (N := N) (M := M) Ξ H)
        (talagrandGaussianMeasureDensity (N := N) (M := M) β) =
      volume.withDensity (fun z : Fin M → ℝ =>
        ∫⁻ σ : Config N, talagrandGaussianDensity (N := N) (M := M) β
            (fun k => z k - hopfieldOverlapVec (N := N) (M := M) Ξ σ k)
          ∂(gibbsMeasure (N := N) H)) := by
  haveI : IsFiniteMeasure (hopfieldOverlapImageMeasure (N := N) (M := M) Ξ H) := by
    dsimp [hopfieldOverlapImageMeasure]
    infer_instance
  haveI : SigmaFinite (hopfieldOverlapImageMeasure (N := N) (M := M) Ξ H) := by infer_instance
  haveI : SFinite (hopfieldOverlapImageMeasure (N := N) (M := M) Ξ H) := by infer_instance
  have h :=
    hopfieldConvolution_talagrandGaussian_eq_withDensity (N := N) (M := M)
      (G' := hopfieldOverlapImageMeasure (N := N) (M := M) Ξ H) (β := β)
  have hmeas : Measurable (hopfieldOverlapVec (N := N) (M := M) Ξ) := by fun_prop
  have hdens :
      (fun z : Fin M → ℝ =>
          ∫⁻ m : Fin M → ℝ,
            talagrandGaussianDensity (N := N) (M := M) β (fun k => z k - m k)
              ∂hopfieldOverlapImageMeasure (N := N) (M := M) Ξ H) =
        fun z : Fin M → ℝ => ∫⁻ σ : Config N,
            talagrandGaussianDensity (N := N) (M := M) β
              (fun k => z k - hopfieldOverlapVec (N := N) (M := M) Ξ σ k)
            ∂(gibbsMeasure (N := N) H) := by
    funext z
    have hGmeas : Measurable (fun m : Fin M → ℝ =>
          talagrandGaussianDensity (N := N) (M := M) β (fun k => z k - m k)) := by
      fun_prop [measurable_talagrandGaussianDensity]
    simpa [hopfieldOverlapImageMeasure] using (lintegral_map hGmeas hmeas)
  simpa [hdens] using h

/-! ### Algebraic normal form for Talagrand’s Gaussian density -/

/-- Dot product on `Fin M → ℝ` as a finite sum. -/
noncomputable def finVecDot (M : ℕ) (x y : Fin M → ℝ) : ℝ :=
  ∑ k : Fin M, x k * y k

lemma finVecNormSq_sub (M : ℕ) (x y : Fin M → ℝ) :
    finVecNormSq M (fun k => x k - y k)
      =
      finVecNormSq M x + finVecNormSq M y - 2 * finVecDot M x y := by
  have hterm : (fun k : Fin M => (x k - y k) ^ 2) =
      fun k : Fin M => x k ^ 2 + y k ^ 2 - 2 * (x k * y k) := by
    funext k
    ring_nf
  simp [finVecNormSq, finVecDot, hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp [Finset.mul_sum, mul_assoc, mul_comm]

lemma talagrandGaussianDensity_sub
    (N M : ℕ) (β : ℝ) (z m : Fin M → ℝ) :
    talagrandGaussianDensity (N := N) (M := M) β (fun k => z k - m k)
      =
      ENNReal.ofReal
          (talagrandW (N := N) (M := M) β
            * Real.exp (-((β * (N : ℝ)) / 2) * finVecNormSq M z))
        *
        ENNReal.ofReal
          (Real.exp ((β * (N : ℝ)) * finVecDot M z m
            - ((β * (N : ℝ)) / 2) * finVecNormSq M m)) := by
  have hsq :
      finVecNormSq M (fun k => z k - m k)
        =
        finVecNormSq M z + finVecNormSq M m - 2 * finVecDot M z m :=
    finVecNormSq_sub (M := M) z m
  have hexp :
      Real.exp (-((β * (N : ℝ)) / 2) * finVecNormSq M (fun k => z k - m k))
        =
        Real.exp (-((β * (N : ℝ)) / 2) * finVecNormSq M z)
          * Real.exp ((β * (N : ℝ)) * finVecDot M z m - ((β * (N : ℝ)) / 2) * finVecNormSq M m) := by
    have :
        -((β * (N : ℝ)) / 2) * finVecNormSq M (fun k => z k - m k)
          =
          (-((β * (N : ℝ)) / 2) * finVecNormSq M z)
            + ((β * (N : ℝ)) * finVecDot M z m - ((β * (N : ℝ)) / 2) * finVecNormSq M m) := by
      simp [hsq]
      ring_nf
    simp [this, Real.exp_add, mul_assoc]
  have hW : 0 ≤ talagrandW (N := N) (M := M) β := by
    dsimp [talagrandW]
    positivity
  have hA :
      0 ≤ talagrandW (N := N) (M := M) β
            * Real.exp (-((β * (N : ℝ)) / 2) * finVecNormSq M z) := by
    positivity
  have hB :
      0 ≤ Real.exp ((β * (N : ℝ)) * finVecDot M z m
            - ((β * (N : ℝ)) / 2) * finVecNormSq M m) := by
    positivity
  have hmul :
      ENNReal.ofReal
          (talagrandW (N := N) (M := M) β
              * (Real.exp (-((β * (N : ℝ)) / 2) * finVecNormSq M z)
                * Real.exp ((β * (N : ℝ)) * finVecDot M z m
                  - ((β * (N : ℝ)) / 2) * finVecNormSq M m)))
        =
        ENNReal.ofReal
            (talagrandW (N := N) (M := M) β
              * Real.exp (-((β * (N : ℝ)) / 2) * finVecNormSq M z))
          *
          ENNReal.ofReal
            (Real.exp ((β * (N : ℝ)) * finVecDot M z m
              - ((β * (N : ℝ)) / 2) * finVecNormSq M m)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (ENNReal.ofReal_mul (p := talagrandW (N := N) (M := M) β
          * Real.exp (-((β * (N : ℝ)) / 2) * finVecNormSq M z))
        (q := Real.exp ((β * (N : ℝ)) * finVecDot M z m
            - ((β * (N : ℝ)) / 2) * finVecNormSq M m)) hA)
  have hexp' :
      Real.exp (-( ((β * (N : ℝ)) / 2) * finVecNormSq M (fun k => z k - m k)))
        =
        Real.exp (-((β * (N : ℝ)) / 2) * finVecNormSq M z)
          * Real.exp ((β * (N : ℝ)) * finVecDot M z m - ((β * (N : ℝ)) / 2) * finVecNormSq M m) := by
    simpa [neg_mul, mul_assoc] using hexp
  dsimp [talagrandGaussianDensity]
  simp [hexp', mul_assoc] at *
  exact hmul

/-! ### Turning the overlap integral into Talagrand’s `ψ` (finite-volume, exact) -/

lemma finVecDot_overlapVec
    (N M : ℕ) (Ξ : Patterns N M) (z : Fin M → ℝ) (σ : Config N) :
    (N : ℝ) * finVecDot M z (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
      =
      ∑ i : Fin N, (hopfieldEtaDot (N := N) (M := M) Ξ i z) * (spin N σ i) := by
  by_cases hN : N = 0
  · subst hN
    simp [finVecDot, hopfieldOverlapVec, hopfieldOverlap, hopfieldEtaDot]
  · have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    have hm (k : Fin M) :
        hopfieldOverlapVec (N := N) (M := M) Ξ σ k
          =
          (1 / (N : ℝ)) * ∑ i : Fin N, (hopfieldEta (N := N) (M := M) Ξ i k) * (spin N σ i) := by
      simpa using hopfieldOverlap_eq_eta (N := N) (M := M) (Ξ := Ξ) (σ := σ) k
    calc
      (N : ℝ) * finVecDot M z (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
          =
          (N : ℝ) * ∑ k : Fin M, z k * ((1 / (N : ℝ)) * ∑ i : Fin N,
            hopfieldEta (N := N) (M := M) Ξ i k * spin N σ i) := by
            simp [finVecDot, hm, mul_assoc, mul_left_comm, mul_comm]
      _ =
          (N : ℝ) * ((1 / (N : ℝ)) * ∑ k : Fin M, z k * ∑ i : Fin N,
            hopfieldEta (N := N) (M := M) Ξ i k * spin N σ i) := by
            simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
      _ =
          ∑ k : Fin M, z k * ∑ i : Fin N,
            hopfieldEta (N := N) (M := M) Ξ i k * spin N σ i := by
            simp [div_eq_mul_inv, hN', mul_assoc, mul_left_comm, mul_comm]
      _ =
          ∑ i : Fin N, (∑ k : Fin M, hopfieldEta (N := N) (M := M) Ξ i k * z k) * spin N σ i := by
            have :
                (∑ k : Fin M, z k * ∑ i : Fin N, hopfieldEta (N := N) (M := M) Ξ i k * spin N σ i)
                  =
                  ∑ k : Fin M, ∑ i : Fin N, z k * (hopfieldEta (N := N) (M := M) Ξ i k * spin N σ i) := by
                refine Finset.sum_congr rfl ?_
                intro k _hk
                simp [Finset.mul_sum, mul_assoc]
            rw [this, Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro i _hi
            have :
                (∑ k : Fin M, z k * (hopfieldEta (N := N) (M := M) Ξ i k * spin N σ i))
                  =
                  (∑ k : Fin M, hopfieldEta (N := N) (M := M) Ξ i k * z k) * spin N σ i := by
                simpa [Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm] using
                  (Finset.sum_mul (s := (Finset.univ : Finset (Fin M)))
                    (f := fun k : Fin M => hopfieldEta (N := N) (M := M) Ξ i k * z k)
                    (a := spin N σ i)).symm
            simpa [hopfieldEtaDot, mul_assoc, mul_left_comm, mul_comm] using this
      _ = ∑ i : Fin N, hopfieldEtaDot (N := N) (M := M) Ξ i z * spin N σ i := by
            simp [hopfieldEtaDot]

lemma lintegral_gibbsMeasure_ofReal
    (N : ℕ) (H : EnergySpace N) (f : Config N → ℝ) (hf : ∀ σ, 0 ≤ f σ) :
    (∫⁻ σ, ENNReal.ofReal (f σ) ∂gibbsMeasure (N := N) H)
      =
      ENNReal.ofReal (∑ σ : Config N, (gibbs_pmf N H σ) * f σ) := by
  -- Delegate to the generic finite-volume Gibbs measure lemma.
  simpa [gibbsMeasure, FiniteGibbs.gibbsMeasure, gibbs_pmf, FiniteGibbs.gibbs_pmf, Z, FiniteGibbs.Z] using
    (FiniteGibbs.lintegral_gibbsMeasure_ofReal (α := Config N) (H := H) (f := f) hf)

lemma overlapImage_talagrandGaussianDensity_factor
    (N M : ℕ) (Ξ : Patterns N M) (H : EnergySpace N) (β : ℝ) (z : Fin M → ℝ) :
    (∫⁻ σ : Config N,
          talagrandGaussianDensity (N := N) (M := M) β
              (fun k => z k - hopfieldOverlapVec (N := N) (M := M) Ξ σ k)
        ∂gibbsMeasure (N := N) H)
      =
      ENNReal.ofReal
          (talagrandW (N := N) (M := M) β
            * Real.exp (-((β * (N : ℝ)) / 2) * finVecNormSq M z))
        *
        (∫⁻ σ : Config N,
            ENNReal.ofReal
              (Real.exp
                ((β * (N : ℝ)) * finVecDot M z (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
                  - ((β * (N : ℝ)) / 2) *
                      finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ σ)))
          ∂gibbsMeasure (N := N) H) := by
  have hmeas :
      Measurable fun σ : Config N =>
        ENNReal.ofReal
          (Real.exp
            ((β * (N : ℝ)) * finVecDot M z (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
              - ((β * (N : ℝ)) / 2) *
                  finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ σ))) := by
    fun_prop
  have hcongr :
      (fun σ : Config N =>
          talagrandGaussianDensity (N := N) (M := M) β
            (fun k => z k - hopfieldOverlapVec (N := N) (M := M) Ξ σ k))
        =
        fun σ : Config N =>
          ENNReal.ofReal
              (talagrandW (N := N) (M := M) β
                * Real.exp (-((β * (N : ℝ)) / 2) * finVecNormSq M z))
            *
            ENNReal.ofReal
              (Real.exp
                ((β * (N : ℝ)) * finVecDot M z (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
                  - ((β * (N : ℝ)) / 2) *
                      finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ σ))) := by
    funext σ
    simpa [Pi.sub_apply] using
      (talagrandGaussianDensity_sub (N := N) (M := M) (β := β) z
        (hopfieldOverlapVec (N := N) (M := M) Ξ σ))
  simp [hcongr, MeasureTheory.lintegral_const_mul, hmeas]

/-- The exact Talagrand `ψ`-density formula (finite volume) under the “first pattern constant”
assumption, with explicit normalization by `Z`. -/
theorem hopfieldConvolution_overlapImage_talagrandGaussian_eq_withDensity_psi
    (N M : ℕ) (Ξ : Patterns N M) (β h : ℝ) (k0 : Fin M)
    (hΞ : IsConstantPattern (N := N) Ξ k0) :
    hopfieldConvolution (M := M)
        (hopfieldOverlapImageMeasure (N := N) (M := M) Ξ (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))
        (talagrandGaussianMeasureDensity (N := N) (M := M) β)
      =
      volume.withDensity (fun z : Fin M → ℝ =>
        ENNReal.ofReal
          ((talagrandW (N := N) (M := M) β) * (2 : ℝ) ^ N / Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0)
            * Real.exp (hopfieldPsi (N := N) (M := M) β h Ξ z))) := by
  have hbase :=
    hopfieldConvolution_overlapImage_talagrandGaussian_eq_withDensity (N := N) (M := M) (Ξ := Ξ)
      (H := hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0) (β := β)
  refine hbase.trans ?_
  congr 1
  funext z
  have hfactor :=
    overlapImage_talagrandGaussianDensity_factor (N := N) (M := M) (Ξ := Ξ)
      (H := hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0) (β := β) z
  have hexp_nonneg : ∀ σ : Config N, 0 ≤
      Real.exp
        ((β * (N : ℝ)) * finVecDot M z (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
          - ((β * (N : ℝ)) / 2) * finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ σ)) := by
    intro σ; exact (Real.exp_pos _).le
  have hlin :
      (∫⁻ σ : Config N,
          ENNReal.ofReal
            (Real.exp
              ((β * (N : ℝ)) * finVecDot M z (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
                - ((β * (N : ℝ)) / 2) * finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ σ)))
        ∂gibbsMeasure (N := N) (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))
        =
        ENNReal.ofReal
          (∑ σ : Config N,
            gibbs_pmf N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0) σ
              *
              Real.exp
                ((β * (N : ℝ)) * finVecDot M z (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
                  - ((β * (N : ℝ)) / 2) *
                      finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ σ))) := by
    simpa using
      (lintegral_gibbsMeasure_ofReal (N := N)
        (H := hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0)
        (f := fun σ =>
          Real.exp
            ((β * (N : ℝ)) * finVecDot M z (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
              - ((β * (N : ℝ)) / 2) *
                  finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ σ)))
        hexp_nonneg)
  have hsum :
      (∑ σ : Config N,
          gibbs_pmf N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0) σ
            *
            Real.exp
              ((β * (N : ℝ)) * finVecDot M z (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
                - ((β * (N : ℝ)) / 2) *
                    finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ σ)))
        =
        (Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))⁻¹
          *
          (∑ σ : Config N,
              Real.exp
                (∑ i : Fin N,
                  (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) * (spin N σ i))) := by
    have hZne : Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0) ≠ 0 :=
      Z_ne_zero (N := N) (H := hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0)
    have hL :
        (∑ σ : Config N,
            gibbs_pmf N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0) σ
              *
              Real.exp
                ((β * (N : ℝ)) * finVecDot M z (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
                  - ((β * (N : ℝ)) / 2) * finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ σ)))
          =
          (Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))⁻¹
            *
            (∑ σ : Config N,
                Real.exp (-(hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0) σ)
                  *
                  Real.exp
                    ((β * (N : ℝ)) * finVecDot M z (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
                      - ((β * (N : ℝ)) / 2) *
                          finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ σ))) := by
      simp [gibbs_pmf, div_eq_mul_inv, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    have hH :=
      exp_neg_hopfieldEnergyWithField_eq (N := N) (M := M) (β := β) (h := h) (Ξ := Ξ) (k0 := k0)
    have hdot' (σ : Config N) :
        (β * (N : ℝ)) * finVecDot M z (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
          =
          ∑ i : Fin N, (β * hopfieldEtaDot (N := N) (M := M) Ξ i z) * (spin N σ i) := by
      have h0 :=
        finVecDot_overlapVec (N := N) (M := M) (Ξ := Ξ) z σ
      have hβ := congrArg (fun t : ℝ => β * t) h0
      simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hβ
    have hfield' (σ : Config N) :
        (h * (N : ℝ)) * hopfieldOverlapVec (N := N) (M := M) Ξ σ k0
          =
          ∑ i : Fin N, (h) * (spin N σ i) := by
      have hpat : ∀ i : Fin N, spin N (Ξ k0) i = 1 := by
        intro i
        have : hopfieldEta (N := N) (M := M) Ξ i k0 = 1 :=
          hopfieldEta_eq_one_of_isConstantPattern (N := N) (Ξ := Ξ) (k0 := k0) hΞ i
        simpa [hopfieldEta] using this
      have hk0 :
          hopfieldOverlapVec (N := N) (M := M) Ξ σ k0
            =
            (1 / (N : ℝ)) * ∑ i : Fin N, spin N σ i := by
        simp [hopfieldOverlapVec, hopfieldOverlap, hpat, mul_one, mul_assoc, mul_left_comm, mul_comm]
      by_cases hN0 : N = 0
      · subst hN0
        simp [hk0]
      · have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN0
        simp [hk0, div_eq_mul_inv, hN', Finset.mul_sum, mul_assoc, mul_comm]
    -- Pointwise HS cancellation:
    have hpoint (σ : Config N) :
        Real.exp (-(hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0) σ)
            *
            Real.exp
              ((β * (N : ℝ)) * finVecDot M z (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
                - ((β * (N : ℝ)) / 2) * finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ σ))
          =
          Real.exp
            (∑ i : Fin N, (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) * spin N σ i) := by
      have hHσ := hH σ
      have hnorm :
          (∑ k : Fin M, (hopfieldOverlapVec (N := N) (M := M) Ξ σ k) ^ 2)
            =
            finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ σ) := by
        simp [finVecNormSq]
      calc
        Real.exp (-(hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0) σ)
            *
            Real.exp
              ((β * (N : ℝ)) * finVecDot M z (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
                - ((β * (N : ℝ)) / 2) * finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ σ))
            =
            Real.exp
              (((β * (N : ℝ)) / 2) * finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
                + (h * (N : ℝ)) * hopfieldOverlapVec (N := N) (M := M) Ξ σ k0)
              *
              Real.exp
                ((β * (N : ℝ)) * finVecDot M z (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
                  - ((β * (N : ℝ)) / 2) * finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ σ)) := by
              simp [hHσ, hnorm]
        _ =
            Real.exp
              (((β * (N : ℝ)) / 2) * finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
                + (h * (N : ℝ)) * hopfieldOverlapVec (N := N) (M := M) Ξ σ k0
                + ((β * (N : ℝ)) * finVecDot M z (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
                  - ((β * (N : ℝ)) / 2) * finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ σ))) := by
              simp [Real.exp_add, mul_assoc, mul_left_comm, mul_comm, add_assoc]
        _ =
            Real.exp
              ((h * (N : ℝ)) * hopfieldOverlapVec (N := N) (M := M) Ξ σ k0
                + (β * (N : ℝ)) * finVecDot M z (hopfieldOverlapVec (N := N) (M := M) Ξ σ)) := by
              ring_nf
        _ =
            Real.exp
              ((∑ i : Fin N, (h) * spin N σ i)
                + ∑ i : Fin N, (β * hopfieldEtaDot (N := N) (M := M) Ξ i z) * spin N σ i) := by
              simp [hfield' σ, hdot' σ, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
        _ =
            Real.exp
              (∑ i : Fin N, (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) * spin N σ i) := by
              simp [Finset.sum_add_distrib, add_mul, mul_add, add_assoc, add_left_comm, add_comm]
    have hR :
        (Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))⁻¹
            *
            (∑ σ : Config N,
                Real.exp (-(hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0) σ)
                  *
                  Real.exp
                    ((β * (N : ℝ)) * finVecDot M z (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
                      - ((β * (N : ℝ)) / 2) *
                          finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ σ)))
          =
          (Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))⁻¹
            *
            (∑ σ : Config N,
              Real.exp
                (∑ i : Fin N,
                  (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) * spin N σ i)) := by
      refine congrArg (fun t => (Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))⁻¹ * t) ?_
      apply Finset.sum_congr rfl
      intro σ _hσ
      simpa [mul_comm, mul_left_comm, mul_assoc] using (hpoint σ)
    simpa [hL] using hR
  have hlin' : (∫⁻ σ : Config N,
          ENNReal.ofReal
            (Real.exp
              ((β * (N : ℝ)) * finVecDot M z (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
                - ((β * (N : ℝ)) / 2) * finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ σ)))
        ∂gibbsMeasure (N := N) (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))
        =
        ENNReal.ofReal
          ((Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))⁻¹
            *
            ((2 : ℝ) ^ N
              * Real.exp (∑ i : Fin N,
                  Real.log (Real.cosh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h))))) := by
    have hspin :=
      sum_exp_hopfield_linear_eq_two_pow_mul_exp_sum_log_cosh
        (N := N) (M := M) (β := β) (h := h) (Ξ := Ξ) z
    calc
      (∫⁻ σ : Config N,
            ENNReal.ofReal
              (Real.exp
                ((β * (N : ℝ)) * finVecDot M z (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
                  - ((β * (N : ℝ)) / 2) * finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ σ)))
          ∂gibbsMeasure (N := N) (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))
          =
          ENNReal.ofReal
            (∑ σ : Config N,
              gibbs_pmf N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0) σ
                *
                Real.exp
                  ((β * (N : ℝ)) * finVecDot M z (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
                    - ((β * (N : ℝ)) / 2) * finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ σ))) := hlin
      _ =
          ENNReal.ofReal
            ((Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))⁻¹
              *
              ∑ σ : Config N,
                Real.exp
                  (∑ i : Fin N, (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) * spin N σ i)) := by
            simp [hsum]
      _ =
          ENNReal.ofReal
            ((Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))⁻¹
              *
              ((2 : ℝ) ^ N
                * Real.exp (∑ i : Fin N,
                    Real.log (Real.cosh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h))))) := by
            simp [hspin, mul_assoc, mul_left_comm, mul_comm]
  have hpsi :
      Real.exp (hopfieldPsi (N := N) (M := M) β h Ξ z)
        =
        Real.exp (-((β * (N : ℝ)) / 2) * finVecNormSq M z)
          *
          Real.exp (∑ i : Fin N, Real.log (Real.cosh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h))) := by
    simp [hopfieldPsi, Real.exp_add, mul_assoc, mul_left_comm, mul_comm]
  rw [hfactor, hlin']
  set A : ℝ :=
    talagrandW (N := N) (M := M) β * Real.exp (-((β * (N : ℝ)) / 2) * finVecNormSq M z)
  set B : ℝ :=
    (Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))⁻¹
      * ((2 : ℝ) ^ N
        * Real.exp (∑ i : Fin N, Real.log (Real.cosh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h))))
  have hA : 0 ≤ A := by
    dsimp [A]
    refine mul_nonneg ?_ (Real.exp_pos _).le
    dsimp [talagrandW]
    exact pow_nonneg (Real.sqrt_nonneg _) _
  have hmul : ENNReal.ofReal A * ENNReal.ofReal B = ENNReal.ofReal (A * B) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (ENNReal.ofReal_mul (p := A) (q := B) hA).symm
  rw [hmul]
  have hexp :
      Real.exp (-((β * (N : ℝ)) / 2) * finVecNormSq M z)
          *
          Real.exp (∑ i : Fin N, Real.log (Real.cosh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h)))
        =
        Real.exp (hopfieldPsi (N := N) (M := M) β h Ξ z) := by
    simp [hpsi, mul_assoc, mul_left_comm, mul_comm]
  have hB : 0 ≤ B := by
    dsimp [B]
    refine mul_nonneg ?_ (mul_nonneg (pow_nonneg (by norm_num) _) (Real.exp_pos _).le)
    have hZpos : 0 < Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0) :=
      Z_pos (N := N) (H := hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0)
    exact inv_nonneg.2 (le_of_lt hZpos)
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have hC : 0 ≤
      (talagrandW (N := N) (M := M) β * (2 : ℝ) ^ N / Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0)
            * Real.exp (hopfieldPsi (N := N) (M := M) β h Ξ z)) := by
    have hZpos : 0 < Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0) :=
      Z_pos (N := N) (H := hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0)
    have hZinv : 0 ≤ (Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))⁻¹ :=
      inv_nonneg.2 (le_of_lt hZpos)
    have hW : 0 ≤ talagrandW (N := N) (M := M) β := by
      dsimp [talagrandW]
      exact pow_nonneg (Real.sqrt_nonneg _) _
    have hpow : 0 ≤ ((2 : ℝ) ^ N) := pow_nonneg (by norm_num) _
    have hexp' : 0 ≤ Real.exp (hopfieldPsi (N := N) (M := M) β h Ξ z) := (Real.exp_pos _).le
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      mul_nonneg (mul_nonneg (mul_nonneg hW hpow) hZinv) hexp'
  refine (ENNReal.ofReal_eq_ofReal_iff hAB hC).2 ?_
  dsimp [A, B]
  have hZpos : 0 < Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0) :=
    Z_pos (N := N) (H := hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0)
  calc
    talagrandW (N := N) (M := M) β * Real.exp (-((β * (N : ℝ)) / 2) * finVecNormSq M z) *
        ((Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))⁻¹ *
          ((2 : ℝ) ^ N *
            Real.exp
              (∑ i : Fin N,
                Real.log (Real.cosh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h))))) =
        talagrandW (N := N) (M := M) β * (2 : ℝ) ^ N / Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0) *
          Real.exp (hopfieldPsi (N := N) (M := M) β h Ξ z) := by
      have hexp' :
          Real.exp (hopfieldPsi (N := N) (M := M) β h Ξ z) =
            Real.exp (-((β * (N : ℝ)) / 2) * finVecNormSq M z)
              * Real.exp (∑ i : Fin N,
                  Real.log (Real.cosh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h))) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hexp.symm
      simp [div_eq_mul_inv, hexp', mul_assoc, mul_left_comm, mul_comm]

/-- Kernel-level version of `hopfieldConvolution_overlapImage_talagrandGaussian_eq_withDensity_psi`. -/
theorem hopfieldConvolutionTalagrandKernel_eq_withDensity_psi
    (N M : ℕ) (Ξ : Patterns N M) (β h : ℝ) (k0 : Fin M)
    (hΞ : IsConstantPattern (N := N) Ξ k0)
    (hβ : 0 ≤ β) (hβN : β * (N : ℝ) ≠ 0) :
    hopfieldConvolutionTalagrandKernel (N := N) (M := M) Ξ β
        (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0)
      =
      volume.withDensity (fun z : Fin M → ℝ =>
        ENNReal.ofReal
          ((talagrandW (N := N) (M := M) β) * (2 : ℝ) ^ N / Z N
              (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0)
            * Real.exp (hopfieldPsi (N := N) (M := M) β h Ξ z))) := by
  -- Unfold kernel application and apply the measure-level identity.
  simpa [hopfieldConvolutionTalagrandKernel_apply (Ξ := Ξ) (β := β) hβ hβN] using
    (hopfieldConvolution_overlapImage_talagrandGaussian_eq_withDensity_psi
      (N := N) (M := M) (Ξ := Ξ) (β := β) (h := h) (k0 := k0) hΞ)

/-- Normalization identity obtained by integrating the `ψ`-density formula over `volume`.

This is the “partition function consistency” statement: if the Gaussian input measure is a
probability measure, then the RHS density integrates to `1`. This lemma is the clean bridge
from Talagrand’s exact finite-volume `ψ`-representation to later asymptotic analysis. -/
theorem lintegral_hopfieldPsi_density_eq_one
    (N M : ℕ) (Ξ : Patterns N M) (β h : ℝ) (k0 : Fin M)
    (hΞ : IsConstantPattern (N := N) Ξ k0)
    (hβ : 0 ≤ β) (hβN : β * (N : ℝ) ≠ 0) :
    (∫⁻ z : Fin M → ℝ,
        ENNReal.ofReal
          ((talagrandW (N := N) (M := M) β) * (2 : ℝ) ^ N
              / Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0)
              * Real.exp (hopfieldPsi (N := N) (M := M) β h Ξ z))
        ∂(volume : Measure (Fin M → ℝ)))
      = 1 := by
  haveI : IsProbabilityMeasure (talagrandGaussianMeasureDensity (N := N) (M := M) β) :=
    instIsProbabilityMeasure_talagrandGaussianMeasureDensity (N := N) (M := M) (β := β) hβ hβN
  have hψ :=
    hopfieldConvolution_overlapImage_talagrandGaussian_eq_withDensity_psi
      (N := N) (M := M) (Ξ := Ξ) (β := β) (h := h) (k0 := k0) hΞ
  -- The LHS is a convolution of two probability measures, hence has mass `1` on `univ`.
  haveI :
      IsProbabilityMeasure
        (hopfieldOverlapImageMeasure (N := N) (M := M) Ξ
          (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0)) := by
    -- `Measure.map` preserves the probability measure property.
    dsimp [hopfieldOverlapImageMeasure]
    have hmeas : Measurable (hopfieldOverlapVec (N := N) (M := M) Ξ) := by fun_prop
    simpa using
      (Measure.isProbabilityMeasure_map (μ := gibbsMeasure (N := N) (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))
        (f := hopfieldOverlapVec (N := N) (M := M) Ξ) hmeas.aemeasurable)
  haveI :
      IsProbabilityMeasure
        (hopfieldConvolution (M := M)
          (hopfieldOverlapImageMeasure (N := N) (M := M) Ξ
            (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))
          (talagrandGaussianMeasureDensity (N := N) (M := M) β)) := by
    infer_instance
  have hmass :
      (hopfieldConvolution (M := M)
          (hopfieldOverlapImageMeasure (N := N) (M := M) Ξ
            (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))
          (talagrandGaussianMeasureDensity (N := N) (M := M) β)) Set.univ = 1 := by
    simpa using (measure_univ :
      (hopfieldConvolution (M := M)
          (hopfieldOverlapImageMeasure (N := N) (M := M) Ξ
            (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))
          (talagrandGaussianMeasureDensity (N := N) (M := M) β)) Set.univ = 1)
  have hmass' :
      (volume.withDensity (fun z : Fin M → ℝ =>
          ENNReal.ofReal
            ((talagrandW (N := N) (M := M) β) * (2 : ℝ) ^ N
                / Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0)
                * Real.exp (hopfieldPsi (N := N) (M := M) β h Ξ z)))) Set.univ
        =
        (∫⁻ z : Fin M → ℝ,
          ENNReal.ofReal
            ((talagrandW (N := N) (M := M) β) * (2 : ℝ) ^ N
                / Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0)
                * Real.exp (hopfieldPsi (N := N) (M := M) β h Ξ z))
          ∂(volume : Measure (Fin M → ℝ))) := by
    simp [MeasureTheory.withDensity_apply, MeasurableSet.univ]
  have huniv :
      (hopfieldConvolution (M := M)
          (hopfieldOverlapImageMeasure (N := N) (M := M) Ξ
            (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))
          (talagrandGaussianMeasureDensity (N := N) (M := M) β)) Set.univ
        =
        (volume.withDensity (fun z : Fin M → ℝ =>
          ENNReal.ofReal
            ((talagrandW (N := N) (M := M) β) * (2 : ℝ) ^ N
                / Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0)
                * Real.exp (hopfieldPsi (N := N) (M := M) β h Ξ z)))) Set.univ := by
    simpa using congrArg (fun μ : Measure (Fin M → ℝ) => μ Set.univ) hψ
  calc
    (∫⁻ z : Fin M → ℝ,
        ENNReal.ofReal
          ((talagrandW (N := N) (M := M) β) * (2 : ℝ) ^ N
              / Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0)
              * Real.exp (hopfieldPsi (N := N) (M := M) β h Ξ z))
        ∂(volume : Measure (Fin M → ℝ)))
        =
        (volume.withDensity (fun z : Fin M → ℝ =>
          ENNReal.ofReal
            ((talagrandW (N := N) (M := M) β) * (2 : ℝ) ^ N
                / Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0)
                * Real.exp (hopfieldPsi (N := N) (M := M) β h Ξ z)))) Set.univ := by
          simpa using hmass'.symm
    _ =
        (hopfieldConvolution (M := M)
          (hopfieldOverlapImageMeasure (N := N) (M := M) Ξ
            (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))
          (talagrandGaussianMeasureDensity (N := N) (M := M) β)) Set.univ := by
          simpa using huniv.symm
    _ = 1 := hmass

end SpinGlass
