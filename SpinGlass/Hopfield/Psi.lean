/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.HopfieldConvolution

/-!
# Talagrand's `ψ`-representation of the Hopfield overlap convolution

The convolution of the overlap pushforward against Talagrand's Gaussian, presented as a kernel and
then identified with a `withDensity` measure whose density is Talagrand's `ψ`. This is the content
of Vol. I, Lemma 4.2.1.
-/

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ENNReal NNReal

namespace SpinGlass

variable {N M : ℕ}

open SpinGlass.KernelBridge

/-! ### Hopfield convolution against Talagrand Gaussian, as a kernel -/

/-- Convolution kernel specialized to Talagrand’s Gaussian input measure. -/
noncomputable def hopfieldConvolutionTalagrandKernel
    {N M : ℕ} (Ξ : Patterns N M) (β : ℝ) :
    ProbabilityTheory.Kernel (EnergySpace N) (Fin M → ℝ) :=
  hopfieldConvolutionKernel (N := N) (M := M) Ξ
    (talagrandGaussianMeasureDensity (N := N) (M := M) β)

/-- The Talagrand-Gaussian convolution kernel is Markov for `0 ≤ β` and `β * N ≠ 0`. -/
lemma isMarkovKernel_hopfieldConvolutionTalagrandKernel
    {N M : ℕ} (Ξ : Patterns N M) (β : ℝ) (hβ : 0 ≤ β) (hβN : β * (N : ℝ) ≠ 0) :
    ProbabilityTheory.IsMarkovKernel (hopfieldConvolutionTalagrandKernel (N := N) (M := M) Ξ β) :=
      by
  have : IsProbabilityMeasure (talagrandGaussianMeasureDensity (N := N) (M := M) β) :=
    isProbabilityMeasure_talagrandGaussianMeasureDensity (N := N) (M := M) (β := β) hβ hβN
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
  have : IsProbabilityMeasure (talagrandGaussianMeasureDensity (N := N) (M := M) β) :=
    isProbabilityMeasure_talagrandGaussianMeasureDensity (N := N) (M := M) (β := β) hβ hβN
  have : SFinite (talagrandGaussianMeasureDensity (N := N) (M := M) β) := by infer_instance
  simp [hopfieldConvolutionTalagrandKernel]

/-! ### Talagrand Gaussian as a constant kernel (Vol II style) -/

/-- Talagrand’s Gaussian measure packaged as a constant kernel. -/
noncomputable def talagrandGaussianKernelDensity
    (N M : ℕ) (β : ℝ) : ProbabilityTheory.Kernel (EnergySpace N) (Fin M → ℝ) :=
  ProbabilityTheory.Kernel.const (EnergySpace N) (talagrandGaussianMeasureDensity (N := N) (M := M)
    β)

/-- The constant Talagrand-Gaussian kernel is Markov for `0 ≤ β` and `β * N ≠ 0`. -/
lemma isMarkovKernel_talagrandGaussianKernelDensity
    (N M : ℕ) (β : ℝ) (hβ : 0 ≤ β) (hβN : β * (N : ℝ) ≠ 0) :
    ProbabilityTheory.IsMarkovKernel (talagrandGaussianKernelDensity (N := N) (M := M) β) := by
  have :
      IsProbabilityMeasure (talagrandGaussianMeasureDensity (N := N) (M := M) β) :=
    isProbabilityMeasure_talagrandGaussianMeasureDensity (N := N) (M := M) (β := β) hβ hβN
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
  have : IsFiniteMeasure (hopfieldOverlapImageMeasure (N := N) (M := M) Ξ H) := by
    dsimp [hopfieldOverlapImageMeasure]
    infer_instance
  have : SigmaFinite (hopfieldOverlapImageMeasure (N := N) (M := M) Ξ H) := by infer_instance
  have : SFinite (hopfieldOverlapImageMeasure (N := N) (M := M) Ξ H) := by infer_instance
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
          * Real.exp ((β * (N : ℝ)) * finVecDot M z m - ((β * (N : ℝ)) / 2) * finVecNormSq M m) :=
            by
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
          * Real.exp ((β * (N : ℝ)) * finVecDot M z m - ((β * (N : ℝ)) / 2) * finVecNormSq M m) :=
            by
    simpa [neg_mul, mul_assoc] using hexp
  dsimp [talagrandGaussianDensity]
  simp only [neg_mul, hexp', mul_assoc] at *
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
            simp [finVecDot, hm]
      _ =
          (N : ℝ) * ((1 / (N : ℝ)) * ∑ k : Fin M, z k * ∑ i : Fin N,
            hopfieldEta (N := N) (M := M) Ξ i k * spin N σ i) := by
            simp [Finset.mul_sum, mul_left_comm, mul_comm, div_eq_mul_inv]
      _ =
          ∑ k : Fin M, z k * ∑ i : Fin N,
            hopfieldEta (N := N) (M := M) Ξ i k * spin N σ i := by
            simp [div_eq_mul_inv, hN', mul_comm]
      _ =
          ∑ i : Fin N, (∑ k : Fin M, hopfieldEta (N := N) (M := M) Ξ i k * z k) * spin N σ i := by
            have :
                (∑ k : Fin M, z k * ∑ i : Fin N, hopfieldEta (N := N) (M := M) Ξ i k * spin N σ i)
                  =
                  ∑ k : Fin M, ∑ i : Fin N, z k * (hopfieldEta (N := N) (M := M) Ξ i k * spin N σ i)
                    := by
                refine Finset.sum_congr rfl ?_
                intro k _hk
                simp [Finset.mul_sum]
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
  simpa [gibbsMeasure, FiniteGibbs.gibbsMeasure, gibbs_pmf, FiniteGibbs.gibbs_pmf, Z, FiniteGibbs.Z]
    using
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

/-- Finite-volume `ψ`-density of the overlap convolution, under `IsConstantPattern`, normalized by
`Z`. -/
theorem hopfieldConvolution_overlapImage_talagrandGaussian_eq_withDensity_psi
    (N M : ℕ) (Ξ : Patterns N M) (β h : ℝ) (k0 : Fin M)
    (hΞ : IsConstantPattern (N := N) Ξ k0) :
    hopfieldConvolution (M := M)
        (hopfieldOverlapImageMeasure (N := N) (M := M) Ξ (hopfieldEnergyWithField (N := N) (M := M)
          β h Ξ k0))
        (talagrandGaussianMeasureDensity (N := N) (M := M) β)
      =
      volume.withDensity (fun z : Fin M → ℝ =>
        ENNReal.ofReal
          ((talagrandW (N := N) (M := M) β) * (2 : ℝ) ^ N / Z N (hopfieldEnergyWithField (N := N) (M
            := M) β h Ξ k0)
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
                  - ((β * (N : ℝ)) / 2) * finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ
                    σ)))
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
        simp [hopfieldOverlapVec, hopfieldOverlap, hpat, mul_comm]
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
                  - ((β * (N : ℝ)) / 2) * finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ σ))
                    := by
              simp [hHσ, hnorm]
        _ =
            Real.exp
              (((β * (N : ℝ)) / 2) * finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
                + (h * (N : ℝ)) * hopfieldOverlapVec (N := N) (M := M) Ξ σ k0
                + ((β * (N : ℝ)) * finVecDot M z (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
                  - ((β * (N : ℝ)) / 2) * finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ
                    σ))) := by
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
              simp [hfield' σ, hdot' σ, mul_assoc]
        _ =
            Real.exp
              (∑ i : Fin N, (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) * spin N σ i) := by
              simp [Finset.sum_add_distrib, add_mul, add_comm]
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
                  - ((β * (N : ℝ)) / 2) * finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ
                    σ)))
          ∂gibbsMeasure (N := N) (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))
          =
          ENNReal.ofReal
            (∑ σ : Config N,
              gibbs_pmf N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0) σ
                *
                Real.exp
                  ((β * (N : ℝ)) * finVecDot M z (hopfieldOverlapVec (N := N) (M := M) Ξ σ)
                    - ((β * (N : ℝ)) / 2) * finVecNormSq M (hopfieldOverlapVec (N := N) (M := M) Ξ
                      σ))) := hlin
      _ =
          ENNReal.ofReal
            ((Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))⁻¹
              *
              ∑ σ : Config N,
                Real.exp
                  (∑ i : Fin N, (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h) * spin N σ i)) :=
                    by
            simp [hsum]
      _ =
          ENNReal.ofReal
            ((Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))⁻¹
              *
              ((2 : ℝ) ^ N
                * Real.exp (∑ i : Fin N,
                    Real.log (Real.cosh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h))))) := by
            simp [hspin, mul_left_comm]
  have hpsi :
      Real.exp (hopfieldPsi (N := N) (M := M) β h Ξ z)
        =
        Real.exp (-((β * (N : ℝ)) / 2) * finVecNormSq M z)
          *
          Real.exp (∑ i : Fin N, Real.log (Real.cosh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z +
            h))) := by
    simp [hopfieldPsi, Real.exp_add, mul_comm]
  rw [hfactor, hlin']
  set A : ℝ :=
    talagrandW (N := N) (M := M) β * Real.exp (-((β * (N : ℝ)) / 2) * finVecNormSq M z)
  set B : ℝ :=
    (Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))⁻¹
      * ((2 : ℝ) ^ N
        * Real.exp (∑ i : Fin N, Real.log (Real.cosh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z +
          h))))
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
          Real.exp (∑ i : Fin N, Real.log (Real.cosh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z +
            h)))
        =
        Real.exp (hopfieldPsi (N := N) (M := M) β h Ξ z) := by
    simp [hpsi]
  have hB : 0 ≤ B := by
    dsimp [B]
    refine mul_nonneg ?_ (mul_nonneg (pow_nonneg (by norm_num) _) (Real.exp_pos _).le)
    have hZpos : 0 < Z N (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0) :=
      Z_pos (N := N) (H := hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0)
    exact inv_nonneg.2 (le_of_lt hZpos)
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have hC : 0 ≤
      (talagrandW (N := N) (M := M) β * (2 : ℝ) ^ N / Z N (hopfieldEnergyWithField (N := N) (M := M)
        β h Ξ k0)
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
        talagrandW (N := N) (M := M) β * (2 : ℝ) ^ N / Z N (hopfieldEnergyWithField (N := N) (M :=
          M) β h Ξ k0) *
          Real.exp (hopfieldPsi (N := N) (M := M) β h Ξ z) := by
      have hexp' :
          Real.exp (hopfieldPsi (N := N) (M := M) β h Ξ z) =
            Real.exp (-((β * (N : ℝ)) / 2) * finVecNormSq M z)
              * Real.exp (∑ i : Fin N,
                  Real.log (Real.cosh (β * hopfieldEtaDot (N := N) (M := M) Ξ i z + h))) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hexp.symm
      simp [div_eq_mul_inv, hexp', mul_assoc, mul_left_comm, mul_comm]

/-- Kernel-level version of
`hopfieldConvolution_overlapImage_talagrandGaussian_eq_withDensity_psi`. -/
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

/-- The Hopfield `ψ`-density integrates to `1` over `volume`. -/
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
  have : IsProbabilityMeasure (talagrandGaussianMeasureDensity (N := N) (M := M) β) :=
    isProbabilityMeasure_talagrandGaussianMeasureDensity (N := N) (M := M) (β := β) hβ hβN
  have hψ :=
    hopfieldConvolution_overlapImage_talagrandGaussian_eq_withDensity_psi
      (N := N) (M := M) (Ξ := Ξ) (β := β) (h := h) (k0 := k0) hΞ
  -- The LHS is a convolution of two probability measures, hence has mass `1` on `univ`.
  have :
      IsProbabilityMeasure
        (hopfieldOverlapImageMeasure (N := N) (M := M) Ξ
          (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0)) := by
    -- `Measure.map` preserves the probability measure property.
    dsimp [hopfieldOverlapImageMeasure]
    have hmeas : Measurable (hopfieldOverlapVec (N := N) (M := M) Ξ) := by fun_prop
    simpa using
      (Measure.isProbabilityMeasure_map (μ := gibbsMeasure (N := N) (hopfieldEnergyWithField (N :=
        N) (M := M) β h Ξ k0))
        (f := hopfieldOverlapVec (N := N) (M := M) Ξ) hmeas.aemeasurable)
  have :
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
    simp
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
          simp
    _ =
        (hopfieldConvolution (M := M)
          (hopfieldOverlapImageMeasure (N := N) (M := M) Ξ
            (hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0))
          (talagrandGaussianMeasureDensity (N := N) (M := M) β)) Set.univ := by
          simpa using huniv.symm
    _ = 1 := hmass

end SpinGlass
