import SpinGlass.HopfieldConvolution
import SpinGlass.Cascades.GhirlandaGuerra
import SpinGlass.Cascades.Posterior
import Mathlib.Probability.Kernel.Composition.ParallelComp

/-!
# Hopfield × Cascades

Hopfield overlap-vector replica laws as inputs to `Cascades/GhirlandaGuerra`. Main:
`hopfieldOverlapPosteriorPredictive`, `HopfieldOverlap_GG1Kernel`.
Talagrand Vol. I, §4.2 / Vol. II.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory ENNReal

namespace SpinGlass
namespace Cascades

variable {N M n : ℕ}

/-! ## Replica laws of Hopfield overlap arrays -/

/-- The overlap-array law of `n` replicas induced by `μH`. -/
noncomputable def hopfieldOverlapLaw (Ξ : Patterns N M)
    (μH : Measure (EnergySpace N)) [IsProbabilityMeasure μH] :
    Measure (Fin n → (Fin M → ℝ)) :=
  (hopfieldOverlapArrayKernel (N := N) (M := M) (n := n) Ξ) ∘ₘ μH

instance (Ξ : Patterns N M) (μH : Measure (EnergySpace N)) [IsProbabilityMeasure μH] :
    IsProbabilityMeasure (hopfieldOverlapLaw (N := N) (M := M) (n := n) Ξ μH) := by
  classical
  dsimp [hopfieldOverlapLaw]
  infer_instance

/-- The overlap-array replica law induced by a disorder law `μH` on energies. -/
noncomputable def hopfieldOverlapReplicaLaw (Ξ : Patterns N M)
    (μH : Measure (EnergySpace N)) [IsProbabilityMeasure μH] :
    Measure (Fin (n + 1) → (Fin M → ℝ)) :=
  (hopfieldOverlapArrayKernel (N := N) (M := M) (n := n + 1) Ξ) ∘ₘ μH

instance (Ξ : Patterns N M) (μH : Measure (EnergySpace N)) [IsProbabilityMeasure μH] :
    IsProbabilityMeasure (hopfieldOverlapReplicaLaw (N := N) (M := M) (n := n) Ξ μH) := by
  classical
  dsimp [hopfieldOverlapReplicaLaw]
  infer_instance

/-! ## GG₁ statements for Hopfield overlap-vector laws -/

/-- GG₁ for the Hopfield overlap-vector replica law. -/
def Hopfield_GG1 (Ξ : Patterns N M)
    (μH : Measure (EnergySpace N)) [IsProbabilityMeasure μH]
    (R : (Fin M → ℝ) → (Fin M → ℝ) → ℝ) : Prop :=
  GG1 (β := (Fin M → ℝ)) n (hopfieldOverlapReplicaLaw (N := N) (M := M) (n := n) Ξ μH) R

/-- GG₁ stated at kernel level for Hopfield overlap-vector laws. -/
def Hopfield_GG1Kernel (Ξ : Patterns N M)
    (μH : Measure (EnergySpace N)) [IsProbabilityMeasure μH]
    (R : (Fin M → ℝ) → (Fin M → ℝ) → ℝ) : Prop :=
  GG1Kernel (β := (Fin M → ℝ)) n μH
    (hopfieldOverlapArrayKernel (N := N) (M := M) (n := n + 1) Ξ) R

@[simp] lemma Hopfield_GG1Kernel_iff (Ξ : Patterns N M)
    (μH : Measure (EnergySpace N)) [IsProbabilityMeasure μH]
    (R : (Fin M → ℝ) → (Fin M → ℝ) → ℝ) :
    Hopfield_GG1Kernel (N := N) (M := M) (n := n) Ξ μH R
      ↔
    Hopfield_GG1 (N := N) (M := M) (n := n) Ξ μH R := by
  rfl

/-! ## Conditional law of the last overlap vector given the prefix -/

/-- Conditional law of the last overlap vector given the first `n`, under the Hopfield replica law. -/
noncomputable def hopfieldCondDistribLast (Ξ : Patterns N M)
    (μH : Measure (EnergySpace N)) [IsProbabilityMeasure μH] :
    ProbabilityTheory.Kernel (Fin n → (Fin M → ℝ)) (Fin M → ℝ) :=
  condDistribLast (β := (Fin M → ℝ)) n (hopfieldOverlapReplicaLaw (N := N) (M := M) (n := n) Ξ μH)

lemma hopfieldCondDistribLast_comp_prefix (Ξ : Patterns N M)
    (μH : Measure (EnergySpace N)) [IsProbabilityMeasure μH] :
    hopfieldCondDistribLast (N := N) (M := M) (n := n) Ξ μH
        ∘ₘ ((hopfieldOverlapReplicaLaw (N := N) (M := M) (n := n) Ξ μH).map
          (restrictReplicas (β := (Fin M → ℝ)) n))
      =
      (hopfieldOverlapReplicaLaw (N := N) (M := M) (n := n) Ξ μH).map
        (lastReplica (β := (Fin M → ℝ)) n) := by
  classical
  -- This is a direct specialization of `condDistribLast_comp_prefix`.
  simpa [hopfieldCondDistribLast] using
    (condDistribLast_comp_prefix (β := (Fin M → ℝ)) (n := n)
      (μ := hopfieldOverlapReplicaLaw (N := N) (M := M) (n := n) Ξ μH))

/-! ## Posterior-predictive kernels for Hopfield observables -/

open SpinGlass.KernelBridge

/-- Posterior predictive for a fresh overlap vector, given `n` replicas and prior `μH`. -/
noncomputable def hopfieldOverlapPosteriorPredictive (Ξ : Patterns N M)
    (μH : Measure (EnergySpace N)) [IsProbabilityMeasure μH] :
    ProbabilityTheory.Kernel (ReplicaSpace N n) (Fin M → ℝ) :=
  (hopfieldOverlapKernel (N := N) (M := M) Ξ) ∘ₖ
    (gibbsPosteriorKernel (N := N) (n := n) μH)

instance (Ξ : Patterns N M) (μH : Measure (EnergySpace N)) [IsProbabilityMeasure μH] :
    ProbabilityTheory.IsMarkovKernel (hopfieldOverlapPosteriorPredictive (N := N) (M := M) (n := n) Ξ μH) := by
  classical
  dsimp [hopfieldOverlapPosteriorPredictive]
  infer_instance

/-- Posterior predictive for the Gaussian-convolved overlap `z`. Talagrand Vol. I, §4.2. -/
noncomputable def hopfieldTalagrandPosteriorPredictive (Ξ : Patterns N M) (β : ℝ)
    (μH : Measure (EnergySpace N)) [IsProbabilityMeasure μH] :
    ProbabilityTheory.Kernel (ReplicaSpace N n) (Fin M → ℝ) :=
  (hopfieldConvolutionTalagrandKernel (N := N) (M := M) Ξ β) ∘ₖ
    (gibbsPosteriorKernel (N := N) (n := n) μH)

instance (Ξ : Patterns N M) (β : ℝ) (μH : Measure (EnergySpace N)) [IsProbabilityMeasure μH]
    (hβ : 0 ≤ β) (hβN : β * (N : ℝ) ≠ 0) :
    ProbabilityTheory.IsMarkovKernel (hopfieldTalagrandPosteriorPredictive (N := N) (M := M) (n := n) Ξ β μH) := by
  classical
  -- need the Markov property of the Talagrand convolution kernel
  haveI : ProbabilityTheory.IsMarkovKernel (hopfieldConvolutionTalagrandKernel (N := N) (M := M) Ξ β) :=
    instIsMarkovKernel_hopfieldConvolutionTalagrandKernel (N := N) (M := M) (Ξ := Ξ) (β := β) hβ hβN
  dsimp [hopfieldTalagrandPosteriorPredictive]
  infer_instance

end Cascades

/-! ## Patterns `Ξ` as environment -/

namespace Cascades

variable {N M : ℕ}

section PatternsEnvironment

variable (β h : ℝ) (k0 : Fin M)
variable (μΞ : Measure (Patterns N M)) [IsProbabilityMeasure μΞ]

/-- The deterministic Hopfield energy (with field) viewed as a function of the environment `Ξ`. -/
noncomputable def hopfieldEnergyWithFieldOfPatterns (Ξ : Patterns N M) : EnergySpace N :=
  hopfieldEnergyWithField (N := N) (M := M) β h Ξ k0

@[measurability] lemma measurable_hopfieldEnergyWithFieldOfPatterns :
    Measurable (hopfieldEnergyWithFieldOfPatterns (N := N) (M := M) (β := β) (h := h) k0) := by
  simpa [hopfieldEnergyWithFieldOfPatterns] using
    (measurable_of_finite (hopfieldEnergyWithFieldOfPatterns (N := N) (M := M) (β := β) (h := h) k0))

/-- The induced disorder law on energies, obtained by pushing `μΞ` forward along `Ξ ↦ H(Ξ)`. -/
noncomputable def hopfieldEnergyLawWithField : Measure (EnergySpace N) :=
  μΞ.map (hopfieldEnergyWithFieldOfPatterns (N := N) (M := M) (β := β) (h := h) k0)

instance : IsProbabilityMeasure (hopfieldEnergyLawWithField (N := N) (M := M) (β := β) (h := h) k0 μΞ) := by
  have hf :
      AEMeasurable (hopfieldEnergyWithFieldOfPatterns (N := N) (M := M) (β := β) (h := h) k0) μΞ :=
    (measurable_hopfieldEnergyWithFieldOfPatterns (N := N) (M := M) (β := β) (h := h) (k0 := k0)).aemeasurable
  simpa [hopfieldEnergyLawWithField] using (Measure.isProbabilityMeasure_map (μ := μΞ) hf)

/-- Deterministic kernel `Ξ ↦ H(Ξ)` (the Hopfield environment-to-energy map). -/
noncomputable def hopfieldEnergyWithFieldKernel :
    ProbabilityTheory.Kernel (Patterns N M) (EnergySpace N) :=
  ProbabilityTheory.Kernel.deterministic
    (hopfieldEnergyWithFieldOfPatterns (N := N) (M := M) (β := β) (h := h) k0)
    (measurable_hopfieldEnergyWithFieldOfPatterns (N := N) (M := M) (β := β) (h := h) (k0 := k0))

instance : ProbabilityTheory.IsMarkovKernel (hopfieldEnergyWithFieldKernel (N := N) (M := M) (β := β) (h := h) k0) := by
  dsimp [hopfieldEnergyWithFieldKernel]
  infer_instance

open SpinGlass.KernelBridge

/-- Kernel `Ξ ↦ G_{H(Ξ)}^{⊗(n+1)}` via `hopfieldEnergyWithField` then `replicaGibbsKernel`. -/
noncomputable def hopfieldReplicaKernelWithField (n : ℕ) :
    ProbabilityTheory.Kernel (Patterns N M) (ReplicaSpace N (n + 1)) :=
  (replicaGibbsKernel (N := N) (n := n + 1)) ∘ₖ
    (hopfieldEnergyWithFieldKernel (N := N) (M := M) (β := β) (h := h) k0)

instance (n : ℕ) :
    ProbabilityTheory.IsMarkovKernel (hopfieldReplicaKernelWithField (N := N) (M := M) (β := β) (h := h) k0 n) := by
  dsimp [hopfieldReplicaKernelWithField]
  infer_instance

/-- The induced `(n+1)`-replica law when the environment `Ξ` has prior `μΞ`. -/
noncomputable def hopfieldReplicaLawWithField (n : ℕ) : Measure (ReplicaSpace N (n + 1)) :=
  (hopfieldReplicaKernelWithField (N := N) (M := M) (β := β) (h := h) k0 n) ∘ₘ μΞ

instance (n : ℕ) :
    IsProbabilityMeasure (hopfieldReplicaLawWithField (N := N) (M := M) (β := β) (h := h) k0 μΞ n) := by
  dsimp [hopfieldReplicaLawWithField]
  infer_instance

/-- GG₁ for `hopfieldReplicaKernelWithField` under prior `μΞ`. -/
def Hopfield_SK_GG1Kernel (n : ℕ) : Prop :=
  GG1Kernel (β := Config N) n μΞ
    (hopfieldReplicaKernelWithField (N := N) (M := M) (β := β) (h := h) k0 n) (overlap N)

/-- Measure-level GG₁ statement for the Hopfield replica law under the pattern prior `μΞ`. -/
def Hopfield_SK_GG1 (n : ℕ) : Prop :=
  SK_GG1 (N := N) (n := n) (μ := hopfieldReplicaLawWithField (N := N) (M := M) (β := β) (h := h) k0 μΞ n)

@[simp] lemma Hopfield_SK_GG1Kernel_iff (n : ℕ) :
    Hopfield_SK_GG1Kernel (N := N) (M := M) (β := β) (h := h) k0 μΞ n
      ↔
    Hopfield_SK_GG1 (N := N) (M := M) (β := β) (h := h) k0 μΞ n := by
  rfl

/-! ### Posterior on patterns -/

/-- `r`-replica sampler kernel from patterns `Ξ`. -/
noncomputable def hopfieldReplicaKernel (r : ℕ) :
    ProbabilityTheory.Kernel (Patterns N M) (ReplicaSpace N r) :=
  (replicaGibbsKernel (N := N) (n := r)) ∘ₖ
    (hopfieldEnergyWithFieldKernel (N := N) (M := M) (β := β) (h := h) k0)

instance (r : ℕ) :
    ProbabilityTheory.IsMarkovKernel (hopfieldReplicaKernel (N := N) (M := M) (β := β) (h := h) k0 r) := by
  dsimp [hopfieldReplicaKernel]
  infer_instance

/-- Posterior kernel: law of the pattern family `Ξ` given `r` replicas. -/
noncomputable def hopfieldPosteriorKernel (r : ℕ) :
    ProbabilityTheory.Kernel (ReplicaSpace N r) (Patterns N M) :=
  (hopfieldReplicaKernel (N := N) (M := M) (β := β) (h := h) k0 r)†μΞ

instance (r : ℕ) :
    ProbabilityTheory.IsMarkovKernel (hopfieldPosteriorKernel (N := N) (M := M) (β := β) (h := h) k0 μΞ r) := by
  dsimp [hopfieldPosteriorKernel]
  infer_instance

/-- Kernel from patterns `Ξ` to one fresh Gibbs configuration (through `H(Ξ)`). -/
noncomputable def hopfieldGibbsKernel :
    ProbabilityTheory.Kernel (Patterns N M) (Config N) :=
  (gibbsKernel (N := N)) ∘ₖ (hopfieldEnergyWithFieldKernel (N := N) (M := M) (β := β) (h := h) k0)

instance : ProbabilityTheory.IsMarkovKernel (hopfieldGibbsKernel (N := N) (M := M) (β := β) (h := h) k0) := by
  dsimp [hopfieldGibbsKernel]
  infer_instance

/-- Posterior predictive for a fresh configuration given `r` replicas, under prior `μΞ`. -/
noncomputable def hopfieldPosteriorPredictive (r : ℕ) :
    ProbabilityTheory.Kernel (ReplicaSpace N r) (Config N) :=
  (hopfieldGibbsKernel (N := N) (M := M) (β := β) (h := h) k0) ∘ₖ
    (hopfieldPosteriorKernel (N := N) (M := M) (β := β) (h := h) k0 μΞ r)

instance (r : ℕ) :
    ProbabilityTheory.IsMarkovKernel (hopfieldPosteriorPredictive (N := N) (M := M) (β := β) (h := h) k0 μΞ r) := by
  dsimp [hopfieldPosteriorPredictive]
  infer_instance

/-! ### Overlap kernels under a pattern prior -/

open scoped ProbabilityTheory

/-- Overlap vector `m(σ)` as a function of the pair `(Ξ, σ)`. -/
noncomputable def hopfieldOverlapVecOfPair (p : (Patterns N M) × (Config N)) : Fin M → ℝ :=
  hopfieldOverlapVec (N := N) (M := M) p.1 p.2

@[measurability] lemma measurable_hopfieldOverlapVecOfPair :
    Measurable (hopfieldOverlapVecOfPair (N := N) (M := M)) := by
  simpa [hopfieldOverlapVecOfPair] using
    (measurable_of_finite (hopfieldOverlapVecOfPair (N := N) (M := M)))

/-- Kernel `Ξ ↦ Law(m(σ))` for a fresh Gibbs sample with field. -/
noncomputable def hopfieldPairGibbsKernel :
    ProbabilityTheory.Kernel (Patterns N M) ((Patterns N M) × (Config N)) :=
  let κσ : ProbabilityTheory.Kernel (Patterns N M) (Config N) :=
    hopfieldGibbsKernel (N := N) (M := M) (β := β) (h := h) k0
  (ProbabilityTheory.Kernel.id ∥ₖ κσ) ∘ₖ (ProbabilityTheory.Kernel.copy (Patterns N M))

instance : ProbabilityTheory.IsMarkovKernel (hopfieldPairGibbsKernel (N := N) (M := M) (β := β) (h := h) k0) := by
  dsimp [hopfieldPairGibbsKernel]
  infer_instance

noncomputable def hopfieldOverlapKernelOfPatterns :
    ProbabilityTheory.Kernel (Patterns N M) (Fin M → ℝ) :=
  (hopfieldPairGibbsKernel (N := N) (M := M) (β := β) (h := h) k0).map
    (hopfieldOverlapVecOfPair (N := N) (M := M))

instance : ProbabilityTheory.IsMarkovKernel (hopfieldOverlapKernelOfPatterns (N := N) (M := M) (β := β) (h := h) k0) := by
  have hm : Measurable (hopfieldOverlapVecOfPair (N := N) (M := M)) :=
    measurable_hopfieldOverlapVecOfPair (N := N) (M := M)
  simpa [hopfieldOverlapKernelOfPatterns] using
    (ProbabilityTheory.Kernel.IsMarkovKernel.map
      (κ := hopfieldPairGibbsKernel (N := N) (M := M) (β := β) (h := h) k0)
      (f := hopfieldOverlapVecOfPair (N := N) (M := M)) hm)

/-- The law of a fresh overlap vector `m(σ)` under the pattern prior `μΞ`. -/
noncomputable def hopfieldOverlapLawOfPatterns : Measure (Fin M → ℝ) :=
  (hopfieldOverlapKernelOfPatterns (N := N) (M := M) (β := β) (h := h) k0) ∘ₘ μΞ

instance : IsProbabilityMeasure (hopfieldOverlapLawOfPatterns (N := N) (M := M) (β := β) (h := h) k0 μΞ) := by
  dsimp [hopfieldOverlapLawOfPatterns]
  infer_instance

/-- Overlap array `(m(σ¹), …, m(σʳ))` as a function of `(Ξ, σs)`. -/
noncomputable def hopfieldOverlapArrayOfPair (r : ℕ) (p : (Patterns N M) × (ReplicaSpace N r)) :
    Fin r → (Fin M → ℝ) :=
  hopfieldOverlapArray (N := N) (M := M) (n := r) p.1 p.2

@[measurability] lemma measurable_hopfieldOverlapArrayOfPair (r : ℕ) :
    Measurable (hopfieldOverlapArrayOfPair (N := N) (M := M) r) := by
  simpa [hopfieldOverlapArrayOfPair] using
    (measurable_of_finite (hopfieldOverlapArrayOfPair (N := N) (M := M) r))

/-- Kernel from patterns `Ξ` to the overlap array of `r` replicas sampled from `H(Ξ)`. -/
noncomputable def hopfieldPairReplicaKernel (r : ℕ) :
    ProbabilityTheory.Kernel (Patterns N M) ((Patterns N M) × (ReplicaSpace N r)) :=
  let κr : ProbabilityTheory.Kernel (Patterns N M) (ReplicaSpace N r) :=
    hopfieldReplicaKernel (N := N) (M := M) (β := β) (h := h) k0 r
  (ProbabilityTheory.Kernel.id ∥ₖ κr) ∘ₖ (ProbabilityTheory.Kernel.copy (Patterns N M))

instance (r : ℕ) :
    ProbabilityTheory.IsMarkovKernel (hopfieldPairReplicaKernel (N := N) (M := M) (β := β) (h := h) k0 r) := by
  dsimp [hopfieldPairReplicaKernel]
  infer_instance

noncomputable def hopfieldOverlapArrayKernelOfPatterns (r : ℕ) :
    ProbabilityTheory.Kernel (Patterns N M) (Fin r → (Fin M → ℝ)) :=
  (hopfieldPairReplicaKernel (N := N) (M := M) (β := β) (h := h) k0 r).map
    (hopfieldOverlapArrayOfPair (N := N) (M := M) r)

instance (r : ℕ) :
    ProbabilityTheory.IsMarkovKernel (hopfieldOverlapArrayKernelOfPatterns (N := N) (M := M) (β := β) (h := h) k0 r) := by
  have hm : Measurable (hopfieldOverlapArrayOfPair (N := N) (M := M) r) :=
    measurable_hopfieldOverlapArrayOfPair (N := N) (M := M) r
  simpa [hopfieldOverlapArrayKernelOfPatterns] using
    (ProbabilityTheory.Kernel.IsMarkovKernel.map
      (κ := hopfieldPairReplicaKernel (N := N) (M := M) (β := β) (h := h) k0 r)
      (f := hopfieldOverlapArrayOfPair (N := N) (M := M) r) hm)

/-- The law of the overlap array of `r` replicas under the pattern prior `μΞ`. -/
noncomputable def hopfieldOverlapArrayLawOfPatterns (r : ℕ) : Measure (Fin r → (Fin M → ℝ)) :=
  (hopfieldOverlapArrayKernelOfPatterns (N := N) (M := M) (β := β) (h := h) k0 r) ∘ₘ μΞ

instance (r : ℕ) :
    IsProbabilityMeasure (hopfieldOverlapArrayLawOfPatterns (N := N) (M := M) (β := β) (h := h) k0 μΞ r) := by
  dsimp [hopfieldOverlapArrayLawOfPatterns]
  infer_instance

/-- GG₁ for Hopfield overlap-vector arrays under pattern prior `μΞ`. -/
def HopfieldOverlap_GG1Kernel (n : ℕ) (R : (Fin M → ℝ) → (Fin M → ℝ) → ℝ) : Prop :=
  GG1Kernel (β := (Fin M → ℝ)) n μΞ
    (hopfieldOverlapArrayKernelOfPatterns (N := N) (M := M) (β := β) (h := h) k0 (r := n + 1)) R

/-- Posterior predictive kernel for a fresh overlap vector given `r` observed replicas. -/
noncomputable def hopfieldOverlapPosteriorPredictiveOfPatterns (r : ℕ) :
    ProbabilityTheory.Kernel (ReplicaSpace N r) (Fin M → ℝ) :=
  (hopfieldOverlapKernelOfPatterns (N := N) (M := M) (β := β) (h := h) k0) ∘ₖ
    (hopfieldPosteriorKernel (N := N) (M := M) (β := β) (h := h) k0 μΞ r)

instance (r : ℕ) :
    ProbabilityTheory.IsMarkovKernel (hopfieldOverlapPosteriorPredictiveOfPatterns (N := N) (M := M) (β := β) (h := h) k0 μΞ r) := by
  dsimp [hopfieldOverlapPosteriorPredictiveOfPatterns]
  infer_instance

end PatternsEnvironment

end Cascades
end SpinGlass
