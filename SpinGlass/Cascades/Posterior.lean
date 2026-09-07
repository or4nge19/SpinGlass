import SpinGlass.ReplicaKernel
import Mathlib.Probability.Kernel.Posterior
import Mathlib.Probability.Kernel.Composition.CompNotation

/-!
# Posterior and posterior-predictive kernels

Given prior `μH` on energies and `replicaGibbsKernel`, the posterior on `H` given replicas and the
posterior predictive for a fresh replica. Main: `gibbsPosteriorPredictive`.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace SpinGlass

namespace Cascades

open SpinGlass.KernelBridge

variable (N n : ℕ)

section

variable (μH : Measure (EnergySpace N)) [IsProbabilityMeasure μH]

/-- Posterior kernel: `ReplicaSpace N n → EnergySpace N`, i.e. law of `H` given `n` replicas. -/
noncomputable def gibbsPosteriorKernel :
    ProbabilityTheory.Kernel (ReplicaSpace N n) (EnergySpace N) :=
  (replicaGibbsKernel (N := N) (n := n))†μH

instance : IsMarkovKernel (gibbsPosteriorKernel (N := N) (n := n) μH) := by
  dsimp [gibbsPosteriorKernel]
  infer_instance

/-- Posterior predictive: Gibbs sampler integrated against the posterior on `H` given `n` replicas. -/
noncomputable def gibbsPosteriorPredictive :
    ProbabilityTheory.Kernel (ReplicaSpace N n) (Config N) :=
  (gibbsKernel (N := N)) ∘ₖ (gibbsPosteriorKernel (N := N) (n := n) μH)

instance : IsMarkovKernel (gibbsPosteriorPredictive (N := N) (n := n) μH) := by
  dsimp [gibbsPosteriorPredictive]
  infer_instance

/-! ### Fundamental posterior identities (specialized) -/

lemma compProd_posterior_eq_map_swap :
    ((replicaGibbsKernel (N := N) (n := n)) ∘ₘ μH) ⊗ₘ (gibbsPosteriorKernel (N := N) (n := n) μH)
      =
      (μH ⊗ₘ (replicaGibbsKernel (N := N) (n := n))).map Prod.swap := by
  simpa [gibbsPosteriorKernel] using
    (ProbabilityTheory.compProd_posterior_eq_map_swap
      (κ := replicaGibbsKernel (N := N) (n := n)) (μ := μH))

lemma posterior_comp_self :
    (gibbsPosteriorKernel (N := N) (n := n) μH) ∘ₘ (replicaGibbsKernel (N := N) (n := n)) ∘ₘ μH
      =
      μH := by
  -- specialized form of `posterior_comp_self`
  dsimp [gibbsPosteriorKernel]
  exact ProbabilityTheory.posterior_comp_self
    (κ := replicaGibbsKernel (N := N) (n := n)) (μ := μH)

end

end Cascades

end SpinGlass
