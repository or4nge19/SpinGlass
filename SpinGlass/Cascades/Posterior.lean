import SpinGlass.ReplicaKernel
import Mathlib.Probability.Kernel.Posterior
import Mathlib.Probability.Kernel.Composition.CompNotation

/-!
# Vol II infrastructure: posterior + posterior-predictive kernels for replica sampling

This file isolates the **de Finetti / Bayesian** viewpoint:

- the disorder/environment `H` has a prior law `μH`;
- given `H`, `n` replicas are sampled by the Markov kernel `replicaGibbsKernel`;
- the conditional law of `H` given replicas is the **posterior kernel**;
- the conditional law of one more replica given the observed replicas is the **posterior predictive**,
  obtained by integrating `gibbsKernel` against that posterior.

This is a principled API boundary for later infinite-dimensional Gaussian arguments
(Cameron–Martin/Fernique/GIBP): analytic estimates live on `μH`, while the sampling algebra is
kernel-compositional.
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

/--
Posterior predictive kernel: conditional law of a fresh configuration given `n` observed replicas,
obtained by integrating the Gibbs sampler against the posterior on `H`.
-/
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
