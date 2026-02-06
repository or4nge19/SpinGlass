import SpinGlass.Cascades.Posterior
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.ParallelComp

/-!
# Vol II infrastructure: posterior predictive as a conditional distribution

This file expresses the de Finetti/Bayesian picture in the most robust way:

- build the **joint law** of `(prefix replicas, fresh replica)` as `μPrefix ⊗ₘ predictive`;
- characterize the conditional law of the fresh replica given the prefix as a `condDistrib`;
- identify it with the posterior predictive kernel.

This is the statement shape that later infinite-dimensional Gaussian tools (Cameron–Martin/Fernique/GIBP)
will feed into: the analytic work produces statements about the posterior on `H`, while the measure/kernel
algebra turns them into statements about replica arrays.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace SpinGlass

namespace Cascades

open SpinGlass.KernelBridge

variable (N n : ℕ)

section

variable (μH : Measure (EnergySpace N)) [IsProbabilityMeasure μH]

/-- Law of `n` observed replicas under prior `μH`. -/
noncomputable def gibbsPrefixLaw : Measure (ReplicaSpace N n) :=
  (replicaGibbsKernel (N := N) (n := n)) ∘ₘ μH

instance : IsProbabilityMeasure (gibbsPrefixLaw (N := N) (n := n) μH) := by
  -- pushforward of a probability measure by a Markov kernel is a probability measure
  dsimp [gibbsPrefixLaw]
  infer_instance

/-- Joint law of `(prefix replicas, fresh replica)` using the posterior predictive kernel. -/
noncomputable def gibbsPrefixFreshLaw : Measure ((ReplicaSpace N n) × (Config N)) :=
  (gibbsPrefixLaw (N := N) (n := n) μH) ⊗ₘ (gibbsPosteriorPredictive (N := N) (n := n) μH)

instance : IsFiniteMeasure (gibbsPrefixFreshLaw (N := N) (n := n) μH) := by
  dsimp [gibbsPrefixFreshLaw]
  infer_instance

/-!
### Bayesian network factorization

These equalities make the “posterior predictive” semantics explicit at the measure level:

1. sample a prefix `σ^{≤n}` from its law,
2. sample `H` from the posterior given that prefix,
3. sample a fresh `σ^{n+1}` from `gibbsKernel H`.
-/

lemma gibbsPrefixFreshLaw_eq_compPosterior :
    gibbsPrefixFreshLaw (N := N) (n := n) μH
      =
      (Kernel.id ∥ₖ gibbsKernel (N := N)) ∘ₘ
        ((gibbsPrefixLaw (N := N) (n := n) μH) ⊗ₘ (gibbsPosteriorKernel (N := N) (n := n) μH)) := by
  -- This is exactly `parallelComp_comp_compProd` with `η = gibbsKernel` and `κ = posterior`.
  -- RHS is `μprefix ⊗ₘ (gibbsKernel ∘ₖ posterior)` which is definitionally `gibbsPrefixFreshLaw`.
  simpa [gibbsPrefixFreshLaw, Cascades.gibbsPosteriorPredictive, Cascades.gibbsPosteriorKernel] using
    (MeasureTheory.Measure.parallelComp_comp_compProd
      (μ := gibbsPrefixLaw (N := N) (n := n) μH)
      (κ := gibbsPosteriorKernel (N := N) (n := n) μH)
      (η := gibbsKernel (N := N))).symm

lemma gibbsPrefixFreshLaw_eq_from_prior :
    gibbsPrefixFreshLaw (N := N) (n := n) μH
      =
      (Kernel.id ∥ₖ gibbsKernel (N := N)) ∘ₘ
        ((μH ⊗ₘ replicaGibbsKernel (N := N) (n := n)).map Prod.swap) := by
  -- Use the defining posterior identity to rewrite `μprefix ⊗ₘ posterior` as the swapped prior joint law.
  have hpost :
      (gibbsPrefixLaw (N := N) (n := n) μH) ⊗ₘ (gibbsPosteriorKernel (N := N) (n := n) μH)
        =
        (μH ⊗ₘ replicaGibbsKernel (N := N) (n := n)).map Prod.swap := by
    -- `compProd_posterior_eq_map_swap` from `Cascades.Posterior`.
    simpa [gibbsPrefixLaw, Cascades.gibbsPosteriorKernel] using
      (Cascades.compProd_posterior_eq_map_swap (N := N) (n := n) (μH := μH))
  -- Substitute into the Bayesian-network factorization.
  simp [gibbsPrefixFreshLaw_eq_compPosterior (N := N) (n := n) (μH := μH), hpost]

/--
The conditional law of the fresh replica given the prefix under `gibbsPrefixFreshLaw`
is (a.e.) the posterior predictive kernel.

This is the canonical “posterior predictive = condDistrib” statement.
-/
lemma condDistrib_snd_fst_gibbsPrefixFreshLaw_ae :
    ProbabilityTheory.condDistrib (fun p : (ReplicaSpace N n) × (Config N) => p.2)
        (fun p : (ReplicaSpace N n) × (Config N) => p.1)
        (gibbsPrefixFreshLaw (N := N) (n := n) μH)
      =ᵐ[(gibbsPrefixFreshLaw (N := N) (n := n) μH).map Prod.fst]
        (gibbsPosteriorPredictive (N := N) (n := n) μH) := by
  classical
  -- Use the uniqueness characterization of `condDistrib` via a compProd identity.
  -- Here `μ = μPrefix ⊗ₘ predictive`, so the required identity is definitional.
  have hκ :
      (gibbsPrefixFreshLaw (N := N) (n := n) μH).map
          (fun p : (ReplicaSpace N n) × (Config N) =>
            ((fun q : (ReplicaSpace N n) × (Config N) => q.1) p,
             (fun q : (ReplicaSpace N n) × (Config N) => q.2) p))
        =
        (gibbsPrefixFreshLaw (N := N) (n := n) μH).map (fun p => p.1) ⊗ₘ
          (gibbsPosteriorPredictive (N := N) (n := n) μH) := by
    have hmapfst :
        (gibbsPrefixFreshLaw (N := N) (n := n) μH).map (fun p => p.1)
          =
          gibbsPrefixLaw (N := N) (n := n) μH := by
      -- `map fst` is the first marginal, and `fst_compProd` gives the marginal of a compProd.
      simpa [gibbsPrefixFreshLaw, Measure.fst] using
        (MeasureTheory.Measure.fst_compProd
          (μ := gibbsPrefixLaw (N := N) (n := n) μH)
          (κ := gibbsPosteriorPredictive (N := N) (n := n) μH))
    -- LHS is `map id` (since `(p.1,p.2)=p`), RHS rewrites to the defining `compProd`.
    have hid :
        (fun p : (ReplicaSpace N n) × (Config N) =>
            ((fun q : (ReplicaSpace N n) × (Config N) => q.1) p,
             (fun q : (ReplicaSpace N n) × (Config N) => q.2) p))
          =
          id := by
      funext p
      cases p
      rfl
    -- Also simplify `map fst` for the explicit `compProd`.
    have hfst' :
        Measure.map (fun p : (ReplicaSpace N n) × (Config N) => p.1)
          (gibbsPrefixLaw (N := N) (n := n) μH ⊗ₘ gibbsPosteriorPredictive (N := N) (n := n) μH)
          =
          gibbsPrefixLaw (N := N) (n := n) μH := by
      simpa [Measure.fst] using
        (MeasureTheory.Measure.fst_compProd
          (μ := gibbsPrefixLaw (N := N) (n := n) μH)
          (κ := gibbsPosteriorPredictive (N := N) (n := n) μH))
    -- Use `hid` and `hfst'` to reduce to reflexivity.
    simp [hid, gibbsPrefixFreshLaw, hfst']
  refine ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := gibbsPrefixFreshLaw (N := N) (n := n) μH)
    (X := fun p : (ReplicaSpace N n) × (Config N) => p.1)
    (Y := fun p : (ReplicaSpace N n) × (Config N) => p.2)
    (hX := by fun_prop) (hY := by fun_prop) (κ := gibbsPosteriorPredictive (N := N) (n := n) μH) ?_
  simpa using hκ

/-!
### Prior-driven joint law

This is the “honest generative” joint distribution of `(prefix replicas, fresh replica)` obtained by:

1. sample `H ~ μH`,
2. sample `n` replicas from `replicaGibbsKernel H`,
3. sample a fresh replica from `gibbsKernel H`,
4. forget `H`.

It is definitionally the same measure as `gibbsPrefixFreshLaw` by the posterior identity.
-/

noncomputable def gibbsPriorPrefixFreshLaw : Measure ((ReplicaSpace N n) × (Config N)) :=
  (Kernel.id ∥ₖ gibbsKernel (N := N)) ∘ₘ
    ((μH ⊗ₘ replicaGibbsKernel (N := N) (n := n)).map Prod.swap)

instance : IsFiniteMeasure (gibbsPriorPrefixFreshLaw (N := N) (n := n) μH) := by
  dsimp [gibbsPriorPrefixFreshLaw]
  infer_instance

lemma gibbsPriorPrefixFreshLaw_eq :
    gibbsPriorPrefixFreshLaw (N := N) (n := n) μH
      =
      gibbsPrefixFreshLaw (N := N) (n := n) μH := by
  -- This is exactly `gibbsPrefixFreshLaw_eq_from_prior`.
  simpa [gibbsPriorPrefixFreshLaw] using
    (gibbsPrefixFreshLaw_eq_from_prior (N := N) (n := n) (μH := μH)).symm

lemma condDistrib_snd_fst_gibbsPriorPrefixFreshLaw_ae :
    ProbabilityTheory.condDistrib (fun p : (ReplicaSpace N n) × (Config N) => p.2)
        (fun p : (ReplicaSpace N n) × (Config N) => p.1)
        (gibbsPriorPrefixFreshLaw (N := N) (n := n) μH)
      =ᵐ[(gibbsPriorPrefixFreshLaw (N := N) (n := n) μH).map Prod.fst]
        (gibbsPosteriorPredictive (N := N) (n := n) μH) := by
  -- Rewrite the measure argument, then apply the already-proved condDistrib identity.
  simpa [gibbsPriorPrefixFreshLaw_eq (N := N) (n := n) (μH := μH)] using
    (condDistrib_snd_fst_gibbsPrefixFreshLaw_ae (N := N) (n := n) (μH := μH))

end

end Cascades

end SpinGlass
