import SpinGlass.GibbsBridge
import SpinGlass.ReplicaMeasure
import SpinGlass.FiniteGibbs.Kernel

/-!
# Gibbs samplers as kernels

Finite-volume Gibbs sampler as a Markov kernel; `n` replicas as the product kernel. Consistent
with `gibbsMeasure` and `replicaGibbsMeasure`. Talagrand Vol. II.
-/

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ENNReal NNReal

namespace SpinGlass

variable (N : ℕ)

namespace KernelBridge

/-! ## Measurability helpers for the finite Gibbs weights -/

lemma measurable_eval (σ : Config N) : Measurable fun H : EnergySpace N => H σ := by
  simpa using (FiniteGibbs.measurable_eval (α := Config N) σ)

lemma measurable_Z : Measurable fun H : EnergySpace N => Z (N := N) H := by
  simpa [Z_eq_FiniteGibbs_Z] using (FiniteGibbs.measurable_Z (α := Config N))

lemma measurable_gibbs_pmf (σ : Config N) :
    Measurable fun H : EnergySpace N => gibbs_pmf N H σ := by
  simpa [gibbs_pmf_eq_FiniteGibbs_gibbs_pmf] using
    (FiniteGibbs.measurable_gibbs_pmf (α := Config N) σ)

lemma measurable_gibbsWeightENNReal (σ : Config N) :
    Measurable fun H : EnergySpace N => ENNReal.ofReal (gibbs_pmf N H σ) := by
  simpa [gibbs_pmf_eq_FiniteGibbs_gibbs_pmf] using
    (FiniteGibbs.measurable_gibbsWeightENNReal (α := Config N) σ)

/-! ## The Gibbs sampler as a Markov kernel -/

/-- The finite-volume Gibbs sampler: a kernel from energies to configurations. -/
noncomputable def gibbsKernel : Kernel (EnergySpace N) (Config N) :=
  FiniteGibbs.gibbsKernel (α := Config N)

instance : IsMarkovKernel (gibbsKernel (N := N)) := by
  simpa [gibbsKernel] using
    (by infer_instance : IsMarkovKernel (FiniteGibbs.gibbsKernel (α := Config N)))

/-! ## Replica sampling kernel (finite-volume) -/

variable (n : ℕ)

/-- The `n`-replica Gibbs sampler as a Markov kernel. -/
noncomputable def replicaGibbsKernel : Kernel (EnergySpace N) (ReplicaSpace N n) :=
  FiniteGibbs.replicaGibbsKernel (α := Config N) n

instance : IsMarkovKernel (replicaGibbsKernel (N := N) (n := n)) := by
  simpa [replicaGibbsKernel] using
    (by infer_instance : IsMarkovKernel (FiniteGibbs.replicaGibbsKernel (α := Config N) n))

end KernelBridge

end SpinGlass
