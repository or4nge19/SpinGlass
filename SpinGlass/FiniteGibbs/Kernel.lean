import SpinGlass.FiniteGibbs.GibbsMeasure
import SpinGlass.FiniteGibbs.ReplicaMeasure
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Probability.Kernel.Basic

/-!
# Finite Gibbs kernels

Markov kernels `H ↦ G_H` (`gibbsKernel`) and `H ↦ G_H^{⊗ n}` (`replicaGibbsKernel`) on a finite
configuration space `α`. Talagrand Vol. II.
-/

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ENNReal NNReal

namespace SpinGlass
namespace FiniteGibbs

noncomputable section

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## Measurability helpers -/

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma measurable_eval (σ : α) : Measurable fun H : EnergySpace α => H σ := by
  simpa [evalCLM] using (evalCLM σ).continuous.measurable

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma measurable_Z : Measurable fun H : EnergySpace α => Z H := by
  have hmeas_term :
      ∀ σ ∈ (Finset.univ : Finset α),
        Measurable fun H : EnergySpace α => Real.exp (-H σ) := by
    intro σ _hσ
    have : Measurable fun H : EnergySpace α => H σ := measurable_eval (σ := σ)
    fun_prop
  simpa [Z] using (Finset.measurable_sum (s := (Finset.univ : Finset α)) hmeas_term)

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma measurable_gibbs_pmf (σ : α) :
    Measurable fun H : EnergySpace α => gibbs_pmf H σ := by
  have hmeas_num : Measurable fun H : EnergySpace α => Real.exp (-H σ) := by
    have : Measurable fun H : EnergySpace α => H σ := measurable_eval (σ := σ)
    fun_prop
  have hmeas_den : Measurable fun H : EnergySpace α => Z H :=
    measurable_Z
  simpa [gibbs_pmf] using hmeas_num.fun_div hmeas_den

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma measurable_gibbsWeightENNReal (σ : α) :
    Measurable fun H : EnergySpace α => ENNReal.ofReal (gibbs_pmf H σ) := by
  exact (measurable_gibbs_pmf (σ := σ)).ennreal_ofReal

/-! ## The Gibbs sampler kernel -/

/-- The finite-volume Gibbs sampler as a kernel from energies to configurations. -/
noncomputable def gibbsKernel : Kernel (EnergySpace α) α where
  toFun := fun H => gibbsMeasure (α := α) H
  measurable' := by
    classical
    refine Measure.measurable_of_measurable_coe (fun H => gibbsMeasure (α := α) H) ?_
    intro s hs
    have hsum :
        (fun H : EnergySpace α => gibbsMeasure (α := α) H s)  =
        fun H => ∑ σ : α, (if σ ∈ s then ENNReal.ofReal (gibbs_pmf H σ) else 0) := by
      funext H
      simp [gibbsMeasure, hs, Measure.dirac_apply', Set.indicator]
    have hterm :
        ∀ σ ∈ (Finset.univ : Finset α),
          Measurable fun H : EnergySpace α =>
            (if σ ∈ s then ENNReal.ofReal (gibbs_pmf H σ) else 0) := by
      intro σ _hσ
      by_cases hσ' : σ ∈ s
      · simp [hσ', measurable_gibbsWeightENNReal (σ := σ)]
      · simp [hσ']
    simpa [hsum] using (Finset.measurable_sum (s := (Finset.univ : Finset α)) hterm)

omit [MeasurableSingletonClass α] in
@[simp] lemma gibbsKernel_apply (H : EnergySpace α) :
    gibbsKernel (α := α) H = gibbsMeasure (α := α) H := rfl

instance : IsMarkovKernel (gibbsKernel (α := α)) := by
  refine ⟨fun H => ?_⟩
  simpa [gibbsKernel] using
    (by infer_instance : IsProbabilityMeasure (gibbsMeasure (α := α) H))

/-! ## Replica sampler kernel -/

/-- The `n`-replica Gibbs sampler as a kernel from energies to `n` replicas: the product of `n`
copies of `gibbsKernel`, i.e. `H ↦ (gibbsMeasure H)^{⊗ n}`. -/
noncomputable def replicaGibbsKernel (n : ℕ) :
    Kernel (EnergySpace α) (ReplicaSpace (α := α) n) where
  toFun := fun H => replicaGibbsMeasure (α := α) (n := n) H
  measurable' := by
    classical
    refine Measure.measurable_of_measurable_coe
      (fun H => replicaGibbsMeasure (α := α) (n := n) H) ?_
    intro s _hs
    have hval : (fun H : EnergySpace α => replicaGibbsMeasure (α := α) (n := n) H s)
        = fun H : EnergySpace α => ∑ σs ∈ s.toFinset,
            ∏ l : Fin n, ENNReal.ofReal (gibbs_pmf (α := α) H (σs l)) := by
      funext H
      calc replicaGibbsMeasure (α := α) (n := n) H s
          = replicaGibbsMeasure (α := α) (n := n) H
              (↑(s.toFinset) : Set (ReplicaSpace (α := α) n)) := by rw [Set.coe_toFinset]
        _ = ∑ σs ∈ s.toFinset, replicaGibbsMeasure (α := α) (n := n) H {σs} :=
            sum_measure_singleton.symm
        _ = ∑ σs ∈ s.toFinset, ∏ l : Fin n, ENNReal.ofReal (gibbs_pmf (α := α) H (σs l)) :=
            Finset.sum_congr rfl fun σs _ =>
              replicaGibbsMeasure_apply_singleton (α := α) n H σs
    rw [hval]
    refine Finset.measurable_sum _ fun σs _ => ?_
    exact Finset.measurable_prod _ fun l _ =>
      ENNReal.measurable_ofReal.comp (measurable_gibbs_pmf (α := α) (σ := σs l))

@[simp] lemma replicaGibbsKernel_apply (n : ℕ) (H : EnergySpace α) :
    replicaGibbsKernel (α := α) n H =
      replicaGibbsMeasure (α := α) (n := n) H := rfl

instance (n : ℕ) : IsMarkovKernel (replicaGibbsKernel (α := α) n) := by
  classical
  refine ⟨fun H => ?_⟩
  simpa [replicaGibbsKernel] using
    (by infer_instance : IsProbabilityMeasure (replicaGibbsMeasure (α := α) (n := n) H))

end

end FiniteGibbs
end SpinGlass
