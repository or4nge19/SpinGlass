import SpinGlass.FiniteGibbs.GibbsMeasure
import SpinGlass.FiniteGibbs.ReplicaMeasure
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Probability.Kernel.Basic

/-!
# Finite Gibbs kernels (model-agnostic)

This file models the finite-volume Gibbs sampler (and its replica version) as Markov kernels
in the **Vol II** style:

- `H ↦ G_H` as a kernel `EnergySpace α ⟶ α`,
- `H ↦ G_H^{⊗ n}` as a kernel `EnergySpace α ⟶ (Fin n → α)`.

Everything is generic in the finite configuration space `α`.
-/

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ENNReal NNReal

namespace SpinGlass
namespace FiniteGibbs

noncomputable section

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## Measurability helpers -/

lemma measurable_eval (σ : α) : Measurable fun H : EnergySpace α => H σ := by
  simpa [evalCLM] using (evalCLM σ).continuous.measurable

lemma measurable_Z : Measurable fun H : EnergySpace α => Z H := by
  have hmeas_term :
      ∀ σ ∈ (Finset.univ : Finset α),
        Measurable fun H : EnergySpace α => Real.exp (-H σ) := by
    intro σ _hσ
    have : Measurable fun H : EnergySpace α => H σ := measurable_eval (σ := σ)
    fun_prop
  simpa [Z] using (Finset.measurable_sum (s := (Finset.univ : Finset α)) hmeas_term)

lemma measurable_gibbs_pmf (σ : α) :
    Measurable fun H : EnergySpace α => gibbs_pmf H σ := by
  have hmeas_num : Measurable fun H : EnergySpace α => Real.exp (-H σ) := by
    have : Measurable fun H : EnergySpace α => H σ := measurable_eval (σ := σ)
    fun_prop
  have hmeas_den : Measurable fun H : EnergySpace α => Z H :=
    measurable_Z
  simpa [gibbs_pmf] using hmeas_num.div hmeas_den

lemma measurable_gibbsWeightENNReal (σ : α) :
    Measurable fun H : EnergySpace α => ENNReal.ofReal (gibbs_pmf H σ) := by
  simpa using (ENNReal.measurable_ofReal.comp (measurable_gibbs_pmf (σ := σ)))

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

@[simp] lemma gibbsKernel_apply (H : EnergySpace α) :
    gibbsKernel (α := α) H = gibbsMeasure (α := α) H := rfl

instance : IsMarkovKernel (gibbsKernel (α := α)) := by
  refine ⟨fun H => ?_⟩
  simpa [gibbsKernel] using
    (by infer_instance : IsProbabilityMeasure (gibbsMeasure (α := α) H))

/-! ## Replica sampler kernel -/

/-- The `n`-replica Gibbs sampler as a kernel from energies to `n` replicas. -/
noncomputable def replicaGibbsKernel (n : ℕ) :
    Kernel (EnergySpace α) (ReplicaSpace (α := α) n) where
  toFun := fun H => replicaGibbsMeasure (α := α) (n := n) H
  measurable' := by
    classical
    refine Measure.measurable_of_measurable_coe
      (fun H => replicaGibbsMeasure (α := α) (n := n) H) ?_
    intro s hs
    have hsum :
        (fun H : EnergySpace α => replicaGibbsMeasure (α := α) (n := n) H s)
          =
        fun H =>
          ∑ σs : ReplicaSpace (α := α) n,
            (if σs ∈ s then (replicaGibbsWeightNNReal (α := α) (n := n) H σs : ℝ≥0∞) else 0) := by
      funext H
      classical
      simp [replicaGibbsMeasure, replicaGibbsWeightNNReal, hs, Measure.dirac_apply', Set.indicator]
    have hterm :
        ∀ σs ∈ (Finset.univ : Finset (ReplicaSpace (α := α) n)),
          Measurable fun H : EnergySpace α =>
            (if σs ∈ s then (replicaGibbsWeightNNReal (α := α) (n := n) H σs : ℝ≥0∞) else 0) := by
      intro σs _hσs
      by_cases hσs' : σs ∈ s
      · have hprod : Measurable fun H : EnergySpace α => ∏ l, gibbs_pmf H (σs l) := by
          classical
          have hfac :
              ∀ l ∈ (Finset.univ : Finset (Fin n)),
                Measurable fun H : EnergySpace α => gibbs_pmf H (σs l) := by
            intro l _hl
            simpa using measurable_gibbs_pmf (σ := σs l)
          simpa using (Finset.measurable_prod (s := (Finset.univ : Finset (Fin n))) hfac)
        have hnn :
            Measurable fun H : EnergySpace α =>
              replicaGibbsWeightNNReal (α := α) (n := n) H σs := by
          simpa [replicaGibbsWeightNNReal] using (Measurable.subtype_mk hprod)
        have hcoe : Measurable fun H : EnergySpace α =>
            (replicaGibbsWeightNNReal (α := α) (n := n) H σs : ℝ≥0∞) := by
          have h_ofReal :
              Measurable fun H : EnergySpace α =>
                ENNReal.ofReal (replicaGibbsWeightNNReal (α := α) (n := n) H σs : ℝ) :=
            ENNReal.measurable_ofReal.comp (measurable_coe_nnreal_real.comp hnn)
          have hconv :
              (fun H : EnergySpace α =>
                  (replicaGibbsWeightNNReal (α := α) (n := n) H σs : ℝ≥0∞)) =
                fun H : EnergySpace α =>
                  ENNReal.ofReal (replicaGibbsWeightNNReal (α := α) (n := n) H σs : ℝ) := by
            funext H
            simp
          simpa [hconv] using h_ofReal
        simp [hσs', hcoe]
      · simp [hσs']
    simpa [hsum] using
      (Finset.measurable_sum (s := (Finset.univ : Finset (ReplicaSpace (α := α) n))) hterm)

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
