import SpinGlass.FiniteGibbs
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Finite Gibbs measure as an atomic probability measure

Talagrand (Vol. I/II) frequently treats the finite-volume Gibbs distribution as a probability
measure on the configuration space.  This file provides the model-agnostic construction for an
arbitrary finite type `α`, bundling the weights `gibbs_pmf` into an explicit atomic measure.

Everything here depends only on a finite
configuration space and a Hamiltonian `H : EnergySpace α`.
-/

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ENNReal NNReal

namespace SpinGlass

namespace FiniteGibbs

noncomputable section

variable {α : Type*} [Fintype α] [Nonempty α]

/-- The Gibbs weight as a nonnegative real. -/
noncomputable def gibbsWeightNNReal (H : EnergySpace α) (σ : α) : ℝ≥0 :=
  ⟨gibbs_pmf (α := α) H σ, gibbs_pmf_nonneg (α := α) (H := H) σ⟩

/-- Coercion of `gibbsWeightNNReal` to `ℝ`. -/
@[simp] lemma gibbsWeightNNReal_coe (H : EnergySpace α) (σ : α) :
    (gibbsWeightNNReal (α := α) H σ : ℝ) = gibbs_pmf (α := α) H σ := rfl

/-- Coercion of `gibbsWeightNNReal` to `ℝ≥0∞` agrees with `ENNReal.ofReal` of the pmf. -/
@[simp] lemma gibbsWeightNNReal_coe_ennreal (H : EnergySpace α) (σ : α) :
    (gibbsWeightNNReal (α := α) H σ : ℝ≥0∞) =
      ENNReal.ofReal (gibbs_pmf (α := α) H σ) := by
  have hσ : 0 ≤ gibbs_pmf (α := α) H σ :=
    gibbs_pmf_nonneg (α := α) (H := H) σ
  have hnn :
      gibbsWeightNNReal (α := α) H σ =
        ⟨gibbs_pmf (α := α) H σ, hσ⟩ := by
    ext
    simp [gibbsWeightNNReal]
  simp [ENNReal.ofReal_eq_coe_nnreal hσ, hnn]

/-- The Gibbs distribution as a `PMF`, the native Mathlib object for finite probability laws. -/
noncomputable def gibbsPMF (H : EnergySpace α) : PMF α :=
  PMF.ofFintype (fun σ => ENNReal.ofReal (gibbs_pmf (α := α) H σ)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · simp [sum_gibbs_pmf (α := α) (H := H)]
    · intro σ _hσ
      exact gibbs_pmf_nonneg (α := α) (H := H) σ

@[simp] lemma gibbsPMF_apply (H : EnergySpace α) (σ : α) :
    gibbsPMF (α := α) H σ = ENNReal.ofReal (gibbs_pmf (α := α) H σ) :=
  rfl

variable [MeasurableSpace α]

/-- The finite-volume Gibbs measure (atomic, with weights `gibbs_pmf`). -/
noncomputable def gibbsMeasure (H : EnergySpace α) : Measure α :=
  (gibbsPMF (α := α) H).toMeasure

lemma lintegral_gibbsMeasure (H : EnergySpace α) (f : α → ℝ≥0∞) [MeasurableSingletonClass α] :
    (∫⁻ σ, f σ ∂gibbsMeasure (α := α) H) =
      ∑ σ : α, (gibbsWeightNNReal (α := α) H σ : ℝ≥0∞) * f σ := by
  rw [lintegral_fintype]
  refine Finset.sum_congr rfl ?_
  intro σ _hσ
  have hsingleton :
      gibbsMeasure (α := α) H ({σ} : Set α) =
        (gibbsWeightNNReal (α := α) H σ : ℝ≥0∞) := by
    simpa [gibbsMeasure, gibbsWeightNNReal_coe_ennreal] using
      (PMF.toMeasure_apply_singleton (gibbsPMF (α := α) H) σ (measurableSet_singleton σ))
  rw [hsingleton, mul_comm]

/-- `lintegral` of a nonnegative real-valued function under the Gibbs measure. -/
lemma lintegral_gibbsMeasure_ofReal
    (H : EnergySpace α) (f : α → ℝ) (hf : ∀ σ, 0 ≤ f σ) [MeasurableSingletonClass α] :
    (∫⁻ σ, ENNReal.ofReal (f σ) ∂gibbsMeasure (α := α) H) =
      ENNReal.ofReal (∑ σ : α, (gibbs_pmf (α := α) H σ) * f σ) := by
  have h :=
    lintegral_gibbsMeasure (α := α) (H := H) (f := fun σ => ENNReal.ofReal (f σ))
  simp [gibbsWeightNNReal_coe_ennreal (α := α) (H := H)] at h
  have hprod :
      (∑ σ : α, ENNReal.ofReal (gibbs_pmf (α := α) H σ) * ENNReal.ofReal (f σ)) =
        ∑ σ : α, ENNReal.ofReal (gibbs_pmf (α := α) H σ * f σ) := by
    refine Finset.sum_congr rfl (fun σ _hσ => ?_)
    have hσ : 0 ≤ gibbs_pmf (α := α) H σ := gibbs_pmf_nonneg (α := α) (H := H) σ
    have hfσ : 0 ≤ f σ := hf σ
    simpa [mul_assoc] using
      (ENNReal.ofReal_mul (p := gibbs_pmf (α := α) H σ) (q := f σ) hσ).symm
  have hnonneg : ∀ σ : α, 0 ≤ gibbs_pmf (α := α) H σ * f σ := by
    intro σ
    exact mul_nonneg (gibbs_pmf_nonneg (α := α) (H := H) σ) (hf σ)
  calc
    (∫⁻ σ, ENNReal.ofReal (f σ) ∂gibbsMeasure (α := α) H)
        =
        ∑ σ : α, ENNReal.ofReal (gibbs_pmf (α := α) H σ) * ENNReal.ofReal (f σ) := h
    _ = ∑ σ : α, ENNReal.ofReal (gibbs_pmf (α := α) H σ * f σ) := hprod
    _ = ENNReal.ofReal (∑ σ : α, gibbs_pmf (α := α) H σ * f σ) := by
          simpa using
            (ENNReal.ofReal_sum_of_nonneg (s := (Finset.univ : Finset α))
              (f := fun σ : α => gibbs_pmf (α := α) H σ * f σ)
              (by intro σ _; exact hnonneg σ)).symm

/-- `integral` of a real-valued function under the Gibbs measure. -/
lemma integral_gibbsMeasure
    (H : EnergySpace α) (f : α → ℝ) [MeasurableSingletonClass α] :
    (∫ σ, f σ ∂gibbsMeasure (α := α) H)  =
      ∑ σ : α, (gibbs_pmf (α := α) H σ) * f σ := by
  calc
    (∫ σ, f σ ∂gibbsMeasure (α := α) H)
        = ∑ σ : α, (gibbsPMF (α := α) H σ).toReal • f σ := by
            simpa [gibbsMeasure] using (PMF.integral_eq_sum (gibbsPMF (α := α) H) f)
    _ = ∑ σ : α, (gibbs_pmf (α := α) H σ) * f σ := by
          refine Finset.sum_congr rfl ?_
          intro σ _hσ
          simp [ENNReal.toReal_ofReal (gibbs_pmf_nonneg (α := α) (H := H) σ), smul_eq_mul]

lemma gibbsMeasure_univ (H : EnergySpace α) : gibbsMeasure (α := α) H Set.univ = 1 := by
  simp [gibbsMeasure]

instance (H : EnergySpace α) : IsProbabilityMeasure (gibbsMeasure (α := α) H) :=
  by
    dsimp [gibbsMeasure]
    infer_instance

end

end FiniteGibbs

end SpinGlass
