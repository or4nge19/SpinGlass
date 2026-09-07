import SpinGlass.FiniteGibbs
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Finite Gibbs measure

Atomic probability measure on a finite type `α` with weights `gibbs_pmf` from Hamiltonian
`H : EnergySpace α`. Talagrand Vol. I–II finite-volume Gibbs law.
-/

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ENNReal NNReal

namespace SpinGlass

namespace FiniteGibbs

noncomputable section

variable {α : Type*} [Fintype α] [Nonempty α]

/-- The Gibbs weight as a nonnegative real. -/
noncomputable def gibbsWeightNNReal (H : EnergySpace α) (σ : α) : ℝ≥0 :=
  .mk (gibbs_pmf (α := α) H σ) (gibbs_pmf_nonneg (α := α) (H := H) σ)

/-- Coercion of `gibbsWeightNNReal` to `ℝ`. -/
@[simp] lemma gibbsWeightNNReal_coe (H : EnergySpace α) (σ : α) :
    (gibbsWeightNNReal (α := α) H σ : ℝ) = gibbs_pmf (α := α) H σ := rfl

/-- Coercion of `gibbsWeightNNReal` to `ℝ≥0∞` agrees with `ENNReal.ofReal` of the pmf. -/
@[simp] lemma gibbsWeightNNReal_coe_ennreal (H : EnergySpace α) (σ : α) :
    (gibbsWeightNNReal (α := α) H σ : ℝ≥0∞) =
      ENNReal.ofReal (gibbs_pmf (α := α) H σ) :=
  (ENNReal.ofReal_eq_coe_nnreal (gibbs_pmf_nonneg (α := α) (H := H) σ)).symm

variable [MeasurableSpace α]

/-- The finite-volume Gibbs measure (atomic, with weights `gibbs_pmf`). -/
noncomputable def gibbsMeasure (H : EnergySpace α) : Measure α :=
  (Finset.univ : Finset α).sum fun σ =>
    ((gibbsWeightNNReal (α := α) H σ : ℝ≥0∞) • Measure.dirac σ)

/-- The atoms of the Gibbs measure are the Gibbs weights. -/
@[simp] lemma gibbsMeasure_apply_singleton (H : EnergySpace α) (σ : α)
    [MeasurableSingletonClass α] :
    gibbsMeasure (α := α) H {σ} = ENNReal.ofReal (gibbs_pmf (α := α) H σ) := by
  classical
  simp [gibbsMeasure, Measure.dirac_apply', Set.indicator_apply, eq_comm]

lemma lintegral_gibbsMeasure (H : EnergySpace α) (f : α → ℝ≥0∞) [MeasurableSingletonClass α] :
    (∫⁻ σ, f σ ∂gibbsMeasure (α := α) H) =
      ∑ σ : α, (gibbsWeightNNReal (α := α) H σ : ℝ≥0∞) * f σ := by
  simp [gibbsMeasure, lintegral_finsetSum_measure, mul_comm]

/-- `lintegral` of a nonnegative real-valued function under the Gibbs measure. -/
lemma lintegral_gibbsMeasure_ofReal
    (H : EnergySpace α) (f : α → ℝ) (hf : ∀ σ, 0 ≤ f σ) [MeasurableSingletonClass α] :
    (∫⁻ σ, ENNReal.ofReal (f σ) ∂gibbsMeasure (α := α) H) =
      ENNReal.ofReal (∑ σ : α, (gibbs_pmf (α := α) H σ) * f σ) := by
  have h :=
    lintegral_gibbsMeasure (α := α) (H := H) (f := fun σ => ENNReal.ofReal (f σ))
  simp only [gibbsWeightNNReal_coe_ennreal (α := α) (H := H)] at h
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
  let μatom : α → Measure α :=
    fun σ => (gibbsWeightNNReal (α := α) H σ : ℝ≥0∞) • Measure.dirac σ
  have h_integrable :
      ∀ σ ∈ (Finset.univ : Finset α), Integrable f (μatom σ) := by
    intro σ _hσ
    exact (MeasureTheory.integrable_dirac (a := σ) (f := f) (by simp)).smul_measure (by simp)
  have hsum :
      (∫ x, f x ∂((Finset.univ : Finset α).sum μatom)) =
        ∑ σ : α, ∫ x, f x ∂μatom σ :=
    MeasureTheory.integral_finsetSum_measure (f := f) (μ := μatom)
      (s := (Finset.univ : Finset α)) h_integrable
  simp only [gibbsMeasure, μatom] at hsum ⊢
  rw [hsum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp [NNReal.smul_def, mul_comm, gibbsWeightNNReal]

lemma gibbsMeasure_univ (H : EnergySpace α) : gibbsMeasure (α := α) H Set.univ = 1 := by
  have h_univ :
      gibbsMeasure (α := α) H Set.univ = ∑ σ : α, (gibbsWeightNNReal (α := α) H σ : ℝ≥0∞) := by
    simp [gibbsMeasure, gibbsWeightNNReal]
  have hsumNNReal : (∑ σ : α, gibbsWeightNNReal (α := α) H σ) = (1 : ℝ≥0) := by
    apply NNReal.coe_injective
    simp [gibbsWeightNNReal, NNReal.coe_sum, sum_gibbs_pmf]
  have hsumENNReal :
      (∑ σ : α, (gibbsWeightNNReal (α := α) H σ : ℝ≥0∞)) = (1 : ℝ≥0∞) := by
    simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) hsumNNReal
  simpa [h_univ] using hsumENNReal

instance (H : EnergySpace α) : IsProbabilityMeasure (gibbsMeasure (α := α) H) :=
  ⟨gibbsMeasure_univ (α := α) (H := H)⟩

end

end FiniteGibbs

end SpinGlass
