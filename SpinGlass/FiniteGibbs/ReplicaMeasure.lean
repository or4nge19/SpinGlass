import SpinGlass.FiniteGibbs
import SpinGlass.FiniteGibbs.GibbsMeasure
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Data.Fintype.Pi

/-!
# Finite-volume replica Gibbs measure (model-agnostic)

This file isolates the **purely finite-volume** definitions around sampling `n` independent
replicas from the finite Gibbs measure, for an arbitrary finite configuration space `α`.

Nothing here depends on an ambient disorder probability space: this is a reusable building block
for Talagrand Vol. II (replicas, overlap arrays, cascades).
-/

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ENNReal NNReal

namespace SpinGlass

namespace FiniteGibbs

noncomputable section

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The space of `n` replicas: `Fin n → α`. -/
abbrev ReplicaSpace (n : ℕ) := Fin n → α

/-- A function of `n` replicas. -/
abbrev ReplicaFun (n : ℕ) := ReplicaSpace (α := α) n → ℝ

/--
Talagrand's deterministic Gibbs average of a function of `n` replicas.

This is the finite-volume object (no ambient probability space).
-/
noncomputable def gibbs_average_n_det (n : ℕ) (H : EnergySpace α) (f : ReplicaFun (α := α) n) : ℝ :=
  ∑ σs : ReplicaSpace (α := α) n, f σs * ∏ l, gibbs_pmf (α := α) H (σs l)

/-! ## Replica Gibbs measure (finite-volume, atomic) -/

/-- The `n`-replica Gibbs weight (as `ℝ≥0`). -/
noncomputable def replicaGibbsWeightNNReal (n : ℕ) (H : EnergySpace α) (σs : ReplicaSpace (α := α) n) : ℝ≥0 :=
  ⟨∏ l, gibbs_pmf (α := α) H (σs l), by
    classical
    refine Finset.prod_nonneg ?_
    intro l _hl
    exact gibbs_pmf_nonneg (α := α) (H := H) (σ := σs l)⟩

/-- The `n`-replica Gibbs measure as an explicit finite atomic measure on `ReplicaSpace α n`. -/
noncomputable def replicaGibbsMeasure (n : ℕ) (H : EnergySpace α) : Measure (ReplicaSpace (α := α) n) :=
  (Finset.univ : Finset (ReplicaSpace (α := α) n)).sum fun σs =>
    ((replicaGibbsWeightNNReal (α := α) (n := n) H σs : ℝ≥0∞) • Measure.dirac σs)

/-! ## Normalization and bracket-as-integral -/

/--
The product Gibbs weights on `n` replicas sum to `1`.
-/
lemma sum_prod_gibbs_pmf_eq_one (n : ℕ) (H : EnergySpace α) :
    (∑ σs : ReplicaSpace (α := α) n, ∏ l, gibbs_pmf (α := α) H (σs l)) = 1 := by
  classical
  induction n with
  | zero =>
      simp
  | succ n ih =>
      let p : α → ℝ := gibbs_pmf (α := α) H
      have hs1 : (∑ σ : α, p σ) = 1 := by
        simpa [p] using (sum_gibbs_pmf (α := α) (H := H))
      let e : (α × (Fin n → α)) ≃ (Fin (n + 1) → α) :=
        Fin.consEquiv (fun _ : Fin (n + 1) => α)
      have hrew :
          (∑ σs : (Fin (n + 1) → α), ∏ l : Fin (n + 1), p (σs l))
            = ∑ x : (α × (Fin n → α)), ∏ l : Fin (n + 1), p (e x l) := by
        simpa using
          (Fintype.sum_equiv e
              (f := fun x => ∏ l : Fin (n + 1), p (e x l))
              (g := fun σs => ∏ l : Fin (n + 1), p (σs l))
              (h := fun x => rfl)).symm
      calc
        (∑ σs : (Fin (n + 1) → α), ∏ l : Fin (n + 1), p (σs l))
            = ∑ x : (α × (Fin n → α)), ∏ l : Fin (n + 1), p (e x l) := hrew
        _ = ∑ σ₀ : α, ∑ σtail : (Fin n → α),
              p σ₀ * (∏ i : Fin n, p (σtail i)) := by
              classical
              simp [Fintype.sum_prod_type, e, p, Fin.prod_univ_succ]
        _ = ∑ σ₀ : α, p σ₀ * (∑ σtail : (Fin n → α), ∏ i : Fin n, p (σtail i)) := by
              classical
              simp [Finset.mul_sum]
        _ = ∑ σ₀ : α, p σ₀ * 1 := by
              simpa [p] using congrArg (fun r => ∑ σ₀ : α, p σ₀ * r) ih
        _ = ∑ σ₀ : α, p σ₀ := by simp
        _ = 1 := hs1

lemma replicaGibbsMeasure_univ (n : ℕ) (H : EnergySpace α) :
    replicaGibbsMeasure (α := α) (n := n) H Set.univ = 1 := by
  classical
  have h_univ :
      replicaGibbsMeasure (α := α) (n := n) H Set.univ
        =
        ∑ σs : ReplicaSpace (α := α) n, (replicaGibbsWeightNNReal (α := α) (n := n) H σs : ℝ≥0∞) := by
    simp [replicaGibbsMeasure, replicaGibbsWeightNNReal]
  have hsumNNReal :
      (∑ σs : ReplicaSpace (α := α) n, replicaGibbsWeightNNReal (α := α) (n := n) H σs) = (1 : ℝ≥0) := by
    apply NNReal.coe_injective
    simpa [replicaGibbsWeightNNReal] using (sum_prod_gibbs_pmf_eq_one (α := α) (n := n) (H := H))
  have hsumENNReal :
      (∑ σs : ReplicaSpace (α := α) n,
          (replicaGibbsWeightNNReal (α := α) (n := n) H σs : ℝ≥0∞)) = (1 : ℝ≥0∞) := by
    simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) hsumNNReal
  simpa [h_univ] using hsumENNReal

instance (n : ℕ) (H : EnergySpace α) :
    IsProbabilityMeasure (replicaGibbsMeasure (α := α) (n := n) H) :=
  ⟨replicaGibbsMeasure_univ (α := α) (n := n) (H := H)⟩

/-- `gibbs_average_n_det` is the expectation of `f` under the `n`-replica Gibbs measure. -/
lemma integral_replicaGibbsMeasure_eq_gibbs_average_n_det (n : ℕ)
    (H : EnergySpace α) (f : ReplicaFun (α := α) n) :
    (∫ σs, f σs ∂(replicaGibbsMeasure (α := α) (n := n) H)) =
      gibbs_average_n_det (α := α) (n := n) H f := by
  classical
  -- Decompose the atomic measure and integrate term-by-term.
  let μatom : ReplicaSpace (α := α) n → Measure (ReplicaSpace (α := α) n) :=
    fun σs =>
      ((replicaGibbsWeightNNReal (α := α) (n := n) H σs : ℝ≥0∞) • Measure.dirac σs)
  have h_integrable :
      ∀ σs ∈ (Finset.univ : Finset (ReplicaSpace (α := α) n)), Integrable f (μatom σs) := by
    intro σs _hσs
    have hdirac : Integrable f (Measure.dirac σs) :=
      MeasureTheory.integrable_dirac (a := σs) (f := f) (by simp)
    exact hdirac.smul_measure (by simp)
  have hsum :
      (∫ x, f x ∂((Finset.univ : Finset (ReplicaSpace (α := α) n)).sum μatom)) =
        (Finset.univ : Finset (ReplicaSpace (α := α) n)).sum fun σs => ∫ x, f x ∂(μatom σs) := by
    simpa using
      (MeasureTheory.integral_finset_sum_measure
        (f := f) (μ := μatom) (s := (Finset.univ : Finset (ReplicaSpace (α := α) n))) h_integrable)
  simpa [replicaGibbsMeasure, μatom, gibbs_average_n_det, replicaGibbsWeightNNReal, mul_comm, mul_left_comm,
    mul_assoc] using hsum

end

end FiniteGibbs

end SpinGlass

