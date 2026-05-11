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

variable {α : Type*} [Fintype α] [Nonempty α]

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
    refine Finset.prod_nonneg ?_
    intro l _hl
    exact gibbs_pmf_nonneg (α := α) (H := H) (σ := σs l)⟩

@[simp] lemma replicaGibbsWeightNNReal_coe (n : ℕ) (H : EnergySpace α)
    (σs : ReplicaSpace (α := α) n) :
    (replicaGibbsWeightNNReal (α := α) (n := n) H σs : ℝ) =
      ∏ l, gibbs_pmf (α := α) H (σs l) := rfl

/-! ## Normalization and bracket-as-integral -/

/--
The product Gibbs weights on `n` replicas sum to `1`.
-/
lemma sum_prod_gibbs_pmf_eq_one (n : ℕ) (H : EnergySpace α) :
    (∑ σs : ReplicaSpace (α := α) n, ∏ l, gibbs_pmf (α := α) H (σs l)) = 1 := by
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

lemma prod_gibbs_pmf_nonneg (n : ℕ) (H : EnergySpace α) (σs : ReplicaSpace (α := α) n) :
    0 ≤ ∏ l, gibbs_pmf (α := α) H (σs l) :=
  Finset.prod_nonneg fun l _hl => gibbs_pmf_nonneg (α := α) (H := H) (σs l)

@[simp] lemma replicaGibbsWeightNNReal_coe_ennreal (n : ℕ) (H : EnergySpace α)
    (σs : ReplicaSpace (α := α) n) :
    (replicaGibbsWeightNNReal (α := α) (n := n) H σs : ℝ≥0∞) =
      ENNReal.ofReal (∏ l, gibbs_pmf (α := α) H (σs l)) := by
  have hnn :
      replicaGibbsWeightNNReal (α := α) (n := n) H σs =
        ⟨∏ l, gibbs_pmf (α := α) H (σs l),
          prod_gibbs_pmf_nonneg (α := α) (n := n) (H := H) σs⟩ := by
    ext
    simp [replicaGibbsWeightNNReal]
  simpa [hnn] using
    (ENNReal.ofReal_eq_coe_nnreal
      (prod_gibbs_pmf_nonneg (α := α) (n := n) (H := H) σs)).symm

/-- The `n`-replica Gibbs distribution as a `PMF`. -/
noncomputable def replicaGibbsPMF (n : ℕ) (H : EnergySpace α) : PMF (ReplicaSpace (α := α) n) :=
  PMF.ofFintype
    (fun σs : ReplicaSpace (α := α) n => ENNReal.ofReal (∏ l, gibbs_pmf (α := α) H (σs l))) <| by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · simp [sum_prod_gibbs_pmf_eq_one (α := α) (n := n) (H := H)]
      · intro σs _hσs
        exact prod_gibbs_pmf_nonneg (α := α) (n := n) (H := H) σs

@[simp] lemma replicaGibbsPMF_apply (n : ℕ) (H : EnergySpace α)
    (σs : ReplicaSpace (α := α) n) :
    replicaGibbsPMF (α := α) (n := n) H σs =
      ENNReal.ofReal (∏ l, gibbs_pmf (α := α) H (σs l)) :=
  rfl

variable [MeasurableSpace α]

/-- The `n`-replica Gibbs measure as an explicit finite atomic measure on `ReplicaSpace α n`. -/
noncomputable def replicaGibbsMeasure (n : ℕ) (H : EnergySpace α) : Measure (ReplicaSpace (α := α) n) :=
  (replicaGibbsPMF (α := α) (n := n) H).toMeasure

lemma replicaGibbsMeasure_univ (n : ℕ) (H : EnergySpace α) :
    replicaGibbsMeasure (α := α) (n := n) H Set.univ = 1 := by
  simp [replicaGibbsMeasure]

instance (n : ℕ) (H : EnergySpace α) :
    IsProbabilityMeasure (replicaGibbsMeasure (α := α) (n := n) H) :=
  by
    dsimp [replicaGibbsMeasure]
    infer_instance

variable [MeasurableSingletonClass α]

lemma lintegral_replicaGibbsMeasure (n : ℕ) (H : EnergySpace α)
    (f : ReplicaSpace (α := α) n → ℝ≥0∞) :
    (∫⁻ σs, f σs ∂replicaGibbsMeasure (α := α) (n := n) H) =
      ∑ σs : ReplicaSpace (α := α) n,
        (replicaGibbsWeightNNReal (α := α) (n := n) H σs : ℝ≥0∞) * f σs := by
  rw [lintegral_fintype]
  refine Finset.sum_congr rfl ?_
  intro σs _hσs
  have hsingleton :
      replicaGibbsMeasure (α := α) (n := n) H ({σs} : Set (ReplicaSpace (α := α) n)) =
        (replicaGibbsWeightNNReal (α := α) (n := n) H σs : ℝ≥0∞) := by
    simpa [replicaGibbsMeasure, replicaGibbsWeightNNReal_coe_ennreal] using
      (PMF.toMeasure_apply_singleton (replicaGibbsPMF (α := α) (n := n) H) σs
        (measurableSet_singleton σs))
  rw [hsingleton, mul_comm]

/-- `gibbs_average_n_det` is the expectation of `f` under the `n`-replica Gibbs measure. -/
lemma integral_replicaGibbsMeasure_eq_gibbs_average_n_det (n : ℕ)
    (H : EnergySpace α) (f : ReplicaFun (α := α) n) :
    (∫ σs, f σs ∂(replicaGibbsMeasure (α := α) (n := n) H)) =
      gibbs_average_n_det (α := α) (n := n) H f := by
  calc
    (∫ σs, f σs ∂(replicaGibbsMeasure (α := α) (n := n) H))
        = ∑ σs : ReplicaSpace (α := α) n,
            (replicaGibbsPMF (α := α) (n := n) H σs).toReal • f σs := by
            simpa [replicaGibbsMeasure] using
              (PMF.integral_eq_sum (replicaGibbsPMF (α := α) (n := n) H) f)
    _ = gibbs_average_n_det (α := α) (n := n) H f := by
          refine Finset.sum_congr rfl ?_
          intro σs _hσs
          simp [ENNReal.toReal_ofReal (prod_gibbs_pmf_nonneg (α := α) (n := n) (H := H) σs),
            smul_eq_mul, mul_comm]

end

end FiniteGibbs

end SpinGlass
