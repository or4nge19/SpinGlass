import SpinGlass.FiniteGibbs
import SpinGlass.FiniteGibbs.GibbsMeasure
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Data.Fintype.Pi

/-!
# Finite-volume replica Gibbs measure

`n` independent replicas from the finite Gibbs measure on a finite type `α`. Main:
`replicaGibbsMeasure`, `gibbs_average_n_det`.
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

/-- Deterministic Gibbs average of a function of `n` replicas. -/
noncomputable def gibbs_average_n_det (n : ℕ) (H : EnergySpace α) (f : ReplicaFun (α := α) n) : ℝ :=
  ∑ σs : ReplicaSpace (α := α) n, f σs * ∏ l, gibbs_pmf (α := α) H (σs l)

/-! ## The replica Gibbs measure is the product of `n` Gibbs measures -/

/-- The `n`-replica Gibbs measure: `n` independent copies of the finite-volume Gibbs measure.

It **is** Mathlib's product measure `Measure.pi`, not a new object. Consequently the whole
`Measure.pi` API applies to the replica bracket verbatim: normalisation, Fubini, the marginals,
and the invariance under permutations of the replica labels
(`map_comp_perm_replicaGibbsMeasure`) that makes the replicas exchangeable. -/
noncomputable def replicaGibbsMeasure (n : ℕ) (H : EnergySpace α) :
    Measure (ReplicaSpace (α := α) n) :=
  Measure.pi fun _ : Fin n => gibbsMeasure (α := α) H

instance (n : ℕ) (H : EnergySpace α) :
    IsProbabilityMeasure (replicaGibbsMeasure (α := α) (n := n) H) := by
  rw [replicaGibbsMeasure]
  infer_instance

omit [MeasurableSingletonClass α] in
lemma replicaGibbsMeasure_univ (n : ℕ) (H : EnergySpace α) :
    replicaGibbsMeasure (α := α) (n := n) H Set.univ = 1 := measure_univ

/-- The atoms of the replica Gibbs measure are the products of the Gibbs weights. -/
lemma replicaGibbsMeasure_apply_singleton (n : ℕ) (H : EnergySpace α)
    (σs : ReplicaSpace (α := α) n) :
    replicaGibbsMeasure (α := α) (n := n) H {σs}
      = ∏ l : Fin n, ENNReal.ofReal (gibbs_pmf (α := α) H (σs l)) := by
  classical
  have hset : ({σs} : Set (ReplicaSpace (α := α) n))
      = Set.univ.pi fun l : Fin n => ({σs l} : Set α) := by
    ext τs
    simp [Set.mem_pi, Set.mem_singleton_iff, funext_iff]
  rw [replicaGibbsMeasure, hset, Measure.pi_pi]
  exact Finset.prod_congr rfl fun l _ => gibbsMeasure_apply_singleton (α := α) H (σs l)

/-! ## Normalization and bracket-as-integral -/

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Product Gibbs weights on `n` replicas sum to `1`: the product of `n` copies of `∑ p = 1`. -/
lemma sum_prod_gibbs_pmf_eq_one (n : ℕ) (H : EnergySpace α) :
    (∑ σs : ReplicaSpace (α := α) n, ∏ l, gibbs_pmf (α := α) H (σs l)) = 1 := by
  classical
  have hfac : (∑ σs : ReplicaSpace (α := α) n, ∏ l : Fin n, gibbs_pmf (α := α) H (σs l))
      = ∏ _l : Fin n, ∑ x : α, gibbs_pmf (α := α) H x := by
    rw [← Finset.sum_prod_piFinset]
    exact Finset.sum_congr (by simp [Fintype.piFinset_univ]) fun _ _ => rfl
  rw [hfac, Finset.prod_congr rfl fun l _ => sum_gibbs_pmf (α := α) H, Finset.prod_const_one]

/-- `gibbs_average_n_det` is the expectation of `f` under the `n`-replica Gibbs measure. -/
lemma integral_replicaGibbsMeasure_eq_gibbs_average_n_det (n : ℕ)
    (H : EnergySpace α) (f : ReplicaFun (α := α) n) :
    (∫ σs, f σs ∂(replicaGibbsMeasure (α := α) (n := n) H)) =
      gibbs_average_n_det (α := α) (n := n) H f := by
  classical
  rw [integral_fintype Integrable.of_finite, gibbs_average_n_det]
  refine Finset.sum_congr rfl fun σs _ => ?_
  rw [measureReal_def, replicaGibbsMeasure_apply_singleton, ← ENNReal.ofReal_prod_of_nonneg
    (fun l _ => gibbs_pmf_nonneg (α := α) H (σs l)),
    ENNReal.toReal_ofReal (Finset.prod_nonneg fun l _ => gibbs_pmf_nonneg (α := α) H (σs l))]
  rw [smul_eq_mul, mul_comm]

/-! ## Exchangeability of the replicas -/

omit [MeasurableSingletonClass α] in
/-- **The replicas are exchangeable**: permuting the replica labels leaves the `n`-replica Gibbs
measure invariant. This is Mathlib's invariance of a product measure under a permutation of the
index, `MeasureTheory.measurePreserving_piCongrLeft`, and it is the hypothesis of de Finetti's
theorem and of the Aldous–Hoover representation. -/
lemma measurePreserving_comp_perm_replicaGibbsMeasure (n : ℕ) (H : EnergySpace α)
    (e : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun σs : ReplicaSpace (α := α) n => σs ∘ e)
      (replicaGibbsMeasure (α := α) (n := n) H) (replicaGibbsMeasure (α := α) (n := n) H) := by
  have h := measurePreserving_piCongrLeft (fun _ : Fin n => gibbsMeasure (α := α) H) e.symm
  have hfun : ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin n => α) e.symm)
      = fun σs : ReplicaSpace (α := α) n => σs ∘ e := by
    funext σs
    funext j
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rw [replicaGibbsMeasure, ← hfun]
  exact h

/-- The bracket form of exchangeability: relabelling the replicas by a permutation does not change
the `n`-replica Gibbs average. -/
lemma gibbs_average_n_det_comp_perm (n : ℕ) (H : EnergySpace α) (f : ReplicaFun (α := α) n)
    (e : Equiv.Perm (Fin n)) :
    gibbs_average_n_det (α := α) (n := n) H (fun σs => f (σs ∘ e))
      = gibbs_average_n_det (α := α) (n := n) H f := by
  have h := measurePreserving_comp_perm_replicaGibbsMeasure (α := α) n H e
  rw [← integral_replicaGibbsMeasure_eq_gibbs_average_n_det,
    ← integral_replicaGibbsMeasure_eq_gibbs_average_n_det]
  conv_rhs => rw [← h.map_eq]
  rw [integral_map h.measurable.aemeasurable
    (StronglyMeasurable.of_discrete).aestronglyMeasurable]

end

end FiniteGibbs

end SpinGlass
