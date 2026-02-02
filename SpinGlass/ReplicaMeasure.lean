import SpinGlass.Defs
import SpinGlass.GibbsBridge
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Data.Fintype.Pi

/-!
# Finite-volume replica measure (Talagrand, Vol. I/II)

This file isolates the **purely finite-volume** definitions around sampling `n` independent
replicas from the finite Gibbs measure.

Crucially, nothing here depends on an ambient probability space `Ω`: this makes the construction
usable as a building block for Volume II (pure states, overlap arrays, cascades) where “replicas”
are treated algebraically/measure-theoretically.
-/

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ENNReal NNReal

namespace SpinGlass

variable {N n : ℕ}

/-- The space of `n` replicas: `Fin n → Config N`. -/
abbrev ReplicaSpace (N n : ℕ) := Fin n → Config N

/-- A function of `n` replicas. -/
abbrev ReplicaFun (N n : ℕ) := ReplicaSpace N n → ℝ

/--
**Equation (1.17)** (Talagrand): the Gibbs average of a function of `n` replicas.

This is the deterministic finite-volume object (no ambient probability space).
-/
noncomputable def gibbs_average_n_det (N n : ℕ) (H : EnergySpace N) (f : ReplicaFun N n) : ℝ :=
  ∑ σs : ReplicaSpace N n, f σs * ∏ l, gibbs_pmf N H (σs l)

/-! ### Replica Gibbs measure (finite-volume, atomic) -/

/-- The `n`-replica Gibbs weight (as `ℝ≥0`): \( \prod_{l=1}^n \mathrm{gibbs\_pmf}(H,\sigma^l)\). -/
noncomputable def replicaGibbsWeightNNReal (N n : ℕ) (H : EnergySpace N) (σs : ReplicaSpace N n) : ℝ≥0 :=
  ⟨∏ l, gibbs_pmf N H (σs l), by
    classical
    refine Finset.prod_nonneg ?_
    intro l _hl
    exact gibbs_pmf_nonneg (N := N) (H := H) (σ := σs l)⟩

/-- The `n`-replica Gibbs measure as an explicit finite atomic measure on `ReplicaSpace N n`. -/
noncomputable def replicaGibbsMeasure (N n : ℕ) (H : EnergySpace N) : Measure (ReplicaSpace N n) :=
  (Finset.univ : Finset (ReplicaSpace N n)).sum fun σs =>
    ((replicaGibbsWeightNNReal (N := N) (n := n) H σs : ℝ≥0∞) • Measure.dirac σs)

/-! ### Normalization and bracket-as-integral -/

/--
The product Gibbs weights on `n` replicas sum to `1`.

This is the finite-dimensional fact that the `n`-replica Gibbs measure is the product of `n`
copies of the one-replica Gibbs measure.
-/
lemma sum_prod_gibbs_pmf_eq_one (N n : ℕ) (H : EnergySpace N) :
    (∑ σs : ReplicaSpace N n, ∏ l, gibbs_pmf N H (σs l)) = 1 := by
  classical
  induction n with
  | zero =>
      simp
  | succ n ih =>
      let p : Config N → ℝ := gibbs_pmf N H
      have hs1 : (∑ σ : Config N, p σ) = 1 := by
        simpa [p] using (SpinGlass.sum_gibbs_pmf (N := N) (H := H))
      let e : (Config N × (Fin n → Config N)) ≃ (Fin (n + 1) → Config N) :=
        Fin.consEquiv (fun _ : Fin (n + 1) => Config N)
      have hrew :
          (∑ σs : (Fin (n + 1) → Config N), ∏ l : Fin (n + 1), p (σs l))
            = ∑ x : (Config N × (Fin n → Config N)), ∏ l : Fin (n + 1), p (e x l) := by
        simpa using
          (Fintype.sum_equiv e
              (f := fun x => ∏ l : Fin (n + 1), p (e x l))
              (g := fun σs => ∏ l : Fin (n + 1), p (σs l))
              (h := fun x => rfl)).symm
      calc
        (∑ σs : (Fin (n + 1) → Config N), ∏ l : Fin (n + 1), p (σs l))
            = ∑ x : (Config N × (Fin n → Config N)), ∏ l : Fin (n + 1), p (e x l) := hrew
        _ = ∑ σ₀ : Config N, ∑ σtail : (Fin n → Config N),
              p σ₀ * (∏ i : Fin n, p (σtail i)) := by
              classical
              simp [Fintype.sum_prod_type, e, p, Fin.prod_univ_succ]
        _ = ∑ σ₀ : Config N, p σ₀ * (∑ σtail : (Fin n → Config N), ∏ i : Fin n, p (σtail i)) := by
              classical
              simp [Finset.mul_sum]
        _ = ∑ σ₀ : Config N, p σ₀ * 1 := by
              simpa [p] using congrArg (fun r => ∑ σ₀ : Config N, p σ₀ * r) ih
        _ = ∑ σ₀ : Config N, p σ₀ := by simp
        _ = 1 := hs1

lemma replicaGibbsMeasure_univ (N n : ℕ) (H : EnergySpace N) :
    replicaGibbsMeasure (N := N) (n := n) H Set.univ = 1 := by
  classical
  have h_univ :
      replicaGibbsMeasure (N := N) (n := n) H Set.univ
        =
        ∑ σs : ReplicaSpace N n, (replicaGibbsWeightNNReal (N := N) (n := n) H σs : ℝ≥0∞) := by
    simp [replicaGibbsMeasure, replicaGibbsWeightNNReal]
  have hsumNNReal :
      (∑ σs : ReplicaSpace N n, replicaGibbsWeightNNReal (N := N) (n := n) H σs) = (1 : ℝ≥0) := by
    apply NNReal.coe_injective
    simpa [replicaGibbsWeightNNReal] using (sum_prod_gibbs_pmf_eq_one (N := N) (n := n) (H := H))
  have hsumENNReal :
      (∑ σs : ReplicaSpace N n,
          (replicaGibbsWeightNNReal (N := N) (n := n) H σs : ℝ≥0∞)) = (1 : ℝ≥0∞) := by
    simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) hsumNNReal
  simpa [h_univ] using hsumENNReal

instance (N n : ℕ) (H : EnergySpace N) : IsProbabilityMeasure (replicaGibbsMeasure (N := N) (n := n) H) :=
  ⟨replicaGibbsMeasure_univ (N := N) (n := n) (H := H)⟩

/-- `gibbs_average_n_det` is the expectation of `f` under the `n`-replica Gibbs measure. -/
lemma integral_replicaGibbsMeasure_eq_gibbs_average_n_det (N n : ℕ)
    (H : EnergySpace N) (f : ReplicaFun N n) :
    (∫ σs, f σs ∂(replicaGibbsMeasure (N := N) (n := n) H)) =
      gibbs_average_n_det (N := N) (n := n) H f := by
  classical
  -- Decompose the atomic measure and integrate term-by-term.
  let μatom : ReplicaSpace N n → Measure (ReplicaSpace N n) :=
    fun σs =>
      ((replicaGibbsWeightNNReal (N := N) (n := n) H σs : ℝ≥0∞) • Measure.dirac σs)
  have h_integrable :
      ∀ σs ∈ (Finset.univ : Finset (ReplicaSpace N n)), Integrable f (μatom σs) := by
    intro σs _hσs
    haveI : MeasurableSingletonClass (ReplicaSpace N n) := by infer_instance
    have hdirac : Integrable f (Measure.dirac σs) :=
      MeasureTheory.integrable_dirac (a := σs) (f := f) (by simp)
    exact hdirac.smul_measure (by simp)
  have hsum :
      (∫ x, f x ∂((Finset.univ : Finset (ReplicaSpace N n)).sum μatom)) =
        (Finset.univ : Finset (ReplicaSpace N n)).sum fun σs => ∫ x, f x ∂(μatom σs) := by
    simpa using
      (MeasureTheory.integral_finset_sum_measure
        (f := f) (μ := μatom) (s := (Finset.univ : Finset (ReplicaSpace N n))) h_integrable)
  simpa [replicaGibbsMeasure, μatom, gibbs_average_n_det, replicaGibbsWeightNNReal, mul_comm, mul_left_comm,
    mul_assoc] using hsum

end SpinGlass

