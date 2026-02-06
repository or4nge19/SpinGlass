import SpinGlass.Defs
import SpinGlass.GibbsBridge
import SpinGlass.FiniteGibbs.ReplicaMeasure
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
  FiniteGibbs.gibbs_average_n_det (α := Config N) (n := n) H f

/-! ### Replica Gibbs measure (finite-volume, atomic) -/

/-- The `n`-replica Gibbs weight (as `ℝ≥0`): \( \prod_{l=1}^n \mathrm{gibbs\_pmf}(H,\sigma^l)\). -/
noncomputable def replicaGibbsWeightNNReal (N n : ℕ) (H : EnergySpace N) (σs : ReplicaSpace N n) : ℝ≥0 :=
  FiniteGibbs.replicaGibbsWeightNNReal (α := Config N) (n := n) H σs

/-- The `n`-replica Gibbs measure as an explicit finite atomic measure on `ReplicaSpace N n`. -/
noncomputable def replicaGibbsMeasure (N n : ℕ) (H : EnergySpace N) : Measure (ReplicaSpace N n) :=
  FiniteGibbs.replicaGibbsMeasure (α := Config N) (n := n) H

/-! ### Normalization and bracket-as-integral -/

/--
The product Gibbs weights on `n` replicas sum to `1`.

This is the finite-dimensional fact that the `n`-replica Gibbs measure is the product of `n`
copies of the one-replica Gibbs measure.
-/
lemma sum_prod_gibbs_pmf_eq_one (N n : ℕ) (H : EnergySpace N) :
    (∑ σs : ReplicaSpace N n, ∏ l, gibbs_pmf N H (σs l)) = 1 := by
  -- Delegate to the configuration-agnostic replica calculus.
  simpa [SpinGlass.gibbs_pmf, SpinGlass.Z, FiniteGibbs.gibbs_pmf, FiniteGibbs.Z, ReplicaSpace] using
    (FiniteGibbs.sum_prod_gibbs_pmf_eq_one (α := Config N) (n := n) (H := H))

lemma replicaGibbsMeasure_univ (N n : ℕ) (H : EnergySpace N) :
    replicaGibbsMeasure (N := N) (n := n) H Set.univ = 1 := by
  simpa [replicaGibbsMeasure] using
    (FiniteGibbs.replicaGibbsMeasure_univ (α := Config N) (n := n) (H := H))

instance (N n : ℕ) (H : EnergySpace N) : IsProbabilityMeasure (replicaGibbsMeasure (N := N) (n := n) H) :=
  by
    -- Inherit from the generic instance.
    simpa [replicaGibbsMeasure] using
      (by infer_instance :
        IsProbabilityMeasure (FiniteGibbs.replicaGibbsMeasure (α := Config N) (n := n) H))

/-- `gibbs_average_n_det` is the expectation of `f` under the `n`-replica Gibbs measure. -/
lemma integral_replicaGibbsMeasure_eq_gibbs_average_n_det (N n : ℕ)
    (H : EnergySpace N) (f : ReplicaFun N n) :
    (∫ σs, f σs ∂(replicaGibbsMeasure (N := N) (n := n) H)) =
      gibbs_average_n_det (N := N) (n := n) H f := by
  -- Delegate to the configuration-agnostic replica calculus.
  simpa [replicaGibbsMeasure, gibbs_average_n_det, ReplicaSpace] using
    (FiniteGibbs.integral_replicaGibbsMeasure_eq_gibbs_average_n_det
      (α := Config N) (n := n) (H := H) (f := f))

end SpinGlass
