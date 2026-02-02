import SpinGlass.GibbsBridge
import SpinGlass.ReplicaMeasure
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Vol II bridge: Gibbs samplers as kernels, replicas as product kernels

Talagrand Vol. II and Georgii-style “structure first” arguments become much cleaner if we can treat

- sampling a configuration from a finite-volume Gibbs law as a **Markov kernel**;
- sampling `n` replicas as the corresponding **replica kernel**.

This file defines those kernels in a way that is definitionally consistent with the existing
finite-volume atomic measures (`gibbsMeasure`, `replicaGibbsMeasure`) and proves measurability
without adding topological assumptions beyond what is already present on `EnergySpace N`.
-/

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ENNReal NNReal

namespace SpinGlass

variable (N : ℕ)

namespace KernelBridge

/-! ## Measurability helpers for the finite Gibbs weights -/

lemma measurable_eval (σ : Config N) : Measurable fun H : EnergySpace N => H σ := by
  -- Use the inner-product representation of evaluation.
  classical
  have hcont : Continuous fun H : EnergySpace N => inner ℝ (std_basis N σ) H := by
    have hpair : Continuous fun H : EnergySpace N => (std_basis N σ, H) :=
      continuous_const.prodMk continuous_id
    simpa using (continuous_inner.comp hpair)
  have : (fun H : EnergySpace N => H σ) = fun H => inner ℝ (std_basis N σ) H := by
    funext H
    simp [inner_std_basis_apply]
  simpa [this] using hcont.measurable

lemma measurable_Z : Measurable fun H : EnergySpace N => Z (N := N) H := by
  classical
  -- Finite sum of measurable functions.
  have hmeas_term :
      ∀ σ ∈ (Finset.univ : Finset (Config N)),
        Measurable fun H : EnergySpace N => Real.exp (-H σ) := by
    intro σ _hσ
    have : Measurable fun H : EnergySpace N => H σ := measurable_eval (N := N) σ
    fun_prop
  simpa [Z] using (Finset.measurable_sum (s := (Finset.univ : Finset (Config N))) hmeas_term)

lemma measurable_gibbs_pmf (σ : Config N) : Measurable fun H : EnergySpace N => gibbs_pmf N H σ := by
  classical
  -- `exp` and division are measurable.
  have hmeas_num : Measurable fun H : EnergySpace N => Real.exp (-H σ) := by
    have : Measurable fun H : EnergySpace N => H σ := measurable_eval (N := N) σ
    fun_prop
  have hmeas_den : Measurable fun H : EnergySpace N => Z (N := N) H := measurable_Z (N := N)
  simpa [gibbs_pmf] using hmeas_num.div hmeas_den

lemma measurable_gibbsWeightENNReal (σ : Config N) :
    Measurable fun H : EnergySpace N => ENNReal.ofReal (gibbs_pmf N H σ) := by
  simpa using (ENNReal.measurable_ofReal.comp (measurable_gibbs_pmf (N := N) σ))

/-! ## The Gibbs sampler as a Markov kernel -/

/-- The finite-volume Gibbs sampler: a kernel from energies to configurations. -/
noncomputable def gibbsKernel : Kernel (EnergySpace N) (Config N) where
  toFun := fun H => gibbsMeasure (N := N) H
  measurable' := by
    -- Show: for each measurable `s`, `H ↦ gibbsMeasure H s` is measurable.
    classical
    refine Measure.measurable_of_measurable_coe (fun H => gibbsMeasure (N := N) H) ?_
    intro s hs
    -- Expand the atomic sum-of-diracs and rewrite weights via `ENNReal.ofReal`.
    have hsum :
        (fun H : EnergySpace N => gibbsMeasure (N := N) H s)
          =
        fun H =>
          ∑ σ : Config N,
            (if σ ∈ s then ENNReal.ofReal (gibbs_pmf N H σ) else 0) := by
      funext H
      classical
      -- Evaluate each atom on `s`.
      -- `dirac_apply'` evaluates to an indicator; simplify the scalar multiplication.
      simp [SpinGlass.gibbsMeasure, SpinGlass.gibbsWeightNNReal, hs,
        Measure.dirac_apply', ENNReal.ofReal_eq_coe_nnreal, gibbs_pmf_nonneg, Set.indicator]
    -- Measurable as a finite sum of measurable terms.
    have hterm :
        ∀ σ ∈ (Finset.univ : Finset (Config N)),
          Measurable fun H : EnergySpace N =>
            (if σ ∈ s then ENNReal.ofReal (gibbs_pmf N H σ) else 0) := by
      intro σ _hσ
      by_cases hσ' : σ ∈ s
      · simp [hσ', measurable_gibbsWeightENNReal (N := N) σ]
      · simp [hσ']
    simpa [hsum] using (Finset.measurable_sum (s := (Finset.univ : Finset (Config N))) hterm)

instance : IsMarkovKernel (gibbsKernel (N := N)) := by
  refine ⟨fun H => ?_⟩
  -- `gibbsMeasure` is already a probability measure.
  simpa [gibbsKernel] using (by infer_instance : IsProbabilityMeasure (gibbsMeasure (N := N) H))

/-! ## Replica sampling kernel (finite-volume) -/

variable (n : ℕ)

/-- The `n`-replica Gibbs sampler as a Markov kernel. -/
noncomputable def replicaGibbsKernel : Kernel (EnergySpace N) (ReplicaSpace N n) where
  toFun := fun H => replicaGibbsMeasure (N := N) (n := n) H
  measurable' := by
    classical
    refine Measure.measurable_of_measurable_coe (fun H => replicaGibbsMeasure (N := N) (n := n) H) ?_
    intro s hs
    have hsum :
        (fun H : EnergySpace N => replicaGibbsMeasure (N := N) (n := n) H s)
          =
        fun H =>
          ∑ σs : ReplicaSpace N n,
            (if σs ∈ s then (replicaGibbsWeightNNReal (N := N) (n := n) H σs : ℝ≥0∞) else 0) := by
      funext H
      classical
      simp [SpinGlass.replicaGibbsMeasure, SpinGlass.replicaGibbsWeightNNReal, hs,
        Measure.dirac_apply', Set.indicator]
    have hterm :
        ∀ σs ∈ (Finset.univ : Finset (ReplicaSpace N n)),
          Measurable fun H : EnergySpace N =>
            (if σs ∈ s then (replicaGibbsWeightNNReal (N := N) (n := n) H σs : ℝ≥0∞) else 0) := by
      intro σs _hσs
      by_cases hσs' : σs ∈ s
      · have hprod : Measurable fun H : EnergySpace N => ∏ l, gibbs_pmf N H (σs l) := by
          classical
          have hfac : ∀ l ∈ (Finset.univ : Finset (Fin n)),
              Measurable fun H : EnergySpace N => gibbs_pmf N H (σs l) := by
            intro l _hl
            simpa using measurable_gibbs_pmf (N := N) (σ := σs l)
          simpa using
            (Finset.measurable_prod (s := (Finset.univ : Finset (Fin n))) hfac)
        have hnn : Measurable fun H : EnergySpace N => replicaGibbsWeightNNReal (N := N) (n := n) H σs := by
          simpa [SpinGlass.replicaGibbsWeightNNReal] using (Measurable.subtype_mk hprod)
        have hcoe : Measurable fun H : EnergySpace N =>
            (replicaGibbsWeightNNReal (N := N) (n := n) H σs : ℝ≥0∞) := by
          have h_ofReal :
              Measurable fun H : EnergySpace N =>
                ENNReal.ofReal (replicaGibbsWeightNNReal (N := N) (n := n) H σs : ℝ) :=
            ENNReal.measurable_ofReal.comp (measurable_coe_nnreal_real.comp hnn)
          have hconv : (fun H : EnergySpace N =>
                  (replicaGibbsWeightNNReal (N := N) (n := n) H σs : ℝ≥0∞)) =
              fun H : EnergySpace N =>
                ENNReal.ofReal (replicaGibbsWeightNNReal (N := N) (n := n) H σs : ℝ) := by
            funext H
            simp
          simpa [hconv] using h_ofReal
        simp [hσs', hcoe]
      · simp [hσs']
    simpa [hsum] using (Finset.measurable_sum (s := (Finset.univ : Finset (ReplicaSpace N n))) hterm)

instance : IsMarkovKernel (replicaGibbsKernel (N := N) (n := n)) := by
  refine ⟨fun H => ?_⟩
  simpa [replicaGibbsKernel] using
    (by infer_instance : IsProbabilityMeasure (replicaGibbsMeasure (N := N) (n := n) H))

end KernelBridge

end SpinGlass
