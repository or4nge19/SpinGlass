/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.PointProcess.PoissonFinite
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.HasLaw

/-!
# Poisson point processes with σ-finite intensity

The Poisson point process with intensity `∑ₙ νₙ`, for finite measures `νₙ`, is the superposition
of independent finite Poisson point processes with intensities `νₙ`. We realise it on the
infinite product of the finite sample spaces and record its counting measure
`∑ₙ Nₙ` as a `Measure`-valued random variable.

Its Laplace functional is the product of the Laplace functionals of the pieces, hence

`𝔼 exp (-∫ φ dN) = exp (-∫ (1 - e^{-φ}) d(∑ₙ νₙ))`,

by dominated convergence along the partial products.

## Main statements

- `ENNReal.continuous_negExp`, `ENNReal.tendsto_prod_negExp_tsum`.
- `ProbabilityTheory.superSampleLaw`, `ProbabilityTheory.superCounting`,
  `ProbabilityTheory.measurable_superCounting`.
- `ProbabilityTheory.integral_negExp_superCounting`: **the Laplace functional**.
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

namespace ENNReal

lemma tendsto_negExp_nhds_top : Tendsto negExp (𝓝 ∞) (𝓝 0) := by
  rw [nhds_top']
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨r, hr⟩ : ∃ r : ℝ≥0, Real.exp (-(r : ℝ)) < ε := by
    refine ⟨Real.toNNReal (1 - Real.log ε), ?_⟩
    have h1 : 1 - Real.log ε ≤ (Real.toNNReal (1 - Real.log ε) : ℝ) := Real.le_coe_toNNReal _
    calc Real.exp (-(Real.toNNReal (1 - Real.log ε) : ℝ))
        ≤ Real.exp (-(1 - Real.log ε)) := Real.exp_le_exp.2 (by linarith)
      _ = ε / Real.exp 1 := by rw [neg_sub, Real.exp_sub, Real.exp_log hε]
      _ < ε := by
          rw [div_lt_iff₀ (Real.exp_pos 1)]
          have := Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)
          nlinarith [Real.exp_pos 1]
  refine Filter.mem_iInf_of_mem r ?_
  rw [Filter.mem_principal]
  intro x hx
  rw [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, abs_of_nonneg (negExp_nonneg x)]
  rcases eq_or_ne x ∞ with hx' | hx'
  · rw [hx', negExp_top]; exact hε
  · rw [negExp_of_ne_top hx']
    refine lt_of_le_of_lt (Real.exp_le_exp.2 (neg_le_neg ?_)) hr
    have h := ENNReal.toReal_mono hx' (le_of_lt (Set.mem_Ioi.1 hx))
    simpa using h

lemma continuous_negExp : Continuous negExp := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  rcases eq_or_ne t ∞ with ht | ht
  · rw [ht, ContinuousAt, negExp_top]
    exact tendsto_negExp_nhds_top
  · have hmem : {a : ℝ≥0∞ | a ≠ ∞} ∈ 𝓝 t := isOpen_ne_top.mem_nhds ht
    have hc : ContinuousAt (fun a : ℝ≥0∞ => Real.exp (-a.toReal)) t :=
      (Real.continuous_exp.continuousAt.comp
        (continuous_neg.continuousAt.comp (continuousOn_toReal.continuousAt hmem)))
    refine hc.congr (Filter.mem_of_superset hmem fun a ha => ?_)
    exact (negExp_of_ne_top ha).symm

/-- `exp (-∑' aₙ)` is the limit of the partial products `∏_{n < K} exp (-aₙ)`. -/
lemma tendsto_prod_negExp_tsum (a : ℕ → ℝ≥0∞) :
    Tendsto (fun K : ℕ => ∏ n ∈ Finset.range K, negExp (a n)) atTop
      (𝓝 (negExp (∑' n, a n))) := by
  have := (continuous_negExp.tendsto _).comp (ENNReal.tendsto_nat_tsum a)
  refine this.congr fun K => ?_
  simp [Function.comp, negExp_finset_sum]

end ENNReal

namespace ProbabilityTheory

open ENNReal

variable {E : Type*} [MeasurableSpace E] [Nonempty E]

/-- The sample space of a superposition of countably many finite Poisson point processes. -/
abbrev SuperSample (E : Type*) := ℕ → PoissonSample E

/-- Independent finite Poisson samples with intensities `ν n`. -/
noncomputable def superSampleLaw (ν : ℕ → Measure E) [∀ n, IsFiniteMeasure (ν n)] :
    Measure (SuperSample E) :=
  Measure.infinitePi fun n => poissonSampleLaw (ν n)

instance (ν : ℕ → Measure E) [∀ n, IsFiniteMeasure (ν n)] :
    IsProbabilityMeasure (superSampleLaw ν) := by
  unfold superSampleLaw; infer_instance

/-- The counting measure of the superposition: the sum of the counting measures of the pieces. -/
noncomputable def superCounting (ω : SuperSample E) : Measure E :=
  Measure.sum fun n => countingMeasure (ω n)

omit [Nonempty E] in
lemma lintegral_superCounting (ω : SuperSample E) (φ : E → ℝ≥0∞) :
    ∫⁻ x, φ x ∂superCounting ω = ∑' n, ∫⁻ x, φ x ∂countingMeasure (ω n) := by
  rw [superCounting, lintegral_sum_measure]

omit [Nonempty E] in
lemma measurable_superCounting : Measurable (superCounting : SuperSample E → Measure E) := by
  refine Measure.measurable_of_measurable_coe superCounting fun s hs => ?_
  simp only [superCounting, Measure.sum_apply _ hs]
  exact Measurable.tsum fun n =>
    (Measure.measurable_coe hs).comp (measurable_countingMeasure.comp (measurable_pi_apply n))

/-- The law of the Poisson point process with intensity `∑ₙ νₙ`, as a measure on the space of
measures. -/
noncomputable def poissonPointProcessSum (ν : ℕ → Measure E) [∀ n, IsFiniteMeasure (ν n)] :
    Measure (Measure E) :=
  (superSampleLaw ν).map superCounting

instance (ν : ℕ → Measure E) [∀ n, IsFiniteMeasure (ν n)] :
    IsProbabilityMeasure (poissonPointProcessSum ν) := by
  unfold poissonPointProcessSum
  exact Measure.isProbabilityMeasure_map measurable_superCounting.aemeasurable

/-- **The Laplace functional of a σ-finite Poisson point process.** For measurable
`φ : E → ℝ≥0∞`, `𝔼 exp (-∫ φ dN) = exp (-∫ (1 - e^{-φ}) d(∑ₙ νₙ))`. -/
theorem integral_negExp_superCounting (ν : ℕ → Measure E) [∀ n, IsFiniteMeasure (ν n)]
    {φ : E → ℝ≥0∞} (hφ : Measurable φ) :
    ∫ ω, negExp (∫⁻ x, φ x ∂superCounting ω) ∂superSampleLaw ν
      = negExp (∫⁻ x, (1 - ENNReal.ofReal (negExp (φ x))) ∂Measure.sum ν) := by
  classical
  have hmeas : ∀ n, Measurable fun ω : SuperSample E => ∫⁻ x, φ x ∂countingMeasure (ω n) :=
    fun n => (Measure.measurable_lintegral hφ).comp
      (measurable_countingMeasure.comp (measurable_pi_apply n))
  simp_rw [lintegral_superCounting]
  have hlim : ∀ ω : SuperSample E, Tendsto
      (fun K => ∏ n ∈ Finset.range K, negExp (∫⁻ x, φ x ∂countingMeasure (ω n))) atTop
      (𝓝 (negExp (∑' n, ∫⁻ x, φ x ∂countingMeasure (ω n)))) :=
    fun ω => tendsto_prod_negExp_tsum _
  have hFmeas : ∀ K, AEStronglyMeasurable
      (fun ω : SuperSample E => ∏ n ∈ Finset.range K, negExp (∫⁻ x, φ x ∂countingMeasure (ω n)))
      (superSampleLaw ν) := fun K =>
    (Finset.measurable_prod _ fun n _ => measurable_negExp.comp (hmeas n)).aestronglyMeasurable
  have hbound : ∀ K, ∀ᵐ ω ∂superSampleLaw ν,
      ‖∏ n ∈ Finset.range K, negExp (∫⁻ x, φ x ∂countingMeasure (ω n))‖ ≤ (1 : ℝ) :=
    fun K => Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun n _ => negExp_nonneg _)]
      exact Finset.prod_le_one (fun n _ => negExp_nonneg _) (fun n _ => negExp_le_one _)
  have hdom := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) hFmeas
    (integrable_const 1) hbound (Filter.Eventually.of_forall hlim)
  have hprod : ∀ K, ∫ ω, ∏ n ∈ Finset.range K, negExp (∫⁻ x, φ x ∂countingMeasure (ω n))
      ∂superSampleLaw ν
      = ∏ n ∈ Finset.range K, negExp (∫⁻ x, (1 - ENNReal.ofReal (negExp (φ x))) ∂ν n) := by
    intro K
    rw [superSampleLaw, integral_prod_range_infinitePi' (fun n => poissonSampleLaw (ν n))
      (g := fun _ p => negExp (∫⁻ x, φ x ∂countingMeasure p))
      (fun _ => measurable_negExp.comp ((Measure.measurable_lintegral hφ).comp
        measurable_countingMeasure)) K]
    exact Finset.prod_congr rfl fun n _ => integral_negExp_countingMeasure (ν n) hφ
  simp_rw [hprod] at hdom
  have hR : Tendsto
      (fun K => ∏ n ∈ Finset.range K, negExp (∫⁻ x, (1 - ENNReal.ofReal (negExp (φ x))) ∂ν n))
      atTop (𝓝 (negExp (∫⁻ x, (1 - ENNReal.ofReal (negExp (φ x))) ∂Measure.sum ν))) := by
    rw [lintegral_sum_measure]
    exact tendsto_prod_negExp_tsum _
  exact tendsto_nhds_unique hdom hR

/-! ### Void probabilities -/

/-- **Void probabilities**: `P (N B = 0) = exp (-(∑ₙ νₙ) B)`. The Laplace functional at
`φ = ∞ · 1_B`. -/
theorem measureReal_superCounting_eq_zero (ν : ℕ → Measure E) [∀ n, IsFiniteMeasure (ν n)]
    {B : Set E} (hB : MeasurableSet B) :
    (superSampleLaw ν).real {ω | superCounting ω B = 0} = negExp (Measure.sum ν B) := by
  have hind : Measurable (B.indicator (1 : E → ℝ≥0∞)) := measurable_one.indicator hB
  have hφ : Measurable fun x => (∞ : ℝ≥0∞) * B.indicator 1 x := measurable_const.mul hind
  have h := integral_negExp_superCounting ν hφ
  have h1 : ∀ ω : SuperSample E, negExp (∫⁻ x, ∞ * B.indicator 1 x ∂superCounting ω)
      = {ω : SuperSample E | superCounting ω B = 0}.indicator 1 ω := by
    intro ω
    rw [lintegral_const_mul _ hind, lintegral_indicator_one hB, negExp_top_mul]
    by_cases h0 : superCounting ω B = 0 <;> simp [h0]
  have h2 : ∀ x, (1 - ENNReal.ofReal (negExp (∞ * B.indicator 1 x))) = B.indicator 1 x := by
    intro x
    by_cases hx : x ∈ B <;> simp [hx]
  simp_rw [h1, h2] at h
  have hset : MeasurableSet {ω : SuperSample E | superCounting ω B = 0} :=
    measurableSet_eq_fun ((Measure.measurable_coe hB).comp measurable_superCounting)
      measurable_const
  rw [integral_indicator_one hset, lintegral_indicator_one hB] at h
  exact h

/-! ### The Poisson point process with an s-finite intensity -/

/-- The counting measure has law `poissonPointProcessSum ν` under the sample law. -/
lemma hasLaw_superCounting (ν : ℕ → Measure E) [∀ n, IsFiniteMeasure (ν n)] :
    HasLaw superCounting (poissonPointProcessSum ν) (superSampleLaw ν) :=
  ⟨measurable_superCounting.aemeasurable, rfl⟩

/-- **The Poisson point process with intensity `Λ`**, for every s-finite measure `Λ`: the
superposition of the finite pieces of Mathlib's canonical decomposition `sfiniteSeq Λ`,
as a probability measure on the space of measures. -/
noncomputable def poissonPointProcess (Λ : Measure E) [SFinite Λ] : Measure (Measure E) :=
  poissonPointProcessSum (sfiniteSeq Λ)

instance (Λ : Measure E) [SFinite Λ] : IsProbabilityMeasure (poissonPointProcess Λ) := by
  unfold poissonPointProcess; infer_instance

lemma hasLaw_superCounting_poissonPointProcess (Λ : Measure E) [SFinite Λ] :
    HasLaw superCounting (poissonPointProcess Λ) (superSampleLaw (sfiniteSeq Λ)) :=
  hasLaw_superCounting _

omit [Nonempty E] in
lemma measurable_negExp_lintegral {φ : E → ℝ≥0∞} (hφ : Measurable φ) :
    Measurable fun N : Measure E => negExp (∫⁻ x, φ x ∂N) :=
  measurable_negExp.comp (Measure.measurable_lintegral hφ)

/-- **The Laplace functional of the Poisson point process with intensity `Λ`**:
`𝔼 exp (-∫ φ dN) = exp (-∫ (1 - e^{-φ}) dΛ)`. -/
theorem integral_negExp_lintegral_poissonPointProcess (Λ : Measure E) [SFinite Λ]
    {φ : E → ℝ≥0∞} (hφ : Measurable φ) :
    ∫ N, negExp (∫⁻ x, φ x ∂N) ∂poissonPointProcess Λ
      = negExp (∫⁻ x, (1 - ENNReal.ofReal (negExp (φ x))) ∂Λ) := by
  rw [← (hasLaw_superCounting_poissonPointProcess Λ).integral_comp
      (measurable_negExp_lintegral hφ).aestronglyMeasurable]
  simp only [Function.comp_def]
  rw [integral_negExp_superCounting _ hφ, sum_sfiniteSeq]

/-- The Laplace functional, for any random measure with the Poisson law. -/
theorem HasLaw.integral_negExp_lintegral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure E} {Λ : Measure E} [SFinite Λ] (hN : HasLaw N (poissonPointProcess Λ) P)
    {φ : E → ℝ≥0∞} (hφ : Measurable φ) :
    ∫ ω, negExp (∫⁻ x, φ x ∂N ω) ∂P
      = negExp (∫⁻ x, (1 - ENNReal.ofReal (negExp (φ x))) ∂Λ) := by
  rw [← integral_negExp_lintegral_poissonPointProcess Λ hφ,
    ← hN.integral_comp (measurable_negExp_lintegral hφ).aestronglyMeasurable]
  rfl

/-- **Void probabilities** of the Poisson point process with intensity `Λ`. -/
theorem measureReal_poissonPointProcess_eq_zero (Λ : Measure E) [SFinite Λ] {B : Set E}
    (hB : MeasurableSet B) :
    (poissonPointProcess Λ).real {N | N B = 0} = negExp (Λ B) := by
  have h := (hasLaw_superCounting_poissonPointProcess Λ).measureReal_eq
    (p := fun N : Measure E => N B = 0)
    (measurableSet_eq_fun (Measure.measurable_coe hB) measurable_const)
  rw [← h, measureReal_superCounting_eq_zero _ hB, sum_sfiniteSeq]

theorem HasLaw.measureReal_eq_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure E} {Λ : Measure E} [SFinite Λ] (hN : HasLaw N (poissonPointProcess Λ) P)
    {B : Set E} (hB : MeasurableSet B) :
    P.real {ω | N ω B = 0} = negExp (Λ B) := by
  rw [← measureReal_poissonPointProcess_eq_zero Λ hB]
  exact hN.measureReal_eq (p := fun N : Measure E => N B = 0)
    (measurableSet_eq_fun (Measure.measurable_coe hB) measurable_const)

end ProbabilityTheory
