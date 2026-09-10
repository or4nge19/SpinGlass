/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Common.Mathlib.MeasureTheory.Integral.LintegralCounting
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Poisson point processes with finite intensity

A Poisson point process with finite intensity measure `ν` on `E` is a Poisson number of
points, `N ~ Poisson(ν E)`, at i.i.d. positions with law `ν / ν E`. We realise it on the sample
space `(ℕ → E) × ℕ` (a sequence of positions and a number of points), and record the random
counting measure `∑_{i < N} δ_{x i}` as a `Measure`-valued random variable.

The characterising property is the **Laplace functional**: for every measurable
`φ : E → ℝ≥0∞`,

`𝔼 exp (-∫ φ dN) = exp (-∫ (1 - e^{-φ}) dν)`,

where `exp (-∞) = 0`. Every other property of the process (void probabilities, the Campbell
formula, the marking and mapping theorems) is read off this formula in the files that follow.

## Main statements

- `ENNReal.negExp`: `t ↦ exp (-t)` on `ℝ≥0∞`, with `negExp ∞ = 0`.
- `ProbabilityTheory.poissonSampleLaw`, `ProbabilityTheory.countingMeasure`,
  `ProbabilityTheory.measurable_countingMeasure`.
- `ProbabilityTheory.integral_negExp_countingMeasure`: **the Laplace functional**.
- `ProbabilityTheory.lintegral_countingMeasure_eq`: **the Campbell formula**
  `𝔼 ∫ φ dN = ∫ φ dν`.
-/

open MeasureTheory Filter Set
open scoped ENNReal NNReal

namespace ENNReal

/-- `negExp t = exp (-t)` for `t < ∞`, and `negExp ∞ = 0`. -/
noncomputable def negExp (t : ℝ≥0∞) : ℝ := if t = ∞ then 0 else Real.exp (-t.toReal)

@[simp] lemma negExp_top : negExp ∞ = 0 := by simp [negExp]

lemma negExp_of_ne_top {t : ℝ≥0∞} (ht : t ≠ ∞) : negExp t = Real.exp (-t.toReal) := by
  simp [negExp, ht]

@[simp] lemma negExp_zero : negExp 0 = 1 := by simp [negExp]

lemma negExp_ofReal {x : ℝ} (hx : 0 ≤ x) : negExp (ENNReal.ofReal x) = Real.exp (-x) := by
  rw [negExp_of_ne_top ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hx]

lemma negExp_nonneg (t : ℝ≥0∞) : 0 ≤ negExp t := by
  unfold negExp; split_ifs <;> positivity

lemma negExp_le_one (t : ℝ≥0∞) : negExp t ≤ 1 := by
  unfold negExp
  split_ifs
  · exact zero_le_one
  · exact Real.exp_le_one_iff.2 (by simp)

lemma negExp_pos {t : ℝ≥0∞} (ht : t ≠ ∞) : 0 < negExp t := by
  rw [negExp_of_ne_top ht]; positivity

lemma negExp_add (a b : ℝ≥0∞) : negExp (a + b) = negExp a * negExp b := by
  rcases eq_or_ne a ∞ with ha | ha
  · simp [ha]
  rcases eq_or_ne b ∞ with hb | hb
  · simp [hb]
  rw [negExp_of_ne_top (ENNReal.add_ne_top.2 ⟨ha, hb⟩), negExp_of_ne_top ha, negExp_of_ne_top hb,
    ENNReal.toReal_add ha hb, neg_add, Real.exp_add]

lemma negExp_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    negExp (∑ i ∈ s, f i) = ∏ i ∈ s, negExp (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, negExp_add, ih]

lemma negExp_antitone : Antitone negExp := by
  intro a b hab
  rcases eq_or_ne b ∞ with hb | hb
  · rw [hb, negExp_top]; exact negExp_nonneg a
  have ha : a ≠ ∞ := ne_top_of_le_ne_top hb hab
  rw [negExp_of_ne_top ha, negExp_of_ne_top hb]
  exact Real.exp_le_exp.2 (neg_le_neg (ENNReal.toReal_mono hb hab))

lemma negExp_top_mul (c : ℝ≥0∞) : negExp (∞ * c) = if c = 0 then 1 else 0 := by
  split_ifs with hc
  · simp [hc]
  · rw [ENNReal.top_mul hc, negExp_top]

lemma measurable_negExp : Measurable negExp := by
  have h1 : Measurable fun t : ℝ≥0∞ => Real.exp (-t.toReal) :=
    Real.measurable_exp.comp (measurable_neg.comp ENNReal.measurable_toReal)
  have hset : MeasurableSet {t : ℝ≥0∞ | t = ∞} := by
    simp
  exact Measurable.ite hset measurable_const h1

lemma one_sub_ofReal_negExp_le_one (t : ℝ≥0∞) : 1 - ENNReal.ofReal (negExp t) ≤ 1 :=
  tsub_le_self

lemma ofReal_negExp_le_one (t : ℝ≥0∞) : ENNReal.ofReal (negExp t) ≤ 1 := by
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (negExp_le_one t)

end ENNReal

namespace ProbabilityTheory

open ENNReal

variable {E : Type*} [MeasurableSpace E]

/-! ### Positions and the sample law -/

/-- The law of a single position: `ν` normalised, or a Dirac mass when `ν = 0`. -/
noncomputable def positionLaw [Nonempty E] (ν : Measure E) : Measure E :=
  if ν univ = 0 then Measure.dirac (Classical.arbitrary E) else (ν univ)⁻¹ • ν

instance [Nonempty E] (ν : Measure E) [IsFiniteMeasure ν] :
    IsProbabilityMeasure (positionLaw ν) := by
  unfold positionLaw
  split_ifs with h
  · infer_instance
  · exact ⟨by rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h (measure_ne_top _ _)]⟩

/-- `ν = ν(E) · positionLaw ν`. -/
lemma smul_positionLaw [Nonempty E] (ν : Measure E) [IsFiniteMeasure ν] :
    ν univ • positionLaw ν = ν := by
  unfold positionLaw
  split_ifs with h
  · rw [h, zero_smul]
    exact (Measure.measure_univ_eq_zero.1 h).symm
  · rw [smul_smul, ENNReal.mul_inv_cancel h (measure_ne_top _ _), one_smul]

/-- The sample space of a finite Poisson point process: a sequence of positions and a number
of points. -/
abbrev PoissonSample (E : Type*) := (ℕ → E) × ℕ

/-- The law of the sample: i.i.d. positions with law `positionLaw ν`, and an independent
`Poisson (ν E)` number of points. -/
noncomputable def poissonSampleLaw [Nonempty E] (ν : Measure E) [IsFiniteMeasure ν] :
    Measure (PoissonSample E) :=
  (Measure.infinitePi fun _ : ℕ => positionLaw ν).prod (poissonMeasure (ν univ).toNNReal)

instance [Nonempty E] (ν : Measure E) [IsFiniteMeasure ν] :
    IsProbabilityMeasure (poissonSampleLaw ν) := by
  unfold poissonSampleLaw; infer_instance

/-- The counting measure of the first `p.2` positions of a sample. -/
noncomputable def countingMeasure (p : PoissonSample E) : Measure E :=
  ∑ i ∈ Finset.range p.2, Measure.dirac (p.1 i)

lemma countingMeasure_apply (p : PoissonSample E) {s : Set E} (hs : MeasurableSet s) :
    countingMeasure p s = ∑ i ∈ Finset.range p.2, s.indicator 1 (p.1 i) := by
  rw [countingMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => Measure.dirac_apply' _ hs

lemma lintegral_countingMeasure (p : PoissonSample E) {φ : E → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ x, φ x ∂countingMeasure p = ∑ i ∈ Finset.range p.2, φ (p.1 i) := by
  rw [countingMeasure, lintegral_finsetSum_measure]
  exact Finset.sum_congr rfl fun i _ => lintegral_dirac' _ hφ

/-- **For a counting measure the product of the integrals dominates the integral of the
product**: `∫ φψ dN ≤ (∫ φ dN)(∫ ψ dN)`. -/
lemma lintegral_mul_le_mul_lintegral_countingMeasure (p : PoissonSample E) {φ ψ : E → ℝ≥0∞}
    (hφ : Measurable φ) (hψ : Measurable ψ) :
    (∫⁻ x, φ x * ψ x ∂countingMeasure p)
      ≤ (∫⁻ x, φ x ∂countingMeasure p) * ∫⁻ x, ψ x ∂countingMeasure p := by
  unfold countingMeasure
  exact lintegral_mul_le_mul_lintegral_finsetSum_dirac _ _ hφ hψ

instance (p : PoissonSample E) : IsFiniteMeasure (countingMeasure p) := by
  unfold countingMeasure; infer_instance

/-- The counting measure is a measurable function of the sample. -/
lemma measurable_countingMeasure : Measurable (countingMeasure : PoissonSample E → Measure E) := by
  refine Measure.measurable_of_measurable_coe countingMeasure fun s hs => ?_
  simp only [countingMeasure_apply _ hs]
  refine measurable_from_prod_countable_left fun n => ?_
  change Measurable fun x : ℕ → E => ∑ i ∈ Finset.range n, s.indicator 1 (x i)
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_one : Measurable (1 : E → ℝ≥0∞)).indicator hs).comp (measurable_pi_apply i)

/-- The law of a finite Poisson point process with intensity `ν`, as a measure on the space of
measures. -/
noncomputable def poissonPointProcessFinite [Nonempty E] (ν : Measure E) [IsFiniteMeasure ν] :
    Measure (Measure E) :=
  (poissonSampleLaw ν).map countingMeasure

instance [Nonempty E] (ν : Measure E) [IsFiniteMeasure ν] :
    IsProbabilityMeasure (poissonPointProcessFinite ν) := by
  unfold poissonPointProcessFinite
  exact Measure.isProbabilityMeasure_map measurable_countingMeasure.aemeasurable

/-! ### The Laplace functional -/

section Laplace

variable [Nonempty E] (ν : Measure E) [IsFiniteMeasure ν]

omit [Nonempty E] in
lemma measurable_prod_negExp_sample {φ : E → ℝ≥0∞} (hφ : Measurable φ) :
    Measurable fun p : PoissonSample E => ∏ i ∈ Finset.range p.2, negExp (φ (p.1 i)) := by
  refine measurable_from_prod_countable_left fun n => ?_
  change Measurable fun x : ℕ → E => ∏ i ∈ Finset.range n, negExp (φ (x i))
  exact Finset.measurable_prod _ fun i _ =>
    (measurable_negExp.comp hφ).comp (measurable_pi_apply i)

omit [Nonempty E] in
/-- The integral of a product of functions of finitely many coordinates against an infinite
product of probability measures is the product of the integrals. -/
lemma integral_prod_range_infinitePi' {X : Type*} [MeasurableSpace X] (μ : ℕ → Measure X)
    [∀ n, IsProbabilityMeasure (μ n)] {g : ℕ → X → ℝ} (hg : ∀ n, Measurable (g n)) (K : ℕ) :
    ∫ x, ∏ i ∈ Finset.range K, g i (x i) ∂(Measure.infinitePi μ)
      = ∏ i ∈ Finset.range K, ∫ x, g i x ∂μ i := by
  have h1 : ∀ x : ℕ → X, ∏ i ∈ Finset.range K, g i (x i)
      = ∏ i : Finset.range K, g i ((Finset.range K).restrict x i) :=
    fun x => (Finset.prod_coe_sort (Finset.range K) fun i => g i (x i)).symm
  simp_rw [h1]
  have hf : AEStronglyMeasurable
      (fun y : (i : Finset.range K) → X => ∏ i : Finset.range K, g i (y i))
      (Measure.pi fun i : Finset.range K => μ i) := by
    refine Measurable.aestronglyMeasurable ?_
    exact Finset.measurable_prod (s := Finset.univ)
      (f := fun (i : Finset.range K) (y : (j : Finset.range K) → X) => g i (y i))
      fun i _ => (hg i).comp (measurable_pi_apply i)
  have key := integral_restrict_infinitePi (μ := μ) (s := Finset.range K)
    (f := fun y : (i : Finset.range K) → X => ∏ i : Finset.range K, g i (y i)) hf
  rw [key]
  have key2 := integral_fintype_prod_eq_prod (fun i : Finset.range K => g i)
    (μ := fun i : Finset.range K => μ i)
  rw [key2, ← Finset.prod_coe_sort (Finset.range K)]

omit [Nonempty E] in
/-- The integral of a product of functions of finitely many coordinates against an infinite
product of copies of a probability measure is the product of the integrals. -/
lemma integral_prod_range_infinitePi (μ : Measure E) [IsProbabilityMeasure μ]
    {g : E → ℝ} (hg : Measurable g) (n : ℕ) :
    ∫ x, ∏ i ∈ Finset.range n, g (x i) ∂(Measure.infinitePi fun _ : ℕ => μ)
      = (∫ x, g x ∂μ) ^ n := by
  rw [integral_prod_range_infinitePi' (fun _ => μ) (g := fun _ => g) (fun _ => hg) n]
  simp

/-- **The Laplace functional of a finite Poisson point process.** For measurable
`φ : E → ℝ≥0∞`, `𝔼 exp (-∫ φ dN) = exp (-∫ (1 - e^{-φ}) dν)`. -/
theorem integral_negExp_countingMeasure {φ : E → ℝ≥0∞} (hφ : Measurable φ) :
    ∫ p, negExp (∫⁻ x, φ x ∂countingMeasure p) ∂poissonSampleLaw ν
      = negExp (∫⁻ x, (1 - ENNReal.ofReal (negExp (φ x))) ∂ν) := by
  classical
  set g : E → ℝ := fun x => negExp (φ x) with hg
  have hgm : Measurable g := measurable_negExp.comp hφ
  have hg0 : ∀ x, 0 ≤ g x := fun x => negExp_nonneg _
  have hg1 : ∀ x, g x ≤ 1 := fun x => negExp_le_one _
  set q : ℝ := ∫ x, g x ∂positionLaw ν with hq
  have hq0 : 0 ≤ q := integral_nonneg hg0
  have hgi : Integrable g (positionLaw ν) :=
    Integrable.mono' (integrable_const 1) hgm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]; exact hg1 x)
  have hq1 : q ≤ 1 := by
    calc q = ∫ x, g x ∂positionLaw ν := rfl
      _ ≤ ∫ _x, (1 : ℝ) ∂positionLaw ν := integral_mono hgi (integrable_const 1) hg1
      _ = 1 := by simp
  -- the integrand is a product over the points
  have hpt : ∀ p : PoissonSample E,
      negExp (∫⁻ x, φ x ∂countingMeasure p) = ∏ i ∈ Finset.range p.2, g (p.1 i) := by
    intro p
    rw [lintegral_countingMeasure p hφ, negExp_finset_sum]
  simp_rw [hpt]
  -- Fubini on the sample space
  have hF : Measurable fun p : PoissonSample E => ∏ i ∈ Finset.range p.2, g (p.1 i) :=
    measurable_prod_negExp_sample hφ
  have hFi : Integrable (fun p : PoissonSample E => ∏ i ∈ Finset.range p.2, g (p.1 i))
      (poissonSampleLaw ν) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hF.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun i _ => hg0 _)]
    exact Finset.prod_le_one (fun i _ => hg0 _) (fun i _ => hg1 _)
  rw [poissonSampleLaw, integral_prod_symm _ hFi]
  have hinner : ∀ n : ℕ,
      ∫ x, ∏ i ∈ Finset.range n, g (x i) ∂(Measure.infinitePi fun _ : ℕ => positionLaw ν)
        = q ^ n :=
    fun n => integral_prod_range_infinitePi (positionLaw ν) hgm n
  simp only [hinner]
  rw [integral_poissonMeasure (ν univ).toNNReal (fun n => q ^ n)]
  have hexp : Real.exp (((ν univ).toNNReal : ℝ) * q)
      = ∑' n : ℕ, (((ν univ).toNNReal : ℝ) * q) ^ n / (Nat.factorial n : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hser : ∑' n : ℕ, (Real.exp (-((ν univ).toNNReal : ℝ)) * ((ν univ).toNNReal : ℝ) ^ n
        / (Nat.factorial n : ℝ)) • q ^ n
      = Real.exp (-((ν univ).toNNReal : ℝ)) * Real.exp (((ν univ).toNNReal : ℝ) * q) := by
    rw [hexp, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [smul_eq_mul, mul_pow]; ring
  rw [hser]
  -- the right-hand side
  have hν : ν = ν univ • positionLaw ν := (smul_positionLaw ν).symm
  have hlin : ∫⁻ x, (1 - ENNReal.ofReal (g x)) ∂positionLaw ν = ENNReal.ofReal (1 - q) := by
    have hfin : ∫⁻ x, ENNReal.ofReal (g x) ∂positionLaw ν ≠ ∞ := by
      refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
      calc ∫⁻ x, ENNReal.ofReal (g x) ∂positionLaw ν
          ≤ ∫⁻ _x, (1 : ℝ≥0∞) ∂positionLaw ν :=
            lintegral_mono fun x => ofReal_negExp_le_one (φ x)
        _ = 1 := by simp
    rw [lintegral_sub hgm.ennreal_ofReal hfin
      (Filter.Eventually.of_forall fun x => ofReal_negExp_le_one (φ x)), lintegral_one,
      measure_univ, ← ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hg0),
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hq0]
  conv_rhs => rw [hν]
  rw [lintegral_smul_measure, hlin, smul_eq_mul]
  have hfin : ν univ * ENNReal.ofReal (1 - q) ≠ ∞ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  rw [negExp_of_ne_top hfin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)]
  have hΛ' : (ν univ).toReal = ((ν univ).toNNReal : ℝ) := rfl
  rw [hΛ', ← Real.exp_add]
  congr 1
  ring

end Laplace

end ProbabilityTheory
