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

/-! ### Joint measurability of sums over the points of a sample -/

section CountingProd

variable {α : Type*} [MeasurableSpace α]

omit [Nonempty E] in
/-- `(a, ω) ↦ ∫ f (a, x) dN_ω(x)` is jointly measurable for the counting measure of a sample. -/
lemma measurable_lintegral_superCounting_prod {f : α × E → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun q : α × SuperSample E => ∫⁻ x, f (q.1, x) ∂superCounting q.2 := by
  classical
  have hpt : ∀ q : α × SuperSample E, ∫⁻ x, f (q.1, x) ∂superCounting q.2
      = ∑' n, ∑' i, if i < (q.2 n).2 then f (q.1, (q.2 n).1 i) else 0 := by
    intro q
    rw [lintegral_superCounting]
    refine tsum_congr fun n => ?_
    have hfx : Measurable fun x : E => f (q.1, x) :=
      hf.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_countingMeasure _ hfx,
      tsum_eq_sum (f := fun i => if i < (q.2 n).2 then f (q.1, (q.2 n).1 i) else 0)
        (s := Finset.range (q.2 n).2) (fun i hi => by rw [Finset.mem_range] at hi; simp [hi])]
    exact Finset.sum_congr rfl fun i hi => by rw [Finset.mem_range] at hi; simp [hi]
  simp_rw [hpt]
  refine Measurable.tsum fun n => Measurable.tsum fun i => ?_
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_lt measurable_const
      (measurable_snd.comp ((measurable_pi_apply n).comp measurable_snd))
  · exact hf.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp
      (measurable_fst.comp ((measurable_pi_apply n).comp measurable_snd))))

end CountingProd

/-! ### The sum over ordered pairs of *distinct* points -/

section OffDiag

/-- **The sum of `F` over ordered pairs of distinct points** of a superposition sample.

The points of `superCounting ω` are indexed by the pairs `(n, i)` with `i < (ω n).2` — the `i`-th
position of the `n`-th piece — and this is Talagrand's `∑_{α ≠ γ} F(x_α, x_γ)`, the pairs being
distinguished by their *index*.  Nothing is therefore presumed about the process being simple;
when it is, the points carrying distinct indices are themselves distinct and the two readings of
`α ≠ γ` agree. -/
noncomputable def superOffDiagSum (ω : SuperSample E) (F : E → E → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' n, ∑ i ∈ Finset.range (ω n).2, ∑' n', ∑ i' ∈ Finset.range (ω n').2,
    if (n, i) = (n', i') then 0 else F ((ω n).1 i) ((ω n').1 i')

omit [MeasurableSpace E] [Nonempty E] in
/-- The sum over pairs of distinct points only depends on the values of `F`. -/
lemma superOffDiagSum_congr (ω : SuperSample E) {F G : E → E → ℝ≥0∞} (h : ∀ x y, F x y = G x y) :
    superOffDiagSum ω F = superOffDiagSum ω G := by
  simp only [superOffDiagSum, h]

omit [MeasurableSpace E] [Nonempty E] in
/-- A constant factor comes out of the sum over pairs of distinct points. -/
lemma superOffDiagSum_mul_const (ω : SuperSample E) (F : E → E → ℝ≥0∞) (c : ℝ≥0∞) :
    superOffDiagSum ω (fun x y => F x y * c) = superOffDiagSum ω F * c := by
  classical
  simp only [superOffDiagSum]
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun n => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun n' => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i' _ => ?_
  split_ifs <;> simp

omit [MeasurableSpace E] [Nonempty E] in
/-- A sum over the points of a superposition, flattened to a sum over the index pairs `ℕ × ℕ`. -/
lemma tsum_sum_range_eq_tsum_prod (ω : SuperSample E) (g : ℕ → ℕ → ℝ≥0∞) :
    ∑' n, ∑ i ∈ Finset.range (ω n).2, g n i
      = ∑' p : ℕ × ℕ, if p.2 < (ω p.1).2 then g p.1 p.2 else 0 := by
  classical
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun n => ?_
  rw [tsum_eq_sum (s := Finset.range (ω n).2)
    (f := fun i => if i < (ω n).2 then g n i else 0)
    (fun i hi => by rw [Finset.mem_range] at hi; simp [hi])]
  exact Finset.sum_congr rfl fun i hi => by rw [Finset.mem_range] at hi; simp [hi]

omit [MeasurableSpace E] [Nonempty E] in
/-- **Deleting one index** from a sum over the points of a superposition: omitting the index
`(n, i)` and then adding back its term recovers the full sum. -/
lemma tsum_sum_range_ite_add (ω : SuperSample E) (g : ℕ → ℕ → ℝ≥0∞) {n i : ℕ}
    (hi : i < (ω n).2) :
    (∑' n', ∑ i' ∈ Finset.range (ω n').2, if (n, i) = (n', i') then 0 else g n' i') + g n i
      = ∑' n', ∑ i' ∈ Finset.range (ω n').2, g n' i' := by
  classical
  rw [tsum_sum_range_eq_tsum_prod, tsum_sum_range_eq_tsum_prod,
    ENNReal.tsum_eq_add_tsum_ite (f := fun p : ℕ × ℕ => if p.2 < (ω p.1).2 then g p.1 p.2 else 0)
      (n, i)]
  have hpos : (if i < (ω n).2 then g n i else 0) = g n i := by simp [hi]
  rw [hpos, add_comm]
  congr 1
  refine tsum_congr fun p => ?_
  by_cases hp : p = (n, i)
  · subst hp; simp
  · have hne : ¬ ((n, i) = (p.1, p.2)) := fun h => hp h.symm
    simp [hp, hne]

omit [Nonempty E] in
/-- **The diagonal decomposition of a second-order sum over a point process**: for the counting
measure of a superposition sample,

`∫∫ F(x, y) dN dN = ∑_{α ≠ γ} F(x_α, x_γ) + ∑_α F(x_α, x_α)`.

This is pure index bookkeeping — no simplicity of the process is used — and it is what turns the
two-insertion term of the bivariate Mecke equation into a statement about pairs of *distinct*
points. -/
theorem superOffDiagSum_add_lintegral_diag (ω : SuperSample E) {F : E → E → ℝ≥0∞}
    (hF : Measurable fun q : E × E => F q.1 q.2) :
    superOffDiagSum ω F + ∫⁻ x, F x x ∂superCounting ω
      = ∫⁻ x, ∫⁻ y, F x y ∂superCounting ω ∂superCounting ω := by
  classical
  have hpt : ∀ φ : E → ℝ≥0∞, Measurable φ →
      ∫⁻ x, φ x ∂superCounting ω = ∑' n, ∑ i ∈ Finset.range (ω n).2, φ ((ω n).1 i) := by
    intro φ hφ
    rw [lintegral_superCounting]
    exact tsum_congr fun n => lintegral_countingMeasure _ hφ
  have hdiag : Measurable fun x : E => F x x := hF.comp (measurable_id.prodMk measurable_id)
  have houter : Measurable fun x : E => ∫⁻ y, F x y ∂superCounting ω := by
    have h := measurable_lintegral_superCounting_prod (α := E)
      (f := fun q : E × E => F q.1 q.2) hF
    have hmap : Measurable fun x : E => (x, ω) := measurable_id.prodMk measurable_const
    have h2 := h.comp hmap
    simp only [Function.comp_def] at h2
    exact h2
  have hin : ∀ x : E, ∫⁻ y, F x y ∂superCounting ω
      = ∑' n', ∑ i' ∈ Finset.range (ω n').2, F x ((ω n').1 i') := fun x =>
    hpt _ (hF.comp (measurable_const.prodMk measurable_id))
  rw [hpt _ hdiag, hpt _ houter]
  simp_rw [hin]
  rw [superOffDiagSum, ← ENNReal.tsum_add]
  refine tsum_congr fun n => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i hi =>
    tsum_sum_range_ite_add ω (fun n' i' => F ((ω n).1 i) ((ω n').1 i')) (Finset.mem_range.1 hi)

omit [Nonempty E] in
/-- `ω ↦ ∑_{α ≠ γ} F(x_α, x_γ)` is measurable. -/
lemma measurable_superOffDiagSum {F : E → E → ℝ≥0∞}
    (hF : Measurable fun q : E × E => F q.1 q.2) :
    Measurable fun ω : SuperSample E => superOffDiagSum ω F := by
  classical
  have hcount : ∀ k : ℕ, Measurable fun ω : SuperSample E => (ω k).2 :=
    fun k => measurable_snd.comp (measurable_pi_apply k)
  have hpos : ∀ k j : ℕ, Measurable fun ω : SuperSample E => (ω k).1 j :=
    fun k j => (measurable_pi_apply j).comp (measurable_fst.comp (measurable_pi_apply k))
  have hpt : ∀ ω : SuperSample E, superOffDiagSum ω F
      = ∑' n, ∑' i, ∑' n', ∑' i',
          if i < (ω n).2 ∧ i' < (ω n').2 ∧ ¬ ((n, i) = (n', i')) then
            F ((ω n).1 i) ((ω n').1 i') else 0 := by
    intro ω
    rw [superOffDiagSum]
    refine tsum_congr fun n => ?_
    rw [tsum_eq_sum (s := Finset.range (ω n).2) (fun i hi => by
      rw [Finset.mem_range] at hi; simp [hi])]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    refine tsum_congr fun n' => ?_
    rw [tsum_eq_sum (s := Finset.range (ω n').2) (fun i' hi' => by
      rw [Finset.mem_range] at hi'; simp [hi'])]
    exact Finset.sum_congr rfl fun i' hi' => by
      rw [Finset.mem_range] at hi'
      by_cases h : (n, i) = (n', i') <;> simp [hi, hi', h]
  simp_rw [hpt]
  refine Measurable.tsum fun n => Measurable.tsum fun i => Measurable.tsum fun n' =>
    Measurable.tsum fun i' => ?_
  have hconst : MeasurableSet {_ω : SuperSample E | ¬ ((n, i) = (n', i'))} := by
    by_cases h : ((n, i) : ℕ × ℕ) = (n', i') <;> simp [h]
  refine Measurable.ite ((measurableSet_lt measurable_const (hcount n)).inter
    ((measurableSet_lt measurable_const (hcount n')).inter hconst)) ?_ measurable_const
  exact hF.comp ((hpos n i).prodMk (hpos n' i'))

/-! ### Deleting one point of a superposition -/

/-- **The counting measure of the points of a superposition other than the `(n, i)`-th** — the
reduced configuration seen from that point. -/
noncomputable def superCountingErase (ω : SuperSample E) (n i : ℕ) : Measure E :=
  Measure.sum fun m => if m = n then countingMeasureErase (ω m) i else countingMeasure (ω m)

omit [Nonempty E] in
/-- Integrating against the reduced configuration is summing over all the indices but one. -/
lemma lintegral_superCountingErase (ω : SuperSample E) (n i : ℕ) {φ : E → ℝ≥0∞}
    (hφ : Measurable φ) :
    ∫⁻ x, φ x ∂superCountingErase ω n i
      = ∑' m, ∑ j ∈ Finset.range (ω m).2, if (n, i) = (m, j) then 0 else φ ((ω m).1 j) := by
  classical
  rw [superCountingErase, lintegral_sum_measure]
  refine tsum_congr fun m => ?_
  split_ifs with hm
  · rw [lintegral_countingMeasureErase _ _ hφ]
    have hz : (if ((n, i) : ℕ × ℕ) = (m, i) then (0 : ℝ≥0∞) else φ ((ω m).1 i)) = 0 := by
      simp [hm]
    rw [← Finset.sum_erase (f := fun j => if ((n, i) : ℕ × ℕ) = (m, j) then (0 : ℝ≥0∞)
        else φ ((ω m).1 j)) (a := i) (Finset.range (ω m).2) hz]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hji : ¬ (((n, i) : ℕ × ℕ) = (m, j)) := fun h =>
      (Finset.mem_erase.1 hj).1 (congrArg Prod.snd h).symm
    simp [hji]
  · rw [lintegral_countingMeasure _ hφ]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hji : ¬ (((n, i) : ℕ × ℕ) = (m, j)) := fun h => hm (congrArg Prod.fst h).symm
    simp [hji]

omit [Nonempty E] in
/-- **Putting the deleted point back**: for an index of an actual point, the reduced configuration
together with a Dirac mass at that point is the whole configuration. -/
lemma superCountingErase_add_dirac (ω : SuperSample E) {n i : ℕ} (hi : i < (ω n).2) :
    superCountingErase ω n i + Measure.dirac ((ω n).1 i) = superCounting ω := by
  classical
  ext s hs
  simp only [superCountingErase, superCounting, Measure.add_apply, Measure.sum_apply _ hs]
  rw [ENNReal.tsum_eq_add_tsum_ite (f := fun m =>
      (if m = n then countingMeasureErase (ω m) i else countingMeasure (ω m)) s) n,
    ENNReal.tsum_eq_add_tsum_ite (f := fun m => countingMeasure (ω m) s) n]
  rw [add_right_comm]
  congr 1
  · have hput := congrArg (fun μ : Measure E => μ s) (countingMeasureErase_add_dirac (ω n) hi)
    simpa using hput
  · refine tsum_congr fun m => ?_
    by_cases h : m = n <;> simp [h]

omit [Nonempty E] in
/-- The reduced counting measure is a measurable function of the sample. -/
lemma measurable_superCountingErase (n i : ℕ) :
    Measurable fun ω : SuperSample E => superCountingErase ω n i := by
  classical
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [superCountingErase, Measure.sum_apply _ hs]
  refine Measurable.tsum fun m => ?_
  split_ifs with hm
  · exact (Measure.measurable_coe hs).comp
      ((measurable_countingMeasureErase i).comp (measurable_pi_apply m))
  · exact (Measure.measurable_coe hs).comp
      (measurable_countingMeasure.comp (measurable_pi_apply m))

/-- **The superposition sample obtained by deleting the `(n, i)`-th point.** -/
def superSampleErase (ω : SuperSample E) (n i : ℕ) : SuperSample E :=
  Function.update ω n (sampleErase (ω n) i)

omit [Nonempty E] in
/-- **The reduced configuration of a superposition is again a configuration.** -/
lemma superCounting_superSampleErase (ω : SuperSample E) {n i : ℕ} (hi : i < (ω n).2) :
    superCounting (superSampleErase ω n i) = superCountingErase ω n i := by
  classical
  simp only [superCounting, superCountingErase, superSampleErase]
  congr 1
  funext m
  rcases eq_or_ne m n with rfl | h
  · simp [countingMeasure_sampleErase _ hi]
  · simp [h]

omit [Nonempty E] in
/-- Deleting a point is a measurable operation on superposition samples. -/
lemma measurable_superSampleErase (n i : ℕ) :
    Measurable fun ω : SuperSample E => superSampleErase ω n i := by
  classical
  refine measurable_pi_lambda _ fun m => ?_
  rcases eq_or_ne m n with rfl | h
  · simp only [superSampleErase, Function.update_self]
    exact (measurable_sampleErase i).comp (measurable_pi_apply m)
  · simp only [superSampleErase, Function.update_of_ne h]
    exact measurable_pi_apply m

omit [Nonempty E] in
/-- **The sum over ordered pairs of distinct points, in reduced form**: the inner sum is the
integral against the configuration seen from the outer point. -/
lemma superOffDiagSum_eq_tsum_sum_lintegral (ω : SuperSample E) {F : E → E → ℝ≥0∞}
    (hF : ∀ x, Measurable (F x)) :
    superOffDiagSum ω F
      = ∑' n, ∑ i ∈ Finset.range (ω n).2,
          ∫⁻ y, F ((ω n).1 i) y ∂superCountingErase ω n i :=
  tsum_congr fun n => Finset.sum_congr rfl fun i _ =>
    (lintegral_superCountingErase ω n i (hF _)).symm

/-! ### The second factorial measure -/

/-- **The second factorial measure** of a superposition sample, `N^{(2)} = ∑_{α ≠ γ} δ_{(x_α, x_γ)}`
on `E × E`: the configuration of ordered pairs of *distinct* points. Integrating against it is the
sum `superOffDiagSum` (`lintegral_superFactorialTwo`). -/
noncomputable def superFactorialTwo (ω : SuperSample E) : Measure (E × E) :=
  Measure.sum fun n => ∑ i ∈ Finset.range (ω n).2, Measure.sum fun n' =>
    ∑ i' ∈ Finset.range (ω n').2,
      if (n, i) = (n', i') then 0 else Measure.dirac ((ω n).1 i, (ω n').1 i')

omit [Nonempty E] in
lemma lintegral_superFactorialTwo (ω : SuperSample E) {G : E × E → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ r, G r ∂superFactorialTwo ω = superOffDiagSum ω fun x y => G (x, y) := by
  classical
  rw [superFactorialTwo, superOffDiagSum, lintegral_sum_measure]
  refine tsum_congr fun n => ?_
  rw [lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lintegral_sum_measure]
  refine tsum_congr fun n' => ?_
  rw [lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun i' _ => ?_
  split_ifs
  · simp
  · exact lintegral_dirac' _ hG

end OffDiag

omit [Nonempty E] in
/-- **For the counting measure of a superposition the product of the integrals dominates the
integral of the product**: `∫ φψ dN ≤ (∫ φ dN)(∫ ψ dN)`. -/
lemma lintegral_mul_le_mul_lintegral_superCounting (ω : SuperSample E) {φ ψ : E → ℝ≥0∞}
    (hφ : Measurable φ) (hψ : Measurable ψ) :
    (∫⁻ x, φ x * ψ x ∂superCounting ω)
      ≤ (∫⁻ x, φ x ∂superCounting ω) * ∫⁻ x, ψ x ∂superCounting ω := by
  unfold superCounting
  exact lintegral_mul_le_mul_lintegral_sum _ fun n =>
    lintegral_mul_le_mul_lintegral_countingMeasure (ω n) hφ hψ

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

omit [Nonempty E] in
lemma measurable_negExp_lintegral {φ : E → ℝ≥0∞} (hφ : Measurable φ) :
    Measurable fun N : Measure E => negExp (∫⁻ x, φ x ∂N) :=
  measurable_negExp.comp (Measure.measurable_lintegral hφ)

/-- **The Laplace functional of the superposition**, at the level of its law: for any
decomposition `ν` into finite pieces, `𝔼 exp (-∫ φ dN) = exp (-∫ (1 - e^{-φ}) d(∑ₙ νₙ))`. -/
theorem integral_negExp_lintegral_poissonPointProcessSum (ν : ℕ → Measure E)
    [∀ n, IsFiniteMeasure (ν n)] {φ : E → ℝ≥0∞} (hφ : Measurable φ) :
    ∫ N, negExp (∫⁻ x, φ x ∂N) ∂poissonPointProcessSum ν
      = negExp (∫⁻ x, (1 - ENNReal.ofReal (negExp (φ x))) ∂Measure.sum ν) := by
  rw [← (hasLaw_superCounting ν).integral_comp
      (measurable_negExp_lintegral hφ).aestronglyMeasurable]
  simp only [Function.comp_def]
  exact integral_negExp_superCounting _ hφ

/-- The Laplace functional, for any random measure with the law of a superposition. -/
theorem HasLaw.integral_negExp_lintegral_sum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure E} {ν : ℕ → Measure E} [∀ n, IsFiniteMeasure (ν n)]
    (hN : HasLaw N (poissonPointProcessSum ν) P) {φ : E → ℝ≥0∞} (hφ : Measurable φ) :
    ∫ ω, negExp (∫⁻ x, φ x ∂N ω) ∂P
      = negExp (∫⁻ x, (1 - ENNReal.ofReal (negExp (φ x))) ∂Measure.sum ν) := by
  rw [← integral_negExp_lintegral_poissonPointProcessSum ν hφ,
    ← hN.integral_comp (measurable_negExp_lintegral hφ).aestronglyMeasurable]
  rfl

/-- **Void probabilities** of the superposition, at the level of its law. -/
theorem measureReal_poissonPointProcessSum_eq_zero (ν : ℕ → Measure E)
    [∀ n, IsFiniteMeasure (ν n)] {B : Set E} (hB : MeasurableSet B) :
    (poissonPointProcessSum ν).real {N | N B = 0} = negExp (Measure.sum ν B) := by
  have h := (hasLaw_superCounting ν).measureReal_eq (p := fun N : Measure E => N B = 0)
    (measurableSet_eq_fun (Measure.measurable_coe hB) measurable_const)
  rw [← h, measureReal_superCounting_eq_zero _ hB]

theorem HasLaw.measureReal_eq_zero_sum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure E} {ν : ℕ → Measure E} [∀ n, IsFiniteMeasure (ν n)]
    (hN : HasLaw N (poissonPointProcessSum ν) P) {B : Set E} (hB : MeasurableSet B) :
    P.real {ω | N ω B = 0} = negExp (Measure.sum ν B) := by
  rw [← measureReal_poissonPointProcessSum_eq_zero ν hB]
  exact hN.measureReal_eq (p := fun N : Measure E => N B = 0)
    (measurableSet_eq_fun (Measure.measurable_coe hB) measurable_const)

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
