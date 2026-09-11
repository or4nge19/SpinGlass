/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.PointProcess.PoissonSuperposition

/-!
# The Mecke formula for Poisson point processes

For a Poisson point process `N` with s-finite intensity `Λ` and every measurable
`f : E × Measure E → ℝ≥0∞`,

`𝔼 ∑_{x ∈ N} f (x, N) = ∫ 𝔼 f (x, N + δ_x) dΛ(x)`

(the **Mecke equation**, Last–Penrose *Lectures on the Poisson process*, Theorem 4.1). It is the
fundamental tool for computing expectations of sums over the points of a Poisson process; the
**Campbell formula** `𝔼 ∫ g dN = ∫ g dΛ` is the special case `f (x, N) = g x`.

The proof is by the structure of the sample space: for a finite intensity, the points are a
Poisson number `n` of i.i.d. positions, each of the `n` terms of the sum has the same law as the
last one by exchangeability of the product measure, and resampling the last position gives the
right-hand side, with `n · P(n) = Λ(E) · P(n - 1)` for the Poisson weights. An s-finite intensity
is a superposition of independent finite pieces, and resampling one piece reduces to the finite
case.

## Main statements

- `MeasureTheory.Measure.infinitePi_prod_map_update`, `MeasureTheory.lintegral_infinitePi_update`:
  resampling one coordinate of an infinite product measure leaves it invariant.
- `MeasureTheory.lintegral_infinitePi_comp_equiv`: an i.i.d. product is exchangeable.
- `ProbabilityTheory.lintegral_sum_countingMeasureErase`,
  `ProbabilityTheory.lintegral_tsum_sum_superCountingErase`: **the reduced Mecke equation** (the
  Palm formula) `𝔼 ∑_{x ∈ N} g (x, N ∖ x) = ∫ 𝔼 g (x, N) dΛ(x)`, in which the integrand sees the
  configuration of the *other* points. This is the fundamental form: the ordinary equation is its
  case `g (x, M) = f (x, M + δ_x)`, and iterating it gives the multivariate equations.
- `ProbabilityTheory.lintegral_lintegral_countingMeasure`: Mecke for a finite intensity.
- `ProbabilityTheory.lintegral_lintegral_superCounting`: Mecke for the superposition.
- `ProbabilityTheory.lintegral_superOffDiagSum_superCounting`: **the off-diagonal bivariate Mecke
  equation** `𝔼 ∑_{x ≠ y ∈ N} f (x, y, N) = ∫∫ 𝔼 f (x, y, N + δ_x + δ_y) dΛ dΛ`, the sum being over
  pairs of *distinct* points, with no finiteness hypothesis.
- `ProbabilityTheory.lintegral_lintegral_lintegral_superCounting`: the full bivariate equation,
  diagonal included.
- `ProbabilityTheory.lintegral_lintegral_poissonPointProcess`,
  `ProbabilityTheory.HasLaw.lintegral_lintegral`: **the Mecke formula** for the law.
- `ProbabilityTheory.lintegral_lintegral_poissonPointProcess_of_fst`: **Campbell's formula**.
-/

open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology

noncomputable section

/-! ### Resampling and exchangeability of infinite products -/

namespace MeasureTheory

section Resample

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- Resampling the coordinate `n` of an infinite product measure leaves it invariant. -/
theorem Measure.infinitePi_prod_map_update (n : ι) :
    ((Measure.infinitePi μ).prod (μ n)).map
        (fun p : (∀ i, X i) × X n => Function.update p.1 n p.2)
      = Measure.infinitePi μ := by
  refine Measure.eq_infinitePi μ fun s t ht => ?_
  rw [Measure.map_apply measurable_update'
    (MeasurableSet.pi (Finset.countable_toSet s) fun i _ => ht i)]
  have hpre : (fun p : (∀ i, X i) × X n => Function.update p.1 n p.2) ⁻¹' Set.pi (↑s) t
      = Set.pi (↑(s.erase n)) t ×ˢ (if n ∈ s then t n else univ) := by
    ext ⟨x, y⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_erase]
    constructor
    · intro h
      refine ⟨fun i hi => ?_, ?_⟩
      · have := h i hi.2
        rwa [Function.update_of_ne hi.1] at this
      · split_ifs with hn
        · have := h n hn
          rwa [Function.update_self] at this
        · exact Set.mem_univ _
    · rintro ⟨h1, h2⟩ i hi
      by_cases hin : i = n
      · subst hin
        rw [Function.update_self]
        simpa [hi] using h2
      · rw [Function.update_of_ne hin]
        exact h1 i ⟨hin, hi⟩
  rw [hpre, Measure.prod_prod, Measure.infinitePi_pi _ (fun i _ => ht i)]
  split_ifs with hn
  · rw [← Finset.mul_prod_erase s _ hn, mul_comm]
  · rw [Finset.erase_eq_of_notMem hn, measure_univ, mul_one]

/-- Integrating against an infinite product, one may resample any single coordinate. -/
theorem lintegral_infinitePi_update (n : ι) {f : (∀ i, X i) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂Measure.infinitePi μ
      = ∫⁻ x, ∫⁻ y, f (Function.update x n y) ∂μ n ∂Measure.infinitePi μ := by
  conv_lhs => rw [← Measure.infinitePi_prod_map_update μ n]
  rw [lintegral_map hf measurable_update',
    lintegral_prod (fun p : (∀ i, X i) × X n => f (Function.update p.1 n p.2))
      (hf.comp measurable_update').aemeasurable]

end Resample

section Exchangeable

variable {ι X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- An i.i.d. product is exchangeable: permuting the coordinates leaves the integral invariant. -/
theorem lintegral_infinitePi_comp_equiv (e : ι ≃ ι) {f : (ι → X) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f (fun i => x (e i)) ∂Measure.infinitePi (fun _ : ι => μ)
      = ∫⁻ x, f x ∂Measure.infinitePi (fun _ : ι => μ) := by
  have hmap := Measure.infinitePi_map_piCongrLeft (μ := fun _ : ι => μ) e.symm
  have hcoe : ∀ x : ι → X, (MeasurableEquiv.piCongrLeft (fun _ : ι => X) e.symm) x
      = fun i => x (e i) := by
    intro x
    funext i
    rw [MeasurableEquiv.coe_piCongrLeft]
    conv_lhs => rw [← e.symm_apply_apply i]
    exact Equiv.piCongrLeft_apply_apply (fun _ : ι => X) e.symm x (e i)
  conv_rhs => rw [← hmap]
  rw [lintegral_map hf (MeasurableEquiv.piCongrLeft (fun _ : ι => X) e.symm).measurable]
  exact lintegral_congr fun x => by rw [hcoe]

end Exchangeable

end MeasureTheory

namespace ProbabilityTheory

open ENNReal

variable {E : Type*} [MeasurableSpace E]

/-! ### Measurability of sums over the points of a finite sample -/

/-- `(a, p) ↦ ∫ f (a, x) dN_p(x)` is jointly measurable for the counting measure of a finite
sample. -/
lemma measurable_lintegral_countingMeasure_prod {α : Type*} [MeasurableSpace α]
    {f : α × E → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun q : α × PoissonSample E => ∫⁻ x, f (q.1, x) ∂countingMeasure q.2 := by
  classical
  have hpt : ∀ q : α × PoissonSample E, ∫⁻ x, f (q.1, x) ∂countingMeasure q.2
      = ∑' i, if i < q.2.2 then f (q.1, q.2.1 i) else 0 := by
    intro q
    have hfx : Measurable fun x : E => f (q.1, x) :=
      hf.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_countingMeasure _ hfx,
      tsum_eq_sum (f := fun i => if i < q.2.2 then f (q.1, q.2.1 i) else 0)
        (s := Finset.range q.2.2) (fun i hi => by rw [Finset.mem_range] at hi; simp [hi])]
    exact Finset.sum_congr rfl fun i hi => by rw [Finset.mem_range] at hi; simp [hi]
  simp_rw [hpt]
  refine Measurable.tsum fun i => ?_
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_lt measurable_const (measurable_snd.comp measurable_snd)
  · exact hf.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp
      (measurable_fst.comp measurable_snd)))

/-! ### The Mecke formula for a finite intensity -/

section Finite

variable [Nonempty E] (ν : Measure E) [IsFiniteMeasure ν]

/-- The Poisson weight `e^{-r} r^n / n!`. -/
def poissonWeight (r : ℝ≥0) (n : ℕ) : ℝ := Real.exp (-r) * r ^ n / n.factorial

lemma poissonWeight_nonneg (r : ℝ≥0) (n : ℕ) : 0 ≤ poissonWeight r n := by
  dsimp only [poissonWeight]; positivity

/-- Integration against the sample law: a Poisson mixture of the i.i.d. position laws. -/
lemma lintegral_poissonSampleLaw {K : PoissonSample E → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ p, K p ∂poissonSampleLaw ν
      = ∑' n, ENNReal.ofReal (poissonWeight (ν univ).toNNReal n)
          * ∫⁻ x, K (x, n) ∂(Measure.infinitePi fun _ : ℕ => positionLaw ν) := by
  rw [poissonSampleLaw, lintegral_prod_symm _ hK.aemeasurable, poissonMeasure,
    lintegral_sum_measure]
  refine tsum_congr fun n => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  rfl

omit [Nonempty E] [IsFiniteMeasure ν] in
/-- `(n + 1) · P(n + 1) = Λ(E) · P(n)` for the Poisson weights. -/
lemma poissonWeight_succ_mul (r : ℝ≥0) (n : ℕ) :
    poissonWeight r (n + 1) * ((n : ℝ) + 1) = r * poissonWeight r n := by
  simp only [poissonWeight, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    pow_succ]
  have h1 : (n.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp

omit [Nonempty E] [IsFiniteMeasure ν] in
/-- The points of a finite sample of size `k + 1`: the first `k` points and the last one. -/
lemma countingMeasure_succ (x : ℕ → E) (k : ℕ) :
    countingMeasure (x, k + 1) = countingMeasure (x, k) + Measure.dirac (x k) := by
  simp only [countingMeasure, Finset.sum_range_succ]

/-! ### The reduced Mecke equation for a finite intensity -/

omit [Nonempty E] in
/-- The reduced summand `g (x_i, N ∖ x_i)` is a measurable function of the positions, since the
reduced configuration is again a configuration (`countingMeasure_sampleErase`). -/
lemma measurable_countingMeasureErase_summand {g : E × Measure E → ℝ≥0∞}
    (hg : Measurable fun q : PoissonSample E × E => g (q.2, countingMeasure q.1)) {n i : ℕ}
    (hi : i < n) :
    Measurable fun x : ℕ → E => g (x i, countingMeasureErase (x, n) i) := by
  have hrw : (fun x : ℕ → E => g (x i, countingMeasureErase (x, n) i))
      = fun x => g (x i, countingMeasure (sampleErase (x, n) i)) := by
    funext x
    rw [countingMeasure_sampleErase _ hi]
  rw [hrw]
  have hmap : Measurable fun x : ℕ → E => (sampleErase ((x, n) : PoissonSample E) i, x i) :=
    ((measurable_sampleErase i).comp (measurable_id.prodMk measurable_const)).prodMk
      (measurable_pi_apply i)
  have h2 := hg.comp hmap
  simp only [Function.comp_def] at h2
  exact h2

omit [Nonempty E] in
/-- The reduced sum over the points of a sample is a measurable function of the sample. -/
lemma measurable_sum_countingMeasureErase {g : E × Measure E → ℝ≥0∞}
    (hg : Measurable fun q : PoissonSample E × E => g (q.2, countingMeasure q.1)) :
    Measurable fun p : PoissonSample E =>
      ∑ i ∈ Finset.range p.2, g (p.1 i, countingMeasureErase p i) := by
  classical
  have hpt : ∀ p : PoissonSample E,
      ∑ i ∈ Finset.range p.2, g (p.1 i, countingMeasureErase p i)
        = ∑' i, if i < p.2 then g (p.1 i, countingMeasureErase p i) else 0 := by
    intro p
    rw [tsum_eq_sum (s := Finset.range p.2) (fun i hi => by
      rw [Finset.mem_range] at hi; simp [hi])]
    exact Finset.sum_congr rfl fun i hi => by rw [Finset.mem_range] at hi; simp [hi]
  simp_rw [hpt]
  refine Measurable.tsum fun i => ?_
  refine measurable_from_prod_countable_left fun k => ?_
  by_cases hik : i < k
  · have h1 : (fun x : ℕ → E => if i < ((x, k) : PoissonSample E).2
        then g (((x, k) : PoissonSample E).1 i, countingMeasureErase (x, k) i) else 0)
        = fun x => g (x i, countingMeasureErase (x, k) i) := by
      funext x; simp [hik]
    rw [h1]
    exact measurable_countingMeasureErase_summand hg hik
  · have h1 : (fun x : ℕ → E => if i < ((x, k) : PoissonSample E).2
        then g (((x, k) : PoissonSample E).1 i, countingMeasureErase (x, k) i) else 0)
        = fun _ => 0 := by
      funext x; simp [hik]
    rw [h1]
    exact measurable_const

/-- Every point of a sample of size `k + 1` contributes as much to the *reduced* sum as the last
one, by exchangeability; and seen from the last point, the reduced configuration is the sample of
size `k`. -/
lemma lintegral_countingMeasureErase_point_eq_last {g : E × Measure E → ℝ≥0∞}
    (hg : Measurable fun q : PoissonSample E × E => g (q.2, countingMeasure q.1))
    {k i : ℕ} (hi : i < k + 1) :
    ∫⁻ x, g (x i, countingMeasureErase (x, k + 1) i)
        ∂(Measure.infinitePi fun _ : ℕ => positionLaw ν)
      = ∫⁻ x, g (x k, countingMeasure (x, k))
          ∂(Measure.infinitePi fun _ : ℕ => positionLaw ν) := by
  classical
  have hF : Measurable fun x : ℕ → E => g (x i, countingMeasureErase (x, k + 1) i) :=
    measurable_countingMeasureErase_summand hg hi
  rw [← lintegral_infinitePi_comp_equiv (positionLaw ν) (Equiv.swap i k) hF]
  refine lintegral_congr fun x => ?_
  have hN : countingMeasureErase (fun j => x ((Equiv.swap i k) j), k + 1) i
      = countingMeasure (x, k) := by
    simp only [countingMeasureErase, countingMeasure]
    refine Finset.sum_equiv (Equiv.swap i k) (fun j => ?_) fun j _ => ?_
    · simp only [Finset.mem_erase, Finset.mem_range, Equiv.swap_apply_def]
      split_ifs <;> omega
    · rfl
  simp only [Equiv.swap_apply_left, hN]

/-- Resampling the last position, seen from the last point: the reduced configuration does not
depend on it. -/
lemma lintegral_countingMeasure_last_reduced {g : E × Measure E → ℝ≥0∞}
    (hg : Measurable fun q : PoissonSample E × E => g (q.2, countingMeasure q.1)) (k : ℕ) :
    ∫⁻ x, g (x k, countingMeasure (x, k)) ∂(Measure.infinitePi fun _ : ℕ => positionLaw ν)
      = ∫⁻ x, ∫⁻ y, g (y, countingMeasure (x, k)) ∂positionLaw ν
          ∂(Measure.infinitePi fun _ : ℕ => positionLaw ν) := by
  classical
  have hF : Measurable fun x : ℕ → E => g (x k, countingMeasure (x, k)) :=
    hg.comp ((measurable_id.prodMk measurable_const).prodMk (measurable_pi_apply k))
  rw [lintegral_infinitePi_update (fun _ : ℕ => positionLaw ν) k hF]
  refine lintegral_congr fun x => lintegral_congr fun y => ?_
  rw [Function.update_self]
  have hN : countingMeasure (Function.update x k y, k) = countingMeasure (x, k) := by
    simp only [countingMeasure]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [Function.update_of_ne hj.ne]
  rw [hN]

/-- **The reduced Mecke equation for a finite intensity** (the Palm formula):
`𝔼 ∑_{x ∈ N} g (x, N ∖ x) = ∫ 𝔼 g (x, N) dν(x)`.

Averaging a function of a point of the process together with the configuration of the *other*
points is averaging it against the intensity and an independent copy of the whole process. The
ordinary Mecke equation is the case `g (x, M) = f (x, M + δ_x)`. -/
theorem lintegral_sum_countingMeasureErase {g : E × Measure E → ℝ≥0∞}
    (hg : Measurable fun q : PoissonSample E × E => g (q.2, countingMeasure q.1)) :
    ∫⁻ p, ∑ i ∈ Finset.range p.2, g (p.1 i, countingMeasureErase p i) ∂poissonSampleLaw ν
      = ∫⁻ p, ∫⁻ x, g (x, countingMeasure p) ∂ν ∂poissonSampleLaw ν := by
  classical
  have hK := measurable_sum_countingMeasureErase hg
  have hK' : Measurable fun p : PoissonSample E => ∫⁻ x, g (x, countingMeasure p) ∂ν :=
    Measurable.lintegral_prod_right' hg
  have hH : ∀ k : ℕ, Measurable fun x : ℕ → E =>
      ∫⁻ y, g (y, countingMeasure (x, k)) ∂positionLaw ν := fun k =>
    Measurable.lintegral_prod_right'
      (f := fun q : (ℕ → E) × E => g (q.2, countingMeasure (q.1, k)))
      (hg.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd))
  rw [lintegral_poissonSampleLaw ν hK, lintegral_poissonSampleLaw ν hK']
  -- the `n`-th term of the left-hand side
  have hterm : ∀ n : ℕ, ∫⁻ x, ∑ i ∈ Finset.range n, g (x i, countingMeasureErase (x, n) i)
        ∂(Measure.infinitePi fun _ : ℕ => positionLaw ν)
      = n * ∫⁻ x, ∫⁻ y, g (y, countingMeasure (x, n - 1)) ∂positionLaw ν
        ∂(Measure.infinitePi fun _ : ℕ => positionLaw ν) := by
    intro n
    rw [lintegral_finsetSum (Finset.range n)
      (f := fun i (x : ℕ → E) => g (x i, countingMeasureErase (x, n) i)) fun i hi =>
        measurable_countingMeasureErase_summand hg (Finset.mem_range.1 hi)]
    cases n with
    | zero => rw [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul]
    | succ k =>
      rw [Finset.sum_congr rfl fun i hi => lintegral_countingMeasureErase_point_eq_last ν hg
        (Finset.mem_range.1 hi), Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        lintegral_countingMeasure_last_reduced ν hg k, Nat.add_sub_cancel]
  simp_rw [hterm]
  -- shift the Poisson series: `(k+1) P(k+1) = Λ(E) P(k)`
  obtain ⟨r, hr⟩ : ∃ r : ℝ≥0, (ν univ).toNNReal = r := ⟨_, rfl⟩
  have hν : ν univ = ENNReal.ofReal (r : ℝ) := by
    rw [ENNReal.ofReal_coe_nnreal, ← hr, ENNReal.coe_toNNReal (measure_ne_top _ _)]
  rw [hr, tsum_eq_zero_add' (by exact ENNReal.summable)]
  simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, Nat.add_sub_cancel]
  have hw : ∀ k : ℕ, ENNReal.ofReal (poissonWeight r (k + 1)) * ((k + 1 : ℕ) : ℝ≥0∞)
      = ν univ * ENNReal.ofReal (poissonWeight r k) := by
    intro k
    rw [hν, ← ENNReal.ofReal_mul (NNReal.coe_nonneg r), ← poissonWeight_succ_mul,
      ENNReal.ofReal_mul (poissonWeight_nonneg _ _), Nat.cast_succ,
      ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one, ENNReal.ofReal_natCast,
      ENNReal.ofReal_one]
  have hshift : ∀ k : ℕ, ENNReal.ofReal (poissonWeight r (k + 1)) * (((k + 1 : ℕ) : ℝ≥0∞) *
      ∫⁻ x, ∫⁻ y, g (y, countingMeasure (x, k)) ∂positionLaw ν
        ∂(Measure.infinitePi fun _ : ℕ => positionLaw ν))
      = ENNReal.ofReal (poissonWeight r k) * (ν univ *
        ∫⁻ x, ∫⁻ y, g (y, countingMeasure (x, k)) ∂positionLaw ν
          ∂(Measure.infinitePi fun _ : ℕ => positionLaw ν)) := by
    intro k
    rw [← mul_assoc, hw k, mul_assoc, mul_left_comm]
  simp_rw [hshift]
  refine tsum_congr fun k => ?_
  rw [← lintegral_const_mul _ (hH k)]
  refine congrArg _ (lintegral_congr fun x => ?_)
  rw [← smul_eq_mul, ← lintegral_smul_measure, smul_positionLaw]

/-- **The Mecke formula for a finite intensity**:
`𝔼 ∑_{x ∈ N} f (x, N) = ∫ 𝔼 f (x, N + δ_x) dν(x)`.

It is the case `g (x, M) = f (x, M + δ_x)` of the reduced equation
`lintegral_sum_countingMeasureErase`: for a point `x_i` of the sample, `N ∖ x_i + δ_{x_i} = N`. -/
theorem lintegral_lintegral_countingMeasure {f : E × Measure E → ℝ≥0∞}
    (hf : Measurable fun q : PoissonSample E × E => f (q.2, countingMeasure q.1))
    (hf' : Measurable fun q : PoissonSample E × E =>
      f (q.2, countingMeasure q.1 + Measure.dirac q.2)) :
    ∫⁻ p, ∫⁻ x, f (x, countingMeasure p) ∂countingMeasure p ∂poissonSampleLaw ν
      = ∫⁻ p, ∫⁻ x, f (x, countingMeasure p + Measure.dirac x) ∂ν ∂poissonSampleLaw ν := by
  have h := lintegral_sum_countingMeasureErase ν
    (g := fun q : E × Measure E => f (q.1, q.2 + Measure.dirac q.1)) hf'
  simp only at h
  rw [← h]
  refine lintegral_congr fun p => ?_
  have hfx : Measurable fun y => f (y, countingMeasure p) :=
    hf.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_countingMeasure p hfx]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [countingMeasureErase_add_dirac p (Finset.mem_range.1 hi)]

end Finite

/-! ### The Mecke formula for the superposition -/

section Superposition

variable [Nonempty E] (ν : ℕ → Measure E) [∀ n, IsFiniteMeasure (ν n)]

omit [Nonempty E] [∀ n, IsFiniteMeasure (ν n)] in
/-- The counting measure of a superposition, after resampling the piece `n`. -/
lemma superCounting_update (ω : SuperSample E) (n : ℕ) (p : PoissonSample E) :
    superCounting (Function.update ω n p)
      = countingMeasure p
        + Measure.sum (fun k => if k = n then 0 else countingMeasure (ω k)) := by
  ext s hs
  rw [superCounting, Measure.sum_apply _ hs, Measure.add_apply, Measure.sum_apply _ hs,
    ENNReal.tsum_eq_add_tsum_ite n, Function.update_self]
  congr 1
  refine tsum_congr fun k => ?_
  split_ifs with hk
  · simp
  · rw [Function.update_of_ne hk]

/-- **The Mecke formula for the superposition** of independent finite pieces. -/
theorem lintegral_lintegral_superCounting {f : E × Measure E → ℝ≥0∞}
    (hjoint : Measurable fun q : SuperSample E × E => f (q.2, superCounting q.1))
    (hG : Measurable fun q : SuperSample E × E =>
      f (q.2, superCounting q.1 + Measure.dirac q.2)) :
    ∫⁻ ω, ∫⁻ x, f (x, superCounting ω) ∂superCounting ω ∂superSampleLaw ν
      = ∫⁻ ω, ∫⁻ x, f (x, superCounting ω + Measure.dirac x) ∂Measure.sum ν
          ∂superSampleLaw ν := by
  have hF : ∀ n, Measurable fun ω : SuperSample E =>
      ∫⁻ x, f (x, superCounting ω) ∂countingMeasure (ω n) := by
    intro n
    have h1 := measurable_lintegral_countingMeasure_prod hjoint
    have h2 : Measurable fun ω : SuperSample E => (ω, ω n) :=
      measurable_id.prodMk (measurable_pi_apply n)
    have h3 := h1.comp h2
    exact h3
  have hG' : ∀ n, Measurable fun ω : SuperSample E =>
      ∫⁻ x, f (x, superCounting ω + Measure.dirac x) ∂ν n := fun n =>
    Measurable.lintegral_prod_right' hG
  have hL : ∀ ω : SuperSample E, ∫⁻ x, f (x, superCounting ω) ∂superCounting ω
      = ∑' n, ∫⁻ x, f (x, superCounting ω) ∂countingMeasure (ω n) := fun ω =>
    lintegral_superCounting ω _
  have hR : ∀ ω : SuperSample E, ∫⁻ x, f (x, superCounting ω + Measure.dirac x) ∂Measure.sum ν
      = ∑' n, ∫⁻ x, f (x, superCounting ω + Measure.dirac x) ∂ν n := fun ω =>
    lintegral_sum_measure _ _
  simp_rw [hL, hR]
  rw [lintegral_tsum fun n => (hF n).aemeasurable, lintegral_tsum fun n => (hG' n).aemeasurable]
  refine tsum_congr fun n => ?_
  -- resample the piece `n`
  have h1 := lintegral_infinitePi_update (fun n => poissonSampleLaw (ν n)) n (hF n)
  have h2 := lintegral_infinitePi_update (fun n => poissonSampleLaw (ν n)) n (hG' n)
  rw [superSampleLaw, h1, h2]
  refine lintegral_congr fun ω => ?_
  -- the finite Mecke formula for the piece `n`, with the other pieces frozen
  set R : Measure E := Measure.sum (fun k => if k = n then 0 else countingMeasure (ω k))
    with hR_def
  have hup : Measurable fun p : PoissonSample E => Function.update ω n p :=
    measurable_pi_lambda _ fun k => by
      rcases eq_or_ne k n with rfl | hk
      · simp only [Function.update_self]
        exact measurable_id
      · simp only [Function.update_of_ne hk]
        exact measurable_const
  have hfn : Measurable fun q : PoissonSample E × E =>
      f (q.2, countingMeasure q.1 + R) := by
    have hrw : ∀ q : PoissonSample E × E, f (q.2, countingMeasure q.1 + R)
        = f (q.2, superCounting (Function.update ω n q.1)) := fun q => by
      rw [superCounting_update, ← hR_def]
    simp_rw [hrw]
    exact hjoint.comp ((hup.comp measurable_fst).prodMk measurable_snd)
  have hfn' : Measurable fun q : PoissonSample E × E =>
      f (q.2, countingMeasure q.1 + Measure.dirac q.2 + R) := by
    have hrw : ∀ q : PoissonSample E × E, f (q.2, countingMeasure q.1 + Measure.dirac q.2 + R)
        = f (q.2, superCounting (Function.update ω n q.1) + Measure.dirac q.2) := fun q => by
      rw [superCounting_update, ← hR_def, add_right_comm]
    simp_rw [hrw]
    exact hG.comp ((hup.comp measurable_fst).prodMk measurable_snd)
  have h := lintegral_lintegral_countingMeasure (ν n)
    (f := fun q : E × Measure E => f (q.1, q.2 + R)) hfn hfn'
  simp only at h
  calc ∫⁻ p, ∫⁻ x, f (x, superCounting (Function.update ω n p))
          ∂countingMeasure ((Function.update ω n p) n) ∂poissonSampleLaw (ν n)
      = ∫⁻ p, ∫⁻ x, f (x, countingMeasure p + R) ∂countingMeasure p
          ∂poissonSampleLaw (ν n) := by
        refine lintegral_congr fun p => ?_
        rw [Function.update_self, superCounting_update]
    _ = ∫⁻ p, ∫⁻ x, f (x, countingMeasure p + Measure.dirac x + R) ∂ν n
          ∂poissonSampleLaw (ν n) := h
    _ = ∫⁻ p, ∫⁻ x, f (x, superCounting (Function.update ω n p) + Measure.dirac x) ∂ν n
          ∂poissonSampleLaw (ν n) := by
        refine lintegral_congr fun p => lintegral_congr fun x => ?_
        rw [superCounting_update, add_right_comm]

/-- **The bivariate Mecke equation at the level of the sample**, with no measurability hypothesis
beyond `Measurable f`:

`𝔼 ∑_{x, y ∈ N} f (x, y, N)
  = ∫∫ 𝔼 f (x, y, N + δ_x + δ_y) dΛ dΛ + ∫ 𝔼 f (x, x, N + δ_x) dΛ`.

The inner integrals are taken against counting measures of samples, so their joint measurability
in the sample is automatic (`measurable_lintegral_superCounting_prod`). This is what makes the
identity usable for an integrand that is a genuine function of the *pair* of points: for such an
integrand the inner integral has no closed form, and the corresponding hypothesis of
`lintegral_lintegral_lintegral_poissonPointProcessSum` — measurability of
`N ↦ ∫ f (x, y, N) dN(y)` on all of `Measure E` — is not available (Mathlib's slice lemma
`measurable_measure_prodMk_left` needs `SFinite`, and the identity kernel `μ ↦ μ` is not
s-finite). -/
theorem lintegral_lintegral_lintegral_superCounting {f : E × E × Measure E → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ ω, ∫⁻ x, ∫⁻ y, f (x, y, superCounting ω) ∂superCounting ω ∂superCounting ω
        ∂superSampleLaw ν
      = (∫⁻ ω, ∫⁻ x, ∫⁻ y, f (x, y, superCounting ω + Measure.dirac x + Measure.dirac y)
            ∂Measure.sum ν ∂Measure.sum ν ∂superSampleLaw ν)
        + ∫⁻ ω, ∫⁻ x, f (x, x, superCounting ω + Measure.dirac x) ∂Measure.sum ν
            ∂superSampleLaw ν := by
  have hsc : Measurable fun q : (SuperSample E × E) × E =>
      f (q.1.2, q.2, superCounting q.1.1) :=
    hf.comp ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.prodMk
      (measurable_superCounting.comp (measurable_fst.comp measurable_fst))))
  have hsd : Measurable fun q : (SuperSample E × E) × E =>
      f (q.1.2, q.2, superCounting q.1.1 + Measure.dirac q.1.2) :=
    hf.comp ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.prodMk
      ((measurable_superCounting.comp (measurable_fst.comp measurable_fst)).add
        (Measure.measurable_dirac.comp (measurable_snd.comp measurable_fst)))))
  have hdup : Measurable fun q : SuperSample E × E => (q, q.1) :=
    measurable_id.prodMk measurable_fst
  have hjoint₁ : Measurable fun q : SuperSample E × E =>
      ∫⁻ y, f (q.2, y, superCounting q.1) ∂superCounting q.1 := by
    have h1 := measurable_lintegral_superCounting_prod (α := SuperSample E × E) hsc
    have h2 := h1.comp hdup
    exact h2
  have hsplit : Measurable fun q : SuperSample E × E =>
      ∫⁻ y, f (q.2, y, superCounting q.1 + Measure.dirac q.2) ∂superCounting q.1 := by
    have h1 := measurable_lintegral_superCounting_prod (α := SuperSample E × E) hsd
    have h2 := h1.comp hdup
    exact h2
  have hdiagm : Measurable fun q : SuperSample E × E =>
      f (q.2, q.2, superCounting q.1 + Measure.dirac q.2) :=
    hf.comp (measurable_snd.prodMk (measurable_snd.prodMk
      ((measurable_superCounting.comp measurable_fst).add
        (Measure.measurable_dirac.comp measurable_snd))))
  have hdirac : ∀ (N : Measure E) (x : E), Measurable fun y => f (x, y, N) :=
    fun N x => hf.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have hG₁ : Measurable fun q : SuperSample E × E =>
      ∫⁻ y, f (q.2, y, superCounting q.1 + Measure.dirac q.2)
        ∂(superCounting q.1 + Measure.dirac q.2) := by
    have hpt : ∀ q : SuperSample E × E,
        ∫⁻ y, f (q.2, y, superCounting q.1 + Measure.dirac q.2)
            ∂(superCounting q.1 + Measure.dirac q.2)
          = (∫⁻ y, f (q.2, y, superCounting q.1 + Measure.dirac q.2) ∂superCounting q.1)
            + f (q.2, q.2, superCounting q.1 + Measure.dirac q.2) := by
      intro q
      rw [lintegral_add_measure, lintegral_dirac' _ (hdirac _ q.2)]
    simp_rw [hpt]
    exact hsplit.add hdiagm
  -- Step 1: the one-point formula in the outer variable
  rw [lintegral_lintegral_superCounting ν
    (f := fun q : E × Measure E => ∫⁻ y, f (q.1, y, q.2) ∂q.2) hjoint₁ hG₁]
  -- Step 2: split off the diagonal
  have h3 : ∀ ω : SuperSample E,
      ∫⁻ x, (∫⁻ y, f (x, y, superCounting ω + Measure.dirac x)
          ∂(superCounting ω + Measure.dirac x)) ∂Measure.sum ν
        = (∫⁻ x, ∫⁻ y, f (x, y, superCounting ω + Measure.dirac x) ∂superCounting ω
            ∂Measure.sum ν)
          + ∫⁻ x, f (x, x, superCounting ω + Measure.dirac x) ∂Measure.sum ν := by
    intro ω
    have hpt : ∀ x : E, ∫⁻ y, f (x, y, superCounting ω + Measure.dirac x)
          ∂(superCounting ω + Measure.dirac x)
        = (∫⁻ y, f (x, y, superCounting ω + Measure.dirac x) ∂superCounting ω)
          + f (x, x, superCounting ω + Measure.dirac x) := fun x => by
      rw [lintegral_add_measure, lintegral_dirac' _ (hdirac _ x)]
    simp_rw [hpt]
    exact lintegral_add_left (hsplit.comp (measurable_const.prodMk measurable_id)) _
  simp_rw [h3]
  rw [lintegral_add_left (Measurable.lintegral_prod_right' (ν := Measure.sum ν) hsplit)]
  congr 1
  -- Step 3: the one-point formula in the inner variable, for each fixed outer point
  rw [lintegral_lintegral_swap (μ := superSampleLaw ν) (ν := Measure.sum ν)
    (f := fun (ω : SuperSample E) (x : E) =>
      ∫⁻ y, f (x, y, superCounting ω + Measure.dirac x) ∂superCounting ω) hsplit.aemeasurable]
  have hx : ∀ x : E,
      ∫⁻ ω, ∫⁻ y, f (x, y, superCounting ω + Measure.dirac x) ∂superCounting ω
          ∂superSampleLaw ν
        = ∫⁻ ω, ∫⁻ y, f (x, y, superCounting ω + Measure.dirac y + Measure.dirac x)
            ∂Measure.sum ν ∂superSampleLaw ν := by
    intro x
    exact lintegral_lintegral_superCounting ν
      (f := fun q : E × Measure E => f (x, q.1, q.2 + Measure.dirac x))
      (hf.comp (measurable_const.prodMk (measurable_snd.prodMk
        ((measurable_superCounting.comp measurable_fst).add measurable_const))))
      (hf.comp (measurable_const.prodMk (measurable_snd.prodMk
        (((measurable_superCounting.comp measurable_fst).add
          (Measure.measurable_dirac.comp measurable_snd)).add measurable_const))))
  simp_rw [hx]
  have hcomm : ∀ (N : Measure E) (x y : E),
      f (x, y, N + Measure.dirac y + Measure.dirac x)
        = f (x, y, N + Measure.dirac x + Measure.dirac y) := fun N x y => by
    rw [add_right_comm]
  simp_rw [hcomm]
  have hjoint2 : Measurable fun q : SuperSample E × E =>
      ∫⁻ y, f (q.2, y, superCounting q.1 + Measure.dirac q.2 + Measure.dirac y)
        ∂Measure.sum ν :=
    Measurable.lintegral_prod_right' (ν := Measure.sum ν)
      (hf.comp ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.prodMk
        (((measurable_superCounting.comp (measurable_fst.comp measurable_fst)).add
          (Measure.measurable_dirac.comp (measurable_snd.comp measurable_fst))).add
          (Measure.measurable_dirac.comp measurable_snd)))))
  exact (lintegral_lintegral_swap (μ := Measure.sum ν) (ν := superSampleLaw ν)
    (f := fun (x : E) (ω : SuperSample E) =>
      ∫⁻ y, f (x, y, superCounting ω + Measure.dirac x + Measure.dirac y) ∂Measure.sum ν)
    (hjoint2.comp (measurable_snd.prodMk measurable_fst)).aemeasurable)

/-! ### The reduced Mecke equation for the superposition -/

omit [Nonempty E] [∀ n, IsFiniteMeasure (ν n)] in
/-- The reduced configuration of a superposition, after resampling the piece `n`. -/
lemma superCountingErase_update (ω : SuperSample E) (n i : ℕ) (p : PoissonSample E) :
    superCountingErase (Function.update ω n p) n i
      = countingMeasureErase p i
        + Measure.sum (fun k => if k = n then 0 else countingMeasure (ω k)) := by
  ext s hs
  rw [superCountingErase, Measure.sum_apply _ hs, Measure.add_apply, Measure.sum_apply _ hs,
    ENNReal.tsum_eq_add_tsum_ite n]
  simp only [Function.update_self, ite_true]
  congr 1
  refine tsum_congr fun k => ?_
  split_ifs with hk
  · simp
  · rw [Function.update_of_ne hk]

omit [Nonempty E] in
/-- The reduced sum over the points of the piece `n` is a measurable function of the sample. -/
lemma measurable_sum_superCountingErase {g : E × Measure E → ℝ≥0∞}
    (hjoint : Measurable fun q : SuperSample E × E => g (q.2, superCounting q.1)) (n : ℕ) :
    Measurable fun ω : SuperSample E =>
      ∑ i ∈ Finset.range (ω n).2, g ((ω n).1 i, superCountingErase ω n i) := by
  classical
  have hpt : ∀ ω : SuperSample E,
      ∑ i ∈ Finset.range (ω n).2, g ((ω n).1 i, superCountingErase ω n i)
        = ∑' i, if i < (ω n).2 then g ((ω n).1 i, superCounting (superSampleErase ω n i))
            else 0 := by
    intro ω
    rw [tsum_eq_sum (s := Finset.range (ω n).2) (fun i hi => by
      rw [Finset.mem_range] at hi; simp [hi])]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    simp [hi, superCounting_superSampleErase ω hi]
  simp_rw [hpt]
  refine Measurable.tsum fun i => ?_
  refine Measurable.ite (measurableSet_lt measurable_const
    (measurable_snd.comp (measurable_pi_apply n))) ?_ measurable_const
  have hmap : Measurable fun ω : SuperSample E => (superSampleErase ω n i, (ω n).1 i) :=
    (measurable_superSampleErase n i).prodMk
      ((measurable_pi_apply i).comp (measurable_fst.comp (measurable_pi_apply n)))
  have h2 := hjoint.comp hmap
  simp only [Function.comp_def] at h2
  exact h2

/-- **The reduced Mecke equation for the superposition** of independent finite pieces (the Palm
formula for an s-finite intensity):

`𝔼 ∑_{x ∈ N} g (x, N ∖ x) = ∫ 𝔼 g (x, N) dΛ(x)`. -/
theorem lintegral_tsum_sum_superCountingErase {g : E × Measure E → ℝ≥0∞}
    (hjoint : Measurable fun q : SuperSample E × E => g (q.2, superCounting q.1)) :
    ∫⁻ ω, ∑' n, ∑ i ∈ Finset.range (ω n).2, g ((ω n).1 i, superCountingErase ω n i)
        ∂superSampleLaw ν
      = ∫⁻ ω, ∫⁻ x, g (x, superCounting ω) ∂Measure.sum ν ∂superSampleLaw ν := by
  have hF : ∀ n, Measurable fun ω : SuperSample E =>
      ∑ i ∈ Finset.range (ω n).2, g ((ω n).1 i, superCountingErase ω n i) :=
    measurable_sum_superCountingErase hjoint
  have hG' : ∀ n, Measurable fun ω : SuperSample E =>
      ∫⁻ x, g (x, superCounting ω) ∂ν n := fun n =>
    Measurable.lintegral_prod_right' hjoint
  have hR : ∀ ω : SuperSample E, ∫⁻ x, g (x, superCounting ω) ∂Measure.sum ν
      = ∑' n, ∫⁻ x, g (x, superCounting ω) ∂ν n := fun ω => lintegral_sum_measure _ _
  simp_rw [hR]
  rw [lintegral_tsum fun n => (hF n).aemeasurable, lintegral_tsum fun n => (hG' n).aemeasurable]
  refine tsum_congr fun n => ?_
  -- resample the piece `n`
  have h1 := lintegral_infinitePi_update (fun n => poissonSampleLaw (ν n)) n (hF n)
  have h2 := lintegral_infinitePi_update (fun n => poissonSampleLaw (ν n)) n (hG' n)
  rw [superSampleLaw, h1, h2]
  refine lintegral_congr fun ω => ?_
  -- the finite reduced Mecke equation for the piece `n`, with the other pieces frozen
  set R : Measure E := Measure.sum (fun k => if k = n then 0 else countingMeasure (ω k))
    with hR_def
  have hup : Measurable fun p : PoissonSample E => Function.update ω n p :=
    measurable_pi_lambda _ fun k => by
      rcases eq_or_ne k n with rfl | hk
      · simp only [Function.update_self]
        exact measurable_id
      · simp only [Function.update_of_ne hk]
        exact measurable_const
  have hgn : Measurable fun q : PoissonSample E × E => g (q.2, countingMeasure q.1 + R) := by
    have hrw : ∀ q : PoissonSample E × E, g (q.2, countingMeasure q.1 + R)
        = g (q.2, superCounting (Function.update ω n q.1)) := fun q => by
      rw [superCounting_update, ← hR_def]
    simp_rw [hrw]
    exact hjoint.comp ((hup.comp measurable_fst).prodMk measurable_snd)
  have h := lintegral_sum_countingMeasureErase (ν n)
    (g := fun q : E × Measure E => g (q.1, q.2 + R)) hgn
  simp only at h
  calc ∫⁻ p, ∑ i ∈ Finset.range ((Function.update ω n p) n).2,
          g (((Function.update ω n p) n).1 i, superCountingErase (Function.update ω n p) n i)
          ∂poissonSampleLaw (ν n)
      = ∫⁻ p, ∑ i ∈ Finset.range p.2, g (p.1 i, countingMeasureErase p i + R)
          ∂poissonSampleLaw (ν n) := by
        refine lintegral_congr fun p => ?_
        simp only [Function.update_self, superCountingErase_update, ← hR_def]
    _ = ∫⁻ p, ∫⁻ x, g (x, countingMeasure p + R) ∂ν n ∂poissonSampleLaw (ν n) := h
    _ = ∫⁻ p, ∫⁻ x, g (x, superCounting (Function.update ω n p)) ∂ν n
          ∂poissonSampleLaw (ν n) := by
        refine lintegral_congr fun p => lintegral_congr fun x => ?_
        rw [superCounting_update]

/-- **The off-diagonal bivariate Mecke equation** (the second-order Palm formula) at the level of
the sample:

`𝔼 ∑_{x ≠ y ∈ N} f (x, y, N) = ∫∫ 𝔼 f (x, y, N + δ_x + δ_y) dΛ dΛ`,

the sum being over ordered pairs of **distinct** points of the process (`superOffDiagSum`).  It is
the reduced Mecke equation in the outer point followed by the ordinary one in the inner point;
in particular it is **unconditional** — no finiteness of any moment is needed, in contrast to
what subtracting the diagonal from the full bivariate equation
(`lintegral_lintegral_lintegral_superCounting`) would require. -/
theorem lintegral_superOffDiagSum_superCounting {f : E × E × Measure E → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ ω, superOffDiagSum ω (fun x y => f (x, y, superCounting ω)) ∂superSampleLaw ν
      = ∫⁻ ω, ∫⁻ x, ∫⁻ y, f (x, y, superCounting ω + Measure.dirac x + Measure.dirac y)
          ∂Measure.sum ν ∂Measure.sum ν ∂superSampleLaw ν := by
  have hsd : Measurable fun q : (SuperSample E × E) × E =>
      f (q.1.2, q.2, superCounting q.1.1 + Measure.dirac q.1.2) :=
    hf.comp ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.prodMk
      ((measurable_superCounting.comp (measurable_fst.comp measurable_fst)).add
        (Measure.measurable_dirac.comp (measurable_snd.comp measurable_fst)))))
  have hdup : Measurable fun q : SuperSample E × E => (q, q.1) :=
    measurable_id.prodMk measurable_fst
  -- the reduced integrand `g (x, M) = ∫ f (x, y, M + δ_x) dM(y)`, measurable along the sample
  have hsplit : Measurable fun q : SuperSample E × E =>
      ∫⁻ y, f (q.2, y, superCounting q.1 + Measure.dirac q.2) ∂superCounting q.1 := by
    have h1 := measurable_lintegral_superCounting_prod (α := SuperSample E × E) hsd
    have h2 := h1.comp hdup
    exact h2
  have hdirac : ∀ (N : Measure E) (x : E), Measurable fun y => f (x, y, N) :=
    fun N x => hf.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  -- Step 1: the off-diagonal sum is the reduced sum of `g`
  have hL : ∀ ω : SuperSample E, superOffDiagSum ω (fun x y => f (x, y, superCounting ω))
      = ∑' n, ∑ i ∈ Finset.range (ω n).2,
          ∫⁻ y, f ((ω n).1 i, y, superCountingErase ω n i + Measure.dirac ((ω n).1 i))
            ∂superCountingErase ω n i := by
    intro ω
    rw [superOffDiagSum_eq_tsum_sum_lintegral ω (hdirac _)]
    refine tsum_congr fun n => Finset.sum_congr rfl fun i hi => ?_
    rw [superCountingErase_add_dirac ω (Finset.mem_range.1 hi)]
  simp_rw [hL]
  -- Step 2: the reduced Mecke equation in the outer point
  rw [lintegral_tsum_sum_superCountingErase ν
    (g := fun q : E × Measure E => ∫⁻ y, f (q.1, y, q.2 + Measure.dirac q.1) ∂q.2) hsplit]
  -- Step 3: the one-point formula in the inner point, for each fixed outer point
  rw [lintegral_lintegral_swap (μ := superSampleLaw ν) (ν := Measure.sum ν)
    (f := fun (ω : SuperSample E) (x : E) =>
      ∫⁻ y, f (x, y, superCounting ω + Measure.dirac x) ∂superCounting ω) hsplit.aemeasurable]
  have hx : ∀ x : E,
      ∫⁻ ω, ∫⁻ y, f (x, y, superCounting ω + Measure.dirac x) ∂superCounting ω
          ∂superSampleLaw ν
        = ∫⁻ ω, ∫⁻ y, f (x, y, superCounting ω + Measure.dirac y + Measure.dirac x)
            ∂Measure.sum ν ∂superSampleLaw ν := by
    intro x
    exact lintegral_lintegral_superCounting ν
      (f := fun q : E × Measure E => f (x, q.1, q.2 + Measure.dirac x))
      (hf.comp (measurable_const.prodMk (measurable_snd.prodMk
        ((measurable_superCounting.comp measurable_fst).add measurable_const))))
      (hf.comp (measurable_const.prodMk (measurable_snd.prodMk
        (((measurable_superCounting.comp measurable_fst).add
          (Measure.measurable_dirac.comp measurable_snd)).add measurable_const))))
  simp_rw [hx]
  have hcomm : ∀ (N : Measure E) (x y : E),
      f (x, y, N + Measure.dirac y + Measure.dirac x)
        = f (x, y, N + Measure.dirac x + Measure.dirac y) := fun N x y => by
    rw [add_right_comm]
  simp_rw [hcomm]
  have hjoint2 : Measurable fun q : SuperSample E × E =>
      ∫⁻ y, f (q.2, y, superCounting q.1 + Measure.dirac q.2 + Measure.dirac y)
        ∂Measure.sum ν :=
    Measurable.lintegral_prod_right' (ν := Measure.sum ν)
      (hf.comp ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.prodMk
        (((measurable_superCounting.comp (measurable_fst.comp measurable_fst)).add
          (Measure.measurable_dirac.comp (measurable_snd.comp measurable_fst))).add
          (Measure.measurable_dirac.comp measurable_snd)))))
  exact (lintegral_lintegral_swap (μ := Measure.sum ν) (ν := superSampleLaw ν)
    (f := fun (x : E) (ω : SuperSample E) =>
      ∫⁻ y, f (x, y, superCounting ω + Measure.dirac x + Measure.dirac y) ∂Measure.sum ν)
    (hjoint2.comp (measurable_snd.prodMk measurable_fst)).aemeasurable)

/-- **The second factorial moment measure of a Poisson process is `Λ ⊗ Λ`** (Last–Penrose,
*Lectures on the Poisson process*, Proposition 4.3 for `m = 2`): `𝔼 N^{(2)}(B) = (Λ ⊗ Λ)(B)`, and
more generally `𝔼 ∫ G dN^{(2)} = ∫ G d(Λ ⊗ Λ)`. It is the off-diagonal bivariate Mecke equation for
an integrand which does not see the configuration. -/
theorem lintegral_lintegral_superFactorialTwo {G : E × E → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ ω, ∫⁻ r, G r ∂superFactorialTwo ω ∂superSampleLaw ν
      = ∫⁻ r, G r ∂(Measure.sum ν).prod (Measure.sum ν) := by
  have hL : ∀ ω : SuperSample E, ∫⁻ r, G r ∂superFactorialTwo ω
      = superOffDiagSum ω fun x y =>
          (fun q : E × E × Measure E => G (q.1, q.2.1)) (x, y, superCounting ω) :=
    fun ω => lintegral_superFactorialTwo ω hG
  simp_rw [hL]
  rw [lintegral_superOffDiagSum_superCounting ν
    (f := fun q : E × E × Measure E => G (q.1, q.2.1))
    (hG.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))]
  simp only
  rw [lintegral_const, measure_univ, mul_one, lintegral_prod _ hG.aemeasurable]

/-- `𝔼 N^{(2)}(B) = (Λ ⊗ Λ)(B)` for every measurable `B ⊆ E × E`. -/
theorem lintegral_superFactorialTwo_apply {B : Set (E × E)} (hB : MeasurableSet B) :
    ∫⁻ ω, superFactorialTwo ω B ∂superSampleLaw ν = (Measure.sum ν).prod (Measure.sum ν) B := by
  have h := lintegral_lintegral_superFactorialTwo ν (G := B.indicator 1)
    (measurable_one.indicator hB)
  simpa only [lintegral_indicator_one hB] using h

end Superposition

/-! ### The Mecke formula for the law -/

section Law

variable [Nonempty E]

/-- **The Mecke formula** for the superposition of any decomposition `ν` into finite pieces, at
the level of its law. -/
theorem lintegral_lintegral_poissonPointProcessSum (ν : ℕ → Measure E)
    [∀ n, IsFiniteMeasure (ν n)] {f : E × Measure E → ℝ≥0∞} (hf : Measurable f)
    (hF : Measurable fun N : Measure E => ∫⁻ x, f (x, N) ∂N) :
    ∫⁻ N, ∫⁻ x, f (x, N) ∂N ∂poissonPointProcessSum ν
      = ∫⁻ N, ∫⁻ x, f (x, N + Measure.dirac x) ∂Measure.sum ν ∂poissonPointProcessSum ν := by
  have hlaw := hasLaw_superCounting ν
  have hG : Measurable fun N : Measure E => ∫⁻ x, f (x, N + Measure.dirac x) ∂Measure.sum ν :=
    Measurable.lintegral_prod_right' (hf.comp (measurable_snd.prodMk
      (measurable_fst.add (Measure.measurable_dirac.comp measurable_snd))))
  rw [← hlaw.lintegral_comp hF.aemeasurable, ← hlaw.lintegral_comp hG.aemeasurable]
  exact lintegral_lintegral_superCounting ν
    (hf.comp (measurable_snd.prodMk (measurable_superCounting.comp measurable_fst)))
    (hf.comp (measurable_snd.prodMk ((measurable_superCounting.comp measurable_fst).add
      (Measure.measurable_dirac.comp measurable_snd))))

/-- **The bivariate Mecke equation** (the second-order Palm formula): for a Poisson point process
with intensity `Λ = ∑ₙ νₙ`,

`𝔼 ∑_{x, y ∈ N} f (x, y, N)
  = ∫∫ 𝔼 f (x, y, N + δ_x + δ_y) dΛ dΛ + ∫ 𝔼 f (x, x, N + δ_x) dΛ`,

the two terms being the off-diagonal and the diagonal of the double sum. It follows from the
one-point formula applied twice, the diagonal appearing when the inner integral against
`N + δ_x` is split. -/
theorem lintegral_lintegral_lintegral_poissonPointProcessSum (ν : ℕ → Measure E)
    [∀ n, IsFiniteMeasure (ν n)] {f : E × E × Measure E → ℝ≥0∞} (hf : Measurable f)
    (hF : Measurable fun N : Measure E => ∫⁻ x, ∫⁻ y, f (x, y, N) ∂N ∂N)
    (hg : Measurable fun q : E × Measure E => ∫⁻ y, f (q.1, y, q.2) ∂q.2)
    (hg' : Measurable fun q : E × Measure E =>
      ∫⁻ y, f (q.1, y, q.2 + Measure.dirac q.1) ∂q.2) :
    ∫⁻ N, ∫⁻ x, ∫⁻ y, f (x, y, N) ∂N ∂N ∂poissonPointProcessSum ν
      = (∫⁻ N, ∫⁻ x, ∫⁻ y, f (x, y, N + Measure.dirac x + Measure.dirac y)
            ∂Measure.sum ν ∂Measure.sum ν ∂poissonPointProcessSum ν)
        + ∫⁻ N, ∫⁻ x, f (x, x, N + Measure.dirac x) ∂Measure.sum ν
            ∂poissonPointProcessSum ν := by
  have hdirac : Measurable fun q : Measure E × E => q.1 + Measure.dirac q.2 :=
    measurable_fst.add (Measure.measurable_dirac.comp measurable_snd)
  -- the diagonal integrand
  have hdiag : Measurable fun q : Measure E × E => f (q.2, q.2, q.1 + Measure.dirac q.2) :=
    hf.comp (measurable_snd.prodMk (measurable_snd.prodMk hdirac))
  -- the shifted inner integral, in `(N, x)`
  have hinner : Measurable fun q : Measure E × E =>
      ∫⁻ y, f (q.2, y, q.1 + Measure.dirac q.2) ∂q.1 :=
    hg'.comp (measurable_snd.prodMk measurable_fst)
  -- Step 1: the one-point formula in the outer variable
  have h1 : ∫⁻ N, ∫⁻ x, ∫⁻ y, f (x, y, N) ∂N ∂N ∂poissonPointProcessSum ν
      = ∫⁻ N, ∫⁻ x, ∫⁻ y, f (x, y, N + Measure.dirac x) ∂(N + Measure.dirac x)
          ∂Measure.sum ν ∂poissonPointProcessSum ν :=
    lintegral_lintegral_poissonPointProcessSum ν
      (f := fun q : E × Measure E => ∫⁻ y, f (q.1, y, q.2) ∂q.2) hg hF
  -- Step 2: split off the diagonal
  have h2 : ∀ (N : Measure E) (x : E),
      ∫⁻ y, f (x, y, N + Measure.dirac x) ∂(N + Measure.dirac x)
        = (∫⁻ y, f (x, y, N + Measure.dirac x) ∂N) + f (x, x, N + Measure.dirac x) := by
    intro N x
    have hmy : Measurable fun y => f (x, y, N + Measure.dirac x) :=
      hf.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
    rw [lintegral_add_measure, lintegral_dirac' _ hmy]
  have h3 : ∀ N : Measure E,
      ∫⁻ x, ∫⁻ y, f (x, y, N + Measure.dirac x) ∂(N + Measure.dirac x) ∂Measure.sum ν
        = (∫⁻ x, ∫⁻ y, f (x, y, N + Measure.dirac x) ∂N ∂Measure.sum ν)
          + ∫⁻ x, f (x, x, N + Measure.dirac x) ∂Measure.sum ν := by
    intro N
    simp_rw [h2]
    exact lintegral_add_left (hinner.comp (measurable_const.prodMk measurable_id)) _
  rw [h1]
  simp_rw [h3]
  rw [lintegral_add_left (Measurable.lintegral_prod_right' (ν := Measure.sum ν) hinner)]
  congr 1
  -- Step 3: the one-point formula in the inner variable, for each fixed outer point
  have hswap1 := lintegral_lintegral_swap (μ := poissonPointProcessSum ν) (ν := Measure.sum ν)
    (f := fun N x => ∫⁻ y, f (x, y, N + Measure.dirac x) ∂N) hinner.aemeasurable
  rw [hswap1]
  have hx : ∀ x : E, ∫⁻ N, ∫⁻ y, f (x, y, N + Measure.dirac x) ∂N ∂poissonPointProcessSum ν
      = ∫⁻ N, ∫⁻ y, f (x, y, N + Measure.dirac y + Measure.dirac x)
          ∂Measure.sum ν ∂poissonPointProcessSum ν := by
    intro x
    exact lintegral_lintegral_poissonPointProcessSum ν
      (f := fun q : E × Measure E => f (x, q.1, q.2 + Measure.dirac x))
      (hf.comp (measurable_const.prodMk (measurable_fst.prodMk
        (measurable_snd.add measurable_const))))
      (hinner.comp (measurable_id.prodMk measurable_const))
  simp_rw [hx]
  have hcomm : ∀ (N : Measure E) (x y : E),
      f (x, y, N + Measure.dirac y + Measure.dirac x)
        = f (x, y, N + Measure.dirac x + Measure.dirac y) := by
    intro N x y
    rw [add_right_comm]
  simp_rw [hcomm]
  have hjoint : Measurable fun q : E × Measure E =>
      ∫⁻ y, f (q.1, y, q.2 + Measure.dirac q.1 + Measure.dirac y) ∂Measure.sum ν :=
    Measurable.lintegral_prod_right' (ν := Measure.sum ν)
      (hf.comp ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.prodMk
        (((measurable_snd.comp measurable_fst).add
          (Measure.measurable_dirac.comp (measurable_fst.comp measurable_fst))).add
          (Measure.measurable_dirac.comp measurable_snd)))))
  exact (lintegral_lintegral_swap (μ := Measure.sum ν) (ν := poissonPointProcessSum ν)
    (f := fun x N => ∫⁻ y, f (x, y, N + Measure.dirac x + Measure.dirac y) ∂Measure.sum ν)
    (hjoint.comp (measurable_fst.prodMk measurable_snd)).aemeasurable)

/-- **The Mecke formula** for any random measure with the law of a superposition. -/
theorem HasLaw.lintegral_lintegral_sum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure E} {ν : ℕ → Measure E} [∀ n, IsFiniteMeasure (ν n)]
    (hN : HasLaw N (poissonPointProcessSum ν) P) {f : E × Measure E → ℝ≥0∞} (hf : Measurable f)
    (hF : Measurable fun N : Measure E => ∫⁻ x, f (x, N) ∂N) :
    ∫⁻ ω, ∫⁻ x, f (x, N ω) ∂N ω ∂P
      = ∫⁻ ω, ∫⁻ x, f (x, N ω + Measure.dirac x) ∂Measure.sum ν ∂P := by
  have hG : Measurable fun N : Measure E => ∫⁻ x, f (x, N + Measure.dirac x) ∂Measure.sum ν :=
    Measurable.lintegral_prod_right' (hf.comp (measurable_snd.prodMk
      (measurable_fst.add (Measure.measurable_dirac.comp measurable_snd))))
  rw [hN.lintegral_comp hF.aemeasurable, hN.lintegral_comp hG.aemeasurable]
  exact lintegral_lintegral_poissonPointProcessSum ν hf hF

/-- **The bivariate Mecke equation** for any random measure with the law of a superposition. -/
theorem HasLaw.lintegral_lintegral_lintegral_sum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure E} {ν : ℕ → Measure E} [∀ n, IsFiniteMeasure (ν n)]
    (hN : HasLaw N (poissonPointProcessSum ν) P) {f : E × E × Measure E → ℝ≥0∞}
    (hf : Measurable f) (hF : Measurable fun M : Measure E => ∫⁻ x, ∫⁻ y, f (x, y, M) ∂M ∂M)
    (hg : Measurable fun q : E × Measure E => ∫⁻ y, f (q.1, y, q.2) ∂q.2)
    (hg' : Measurable fun q : E × Measure E =>
      ∫⁻ y, f (q.1, y, q.2 + Measure.dirac q.1) ∂q.2) :
    ∫⁻ ω, ∫⁻ x, ∫⁻ y, f (x, y, N ω) ∂N ω ∂N ω ∂P
      = (∫⁻ ω, ∫⁻ x, ∫⁻ y, f (x, y, N ω + Measure.dirac x + Measure.dirac y)
            ∂Measure.sum ν ∂Measure.sum ν ∂P)
        + ∫⁻ ω, ∫⁻ x, f (x, x, N ω + Measure.dirac x) ∂Measure.sum ν ∂P := by
  have hR1 : Measurable fun M : Measure E => ∫⁻ x, ∫⁻ y,
      f (x, y, M + Measure.dirac x + Measure.dirac y) ∂Measure.sum ν ∂Measure.sum ν := by
    have h1 : Measurable fun q : (Measure E × E) × E =>
        f (q.1.2, q.2, q.1.1 + Measure.dirac q.1.2 + Measure.dirac q.2) :=
      hf.comp ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.prodMk
        (((measurable_fst.comp measurable_fst).add
          (Measure.measurable_dirac.comp (measurable_snd.comp measurable_fst))).add
          (Measure.measurable_dirac.comp measurable_snd))))
    exact Measurable.lintegral_prod_right' (ν := Measure.sum ν)
      (Measurable.lintegral_prod_right' (ν := Measure.sum ν) h1)
  have hR2 : Measurable fun M : Measure E =>
      ∫⁻ x, f (x, x, M + Measure.dirac x) ∂Measure.sum ν :=
    Measurable.lintegral_prod_right' (ν := Measure.sum ν)
      (hf.comp (measurable_snd.prodMk (measurable_snd.prodMk
        (measurable_fst.add (Measure.measurable_dirac.comp measurable_snd)))))
  rw [hN.lintegral_comp hF.aemeasurable, hN.lintegral_comp hR1.aemeasurable,
    hN.lintegral_comp hR2.aemeasurable]
  exact lintegral_lintegral_lintegral_poissonPointProcessSum ν hf hF hg hg'

/-- **The Mecke formula** for the Poisson point process with s-finite intensity `Λ`:
`𝔼 ∑_{x ∈ N} f (x, N) = ∫ 𝔼 f (x, N + δ_x) dΛ(x)`, for every measurable
`f : E × Measure E → ℝ≥0∞` such that `N ↦ ∫ f (x, N) dN(x)` is measurable. -/
theorem lintegral_lintegral_poissonPointProcess (Λ : Measure E) [SFinite Λ]
    {f : E × Measure E → ℝ≥0∞} (hf : Measurable f)
    (hF : Measurable fun N : Measure E => ∫⁻ x, f (x, N) ∂N) :
    ∫⁻ N, ∫⁻ x, f (x, N) ∂N ∂poissonPointProcess Λ
      = ∫⁻ N, ∫⁻ x, f (x, N + Measure.dirac x) ∂Λ ∂poissonPointProcess Λ := by
  have hlaw := hasLaw_superCounting_poissonPointProcess Λ
  have hG : Measurable fun N : Measure E => ∫⁻ x, f (x, N + Measure.dirac x) ∂Λ :=
    Measurable.lintegral_prod_right' (hf.comp (measurable_snd.prodMk
      (measurable_fst.add (Measure.measurable_dirac.comp measurable_snd))))
  rw [← hlaw.lintegral_comp hF.aemeasurable, ← hlaw.lintegral_comp hG.aemeasurable]
  have h := lintegral_lintegral_superCounting (sfiniteSeq Λ)
    (hf.comp (measurable_snd.prodMk (measurable_superCounting.comp measurable_fst)))
    (hf.comp (measurable_snd.prodMk ((measurable_superCounting.comp measurable_fst).add
      (Measure.measurable_dirac.comp measurable_snd))))
  rw [sum_sfiniteSeq] at h
  exact h

/-- **The Mecke formula** for any random measure with the Poisson law. -/
theorem HasLaw.lintegral_lintegral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure E} {Λ : Measure E} [SFinite Λ] (hN : HasLaw N (poissonPointProcess Λ) P)
    {f : E × Measure E → ℝ≥0∞} (hf : Measurable f)
    (hF : Measurable fun N : Measure E => ∫⁻ x, f (x, N) ∂N) :
    ∫⁻ ω, ∫⁻ x, f (x, N ω) ∂N ω ∂P = ∫⁻ ω, ∫⁻ x, f (x, N ω + Measure.dirac x) ∂Λ ∂P := by
  have hG : Measurable fun N : Measure E => ∫⁻ x, f (x, N + Measure.dirac x) ∂Λ :=
    Measurable.lintegral_prod_right' (hf.comp (measurable_snd.prodMk
      (measurable_fst.add (Measure.measurable_dirac.comp measurable_snd))))
  rw [hN.lintegral_comp hF.aemeasurable, hN.lintegral_comp hG.aemeasurable]
  exact lintegral_lintegral_poissonPointProcess Λ hf hF

/-- **Campbell's formula**: `𝔼 ∫ g dN = ∫ g dΛ`. -/
theorem lintegral_lintegral_poissonPointProcess_of_fst (Λ : Measure E) [SFinite Λ]
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ N, ∫⁻ x, g x ∂N ∂poissonPointProcess Λ = ∫⁻ x, g x ∂Λ := by
  have h := lintegral_lintegral_poissonPointProcess Λ (f := fun q => g q.1)
    (hg.comp measurable_fst) (Measure.measurable_lintegral hg)
  simp only at h
  rw [h, lintegral_const, measure_univ, mul_one]

theorem HasLaw.lintegral_lintegral_of_fst {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure E} {Λ : Measure E} [SFinite Λ] (hN : HasLaw N (poissonPointProcess Λ) P)
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, ∫⁻ x, g x ∂N ω ∂P = ∫⁻ x, g x ∂Λ := by
  rw [hN.lintegral_comp (Measure.measurable_lintegral hg).aemeasurable]
  exact lintegral_lintegral_poissonPointProcess_of_fst Λ hg

end Law

end ProbabilityTheory

end
