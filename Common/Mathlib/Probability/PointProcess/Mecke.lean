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
- `ProbabilityTheory.lintegral_lintegral_countingMeasure`: Mecke for a finite intensity.
- `ProbabilityTheory.lintegral_lintegral_superCounting`: Mecke for the superposition.
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

/-- Every point of a sample of size `k + 1` contributes as much as the last one, by
exchangeability. -/
lemma lintegral_countingMeasure_point_eq_last {f : E × Measure E → ℝ≥0∞} (hf : Measurable f)
    {k i : ℕ} (hi : i < k + 1) :
    ∫⁻ x, f (x i, countingMeasure (x, k + 1)) ∂(Measure.infinitePi fun _ : ℕ => positionLaw ν)
      = ∫⁻ x, f (x k, countingMeasure (x, k + 1))
          ∂(Measure.infinitePi fun _ : ℕ => positionLaw ν) := by
  classical
  have hF : Measurable fun x : ℕ → E => f (x i, countingMeasure (x, k + 1)) :=
    hf.comp ((measurable_pi_apply i).prodMk
      (measurable_countingMeasure.comp (measurable_id.prodMk measurable_const)))
  rw [← lintegral_infinitePi_comp_equiv (positionLaw ν) (Equiv.swap i k) hF]
  refine lintegral_congr fun x => ?_
  have hN : countingMeasure (fun j => x ((Equiv.swap i k) j), k + 1)
      = countingMeasure (x, k + 1) := by
    simp only [countingMeasure]
    refine Equiv.Perm.sum_comp (Equiv.swap i k) (Finset.range (k + 1))
      (fun j => Measure.dirac (x j)) fun j hj => ?_
    rw [Set.mem_ofPred_eq] at hj
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra hcon
    push Not at hcon
    exact hj (Equiv.swap_apply_of_ne_of_ne (by omega) (by omega))
  simp only [Equiv.swap_apply_left, hN]

/-- Resampling the last point of a sample of size `k + 1`. -/
lemma lintegral_countingMeasure_last {f : E × Measure E → ℝ≥0∞} (hf : Measurable f) (k : ℕ) :
    ∫⁻ x, f (x k, countingMeasure (x, k + 1)) ∂(Measure.infinitePi fun _ : ℕ => positionLaw ν)
      = ∫⁻ x, ∫⁻ y, f (y, countingMeasure (x, k) + Measure.dirac y) ∂positionLaw ν
          ∂(Measure.infinitePi fun _ : ℕ => positionLaw ν) := by
  classical
  have hF : Measurable fun x : ℕ → E => f (x k, countingMeasure (x, k + 1)) :=
    hf.comp ((measurable_pi_apply k).prodMk
      (measurable_countingMeasure.comp (measurable_id.prodMk measurable_const)))
  rw [lintegral_infinitePi_update (fun _ : ℕ => positionLaw ν) k hF]
  refine lintegral_congr fun x => lintegral_congr fun y => ?_
  rw [countingMeasure_succ, Function.update_self]
  have hN : countingMeasure (Function.update x k y, k) = countingMeasure (x, k) := by
    simp only [countingMeasure]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [Function.update_of_ne hj.ne]
  rw [hN]

/-- **The Mecke formula for a finite intensity**:
`𝔼 ∑_{x ∈ N} f (x, N) = ∫ 𝔼 f (x, N + δ_x) dν(x)`. -/
theorem lintegral_lintegral_countingMeasure {f : E × Measure E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, ∫⁻ x, f (x, countingMeasure p) ∂countingMeasure p ∂poissonSampleLaw ν
      = ∫⁻ p, ∫⁻ x, f (x, countingMeasure p + Measure.dirac x) ∂ν ∂poissonSampleLaw ν := by
  classical
  -- measurability of both integrands
  have hK : Measurable fun p : PoissonSample E =>
      ∫⁻ x, f (x, countingMeasure p) ∂countingMeasure p := by
    have h1 := measurable_lintegral_countingMeasure_prod (α := PoissonSample E)
      (f := fun q : PoissonSample E × E => f (q.2, countingMeasure q.1))
      (hf.comp (measurable_snd.prodMk (measurable_countingMeasure.comp measurable_fst)))
    have h2 : Measurable fun p : PoissonSample E => (p, p) := measurable_id.prodMk measurable_id
    have h3 := h1.comp h2
    exact h3
  have hG : Measurable fun q : PoissonSample E × E =>
      f (q.2, countingMeasure q.1 + Measure.dirac q.2) :=
    hf.comp (measurable_snd.prodMk ((measurable_countingMeasure.comp measurable_fst).add
      (Measure.measurable_dirac.comp measurable_snd)))
  have hK' : Measurable fun p : PoissonSample E =>
      ∫⁻ x, f (x, countingMeasure p + Measure.dirac x) ∂ν :=
    Measurable.lintegral_prod_right' hG
  have hH : ∀ k : ℕ, Measurable fun x : ℕ → E =>
      ∫⁻ y, f (y, countingMeasure (x, k) + Measure.dirac y) ∂positionLaw ν := fun k =>
    Measurable.lintegral_prod_right'
      (f := fun q : (ℕ → E) × E => f (q.2, countingMeasure (q.1, k) + Measure.dirac q.2))
      (hf.comp (measurable_snd.prodMk ((measurable_countingMeasure.comp
        (measurable_fst.prodMk measurable_const)).add
          (Measure.measurable_dirac.comp measurable_snd))))
  rw [lintegral_poissonSampleLaw ν hK, lintegral_poissonSampleLaw ν hK']
  -- the `n`-th term of the left-hand side
  have hterm : ∀ n : ℕ, ∫⁻ x, ∫⁻ y, f (y, countingMeasure (x, n)) ∂countingMeasure (x, n)
        ∂(Measure.infinitePi fun _ : ℕ => positionLaw ν)
      = n * ∫⁻ x, ∫⁻ y, f (y, countingMeasure (x, n - 1) + Measure.dirac y) ∂positionLaw ν
        ∂(Measure.infinitePi fun _ : ℕ => positionLaw ν) := by
    intro n
    have hfx : ∀ x : ℕ → E, Measurable fun y => f (y, countingMeasure (x, n)) := fun x =>
      hf.comp (measurable_id.prodMk measurable_const)
    simp_rw [fun x => lintegral_countingMeasure (x, n) (hfx x)]
    rw [lintegral_finsetSum (Finset.range n)
      (f := fun i (x : ℕ → E) => f (x i, countingMeasure (x, n))) fun i _ =>
        hf.comp ((measurable_pi_apply i).prodMk
          (measurable_countingMeasure.comp (measurable_id.prodMk measurable_const)))]
    cases n with
    | zero => rw [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul]
    | succ k =>
      rw [Finset.sum_congr rfl fun i hi => lintegral_countingMeasure_point_eq_last ν hf
        (Finset.mem_range.1 hi), Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        lintegral_countingMeasure_last ν hf k, Nat.add_sub_cancel]
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
      ∫⁻ x, ∫⁻ y, f (y, countingMeasure (x, k) + Measure.dirac y) ∂positionLaw ν
        ∂(Measure.infinitePi fun _ : ℕ => positionLaw ν))
      = ENNReal.ofReal (poissonWeight r k) * (ν univ *
        ∫⁻ x, ∫⁻ y, f (y, countingMeasure (x, k) + Measure.dirac y) ∂positionLaw ν
          ∂(Measure.infinitePi fun _ : ℕ => positionLaw ν)) := by
    intro k
    rw [← mul_assoc, hw k, mul_assoc, mul_left_comm]
  simp_rw [hshift]
  refine tsum_congr fun k => ?_
  rw [← lintegral_const_mul _ (hH k)]
  refine congrArg _ (lintegral_congr fun x => ?_)
  rw [← smul_eq_mul, ← lintegral_smul_measure, smul_positionLaw]

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
theorem lintegral_lintegral_superCounting {f : E × Measure E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, ∫⁻ x, f (x, superCounting ω) ∂superCounting ω ∂superSampleLaw ν
      = ∫⁻ ω, ∫⁻ x, f (x, superCounting ω + Measure.dirac x) ∂Measure.sum ν
          ∂superSampleLaw ν := by
  have hjoint : Measurable fun q : SuperSample E × E => f (q.2, superCounting q.1) :=
    hf.comp (measurable_snd.prodMk (measurable_superCounting.comp measurable_fst))
  have hF : ∀ n, Measurable fun ω : SuperSample E =>
      ∫⁻ x, f (x, superCounting ω) ∂countingMeasure (ω n) := by
    intro n
    have h1 := measurable_lintegral_countingMeasure_prod hjoint
    have h2 : Measurable fun ω : SuperSample E => (ω, ω n) :=
      measurable_id.prodMk (measurable_pi_apply n)
    have h3 := h1.comp h2
    exact h3
  have hG : Measurable fun q : SuperSample E × E =>
      f (q.2, superCounting q.1 + Measure.dirac q.2) :=
    hf.comp (measurable_snd.prodMk ((measurable_superCounting.comp measurable_fst).add
      (Measure.measurable_dirac.comp measurable_snd)))
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
  have hfn : Measurable fun q : E × Measure E => f (q.1, q.2 + R) :=
    hf.comp (measurable_fst.prodMk (measurable_snd.add measurable_const))
  have h := lintegral_lintegral_countingMeasure (ν n) hfn
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
  exact lintegral_lintegral_superCounting ν hf

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
  have h := lintegral_lintegral_superCounting (sfiniteSeq Λ) hf
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
