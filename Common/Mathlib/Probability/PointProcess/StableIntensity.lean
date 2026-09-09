/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The intensity `u^{-m-1} du` on `(0, ∞)`

Talagrand, *Mean Field Models for Spin Glasses*, Vol. II, (13.1): the measure `μ_m` on `(0, ∞)`
with density `u^{-m-1}`, `0 < m < 1`, the Lévy measure of the `m`-stable subordinator. It has
infinite mass near `0` and finite mass on `[ε, ∞)`, so we cut `(0, ∞)` into the dyadic pieces
`(1, ∞)`, `(2^{-n-1}, 2^{-n}]`, each of finite mass, and represent `μ_m` as their sum.

The analytic heart of the Poisson–Dirichlet computations is the scaling identity

`∫_0^∞ (1 - e^{-a u}) u^{-m-1} du = a^m · c_m`, `c_m = ∫_0^∞ (1 - e^{-u}) u^{-m-1} du ∈ (0, ∞)`,

which is Lemma 13.1.1 in Laplace-transform form: the image of `μ_m ⊗ ν` under `(u, v) ↦ u v` is
`(∫ v^m dν) μ_m`.

## Main statements

- `ProbabilityTheory.stableDensity`, `ProbabilityTheory.stableIntensity`,
  `ProbabilityTheory.stablePiece`, `ProbabilityTheory.lintegral_sum_stablePiece`.
- `ProbabilityTheory.isFiniteMeasure_stablePiece`.
- `ProbabilityTheory.stableConst`, `ProbabilityTheory.stableConst_pos`,
  `ProbabilityTheory.integrableOn_stableKernel`.
- `ProbabilityTheory.integral_one_sub_exp_mul_rpow`: **the scaling identity**.
- `ProbabilityTheory.lintegral_stableDensity_Ioi`: the mass of `(c, ∞)` is `c^{-m}/m`.
-/

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace ProbabilityTheory

noncomputable section

/-! ### The density and the intensity -/

/-- The density `u ↦ u^{-m-1}`, as an `ℝ≥0∞`-valued function. -/
def stableDensity (m u : ℝ) : ℝ≥0∞ := ENNReal.ofReal (u ^ (-m - 1))

lemma measurable_stableDensity (m : ℝ) : Measurable (stableDensity m) :=
  ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)

/-- Talagrand's measure `μ_m`: density `u^{-m-1}` on `(0, ∞)`. Vol. II, (13.1). -/
def stableIntensity (m : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (stableDensity m)

/-! ### Dyadic pieces of `(0, ∞)` -/

/-- `(1, ∞)`, then `(2^{-n-1}, 2^{-n}]`. -/
def dyadicPiece : ℕ → Set ℝ
  | 0 => Ioi 1
  | n + 1 => Ioc ((1 / 2 : ℝ) ^ (n + 1)) ((1 / 2 : ℝ) ^ n)

lemma measurableSet_dyadicPiece (n : ℕ) : MeasurableSet (dyadicPiece n) := by
  cases n with
  | zero => exact measurableSet_Ioi
  | succ n => exact measurableSet_Ioc

lemma half_pow_succ_lt (n : ℕ) : (1 / 2 : ℝ) ^ (n + 1) < (1 / 2 : ℝ) ^ n := by
  rw [pow_succ]
  exact mul_lt_of_lt_one_right (by positivity) (by norm_num)

lemma half_pow_le_one (n : ℕ) : (1 / 2 : ℝ) ^ n ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

lemma dyadicPiece_subset_Ioi (n : ℕ) : dyadicPiece n ⊆ Ioi ((1 / 2 : ℝ) ^ (n + 1)) := by
  cases n with
  | zero =>
    intro x hx
    simp only [dyadicPiece, mem_Ioi] at hx ⊢
    norm_num
    linarith
  | succ n =>
    intro x hx
    simp only [dyadicPiece, mem_Ioc, mem_Ioi] at hx ⊢
    exact lt_trans (half_pow_succ_lt (n + 1)) hx.1

lemma dyadicPiece_subset_Ioi_zero (n : ℕ) : dyadicPiece n ⊆ Ioi 0 :=
  (dyadicPiece_subset_Ioi n).trans (Ioi_subset_Ioi (by positivity))

lemma disjoint_dyadicPiece_of_lt {i j : ℕ} (hij : i < j) :
    Disjoint (dyadicPiece i) (dyadicPiece j) := by
  rw [Set.disjoint_left]
  intro x hi hj
  cases i with
  | zero =>
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    simp only [dyadicPiece, mem_Ioi, mem_Ioc] at hi hj
    linarith [hj.2, half_pow_le_one k]
  | succ a =>
    obtain ⟨b, rfl⟩ : ∃ b, j = b + 1 := ⟨j - 1, by omega⟩
    simp only [dyadicPiece, mem_Ioc] at hi hj
    have hab : a + 1 ≤ b := by omega
    have : (1 / 2 : ℝ) ^ b ≤ (1 / 2 : ℝ) ^ (a + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hab
    linarith [hi.1, hj.2]

lemma pairwise_disjoint_dyadicPiece : Pairwise (Disjoint on dyadicPiece) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact disjoint_dyadicPiece_of_lt h
  · exact (disjoint_dyadicPiece_of_lt h).symm

lemma iUnion_dyadicPiece : ⋃ n, dyadicPiece n = Ioi 0 := by
  refine subset_antisymm (iUnion_subset fun n => dyadicPiece_subset_Ioi_zero n) fun t ht => ?_
  rw [mem_Ioi] at ht
  rw [mem_iUnion]
  rcases lt_or_ge 1 t with h1 | h1
  · exact ⟨0, h1⟩
  · have hinv : (1 : ℝ) ≤ 1 / t := by rw [le_one_div (by norm_num) ht]; simpa using h1
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hinv (by norm_num : (1 : ℝ) < 2)
    refine ⟨n + 1, ?_⟩
    simp only [dyadicPiece, mem_Ioc, one_div_pow]
    constructor
    · rw [one_div_lt (by positivity) ht]
      simpa using hn2
    · rw [le_one_div ht (by positivity)]
      exact hn1

/-! ### The pieces of the intensity -/

/-- The intensity restricted to the `n`-th dyadic piece. -/
def stablePiece (m : ℝ) (n : ℕ) : Measure ℝ :=
  (volume.restrict (dyadicPiece n)).withDensity (stableDensity m)

lemma lintegral_stablePiece (m : ℝ) (n : ℕ) {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ u, F u ∂stablePiece m n = ∫⁻ u in dyadicPiece n, stableDensity m u * F u := by
  rw [stablePiece, lintegral_withDensity_eq_lintegral_mul _ (measurable_stableDensity m) hF]
  rfl

/-- The pieces sum to the intensity, in integrated form. -/
lemma lintegral_sum_stablePiece (m : ℝ) {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ u, F u ∂Measure.sum (stablePiece m) = ∫⁻ u in Ioi 0, stableDensity m u * F u := by
  rw [lintegral_sum_measure]
  simp_rw [lintegral_stablePiece m _ hF]
  rw [← lintegral_iUnion measurableSet_dyadicPiece pairwise_disjoint_dyadicPiece,
    iUnion_dyadicPiece]

lemma integrableOn_rpow_dyadicPiece {m : ℝ} (hm : 0 < m) (n : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ (-m - 1)) (dyadicPiece n) :=
  (integrableOn_Ioi_rpow_of_lt (by linarith) (by positivity : (0 : ℝ) < (1 / 2) ^ (n + 1))).mono_set
    (dyadicPiece_subset_Ioi n)

lemma isFiniteMeasure_stablePiece {m : ℝ} (hm : 0 < m) (n : ℕ) :
    IsFiniteMeasure (stablePiece m n) := by
  refine ⟨?_⟩
  rw [stablePiece, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hnn : 0 ≤ᵐ[volume.restrict (dyadicPiece n)] fun u : ℝ => u ^ (-m - 1) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' (measurableSet_dyadicPiece n)]
    exact Filter.Eventually.of_forall fun u hu =>
      Real.rpow_nonneg (le_of_lt (dyadicPiece_subset_Ioi_zero n hu)) _
  exact (hasFiniteIntegral_iff_ofReal hnn).1 (integrableOn_rpow_dyadicPiece hm n).hasFiniteIntegral

/-! ### The scaling identity -/

/-- The kernel `u ↦ (1 - e^{-u}) u^{-m-1}`. -/
def stableKernel (m u : ℝ) : ℝ := (1 - Real.exp (-u)) * u ^ (-m - 1)

lemma measurable_stableKernel (m : ℝ) : Measurable (stableKernel m) :=
  (measurable_const.sub (Real.measurable_exp.comp measurable_neg)).mul (measurable_id.pow_const _)

lemma stableKernel_nonneg {m u : ℝ} (hu : 0 < u) : 0 ≤ stableKernel m u :=
  mul_nonneg (by linarith [Real.exp_le_one_iff.2 (by linarith : -u ≤ 0)]) (Real.rpow_nonneg hu.le _)

lemma stableKernel_pos {m u : ℝ} (hu : 0 < u) : 0 < stableKernel m u :=
  mul_pos (by linarith [Real.exp_lt_one_iff.2 (by linarith : -u < 0)]) (Real.rpow_pos_of_pos hu _)

/-- `(1 - e^{-u}) u^{-m-1} ≤ u^{-m}` for `u > 0`. -/
lemma stableKernel_le_rpow {m u : ℝ} (hu : 0 < u) : stableKernel m u ≤ u ^ (-m) := by
  have h1 : 1 - Real.exp (-u) ≤ u := by linarith [Real.add_one_le_exp (-u)]
  have h2 : u * u ^ (-m - 1) = u ^ (-m) := by
    conv_rhs => rw [show (-m : ℝ) = 1 + (-m - 1) by ring, Real.rpow_add hu, Real.rpow_one]
  calc stableKernel m u = (1 - Real.exp (-u)) * u ^ (-m - 1) := rfl
    _ ≤ u * u ^ (-m - 1) := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hu.le _)
    _ = u ^ (-m) := h2

/-- `(1 - e^{-u}) u^{-m-1} ≤ u^{-m-1}` for `u > 0`. -/
lemma stableKernel_le_rpow' {m u : ℝ} (hu : 0 < u) : stableKernel m u ≤ u ^ (-m - 1) := by
  have h1 : 1 - Real.exp (-u) ≤ 1 := by linarith [Real.exp_pos (-u)]
  calc stableKernel m u = (1 - Real.exp (-u)) * u ^ (-m - 1) := rfl
    _ ≤ 1 * u ^ (-m - 1) := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hu.le _)
    _ = u ^ (-m - 1) := one_mul _

/-- The kernel is integrable on `(0, ∞)` for `0 < m < 1`. -/
theorem integrableOn_stableKernel {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) :
    IntegrableOn (stableKernel m) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  refine IntegrableOn.union ?_ ?_
  · -- on `(0, 1]`: dominated by `u^{-m}`
    have hint : IntegrableOn (fun u : ℝ => u ^ (-m)) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    refine Integrable.mono' hint (measurable_stableKernel m).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun u hu => by
      rw [Real.norm_eq_abs, abs_of_nonneg (stableKernel_nonneg hu.1)]
      exact stableKernel_le_rpow hu.1
  · -- on `(1, ∞)`: dominated by `u^{-m-1}`
    have hint : IntegrableOn (fun u : ℝ => u ^ (-m - 1)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine Integrable.mono' hint (measurable_stableKernel m).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun u hu => by
      have hu0 : 0 < u := lt_trans one_pos hu
      rw [Real.norm_eq_abs, abs_of_nonneg (stableKernel_nonneg hu0)]
      exact stableKernel_le_rpow' hu0

/-- `c_m = ∫_0^∞ (1 - e^{-u}) u^{-m-1} du`. -/
def stableConst (m : ℝ) : ℝ := ∫ u in Ioi 0, stableKernel m u

lemma stableConst_pos {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) : 0 < stableConst m := by
  rw [stableConst, setIntegral_pos_iff_support_of_nonneg_ae ?_ (integrableOn_stableKernel hm0 hm1)]
  · have hsub : Ioi 0 ⊆ Function.support (stableKernel m) ∩ Ioi 0 := fun u hu =>
      ⟨Function.mem_support.2 (stableKernel_pos hu).ne', hu⟩
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    simp
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun u hu => stableKernel_nonneg hu

/-- **The scaling identity**: `∫_0^∞ (1 - e^{-a u}) u^{-m-1} du = a^m c_m` for `a ≥ 0`. -/
theorem integral_one_sub_exp_mul_rpow {m : ℝ} (hm0 : 0 < m) {a : ℝ} (ha : 0 ≤ a) :
    ∫ u in Ioi 0, (1 - Real.exp (-(a * u))) * u ^ (-m - 1) = a ^ m * stableConst m := by
  rcases eq_or_lt_of_le ha with rfl | ha
  · simp [Real.zero_rpow hm0.ne']
  -- pointwise: `(1 - e^{-au}) u^{-m-1} = a^{m+1} · stableKernel m (a u)`
  have hpt : ∀ u ∈ Ioi (0 : ℝ),
      (1 - Real.exp (-(a * u))) * u ^ (-m - 1) = a ^ (m + 1) * stableKernel m (a * u) := by
    intro u hu
    rw [mem_Ioi] at hu
    rw [stableKernel, Real.mul_rpow ha.le hu.le]
    have : a ^ (m + 1) * a ^ (-m - 1) = 1 := by
      rw [← Real.rpow_add ha]; norm_num
    calc (1 - Real.exp (-(a * u))) * u ^ (-m - 1)
        = (a ^ (m + 1) * a ^ (-m - 1)) * ((1 - Real.exp (-(a * u))) * u ^ (-m - 1)) := by
          rw [this, one_mul]
      _ = a ^ (m + 1) * ((1 - Real.exp (-(a * u))) * (a ^ (-m - 1) * u ^ (-m - 1))) := by ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_comp_mul_left_Ioi (stableKernel m) 0 ha, mul_zero, smul_eq_mul, ← mul_assoc,
    ← Real.rpow_neg_one a, ← Real.rpow_add ha]
  rw [stableConst]
  ring_nf

/-- The scaling identity in `ℝ≥0∞`-integral form. -/
theorem lintegral_stableDensity_one_sub_exp {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) {a : ℝ}
    (ha : 0 ≤ a) :
    ∫⁻ u in Ioi 0, stableDensity m u * ENNReal.ofReal (1 - Real.exp (-(a * u)))
      = ENNReal.ofReal (a ^ m * stableConst m) := by
  rw [← integral_one_sub_exp_mul_rpow hm0 ha]
  have hint : IntegrableOn (fun u : ℝ => (1 - Real.exp (-(a * u))) * u ^ (-m - 1)) (Ioi 0) := by
    rcases eq_or_lt_of_le ha with rfl | ha
    · simp
    have h1 : IntegrableOn (fun u : ℝ => stableKernel m (a * u)) (Ioi 0) := by
      rw [integrableOn_Ioi_comp_mul_left_iff _ 0 ha, mul_zero]
      exact integrableOn_stableKernel hm0 hm1
    refine IntegrableOn.congr_fun
      (show IntegrableOn (fun u : ℝ => a ^ (m + 1) * stableKernel m (a * u)) (Ioi 0) volume from
        h1.const_mul _) ?_ measurableSet_Ioi
    intro u hu
    rw [mem_Ioi] at hu
    beta_reduce
    rw [stableKernel, Real.mul_rpow ha.le hu.le]
    have : a ^ (m + 1) * a ^ (-m - 1) = 1 := by
      rw [← Real.rpow_add ha]; norm_num
    calc a ^ (m + 1) * ((1 - Real.exp (-(a * u))) * (a ^ (-m - 1) * u ^ (-m - 1)))
        = (a ^ (m + 1) * a ^ (-m - 1)) * ((1 - Real.exp (-(a * u))) * u ^ (-m - 1)) := by ring
      _ = (1 - Real.exp (-(a * u))) * u ^ (-m - 1) := by rw [this, one_mul]
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      fun u : ℝ => (1 - Real.exp (-(a * u))) * u ^ (-m - 1) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun u hu =>
      mul_nonneg (by linarith [Real.exp_le_one_iff.2 (by nlinarith [mem_Ioi.1 hu] : -(a * u) ≤ 0)])
        (Real.rpow_nonneg (le_of_lt hu) _)
  rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
  refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  rw [stableDensity, ← ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hu) _), mul_comm]

/-! ### The mass of `(c, ∞)` -/

/-- `μ_m ((c, ∞)) = c^{-m}/m` for `c > 0`. -/
theorem lintegral_stableDensity_Ioi {m : ℝ} (hm : 0 < m) {c : ℝ} (hc : 0 < c) :
    ∫⁻ u in Ioi c, stableDensity m u = ENNReal.ofReal (c ^ (-m) / m) := by
  have hint : IntegrableOn (fun u : ℝ => u ^ (-m - 1)) (Ioi c) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hc
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi c)] fun u : ℝ => u ^ (-m - 1) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun u hu =>
      Real.rpow_nonneg (le_of_lt (lt_trans hc (mem_Ioi.1 hu))) _
  simp only [stableDensity]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_Ioi_rpow_of_lt (by linarith) hc]
  congr 1
  have : -m - 1 + 1 = -m := by ring
  rw [this]
  field_simp

end

end ProbabilityTheory
