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
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The intensity `u^{-m-1} du` on `(0, ∞)`

Talagrand, *Mean Field Models for Spin Glasses*, Vol. II, (13.1): the measure `μ_m` on `(0, ∞)`
with density `u^{-m-1}`, `0 < m < 1`, the Lévy measure of the `m`-stable subordinator. It has
infinite mass near `0` and finite mass on `[ε, ∞)`; it is s-finite, which is all the Poisson point
process construction needs.

The analytic heart of the Poisson–Dirichlet computations is the scaling identity

`∫_0^∞ (1 - e^{-a u}) u^{-m-1} du = a^m · c_m`, `c_m = ∫_0^∞ (1 - e^{-u}) u^{-m-1} du ∈ (0, ∞)`,

which is Lemma 13.1.1 in Laplace-transform form: the image of `μ_m ⊗ ν` under `(u, v) ↦ u v` is
`(∫ v^m dν) μ_m`.

## Main statements

- `ProbabilityTheory.stableDensity`, `ProbabilityTheory.stableIntensity`,
  `ProbabilityTheory.lintegral_stableIntensity`; the intensity is `SFinite`.
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

/-! ### The intensity is s-finite, and integrates against `u^{-m-1} du` -/

instance (m : ℝ) : SFinite (stableIntensity m) := by
  unfold stableIntensity; infer_instance

lemma lintegral_stableIntensity (m : ℝ) {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ u, F u ∂stableIntensity m = ∫⁻ u in Ioi 0, stableDensity m u * F u := by
  rw [stableIntensity, lintegral_withDensity_eq_lintegral_mul _ (measurable_stableDensity m) hF]
  rfl

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

/-- Integrability of `(1 - e^{-au}) u^{-m-1}` on `(0, ∞)`. -/
theorem integrableOn_one_sub_exp_mul_rpow {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) {a : ℝ}
    (ha : 0 ≤ a) :
    IntegrableOn (fun u : ℝ => (1 - Real.exp (-(a * u))) * u ^ (-m - 1)) (Ioi 0) := by
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

lemma one_sub_exp_mul_rpow_nonneg {m a u : ℝ} (ha : 0 ≤ a) (hu : 0 < u) :
    0 ≤ (1 - Real.exp (-(a * u))) * u ^ (-m - 1) :=
  mul_nonneg (by linarith [Real.exp_le_one_iff.2 (by nlinarith : -(a * u) ≤ 0)])
    (Real.rpow_nonneg hu.le _)

/-- The scaling identity in `ℝ≥0∞`-integral form. -/
theorem lintegral_stableDensity_one_sub_exp {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) {a : ℝ}
    (ha : 0 ≤ a) :
    ∫⁻ u in Ioi 0, stableDensity m u * ENNReal.ofReal (1 - Real.exp (-(a * u)))
      = ENNReal.ofReal (a ^ m * stableConst m) := by
  rw [← integral_one_sub_exp_mul_rpow hm0 ha]
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      fun u : ℝ => (1 - Real.exp (-(a * u))) * u ^ (-m - 1) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun u hu => one_sub_exp_mul_rpow_nonneg ha hu
  rw [ofReal_integral_eq_lintegral_ofReal (integrableOn_one_sub_exp_mul_rpow hm0 hm1 ha) hnn]
  refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  rw [stableDensity, ← ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hu) _), mul_comm]

/-! ### The moment integral `∫ (1 - e^{-a u^m}) u^{-m'-1} du` -/

/-- The substitution `u = w^{1/m}` in the scaling identity: for `0 < m' < m`,
`∫₀^∞ (1 - e^{-a u^m}) u^{-m'-1} du = a^{m'/m} c_{m'/m} / m`. This is the integral behind the
moments of order `m' < m` of a stable sum. -/
theorem integral_one_sub_exp_mul_rpow_rpow {m m' : ℝ} (hm0 : 0 < m) (hm'0 : 0 < m') {a : ℝ}
    (ha : 0 ≤ a) :
    ∫ u in Ioi 0, (1 - Real.exp (-(a * u ^ m))) * u ^ (-m' - 1)
      = a ^ (m' / m) * stableConst (m' / m) / m := by
  have hq : 0 < m' / m := div_pos hm'0 hm0
  have hsub := integral_comp_rpow_Ioi
    (fun w : ℝ => (1 - Real.exp (-(a * w))) * w ^ (-(m' / m) - 1)) hm0.ne'
  rw [integral_one_sub_exp_mul_rpow hq ha] at hsub
  have hpt : ∀ u ∈ Ioi (0 : ℝ), (|m| * u ^ (m - 1)) •
      ((fun w : ℝ => (1 - Real.exp (-(a * w))) * w ^ (-(m' / m) - 1)) (u ^ m))
      = m * ((1 - Real.exp (-(a * u ^ m))) * u ^ (-m' - 1)) := by
    intro u hu
    rw [mem_Ioi] at hu
    simp only [smul_eq_mul, abs_of_pos hm0]
    rw [← Real.rpow_mul hu.le]
    have h1 : m * (-(m' / m) - 1) = -m' - m := by field_simp
    rw [h1]
    have h2 : u ^ (m - 1) * u ^ (-m' - m) = u ^ (-m' - 1) := by
      rw [← Real.rpow_add hu]; ring_nf
    calc m * u ^ (m - 1) * ((1 - Real.exp (-(a * u ^ m))) * u ^ (-m' - m))
        = m * ((1 - Real.exp (-(a * u ^ m))) * (u ^ (m - 1) * u ^ (-m' - m))) := by ring
      _ = m * ((1 - Real.exp (-(a * u ^ m))) * u ^ (-m' - 1)) := by rw [h2]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul] at hsub
  rw [eq_div_iff hm0.ne', mul_comm, hsub]

theorem integrableOn_one_sub_exp_mul_rpow_rpow {m m' : ℝ} (hm0 : 0 < m) (hm'0 : 0 < m')
    (hm'm : m' < m) {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun u : ℝ => (1 - Real.exp (-(a * u ^ m))) * u ^ (-m' - 1)) (Ioi 0) := by
  have hq : 0 < m' / m := div_pos hm'0 hm0
  have hq1 : m' / m < 1 := (div_lt_one hm0).2 hm'm
  have h := (integrableOn_Ioi_comp_rpow_iff
    (fun w : ℝ => (1 - Real.exp (-(a * w))) * w ^ (-(m' / m) - 1)) hm0.ne').2
    (integrableOn_one_sub_exp_mul_rpow hq hq1 ha)
  have hpt : ∀ u ∈ Ioi (0 : ℝ), (|m| * u ^ (m - 1)) •
      ((fun w : ℝ => (1 - Real.exp (-(a * w))) * w ^ (-(m' / m) - 1)) (u ^ m))
      = m * ((1 - Real.exp (-(a * u ^ m))) * u ^ (-m' - 1)) := by
    intro u hu
    rw [mem_Ioi] at hu
    simp only [smul_eq_mul, abs_of_pos hm0]
    rw [← Real.rpow_mul hu.le]
    have h1 : m * (-(m' / m) - 1) = -m' - m := by field_simp
    rw [h1]
    have h2 : u ^ (m - 1) * u ^ (-m' - m) = u ^ (-m' - 1) := by
      rw [← Real.rpow_add hu]; ring_nf
    calc m * u ^ (m - 1) * ((1 - Real.exp (-(a * u ^ m))) * u ^ (-m' - m))
        = m * ((1 - Real.exp (-(a * u ^ m))) * (u ^ (m - 1) * u ^ (-m' - m))) := by ring
      _ = m * ((1 - Real.exp (-(a * u ^ m))) * u ^ (-m' - 1)) := by rw [h2]
  have h' : IntegrableOn (fun u : ℝ => m⁻¹ * (m * ((1 - Real.exp (-(a * u ^ m)))
      * u ^ (-m' - 1)))) (Ioi 0) := (h.congr_fun hpt measurableSet_Ioi).const_mul m⁻¹
  refine h'.congr_fun (fun u _ => ?_) measurableSet_Ioi
  simp only
  rw [← mul_assoc, inv_mul_cancel₀ hm0.ne', one_mul]

/-- The moment integral in `ℝ≥0∞`-integral form. -/
theorem lintegral_stableDensity_one_sub_exp_rpow {m m' : ℝ} (hm0 : 0 < m) (hm'0 : 0 < m')
    (hm'm : m' < m) {a : ℝ} (ha : 0 ≤ a) :
    ∫⁻ u in Ioi 0, stableDensity m' u * ENNReal.ofReal (1 - Real.exp (-(a * u ^ m)))
      = ENNReal.ofReal (a ^ (m' / m) * stableConst (m' / m) / m) := by
  rw [← integral_one_sub_exp_mul_rpow_rpow hm0 hm'0 ha]
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      fun u : ℝ => (1 - Real.exp (-(a * u ^ m))) * u ^ (-m' - 1) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun u hu => ?_
    have hum : 0 ≤ u ^ m := Real.rpow_nonneg (le_of_lt hu) m
    exact mul_nonneg (by linarith [Real.exp_le_one_iff.2 (by nlinarith : -(a * u ^ m) ≤ 0)])
      (Real.rpow_nonneg (le_of_lt hu) _)
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrableOn_one_sub_exp_mul_rpow_rpow hm0 hm'0 hm'm ha) hnn]
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

/-- `μ_m ((c, ∞)) = c^{-m}/m` for `c > 0`, as a value of the intensity. -/
theorem stableIntensity_Ioi {m : ℝ} (hm : 0 < m) {c : ℝ} (hc : 0 < c) :
    stableIntensity m (Ioi c) = ENNReal.ofReal (c ^ (-m) / m) := by
  rw [stableIntensity, withDensity_apply _ measurableSet_Ioi, Measure.restrict_restrict
    measurableSet_Ioi, Set.Ioi_inter_Ioi, max_eq_left hc.le, lintegral_stableDensity_Ioi hm hc]

/-- `μ_m` has infinite total mass: `∫₀^∞ u^{-m-1} du = ∞`. -/
theorem lintegral_stableDensity_Ioi_zero {m : ℝ} (hm : 0 < m) :
    ∫⁻ u in Ioi 0, stableDensity m u = ∞ := by
  by_contra hne
  set L := (∫⁻ u in Ioi 0, stableDensity m u).toReal with hL
  have hLnn : 0 ≤ L := ENNReal.toReal_nonneg
  -- the mass of `(c, ∞)` with `c^{-m} = m L + 1` exceeds `L`
  set c : ℝ := (m * L + 1) ^ (-(1 / m)) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos (by positivity) _
  have hcm : c ^ (-m) = m * L + 1 := by
    rw [hc, ← Real.rpow_mul (by positivity)]
    have : -(1 / m) * -m = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hle : ∫⁻ u in Ioi c, stableDensity m u ≤ ∫⁻ u in Ioi 0, stableDensity m u :=
    lintegral_mono_set (Set.Ioi_subset_Ioi hcpos.le)
  rw [lintegral_stableDensity_Ioi hm hcpos, hcm] at hle
  have hle' := ENNReal.toReal_mono hne hle
  rw [ENNReal.toReal_ofReal (by positivity), ← hL] at hle'
  have : (m * L + 1) / m = L + 1 / m := by field_simp
  rw [this] at hle'
  have : 0 < 1 / m := by positivity
  linarith

/-! ### The stable constant and the Gamma function -/

/-- **`m c_m = Γ(1 - m)`**: integration by parts in `∫₀^∞ (1 - e^{-u}) u^{-m-1} du`. -/
theorem mul_stableConst_eq_Gamma {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) :
    m * stableConst m = Real.Gamma (1 - m) := by
  -- `F u = (1 - e^{-u}) u^{-m}` has derivative `e^{-u} u^{-m} - m (1 - e^{-u}) u^{-m-1}`
  set F : ℝ → ℝ := fun u => (1 - Real.exp (-u)) * u ^ (-m) with hF
  set F' : ℝ → ℝ := fun u => Real.exp (-u) * u ^ (-m) + (1 - Real.exp (-u)) * (-m * u ^ (-m - 1))
    with hF'
  have hderiv : ∀ u ∈ Ioi (0 : ℝ), HasDerivAt F (F' u) u := by
    intro u hu
    rw [mem_Ioi] at hu
    have h1 : HasDerivAt (fun u : ℝ => 1 - Real.exp (-u)) (Real.exp (-u)) u := by
      have := ((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).const_sub 1
      simpa using this
    have h2 : HasDerivAt (fun u : ℝ => u ^ (-m)) (-m * u ^ (-m - 1)) u :=
      Real.hasDerivAt_rpow_const (Or.inl hu.ne')
    exact h1.mul h2
  have hF0 : F 0 = 0 := by simp [hF, Real.zero_rpow (neg_ne_zero.2 hm0.ne')]
  -- bounds: `0 ≤ F u ≤ u^{1-m}` and `F u ≤ u^{-m}` for `u > 0`
  have hFnn : ∀ u, 0 < u → 0 ≤ F u := fun u hu =>
    mul_nonneg (by linarith [Real.exp_le_one_iff.2 (by linarith : -u ≤ 0)])
      (Real.rpow_nonneg hu.le _)
  have hFle : ∀ u, 0 < u → F u ≤ u ^ (1 - m) := by
    intro u hu
    have h1 : 1 - Real.exp (-u) ≤ u := by linarith [Real.one_sub_le_exp_neg u]
    calc F u = (1 - Real.exp (-u)) * u ^ (-m) := rfl
      _ ≤ u * u ^ (-m) := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hu.le _)
      _ = u ^ (1 - m) := by
          rw [sub_eq_add_neg, Real.rpow_add hu, Real.rpow_one]
  have hFle' : ∀ u, 0 < u → F u ≤ u ^ (-m) := by
    intro u hu
    have h1 : 1 - Real.exp (-u) ≤ 1 := by linarith [Real.exp_pos (-u)]
    calc F u = (1 - Real.exp (-u)) * u ^ (-m) := rfl
      _ ≤ 1 * u ^ (-m) := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hu.le _)
      _ = u ^ (-m) := one_mul _
  have hcont : ContinuousWithinAt F (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt, hF0]
    have hlim : Tendsto (fun u : ℝ => u ^ (1 - m)) (𝓝[>] 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 (1 - m) (Or.inr (by linarith))).tendsto
      rw [Real.zero_rpow (by linarith : (1 : ℝ) - m ≠ 0)] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (eventually_nhdsWithin_of_forall fun u hu => hFnn u hu)
      (eventually_nhdsWithin_of_forall fun u hu => hFle u hu)
  have htop : Tendsto F atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (tendsto_rpow_neg_atTop hm0)
      ((eventually_gt_atTop 0).mono fun u hu => hFnn u hu)
      ((eventually_gt_atTop 0).mono fun u hu => hFle' u hu)
  -- integrability of the two parts of `F'`
  have hint1 : IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ (-m)) (Ioi 0) := by
    have := Real.GammaIntegral_convergent (by linarith : 0 < 1 - m)
    simpa [sub_sub_cancel_left] using this
  have hint2 : IntegrableOn (fun u : ℝ => (1 - Real.exp (-u)) * (-m * u ^ (-m - 1))) (Ioi 0) := by
    have h : IntegrableOn (fun u : ℝ => -m * stableKernel m u) (Ioi 0) :=
      (integrableOn_stableKernel hm0 hm1).const_mul (-m)
    refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp only [stableKernel]
    ring
  have hint : IntegrableOn F' (Ioi 0) := hint1.add hint2
  have hIBP := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htop
  rw [hF0, sub_zero] at hIBP
  -- `∫ F' = Γ(1-m) - m c_m`
  have hsplit : ∫ u in Ioi (0 : ℝ), F' u
      = Real.Gamma (1 - m) + (-m) * stableConst m := by
    rw [integral_add hint1 hint2, Real.Gamma_eq_integral (by linarith), stableConst]
    congr 1
    · refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      simp [sub_sub_cancel_left]
    · rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      simp only [stableKernel]
      ring
  rw [hsplit] at hIBP
  linarith

/-- The Gamma integral in `ℝ≥0∞`-integral form: `∫₀^∞ u^{a-1} e^{-ru} du = r^{-a} Γ(a)`. -/
theorem lintegral_rpow_mul_exp_neg_mul_Ioi {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫⁻ u in Ioi 0, ENNReal.ofReal (u ^ (a - 1) * Real.exp (-(r * u)))
      = ENNReal.ofReal ((1 / r) ^ a * Real.Gamma a) := by
  rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr]
  have hint : IntegrableOn (fun u : ℝ => u ^ (a - 1) * Real.exp (-(r * u))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : -1 < a - 1) one_pos hr
    refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp [Real.rpow_one]
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] fun u : ℝ => u ^ (a - 1) * Real.exp (-(r * u)) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun u hu =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt hu) _) (Real.exp_pos _).le
  rw [ofReal_integral_eq_lintegral_ofReal hint hnn]

/-- `∫₀^∞ s^{m-1} e^{-b s^m} ds = 1 / (m b)`, by the substitution `t = s^m`. -/
theorem integral_rpow_mul_exp_neg_mul_rpow_Ioi {m b : ℝ} (hm0 : 0 < m) (hb : 0 < b) :
    ∫ s in Ioi (0 : ℝ), s ^ (m - 1) * Real.exp (-(b * s ^ m)) = 1 / (m * b) := by
  have hsub := integral_comp_rpow_Ioi (fun t : ℝ => Real.exp (-(b * t))) hm0.ne'
  have hexp : ∫ t in Ioi (0 : ℝ), Real.exp (-(b * t)) = b⁻¹ := by
    have := integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x)) 0 hb
    simp only [mul_zero, smul_eq_mul] at this
    rw [this, integral_exp_neg_Ioi_zero, mul_one]
  rw [hexp] at hsub
  have hpt : ∀ s ∈ Ioi (0 : ℝ), (|m| * s ^ (m - 1)) •
      ((fun t : ℝ => Real.exp (-(b * t))) (s ^ m))
        = m * (s ^ (m - 1) * Real.exp (-(b * s ^ m))) := by
    intro s _
    simp only [smul_eq_mul, abs_of_pos hm0]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul] at hsub
  rw [one_div, mul_inv, ← hsub, ← mul_assoc, inv_mul_cancel₀ hm0.ne', one_mul]

theorem lintegral_rpow_mul_exp_neg_mul_rpow_Ioi {m b : ℝ} (hm0 : 0 < m) (hb : 0 < b) :
    ∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ (m - 1) * Real.exp (-(b * s ^ m)))
      = ENNReal.ofReal (1 / (m * b)) := by
  rw [← integral_rpow_mul_exp_neg_mul_rpow_Ioi hm0 hb]
  have hint : IntegrableOn (fun s : ℝ => s ^ (m - 1) * Real.exp (-(b * s ^ m))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : -1 < m - 1) hm0 hb
    refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp [neg_mul]
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      fun s : ℝ => s ^ (m - 1) * Real.exp (-(b * s ^ m)) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun u hu =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt hu) _) (Real.exp_pos _).le
  rw [ofReal_integral_eq_lintegral_ofReal hint hnn]

/-- `∫₀^∞ s^{b-1} e^{-β s^m} ds = Γ(b/m) β^{-b/m} / m`, by the substitution `t = s^m`. -/
theorem integral_rpow_mul_exp_neg_mul_rpow_Ioi' {m b β : ℝ} (hm0 : 0 < m) (hb : 0 < b)
    (hβ : 0 < β) :
    ∫ s in Ioi (0 : ℝ), s ^ (b - 1) * Real.exp (-(β * s ^ m))
      = (1 / m) * ((1 / β) ^ (b / m) * Real.Gamma (b / m)) := by
  have hsub := integral_comp_rpow_Ioi
    (fun t : ℝ => t ^ (b / m - 1) * Real.exp (-(β * t))) hm0.ne'
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (div_pos hb hm0) hβ] at hsub
  have hpt : ∀ s ∈ Ioi (0 : ℝ), (|m| * s ^ (m - 1)) •
      ((fun t : ℝ => t ^ (b / m - 1) * Real.exp (-(β * t))) (s ^ m))
        = m * (s ^ (b - 1) * Real.exp (-(β * s ^ m))) := by
    intro s hs
    rw [mem_Ioi] at hs
    simp only [smul_eq_mul, abs_of_pos hm0]
    rw [← Real.rpow_mul hs.le]
    have h1 : m * (b / m - 1) = b - m := by field_simp
    have h2 : s ^ (m - 1) * s ^ (b - m) = s ^ (b - 1) := by
      rw [← Real.rpow_add hs]; ring_nf
    rw [h1]
    calc m * s ^ (m - 1) * (s ^ (b - m) * Real.exp (-(β * s ^ m)))
        = m * ((s ^ (m - 1) * s ^ (b - m)) * Real.exp (-(β * s ^ m))) := by ring
      _ = m * (s ^ (b - 1) * Real.exp (-(β * s ^ m))) := by rw [h2]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul] at hsub
  rw [← hsub, one_div, ← mul_assoc, inv_mul_cancel₀ hm0.ne', one_mul]

theorem lintegral_rpow_mul_exp_neg_mul_rpow_Ioi' {m b β : ℝ} (hm0 : 0 < m) (hb : 0 < b)
    (hβ : 0 < β) :
    ∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ (b - 1) * Real.exp (-(β * s ^ m)))
      = ENNReal.ofReal ((1 / m) * ((1 / β) ^ (b / m) * Real.Gamma (b / m))) := by
  rw [← integral_rpow_mul_exp_neg_mul_rpow_Ioi' hm0 hb hβ]
  have hint : IntegrableOn (fun s : ℝ => s ^ (b - 1) * Real.exp (-(β * s ^ m))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : -1 < b - 1) hm0 hβ
    refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp [neg_mul]
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      fun s : ℝ => s ^ (b - 1) * Real.exp (-(β * s ^ m)) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun u hu =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt hu) _) (Real.exp_pos _).le
  rw [ofReal_integral_eq_lintegral_ofReal hint hnn]

end

end ProbabilityTheory

/-! ### An explicit decomposition of the intensity into nonzero finite pieces -/

namespace ProbabilityTheory

open MeasureTheory Set

/-- The pieces of an explicit decomposition of `(0, ∞)` into bounded intervals away from `0`:
`stablePiece n = (1/(n+2), 1/(n+1)] ∪ (n+1, n+2]`. -/
def stablePiece (n : ℕ) : Set ℝ :=
  Ioc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1)) ∪ Ioc ((n : ℝ) + 1) ((n : ℝ) + 2)

lemma measurableSet_stablePiece (n : ℕ) : MeasurableSet (stablePiece n) :=
  measurableSet_Ioc.union measurableSet_Ioc

lemma stablePiece_subset_Ioi (n : ℕ) : stablePiece n ⊆ Ioi 0 := by
  rintro x (hx | hx)
  · exact Set.mem_Ioi.2 (lt_trans (by positivity) hx.1)
  · exact Set.mem_Ioi.2 (lt_trans (by positivity) hx.1)

lemma stablePiece_subset_Icc (n : ℕ) :
    stablePiece n ⊆ Icc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) := by
  have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h2 : (1 : ℝ) / ((n : ℝ) + 2) ≤ (n : ℝ) + 1 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rintro x (hx | hx)
  · exact ⟨hx.1.le, hx.2.trans (by linarith)⟩
  · exact ⟨by linarith [hx.1], hx.2⟩

lemma iUnion_stablePiece : ⋃ n, stablePiece n = Ioi 0 := by
  classical
  refine Subset.antisymm (iUnion_subset stablePiece_subset_Ioi) fun x hx => ?_
  have hx0 : 0 < x := Set.mem_Ioi.1 hx
  rcases le_or_gt x 1 with h1 | h1
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx0
    have hex : ∃ n : ℕ, 1 / ((n : ℝ) + 1) < x := ⟨n, hn⟩
    have hk : 1 / ((Nat.find hex : ℝ) + 1) < x := Nat.find_spec hex
    rcases (Nat.find hex).eq_zero_or_pos with hk0 | hkpos
    · exfalso
      rw [hk0] at hk
      norm_num at hk
      exact absurd hk (not_lt.2 h1)
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hkpos.ne'
      have hmin : ¬ 1 / ((j : ℝ) + 1) < x := Nat.find_min hex (by omega)
      have hjk : (Nat.find hex : ℝ) = j + 1 := by exact_mod_cast hj
      rw [hjk] at hk
      refine mem_iUnion.2 ⟨j, Or.inl ⟨?_, not_lt.1 hmin⟩⟩
      have h2 : (1 : ℝ) / ((j : ℝ) + 2) = 1 / ((j : ℝ) + 1 + 1) := by ring
      rw [h2]
      exact hk
  · have hex : ∃ n : ℕ, x ≤ (n : ℝ) + 2 := by
      obtain ⟨n, hn⟩ := exists_nat_gt x
      exact ⟨n, by linarith⟩
    have hk : x ≤ (Nat.find hex : ℝ) + 2 := Nat.find_spec hex
    rcases (Nat.find hex).eq_zero_or_pos with hk0 | hkpos
    · rw [hk0] at hk
      norm_num at hk
      exact mem_iUnion.2 ⟨0, Or.inr ⟨by norm_num; exact h1, by norm_num; exact hk⟩⟩
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hkpos.ne'
      have hmin : ¬ x ≤ (j : ℝ) + 2 := Nat.find_min hex (by omega)
      have hjk : (Nat.find hex : ℝ) = j + 1 := by exact_mod_cast hj
      rw [hjk] at hk
      refine mem_iUnion.2 ⟨j + 1, Or.inr ⟨?_, ?_⟩⟩
      · push_cast
        linarith [not_le.1 hmin]
      · push_cast
        linarith

lemma pairwise_disjoint_stablePiece : Pairwise (Function.onFun Disjoint stablePiece) := by
  intro a b hab
  simp only [Function.onFun, stablePiece]
  have hlow : ∀ n : ℕ, ∀ x ∈ Ioc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1)), x ≤ 1 := by
    intro n x hx
    refine hx.2.trans ?_
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hhigh : ∀ n : ℕ, ∀ x ∈ Ioc ((n : ℝ) + 1) ((n : ℝ) + 2), 1 < x := by
    intro n x hx
    linarith [hx.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hcross : ∀ a b : ℕ, Disjoint (Ioc (1 / ((a : ℝ) + 2)) (1 / ((a : ℝ) + 1)))
      (Ioc ((b : ℝ) + 1) ((b : ℝ) + 2)) := by
    intro a b
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd (hhigh b x hx') (not_lt.2 (hlow a x hx))
  have hlowlow : ∀ a b : ℕ, a < b → Disjoint (Ioc (1 / ((a : ℝ) + 2)) (1 / ((a : ℝ) + 1)))
      (Ioc (1 / ((b : ℝ) + 2)) (1 / ((b : ℝ) + 1))) := by
    intro a b h
    rw [Set.disjoint_left]
    intro x hx hx'
    have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
    have h1 : (1 : ℝ) / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    exact absurd (lt_of_lt_of_le hx.1 (hx'.2.trans h1)) (lt_irrefl _)
  have hhighhigh : ∀ a b : ℕ, a < b → Disjoint (Ioc ((a : ℝ) + 1) ((a : ℝ) + 2))
      (Ioc ((b : ℝ) + 1) ((b : ℝ) + 2)) := by
    intro a b h
    rw [Set.disjoint_left]
    intro x hx hx'
    have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
    linarith [hx.2, hx'.1]
  rcases lt_or_gt_of_ne hab with h | h
  · exact Set.disjoint_union_left.2 ⟨Set.disjoint_union_right.2 ⟨hlowlow a b h, hcross a b⟩,
      Set.disjoint_union_right.2 ⟨(hcross b a).symm, hhighhigh a b h⟩⟩
  · exact Set.disjoint_union_left.2 ⟨Set.disjoint_union_right.2 ⟨(hlowlow b a h).symm, hcross a b⟩,
      Set.disjoint_union_right.2 ⟨(hcross b a).symm, (hhighhigh b a h).symm⟩⟩

/-- **An explicit decomposition of the stable intensity into nonzero finite pieces**:
`μ_m = ∑ₙ μ_m|_{stablePiece n}`. Unlike Mathlib's `sfiniteSeq`, every piece is nonzero for
`m > 0`, so that the position law of a product piece `(μ_m|_{piece}) ⊗ η` is a product. -/
noncomputable def stableSeq (m : ℝ) (n : ℕ) : Measure ℝ :=
  (stableIntensity m).restrict (stablePiece n)

lemma stableIntensity_restrict_Ioi (m : ℝ) :
    (stableIntensity m).restrict (Ioi 0) = stableIntensity m := by
  rw [stableIntensity, restrict_withDensity measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, inter_self]

lemma sum_stableSeq (m : ℝ) : Measure.sum (stableSeq m) = stableIntensity m := by
  rw [← stableIntensity_restrict_Ioi m, ← iUnion_stablePiece,
    Measure.restrict_iUnion pairwise_disjoint_stablePiece measurableSet_stablePiece]
  rfl

/-- The density `u^{-m-1}` is bounded on `[a, b]`, `0 < a`. -/
lemma rpow_le_max_of_mem_Icc {a b : ℝ} (ha : 0 < a) {u : ℝ} (hu : u ∈ Icc a b) (p : ℝ) :
    u ^ p ≤ max (a ^ p) (b ^ p) := by
  rcases le_or_gt 0 p with hp | hp
  · exact (Real.rpow_le_rpow (ha.le.trans hu.1) hu.2 hp).trans (le_max_right _ _)
  · exact ((Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hp.le) (Set.mem_Ioi.2 ha)
      (Set.mem_Ioi.2 (ha.trans_le hu.1)) hu.1).trans (le_max_left _ _)

lemma stableIntensity_Icc_lt_top (m : ℝ) {a b : ℝ} (ha : 0 < a) :
    stableIntensity m (Icc a b) < ∞ := by
  rw [stableIntensity, withDensity_apply _ measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc]
  calc ∫⁻ u in Icc a b ∩ Ioi 0, stableDensity m u ∂volume
      ≤ ∫⁻ _u in Icc a b ∩ Ioi 0, ENNReal.ofReal (max (a ^ (-m - 1)) (b ^ (-m - 1))) ∂volume := by
        refine setLIntegral_mono measurable_const fun u hu => ?_
        exact ENNReal.ofReal_le_ofReal (rpow_le_max_of_mem_Icc ha hu.1 _)
    _ = ENNReal.ofReal (max (a ^ (-m - 1)) (b ^ (-m - 1))) * volume (Icc a b ∩ Ioi 0) := by
        rw [setLIntegral_const]
    _ < ∞ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        exact (measure_mono Set.inter_subset_left).trans_lt (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)

/-- The intensity charges every interval `(a, b]`, `0 < a < b`, for every `m`. -/
lemma stableIntensity_Ioc_pos (m : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < stableIntensity m (Ioc a b) := by
  rw [stableIntensity, withDensity_apply _ measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, lintegral_pos_iff_support (measurable_stableDensity m),
    Measure.restrict_apply' (measurableSet_Ioc.inter measurableSet_Ioi)]
  have hsub : Ioc a b ⊆ Function.support (stableDensity m) ∩ (Ioc a b ∩ Ioi 0) := by
    intro u hu
    have hu0 : 0 < u := ha.trans hu.1
    refine ⟨?_, hu, hu0⟩
    simp only [Function.mem_support, stableDensity, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.rpow_pos_of_pos hu0 _
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioc]
  exact ENNReal.ofReal_pos.2 (by linarith)

/-- Every piece of the decomposition is nonzero. -/
lemma stableSeq_univ_ne_zero (m : ℝ) (n : ℕ) : stableSeq m n univ ≠ 0 := by
  rw [stableSeq, Measure.restrict_apply_univ]
  exact (lt_of_lt_of_le (stableIntensity_Ioc_pos m (a := (n : ℝ) + 1) (b := (n : ℝ) + 2)
    (by positivity) (by linarith)) (measure_mono Set.subset_union_right)).ne'

instance (m : ℝ) (n : ℕ) : IsFiniteMeasure (stableSeq m n) := by
  refine ⟨?_⟩
  rw [stableSeq, Measure.restrict_apply_univ]
  exact (measure_mono (stablePiece_subset_Icc n)).trans_lt
    (stableIntensity_Icc_lt_top m (by positivity))

end ProbabilityTheory
