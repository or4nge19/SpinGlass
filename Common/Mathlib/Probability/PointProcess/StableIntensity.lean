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

end

end ProbabilityTheory
