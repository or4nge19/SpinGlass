/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.Distributions.GaussianIntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# The Gaussian heat semigroup on functions of exponential growth

`P_s H (x) = ∫ H (x + z) dN(0, s)(z) = 𝔼 H (x + g√s)` (`g` standard Gaussian). For `H` of
exponential growth (`HasExpGrowth`):

* `HasExpGrowth.integral_comp_add_gaussianReal`: `P_s H` has exponential growth;
* `integral_comp_add_gaussianReal_zero_var`: `P_0 H = H`;
* `continuous_integral_comp_add_gaussianReal`: `(x, s) ↦ P_s H x` is jointly continuous;
* `hasDerivAt_integral_curve_gaussianReal`: **the master chain rule** for a time-dependent
  integrand along a curve `v ↦ (y v, σ v)` in the point and the variance,
  `d/dv 𝔼 H(y v + g√σ v, v) = 𝔼 (y' ∂_w H + (σ'/2) ∂²_w H + ∂_v H)(y v + g√σ v, v)`,
  by differentiation under the integral sign and Gaussian integration by parts;
* `hasDerivAt_integral_comp_add_gaussianReal_curve` (time-independent integrand),
  `hasDerivAt_integral_comp_add_gaussianReal_var` (the heat equation `∂_s P_s H = ½ P_s H''`)
  and `hasDerivWithinAt_integral_comp_add_gaussianReal_var_zero` (its one-sided form at `s = 0`);
* `contDiff_integral_comp_add_gaussianReal`, `iteratedDeriv_integral_comp_add_gaussianReal`:
  `P_s` preserves `C^n` with derivatives of exponential growth and commutes with `d/dx`;
* `hasDerivAt_iteratedDeriv_integral_comp_add_gaussianReal_var`: every `x`-derivative again
  solves the heat equation, `∂_s ∂_x^i P_s H = ½ ∂_x^{i+2} P_s H`, so mixed partials of
  `(x, s) ↦ P_s H x` need no Clairaut argument.

These are the analytic facts behind Talagrand's operators `T_{m,v}` (Vol. II, §14.7).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {H H' H'' : ℝ → ℝ}

/-! ### Scaling, shifting, and the degenerate variance -/

/-- `N(0, v)` is the image of `N(0, 1)` under `g ↦ √v g`. -/
lemma gaussianReal_map_sqrt_mul (v : ℝ≥0) :
    (gaussianReal 0 1).map (fun g => Real.sqrt v * g) = gaussianReal 0 v := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    simp [Real.sq_sqrt (NNReal.coe_nonneg v)]

/-- Scaling of Gaussian integrals: `∫ F dN(0, v) = ∫ F(√v g) dN(0, 1)`. -/
lemma integral_gaussianReal_eq_integral_sqrt_mul (v : ℝ≥0) {F : ℝ → ℝ}
    (hF : AEStronglyMeasurable F (gaussianReal 0 v)) :
    ∫ z, F z ∂gaussianReal 0 v = ∫ g, F (Real.sqrt v * g) ∂gaussianReal 0 1 := by
  rw [← gaussianReal_map_sqrt_mul v, integral_map (measurable_const_mul _).aemeasurable
    (by rw [gaussianReal_map_sqrt_mul]; exact hF)]

lemma integrable_gaussianReal_iff_sqrt_mul (v : ℝ≥0) {F : ℝ → ℝ}
    (hF : AEStronglyMeasurable F (gaussianReal 0 v)) :
    Integrable F (gaussianReal 0 v)
      ↔ Integrable (fun g => F (Real.sqrt v * g)) (gaussianReal 0 1) := by
  rw [← gaussianReal_map_sqrt_mul v, integrable_map_measure
    (by rw [gaussianReal_map_sqrt_mul]; exact hF) (measurable_const_mul _).aemeasurable]
  exact Iff.rfl

/-- `∫ H dN(x, s) = ∫ H (x + z) dN(0, s)(z)`: the Gaussian average with mean `x` as a shifted
centred average. -/
lemma integral_gaussianReal_eq_integral_comp_add (x : ℝ) (s : ℝ≥0)
    (hH : AEStronglyMeasurable H (gaussianReal x s)) :
    ∫ y, H y ∂gaussianReal x s = ∫ z, H (x + z) ∂gaussianReal 0 s := by
  have h : gaussianReal x s = (gaussianReal 0 s).map (fun z => x + z) := by
    rw [gaussianReal_map_const_add, zero_add]
  rw [h, integral_map (measurable_const_add x).aemeasurable (by rwa [← h])]

/-- `P_0 H = H`. -/
@[simp] lemma integral_comp_add_gaussianReal_zero_var (H : ℝ → ℝ) (x : ℝ) :
    ∫ z, H (x + z) ∂gaussianReal 0 0 = H x := by
  rw [gaussianReal_zero_var, integral_dirac]
  simp

/-- Gaussian averages of functions of exponential growth have exponential growth. -/
lemma HasExpGrowth.integral_comp_add_gaussianReal (hH : HasExpGrowth H) (hHm : Measurable H)
    (s : ℝ≥0) : HasExpGrowth fun x => ∫ z, H (x + z) ∂gaussianReal 0 s := by
  obtain ⟨C, c, hc, hb⟩ := hH
  have hC := HasExpGrowth.nonneg_of_bound hb
  have hint : Integrable (fun z => Real.exp (c * |z|)) (gaussianReal 0 s) :=
    integrable_exp_mul_abs_gaussianReal 0 s c
  refine ⟨C * ∫ z, Real.exp (c * |z|) ∂gaussianReal 0 s, c, hc, fun x => ?_⟩
  have hHg : HasExpGrowth H := ⟨C, c, hc, hb⟩
  have hHx : HasExpGrowth fun z => H (x + z) := hHg.comp_add_const x
  have hi : Integrable (fun z => H (x + z)) (gaussianReal 0 s) :=
    hHx.integrable_gaussianReal (hHm.comp (measurable_const_add x)).aestronglyMeasurable
  calc |∫ z, H (x + z) ∂gaussianReal 0 s|
      ≤ ∫ z, |H (x + z)| ∂gaussianReal 0 s := abs_integral_le_integral_abs
    _ ≤ ∫ z, C * Real.exp (c * |x|) * Real.exp (c * |z|) ∂gaussianReal 0 s := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _)
          ((hint.const_mul _)) (Eventually.of_forall fun z => ?_)
        calc |H (x + z)| ≤ C * Real.exp (c * |x + z|) := hb _
          _ ≤ C * Real.exp (c * (|x| + |z|)) := by
              gcongr
              exact abs_add_le _ _
          _ = C * Real.exp (c * |x|) * Real.exp (c * |z|) := by
              rw [mul_add, Real.exp_add]; ring
    _ = C * (∫ z, Real.exp (c * |z|) ∂gaussianReal 0 s) * Real.exp (c * |x|) := by
        rw [integral_const_mul]; ring

/-! ### Joint continuity in the point and the variance -/

/-- **Joint continuity of `(x, s) ↦ P_s H x`** for continuous `H` of exponential growth, the
variance being `max s 0`. -/
theorem continuous_integral_comp_add_gaussianReal (hHc : Continuous H) (hHg : HasExpGrowth H) :
    Continuous fun p : ℝ × ℝ => ∫ z, H (p.1 + z) ∂gaussianReal 0 (Real.toNNReal p.2) := by
  have hrepr : (fun p : ℝ × ℝ => ∫ z, H (p.1 + z) ∂gaussianReal 0 (Real.toNNReal p.2))
      = fun p => ∫ g, H (p.1 + Real.sqrt (Real.toNNReal p.2) * g) ∂gaussianReal 0 1 := by
    funext p
    exact integral_gaussianReal_eq_integral_sqrt_mul _
      (hHc.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  rw [hrepr, continuous_iff_continuousAt]
  intro p₀
  obtain ⟨C, c, hc, hb⟩ := hHg
  have hC := HasExpGrowth.nonneg_of_bound hb
  set r : ℝ := Real.sqrt (Real.toNNReal p₀.2 + 1) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  refine continuousAt_of_dominated (F := fun (p : ℝ × ℝ) g =>
      H (p.1 + Real.sqrt (Real.toNNReal p.2) * g))
    (bound := fun g => C * Real.exp (c * (|p₀.1| + 1)) * Real.exp (c * r * |g|)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun p => (hHc.comp (continuous_const.add
      (continuous_const.mul continuous_id))).aestronglyMeasurable
  · have h1 : ∀ᶠ p : ℝ × ℝ in 𝓝 p₀, |p.1 - p₀.1| < 1 ∧ p.2 < p₀.2 + 1 := by
      have ha : ∀ᶠ p : ℝ × ℝ in 𝓝 p₀, |p.1 - p₀.1| < 1 := by
        have := (continuous_fst.tendsto p₀).eventually (Metric.ball_mem_nhds p₀.1 one_pos)
        filter_upwards [this] with p hp
        simpa [Real.dist_eq] using hp
      have hb' : ∀ᶠ p : ℝ × ℝ in 𝓝 p₀, p.2 < p₀.2 + 1 :=
        (continuous_snd.tendsto p₀).eventually (Iio_mem_nhds (by linarith))
      exact ha.and hb'
    filter_upwards [h1] with p hp
    refine Eventually.of_forall fun g => ?_
    have hx : |p.1| ≤ |p₀.1| + 1 := by linarith [abs_sub_abs_le_abs_sub p.1 p₀.1]
    have hs : Real.sqrt (Real.toNNReal p.2) ≤ r := by
      rw [hr]
      refine Real.sqrt_le_sqrt ?_
      rw [Real.coe_toNNReal', Real.coe_toNNReal']
      have h1 := le_max_left p₀.2 0
      have h2 := le_max_right p₀.2 0
      exact max_le (by linarith [hp.2]) (by linarith)
    have hY : |p.1 + Real.sqrt (Real.toNNReal p.2) * g| ≤ (|p₀.1| + 1) + r * |g| := by
      calc |p.1 + Real.sqrt (Real.toNNReal p.2) * g|
          ≤ |p.1| + |Real.sqrt (Real.toNNReal p.2) * g| := abs_add_le _ _
        _ = |p.1| + Real.sqrt (Real.toNNReal p.2) * |g| := by
            rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        _ ≤ (|p₀.1| + 1) + r * |g| := by gcongr
    rw [Real.norm_eq_abs]
    calc |H (p.1 + Real.sqrt (Real.toNNReal p.2) * g)|
        ≤ C * Real.exp (c * |p.1 + Real.sqrt (Real.toNNReal p.2) * g|) := hb _
      _ ≤ C * Real.exp (c * ((|p₀.1| + 1) + r * |g|)) := by gcongr
      _ = C * Real.exp (c * (|p₀.1| + 1)) * Real.exp (c * r * |g|) := by
          rw [mul_add, Real.exp_add, mul_assoc c r]; ring
  · exact (integrable_exp_mul_abs_gaussianReal 0 1 (c * r)).const_mul _
  · refine Eventually.of_forall fun g => ?_
    have hcont : Continuous fun p : ℝ × ℝ => p.1 + Real.sqrt (Real.toNNReal p.2) * g :=
      continuous_fst.add ((Real.continuous_sqrt.comp (NNReal.continuous_coe.comp
        (continuous_real_toNNReal.comp continuous_snd))).mul continuous_const)
    exact (hHc.comp hcont).continuousAt

/-! ### The chain rule along a curve, with a time-dependent integrand -/

/-- **The master chain rule for Gaussian averages along a curve.** Let `H w v` be a
time-dependent integrand and `v ↦ (y v, σ v)` a curve in the point and the variance with
`σ v₀ > 0`. Suppose that, uniformly for `v` near `v₀` and every `g`, the composite
`v ↦ H (y v + g √σ v) v` is differentiable with derivative
`∂_w H · (y' + σ' g/(2√σ)) + ∂_v H`, that the partial derivatives `∂_w H (·, v)`, `∂_v H (·, v)`
have exponential growth uniformly near `v₀`, and that `∂_w H (·, v₀)` has a continuous derivative
`∂²_w H (·, v₀)` of exponential growth. Then

`d/dv 𝔼 H (y v + g √σ v, v) |_{v₀} = 𝔼 (y' ∂_w H + (σ'/2) ∂²_w H + ∂_v H) (y v₀ + g √σ v₀, v₀)`,

Gaussian integration by parts (Stein's lemma) having turned the factor `g/(2√σ)` into `½ ∂_w`. -/
theorem hasDerivAt_integral_curve_gaussianReal {H Hw Hww Hv : ℝ → ℝ → ℝ} {y σ y' σ' : ℝ → ℝ}
    {v₀ : ℝ} (hσ₀ : 0 < σ v₀)
    (hy : ∀ᶠ v in 𝓝 v₀, HasDerivAt y (y' v) v) (hy'c : ContinuousAt y' v₀)
    (hσ : ∀ᶠ v in 𝓝 v₀, HasDerivAt σ (σ' v) v) (hσ'c : ContinuousAt σ' v₀)
    (hΦ : ∀ᶠ v in 𝓝 v₀, ∀ g, HasDerivAt (fun v => H (y v + Real.sqrt (σ v) * g) v)
      (Hw (y v + Real.sqrt (σ v) * g) v * (y' v + σ' v / (2 * Real.sqrt (σ v)) * g)
        + Hv (y v + Real.sqrt (σ v) * g) v) v)
    (hHm : ∀ v, Measurable fun w => H w v) (hHwm : Measurable fun w => Hw w v₀)
    (hHvm : Measurable fun w => Hv w v₀)
    (hHwb : ∃ C c : ℝ, 0 ≤ c ∧ ∀ᶠ v in 𝓝 v₀, ∀ w, |Hw w v| ≤ C * Real.exp (c * |w|))
    (hHvb : ∃ C c : ℝ, 0 ≤ c ∧ ∀ᶠ v in 𝓝 v₀, ∀ w, |Hv w v| ≤ C * Real.exp (c * |w|))
    (hint : Integrable (fun g => H (y v₀ + Real.sqrt (σ v₀) * g) v₀) (gaussianReal 0 1))
    (hHw : ∀ w, HasDerivAt (fun w => Hw w v₀) (Hww w v₀) w)
    (hHwwc : Continuous fun w => Hww w v₀) (hHwwg : HasExpGrowth fun w => Hww w v₀) :
    HasDerivAt (fun v => ∫ g, H (y v + Real.sqrt (σ v) * g) v ∂gaussianReal 0 1)
      (∫ g, y' v₀ * Hw (y v₀ + Real.sqrt (σ v₀) * g) v₀
        + σ' v₀ / 2 * Hww (y v₀ + Real.sqrt (σ v₀) * g) v₀
        + Hv (y v₀ + Real.sqrt (σ v₀) * g) v₀ ∂gaussianReal 0 1) v₀ := by
  set x₀ := y v₀ with hx₀
  set s₀ := σ v₀ with hs₀def
  have hyc : ContinuousAt y v₀ := by
    obtain ⟨t, ht, hyt⟩ := hy.exists_mem
    exact (hyt v₀ (mem_of_mem_nhds ht)).continuousAt
  have hσc : ContinuousAt σ v₀ := by
    obtain ⟨t, ht, hσt⟩ := hσ.exists_mem
    exact (hσt v₀ (mem_of_mem_nhds ht)).continuousAt
  obtain ⟨C₁, c₁, hc₁, hb₁⟩ := hHwb
  obtain ⟨C₂, c₂, hc₂, hb₂⟩ := hHvb
  have hC₁ : 0 ≤ C₁ := HasExpGrowth.nonneg_of_bound hb₁.self_of_nhds
  have hC₂ : 0 ≤ C₂ := HasExpGrowth.nonneg_of_bound hb₂.self_of_nhds
  set r : ℝ := Real.sqrt (3 * s₀ / 2) with hr
  set k : ℝ := 1 / (2 * Real.sqrt (s₀ / 2)) with hk
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hk0 : 0 ≤ k := by positivity
  set Y₀ : ℝ := |x₀| + 1 with hY₀
  set Y₁ : ℝ := |y' v₀| + 1 with hY₁
  set S₁ : ℝ := |σ' v₀| + 1 with hS₁
  set c : ℝ := (c₁ + c₂) * r + 1 with hc
  set K : ℝ := C₁ * Real.exp (c₁ * Y₀) * (Y₁ + S₁ * k) + C₂ * Real.exp (c₂ * Y₀) with hK
  have hc0 : 0 ≤ c := by positivity
  -- the good neighbourhood
  have hs : ∀ᶠ v in 𝓝 v₀, (∀ g, HasDerivAt (fun v => H (y v + Real.sqrt (σ v) * g) v)
      (Hw (y v + Real.sqrt (σ v) * g) v * (y' v + σ' v / (2 * Real.sqrt (σ v)) * g)
        + Hv (y v + Real.sqrt (σ v) * g) v) v)
      ∧ (s₀ / 2 < σ v ∧ σ v < 3 * s₀ / 2) ∧ |y v - x₀| < 1 ∧ |y' v| ≤ Y₁ ∧ |σ' v| ≤ S₁
      ∧ (∀ w, |Hw w v| ≤ C₁ * Real.exp (c₁ * |w|))
      ∧ (∀ w, |Hv w v| ≤ C₂ * Real.exp (c₂ * |w|)) := by
    have h1 : ∀ᶠ v in 𝓝 v₀, s₀ / 2 < σ v ∧ σ v < 3 * s₀ / 2 :=
      hσc.eventually (Ioo_mem_nhds (by linarith) (by linarith))
    have h2 : ∀ᶠ v in 𝓝 v₀, |y v - x₀| < 1 := by
      have := hyc.eventually (Metric.ball_mem_nhds x₀ one_pos)
      filter_upwards [this] with v hv
      simpa [Real.dist_eq] using hv
    have h3 : ∀ᶠ v in 𝓝 v₀, |y' v| ≤ Y₁ := by
      have := hy'c.eventually (Metric.ball_mem_nhds (y' v₀) one_pos)
      filter_upwards [this] with v hv
      rw [Real.dist_eq] at hv
      rw [hY₁]
      linarith [abs_sub_abs_le_abs_sub (y' v) (y' v₀)]
    have h4 : ∀ᶠ v in 𝓝 v₀, |σ' v| ≤ S₁ := by
      have := hσ'c.eventually (Metric.ball_mem_nhds (σ' v₀) one_pos)
      filter_upwards [this] with v hv
      rw [Real.dist_eq] at hv
      rw [hS₁]
      linarith [abs_sub_abs_le_abs_sub (σ' v) (σ' v₀)]
    filter_upwards [hΦ, h1, h2, h3, h4, hb₁, hb₂] with v a b c d e f g
    exact ⟨a, b, c, d, e, f, g⟩
  obtain ⟨t, ht, hts⟩ := hs.exists_mem
  have hmeasF : ∀ v : ℝ, AEStronglyMeasurable
      (fun g => H (y v + Real.sqrt (σ v) * g) v) (gaussianReal 0 1) := fun v =>
    ((hHm v).comp (measurable_const.add (measurable_const_mul _))).aestronglyMeasurable
  -- differentiation under the integral sign
  have hdJ : HasDerivAt (fun v => ∫ g, H (y v + Real.sqrt (σ v) * g) v ∂gaussianReal 0 1)
      (∫ g, Hw (x₀ + Real.sqrt s₀ * g) v₀ * (y' v₀ + σ' v₀ / (2 * Real.sqrt s₀) * g)
        + Hv (x₀ + Real.sqrt s₀ * g) v₀ ∂gaussianReal 0 1) v₀ := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gaussianReal 0 1)
      (F := fun v g => H (y v + Real.sqrt (σ v) * g) v)
      (F' := fun v g => Hw (y v + Real.sqrt (σ v) * g) v
        * (y' v + σ' v / (2 * Real.sqrt (σ v)) * g) + Hv (y v + Real.sqrt (σ v) * g) v)
      (bound := fun g => K * Real.exp (c * |g|)) ht
      (Eventually.of_forall hmeasF) hint ?_ ?_ ?_ ?_).2
    · exact (((hHwm.comp (measurable_const.add (measurable_const_mul _))).mul
        (measurable_const.add (measurable_const.mul measurable_id))).add
        (hHvm.comp (measurable_const.add (measurable_const_mul _)))).aestronglyMeasurable
    · -- the uniform bound
      refine Eventually.of_forall fun g v hv => ?_
      obtain ⟨_, ⟨hs1, hs2⟩, hyv, hy'v, hσ'v, hbw, hbv⟩ := hts v hv
      have hspos : 0 < σ v := by linarith
      have hsq_le : Real.sqrt (σ v) ≤ r := Real.sqrt_le_sqrt hs2.le
      have hinv_le : 1 / (2 * Real.sqrt (σ v)) ≤ k := by
        rw [hk]
        refine one_div_le_one_div_of_le (by positivity) ?_
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs1.le) two_pos.le
      have hyv' : |y v| ≤ Y₀ := by
        rw [hY₀]
        linarith [abs_sub_abs_le_abs_sub (y v) x₀]
      have hY : |y v + Real.sqrt (σ v) * g| ≤ Y₀ + r * |g| := by
        calc |y v + Real.sqrt (σ v) * g| ≤ |y v| + |Real.sqrt (σ v) * g| := abs_add_le _ _
          _ = |y v| + Real.sqrt (σ v) * |g| := by
              rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          _ ≤ Y₀ + r * |g| := by gcongr
      have hg_le : |g| ≤ Real.exp |g| := by linarith [Real.add_one_le_exp |g|]
      have e1 : |Hw (y v + Real.sqrt (σ v) * g) v| ≤ C₁ * Real.exp (c₁ * (Y₀ + r * |g|)) :=
        (hbw _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
          (mul_le_mul_of_nonneg_left hY hc₁)) hC₁)
      have e2 : |Hv (y v + Real.sqrt (σ v) * g) v| ≤ C₂ * Real.exp (c₂ * (Y₀ + r * |g|)) :=
        (hbv _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
          (mul_le_mul_of_nonneg_left hY hc₂)) hC₂)
      have e3 : |y' v + σ' v / (2 * Real.sqrt (σ v)) * g| ≤ (Y₁ + S₁ * k) * Real.exp |g| := by
        have h1 : |σ' v / (2 * Real.sqrt (σ v)) * g| ≤ S₁ * k * |g| := by
          rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.sqrt (σ v))]
          calc |σ' v| / (2 * Real.sqrt (σ v)) * |g|
              = |σ' v| * (1 / (2 * Real.sqrt (σ v))) * |g| := by ring
            _ ≤ S₁ * k * |g| := by gcongr
        have h2 : 1 ≤ Real.exp |g| := Real.one_le_exp (abs_nonneg g)
        calc |y' v + σ' v / (2 * Real.sqrt (σ v)) * g|
            ≤ |y' v| + |σ' v / (2 * Real.sqrt (σ v)) * g| := abs_add_le _ _
          _ ≤ Y₁ + S₁ * k * |g| := add_le_add hy'v h1
          _ ≤ Y₁ * Real.exp |g| + S₁ * k * Real.exp |g| := by
              have i1 : Y₁ ≤ Y₁ * Real.exp |g| := le_mul_of_one_le_right (by positivity) h2
              have i2 : S₁ * k * |g| ≤ S₁ * k * Real.exp |g| :=
                mul_le_mul_of_nonneg_left hg_le (by positivity)
              linarith
          _ = (Y₁ + S₁ * k) * Real.exp |g| := by ring
      have hexp1 : Real.exp (c₁ * (Y₀ + r * |g|)) * Real.exp |g|
          ≤ Real.exp (c₁ * Y₀) * Real.exp (c * |g|) := by
        rw [← Real.exp_add, ← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        rw [hc]
        nlinarith [abs_nonneg g, mul_nonneg (mul_nonneg hc₂ hr0) (abs_nonneg g)]
      have hexp2 : Real.exp (c₂ * (Y₀ + r * |g|)) ≤ Real.exp (c₂ * Y₀) * Real.exp (c * |g|) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        rw [hc]
        nlinarith [abs_nonneg g, mul_nonneg (mul_nonneg hc₁ hr0) (abs_nonneg g)]
      rw [Real.norm_eq_abs]
      calc |Hw (y v + Real.sqrt (σ v) * g) v * (y' v + σ' v / (2 * Real.sqrt (σ v)) * g)
            + Hv (y v + Real.sqrt (σ v) * g) v|
          ≤ |Hw (y v + Real.sqrt (σ v) * g) v| * |y' v + σ' v / (2 * Real.sqrt (σ v)) * g|
            + |Hv (y v + Real.sqrt (σ v) * g) v| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ C₁ * Real.exp (c₁ * (Y₀ + r * |g|)) * ((Y₁ + S₁ * k) * Real.exp |g|)
            + C₂ * Real.exp (c₂ * (Y₀ + r * |g|)) := by
            gcongr
        _ = C₁ * (Y₁ + S₁ * k) * (Real.exp (c₁ * (Y₀ + r * |g|)) * Real.exp |g|)
            + C₂ * Real.exp (c₂ * (Y₀ + r * |g|)) := by ring
        _ ≤ C₁ * (Y₁ + S₁ * k) * (Real.exp (c₁ * Y₀) * Real.exp (c * |g|))
            + C₂ * (Real.exp (c₂ * Y₀) * Real.exp (c * |g|)) := by
            gcongr
        _ = K * Real.exp (c * |g|) := by rw [hK]; ring
    · exact (integrable_exp_mul_abs_gaussianReal 0 1 c).const_mul K
    · exact Eventually.of_forall fun g v hv => (hts v hv).1 g
  -- Stein's lemma turns the factor `g` into a derivative
  have hΦ' : ∀ g, HasDerivAt (fun g => Hw (x₀ + Real.sqrt s₀ * g) v₀)
      (Real.sqrt s₀ * Hww (x₀ + Real.sqrt s₀ * g) v₀) g := by
    intro g
    have h1 : HasDerivAt (fun g => x₀ + Real.sqrt s₀ * g) (Real.sqrt s₀) g := by
      have := ((hasDerivAt_id g).const_mul (Real.sqrt s₀)).const_add x₀
      simpa using this
    exact ((hHw _).comp g h1).congr_deriv (by ring)
  have hHwg : HasExpGrowth fun w => Hw w v₀ := ⟨C₁, c₁, hc₁, hb₁.self_of_nhds⟩
  have hHvg : HasExpGrowth fun w => Hv w v₀ := ⟨C₂, c₂, hc₂, hb₂.self_of_nhds⟩
  have hHwg' : HasExpGrowth fun g => Hw (x₀ + Real.sqrt s₀ * g) v₀ :=
    (hHwg.comp_add_const x₀).comp_const_mul (Real.sqrt s₀)
  have hHvg' : HasExpGrowth fun g => Hv (x₀ + Real.sqrt s₀ * g) v₀ :=
    (hHvg.comp_add_const x₀).comp_const_mul (Real.sqrt s₀)
  have hHwwg' : HasExpGrowth fun g => Real.sqrt s₀ * Hww (x₀ + Real.sqrt s₀ * g) v₀ :=
    ((hHwwg.comp_add_const x₀).comp_const_mul (Real.sqrt s₀)).const_mul _
  have hHwwc' : Continuous fun g => Real.sqrt s₀ * Hww (x₀ + Real.sqrt s₀ * g) v₀ :=
    continuous_const.mul (hHwwc.comp (continuous_const.add (continuous_const.mul continuous_id)))
  have hstein := stein_lemma_gaussianReal_of_expGrowth' (v := 1) hΦ' hHwwc' hHwg' hHwwg'
  simp only [NNReal.coe_one, one_mul] at hstein
  -- assemble
  refine hdJ.congr_deriv ?_
  have hi1 : Integrable (fun g => Hw (x₀ + Real.sqrt s₀ * g) v₀) (gaussianReal 0 1) :=
    hHwg'.integrable_gaussianReal
      (hHwm.comp (measurable_const.add (measurable_const_mul _))).aestronglyMeasurable
  have hi2 : Integrable (fun g => g * Hw (x₀ + Real.sqrt s₀ * g) v₀) (gaussianReal 0 1) := by
    have hg : HasExpGrowth fun g : ℝ => g :=
      ⟨1, 1, zero_le_one, fun g => by
        rw [one_mul, one_mul]
        linarith [Real.add_one_le_exp |g|]⟩
    exact (hg.mul hHwg').integrable_gaussianReal (measurable_id.mul
      (hHwm.comp (measurable_const.add (measurable_const_mul _)))).aestronglyMeasurable
  have hi3 : Integrable (fun g => Hv (x₀ + Real.sqrt s₀ * g) v₀) (gaussianReal 0 1) :=
    hHvg'.integrable_gaussianReal
      (hHvm.comp (measurable_const.add (measurable_const_mul _))).aestronglyMeasurable
  have hi4 : Integrable (fun g => Real.sqrt s₀ * Hww (x₀ + Real.sqrt s₀ * g) v₀)
      (gaussianReal 0 1) :=
    hHwwg'.integrable_gaussianReal hHwwc'.aestronglyMeasurable
  have h1 : Integrable (fun g => y' v₀ * Hw (x₀ + Real.sqrt s₀ * g) v₀) (gaussianReal 0 1) :=
    hi1.const_mul _
  have h2 : Integrable (fun g => σ' v₀ / (2 * Real.sqrt s₀) * (g * Hw (x₀ + Real.sqrt s₀ * g) v₀))
      (gaussianReal 0 1) := hi2.const_mul _
  have h4 : Integrable (fun g => σ' v₀ / (2 * Real.sqrt s₀)
      * (Real.sqrt s₀ * Hww (x₀ + Real.sqrt s₀ * g) v₀)) (gaussianReal 0 1) := hi4.const_mul _
  have h12 : Integrable (fun g => y' v₀ * Hw (x₀ + Real.sqrt s₀ * g) v₀
      + σ' v₀ / (2 * Real.sqrt s₀) * (g * Hw (x₀ + Real.sqrt s₀ * g) v₀)) (gaussianReal 0 1) :=
    h1.add h2
  have h14 : Integrable (fun g => y' v₀ * Hw (x₀ + Real.sqrt s₀ * g) v₀
      + σ' v₀ / (2 * Real.sqrt s₀) * (Real.sqrt s₀ * Hww (x₀ + Real.sqrt s₀ * g) v₀))
      (gaussianReal 0 1) := h1.add h4
  have e1 : (∫ g, Hw (x₀ + Real.sqrt s₀ * g) v₀ * (y' v₀ + σ' v₀ / (2 * Real.sqrt s₀) * g)
      + Hv (x₀ + Real.sqrt s₀ * g) v₀ ∂gaussianReal 0 1)
      = y' v₀ * (∫ g, Hw (x₀ + Real.sqrt s₀ * g) v₀ ∂gaussianReal 0 1)
        + (σ' v₀ / (2 * Real.sqrt s₀))
          * (∫ g, g * Hw (x₀ + Real.sqrt s₀ * g) v₀ ∂gaussianReal 0 1)
        + ∫ g, Hv (x₀ + Real.sqrt s₀ * g) v₀ ∂gaussianReal 0 1 := by
    calc (∫ g, Hw (x₀ + Real.sqrt s₀ * g) v₀ * (y' v₀ + σ' v₀ / (2 * Real.sqrt s₀) * g)
          + Hv (x₀ + Real.sqrt s₀ * g) v₀ ∂gaussianReal 0 1)
        = ∫ g, (y' v₀ * Hw (x₀ + Real.sqrt s₀ * g) v₀
            + σ' v₀ / (2 * Real.sqrt s₀) * (g * Hw (x₀ + Real.sqrt s₀ * g) v₀))
            + Hv (x₀ + Real.sqrt s₀ * g) v₀ ∂gaussianReal 0 1 :=
          integral_congr_ae (Eventually.of_forall fun g => by ring)
      _ = _ := by
          rw [integral_add h12 hi3, integral_add h1 h2, integral_const_mul, integral_const_mul]
  have e2 : (∫ g, y' v₀ * Hw (x₀ + Real.sqrt s₀ * g) v₀
      + σ' v₀ / 2 * Hww (x₀ + Real.sqrt s₀ * g) v₀
      + Hv (x₀ + Real.sqrt s₀ * g) v₀ ∂gaussianReal 0 1)
      = y' v₀ * (∫ g, Hw (x₀ + Real.sqrt s₀ * g) v₀ ∂gaussianReal 0 1)
        + (σ' v₀ / (2 * Real.sqrt s₀))
          * (∫ g, Real.sqrt s₀ * Hww (x₀ + Real.sqrt s₀ * g) v₀ ∂gaussianReal 0 1)
        + ∫ g, Hv (x₀ + Real.sqrt s₀ * g) v₀ ∂gaussianReal 0 1 := by
    have hsqrt : Real.sqrt s₀ ≠ 0 := (Real.sqrt_pos.2 hσ₀).ne'
    calc (∫ g, y' v₀ * Hw (x₀ + Real.sqrt s₀ * g) v₀
          + σ' v₀ / 2 * Hww (x₀ + Real.sqrt s₀ * g) v₀
          + Hv (x₀ + Real.sqrt s₀ * g) v₀ ∂gaussianReal 0 1)
        = ∫ g, (y' v₀ * Hw (x₀ + Real.sqrt s₀ * g) v₀
            + σ' v₀ / (2 * Real.sqrt s₀) * (Real.sqrt s₀ * Hww (x₀ + Real.sqrt s₀ * g) v₀))
            + Hv (x₀ + Real.sqrt s₀ * g) v₀ ∂gaussianReal 0 1 :=
          integral_congr_ae (Eventually.of_forall fun g => by field_simp)
      _ = _ := by
          rw [integral_add h14 hi3, integral_add h1 h4, integral_const_mul, integral_const_mul]
  rw [e1, e2, hstein]

/-! ### The heat equation -/

section TimeIndependent

variable (hH : ∀ w, HasDerivAt H (H' w) w) (hH' : ∀ w, HasDerivAt H' (H'' w) w)
  (hHg : HasExpGrowth H) (hH'g : HasExpGrowth H') (hH''g : HasExpGrowth H'')
  (hH''c : Continuous H'')
include hH hH' hHg hH'g hH''g hH''c

/-- **The chain rule for `(x, s) ↦ P_s H x` along a curve** `v ↦ (y v, σ v)` with `σ v₀ > 0`:
`d/dv P_{σ v} H (y v) = y' P_σ H' (y) + (σ'/2) P_σ H'' (y)`. -/
theorem hasDerivAt_integral_comp_add_gaussianReal_curve {y σ y' σ' : ℝ → ℝ} {v₀ : ℝ}
    (hy : ∀ᶠ v in 𝓝 v₀, HasDerivAt y (y' v) v) (hy'c : ContinuousAt y' v₀)
    (hσ : ∀ᶠ v in 𝓝 v₀, HasDerivAt σ (σ' v) v) (hσ'c : ContinuousAt σ' v₀) (hσ₀ : 0 < σ v₀) :
    HasDerivAt (fun v => ∫ z, H (y v + z) ∂gaussianReal 0 (Real.toNNReal (σ v)))
      (y' v₀ * ∫ z, H' (y v₀ + z) ∂gaussianReal 0 (Real.toNNReal (σ v₀))
        + σ' v₀ / 2 * ∫ z, H'' (y v₀ + z) ∂gaussianReal 0 (Real.toNNReal (σ v₀))) v₀ := by
  have hHc : Continuous H := continuous_iff_continuousAt.2 fun w => (hH w).continuousAt
  have hH'c : Continuous H' := continuous_iff_continuousAt.2 fun w => (hH' w).continuousAt
  have hσc : ContinuousAt σ v₀ := by
    obtain ⟨t, ht, hσt⟩ := hσ.exists_mem
    exact (hσt v₀ (mem_of_mem_nhds ht)).continuousAt
  have hs₀' : (Real.toNNReal (σ v₀) : ℝ) = σ v₀ := Real.coe_toNNReal _ hσ₀.le
  have hfun : ∀ᶠ v in 𝓝 v₀, (∫ g, H (y v + Real.sqrt (σ v) * g) ∂gaussianReal 0 1)
      = ∫ z, H (y v + z) ∂gaussianReal 0 (Real.toNNReal (σ v)) := by
    filter_upwards [hσc.eventually (lt_mem_nhds hσ₀)] with v hv
    have hm : AEStronglyMeasurable (fun z => H (y v + z)) (gaussianReal 0 (Real.toNNReal (σ v))) :=
      (hHc.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    rw [integral_gaussianReal_eq_integral_sqrt_mul _ hm, Real.coe_toNNReal _ hv.le]
  have hHwb : ∃ C c : ℝ, 0 ≤ c ∧ ∀ᶠ v in 𝓝 v₀, ∀ w, |H' w| ≤ C * Real.exp (c * |w|) := by
    obtain ⟨C, c, hc, hb⟩ := hH'g
    exact ⟨C, c, hc, Eventually.of_forall fun _ => hb⟩
  have hmain := hasDerivAt_integral_curve_gaussianReal (H := fun w _ => H w)
    (Hw := fun w _ => H' w) (Hww := fun w _ => H'' w) (Hv := fun _ _ => 0) hσ₀ hy hy'c hσ hσ'c
    ?_ (fun _ => hHc.measurable) hH'c.measurable measurable_const hHwb
    ⟨0, 0, le_rfl, Eventually.of_forall fun _ w => by simp⟩ ?_ hH' hH''c hH''g
  · refine (hmain.congr_of_eventuallyEq (hfun.mono fun v hv => hv.symm)).congr_deriv ?_
    have hscale : Continuous fun g : ℝ => y v₀ + Real.sqrt (σ v₀) * g :=
      continuous_const.add (continuous_const.mul continuous_id)
    have hi1 : Integrable (fun g => H' (y v₀ + Real.sqrt (σ v₀) * g)) (gaussianReal 0 1) :=
      ((hH'g.comp_add_const _).comp_const_mul _).integrable_gaussianReal
        (hH'c.comp hscale).aestronglyMeasurable
    have hi2 : Integrable (fun g => H'' (y v₀ + Real.sqrt (σ v₀) * g)) (gaussianReal 0 1) :=
      ((hH''g.comp_add_const _).comp_const_mul _).integrable_gaussianReal
        (hH''c.comp hscale).aestronglyMeasurable
    have hm1 : AEStronglyMeasurable (fun z => H' (y v₀ + z))
        (gaussianReal 0 (Real.toNNReal (σ v₀))) :=
      (hH'c.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (fun z => H'' (y v₀ + z))
        (gaussianReal 0 (Real.toNNReal (σ v₀))) :=
      (hH''c.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    have e1 : (∫ z, H' (y v₀ + z) ∂gaussianReal 0 (Real.toNNReal (σ v₀)))
        = ∫ g, H' (y v₀ + Real.sqrt (σ v₀) * g) ∂gaussianReal 0 1 := by
      rw [integral_gaussianReal_eq_integral_sqrt_mul _ hm1, hs₀']
    have e2 : (∫ z, H'' (y v₀ + z) ∂gaussianReal 0 (Real.toNNReal (σ v₀)))
        = ∫ g, H'' (y v₀ + Real.sqrt (σ v₀) * g) ∂gaussianReal 0 1 := by
      rw [integral_gaussianReal_eq_integral_sqrt_mul _ hm2, hs₀']
    have hi1' : Integrable (fun g => y' v₀ * H' (y v₀ + Real.sqrt (σ v₀) * g))
        (gaussianReal 0 1) := hi1.const_mul _
    have hi2' : Integrable (fun g => σ' v₀ / 2 * H'' (y v₀ + Real.sqrt (σ v₀) * g))
        (gaussianReal 0 1) := hi2.const_mul _
    simp only [add_zero]
    rw [integral_add hi1' hi2', integral_const_mul, integral_const_mul, e1, e2]
  · filter_upwards [hy, hσ, hσc.eventually (lt_mem_nhds hσ₀)] with v hyv hσv hpos
    intro g
    have hsq : HasDerivAt (fun v => Real.sqrt (σ v)) (1 / (2 * Real.sqrt (σ v)) * σ' v) v :=
      (Real.hasDerivAt_sqrt hpos.ne').comp v hσv
    have h1 : HasDerivAt (fun v => y v + Real.sqrt (σ v) * g)
        (y' v + 1 / (2 * Real.sqrt (σ v)) * σ' v * g) v := hyv.add (hsq.mul_const g)
    exact ((hH _).comp v h1).congr_deriv (by ring)
  · exact ((hHg.comp_add_const _).comp_const_mul _).integrable_gaussianReal
      (hHc.comp (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable

/-- **The heat equation**: `∂_s P_s H (x) = ½ P_s H'' (x)` for `s > 0`. -/
theorem hasDerivAt_integral_comp_add_gaussianReal_var {s₀ : ℝ} (hs₀ : 0 < s₀) (x : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ z, H (x + z) ∂gaussianReal 0 (Real.toNNReal s))
      ((1 / 2) * ∫ z, H'' (x + z) ∂gaussianReal 0 (Real.toNNReal s₀)) s₀ := by
  have h := hasDerivAt_integral_comp_add_gaussianReal_curve hH hH' hHg hH'g hH''g hH''c
    (y := fun _ => x) (σ := fun s => s) (y' := fun _ => 0) (σ' := fun _ => 1) (v₀ := s₀)
    (Eventually.of_forall fun v => hasDerivAt_const v x) continuousAt_const
    (Eventually.of_forall fun v => hasDerivAt_id v) continuousAt_const hs₀
  refine h.congr_deriv ?_
  ring

/-- **The heat equation at `s = 0`**, one-sided: `∂_s⁺ P_s H (x) |_{s=0} = ½ H'' x`. -/
theorem hasDerivWithinAt_integral_comp_add_gaussianReal_var_zero (x : ℝ) :
    HasDerivWithinAt (fun s : ℝ => ∫ z, H (x + z) ∂gaussianReal 0 (Real.toNNReal s))
      ((1 / 2) * H'' x) (Ici 0) 0 := by
  have hHc : Continuous H := continuous_iff_continuousAt.2 fun w => (hH w).continuousAt
  have hfc : Continuous fun s : ℝ => ∫ z, H (x + z) ∂gaussianReal 0 (Real.toNNReal s) :=
    (continuous_integral_comp_add_gaussianReal hHc hHg).comp
      (continuous_const.prodMk continuous_id)
  have hdiff : DifferentiableOn ℝ
      (fun s : ℝ => ∫ z, H (x + z) ∂gaussianReal 0 (Real.toNNReal s)) (Ioi 0) := fun s hs =>
    (hasDerivAt_integral_comp_add_gaussianReal_var hH hH' hHg hH'g hH''g hH''c hs
      x).differentiableAt.differentiableWithinAt
  have hderiv : ∀ s ∈ Ioi (0 : ℝ),
      deriv (fun s : ℝ => ∫ z, H (x + z) ∂gaussianReal 0 (Real.toNNReal s)) s
        = (1 / 2) * ∫ z, H'' (x + z) ∂gaussianReal 0 (Real.toNNReal s) := fun s hs =>
    (hasDerivAt_integral_comp_add_gaussianReal_var hH hH' hHg hH'g hH''g hH''c hs x).deriv
  refine hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hfc.continuousAt.continuousWithinAt
    self_mem_nhdsWithin ?_
  have hc2 : Continuous fun s : ℝ =>
      (1 / 2) * ∫ z, H'' (x + z) ∂gaussianReal 0 (Real.toNNReal s) :=
    continuous_const.mul ((continuous_integral_comp_add_gaussianReal hH''c hH''g).comp
      (continuous_const.prodMk continuous_id))
  have hlim : Tendsto (fun s : ℝ => (1 / 2) * ∫ z, H'' (x + z) ∂gaussianReal 0 (Real.toNNReal s))
      (𝓝[>] 0) (𝓝 ((1 / 2) * H'' x)) := by
    have := (hc2.continuousAt (x := 0)).tendsto
    rw [Real.toNNReal_zero, integral_comp_add_gaussianReal_zero_var] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact hlim.congr' (eventuallyEq_nhdsWithin_of_eqOn fun s hs => (hderiv s hs).symm)

end TimeIndependent

/-! ### Smoothness in the point -/

/-- `P_s` preserves `C^n` with derivatives of exponential growth and commutes with `d/dx`
(auxiliary form, by induction on `n`). -/
theorem contDiff_integral_comp_add_gaussianReal_aux (n : ℕ) :
    ∀ {H : ℝ → ℝ}, ContDiff ℝ n H → (∀ i ≤ n, HasExpGrowth (iteratedDeriv i H)) → ∀ s : ℝ≥0,
      ContDiff ℝ n (fun x => ∫ z, H (x + z) ∂gaussianReal 0 s)
        ∧ ∀ i ≤ n, iteratedDeriv i (fun x => ∫ z, H (x + z) ∂gaussianReal 0 s)
          = fun x => ∫ z, iteratedDeriv i H (x + z) ∂gaussianReal 0 s := by
  induction n with
  | zero =>
    intro H hH hg s
    have hHc : Continuous H := hH.continuous
    have hg0 : HasExpGrowth H := by simpa using hg 0 le_rfl
    refine ⟨contDiff_zero.2 ?_, fun i hi => ?_⟩
    · have := (continuous_integral_comp_add_gaussianReal hHc hg0).comp
        (continuous_id.prodMk (continuous_const (y := (s : ℝ))))
      simpa [Function.comp_def, Real.toNNReal_coe] using this
    · obtain rfl : i = 0 := Nat.le_zero.1 hi
      simp [iteratedDeriv_zero]
  | succ n ih =>
    intro H hH hg s
    have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by norm_cast
    rw [hcast, contDiff_succ_iff_deriv] at hH
    obtain ⟨hdiff, -, hderivC⟩ := hH
    have hH'c : Continuous (deriv H) := hderivC.continuous
    have hg0 : HasExpGrowth H := by simpa using hg 0 (Nat.zero_le _)
    have hg1 : HasExpGrowth (deriv H) := by simpa [iteratedDeriv_one] using hg 1 (by omega)
    have hg' : ∀ i ≤ n, HasExpGrowth (iteratedDeriv i (deriv H)) := fun i hi => by
      rw [← iteratedDeriv_succ']
      exact hg (i + 1) (by omega)
    obtain ⟨ih1, ih2⟩ := ih hderivC hg' s
    have hd : ∀ x, HasDerivAt (fun x => ∫ z, H (x + z) ∂gaussianReal 0 s)
        (∫ z, deriv H (x + z) ∂gaussianReal 0 s) x := fun x =>
      hasDerivAt_integral_comp_add_gaussianReal (fun y => (hdiff y).hasDerivAt) hg0 hg1
        hH'c.measurable 0 s x
    have hderiv_eq : deriv (fun x => ∫ z, H (x + z) ∂gaussianReal 0 s)
        = fun x => ∫ z, deriv H (x + z) ∂gaussianReal 0 s := funext fun x => (hd x).deriv
    refine ⟨?_, fun i hi => ?_⟩
    · rw [hcast, contDiff_succ_iff_deriv]
      exact ⟨fun x => (hd x).differentiableAt, fun h => absurd h (by simp),
        by rw [hderiv_eq]; exact ih1⟩
    · rcases i with _ | i
      · simp [iteratedDeriv_zero]
      · rw [iteratedDeriv_succ', hderiv_eq, ih2 i (by omega), iteratedDeriv_succ']

/-- **`P_s` preserves `C^n`** when the derivatives of `H` up to order `n` have exponential
growth. -/
theorem contDiff_integral_comp_add_gaussianReal {n : ℕ} (hH : ContDiff ℝ n H)
    (hg : ∀ i ≤ n, HasExpGrowth (iteratedDeriv i H)) (s : ℝ≥0) :
    ContDiff ℝ n (fun x => ∫ z, H (x + z) ∂gaussianReal 0 s) :=
  (contDiff_integral_comp_add_gaussianReal_aux n hH hg s).1

/-- **`P_s` commutes with `d^i/dx^i`**, `i ≤ n`. -/
theorem iteratedDeriv_integral_comp_add_gaussianReal {n : ℕ} (hH : ContDiff ℝ n H)
    (hg : ∀ i ≤ n, HasExpGrowth (iteratedDeriv i H)) (s : ℝ≥0) {i : ℕ} (hi : i ≤ n) :
    iteratedDeriv i (fun x => ∫ z, H (x + z) ∂gaussianReal 0 s)
      = fun x => ∫ z, iteratedDeriv i H (x + z) ∂gaussianReal 0 s :=
  (contDiff_integral_comp_add_gaussianReal_aux n hH hg s).2 i hi

/-! ### The heat equation for the iterated `x`-derivatives -/

/-- **Every `x`-derivative of the heat flow again solves the heat equation**:
`∂_s (∂_x^i P_s H) = ½ ∂_x^{i+2} P_s H` for `s > 0`. In particular the mixed partial derivatives
of `(x, s) ↦ P_s H x` need no Clairaut argument: differentiating in `s` is differentiating twice
in `x`. -/
theorem hasDerivAt_iteratedDeriv_integral_comp_add_gaussianReal_var {n : ℕ}
    (hH : ContDiff ℝ n H) (hg : ∀ i ≤ n, HasExpGrowth (iteratedDeriv i H))
    {i : ℕ} (hi : i + 2 ≤ n) {s₀ : ℝ} (hs₀ : 0 < s₀) (x : ℝ) :
    HasDerivAt (fun s : ℝ => iteratedDeriv i
        (fun x => ∫ z, H (x + z) ∂gaussianReal 0 (Real.toNNReal s)) x)
      ((1 / 2) * iteratedDeriv (i + 2)
        (fun x => ∫ z, H (x + z) ∂gaussianReal 0 (Real.toNNReal s₀)) x) s₀ := by
  have hstep : ∀ j, j < n → ∀ w, HasDerivAt (iteratedDeriv j H) (iteratedDeriv (j + 1) H w) w := by
    intro j hj w
    have hd : DifferentiableAt ℝ (iteratedDeriv j H) w :=
      (hH.differentiable_iteratedDeriv j (by exact_mod_cast hj)) w
    have h := hd.hasDerivAt
    rwa [← iteratedDeriv_succ] at h
  have hcomm : ∀ j, j ≤ n → ∀ s : ℝ,
      iteratedDeriv j (fun x => ∫ z, H (x + z) ∂gaussianReal 0 (Real.toNNReal s))
        = fun x => ∫ z, iteratedDeriv j H (x + z) ∂gaussianReal 0 (Real.toNNReal s) :=
    fun j hj s => iteratedDeriv_integral_comp_add_gaussianReal hH hg _ hj
  simp only [hcomm i (by omega), hcomm (i + 2) (by omega)]
  exact hasDerivAt_integral_comp_add_gaussianReal_var (hstep i (by omega))
    (hstep (i + 1) (by omega)) (hg i (by omega)) (hg (i + 1) (by omega)) (hg (i + 2) (by omega))
    (hH.continuous_iteratedDeriv (i + 2) (by exact_mod_cast hi)) hs₀ x

/-- The `s = 0` endpoint of the previous theorem: `∂_s⁺ (∂_x^i P_s H) x |_{s=0} = ½ H^{(i+2)} x`. -/
theorem hasDerivWithinAt_iteratedDeriv_integral_comp_add_gaussianReal_var_zero {n : ℕ}
    (hH : ContDiff ℝ n H) (hg : ∀ i ≤ n, HasExpGrowth (iteratedDeriv i H))
    {i : ℕ} (hi : i + 2 ≤ n) (x : ℝ) :
    HasDerivWithinAt (fun s : ℝ => iteratedDeriv i
        (fun x => ∫ z, H (x + z) ∂gaussianReal 0 (Real.toNNReal s)) x)
      ((1 / 2) * iteratedDeriv (i + 2) H x) (Ici 0) 0 := by
  have hstep : ∀ j, j < n → ∀ w, HasDerivAt (iteratedDeriv j H) (iteratedDeriv (j + 1) H w) w := by
    intro j hj w
    have hd : DifferentiableAt ℝ (iteratedDeriv j H) w :=
      (hH.differentiable_iteratedDeriv j (by exact_mod_cast hj)) w
    have h := hd.hasDerivAt
    rwa [← iteratedDeriv_succ] at h
  have hcomm : ∀ j, j ≤ n → ∀ s : ℝ,
      iteratedDeriv j (fun x => ∫ z, H (x + z) ∂gaussianReal 0 (Real.toNNReal s))
        = fun x => ∫ z, iteratedDeriv j H (x + z) ∂gaussianReal 0 (Real.toNNReal s) :=
    fun j hj s => iteratedDeriv_integral_comp_add_gaussianReal hH hg _ hj
  simp only [hcomm i (by omega)]
  exact hasDerivWithinAt_integral_comp_add_gaussianReal_var_zero (hstep i (by omega))
    (hstep (i + 1) (by omega)) (hg i (by omega)) (hg (i + 1) (by omega)) (hg (i + 2) (by omega))
    (hH.continuous_iteratedDeriv (i + 2) (by exact_mod_cast hi)) x

end ProbabilityTheory
