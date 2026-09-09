/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Common.Mathlib.Probability.PointProcess.PoissonFinite

/-!
# Frullani's integral for exponentials, and the logarithm through the Laplace transform

`∫_0^∞ (e^{-as} - e^{-bs})/s ds = log (b/a)` for `a, b > 0`; in particular
`log x = ∫_0^∞ (e^{-s} - e^{-xs})/s ds` for `x > 0`, and the integrand has constant sign, so the
same integral of its absolute value is `|log x|`.

Consequently, for a positive finite random variable `S` with `𝔼|log S| < ∞`, Fubini gives

`𝔼 log S = ∫_0^∞ (e^{-s} - 𝔼 e^{-sS})/s ds`,

which expresses the mean logarithm through the Laplace transform. This is the device behind
Talagrand's identity (13.10) for the Poisson–Dirichlet weights.

## Main statements

- `Real.frullani_exp`, `Real.integrableOn_inv_mul_exp_sub`.
- `Real.log_eq_integral_Ioi`, `Real.integral_norm_inv_mul_exp_sub`.
- `ProbabilityTheory.integral_log_toReal_eq_integral_Ioi`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Real

/-- `0 ≤ e^{-as} - e^{-bs} ≤ (b - a) s e^{-as}` for `0 ≤ a ≤ b`, `s ≥ 0`. -/
lemma exp_neg_sub_exp_neg_bounds {a b s : ℝ} (hab : a ≤ b) (hs : 0 ≤ s) :
    0 ≤ Real.exp (-(a * s)) - Real.exp (-(b * s))
      ∧ Real.exp (-(a * s)) - Real.exp (-(b * s)) ≤ (b - a) * s * Real.exp (-(a * s)) := by
  have h1 : Real.exp (-(b * s)) = Real.exp (-(a * s)) * Real.exp (-((b - a) * s)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hnn : 0 ≤ (b - a) * s := mul_nonneg (by linarith) hs
  have h2 : Real.exp (-((b - a) * s)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h3 : 1 - Real.exp (-((b - a) * s)) ≤ (b - a) * s := by
    linarith [Real.add_one_le_exp (-((b - a) * s))]
  have hpos := Real.exp_pos (-(a * s))
  constructor
  · rw [h1]; nlinarith
  · rw [h1]; nlinarith

/-- The Frullani integrand for exponentials is integrable on `(0, ∞)`. -/
theorem integrableOn_inv_mul_exp_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun s : ℝ => s⁻¹ * (Real.exp (-(a * s)) - Real.exp (-(b * s)))) (Ioi 0) := by
  have hmin : 0 < min a b := lt_min ha hb
  have hint : IntegrableOn (fun s : ℝ => |b - a| * Real.exp (-(min a b * s))) (Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => Real.exp (-x)) 0 hmin).2
      (by simpa using integrableOn_exp_neg_Ioi 0)
    exact this.const_mul _
  have hmeas : Measurable fun s : ℝ => s⁻¹ * (Real.exp (-(a * s)) - Real.exp (-(b * s))) :=
    measurable_inv.mul ((Real.measurable_exp.comp (measurable_const.mul measurable_id).neg).sub
      (Real.measurable_exp.comp (measurable_const.mul measurable_id).neg))
  refine Integrable.mono' hint hmeas.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun s hs => ?_
  rw [mem_Ioi] at hs
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 hs)]
  rcases le_total a b with hab | hab
  · obtain ⟨h0, h1⟩ := exp_neg_sub_exp_neg_bounds hab hs.le
    rw [abs_of_nonneg h0, min_eq_left hab, abs_of_nonneg (by linarith : 0 ≤ b - a)]
    calc s⁻¹ * (Real.exp (-(a * s)) - Real.exp (-(b * s)))
        ≤ s⁻¹ * ((b - a) * s * Real.exp (-(a * s))) :=
          mul_le_mul_of_nonneg_left h1 (inv_pos.2 hs).le
      _ = (b - a) * Real.exp (-(a * s)) := by field_simp
  · obtain ⟨h0, h1⟩ := exp_neg_sub_exp_neg_bounds hab hs.le
    rw [abs_sub_comm, abs_of_nonneg h0, min_eq_right hab, abs_of_nonpos (by linarith : b - a ≤ 0)]
    calc s⁻¹ * (Real.exp (-(b * s)) - Real.exp (-(a * s)))
        ≤ s⁻¹ * ((a - b) * s * Real.exp (-(b * s))) :=
          mul_le_mul_of_nonneg_left h1 (inv_pos.2 hs).le
      _ = -(b - a) * Real.exp (-(b * s)) := by field_simp; ring

/-- **Frullani's integral for exponentials**: `∫_0^∞ (e^{-as} - e^{-bs})/s ds = log (b/a)`. -/
theorem frullani_exp {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ s in Ioi (0 : ℝ), s⁻¹ * (Real.exp (-(a * s)) - Real.exp (-(b * s))) = Real.log (b / a) := by
  have hf : LocallyIntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) :=
    (Real.continuous_exp.comp continuous_neg).continuousOn.locallyIntegrableOn measurableSet_Ioi
  have hL : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[>] 0) (𝓝 1) := by
    have h : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝 0) (𝓝 (Real.exp (-0))) :=
      (Real.continuous_exp.comp continuous_neg).tendsto 0
    rw [neg_zero, Real.exp_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hR : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hint : IntegrableOn (fun x : ℝ => x⁻¹ • (Real.exp (-(a * x)) - Real.exp (-(b * x))))
      (Ioi 0) := by
    simpa [smul_eq_mul] using integrableOn_inv_mul_exp_sub ha hb
  have := Frullani.integral_Ioi_eq (f := fun t : ℝ => Real.exp (-t)) hf ha hb hL hR hint
  simpa [smul_eq_mul] using this

/-- `log x = ∫_0^∞ (e^{-s} - e^{-xs})/s ds` for `x > 0`. -/
theorem log_eq_integral_Ioi {x : ℝ} (hx : 0 < x) :
    Real.log x = ∫ s in Ioi (0 : ℝ), s⁻¹ * (Real.exp (-s) - Real.exp (-(x * s))) := by
  have := frullani_exp one_pos hx
  simpa using this.symm

/-- The Frullani integrand for `log x` has constant sign, so integrating its absolute value gives
`|log x|`. -/
theorem integral_norm_inv_mul_exp_sub {x : ℝ} (hx : 0 < x) :
    ∫ s in Ioi (0 : ℝ), ‖s⁻¹ * (Real.exp (-s) - Real.exp (-(x * s)))‖ = |Real.log x| := by
  rcases le_or_gt 1 x with h1 | h1
  · have hpt : ∀ s ∈ Ioi (0 : ℝ), ‖s⁻¹ * (Real.exp (-s) - Real.exp (-(x * s)))‖
        = s⁻¹ * (Real.exp (-s) - Real.exp (-(x * s))) := by
      intro s hs
      rw [mem_Ioi] at hs
      rw [Real.norm_of_nonneg]
      refine mul_nonneg (inv_nonneg.2 hs.le) ?_
      have : Real.exp (-(x * s)) ≤ Real.exp (-s) := Real.exp_le_exp.2 (by nlinarith)
      linarith
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, ← log_eq_integral_Ioi hx,
      abs_of_nonneg (Real.log_nonneg h1)]
  · have hpt : ∀ s ∈ Ioi (0 : ℝ), ‖s⁻¹ * (Real.exp (-s) - Real.exp (-(x * s)))‖
        = -(s⁻¹ * (Real.exp (-s) - Real.exp (-(x * s)))) := by
      intro s hs
      rw [mem_Ioi] at hs
      rw [Real.norm_of_nonpos]
      have : Real.exp (-s) ≤ Real.exp (-(x * s)) := Real.exp_le_exp.2 (by nlinarith)
      exact mul_nonpos_iff.2 (Or.inl ⟨inv_nonneg.2 hs.le, by linarith⟩)
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_neg, ← log_eq_integral_Ioi hx,
      abs_of_neg (Real.log_neg hx h1)]

end Real

namespace ProbabilityTheory

open ENNReal

/-- The Laplace transform `s ↦ 𝔼 e^{-sS}` of an `ℝ≥0∞`-valued random variable. -/
noncomputable def laplaceTransform {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : Ω → ℝ≥0∞) (s : ℝ) : ℝ :=
  ∫ ω, negExp (ENNReal.ofReal s * S ω) ∂P

/-- **The mean logarithm through the Laplace transform.** For a measurable `S : Ω → ℝ≥0∞`,
almost surely in `(0, ∞)`, with `𝔼|log S| < ∞`,

`𝔼 log S = ∫_0^∞ (e^{-s} - 𝔼 e^{-sS})/s ds`,

and the integrand on the right is integrable on `(0, ∞)`. -/
theorem integral_log_toReal_eq_integral_Ioi {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {S : Ω → ℝ≥0∞} (hS : Measurable S)
    (hpos : ∀ᵐ ω ∂P, 0 < S ω) (hfin : ∀ᵐ ω ∂P, S ω < ∞)
    (hint : Integrable (fun ω => Real.log (S ω).toReal) P) :
    (∫ ω, Real.log (S ω).toReal ∂P
        = ∫ s, s⁻¹ * (Real.exp (-s) - laplaceTransform P S s) ∂(volume.restrict (Ioi (0 : ℝ))))
      ∧ IntegrableOn (fun s : ℝ => s⁻¹ * (Real.exp (-s) - laplaceTransform P S s)) (Ioi 0) := by
  classical
  -- the good set
  have hgood : ∀ᵐ ω ∂P, 0 < (S ω).toReal ∧ S ω ≠ ∞ := by
    filter_upwards [hpos, hfin] with ω h0 h1
    exact ⟨ENNReal.toReal_pos h0.ne' h1.ne, h1.ne⟩
  -- on the good set the integrand is the Frullani integrand of `x = (S ω).toReal`
  have hpt : ∀ ω, 0 < (S ω).toReal → S ω ≠ ∞ → ∀ s : ℝ, 0 < s →
      negExp (ENNReal.ofReal s * S ω) = Real.exp (-((S ω).toReal * s)) := by
    intro ω hx hne s hs
    conv_lhs => rw [← ENNReal.ofReal_toReal hne]
    rw [← ENNReal.ofReal_mul hs.le, negExp_ofReal (mul_nonneg hs.le hx.le), mul_comm]
  have hmeas : Measurable fun p : ℝ × Ω =>
      p.1⁻¹ * (Real.exp (-p.1) - negExp (ENNReal.ofReal p.1 * S p.2)) :=
    measurable_fst.inv.mul ((Real.measurable_exp.comp measurable_fst.neg).sub
      (measurable_negExp.comp (measurable_fst.ennreal_ofReal.mul (hS.comp measurable_snd))))
  -- a.e. identity
  have hae : ∀ᵐ ω ∂P, Real.log (S ω).toReal
      = ∫ s, s⁻¹ * (Real.exp (-s) - negExp (ENNReal.ofReal s * S ω))
          ∂(volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [hgood] with ω hω
    rw [Real.log_eq_integral_Ioi hω.1]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    rw [mem_Ioi] at hs
    rw [hpt ω hω.1 hω.2 s hs]
  -- joint integrability
  have hFint : Integrable (fun p : ℝ × Ω =>
      p.1⁻¹ * (Real.exp (-p.1) - negExp (ENNReal.ofReal p.1 * S p.2)))
      ((volume.restrict (Ioi (0 : ℝ))).prod P) := by
    refine (integrable_prod_iff' hmeas.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · filter_upwards [hgood] with ω hω
      refine IntegrableOn.congr_fun (Real.integrableOn_inv_mul_exp_sub one_pos hω.1) ?_
        measurableSet_Ioi
      intro s hs
      rw [mem_Ioi] at hs
      simp only [one_mul]
      rw [hpt ω hω.1 hω.2 s hs]
    · refine (hint.abs).congr ?_
      filter_upwards [hgood] with ω hω
      have := Real.integral_norm_inv_mul_exp_sub hω.1
      rw [← this]
      refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
      rw [mem_Ioi] at hs
      rw [hpt ω hω.1 hω.2 s hs]
  have hinner : ∀ s : ℝ, ∫ ω, s⁻¹ * (Real.exp (-s) - negExp (ENNReal.ofReal s * S ω)) ∂P
      = s⁻¹ * (Real.exp (-s) - laplaceTransform P S s) := by
    intro s
    have hb : Integrable (fun ω => negExp (ENNReal.ofReal s * S ω)) P :=
      Integrable.mono' (integrable_const 1)
        (measurable_negExp.comp (measurable_const.mul hS)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (negExp_nonneg _)]; exact negExp_le_one _)
    rw [integral_const_mul, integral_sub (integrable_const _) hb, integral_const, probReal_univ,
      one_smul]
    rfl
  constructor
  · calc ∫ ω, Real.log (S ω).toReal ∂P
        = ∫ ω, ∫ s, s⁻¹ * (Real.exp (-s) - negExp (ENNReal.ofReal s * S ω))
            ∂(volume.restrict (Ioi (0 : ℝ))) ∂P := integral_congr_ae hae
      _ = ∫ s, ∫ ω, s⁻¹ * (Real.exp (-s) - negExp (ENNReal.ofReal s * S ω)) ∂P
            ∂(volume.restrict (Ioi (0 : ℝ))) := (integral_integral_swap hFint).symm
      _ = ∫ s, s⁻¹ * (Real.exp (-s) - laplaceTransform P S s)
            ∂(volume.restrict (Ioi (0 : ℝ))) :=
          integral_congr_ae (Filter.Eventually.of_forall hinner)
  · have := hFint.integral_prod_left
    refine this.congr (Filter.Eventually.of_forall fun s => ?_)
    exact hinner s

end ProbabilityTheory
