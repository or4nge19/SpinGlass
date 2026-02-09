/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.HasLaw
import Common.Mathlib.Probability.Distributions.Gaussian.CameronMartin
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Cameron–Martin theorem

Let `μ` be a Gaussian measure on a real Banach space `E`. The **Cameron–Martin theorem** describes
how `μ` transforms under translations by vectors coming from the Cameron–Martin space
`cameronMartin μ`: translating by `cmCoe x` (for `x : cameronMartin μ`) yields an absolutely
continuous measure with density
\(y \mapsto \exp(x(y) - \|x\|^2/2)\).

This file provides:

- the fact that elements of `cameronMartin μ` are centered real Gaussians (`hasLaw_cameronMartin`);
- variance/covariance computations (`variance_cameronMartin`, `covariance_cameronMartin`);
- the measure-level Cameron–Martin theorem (`map_add_cameronMartin_eq_withDensity`) and the
  absolute continuity corollary (`absolutelyContinuous_map_add_cameronMartin`).

## References

* V. I. Bogachev, *Gaussian Measures*, AMS, 1998.

## Tags

Gaussian measure, Cameron–Martin theorem, quasi-invariance
-/


open MeasureTheory Filter Complex
open scoped ENNReal NNReal Topology InnerProductSpace

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsGaussian μ]

/-- An element `x` of the Cameron-Martin space associated to a Gaussian measure has a centered
Gaussian law with variance `‖x‖₊ ^ 2`. -/
lemma hasLaw_cameronMartin (x : cameronMartin μ) : HasLaw x (gaussianReal 0 (‖x‖₊ ^ 2)) μ where
  map_eq := by
    by_cases hx0 : x = 0
    · simp only [hx0, ZeroMemClass.coe_zero, nnnorm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, gaussianReal_zero_var]
      suffices μ.map (fun _ ↦ (0 : ℝ)) = Measure.dirac 0 by
        convert this; simp
      simp
    have hx_norm_pos : 0 < ‖x‖ := by simp [norm_pos_iff, hx0]
    have h := x.2
    -- `x` is in the closure of the range of `centeredToLp`, so it is the `Lp`-limit of such elements.
    have h' :
        (x : Lp ℝ 2 μ) ∈
          closure
            ((LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap : Submodule ℝ (Lp ℝ 2 μ)) :
              Set (Lp ℝ 2 μ)) := by
      -- `x.2` is membership in `topologicalClosure`; rewrite the goal accordingly.
      let s : Submodule ℝ (Lp ℝ 2 μ) :=
        LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap
      have hx : (x : Lp ℝ 2 μ) ∈ (s.topologicalClosure : Set (Lp ℝ 2 μ)) := by
        -- Unfold the abbreviations so the goal matches `x.2`.
        dsimp [s]
        have hx' :
            (x : Lp ℝ 2 μ) ∈
              ((LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap).topologicalClosure :
                Set (Lp ℝ 2 μ)) := by
          -- `x.2` is membership in `cameronMartin μ`; unfold it.
          have hx0 :
              (x : Lp ℝ 2 μ) ∈ (ProbabilityTheory.cameronMartin (μ := μ) : Set (Lp ℝ 2 μ)) := x.2
          dsimp [ProbabilityTheory.cameronMartin] at hx0
          exact hx0
        exact hx'
      -- now rewrite `closure` as `topologicalClosure` and conclude.
      -- `Submodule.topologicalClosure_coe` is definitional (`rfl`), but `rw` avoids `simpa`.
      rw [← Submodule.topologicalClosure_coe (s := s)]
      exact hx
    rcases (mem_closure_iff_seq_limit.mp h') with ⟨L, hL_mem, hL_tendsto⟩
    have hL_mem' :
        ∀ n, ∃ y : StrongDual ℝ E, StrongDual.centeredToLp (E := E) μ y = L n := by
      simpa [SetLike.mem_coe, LinearMap.mem_range] using hL_mem
    have hL_ne_zero : ∀ᶠ n in atTop, L n ≠ 0 := hL_tendsto.eventually_ne (by simp [hx0])
    let L' := fun n ↦ (‖x‖ / ‖L n‖) • L n
    have hL'_mem n : ∃ y, StrongDual.centeredToLp (E := E) μ y = L' n := by
      choose y' hy' using hL_mem'
      refine ⟨(‖x‖ / ‖L n‖) • y' n, ?_⟩
      simp [hy' n, L']
    have hL'_tendsto : Tendsto L' atTop (𝓝 x) := by
      unfold L'
      have h_norm : Tendsto (fun n ↦ ‖L n‖) atTop (𝓝 ‖x‖) := hL_tendsto.norm
      suffices Tendsto (fun n ↦ (‖x‖ / ‖L n‖) • L n) atTop (𝓝 ((‖x‖ / ‖x‖) • x)) by
        rwa [div_self hx_norm_pos.ne', one_smul] at this
      refine Tendsto.smul ?_ hL_tendsto
      exact Tendsto.div tendsto_const_nhds h_norm hx_norm_pos.ne'
    choose y hy using hL'_mem
    have hy_map (n : ℕ) (hn : L n ≠ 0) :
        μ.map (y n) = gaussianReal (μ[y n]) (‖x‖₊ ^ 2) := by
      rw [IsGaussian.map_eq_gaussianReal]
      congr
      rw [← StrongDual.sq_norm_centeredToLp_two (μ := μ) (h := memLp_two_id) (L := y n), hy n]
      unfold L'
      simp only [AddSubgroupClass.coe_norm, norm_smul, norm_div, norm_norm]
      rw [div_mul_cancel₀]
      · norm_cast
        rw [Real.toNNReal_pow (norm_nonneg _), norm_toNNReal]
      · simp [hn]
    have hL'_map (n : ℕ) (hn : L n ≠ 0) :
        μ.map (L' n) = gaussianReal 0 (‖x‖₊ ^ 2) := by
      have h_eq : L' n =ᵐ[μ] fun x ↦ y n x - μ[y n] := by
        rw [← hy]
        filter_upwards [StrongDual.centeredToLp_apply (μ := μ) memLp_two_id (y n)] with z hz
        simp only [hz, sub_right_inj]
        rw [IsGaussian.integral_dual]
      rw [Measure.map_congr h_eq]
      -- rewrite `μ.map (fun ω ↦ y n ω - μ[y n])` as the map of the pushforward measure
      have hy_meas : Measurable (fun ω : E ↦ y n ω) := by
        simpa using (y n : StrongDual ℝ E).continuous.measurable
      have hsub_meas : Measurable (fun z : ℝ ↦ z - μ[y n]) := by
        simpa using (measurable_id.sub measurable_const)
      have h_comp :
          μ.map (fun ω : E ↦ y n ω - μ[y n])
            = Measure.map (fun z : ℝ ↦ z - μ[y n]) (μ.map (fun ω : E ↦ y n ω)) := by
        -- `Measure.map_map` is stated as `(μ.map f).map g = μ.map (g ∘ f)`.
        simpa [Function.comp] using (Measure.map_map (μ := μ) hsub_meas hy_meas).symm
      -- then use that `μ.map (y n)` is Gaussian and shift to mean 0
      rw [h_comp]
      calc
        Measure.map (fun z : ℝ ↦ z - μ[y n]) (μ.map (fun ω : E ↦ y n ω))
            = Measure.map (fun z : ℝ ↦ z - μ[y n]) (gaussianReal (μ[y n]) (‖x‖₊ ^ 2)) := by
                simp [hy_map n hn]
        _ = gaussianReal (μ[y n] - μ[y n]) (‖x‖₊ ^ 2) := by
                simpa using
                  (gaussianReal_map_sub_const (μ := μ[y n]) (v := (‖x‖₊ ^ 2)) (y := μ[y n]))
        _ = gaussianReal 0 (‖x‖₊ ^ 2) := by simp
    have hL'_prob (n : ℕ) : IsProbabilityMeasure (μ.map (L' n)) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    let ν n : ProbabilityMeasure ℝ := ⟨μ.map (L' n), hL'_prob n⟩
    have h_eventuallyEq :
        ∀ᶠ n in atTop, ν n = ⟨gaussianReal 0 (‖x‖₊ ^ 2), inferInstance⟩ := by
      filter_upwards [hL_ne_zero] with n hn
      unfold ν
      simp_rw [hL'_map n hn]
    have hν_tendsto_1 :
        Tendsto ν atTop (𝓝 ⟨gaussianReal 0 (‖x‖₊ ^ 2), inferInstance⟩) := by
      rw [tendsto_congr' h_eventuallyEq]
      exact tendsto_const_nhds
    have hx_prob : IsProbabilityMeasure (μ.map (x : E → ℝ)) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    have hν_tendsto_2 : Tendsto ν atTop (𝓝 ⟨μ.map x, hx_prob⟩) :=
      ((tendstoInMeasure_of_tendsto_Lp hL'_tendsto).tendstoInDistribution
        (fun _ ↦ by fun_prop)).tendsto
    have h_eq := tendsto_nhds_unique hν_tendsto_2 hν_tendsto_1
    rwa [Subtype.ext_iff] at h_eq

/-- The variance of an element of the Cameron-Martin space is the square of its norm. -/
lemma variance_cameronMartin (x : cameronMartin μ) :
    Var[x; μ] = ‖x‖₊ ^ 2 := by
  have : Var[fun y ↦ y; μ.map x] = ‖x‖₊ ^ 2 := by
    simp [(hasLaw_cameronMartin (μ := μ) x).map_eq]
  -- `Var` is invariant under pushing forward along the identity.
  rwa [variance_map aemeasurable_id' (by fun_prop)] at this

/-- The covariance of two elements of the Cameron-Martin space is their inner product. -/
lemma covariance_cameronMartin (x y : cameronMartin μ) :
    cov[x, y; μ] = ⟪x, y⟫_ℝ := by
  have hVarAdd :
      Var[(x : E → ℝ) + (y : E → ℝ); μ]
        = Var[x; μ] + 2 * cov[x, y; μ] + Var[y; μ] :=
    (variance_add (μ := μ) (Lp.memLp x.1) (Lp.memLp y.1))
  have hxy :
      (x : E → ℝ) + (y : E → ℝ) =ᵐ[μ] (x + y : cameronMartin μ) := by
    simp only [Submodule.coe_add, AddSubgroup.coe_add]
    exact (AEEqFun.coeFn_add _ _).symm
  have hVarAdd' :
      Var[x + y; μ] = Var[x; μ] + 2 * cov[x, y; μ] + Var[y; μ] := by
    simpa [variance_congr hxy] using hVarAdd
  -- Rewrite all variances using `variance_cameronMartin`, then solve for the covariance.
  have hCov :
      cov[x, y; μ]
        =
          (Var[x + y; μ] - Var[x; μ] - Var[y; μ]) / 2 := by
    have : (2 : ℝ) * cov[x, y; μ] = Var[x + y; μ] - Var[x; μ] - Var[y; μ] := by
      linarith [hVarAdd']
    linarith
  -- Rewrite `Var` as squared norm and conclude.
  have hVarx : Var[x; μ] = ‖x‖ ^ 2 := by
    simpa using (variance_cameronMartin (μ := μ) x)
  have hVary : Var[y; μ] = ‖y‖ ^ 2 := by
    simpa using (variance_cameronMartin (μ := μ) y)
  have hVarxy : Var[x + y; μ] = ‖x + y‖ ^ 2 := by
    simpa using (variance_cameronMartin (μ := μ) (x + y))
  have hInner :
      ⟪x, y⟫_ℝ = (‖x + y‖ ^ 2 - ‖x‖ ^ 2 - ‖y‖ ^ 2) / 2 := by
    -- `Mathlib` states this using products `‖·‖ * ‖·‖`; rewrite as squares.
    simpa [pow_two, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two x y)
  have hInner' :
      (‖x + y‖ ^ 2 - ‖x‖ ^ 2 - ‖y‖ ^ 2) / 2 = ⟪x, y⟫_ℝ := by
    linarith [hInner]
  calc
    cov[x, y; μ] = (Var[x + y; μ] - Var[x; μ] - Var[y; μ]) / 2 := hCov
    _ = (‖x + y‖ ^ 2 - ‖x‖ ^ 2 - ‖y‖ ^ 2) / 2 := by
          rw [hVarxy, hVarx, hVary]
    _ = ⟪x, y⟫_ℝ := hInner'

/-- The Cameron–Martin density `y ↦ exp (x y - ‖x‖^2/2)` is normalized to integrate to `1`. -/
lemma isProbabilityMeasure_withDensity_cameronMartin (x : cameronMartin μ) :
    IsProbabilityMeasure (μ.withDensity fun y ↦ .ofReal (.exp (x y - ‖x‖ ^ 2 / 2))) where
  measure_univ := by
    rw [withDensity_apply _ .univ, setLIntegral_univ]
    calc
      ∫⁻ a, .ofReal (.exp (x a - ‖x‖ ^ 2 / 2)) ∂μ
          = .ofReal (.exp (- ‖x‖ ^ 2 / 2)) * ∫⁻ a, .ofReal (.exp (x a)) ∂μ := by
            simp_rw [sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]
            rw [lintegral_mul_const _ (by fun_prop), mul_comm, neg_div]
      _ = .ofReal (.exp (- ‖x‖ ^ 2 / 2)) * ∫⁻ a, .ofReal (.exp a) ∂(μ.map x) := by
            rw [lintegral_map (by fun_prop) (by fun_prop)]
      _ = .ofReal (.exp (- ‖x‖ ^ 2 / 2))
            * ∫⁻ a, .ofReal (.exp a) ∂(gaussianReal 0 (‖x‖₊ ^ 2)) := by
            rw [(hasLaw_cameronMartin (μ := μ) x).map_eq]
      _ = .ofReal (.exp (- ‖x‖ ^ 2 / 2)) * .ofReal (.exp (‖x‖ ^ 2 / 2)) := by
            congr
            have h := mgf_id_gaussianReal (μ := (0 : ℝ)) (v := ‖x‖₊ ^ 2)
            rw [funext_iff] at h
            specialize h 1
            simp only [mgf, id_eq, one_mul, mul_one, NNReal.coe_pow, coe_nnnorm, one_pow, zero_add] at h
            rw [← h, ofReal_integral_eq_lintegral_ofReal]
            · simpa using
                (integrable_exp_mul_gaussianReal (μ := (0 : ℝ)) (v := ‖x‖₊ ^ 2) 1)
            · exact ae_of_all _ fun _ ↦ Real.exp_nonneg _
      _ = 1 := by
            rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
            ring_nf
            simp

private lemma integral_exp_sub_mul_I_sub_norm_sq_eq_exp_mul_integral_exp_centered
    (x : cameronMartin μ) (L : StrongDual ℝ E) (t : ℝ) :
    ∫ u, exp ((L u - t * x u) * I - ‖x‖ ^ 2 / 2) ∂μ
      = exp (- ‖x‖ ^ 2 / 2) * ∫ u, exp (((L : cameronMartin μ) - t • x) u * I + μ[L] * I) ∂μ := by
  calc
    ∫ u, exp ((L u - t * x u) * I - ‖x‖ ^ 2 / 2) ∂μ
        = exp (- ‖x‖ ^ 2 / 2) * ∫ u, exp ((L u - t * x u) * I) ∂μ := by
            simp_rw [sub_eq_add_neg, exp_add]
            rw [integral_mul_const, mul_comm (exp _), neg_div]
    _ = exp (- ‖x‖ ^ 2 / 2) * ∫ u, exp ((L u - μ[L] - t * x u) * I + μ[L] * I) ∂μ := by
          congr with u
          congr
          ring
    _ = exp (- ‖x‖ ^ 2 / 2) * ∫ u, exp (((L : cameronMartin μ) - t • x) u * I + μ[L] * I) ∂μ := by
          congr 1
          refine integral_congr_ae ?_
          have h_eq : (L : cameronMartin μ) - t • x =ᵐ[μ] fun u ↦ L u - μ[L] - t * x u := by
            simp only [cmOfDual_apply, AddSubgroupClass.coe_sub, SetLike.val_smul]
            rw [IsGaussian.integral_dual L]
            filter_upwards [StrongDual.centeredToLp_apply (μ := μ) memLp_two_id L,
              AEEqFun.coeFn_sub (γ := ℝ) (StrongDual.centeredToLp (E := E) μ L) (t • x),
              Lp.coeFn_smul (E := ℝ) t (x : Lp ℝ 2 μ)] with u h_toLp h_sub h_smul
            simp only [SetLike.val_smul, Pi.sub_apply] at h_sub
            simp only [Pi.smul_apply, smul_eq_mul] at h_smul
            rw [← h_smul, ← h_toLp, ← h_sub]
            rfl
          filter_upwards [h_eq] with u hu
          rw [hu, integral_complex_ofReal]
          simp

lemma integral_exp_sub_mul_I_sub_norm_sq_eq_exp_mul_integral_gaussianReal
    (x : cameronMartin μ) (L : StrongDual ℝ E) (t : ℝ) :
    ∫ u, exp ((L u - t * x u) * I - ‖x‖ ^ 2 / 2) ∂μ
      = exp (- ‖x‖ ^ 2 / 2 + μ[L] * I)
        * ∫ u : ℝ, exp (u * I) ∂(gaussianReal 0 (‖(L : cameronMartin μ) - t • x‖₊ ^ 2)) := by
  calc
    ∫ u, exp ((L u - t * x u) * I - ‖x‖ ^ 2 / 2) ∂μ
        = exp (- ‖x‖ ^ 2 / 2) * ∫ u, exp (((L : cameronMartin μ) - t • x) u * I + μ[L] * I) ∂μ :=
            integral_exp_sub_mul_I_sub_norm_sq_eq_exp_mul_integral_exp_centered (μ := μ) x L t
    _ = exp (- ‖x‖ ^ 2 / 2)
          * ∫ u : ℝ, exp (u * I + μ[L] * I) ∂(μ.map (((L : cameronMartin μ) - t • x))) := by
            rw [integral_map (by fun_prop) (by fun_prop)]
    _ = exp (- ‖x‖ ^ 2 / 2)
          * ∫ u : ℝ, exp (u * I + μ[L] * I)
              ∂(gaussianReal 0 (‖(L : cameronMartin μ) - t • x‖₊ ^ 2)) := by
            rw [(hasLaw_cameronMartin (μ := μ) ((L : cameronMartin μ) - t • x)).map_eq]
    _ = exp (- ‖x‖ ^ 2 / 2 + μ[L] * I)
          * ∫ u : ℝ, exp (u * I) ∂(gaussianReal 0 (‖(L : cameronMartin μ) - t • x‖₊ ^ 2)) := by
            rw [exp_add, mul_assoc]
            congr 1
            simp_rw [exp_add]
            rw [integral_mul_const, mul_comm _ (exp _)]

private lemma integral_exp_sub_mul_I_sub_norm_sq_eq_closed_form
    (x : cameronMartin μ) (L : StrongDual ℝ E) (t : ℝ) :
    ∫ u, exp ((L u - t * x u) * I - ‖x‖ ^ 2 / 2) ∂μ
      = exp (t * L (cmCoe x) - (1 + t ^ 2) / 2 * ‖x‖ ^ 2 + μ[L] * I - Var[L; μ] / 2) := by
  calc
    ∫ u, exp ((L u - t * x u) * I - ‖x‖ ^ 2 / 2) ∂μ
        =
          exp (- ‖x‖ ^ 2 / 2 + μ[L] * I)
            * ∫ u : ℝ, exp (u * I)
                ∂(gaussianReal 0 (‖(L : cameronMartin μ) - t • x‖₊ ^ 2)) :=
          integral_exp_sub_mul_I_sub_norm_sq_eq_exp_mul_integral_gaussianReal (μ := μ) x L t
    _ = exp (- ‖x‖ ^ 2 / 2 + μ[L] * I - ‖(L : cameronMartin μ) - t • x‖ ^ 2 / 2) := by
          conv_lhs => rw [exp_add]
          conv_rhs => rw [add_sub_assoc, exp_add, sub_eq_add_neg, exp_add, ← mul_assoc]
          have h := charFun_gaussianReal (μ := 0) (v := ‖(L : cameronMartin μ) - t • x‖₊ ^ 2) 1
          simp only [charFun, RCLike.inner_apply, conj_trivial, one_mul, Complex.ofReal_one,
            Complex.ofReal_zero, mul_zero, zero_mul, NNReal.coe_pow, coe_nnnorm, Complex.ofReal_pow,
            one_pow, mul_one, zero_sub] at h
          rw [h]
    _ =
        exp (t * L (cmCoe x) - (1 + t ^ 2) / 2 * ‖x‖ ^ 2 + μ[L] * I - Var[L; μ] / 2) := by
          have h_inner : (t : ℂ) * L (cmCoe x) = ⟪cmOfDual μ L, t • x⟫_ℝ := by
            rw [← apply_cmCoe_eq_inner]
            simp
          rw [h_inner,
            real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
          simp_rw [← pow_two]
          rw [sq_norm_cmOfDual (μ := μ) L]
          simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Complex.ofReal_div,
            Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow,
            Complex.ofReal_ofNat]
          ring_nf

private lemma hasDerivAt_integral_exp_cameronMartin (x : cameronMartin μ) (L : StrongDual ℝ E) (z : ℂ) :
    HasDerivAt (fun z ↦ ∫ u, exp ((L u - z * x u) * I) ∂μ)
      (∫ u, - x u * I * exp ((L u - z * x u) * I) ∂μ) z := by
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun ω ↦ |x ω| * Real.exp (z.im * x ω + |x ω|))
    (F := fun z ω ↦ cexp ((L ω - z * x ω) * I))
    (F' := fun z ω ↦ - x ω * I * exp ((L ω - z * x ω) * I))
    (Metric.ball_mem_nhds z zero_lt_one) ?_ ?_ (by fun_prop) ?_ ?_ ?_).2
  · exact .of_forall fun z ↦ by fun_prop
  · rw [← integrable_norm_iff (by fun_prop)]
    simp only [norm_exp, mul_re, sub_re, ofReal_re, ofReal_im, mul_zero, sub_zero, I_re, sub_im,
      mul_im, zero_add, zero_sub, I_im, mul_one, sub_neg_eq_add]
    change Integrable ((fun a ↦ Real.exp (z.im * a)) ∘ x) μ
    rw [← integrable_map_measure (f := x) (by fun_prop)
      (by fun_prop), (hasLaw_cameronMartin (μ := μ) x).map_eq]
    exact integrable_exp_mul_gaussianReal (μ := 0) (v := ‖x‖₊ ^ 2) z.im
  · refine ae_of_all _ fun ω ε hε ↦ ?_
    simp only [neg_mul, norm_neg, norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one]
    rw [Complex.norm_exp]
    simp only [mul_re, sub_re, ofReal_re, ofReal_im, mul_zero, sub_zero, I_re, sub_im, mul_im,
      zero_add, zero_sub, I_im, mul_one, sub_neg_eq_add]
    gcongr
    have : ε = z + (ε - z) := by simp
    rw [this, add_im, add_mul]
    gcongr _ + ?_
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    conv_rhs => rw [← one_mul (|x ω|)]
    gcongr
    refine (abs_im_le_norm _).trans ?_
    simp only [Metric.mem_ball, dist_eq_norm] at hε
    exact hε.le
  · change Integrable ((fun ω ↦ |ω| * Real.exp (z.im * ω + |ω|)) ∘ x) μ
    rw [← integrable_map_measure (f := x) (by fun_prop) (by fun_prop),
      (hasLaw_cameronMartin (μ := μ) x).map_eq]
    have h := integrable_pow_abs_mul_exp_add_of_integrable_exp_mul (x := 1) (v := z.im) (X := id)
      (t := 2) (μ := gaussianReal 0 (‖x‖₊ ^ 2)) ?_ ?_ zero_le_one (by simp) 1
    · simpa only [id_eq, pow_one, one_mul] using h
    · exact integrable_exp_mul_gaussianReal (z.im + 2)
    · exact integrable_exp_mul_gaussianReal (z.im - 2)
  · refine ae_of_all _ fun ω ε hε ↦ ?_
    simp_rw [sub_mul, sub_eq_add_neg, exp_add, ← neg_mul, mul_comm (_ * I), mul_assoc]
    refine HasDerivAt.const_mul _ ?_
    simp_rw [neg_mul, mul_comm _ (_ * I), ← neg_mul]
    simp_rw [← smul_eq_mul, Complex.exp_eq_exp_ℂ]
    convert hasDerivAt_exp_smul_const (-x ω * I : ℂ) ε using 1
    · ext ω
      congr 1
      simp only [smul_eq_mul, neg_mul, mul_neg, neg_inj]
      ring
    · simp only [smul_eq_mul, neg_mul, mul_neg, neg_inj, mul_eq_mul_right_iff, mul_eq_zero,
        ofReal_eq_zero, I_ne_zero, or_false]
      left
      congr 2
      ring

private lemma analyticOnNhd_integral_exp_cameronMartin (x : cameronMartin μ) (L : StrongDual ℝ E) :
    AnalyticOnNhd ℂ (fun z ↦ ∫ u, exp ((L u - z * x u) * I) ∂μ) Set.univ := by
  refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) isOpen_univ
  have h := hasDerivAt_integral_exp_cameronMartin (μ := μ) x L z
  rw [hasDerivAt_iff_hasFDerivAt] at h
  exact h.hasFDerivWithinAt.differentiableWithinAt

private lemma integral_exp_sub_mul_I_sub_norm_sq_eq_closed_form_complex
    (x : cameronMartin μ) (L : StrongDual ℝ E) (z : ℂ) :
    ∫ u, exp ((L u - z * x u) * I - ‖x‖ ^ 2 / 2) ∂μ
      = exp (z * L (cmCoe x) - (1 + z ^ 2) / 2 * ‖x‖ ^ 2 + μ[L] * I - Var[L; μ] / 2) := by
  revert z
  refine funext_iff.mp ?_
  rw [← Set.eqOn_univ]
  refine
    AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (𝕜 := ℂ) (E := ℂ) (z₀ := 0) ?_ ?_
      isPreconnected_univ (Set.mem_univ 0) ?_
  · simp_rw [sub_eq_add_neg, exp_add, integral_mul_const]
    refine AnalyticOnNhd.mul ?_ analyticOnNhd_const
    simp_rw [← sub_eq_add_neg]
    exact analyticOnNhd_integral_exp_cameronMartin (μ := μ) x L
  · simp_rw [sub_eq_add_neg, exp_add]
    refine AnalyticOnNhd.mul ?_ analyticOnNhd_const
    refine AnalyticOnNhd.mul ?_ analyticOnNhd_const
    refine AnalyticOnNhd.mul ?_ ?_
    · exact (analyticOnNhd_id.mul analyticOnNhd_const).cexp
    · refine (AnalyticOnNhd.mul ?_ analyticOnNhd_const).neg.cexp
      exact (analyticOnNhd_const.add (analyticOnNhd_id.pow 2)).mul analyticOnNhd_const
  have h_real :
      ∃ᶠ (t : ℝ) in 𝓝[≠] 0,
        ∫ u, exp ((L u - t * x u) * I - ‖x‖ ^ 2 / 2) ∂μ
          =
          .exp
            (t * L (cmCoe x) - (1 + t ^ 2) / 2 * ‖x‖ ^ 2 + μ[L] * I - Var[L; μ] / 2) :=
    .of_forall fun y ↦ integral_exp_sub_mul_I_sub_norm_sq_eq_closed_form (μ := μ) x L y
  rw [frequently_iff_seq_forall] at h_real ⊢
  obtain ⟨xs, hx_tendsto, hx_eq⟩ := h_real
  refine ⟨fun n ↦ xs n, ?_, fun n ↦ ?_⟩
  · rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
    constructor
    · rw [← Complex.ofReal_zero, tendsto_ofReal_iff]
      exact hx_tendsto.1
    · simpa using hx_tendsto.2
  · simp only [AddSubgroupClass.coe_norm] at hx_eq
    simp [hx_eq]

private lemma charFunDual_withDensity_exp_cameronMartin (x : cameronMartin μ) (L : StrongDual ℝ E) :
    charFunDual (μ.withDensity fun y ↦ .ofReal (.exp (x y - ‖x‖ ^ 2 / 2))) L
      = exp ((μ[L] + L (cmCoe x)) * I - Var[L; μ] / 2) := by
  calc
    charFunDual (μ.withDensity fun y ↦ .ofReal (.exp (x y - ‖x‖ ^ 2 / 2))) L
        = ∫ u, exp (L u * I + x u - ‖x‖ ^ 2 / 2) ∂μ := by
            rw [charFunDual_apply, integral_withDensity_eq_integral_toReal_smul (by fun_prop)]
            swap
            · exact ae_of_all _ (by finiteness)
            congr with u
            rw [ENNReal.toReal_ofReal (Real.exp_nonneg _), add_sub_assoc, exp_add,
              mul_comm (exp _)]
            simp
    _ = exp ((μ[L] + L (cmCoe x)) * I - Var[L; μ] / 2) := by
          have h := integral_exp_sub_mul_I_sub_norm_sq_eq_closed_form_complex (μ := μ) x L I
          simp only [I_sq, add_neg_cancel, zero_div, zero_mul, sub_zero] at h
          convert h using 3
          · congr
            simp [mul_comm I, sub_mul, mul_assoc]
          · ring

/-- Part of the **Cameron–Martin theorem**: translating `μ` by `cmCoe x` is given by a density.

More precisely, for `x : cameronMartin μ`,
`μ.map (fun y ↦ y + cmCoe x)` is absolutely continuous with respect to `μ`, with
density `y ↦ exp (x y - ‖x‖ ^ 2 / 2)`. -/
theorem map_add_cameronMartin_eq_withDensity (x : cameronMartin μ) :
    μ.map (fun y ↦ y + cmCoe x) = μ.withDensity (fun y ↦ .ofReal (.exp (x y - ‖x‖ ^ 2 / 2))) := by
  have := isProbabilityMeasure_withDensity_cameronMartin (μ := μ) x
  refine Measure.ext_of_charFunDual ?_
  ext L
  rw [charFunDual_map_add_const, IsGaussian.charFunDual_eq, ← exp_add,
    charFunDual_withDensity_exp_cameronMartin (μ := μ) x L]
  congr
  ring

/-- Part of the **Cameron–Martin theorem**: translating `μ` by `cmCoe x` is absolutely continuous. -/
theorem absolutelyContinuous_map_add_cameronMartin (x : cameronMartin μ) :
    μ.map (fun y ↦ y + cmCoe x) ≪ μ := by
  rw [map_add_cameronMartin_eq_withDensity (μ := μ) x]
  exact withDensity_absolutelyContinuous _ _

end ProbabilityTheory
