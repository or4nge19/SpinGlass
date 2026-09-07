/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.Distributions.Gaussian_Poincare
import Mathlib.Probability.Moments.SubGaussian

/-!
# The Gaussian concentration inequality

For a centered Gaussian measure `μ` on a real Hilbert space and a `C¹` functional `f` with
`‖fderiv ℝ f x‖ ≤ K`, the centred variable `f - 𝔼f` is sub-Gaussian with parameter
`‖covarianceOperator μ‖ * K²`:

`𝔼[exp (t (f - 𝔼f))] ≤ exp (‖C‖ K² t² / 2)`,  hence  `μ{f - 𝔼f ≥ ε} ≤ exp (-ε² / (2‖C‖K²))`.

This is the Borell–Tsirelson–Ibragimov–Sudakov concentration inequality, and Talagrand's
Theorem 1.3.4. The constant is sharp: for `f` linear it is an equality.

## Main statements

- `ProbabilityTheory.IsGaussian.integrable_exp_mul_norm`: `exp (a ‖x‖)` is `μ`-integrable.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Gradient RealInnerProductSpace

namespace ProbabilityTheory

namespace IsGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsGaussian μ]

/-- **Every exponential moment of the norm is finite.** A consequence of Fernique's theorem: the
Gaussian tail `exp (C ‖x‖²)` dominates `exp (a ‖x‖)` for every `a`. -/
theorem integrable_exp_mul_norm (a : ℝ) :
    Integrable (fun x : E => Real.exp (a * ‖x‖)) μ := by
  obtain ⟨C, hC, hint⟩ := IsGaussian.exists_integrable_exp_sq (E := E) μ
  refine Integrable.mono' (hint.const_mul (Real.exp (a ^ 2 / (4 * C)))) (by fun_prop)
    (Filter.Eventually.of_forall fun x => ?_)
  have hkey : a * ‖x‖ ≤ a ^ 2 / (4 * C) + C * ‖x‖ ^ 2 := by
    have hd : a ^ 2 / (4 * C) + C * ‖x‖ ^ 2 - a * ‖x‖
        = (2 * C * ‖x‖ - a) ^ 2 / (4 * C) := by
      field_simp
      ring
    have hnn : (0 : ℝ) ≤ (2 * C * ‖x‖ - a) ^ 2 / (4 * C) :=
      div_nonneg (sq_nonneg _) (by linarith)
    rw [← hd] at hnn
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), ← Real.exp_add]
  exact Real.exp_le_exp.mpr hkey


/-! ### The moment generating function of a bounded Lipschitz functional

The `C¹` functional `f` is bounded here only so that the integration by parts behind the
covariance inequality applies to `exp (t (f - 𝔼f))`, whose derivative would otherwise grow
exponentially. The hypothesis is removed by truncation in
`hasSubgaussianMGF_sub_integral_of_norm_fderiv_le`. -/

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  {ν : Measure H} [IsGaussian ν]

/-- **The sub-Gaussian bound on the moment generating function**, for a bounded `C¹` functional
with derivative bounded by `K`, at a nonnegative parameter. -/
private lemma mgf_le_of_bounded_of_nonneg
    (hmean0 : (∫ x : H, x ∂ν) = 0)
    {f : H → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ} (hK : ∀ x, ‖fderiv ℝ f x‖ ≤ K)
    {A : ℝ} (hA : ∀ x, ⟪covarianceOperator ν (∇ f x), ∇ f x⟫ ≤ A)
    {M : ℝ} (hM : ∀ x, |f x| ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x : H, Real.exp (t * (f x - ν[f])) ∂ν) ≤ Real.exp (A * t ^ 2 / 2) := by
  classical
  set c : ℝ := ν[f] with hcdef
  set a : ℝ := A with hadef
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0)
  have ha0 : 0 ≤ a := by
    rw [hadef]
    exact le_trans (LinearMap.IsPositive.inner_nonneg_left isPositive_covarianceOperator (∇ f 0))
      (hA 0)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hfc : Continuous f := hf.continuous
  have hfint : Integrable f ν :=
    Integrable.mono' (integrable_const M) hfc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM x)
  have hcM : |c| ≤ M := by
    rw [hcdef]
    calc |∫ x : H, f x ∂ν| ≤ ∫ x : H, |f x| ∂ν := by
          simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := ν) f
      _ ≤ ∫ _x : H, M ∂ν :=
          integral_mono hfint.abs (integrable_const M) fun x => hM x
      _ = M := by simp [probReal_univ]
  have hdiff2 : ∀ x : H, |f x - c| ≤ 2 * M := fun x => by
    have := hM x
    have := hcM
    rw [abs_sub_le_iff]
    constructor <;> [skip; skip] <;>
      [ (have h1 := abs_le.mp (hM x); have h2 := abs_le.mp hcM; linarith [h1.1, h1.2, h2.1, h2.2]);
        (have h1 := abs_le.mp (hM x); have h2 := abs_le.mp hcM;
          linarith [h1.1, h1.2, h2.1, h2.2]) ]
  -- the exponential family and its basic properties
  set Z : ℝ → ℝ := fun s => ∫ x : H, Real.exp (s * (f x - c)) ∂ν with hZdef
  have hgc : ∀ s : ℝ, Continuous fun x : H => Real.exp (s * (f x - c)) := fun s => by fun_prop
  have hgb : ∀ (s : ℝ) (x : H), Real.exp (s * (f x - c)) ≤ Real.exp (|s| * (2 * M)) := by
    intro s x
    refine Real.exp_le_exp.mpr ?_
    calc s * (f x - c) ≤ |s * (f x - c)| := le_abs_self _
      _ = |s| * |f x - c| := abs_mul _ _
      _ ≤ |s| * (2 * M) := mul_le_mul_of_nonneg_left (hdiff2 x) (abs_nonneg s)
  have hgi : ∀ s : ℝ, Integrable (fun x : H => Real.exp (s * (f x - c))) ν := fun s =>
    Integrable.mono' (integrable_const (Real.exp (|s| * (2 * M))))
      (hgc s).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
        exact hgb s x)
  have hZpos : ∀ s : ℝ, 0 < Z s := by
    intro s
    have hlow : ∀ x : H, Real.exp (-(|s| * (2 * M))) ≤ Real.exp (s * (f x - c)) := by
      intro x
      refine Real.exp_le_exp.mpr ?_
      have : -(|s| * (2 * M)) ≤ -|s * (f x - c)| := by
        have : |s * (f x - c)| ≤ |s| * (2 * M) := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hdiff2 x) (abs_nonneg s)
        linarith
      calc -(|s| * (2 * M)) ≤ -|s * (f x - c)| := this
        _ ≤ s * (f x - c) := neg_abs_le _
    calc (0 : ℝ) < Real.exp (-(|s| * (2 * M))) := Real.exp_pos _
      _ = ∫ _x : H, Real.exp (-(|s| * (2 * M))) ∂ν := by simp [probReal_univ]
      _ ≤ Z s := integral_mono (integrable_const _) (hgi s) hlow
  have hZ0 : Z 0 = 1 := by simp [hZdef, probReal_univ]
  -- the derivative of the moment generating function
  have hderiv : ∀ s : ℝ,
      HasDerivAt Z (∫ x : H, (f x - c) * Real.exp (s * (f x - c)) ∂ν) s := by
    intro s
    have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := ν) (F := fun s x => Real.exp (s * (f x - c)))
      (F' := fun s x => (f x - c) * Real.exp (s * (f x - c)))
      (x₀ := s) (s := Metric.ball s 1)
      (bound := fun _ : H => 2 * M * Real.exp ((|s| + 1) * (2 * M)))
      (Metric.ball_mem_nhds s one_pos)
      (Filter.Eventually.of_forall fun s' => (hgc s').aestronglyMeasurable)
      (hgi s)
      (((hfc.sub continuous_const).mul (hgc s)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x s' hs' => ?_)
      (integrable_const _)
      (Filter.Eventually.of_forall fun x s' _ => ?_)
    · exact hres.2
    · have hs'1 : |s'| ≤ |s| + 1 := by
        have := Metric.mem_ball.mp hs'
        rw [Real.dist_eq] at this
        calc |s'| = |s + (s' - s)| := by ring_nf
          _ ≤ |s| + |s' - s| := abs_add_le _ _
          _ ≤ |s| + 1 := by
              have habs : |s' - s| ≤ 1 := le_of_lt this
              have : |s + (s' - s)| ≤ |s| + |s' - s| := abs_add_le _ _
              linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      refine mul_le_mul (hdiff2 x) ?_ (Real.exp_nonneg _) (by positivity)
      refine le_trans (hgb s' x) (Real.exp_le_exp.mpr ?_)
      exact mul_le_mul_of_nonneg_right hs'1 (by positivity)
    · have hlin : HasDerivAt (fun y : ℝ => y * (f x - c)) (f x - c) s' := by
        simpa using (hasDerivAt_id s').mul_const (f x - c)
      simpa [mul_comm] using hlin.exp
  -- the differential inequality, from the asymmetric covariance inequality
  have hcov : ∀ s : ℝ, 0 ≤ s →
      (∫ x : H, (f x - c) * Real.exp (s * (f x - c)) ∂ν) ≤ s * a * Z s := by
    intro s hs
    set g : H → ℝ := fun x => Real.exp (s * (f x - c)) with hgdef
    have hgC1 : ContDiff ℝ 1 g := Real.contDiff_exp.comp ((hf.sub contDiff_const).const_smul s)
    have hgderiv : ∀ x : H, fderiv ℝ g x = (s * g x) • fderiv ℝ f x := by
      intro x
      have h0 : HasFDerivAt (fun y : H => f y - c) (fderiv ℝ f x) x :=
        ((hf.differentiable_one x).hasFDerivAt).sub_const c
      have hlin : HasFDerivAt (fun y : H => s * (f y - c)) (s • fderiv ℝ f x) x :=
        h0.const_mul s
      have hcomp : HasFDerivAt g ((Real.exp (s * (f x - c))) • (s • fderiv ℝ f x)) x := by
        simpa [hgdef, Function.comp_def] using
          (Real.hasDerivAt_exp (s * (f x - c))).comp_hasFDerivAt x hlin
      rw [hcomp.fderiv, smul_smul]
      simp only [hgdef]
      congr 1
      ring
    have hgK : ∀ x : H, ‖fderiv ℝ g x‖ ≤ s * Real.exp (|s| * (2 * M)) * K := by
      intro x
      rw [hgderiv x, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine mul_le_mul ?_ (hK x) (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left (hgb s x) hs
    have hgrad : ∀ x : H, ∇ g x = (s * g x) • ∇ f x := by
      intro x
      unfold gradient
      rw [hgderiv x, map_smul]
    have hqg : ∀ x : H,
        Real.sqrt ⟪covarianceOperator ν (∇ g x), ∇ g x⟫ ≤ s * Real.sqrt a * g x := by
      intro x
      have hgx : 0 < g x := Real.exp_pos _
      have heq : ⟪covarianceOperator ν (∇ g x), ∇ g x⟫
          = (s * g x) ^ 2 * ⟪covarianceOperator ν (∇ f x), ∇ f x⟫ := by
        rw [hgrad x, map_smul, real_inner_smul_left, real_inner_smul_right]
        ring
      rw [heq, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      rw [hadef]
      have := Real.sqrt_le_sqrt (hA x)
      calc s * g x * Real.sqrt ⟪covarianceOperator ν (∇ f x), ∇ f x⟫
          ≤ s * g x * Real.sqrt A := mul_le_mul_of_nonneg_left this (by positivity)
        _ = s * Real.sqrt A * g x := by ring
    have hsqrtint : Integrable
        (fun x : H => Real.sqrt ⟪covarianceOperator ν (∇ g x), ∇ g x⟫) ν := by
      have hcont : Continuous fun x : H => Real.sqrt ⟪covarianceOperator ν (∇ g x), ∇ g x⟫ :=
        Real.continuous_sqrt.comp (continuous_inner.comp
          (((covarianceOperator ν).continuous.comp
            (ContDiff.continuous_gradient hgC1)).prodMk (ContDiff.continuous_gradient hgC1)))
      refine Integrable.mono' ((hgi s).const_mul (s * Real.sqrt a))
        hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact hqg x
    have hgradle : (∫ x : H, Real.sqrt ⟪covarianceOperator ν (∇ g x), ∇ g x⟫ ∂ν)
        ≤ s * Real.sqrt a * Z s := by
      calc (∫ x : H, Real.sqrt ⟪covarianceOperator ν (∇ g x), ∇ g x⟫ ∂ν)
          ≤ ∫ x : H, s * Real.sqrt a * g x ∂ν :=
            integral_mono hsqrtint ((hgi s).const_mul (s * Real.sqrt a)) hqg
        _ = s * Real.sqrt a * Z s := by rw [MeasureTheory.integral_const_mul]
    have hcovbound : |cov[f, g; ν]|
        ≤ Real.sqrt a * ∫ x : H, Real.sqrt ⟪covarianceOperator ν (∇ g x), ∇ g x⟫ ∂ν := by
      rw [hadef]
      exact abs_covariance_le_sqrt_mul_integral_sqrt (μ := ν) hmean0 hf hgC1 hK hgK hA
    have hcoveq : cov[f, g; ν] = ∫ x : H, (f x - c) * g x ∂ν := by
      have hfLp : MemLp f 2 ν :=
        MemLp.mono_exponent (memLp_top_of_bound hfc.aestronglyMeasurable M
          (Filter.Eventually.of_forall fun x => by
            simpa [Real.norm_eq_abs] using hM x)) le_top
      have hgLp : MemLp g 2 ν :=
        MemLp.mono_exponent (memLp_top_of_bound (hgc s).aestronglyMeasurable
          (Real.exp (|s| * (2 * M)))
          (Filter.Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
            exact hgb s x)) le_top
      rw [covariance_eq_sub hfLp hgLp]
      have hmul : Integrable (fun x : H => f x * g x) ν := by
        simpa [Pi.mul_def] using MemLp.integrable_mul hfLp hgLp
      have : (∫ x : H, (f x - c) * g x ∂ν)
          = (∫ x : H, f x * g x ∂ν) - c * ∫ x : H, g x ∂ν := by
        rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_sub hmul
          ((hgi s).const_mul c)]
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      rw [this, hcdef]
      simp [Pi.mul_apply]
    calc (∫ x : H, (f x - c) * Real.exp (s * (f x - c)) ∂ν)
        = cov[f, g; ν] := hcoveq.symm
      _ ≤ |cov[f, g; ν]| := le_abs_self _
      _ ≤ Real.sqrt a * ∫ x : H, Real.sqrt ⟪covarianceOperator ν (∇ g x), ∇ g x⟫ ∂ν :=
          hcovbound
      _ ≤ Real.sqrt a * (s * Real.sqrt a * Z s) :=
          mul_le_mul_of_nonneg_left hgradle (Real.sqrt_nonneg _)
      _ = s * a * Z s := by
          rw [show Real.sqrt a * (s * Real.sqrt a * Z s)
              = (Real.sqrt a * Real.sqrt a) * (s * Z s) by ring, Real.mul_self_sqrt ha0]
          ring
  -- Grönwall
  set u : ℝ → ℝ := fun s => Real.log (Z s) - a * s ^ 2 / 2 with hudef
  have huderiv : ∀ s : ℝ, HasDerivAt u
      ((∫ x : H, (f x - c) * Real.exp (s * (f x - c)) ∂ν) / Z s - a * s) s := by
    intro s
    have hlog := (hderiv s).log (ne_of_gt (hZpos s))
    have hquad : HasDerivAt (fun y : ℝ => a * y ^ 2 / 2) (a * s) s := by
      have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * s) s := by
        simpa using hasDerivAt_pow 2 s
      have h3 : HasDerivAt (fun y : ℝ => a * y ^ 2 / 2) (a * (2 * s) / 2) s :=
        (h2.const_mul a).div_const 2
      have heq : a * (2 * s) / 2 = a * s := by ring
      rwa [heq] at h3
    rw [hudef]
    exact hlog.sub hquad
  have hunonpos : ∀ s ∈ interior (Set.Ici (0:ℝ)), deriv u s ≤ 0 := by
    intro s hs
    rw [interior_Ici] at hs
    have hs0 : (0:ℝ) ≤ s := le_of_lt hs
    rw [(huderiv s).deriv]
    have hb := hcov s hs0
    have hZs := hZpos s
    have h1 : (∫ x : H, (f x - c) * Real.exp (s * (f x - c)) ∂ν) / Z s ≤ s * a := by
      rw [div_le_iff₀ hZs]
      exact hb
    linarith
  have hanti : AntitoneOn u (Set.Ici (0:ℝ)) :=
    antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun s _ => ((huderiv s).continuousAt).continuousWithinAt)
      (fun s _ => (huderiv s).differentiableAt.differentiableWithinAt) hunonpos
  have hut : u t ≤ u 0 := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  have hu0 : u 0 = 0 := by simp [hudef, hZ0]
  have hlog : Real.log (Z t) ≤ a * t ^ 2 / 2 := by
    have := hut
    rw [hu0, hudef] at this
    simpa using this
  calc Z t = Real.exp (Real.log (Z t)) := (Real.exp_log (hZpos t)).symm
    _ ≤ Real.exp (a * t ^ 2 / 2) := Real.exp_le_exp.mpr hlog


/-! ### Removing the boundedness hypothesis

The truncation `f ↦ n · arctan (f / n)` is `C¹`, has the same derivative bound (because
`|arctan'| ≤ 1`), is bounded by `n π / 2`, is dominated by `|f|`, and converges to `f` pointwise.
Dominated convergence — legitimate because every exponential moment of `‖x‖` is finite — then
transfers the moment generating function bound. -/

private lemma abs_arctan_le (y : ℝ) : |Real.arctan y| ≤ |y| := by
  have hderiv : ∀ x : ℝ, deriv Real.arctan x = 1 / (1 + x ^ 2) :=
    fun x => (Real.hasDerivAt_arctan x).deriv
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := Real.arctan) (C := 1)
    (s := Set.univ) (fun x _ => Real.differentiable_arctan x)
    (fun x _ => by
      rw [hderiv x, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (1 + x ^ 2)), div_le_one (by positivity)]
      nlinarith [sq_nonneg x])
    convex_univ (Set.mem_univ 0) (Set.mem_univ y)
  simpa [Real.arctan_zero] using h

private lemma tendsto_mul_arctan_div (u : ℝ) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) * Real.arctan (u / n)) Filter.atTop (nhds u) := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  · have hslope : Filter.Tendsto (slope Real.arctan 0)
        (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) := by
      have h := (Real.hasDerivAt_arctan 0)
      rw [hasDerivAt_iff_tendsto_slope] at h
      simpa using h
    have hy : Filter.Tendsto (fun n : ℕ => u / n) Filter.atTop (nhdsWithin 0 {(0 : ℝ)}ᶜ) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · simpa using tendsto_const_div_atTop_nhds_zero_nat u
      · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact div_ne_zero hu (Nat.cast_ne_zero.mpr hn.ne')
    have hcomp : Filter.Tendsto
        (fun n : ℕ => u * slope Real.arctan 0 (u / n)) Filter.atTop (nhds (u * 1)) :=
      Filter.Tendsto.const_mul u (hslope.comp hy)
    rw [mul_one] at hcomp
    refine hcomp.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hs : slope Real.arctan 0 (u / n) = (u / n)⁻¹ * Real.arctan (u / n) := by
      simp [slope, Real.arctan_zero]
    rw [hs]
    field_simp

/-- **The Gaussian concentration inequality** (Borell–Tsirelson–Ibragimov–Sudakov; Talagrand,
*Mean Field Models for Spin Glasses*, Vol. I, Theorem 1.3.4). For a centered Gaussian measure on a
real Hilbert space and a `C¹` functional whose derivative is bounded by `K`, the centred variable
`f - 𝔼f` is sub-Gaussian with parameter `‖covarianceOperator μ‖ K²`. The constant is sharp: for
`f` a linear functional it is an equality.

All tail bounds follow from Mathlib's sub-Gaussian API: `HasSubgaussianMGF.measure_ge_le` gives
`μ{f - 𝔼f ≥ ε} ≤ exp (-ε² / (2‖C‖K²))`. -/
theorem hasSubgaussianMGF_sub_integral_of_inner_covarianceOperator_le
    (hmean0 : (∫ x : H, x ∂ν) = 0)
    {f : H → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ} (hK : ∀ x, ‖fderiv ℝ f x‖ ≤ K)
    {A : ℝ} (hA : ∀ x, ⟪covarianceOperator ν (∇ f x), ∇ f x⟫ ≤ A) :
    HasSubgaussianMGF (fun x : H => f x - ν[f]) A.toNNReal ν := by
  classical
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0)
  have ha0 : (0 : ℝ) ≤ A :=
    le_trans (LinearMap.IsPositive.inner_nonneg_left isPositive_covarianceOperator (∇ f 0)) (hA 0)
  have hfd : Differentiable ℝ f := hf.differentiable_one
  have hfc : Continuous f := hf.continuous
  -- linear growth and the resulting exponential integrability
  have hgrow : ∀ x : H, |f x| ≤ |f 0| + K * ‖x‖ := fun x => by
    simpa [Real.norm_eq_abs] using norm_le_add_mul_norm_of_norm_fderiv_le hfd hK x
  have hfint : Integrable f ν :=
    MemLp.integrable le_rfl
      (MemLp.of_norm_fderiv_le hfd hK (IsGaussian.memLp_id ν 1 (by simp)))
  set c : ℝ := ν[f] with hcdef
  have hexpint : ∀ t : ℝ, Integrable (fun x : H => Real.exp (t * (f x - c))) ν := by
    intro t
    refine Integrable.mono'
      ((integrable_exp_mul_norm (μ := ν) (|t| * K)).const_mul
        (Real.exp (|t| * (|f 0| + |c|)))) (by fun_prop)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    calc t * (f x - c) ≤ |t| * |f x - c| := by
          rw [← abs_mul]; exact le_abs_self _
      _ ≤ |t| * (|f 0| + K * ‖x‖ + |c|) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg t)
          calc |f x - c| ≤ |f x| + |c| := abs_sub _ _
            _ ≤ |f 0| + K * ‖x‖ + |c| := by linarith [hgrow x]
      _ = |t| * (|f 0| + |c|) + |t| * K * ‖x‖ := by ring
  -- the truncations
  set g : ℕ → H → ℝ := fun n x => (n : ℝ) * Real.arctan (f x / n) with hgdef
  have hgC1 : ∀ n : ℕ, ContDiff ℝ 1 (g n) := fun n =>
    contDiff_const.mul (Real.contDiff_arctan.comp (hf.div_const (n : ℝ)))
  have hgfderiv : ∀ (n : ℕ), 0 < n → ∀ x : H,
      fderiv ℝ (g n) x = ((1 : ℝ) / (1 + (f x / n) ^ 2)) • fderiv ℝ f x := by
    intro n hn x
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have h1 : HasFDerivAt (fun y : H => f y / n) (((n : ℝ)⁻¹) • fderiv ℝ f x) x := by
      have h0 : HasFDerivAt (fun y : H => (n : ℝ)⁻¹ * f y) (((n : ℝ)⁻¹) • fderiv ℝ f x) x :=
        (hfd x).hasFDerivAt.const_mul ((n : ℝ)⁻¹)
      simpa [div_eq_inv_mul] using h0
    have h2 := (Real.hasDerivAt_arctan (f x / n)).comp_hasFDerivAt x h1
    have h3 : HasFDerivAt (g n)
        ((n : ℝ) • ((1 / (1 + (f x / n) ^ 2)) • ((n : ℝ)⁻¹ • fderiv ℝ f x))) x := by
      simpa [hgdef, Function.comp_def] using h2.const_mul (n : ℝ)
    rw [h3.fderiv]
    simp only [smul_smul]
    field_simp
  have hgK : ∀ (n : ℕ), 0 < n → ∀ x : H, ‖fderiv ℝ (g n) x‖ ≤ K := by
    intro n hn x
    rw [hgfderiv n hn x, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (1:ℝ) / (1 + (f x / n) ^ 2))]
    have hle : (1 : ℝ) / (1 + (f x / n) ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [sq_nonneg (f x / n)]
    calc 1 / (1 + (f x / n) ^ 2) * ‖fderiv ℝ f x‖ ≤ 1 * ‖fderiv ℝ f x‖ :=
          mul_le_mul_of_nonneg_right hle (norm_nonneg _)
      _ ≤ K := by rw [one_mul]; exact hK x
  have hgA : ∀ (n : ℕ), 0 < n → ∀ x : H,
      ⟪covarianceOperator ν (∇ (g n) x), ∇ (g n) x⟫ ≤ A := by
    intro n hn x
    have hgrad : ∇ (g n) x = ((1 : ℝ) / (1 + (f x / n) ^ 2)) • ∇ f x := by
      unfold gradient
      rw [hgfderiv n hn x, map_smul]
    have hnn : (0 : ℝ) ≤ (1 : ℝ) / (1 + (f x / n) ^ 2) := by positivity
    have hle1 : (1 : ℝ) / (1 + (f x / n) ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [sq_nonneg (f x / n)]
    have hq0 : 0 ≤ ⟪covarianceOperator ν (∇ f x), ∇ f x⟫ :=
      LinearMap.IsPositive.inner_nonneg_left isPositive_covarianceOperator _
    rw [hgrad, map_smul, real_inner_smul_left, real_inner_smul_right]
    have hstep : (1 : ℝ) / (1 + (f x / n) ^ 2) * ((1 : ℝ) / (1 + (f x / n) ^ 2)
        * ⟪covarianceOperator ν (∇ f x), ∇ f x⟫)
          ≤ 1 * (1 * ⟪covarianceOperator ν (∇ f x), ∇ f x⟫) := by
      refine mul_le_mul hle1 ?_ (by positivity) zero_le_one
      exact mul_le_mul hle1 le_rfl hq0 zero_le_one
    rw [one_mul, one_mul] at hstep
    exact le_trans hstep (hA x)
  have hgbdd : ∀ (n : ℕ), ∀ x : H, |g n x| ≤ (n : ℝ) * (π / 2) := by
    intro n x
    rw [hgdef, abs_mul, Nat.abs_cast]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
    exact le_of_lt (abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩)
  have hgdom : ∀ (n : ℕ), ∀ x : H, |g n x| ≤ |f x| := by
    intro n x
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hgdef]
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    rw [hgdef, abs_mul, Nat.abs_cast]
    calc (n : ℝ) * |Real.arctan (f x / n)| ≤ (n : ℝ) * |f x / n| :=
          mul_le_mul_of_nonneg_left (abs_arctan_le _) (le_of_lt hn0)
      _ = |f x| := by
          rw [abs_div, Nat.abs_cast]
          field_simp
  have hgint : ∀ n : ℕ, Integrable (g n) ν := fun n =>
    Integrable.mono' hfint.abs ((hgC1 n).continuous.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hgdom n x)
  have hgtend : ∀ x : H, Filter.Tendsto (fun n : ℕ => g n x) Filter.atTop (nhds (f x)) :=
    fun x => tendsto_mul_arctan_div (f x)
  -- the truncated means converge
  have hmeantend : Filter.Tendsto (fun n : ℕ => ν[g n]) Filter.atTop (nhds c) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |f x|)
      (fun n => ((hgC1 n).continuous.aestronglyMeasurable)) hfint.abs
      (fun n => Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hgdom n x)
      (Filter.Eventually.of_forall hgtend)
  refine ⟨hexpint, fun t => ?_⟩
  -- the moment generating function converges too, and each truncation obeys the bound
  have hdomexp : ∀ᵐ x ∂ν, ∀ n : ℕ,
      ‖Real.exp (t * (g n x - ν[g n]))‖
        ≤ Real.exp (|t| * (|f 0| + K * ‖x‖ + ∫ y : H, |f y| ∂ν)) := by
    refine Filter.Eventually.of_forall fun x n => ?_
    have hmn : |ν[g n]| ≤ ∫ y : H, |f y| ∂ν := by
      calc |ν[g n]| ≤ ∫ y : H, |g n y| ∂ν := by
            simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := ν) (g n)
        _ ≤ ∫ y : H, |f y| ∂ν :=
            integral_mono (hgint n).abs hfint.abs fun y => hgdom n y
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    refine Real.exp_le_exp.mpr ?_
    calc t * (g n x - ν[g n]) ≤ |t| * |g n x - ν[g n]| := by
          rw [← abs_mul]; exact le_abs_self _
      _ ≤ |t| * (|f 0| + K * ‖x‖ + ∫ y : H, |f y| ∂ν) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg t)
          calc |g n x - ν[g n]| ≤ |g n x| + |ν[g n]| := abs_sub _ _
            _ ≤ |f x| + ∫ y : H, |f y| ∂ν := add_le_add (hgdom n x) hmn
            _ ≤ |f 0| + K * ‖x‖ + ∫ y : H, |f y| ∂ν := by linarith [hgrow x]
  have hdomint : Integrable
      (fun x : H => Real.exp (|t| * (|f 0| + K * ‖x‖ + ∫ y : H, |f y| ∂ν))) ν := by
    refine Integrable.mono'
      ((integrable_exp_mul_norm (μ := ν) (|t| * K)).const_mul
        (Real.exp (|t| * (|f 0| + ∫ y : H, |f y| ∂ν)))) (by fun_prop)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by ring_nf; rfl)
  have hmgftend : Filter.Tendsto
      (fun n : ℕ => ∫ x : H, Real.exp (t * (g n x - ν[g n])) ∂ν) Filter.atTop
      (nhds (∫ x : H, Real.exp (t * (f x - c)) ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => Real.exp (|t| * (|f 0| + K * ‖x‖ + ∫ y : H, |f y| ∂ν)))
      (fun n => by fun_prop) hdomint
      (fun n => (hdomexp.mono fun x hx => hx n))
      (Filter.Eventually.of_forall fun x => ?_)
    exact ((Real.continuous_exp.tendsto _).comp
      (((hgtend x).sub hmeantend).const_mul t))
  have hbound : ∀ n : ℕ, 0 < n →
      (∫ x : H, Real.exp (t * (g n x - ν[g n])) ∂ν) ≤ Real.exp (A * t ^ 2 / 2) := by
    intro n hn
    have hnegfderiv : ∀ x : H, fderiv ℝ (fun y : H => -g n y) x = -fderiv ℝ (g n) x := fun x =>
      (((hgC1 n).differentiable_one x).hasFDerivAt.neg).fderiv
    have hneggrad : ∀ x : H, ∇ (fun y : H => -g n y) x = -∇ (g n) x := by
      intro x
      unfold gradient
      rw [hnegfderiv x, map_neg]
    rcases le_or_gt 0 t with ht | ht
    · exact mgf_le_of_bounded_of_nonneg (ν := ν) hmean0 (hgC1 n) (hgK n hn) (hgA n hn)
        (hgbdd n) ht
    · have hneg := mgf_le_of_bounded_of_nonneg (ν := ν) hmean0 ((hgC1 n).neg)
        (K := K) (fun x => by
          rw [hnegfderiv x, norm_neg]
          exact hgK n hn x)
        (A := A) (fun x => by
          rw [hneggrad x, map_neg, inner_neg_neg]
          exact hgA n hn x)
        (M := (n : ℝ) * (π / 2)) (fun x => by simpa using hgbdd n x)
        (t := -t) (by linarith)
      have hmean : ν[fun x => -g n x] = -ν[g n] := by
        simpa using MeasureTheory.integral_neg (μ := ν) (g n)
      rw [hmean] at hneg
      have hcongr : (∫ x : H, Real.exp (-t * (-g n x - -ν[g n])) ∂ν)
          = ∫ x : H, Real.exp (t * (g n x - ν[g n])) ∂ν := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        ring_nf
      rw [hcongr] at hneg
      calc (∫ x : H, Real.exp (t * (g n x - ν[g n])) ∂ν)
          ≤ Real.exp (A * (-t) ^ 2 / 2) := hneg
        _ = Real.exp (A * t ^ 2 / 2) := by
            congr 1
            ring
  have hlim : (∫ x : H, Real.exp (t * (f x - c)) ∂ν) ≤ Real.exp (A * t ^ 2 / 2) :=
    le_of_tendsto hmgftend
      (Filter.eventually_atTop.mpr ⟨1, fun n hn => hbound n (by omega)⟩)
  calc mgf (fun x : H => f x - ν[f]) ν t
      = ∫ x : H, Real.exp (t * (f x - c)) ∂ν := rfl
    _ ≤ Real.exp (A * t ^ 2 / 2) := hlim
    _ = Real.exp ((A.toNNReal : ℝ) * t ^ 2 / 2) := by rw [Real.coe_toNNReal _ ha0]

/-- The operator-norm form of the concentration inequality: `⟪C ∇f, ∇f⟫ ≤ ‖C‖ K²`, so `f - 𝔼f` is
sub-Gaussian with parameter `‖C‖ K²`. Weaker than
`hasSubgaussianMGF_sub_integral_of_inner_covarianceOperator_le`, but stated in terms of `K`
alone. -/
theorem hasSubgaussianMGF_sub_integral_of_norm_fderiv_le
    (hmean0 : (∫ x : H, x ∂ν) = 0)
    {f : H → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ} (hK : ∀ x, ‖fderiv ℝ f x‖ ≤ K) :
    HasSubgaussianMGF (fun x : H => f x - ν[f])
      (‖covarianceOperator ν‖ * K ^ 2).toNNReal ν := by
  refine hasSubgaussianMGF_sub_integral_of_inner_covarianceOperator_le (ν := ν) hmean0 hf hK
    fun x => ?_
  have hnx : ‖∇ f x‖ ≤ K := by rw [norm_gradient]; exact hK x
  calc ⟪covarianceOperator ν (∇ f x), ∇ f x⟫
      ≤ ‖covarianceOperator ν (∇ f x)‖ * ‖∇ f x‖ := real_inner_le_norm _ _
    _ ≤ (‖covarianceOperator ν‖ * ‖∇ f x‖) * ‖∇ f x‖ :=
        mul_le_mul_of_nonneg_right ((covarianceOperator ν).le_opNorm _) (norm_nonneg _)
    _ ≤ (‖covarianceOperator ν‖ * K) * K := by
        have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hnx (norm_nonneg _)) hnx (norm_nonneg _)
          (by positivity)
    _ = ‖covarianceOperator ν‖ * K ^ 2 := by ring

/-- **Talagrand's Theorem 1.3.4**, one-sided form: a `C¹` functional of a centered Gaussian whose
Dirichlet density `⟪C ∇f, ∇f⟫` is at most `A` deviates above its mean with probability at most
`exp (-ε² / (2A))`. -/
theorem measure_ge_le_of_inner_covarianceOperator_le
    (hmean0 : (∫ x : H, x ∂ν) = 0)
    {f : H → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ} (hK : ∀ x, ‖fderiv ℝ f x‖ ≤ K)
    {A : ℝ} (hA : ∀ x, ⟪covarianceOperator ν (∇ f x), ∇ f x⟫ ≤ A)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ν.real {x : H | ε ≤ f x - ν[f]} ≤ Real.exp (-ε ^ 2 / (2 * A.toNNReal)) := by
  simpa using
    (hasSubgaussianMGF_sub_integral_of_inner_covarianceOperator_le (ν := ν) hmean0 hf hK
      hA).measure_ge_le hε

/-- **Talagrand's Theorem 1.3.4**, two-sided form. -/
theorem measure_abs_ge_le_of_inner_covarianceOperator_le
    (hmean0 : (∫ x : H, x ∂ν) = 0)
    {f : H → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ} (hK : ∀ x, ‖fderiv ℝ f x‖ ≤ K)
    {A : ℝ} (hA : ∀ x, ⟪covarianceOperator ν (∇ f x), ∇ f x⟫ ≤ A)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ν.real {x : H | ε ≤ |f x - ν[f]|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * A.toNNReal)) := by
  have hsub :=
    hasSubgaussianMGF_sub_integral_of_inner_covarianceOperator_le (ν := ν) hmean0 hf hK hA
  have hpos : ν.real {x : H | ε ≤ f x - ν[f]}
      ≤ Real.exp (-ε ^ 2 / (2 * A.toNNReal)) := by
    simpa using hsub.measure_ge_le hε
  have hneg : ν.real {x : H | ε ≤ -(f x - ν[f])}
      ≤ Real.exp (-ε ^ 2 / (2 * A.toNNReal)) := by
    simpa using hsub.neg.measure_ge_le hε
  have hsubset : {x : H | ε ≤ |f x - ν[f]|}
      ⊆ {x : H | ε ≤ f x - ν[f]} ∪ {x : H | ε ≤ -(f x - ν[f])} := by
    intro x hx
    rcases abs_cases (f x - ν[f]) with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl (by simpa [h1] using hx)
    · exact Or.inr (by simpa [h1] using hx)
  calc ν.real {x : H | ε ≤ |f x - ν[f]|}
      ≤ ν.real ({x : H | ε ≤ f x - ν[f]} ∪ {x : H | ε ≤ -(f x - ν[f])}) :=
        measureReal_mono hsubset
    _ ≤ ν.real {x : H | ε ≤ f x - ν[f]} + ν.real {x : H | ε ≤ -(f x - ν[f])} :=
        measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-ε ^ 2 / (2 * A.toNNReal)) := by linarith

end Hilbert

end IsGaussian

end ProbabilityTheory
