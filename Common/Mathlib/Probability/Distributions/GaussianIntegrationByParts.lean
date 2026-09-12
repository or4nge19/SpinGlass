/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.Distributions.Gaussian.IntegrationByParts
import Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinFernique
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Common.Mathlib.Probability.Distributions.Gaussian.ExpGrowth

/-!
# Gaussian IBP for `gaussianReal`

One-dimensional IBP for `gaussianReal μ v`, from `cameronMartin_integral_by_parts_polyGrowth`.
Main: `gaussian_integration_by_parts_general`, `stein_lemma_gaussianReal`,
`gaussianRV_integration_by_parts`.
-/

open MeasureTheory Filter
open scoped Topology Real NNReal ENNReal ProbabilityTheory

namespace ProbabilityTheory

/-! ### `cmCoe` for the identity dual on `ℝ` -/

/-! ### Integrability for `gaussianReal` -/

/-- The degenerate Gaussian `gaussianReal μ 0` is the Dirac measure at `μ`. -/
@[simp] lemma gaussianReal_dirac (μ : ℝ) : gaussianReal μ 0 = Measure.dirac μ := by
  simp

/-- For a centered real Gaussian, the square is integrable. -/
lemma integrable_sq_gaussianReal_centered (v : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := by
  have : IsGaussian (gaussianReal (0 : ℝ) v) := by infer_instance
  simpa [Real.norm_eq_abs, pow_two, sq_abs] using
    (IsGaussian.integrable_norm_pow (μ := gaussianReal (0 : ℝ) v) 2)

/-- For a centered real Gaussian, all polynomial weights `(1 + |x|)^k` are integrable. -/
lemma gaussianReal_integrable_one_add_abs_pow_centered (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ k) (gaussianReal 0 v) := by
  have : IsGaussian (gaussianReal (0 : ℝ) v) := by infer_instance
  simpa [Real.norm_eq_abs] using
    (IsGaussian.integrable_one_add_norm_pow (μ := gaussianReal (0 : ℝ) v) k)

private noncomputable def idDual : StrongDual ℝ ℝ :=
  (ContinuousLinearMap.id ℝ ℝ)

private lemma idDual_cmCoe_cmOfDual_eq_sq_norm (μ : Measure ℝ) [IsGaussian μ] :
    idDual (cmCoe (μ := μ) (cmOfDual (μ := μ) idDual)) = ‖cmOfDual (μ := μ) idDual‖ ^ 2 := by
  simpa [real_inner_self_eq_norm_sq] using
    (apply_cmCoe_eq_inner (μ := μ) (x := (cmOfDual (μ := μ) idDual)) (L := idDual))

private lemma sq_norm_cmOfDual_idDual_eq_var (μ : Measure ℝ) [IsGaussian μ] :
    ‖cmOfDual (μ := μ) idDual‖ ^ 2 = (Var[idDual; μ] : ℝ) := by
  simpa using (sq_norm_cmOfDual (μ := μ) idDual)

private lemma var_idDual_gaussianReal (μ : ℝ) (v : ℝ≥0) : Var[idDual; gaussianReal μ v] = v := by
  simp [idDual]

private lemma cmCoe_cmOfDual_idDual_gaussianReal (μ : ℝ) (v : ℝ≥0) :
    cmCoe (μ := gaussianReal μ v) (cmOfDual (μ := gaussianReal μ v) idDual) = (v : ℝ) := by
  let μR : Measure ℝ := gaussianReal μ v
  have : IsGaussian μR := by infer_instance
  have hVar' : (Var[idDual; μR] : ℝ) = (v : ℝ) := by
    exact_mod_cast (var_idDual_gaussianReal μ v)
  have : idDual (cmCoe (μ := μR) (cmOfDual (μ := μR) idDual)) = (v : ℝ) := by
    calc
      idDual (cmCoe (μ := μR) (cmOfDual (μ := μR) idDual))
          = ‖cmOfDual (μ := μR) idDual‖ ^ 2 := idDual_cmCoe_cmOfDual_eq_sq_norm (μ := μR)
      _ = (Var[idDual; μR] : ℝ) := sq_norm_cmOfDual_idDual_eq_var (μ := μR)
      _ = (v : ℝ) := hVar'
  simpa [idDual] using this

private lemma gaussianReal_polyGrowth_norm
    {F : ℝ → ℝ} {C : ℝ} {m : ℕ} (hF_growth : ∀ x, |F x| ≤ C * (1 + |x|) ^ m) :
    ∀ x, ‖F x‖ ≤ C * (1 + ‖x‖) ^ m := by
  intro x
  simpa [Real.norm_eq_abs] using hF_growth x

private lemma gaussianReal_polyGrowth_fderiv_norm
    {F : ℝ → ℝ} {C : ℝ} {m : ℕ} (hF'_growth : ∀ x, |deriv F x| ≤ C * (1 + |x|) ^ m) :
    ∀ x, ‖fderiv ℝ F x‖ ≤ C * (1 + ‖x‖) ^ m := by
  intro x
  have hn : ‖fderiv ℝ F x‖ = ‖deriv F x‖ := by
    simpa using (norm_deriv_eq_norm_fderiv (f := F) (x := x)).symm
  simpa [hn, Real.norm_eq_abs] using hF'_growth x

private lemma gaussianReal_cmOfDual_idDual_ae (μ : ℝ) (v : ℝ≥0) :
    (fun x : ℝ => (cmOfDual (μ := gaussianReal μ v) idDual) x) =ᵐ[gaussianReal μ v] fun x => x - μ
      := by
  let μR : Measure ℝ := gaussianReal μ v
  have hmean : (∫ x : ℝ, x ∂μR) = μ := by simp [μR]
  have hcent' :=
    (StrongDual.centeredToLp_apply (μ := μR) (E := ℝ) (h := memLp_two_id) idDual)
  filter_upwards [hcent'] with x hx
  simpa [idDual, hmean, cmOfDual_apply] using hx

private lemma gaussianReal_integral_cmOfDual_idDual_mul
    (μ : ℝ) (v : ℝ≥0) (F : ℝ → ℝ) :
    (∫ x, ((cmOfDual (μ := gaussianReal μ v) idDual) x) * F x ∂(gaussianReal μ v))
      = ∫ x, (x - μ) * F x ∂(gaussianReal μ v) := by
  refine integral_congr_ae ?_
  filter_upwards [gaussianReal_cmOfDual_idDual_ae (μ := μ) (v := v)] with x hx
  simp [hx, mul_comm]

private lemma gaussianReal_integral_fderiv_cmCoe_idDual
    (μ : ℝ) (v : ℝ≥0) (F : ℝ → ℝ) :
    (∫ x, (fderiv ℝ F x) (cmCoe (μ := gaussianReal μ v) (cmOfDual (μ := gaussianReal μ v) idDual))
        ∂(gaussianReal μ v))
      = (v : ℝ) * ∫ x, deriv F x ∂(gaussianReal μ v) := by
  let μR : Measure ℝ := gaussianReal μ v
  have hcm : cmCoe (μ := μR) (cmOfDual (μ := μR) idDual) = (v : ℝ) :=
    cmCoe_cmOfDual_idDual_gaussianReal μ v
  calc
    (∫ x, (fderiv ℝ F x) (cmCoe (μ := μR) (cmOfDual (μ := μR) idDual)) ∂μR)
        = ∫ x, (deriv F x) * (v : ℝ) ∂μR := by
              refine integral_congr_ae (ae_of_all _ (fun x => ?_))
              simp [hcm, mul_comm]
    _ = (v : ℝ) * ∫ x, deriv F x ∂μR := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (integral_mul_const (μ := μR) (r := (v : ℝ)) (f := fun x : ℝ => deriv F x))

private lemma hasLaw_integral_comp
    {Ω : Type*} [MeasureSpace Ω] {P : Measure Ω} {g : Ω → ℝ} {v : ℝ≥0}
    (hg : HasLaw g (gaussianReal 0 v) P) {f : ℝ → ℝ} (hf : Integrable f (gaussianReal 0 v)) :
    (∫ ω, f (g ω) ∂P) = ∫ x, f x ∂(gaussianReal 0 v) := by
  simpa [Function.comp_def] using (hg.integral_comp (f := f) (hf := hf.aestronglyMeasurable))

private lemma abs_id_mul_polyGrowth_bound
    {F : ℝ → ℝ} {C : ℝ} {m : ℕ} (hF_growth : ∀ x, |F x| ≤ C * (1 + |x|) ^ m) :
    ∀ x, |x * F x| ≤ C * (1 + |x|) ^ (m + 1) := by
  intro x
  have hx : |x| ≤ 1 + |x| := by nlinarith [abs_nonneg x]
  calc
    |x * F x| = |x| * |F x| := by simp [abs_mul]
    _ ≤ (1 + |x|) * |F x| := by
          simpa [mul_assoc] using (mul_le_mul_of_nonneg_right hx (abs_nonneg (F x)))
    _ ≤ (1 + |x|) * (C * (1 + |x|) ^ m) := by
          exact mul_le_mul_of_nonneg_left (hF_growth x) (by nlinarith [abs_nonneg x])
    _ = C * (1 + |x|) ^ (m + 1) := by
          simp [pow_succ, mul_left_comm, mul_comm, add_comm]

private lemma integrable_id_mul_polyGrowth
    {v : ℝ≥0} {F : ℝ → ℝ} (hF_meas : Measurable F) {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ x, |F x| ≤ C * (1 + |x|) ^ m) :
    Integrable (fun x : ℝ => x * F x) (gaussianReal 0 v) := by
  have : IsGaussian (gaussianReal (0 : ℝ) v) := by infer_instance
  have hmeas : Measurable (fun x : ℝ => x * F x) := measurable_id.mul hF_meas
  refine IsGaussian.integrable_of_abs_le_mul_one_add_norm_pow (μ := gaussianReal (0 : ℝ) v) hmeas
    (C := C) (m := m + 1) hC ?_
  intro x
  simpa [Real.norm_eq_abs] using (abs_id_mul_polyGrowth_bound (F := F) (C := C) (m := m) hF_growth
    x)

private lemma integrable_deriv_polyGrowth
    {v : ℝ≥0} {F : ℝ → ℝ} (hF_c1 : ContDiff ℝ 1 F) {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF'_growth : ∀ x, |deriv F x| ≤ C * (1 + |x|) ^ m) :
    Integrable (fun x : ℝ => deriv F x) (gaussianReal 0 v) := by
  have : IsGaussian (gaussianReal (0 : ℝ) v) := by infer_instance
  have hmeas : Measurable (fun x : ℝ => deriv F x) := (hF_c1.continuous_deriv_one).measurable
  refine IsGaussian.integrable_of_abs_le_mul_one_add_norm_pow (μ := gaussianReal (0 : ℝ) v) hmeas
    (C := C) (m := m) hC (by intro x; simpa using hF'_growth x)

/-! ### Measure-level IBP -/

/-- **Gaussian integration by parts** for `gaussianReal μ v`. -/
theorem gaussian_integration_by_parts_general
    {μ : ℝ} {v : ℝ≥0} {F : ℝ → ℝ}
    (hF_meas : Measurable F)
    (hF_c1 : ContDiff ℝ 1 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ x, |F x| ≤ C * (1 + |x|) ^ m)
    (hF'_growth : ∀ x, |deriv F x| ≤ C * (1 + |x|) ^ m) :
    ∫ x, (x - μ) * F x ∂(gaussianReal μ v)
      = (v : ℝ) * ∫ x, deriv F x ∂(gaussianReal μ v) := by
  let μR : Measure ℝ := gaussianReal μ v
  have : IsGaussian μR := by infer_instance
  calc
    ∫ x, (x - μ) * F x ∂μR
        = ∫ x, ((cmOfDual (μ := μR) idDual) x) * F x ∂μR := by
            simpa [μR] using (gaussianReal_integral_cmOfDual_idDual_mul (μ := μ) (v := v) (F :=
              F)).symm
    _ = ∫ x, (fderiv ℝ F x) (cmCoe (μ := μR) (cmOfDual (μ := μR) idDual)) ∂μR := by
          simpa using
            (cameronMartin_integral_by_parts_polyGrowth (μ := μR) (x := (cmOfDual (μ := μR) idDual))
              (F := F) hF_meas hF_c1 hC
              (gaussianReal_polyGrowth_norm (F := F) (C := C) (m := m) hF_growth)
              (gaussianReal_polyGrowth_fderiv_norm (F := F) (C := C) (m := m) hF'_growth))
    _ = (v : ℝ) * ∫ x, deriv F x ∂μR := by
            simpa [μR] using gaussianReal_integral_fderiv_cmCoe_idDual (μ := μ) (v := v) (F := F)

/-- **Stein's lemma** for the centered Gaussian law `gaussianReal 0 v`. -/
theorem stein_lemma_gaussianReal
    {v : ℝ≥0} {F : ℝ → ℝ}
    (hF_meas : Measurable F)
    (hF_c1 : ContDiff ℝ 1 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ x, |F x| ≤ C * (1 + |x|) ^ m)
    (hF'_growth : ∀ x, |deriv F x| ≤ C * (1 + |x|) ^ m) :
    ∫ x, x * F x ∂(gaussianReal 0 v)
      = (v : ℝ) * ∫ x, deriv F x ∂(gaussianReal 0 v) := by
  simpa using
    (gaussian_integration_by_parts_general (μ := (0 : ℝ)) (v := v) (F := F)
      hF_meas hF_c1 hC hF_growth hF'_growth)

/-- Alias of `stein_lemma_gaussianReal`. -/
lemma gaussianReal_integration_by_parts
    {F : ℝ → ℝ} {v : ℝ≥0}
    (hF_meas : Measurable F)
    (hF_c1 : ContDiff ℝ 1 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ x, |F x| ≤ C * (1 + |x|) ^ m)
    (hF'_growth : ∀ x, |deriv F x| ≤ C * (1 + |x|) ^ m) :
    ∫ x, x * F x ∂(gaussianReal 0 v)
      = (v : ℝ) * ∫ x, deriv F x ∂(gaussianReal 0 v) :=
  stein_lemma_gaussianReal (v := v) (F := F) hF_meas hF_c1 hC hF_growth hF'_growth

/-- **Stein's lemma for functions of exponential growth**: `∫ x F(x) dγ_v = v ∫ F'(x) dγ_v` for
`F ∈ C¹` with `F` and `F'` of exponential growth. -/
theorem stein_lemma_gaussianReal_of_expGrowth {v : ℝ≥0} {F : ℝ → ℝ} (hF_meas : Measurable F)
    (hF_c1 : ContDiff ℝ 1 F) (hF : HasExpGrowth F) (hF' : HasExpGrowth (deriv F)) :
    ∫ x, x * F x ∂(gaussianReal 0 v) = (v : ℝ) * ∫ x, deriv F x ∂(gaussianReal 0 v) := by
  have : IsGaussian (gaussianReal (0 : ℝ) v) := by infer_instance
  have hF_int : Integrable F (gaussianReal 0 v) :=
    hF.integrable_gaussianReal hF_meas.aestronglyMeasurable
  obtain ⟨C, c, hc, hFb⟩ := hF
  obtain ⟨C', c', hc', hF'b⟩ := hF'
  have hC := HasExpGrowth.nonneg_of_bound hFb
  have hC' := HasExpGrowth.nonneg_of_bound hF'b
  have hcm : cmCoe (μ := gaussianReal 0 v) (cmOfDual (μ := gaussianReal 0 v) idDual) = (v : ℝ) :=
    cmCoe_cmOfDual_idDual_gaussianReal 0 v
  have hv0 : (0 : ℝ) ≤ v := NNReal.coe_nonneg v
  -- the bound on the derivative along the Cameron–Martin shift
  have hbound_int : Integrable (fun y : ℝ => ((v : ℝ) * C' * Real.exp (c' * v))
      * Real.exp (c' * |y|)) (gaussianReal 0 v) :=
    (integrable_exp_mul_abs_gaussianReal 0 v c').const_mul _
  have hIBP : (∫ y, (cmOfDual (μ := gaussianReal 0 v) idDual) y * F y ∂(gaussianReal 0 v))
      = ∫ y, (fderiv ℝ F y) (cmCoe (μ := gaussianReal 0 v)
          (cmOfDual (μ := gaussianReal 0 v) idDual)) ∂(gaussianReal 0 v) := by
    refine cameronMartin_integral_by_parts_of_integrable_bound (μ := gaussianReal 0 v)
      (cmOfDual (μ := gaussianReal 0 v) idDual) F hF_meas hF_c1 one_pos hF_int _ hbound_int ?_ ?_
    · refine Filter.Eventually.of_forall fun y t ht => ?_
      rw [hcm, fderiv_eq_smul_deriv, smul_eq_mul, smul_eq_mul, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hv0]
      have ht' : |t| < 1 := by simpa [Real.dist_eq] using ht
      have h1 : |y + t * v| ≤ |y| + v := by
        calc |y + t * v| ≤ |y| + |t * v| := abs_add_le _ _
          _ ≤ |y| + v := by
              rw [abs_mul, abs_of_nonneg hv0]
              nlinarith [abs_nonneg t]
      calc (v : ℝ) * |deriv F (y + t * v)|
          ≤ v * (C' * Real.exp (c' * |y + t * v|)) :=
            mul_le_mul_of_nonneg_left (hF'b _) hv0
        _ ≤ v * (C' * Real.exp (c' * (|y| + v))) := by
            gcongr
        _ = (v : ℝ) * C' * Real.exp (c' * v) * Real.exp (c' * |y|) := by
            rw [mul_add, Real.exp_add]; ring
    · -- the tilt integrability: `|F y| (|y| + 1) e^{|y|}` is Gaussian-integrable
      set K : ℝ := 1 * ((‖cmOfDual (μ := gaussianReal 0 v) idDual‖₊ : ℝ) ^ 2) + 1 with hK
      have hK0 : 0 ≤ K := by positivity
      have hg : Integrable (fun y : ℝ => |F y| * K * ((|y| + 1) * Real.exp (1 * |y|)))
          (gaussianReal 0 v) := by
        refine ((integrable_exp_mul_abs_gaussianReal 0 v (c + 2)).const_mul (C * K)).mono'
          (((continuous_abs.measurable.comp hF_meas).mul_const K).mul
            ((continuous_abs.add continuous_const).mul
            (Real.continuous_exp.comp (continuous_const.mul continuous_abs))).measurable
            |>.aestronglyMeasurable) (Filter.Eventually.of_forall fun y => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have e1 : |y| + 1 ≤ Real.exp |y| := by linarith [Real.add_one_le_exp |y|]
        have e2 : Real.exp (1 * |y|) = Real.exp |y| := by rw [one_mul]
        rw [e2]
        calc |F y| * K * ((|y| + 1) * Real.exp |y|)
            ≤ (C * Real.exp (c * |y|)) * K * (Real.exp |y| * Real.exp |y|) := by
              gcongr
              exact hFb y
          _ = C * K * Real.exp ((c + 2) * |y|) := by
              rw [show (c + 2) * |y| = c * |y| + |y| + |y| by ring, Real.exp_add, Real.exp_add]
              ring
      refine hg.congr ?_
      filter_upwards [gaussianReal_cmOfDual_idDual_ae (μ := 0) (v := v)] with y hy
      rw [hy, sub_zero]
  calc ∫ x, x * F x ∂(gaussianReal 0 v)
      = ∫ x, ((cmOfDual (μ := gaussianReal 0 v) idDual) x) * F x ∂(gaussianReal 0 v) := by
        simpa using (gaussianReal_integral_cmOfDual_idDual_mul (μ := 0) (v := v) (F := F)).symm
    _ = ∫ x, (fderiv ℝ F x) (cmCoe (μ := gaussianReal 0 v)
          (cmOfDual (μ := gaussianReal 0 v) idDual)) ∂(gaussianReal 0 v) := hIBP
    _ = (v : ℝ) * ∫ x, deriv F x ∂(gaussianReal 0 v) :=
        gaussianReal_integral_fderiv_cmCoe_idDual (μ := 0) (v := v) (F := F)

/-- Stein's lemma for functions of exponential growth, with an explicit derivative. -/
theorem stein_lemma_gaussianReal_of_expGrowth' {v : ℝ≥0} {F F' : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (F' x) x) (hF'c : Continuous F') (hFg : HasExpGrowth F)
    (hF'g : HasExpGrowth F') :
    ∫ x, x * F x ∂(gaussianReal 0 v) = (v : ℝ) * ∫ x, F' x ∂(gaussianReal 0 v) := by
  have hderiv : deriv F = F' := funext fun x => (hF x).deriv
  have hF_meas : Measurable F :=
    (continuous_iff_continuousAt.2 fun y => (hF y).continuousAt).measurable
  have hF_c1 : ContDiff ℝ 1 F := by
    rw [contDiff_one_iff_deriv]
    exact ⟨fun x => (hF x).differentiableAt, hderiv ▸ hF'c⟩
  have := stein_lemma_gaussianReal_of_expGrowth (v := v) hF_meas hF_c1 hFg (hderiv ▸ hF'g)
  rwa [hderiv] at this

/-- Random-variable version of `stein_lemma_gaussianReal`, transported via `HasLaw`. -/
theorem gaussianRV_integration_by_parts
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {g : Ω → ℝ} {v : ℝ≥0}
    (hg : HasLaw g (gaussianReal 0 v) (ℙ : Measure Ω))
    {F : ℝ → ℝ}
    (hF_meas : Measurable F)
    (hF_c1 : ContDiff ℝ 1 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ x, |F x| ≤ C * (1 + |x|) ^ m)
    (hF'_growth : ∀ x, |deriv F x| ≤ C * (1 + |x|) ^ m) :
    ∫ ω, g ω * F (g ω) ∂ℙ
      = (v : ℝ) * ∫ ω, deriv F (g ω) ∂ℙ := by
  have hInt_xF : Integrable (fun x : ℝ => x * F x) (gaussianReal 0 v) :=
    integrable_id_mul_polyGrowth (v := v) (F := F) hF_meas hC hF_growth
  have hInt_dF : Integrable (fun x : ℝ => deriv F x) (gaussianReal 0 v) :=
    integrable_deriv_polyGrowth (v := v) (F := F) hF_c1 hC hF'_growth
  have hdF' :
      (∫ x, deriv F x ∂(gaussianReal 0 v)) = ∫ ω, deriv F (g ω) ∂ℙ := by
    simpa using (hasLaw_integral_comp (hg := hg) (f := fun x => deriv F x) hInt_dF).symm
  calc
    ∫ ω, g ω * F (g ω) ∂ℙ
        = ∫ x, x * F x ∂(gaussianReal 0 v) := by
              simpa using (hasLaw_integral_comp (hg := hg) (f := fun x => x * F x) hInt_xF)
    _ = (v : ℝ) * ∫ x, deriv F x ∂(gaussianReal 0 v) :=
          stein_lemma_gaussianReal (v := v) (F := F) hF_meas hF_c1 hC hF_growth hF'_growth
    _ = (v : ℝ) * ∫ ω, deriv F (g ω) ∂ℙ := by simp [hdF']

end ProbabilityTheory
