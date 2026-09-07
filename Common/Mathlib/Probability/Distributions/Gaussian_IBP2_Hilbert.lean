/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.Distributions.Gaussian_IBP_Hilbert

/-!
# Second-order Gaussian integration by parts (Price's theorem) on Hilbert space

For a centered Gaussian measure `μ` on a real Hilbert space `H` with covariance operator
`C = covarianceOperator μ`, and `F : H → ℝ` of class `C²` with polynomial growth of `F`, `DF` and
`D²F`,

`∫ ⟪x,h⟫ ⟪x,k⟫ F x ∂μ = ⟪C h, k⟫ ∫ F ∂μ + ∫ (D²F x) (C k) (C h) ∂μ`.

This is the second-order Gaussian integration-by-parts formula (Price's theorem, the
Gaussian-process form of Wick's theorem). It is obtained by applying the first-order formula
`IsGaussian.integral_inner_mul_eq_integral_fderiv_covarianceOperator` twice: once to
`x ↦ ⟪x,k⟫ F x`, then to the directional derivative `x ↦ (DF x) (C h)`.

Talagrand uses this identity as the engine of every interpolation computation: it is what turns
`d/dt 𝔼 F(√t X + √(1-t) Y)` into a covariance-weighted trace of the Hessian
(Vol. I, §1.3 and Appendix A.3; Vol. II, §8.2).

## Main statements

- `IsGaussian.integral_inner_mul_inner_mul_eq_covariance_add_integral_fderiv2`: Price's theorem.
- `IsGaussian.integral_inner_mul_inner_mul_eq_integral_fderiv2_of_integral_eq_zero`: the
  centered-`F` form, in which the first term drops out.
-/

open scoped Filter BigOperators Topology ProbabilityTheory ENNReal InnerProductSpace NNReal
open MeasureTheory Filter Set

noncomputable section

namespace ProbabilityTheory

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {μ : Measure H} [IsGaussian μ]

/-! ### The auxiliary function `x ↦ ⟪x,k⟫ * F x` -/

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
/-- `fun x ↦ ⟪x, k⟫` is the continuous linear functional `innerSL ℝ k`. -/
private lemma inner_right_eq_innerSL (k : H) :
    (fun x : H => ⟪x, k⟫_ℝ) = fun x : H => (innerSL ℝ k) x := by
  funext x
  exact real_inner_comm _ _

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
/-- Product rule for `x ↦ ⟪x,k⟫ * F x`. -/
private lemma hasFDerivAt_inner_right_mul {F : H → ℝ} {F' : H →L[ℝ] ℝ} {x : H}
    (hF : HasFDerivAt F F' x) (k : H) :
    HasFDerivAt (fun y : H => ⟪y, k⟫_ℝ * F y)
      (⟪x, k⟫_ℝ • F' + F x • (innerSL ℝ k)) x := by
  have hlin : HasFDerivAt (fun y : H => ⟪y, k⟫_ℝ) (innerSL ℝ k) x := by
    rw [inner_right_eq_innerSL k]
    exact (innerSL ℝ k).hasFDerivAt
  exact hlin.mul hF

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
/-- `|⟪x,k⟫| ≤ ‖k‖ * (1 + ‖x‖)`. -/
private lemma abs_inner_le (k x : H) : |⟪x, k⟫_ℝ| ≤ ‖k‖ * (1 + ‖x‖) := by
  have h1 : |⟪x, k⟫_ℝ| ≤ ‖x‖ * ‖k‖ := abs_real_inner_le_norm x k
  have h2 : ‖x‖ * ‖k‖ ≤ ‖k‖ * (1 + ‖x‖) := by
    have : ‖x‖ ≤ 1 + ‖x‖ := by linarith
    calc ‖x‖ * ‖k‖ = ‖k‖ * ‖x‖ := mul_comm _ _
      _ ≤ ‖k‖ * (1 + ‖x‖) := by
          exact mul_le_mul_of_nonneg_left this (norm_nonneg k)
  exact h1.trans h2

/-! ### Price's theorem -/

namespace IsGaussian

variable (μ)

/-- **Second-order Gaussian integration by parts (Price's theorem).** For a centered Gaussian `μ`
on a real Hilbert space and `F` of class `C²` with polynomial growth of `F`, `DF` and `D²F`,

`∫ ⟪x,h⟫ ⟪x,k⟫ F x ∂μ = ⟪C h, k⟫ ∫ F ∂μ + ∫ (D²F x) (C k) (C h) ∂μ`

where `C = covarianceOperator μ`. Talagrand Vol. I, Appendix A.3. -/
theorem integral_inner_mul_inner_mul_eq_covariance_add_integral_fderiv2
    (hmean0 : (∫ x : H, x ∂μ) = 0) (h k : H)
    (F : H → ℝ) (hF_meas : Measurable F) (hF_c2 : ContDiff ℝ 2 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ x, |F x| ≤ C * (1 + ‖x‖) ^ m)
    (hF'_growth : ∀ x, ‖fderiv ℝ F x‖ ≤ C * (1 + ‖x‖) ^ m)
    (hF''_growth : ∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ C * (1 + ‖x‖) ^ m) :
    (∫ x : H, ⟪x, h⟫_ℝ * (⟪x, k⟫_ℝ * F x) ∂μ)
      = ⟪covarianceOperator μ h, k⟫_ℝ * (∫ x : H, F x ∂μ)
        + ∫ x : H, ((fderiv ℝ (fderiv ℝ F) x) (covarianceOperator μ k))
            (covarianceOperator μ h) ∂μ := by
  classical
  have hFdiff : ∀ x : H, HasFDerivAt F (fderiv ℝ F x) x := fun x =>
    (hF_c2.differentiable (by norm_num) x).hasFDerivAt
  have hFc1 : ContDiff ℝ 1 F := hF_c2.of_le (by norm_num)
  have hDFc1 : ContDiff ℝ 1 (fderiv ℝ F) := hF_c2.fderiv_right (by norm_num)
  -- ## Step 1: first-order IBP applied to `G x = ⟪x,k⟫ * F x`.
  have hG_meas : Measurable (fun x : H => ⟪x, k⟫_ℝ * F x) := by
    have : Measurable (fun x : H => ⟪x, k⟫_ℝ) := by
      rw [inner_right_eq_innerSL k]; exact (innerSL ℝ k).continuous.measurable
    exact this.mul hF_meas
  have hG_c1 : ContDiff ℝ 1 (fun x : H => ⟪x, k⟫_ℝ * F x) := by
    have hlin : ContDiff ℝ 1 (fun x : H => ⟪x, k⟫_ℝ) := by
      rw [inner_right_eq_innerSL k]; exact (innerSL ℝ k).contDiff
    exact hlin.mul hFc1
  have hG_fderiv : ∀ x : H, fderiv ℝ (fun y : H => ⟪y, k⟫_ℝ * F y) x
      = ⟪x, k⟫_ℝ • fderiv ℝ F x + F x • (innerSL ℝ k) := fun x =>
    (hasFDerivAt_inner_right_mul (hFdiff x) k).fderiv
  -- Growth bounds for `G` and `DG`, with constant `2 C (1 + ‖k‖)` and degree `m + 1`.
  have hCk' : (0 : ℝ) ≤ 2 * C * (1 + ‖k‖) := by positivity
  have hG_growth : ∀ x : H, |⟪x, k⟫_ℝ * F x| ≤ (2 * C * (1 + ‖k‖)) * (1 + ‖x‖) ^ (m + 1) := by
    intro x
    have hb : (0 : ℝ) ≤ (1 + ‖x‖) ^ m := by positivity
    calc |⟪x, k⟫_ℝ * F x| = |⟪x, k⟫_ℝ| * |F x| := abs_mul _ _
      _ ≤ (‖k‖ * (1 + ‖x‖)) * (C * (1 + ‖x‖) ^ m) := by
          exact mul_le_mul (abs_inner_le k x) (hF_growth x) (abs_nonneg _)
            (by positivity)
      _ ≤ (2 * C * (1 + ‖k‖)) * (1 + ‖x‖) ^ (m + 1) := by
          have h1 : ‖k‖ ≤ 1 + ‖k‖ := by linarith [norm_nonneg k]
          have : (‖k‖ * (1 + ‖x‖)) * (C * (1 + ‖x‖) ^ m)
              = (C * ‖k‖) * (1 + ‖x‖) ^ (m + 1) := by ring
          rw [this]
          have hstep : C * ‖k‖ ≤ 2 * C * (1 + ‖k‖) := by nlinarith [norm_nonneg k]
          exact mul_le_mul_of_nonneg_right hstep (by positivity)
  have hG'_growth : ∀ x : H, ‖fderiv ℝ (fun y : H => ⟪y, k⟫_ℝ * F y) x‖
      ≤ (2 * C * (1 + ‖k‖)) * (1 + ‖x‖) ^ (m + 1) := by
    intro x
    rw [hG_fderiv x]
    have hsplit : ‖⟪x, k⟫_ℝ • fderiv ℝ F x + F x • (innerSL ℝ k)‖
        ≤ |⟪x, k⟫_ℝ| * ‖fderiv ℝ F x‖ + |F x| * ‖k‖ := by
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖⟪x, k⟫_ℝ • fderiv ℝ F x‖ = |⟪x, k⟫_ℝ| * ‖fderiv ℝ F x‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      have h2 : ‖F x • (innerSL ℝ k : H →L[ℝ] ℝ)‖ = |F x| * ‖k‖ := by
        rw [norm_smul, Real.norm_eq_abs, innerSL_apply_norm]
      rw [h1, h2]
    refine hsplit.trans ?_
    have hb : (0 : ℝ) ≤ (1 + ‖x‖) ^ m := by positivity
    have t1 : |⟪x, k⟫_ℝ| * ‖fderiv ℝ F x‖ ≤ (C * ‖k‖) * (1 + ‖x‖) ^ (m + 1) := by
      have := mul_le_mul (abs_inner_le k x) (hF'_growth x) (norm_nonneg _) (by positivity)
      calc |⟪x, k⟫_ℝ| * ‖fderiv ℝ F x‖
          ≤ (‖k‖ * (1 + ‖x‖)) * (C * (1 + ‖x‖) ^ m) := this
        _ = (C * ‖k‖) * (1 + ‖x‖) ^ (m + 1) := by ring
    have t2 : |F x| * ‖k‖ ≤ (C * ‖k‖) * (1 + ‖x‖) ^ (m + 1) := by
      have h1 : |F x| * ‖k‖ ≤ (C * (1 + ‖x‖) ^ m) * ‖k‖ :=
        mul_le_mul_of_nonneg_right (hF_growth x) (norm_nonneg k)
      have h2 : (C * (1 + ‖x‖) ^ m) * ‖k‖ ≤ (C * ‖k‖) * (1 + ‖x‖) ^ (m + 1) := by
        have hmono : (1 + ‖x‖) ^ m ≤ (1 + ‖x‖) ^ (m + 1) := by
          refine pow_le_pow_right₀ ?_ (Nat.le_succ m)
          linarith [norm_nonneg x]
        calc (C * (1 + ‖x‖) ^ m) * ‖k‖ = (C * ‖k‖) * (1 + ‖x‖) ^ m := by ring
          _ ≤ (C * ‖k‖) * (1 + ‖x‖) ^ (m + 1) := by
              exact mul_le_mul_of_nonneg_left hmono (by positivity)
      exact h1.trans h2
    have : (C * ‖k‖) * (1 + ‖x‖) ^ (m + 1) + (C * ‖k‖) * (1 + ‖x‖) ^ (m + 1)
        ≤ (2 * C * (1 + ‖k‖)) * (1 + ‖x‖) ^ (m + 1) := by
      have hstep : C * ‖k‖ + C * ‖k‖ ≤ 2 * C * (1 + ‖k‖) := by nlinarith [norm_nonneg k]
      calc (C * ‖k‖) * (1 + ‖x‖) ^ (m + 1) + (C * ‖k‖) * (1 + ‖x‖) ^ (m + 1)
          = (C * ‖k‖ + C * ‖k‖) * (1 + ‖x‖) ^ (m + 1) := by ring
        _ ≤ (2 * C * (1 + ‖k‖)) * (1 + ‖x‖) ^ (m + 1) := by
            exact mul_le_mul_of_nonneg_right hstep (by positivity)
    linarith [t1, t2]
  have hstep1 := integral_inner_mul_eq_integral_fderiv_covarianceOperator (μ := μ) hmean0 h
    (fun x : H => ⟪x, k⟫_ℝ * F x) hG_meas hG_c1 hCk' hG_growth hG'_growth
  -- ## Step 2: first-order IBP applied to `F₁ x = (DF x) (C h)`.
  have hF1_meas : Measurable (fun x : H => (fderiv ℝ F x) (covarianceOperator μ h)) := by
    have : Continuous fun x : H => (fderiv ℝ F x) (covarianceOperator μ h) :=
      ((ContinuousLinearMap.apply ℝ ℝ (covarianceOperator μ h)).continuous).comp hDFc1.continuous
    exact this.measurable
  have hF1_c1 : ContDiff ℝ 1 (fun x : H => (fderiv ℝ F x) (covarianceOperator μ h)) :=
    (ContinuousLinearMap.apply ℝ ℝ (covarianceOperator μ h)).contDiff.comp hDFc1
  have hF1_fderiv : ∀ x : H, fderiv ℝ (fun y : H => (fderiv ℝ F y) (covarianceOperator μ h)) x
      = (ContinuousLinearMap.apply ℝ ℝ (covarianceOperator μ h)).comp (fderiv ℝ (fderiv ℝ F) x) :=
        by
    intro x
    have hd : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x) x :=
      (hDFc1.differentiable (by norm_num) x).hasFDerivAt
    exact ((ContinuousLinearMap.apply ℝ ℝ (covarianceOperator μ h)).hasFDerivAt.comp x hd).fderiv
  have hCh' : (0 : ℝ) ≤ C * (1 + ‖(covarianceOperator μ h)‖) := by positivity
  have hF1_growth : ∀ x : H, |(fderiv ℝ F x) (covarianceOperator μ h)| ≤ (C * (1 +
    ‖(covarianceOperator μ h)‖)) * (1 + ‖x‖) ^ m := by
    intro x
    have h1 : |(fderiv ℝ F x) (covarianceOperator μ h)| ≤ ‖fderiv ℝ F x‖ * ‖(covarianceOperator μ
      h)‖ := by
      simpa [Real.norm_eq_abs] using (fderiv ℝ F x).le_opNorm (covarianceOperator μ h)
    have h2 : ‖fderiv ℝ F x‖ * ‖(covarianceOperator μ h)‖ ≤ (C * (1 + ‖x‖) ^ m) *
      ‖(covarianceOperator μ h)‖ :=
      mul_le_mul_of_nonneg_right (hF'_growth x) (norm_nonneg (covarianceOperator μ h))
    have h3 : (C * (1 + ‖x‖) ^ m) * ‖(covarianceOperator μ h)‖ ≤ (C * (1 + ‖(covarianceOperator μ
      h)‖)) * (1 + ‖x‖) ^ m := by
      have hstep : C * ‖(covarianceOperator μ h)‖ ≤ C * (1 + ‖(covarianceOperator μ h)‖) := by
        nlinarith [norm_nonneg (covarianceOperator μ h)]
      calc (C * (1 + ‖x‖) ^ m) * ‖(covarianceOperator μ h)‖ = (C * ‖(covarianceOperator μ h)‖) * (1
        + ‖x‖) ^ m := by ring
        _ ≤ (C * (1 + ‖(covarianceOperator μ h)‖)) * (1 + ‖x‖) ^ m := by
            exact mul_le_mul_of_nonneg_right hstep (by positivity)
    linarith
  have hF1'_growth : ∀ x : H, ‖fderiv ℝ (fun y : H => (fderiv ℝ F y) (covarianceOperator μ h)) x‖
      ≤ (C * (1 + ‖(covarianceOperator μ h)‖)) * (1 + ‖x‖) ^ m := by
    intro x
    rw [hF1_fderiv x]
    have h1 : ‖(ContinuousLinearMap.apply ℝ ℝ (covarianceOperator μ h)).comp (fderiv ℝ (fderiv ℝ F)
      x)‖
        ≤ ‖(covarianceOperator μ h)‖ * ‖fderiv ℝ (fderiv ℝ F) x‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
      have hv : ‖(fderiv ℝ (fderiv ℝ F) x) v‖ ≤ ‖fderiv ℝ (fderiv ℝ F) x‖ * ‖v‖ :=
        (fderiv ℝ (fderiv ℝ F) x).le_opNorm v
      calc ‖((ContinuousLinearMap.apply ℝ ℝ (covarianceOperator μ h)).comp (fderiv ℝ (fderiv ℝ F)
        x)) v‖
          = ‖((fderiv ℝ (fderiv ℝ F) x) v) (covarianceOperator μ h)‖ := rfl
        _ ≤ ‖(fderiv ℝ (fderiv ℝ F) x) v‖ * ‖(covarianceOperator μ h)‖ :=
            ((fderiv ℝ (fderiv ℝ F) x) v).le_opNorm (covarianceOperator μ h)
        _ ≤ (‖fderiv ℝ (fderiv ℝ F) x‖ * ‖v‖) * ‖(covarianceOperator μ h)‖ :=
            mul_le_mul_of_nonneg_right hv (norm_nonneg (covarianceOperator μ h))
        _ = ‖(covarianceOperator μ h)‖ * ‖fderiv ℝ (fderiv ℝ F) x‖ * ‖v‖ := by ring
    have h2 : ‖(covarianceOperator μ h)‖ * ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ ‖(covarianceOperator μ h)‖ *
      (C * (1 + ‖x‖) ^ m) :=
      mul_le_mul_of_nonneg_left (hF''_growth x) (norm_nonneg (covarianceOperator μ h))
    have h3 : ‖(covarianceOperator μ h)‖ * (C * (1 + ‖x‖) ^ m) ≤ (C * (1 + ‖(covarianceOperator μ
      h)‖)) * (1 + ‖x‖) ^ m := by
      have hstep : C * ‖(covarianceOperator μ h)‖ ≤ C * (1 + ‖(covarianceOperator μ h)‖) := by
        nlinarith [norm_nonneg (covarianceOperator μ h)]
      calc ‖(covarianceOperator μ h)‖ * (C * (1 + ‖x‖) ^ m) = (C * ‖(covarianceOperator μ h)‖) * (1
        + ‖x‖) ^ m := by ring
        _ ≤ (C * (1 + ‖(covarianceOperator μ h)‖)) * (1 + ‖x‖) ^ m := by
            exact mul_le_mul_of_nonneg_right hstep (by positivity)
    linarith
  have hstep2 := integral_inner_mul_eq_integral_fderiv_covarianceOperator (μ := μ) hmean0 k
    (fun x : H => (fderiv ℝ F x) (covarianceOperator μ h)) hF1_meas hF1_c1 hCh' hF1_growth
      hF1'_growth
  -- ## Splitting the step-1 integrand.
  have hIntF : Integrable F μ :=
    integrable_of_abs_le_mul_one_add_norm_pow (μ := μ) hF_meas hC hF_growth
  have hIntF1 : Integrable (fun x : H => ⟪x, k⟫_ℝ * (fderiv ℝ F x) (covarianceOperator μ h)) μ := by
    refine integrable_of_abs_le_mul_one_add_norm_pow (μ := μ) ?_ (C := ‖k‖ * (C * (1 +
      ‖(covarianceOperator μ h)‖)))
      (m := m + 1) (by positivity) (fun x => ?_)
    · have hmeas : Measurable (fun x : H => ⟪x, k⟫_ℝ) := by
        rw [inner_right_eq_innerSL k]; exact (innerSL ℝ k).continuous.measurable
      exact hmeas.mul hF1_meas
    · rw [abs_mul]
      calc |⟪x, k⟫_ℝ| * |(fderiv ℝ F x) (covarianceOperator μ h)|
          ≤ (‖k‖ * (1 + ‖x‖)) * ((C * (1 + ‖covarianceOperator μ h‖)) * (1 + ‖x‖) ^ m) :=
            mul_le_mul (abs_inner_le k x) (hF1_growth x) (abs_nonneg _) (by positivity)
        _ = (‖k‖ * (C * (1 + ‖covarianceOperator μ h‖))) * (1 + ‖x‖) ^ (m + 1) := by ring
  have hsplit :
      (∫ x : H, (fderiv ℝ (fun y : H => ⟪y, k⟫_ℝ * F y) x) (covarianceOperator μ h) ∂μ)
        = ⟪(covarianceOperator μ h), k⟫_ℝ * (∫ x : H, F x ∂μ)
          + ∫ x : H, ⟪x, k⟫_ℝ * (fderiv ℝ F x) (covarianceOperator μ h) ∂μ := by
    have hpt : ∀ x : H, (fderiv ℝ (fun y : H => ⟪y, k⟫_ℝ * F y) x) (covarianceOperator μ h)
        = ⟪(covarianceOperator μ h), k⟫_ℝ * F x + ⟪x, k⟫_ℝ * (fderiv ℝ F x) (covarianceOperator μ h)
          := by
      intro x
      rw [hG_fderiv x]
      simp only [add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul,
        real_inner_comm k (covarianceOperator μ h)]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_add (hIntF.const_mul _) hIntF1, integral_const_mul]
  have hfinal :
      (∫ x : H, (fderiv ℝ (fun y : H => (fderiv ℝ F y) (covarianceOperator μ h)) x)
          (covarianceOperator μ k) ∂μ)
        = ∫ x : H, ((fderiv ℝ (fderiv ℝ F) x) (covarianceOperator μ k))
            (covarianceOperator μ h) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hF1_fderiv x]
    rfl
  rw [hstep1, hsplit, hstep2, hfinal]

/-- Price's theorem for a centered integrand: if `∫ F ∂μ = 0` the covariance term drops out and
`∫ ⟪x,h⟫ ⟪x,k⟫ F x ∂μ = ∫ (D²F x) (C k) (C h) ∂μ`. -/
theorem integral_inner_mul_inner_mul_eq_integral_fderiv2_of_integral_eq_zero
    (hmean0 : (∫ x : H, x ∂μ) = 0) (h k : H)
    (F : H → ℝ) (hF_meas : Measurable F) (hF_c2 : ContDiff ℝ 2 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ x, |F x| ≤ C * (1 + ‖x‖) ^ m)
    (hF'_growth : ∀ x, ‖fderiv ℝ F x‖ ≤ C * (1 + ‖x‖) ^ m)
    (hF''_growth : ∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ C * (1 + ‖x‖) ^ m)
    (hF_int_zero : (∫ x : H, F x ∂μ) = 0) :
    (∫ x : H, ⟪x, h⟫_ℝ * (⟪x, k⟫_ℝ * F x) ∂μ)
      = ∫ x : H, ((fderiv ℝ (fderiv ℝ F) x) (covarianceOperator μ k))
          (covarianceOperator μ h) ∂μ := by
  rw [integral_inner_mul_inner_mul_eq_covariance_add_integral_fderiv2 (μ := μ) hmean0 h k F
    hF_meas hF_c2 hC hF_growth hF'_growth hF''_growth, hF_int_zero]
  ring

end IsGaussian

end Hilbert

end ProbabilityTheory
