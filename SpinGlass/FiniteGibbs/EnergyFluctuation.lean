/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.FiniteGibbs.GGError

/-!
# The energy fluctuation is a covariance bracket

`FiniteGibbs.ghirlandaGuerra_error_le` bounds the Ghirlanda–Guerra error by `√(𝔼⟨(H - 𝔼⟨H⟩)²⟩)`.
This file computes that fluctuation **exactly**, for a centered Gaussian Hamiltonian whose
covariance kernel has constant diagonal `c σ σ = d`:

`𝔼⟨H²⟩ = d + 𝔼⟨H(σ¹) c(σ¹, σ²)⟩ - d 𝔼⟨H⟩`,

so that, with `a = 𝔼⟨H⟩`,

`𝔼⟨(H - a)²⟩ = d + 𝔼⟨H(σ¹) c(σ¹, σ²)⟩ - d a - a²`.

The mechanism is one Gaussian integration by parts applied to the *energy-weighted* Gibbs weight
`H ↦ H_ρ p_ρ(H)`: differentiating the weight produces the fresh-replica covariance
`freshCov`, and differentiating the explicit factor `H_ρ` produces the diagonal `d`. Summing over
`ρ` turns the two contributions into `𝔼⟨H c₁₂⟩` and `d`. Applying the cavity identity once more
to the surviving `𝔼⟨H c₁₂⟩` removes the Hamiltonian altogether
(`integral_gibbs_average_energy_mul_kernel`), leaving a pure covariance-kernel expression: the
energy fluctuation of a Gaussian spin glass is the diagonal `d` plus a combination of three- and
two-replica overlap brackets.

## Main statements

- `FiniteGibbs.fderiv_energy_weight_apply`: the derivative of the energy-weighted Gibbs weight.
- `FiniteGibbs.integral_energy_sq_weight`: the integration by parts, one configuration at a time.
- `FiniteGibbs.integral_gibbs_average_energy_sq`: `𝔼⟨H²⟩ = d + 𝔼⟨H c₁₂⟩ - d 𝔼⟨H⟩`.
- `FiniteGibbs.integral_gibbs_average_sub_mean_sq`: the energy fluctuation.
-/

open MeasureTheory ProbabilityTheory BigOperators
open scoped InnerProductSpace ContDiff

namespace SpinGlass

namespace FiniteGibbs

noncomputable section

variable {α : Type*} [Fintype α] [Nonempty α]

/-! ### The energy-weighted Gibbs weight and its derivative -/

/-- The derivative of the energy-weighted Gibbs weight `H ↦ H_ρ p_ρ(H)`: the product rule, with
the softmax derivative in the second factor. -/
lemma hasFDerivAt_energy_weight (H : EnergySpace α) (ρ : α) :
    HasFDerivAt (fun H' : EnergySpace α => H' ρ * gibbs_pmf (α := α) H' ρ)
      ((H ρ) • fderiv ℝ (fun H' : EnergySpace α => gibbs_pmf (α := α) H' ρ) H
        + (gibbs_pmf (α := α) H ρ) • (evalCLM (α := α) ρ)) H :=
  ((evalCLM (α := α) ρ).hasFDerivAt).mul (hasFDerivAt_gibbs_pmf (α := α) H ρ)

/-- The directional derivative of the energy-weighted Gibbs weight:
`D(H_ρ p_ρ)(H)(v) = v_ρ p_ρ + H_ρ p_ρ (⟨v⟩ - v_ρ)`. -/
lemma fderiv_energy_weight_apply (H v : EnergySpace α) (ρ : α) :
    fderiv ℝ (fun H' : EnergySpace α => H' ρ * gibbs_pmf (α := α) H' ρ) H v
      = v ρ * gibbs_pmf (α := α) H ρ
        + H ρ * (gibbs_pmf (α := α) H ρ
            * ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v ρ)) := by
  rw [(hasFDerivAt_energy_weight (α := α) H ρ).fderiv]
  have heval : (evalCLM (α := α) ρ) v = v ρ := rfl
  simp only [add_apply, smul_apply, smul_eq_mul, heval]
  rw [fderiv_gibbs_pmf_apply]
  ring

/-- The energy-weighted Gibbs weight is bounded by the norm of the Hamiltonian. -/
lemma abs_energy_weight_le (H : EnergySpace α) (ρ : α) :
    |H ρ * gibbs_pmf (α := α) H ρ| ≤ ‖H‖ := by
  rw [abs_mul, abs_of_nonneg (gibbs_pmf_nonneg (α := α) H ρ)]
  have h1 : |H ρ| ≤ ‖H‖ := abs_apply_le_norm (α := α) H ρ
  have h2 : gibbs_pmf (α := α) H ρ ≤ 1 := gibbs_pmf_le_one (α := α) H ρ
  nlinarith [abs_nonneg (H ρ), gibbs_pmf_nonneg (α := α) H ρ, norm_nonneg H]

/-- The derivative of the energy-weighted Gibbs weight has linear growth. -/
lemma norm_fderiv_energy_weight_le (H : EnergySpace α) (ρ : α) :
    ‖fderiv ℝ (fun H' : EnergySpace α => H' ρ * gibbs_pmf (α := α) H' ρ) H‖
      ≤ 2 * (1 + ‖H‖) ^ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [Real.norm_eq_abs, fderiv_energy_weight_apply]
  have hv : |v ρ| ≤ ‖v‖ := abs_apply_le_norm (α := α) v ρ
  have hbr : |∑ τ : α, gibbs_pmf (α := α) H τ * v τ| ≤ ‖v‖ := by
    simpa [gibbs_pmf_eq_softmax] using Real.abs_sum_softmax_mul_le (-H) v
  have hH : |H ρ| ≤ ‖H‖ := abs_apply_le_norm (α := α) H ρ
  have hp0 : 0 ≤ gibbs_pmf (α := α) H ρ := gibbs_pmf_nonneg (α := α) H ρ
  have hp1 : gibbs_pmf (α := α) H ρ ≤ 1 := gibbs_pmf_le_one (α := α) H ρ
  calc |v ρ * gibbs_pmf (α := α) H ρ
        + H ρ * (gibbs_pmf (α := α) H ρ
            * ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v ρ))|
      ≤ |v ρ * gibbs_pmf (α := α) H ρ|
        + |H ρ * (gibbs_pmf (α := α) H ρ
            * ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v ρ))| := abs_add_le _ _
    _ ≤ ‖v‖ + ‖H‖ * (2 * ‖v‖) := by
        have e1 : |v ρ * gibbs_pmf (α := α) H ρ| ≤ ‖v‖ := by
          rw [abs_mul, abs_of_nonneg hp0]
          nlinarith [abs_nonneg (v ρ), norm_nonneg v]
        have e3 : |(∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v ρ| ≤ 2 * ‖v‖ := by
          refine le_trans (abs_sub _ _) ?_
          linarith
        have hq : gibbs_pmf (α := α) H ρ
            * |(∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v ρ| ≤ 2 * ‖v‖ := by
          nlinarith [abs_nonneg ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v ρ), norm_nonneg v]
        have e2 : |H ρ * (gibbs_pmf (α := α) H ρ
              * ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v ρ))| ≤ ‖H‖ * (2 * ‖v‖) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hp0]
          exact mul_le_mul hH hq (by positivity) (norm_nonneg H)
        linarith
    _ ≤ 2 * (1 + ‖H‖) ^ 1 * ‖v‖ := by
        rw [pow_one]
        nlinarith [norm_nonneg v, norm_nonneg H]


/-! ### Integration by parts on the energy-weighted Gibbs weight -/

variable {μ : Measure (EnergySpace α)} [IsGaussian μ]

/-- **The integration by parts.** For a centered Gaussian law, integrating the energy-weighted
Gibbs weight against `H_ρ` trades one Hamiltonian for the covariance kernel: the derivative of the
explicit factor `H_ρ` contributes the diagonal `c(ρ, ρ)`, and the derivative of the Gibbs weight
contributes the fresh-replica covariance `freshCov`. -/
lemma integral_energy_sq_weight (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0) (ρ : α) :
    (∫ H : EnergySpace α, H ρ * (H ρ * gibbs_pmf (α := α) H ρ) ∂μ)
      = ∫ H : EnergySpace α,
          ((covarianceOperator μ (std_basis (α := α) ρ)) ρ * gibbs_pmf (α := α) H ρ
            + H ρ * (gibbs_pmf (α := α) H ρ
                * (freshCov μ H ρ - (covarianceOperator μ (std_basis (α := α) ρ)) ρ))) ∂μ := by
  classical
  have hc1 : ContDiff ℝ 1 (fun H : EnergySpace α => H ρ * gibbs_pmf (α := α) H ρ) :=
    ((evalCLM (α := α) ρ).contDiff).mul ((contDiff_gibbs_pmf (α := α) ρ).of_le (by simp))
  have hIBP := ProbabilityTheory.IsGaussian.integral_inner_mul_eq_integral_fderiv_covarianceOperator
    (μ := μ) hmean0 (std_basis (α := α) ρ)
    (fun H : EnergySpace α => H ρ * gibbs_pmf (α := α) H ρ)
    hc1.continuous.measurable hc1 (C := 2) (m := 1) (by norm_num)
    (fun H => le_trans (abs_energy_weight_le (α := α) H ρ) (by
      rw [pow_one]
      nlinarith [norm_nonneg H]))
    (fun H => norm_fderiv_energy_weight_le (α := α) H ρ)
  have hLHS : (∫ H : EnergySpace α,
        ⟪H, std_basis (α := α) ρ⟫_ℝ * (H ρ * gibbs_pmf (α := α) H ρ) ∂μ)
      = ∫ H : EnergySpace α, H ρ * (H ρ * gibbs_pmf (α := α) H ρ) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun H => ?_)
    simp only []
    rw [real_inner_comm, inner_std_basis_apply]
  rw [← hLHS, hIBP]
  refine integral_congr_ae (Filter.Eventually.of_forall fun H => ?_)
  simp only []
  rw [fderiv_energy_weight_apply]
  simp only [freshCov]

/-! ### The second moment of the energy -/

omit [Nonempty α] in
private lemma integrable_of_bounded_growth {F : EnergySpace α → ℝ} (hF : Continuous F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C) (hb : ∀ H : EnergySpace α, |F H| ≤ C * (1 + ‖H‖) ^ m) :
    Integrable F μ :=
  ProbabilityTheory.IsGaussian.integrable_of_abs_le_mul_one_add_norm_pow (μ := μ)
    hF.measurable hC hb

/-- **The second moment of the energy.** For a centered Gaussian Hamiltonian whose covariance
kernel has constant diagonal `c σ σ = d`,

`𝔼⟨H²⟩ = d + 𝔼⟨H(σ¹) c(σ¹, σ²)⟩ - d 𝔼⟨H⟩`,

where the middle term is the Gibbs average of the Hamiltonian weighted by the covariance against a
fresh replica. -/
theorem integral_gibbs_average_energy_sq
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0) {d : ℝ}
    (hdiag : ∀ σ : α, (covarianceOperator μ (std_basis (α := α) σ)) σ = d) :
    (∫ H : EnergySpace α, (∑ σ : α, gibbs_pmf (α := α) H σ * (H σ * H σ)) ∂μ)
      = d + (∫ H : EnergySpace α,
            (∑ σ : α, gibbs_pmf (α := α) H σ * (H σ * freshCov μ H σ)) ∂μ)
        - d * ∫ H : EnergySpace α, (∑ σ : α, gibbs_pmf (α := α) H σ * H σ) ∂μ := by
  classical
  set K : ℝ := ‖covarianceOperator μ‖ with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  -- the four integrability facts, all from polynomial growth
  have hIw : ∀ ρ : α, Integrable (fun H : EnergySpace α => gibbs_pmf (α := α) H ρ) μ := by
    intro ρ
    refine integrable_of_bounded_growth (μ := μ) (contDiff_gibbs_pmf (α := α) ρ).continuous
      (C := 1) (m := 0) zero_le_one fun H => ?_
    rw [abs_of_nonneg (gibbs_pmf_nonneg (α := α) H ρ)]
    simpa using gibbs_pmf_le_one (α := α) H ρ
  have hIe : ∀ ρ : α,
      Integrable (fun H : EnergySpace α => H ρ * gibbs_pmf (α := α) H ρ) μ := by
    intro ρ
    refine integrable_of_bounded_growth (μ := μ)
      (((evalCLM (α := α) ρ).continuous).mul (contDiff_gibbs_pmf (α := α) ρ).continuous)
      (C := 1) (m := 1) zero_le_one fun H => ?_
    refine le_trans (abs_energy_weight_le (α := α) H ρ) ?_
    rw [pow_one, one_mul]
    linarith
  have hIsq : ∀ ρ : α,
      Integrable (fun H : EnergySpace α => H ρ * (H ρ * gibbs_pmf (α := α) H ρ)) μ := by
    intro ρ
    refine integrable_of_bounded_growth (μ := μ)
      (((evalCLM (α := α) ρ).continuous).mul
        (((evalCLM (α := α) ρ).continuous).mul (contDiff_gibbs_pmf (α := α) ρ).continuous))
      (C := 1) (m := 2) zero_le_one fun H => ?_
    have h1 : |H ρ| ≤ ‖H‖ := abs_apply_le_norm (α := α) H ρ
    have h2 : |H ρ * gibbs_pmf (α := α) H ρ| ≤ ‖H‖ := abs_energy_weight_le (α := α) H ρ
    calc |H ρ * (H ρ * gibbs_pmf (α := α) H ρ)|
        = |H ρ| * |H ρ * gibbs_pmf (α := α) H ρ| := abs_mul _ _
      _ ≤ ‖H‖ * ‖H‖ := mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
      _ ≤ 1 * (1 + ‖H‖) ^ 2 := by nlinarith [norm_nonneg H]
  have hIf : ∀ ρ : α, Integrable (fun H : EnergySpace α =>
      H ρ * (gibbs_pmf (α := α) H ρ * freshCov μ H ρ)) μ := by
    intro ρ
    refine integrable_of_bounded_growth (μ := μ)
      (((evalCLM (α := α) ρ).continuous).mul
        ((contDiff_gibbs_pmf (α := α) ρ).continuous.mul (continuous_freshCov (μ := μ) ρ)))
      (C := K) (m := 1) hK0 fun H => ?_
    have h1 : |H ρ| ≤ ‖H‖ := abs_apply_le_norm (α := α) H ρ
    have h2 : |gibbs_pmf (α := α) H ρ * freshCov μ H ρ| ≤ K := by
      rw [abs_mul, abs_of_nonneg (gibbs_pmf_nonneg (α := α) H ρ)]
      have := abs_freshCov_le (μ := μ) H ρ
      nlinarith [gibbs_pmf_nonneg (α := α) H ρ, gibbs_pmf_le_one (α := α) H ρ,
        abs_nonneg (freshCov μ H ρ)]
    calc |H ρ * (gibbs_pmf (α := α) H ρ * freshCov μ H ρ)|
        = |H ρ| * |gibbs_pmf (α := α) H ρ * freshCov μ H ρ| := abs_mul _ _
      _ ≤ ‖H‖ * K := mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
      _ ≤ K * (1 + ‖H‖) ^ 1 := by
          rw [pow_one]
          nlinarith [norm_nonneg H]
  -- rewrite both sides as sums of integrals
  have hL : (∫ H : EnergySpace α, (∑ σ : α, gibbs_pmf (α := α) H σ * (H σ * H σ)) ∂μ)
      = ∑ ρ : α, ∫ H : EnergySpace α, H ρ * (H ρ * gibbs_pmf (α := α) H ρ) ∂μ := by
    rw [← MeasureTheory.integral_finsetSum _ fun ρ (_ : ρ ∈ Finset.univ) => hIsq ρ]
    exact integral_congr_ae (Filter.Eventually.of_forall fun H =>
      Finset.sum_congr rfl fun ρ _ => by ring)
  have hM : (∫ H : EnergySpace α,
        (∑ σ : α, gibbs_pmf (α := α) H σ * (H σ * freshCov μ H σ)) ∂μ)
      = ∑ ρ : α, ∫ H : EnergySpace α,
          H ρ * (gibbs_pmf (α := α) H ρ * freshCov μ H ρ) ∂μ := by
    rw [← MeasureTheory.integral_finsetSum _ fun ρ (_ : ρ ∈ Finset.univ) => hIf ρ]
    exact integral_congr_ae (Filter.Eventually.of_forall fun H =>
      Finset.sum_congr rfl fun ρ _ => by ring)
  have hR : (∫ H : EnergySpace α, (∑ σ : α, gibbs_pmf (α := α) H σ * H σ) ∂μ)
      = ∑ ρ : α, ∫ H : EnergySpace α, H ρ * gibbs_pmf (α := α) H ρ ∂μ := by
    rw [← MeasureTheory.integral_finsetSum _ fun ρ (_ : ρ ∈ Finset.univ) => hIe ρ]
    exact integral_congr_ae (Filter.Eventually.of_forall fun H =>
      Finset.sum_congr rfl fun ρ _ => by ring)
  have hone : (∑ ρ : α, ∫ H : EnergySpace α, gibbs_pmf (α := α) H ρ ∂μ) = 1 := by
    rw [← MeasureTheory.integral_finsetSum _ fun ρ (_ : ρ ∈ Finset.univ) => hIw ρ]
    rw [show (fun H : EnergySpace α => ∑ ρ : α, gibbs_pmf (α := α) H ρ)
        = fun _ : EnergySpace α => (1 : ℝ) from funext fun H => sum_gibbs_pmf (α := α) H]
    simp [probReal_univ]
  -- integrate the integration by parts, one configuration at a time
  have hterm : ∀ ρ : α, (∫ H : EnergySpace α, H ρ * (H ρ * gibbs_pmf (α := α) H ρ) ∂μ)
      = d * (∫ H : EnergySpace α, gibbs_pmf (α := α) H ρ ∂μ)
        + ((∫ H : EnergySpace α, H ρ * (gibbs_pmf (α := α) H ρ * freshCov μ H ρ) ∂μ)
          - d * ∫ H : EnergySpace α, H ρ * gibbs_pmf (α := α) H ρ ∂μ) := by
    intro ρ
    rw [integral_energy_sq_weight (μ := μ) hmean0 ρ]
    have hcongr : ∀ H : EnergySpace α,
        (covarianceOperator μ (std_basis (α := α) ρ)) ρ * gibbs_pmf (α := α) H ρ
            + H ρ * (gibbs_pmf (α := α) H ρ
                * (freshCov μ H ρ - (covarianceOperator μ (std_basis (α := α) ρ)) ρ))
          = d * gibbs_pmf (α := α) H ρ
            + (H ρ * (gibbs_pmf (α := α) H ρ * freshCov μ H ρ)
              - d * (H ρ * gibbs_pmf (α := α) H ρ)) := by
      intro H
      rw [hdiag ρ]
      ring
    have hdw : Integrable (fun H : EnergySpace α => d * gibbs_pmf (α := α) H ρ) μ :=
      (hIw ρ).const_mul d
    have hde : Integrable
        (fun H : EnergySpace α => d * (H ρ * gibbs_pmf (α := α) H ρ)) μ := (hIe ρ).const_mul d
    have hsub : Integrable (fun H : EnergySpace α =>
        H ρ * (gibbs_pmf (α := α) H ρ * freshCov μ H ρ)
          - d * (H ρ * gibbs_pmf (α := α) H ρ)) μ := (hIf ρ).sub hde
    rw [integral_congr_ae (Filter.Eventually.of_forall hcongr),
      MeasureTheory.integral_add hdw hsub,
      MeasureTheory.integral_sub (hIf ρ) hde,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hL, Finset.sum_congr rfl fun ρ _ => hterm ρ, hM, hR, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hone, mul_one]
  ring

/-! ### The energy fluctuation -/

/-- **The energy fluctuation of a Gaussian spin glass.** With `a = 𝔼⟨H⟩`,

`𝔼⟨(H - a)²⟩ = d + 𝔼⟨H(σ¹) c(σ¹, σ²)⟩ - d a - a²`.

Combined with `FiniteGibbs.ghirlandaGuerra_error_le` this makes the Ghirlanda–Guerra error term
explicit: it is a covariance-kernel expression, with no Gibbs measure left except through the
brackets. -/
theorem integral_gibbs_average_sub_mean_sq
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0) {d : ℝ}
    (hdiag : ∀ σ : α, (covarianceOperator μ (std_basis (α := α) σ)) σ = d) :
    (∫ H : EnergySpace α, (∑ σ : α, gibbs_pmf (α := α) H σ
        * (H σ - ∫ H' : EnergySpace α,
            (∑ τ : α, gibbs_pmf (α := α) H' τ * H' τ) ∂μ) ^ 2) ∂μ)
      = d + (∫ H : EnergySpace α,
            (∑ σ : α, gibbs_pmf (α := α) H σ * (H σ * freshCov μ H σ)) ∂μ)
        - d * (∫ H : EnergySpace α, (∑ σ : α, gibbs_pmf (α := α) H σ * H σ) ∂μ)
        - (∫ H : EnergySpace α, (∑ σ : α, gibbs_pmf (α := α) H σ * H σ) ∂μ) ^ 2 := by
  classical
  set a : ℝ := ∫ H : EnergySpace α, (∑ σ : α, gibbs_pmf (α := α) H σ * H σ) ∂μ with ha
  have hexp : ∀ H : EnergySpace α,
      (∑ σ : α, gibbs_pmf (α := α) H σ * (H σ - a) ^ 2)
        = (∑ σ : α, gibbs_pmf (α := α) H σ * (H σ * H σ))
          - 2 * a * (∑ σ : α, gibbs_pmf (α := α) H σ * H σ) + a ^ 2 := by
    intro H
    have h1 : (∑ σ : α, gibbs_pmf (α := α) H σ * (H σ - a) ^ 2)
        = ∑ σ : α, (gibbs_pmf (α := α) H σ * (H σ * H σ)
            - 2 * a * (gibbs_pmf (α := α) H σ * H σ)
            + a ^ 2 * gibbs_pmf (α := α) H σ) :=
      Finset.sum_congr rfl fun σ _ => by ring
    rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_gibbs_pmf, mul_one]
  have hIsq : Integrable (fun H : EnergySpace α =>
      ∑ σ : α, gibbs_pmf (α := α) H σ * (H σ * H σ)) μ := by
    have := integrable_sum_gibbs_pmf_mul_sub_sq (α := α) (μ := μ) 0
    refine (this.congr (Filter.Eventually.of_forall fun H => ?_))
    exact Finset.sum_congr rfl fun σ _ => by ring
  have hIe : Integrable (fun H : EnergySpace α =>
      ∑ σ : α, gibbs_pmf (α := α) H σ * H σ) μ := by
    have := (memLp_two_sum_gibbs_pmf_mul_abs_sub (α := α) (μ := μ) 0).integrable one_le_two
    refine Integrable.mono' this
      ((continuous_finsetSum _ fun σ _ =>
        ((contDiff_gibbs_pmf (α := α) σ).continuous).mul
          (evalCLM (α := α) σ).continuous).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun H => ?_)
    calc ‖∑ σ : α, gibbs_pmf (α := α) H σ * H σ‖
        ≤ ∑ σ : α, |gibbs_pmf (α := α) H σ * H σ| := by
          simpa [Real.norm_eq_abs] using Finset.abs_sum_le_sum_abs
            (fun σ : α => gibbs_pmf (α := α) H σ * H σ) Finset.univ
      _ = ∑ σ : α, gibbs_pmf (α := α) H σ * |H σ - 0| := by
          exact Finset.sum_congr rfl fun σ _ => by
            rw [abs_mul, abs_of_nonneg (gibbs_pmf_nonneg (α := α) H σ), sub_zero]
  have hIe2 : Integrable
      (fun H : EnergySpace α => 2 * a * ∑ σ : α, gibbs_pmf (α := α) H σ * H σ) μ :=
    hIe.const_mul (2 * a)
  have hIdiff : Integrable (fun H : EnergySpace α =>
      (∑ σ : α, gibbs_pmf (α := α) H σ * (H σ * H σ))
        - 2 * a * ∑ σ : α, gibbs_pmf (α := α) H σ * H σ) μ := hIsq.sub hIe2
  have hIc : Integrable (fun _ : EnergySpace α => a ^ 2) μ := integrable_const _
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
    MeasureTheory.integral_add hIdiff hIc,
    MeasureTheory.integral_sub hIsq hIe2,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const,
    integral_gibbs_average_energy_sq (μ := μ) hmean0 hdiag, ← ha]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring


/-! ### Ghirlanda–Guerra with a covariance-kernel error term -/

omit [Nonempty α] [IsGaussian μ] in
/-- The one-replica Gibbs average of the energy, in plain-sum form. -/
lemma gibbs_average_one_energy (H : EnergySpace α) :
    gibbs_average_n_det (α := α) (n := 1) H (fun τs => H (τs 0))
      = ∑ σ : α, gibbs_pmf (α := α) H σ * H σ := by
  rw [gibbs_average_one]
  exact Finset.sum_congr rfl fun τ _ => mul_comm _ _

/-- **Ghirlanda–Guerra with an explicit covariance-kernel error term.** Combining
`FiniteGibbs.ghirlandaGuerra_error_le` with the exact energy fluctuation
`FiniteGibbs.integral_gibbs_average_sub_mean_sq`, the Ghirlanda–Guerra combination of an
`m`-replica test function bounded by `B` obeys

`|GG(f)| ≤ B √(d + 𝔼⟨H(σ¹) c(σ¹,σ²)⟩ - d 𝔼⟨H⟩ - (𝔼⟨H⟩)²)`,

at every finite volume, for every centered Gaussian Hamiltonian with constant-diagonal covariance
kernel. Nothing on the right-hand side involves the observable: the error is a property of the
Hamiltonian alone, and it is `O(N)` exactly when the energy self-averages, which is what makes the
identities hold in the limit after the customary normalisation. -/
theorem ghirlandaGuerra_error_le_energy_fluctuation
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0) {d : ℝ}
    (hdiag : ∀ σ : α, (covarianceOperator μ (std_basis (α := α) σ)) σ = d)
    (m : ℕ) (f : ReplicaFun (α := α) m) (i : Fin m) {B : ℝ} (hB : ∀ σs, |f σs| ≤ B) :
    |(m : ℝ) * (∫ H : EnergySpace α,
          gibbs_average_n_det (α := α) (n := m) H
            (fun σs => f σs * freshCov μ H (σs i)) ∂μ)
        - (∫ H : EnergySpace α, gibbs_average_n_det (α := α) (n := m) H f ∂μ)
            * (∫ H : EnergySpace α,
                gibbs_average_n_det (α := α) (n := 1) H (fun τs => freshCov μ H (τs 0)) ∂μ)
        - ∑ l ∈ Finset.univ.erase i, ∫ H : EnergySpace α,
            gibbs_average_n_det (α := α) (n := m) H
              (fun σs => f σs
                * (covarianceOperator μ (std_basis (α := α) (σs i))) (σs l)) ∂μ|
      ≤ B * Real.sqrt (d + (∫ H : EnergySpace α,
            (∑ σ : α, gibbs_pmf (α := α) H σ * (H σ * freshCov μ H σ)) ∂μ)
          - d * (∫ H : EnergySpace α, (∑ σ : α, gibbs_pmf (α := α) H σ * H σ) ∂μ)
          - (∫ H : EnergySpace α, (∑ σ : α, gibbs_pmf (α := α) H σ * H σ) ∂μ) ^ 2) := by
  classical
  have hmean : (∫ H : EnergySpace α,
        gibbs_average_n_det (α := α) (n := 1) H (fun τs => H (τs 0)) ∂μ)
      = ∫ H : EnergySpace α, (∑ σ : α, gibbs_pmf (α := α) H σ * H σ) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun H => gibbs_average_one_energy (α := α) H)
  have h := ghirlandaGuerra_error_le (μ := μ) hmean0 hdiag m f i hB
  rw [hmean] at h
  rwa [integral_gibbs_average_sub_mean_sq (μ := μ) hmean0 hdiag] at h


/-! ### Closing the fluctuation into covariance brackets -/

omit [Nonempty α] [IsGaussian μ] in
/-- The two-replica Gibbs bracket, as an explicit double sum. -/
lemma gibbs_average_two (H : EnergySpace α) (F : α → α → ℝ) :
    gibbs_average_n_det (α := α) (n := 2) H (fun σs => F (σs 0) (σs 1))
      = ∑ σ : α, ∑ τ : α, gibbs_pmf (α := α) H σ * gibbs_pmf (α := α) H τ * F σ τ := by
  classical
  rw [gibbs_average_n_det, ← Equiv.sum_comp (finTwoArrowEquiv α).symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
  simp only [finTwoArrowEquiv_symm_apply, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

/-- **The energy fluctuation as a covariance bracket.** For a centered Gaussian Hamiltonian with
constant-diagonal covariance kernel `c`, with `A = 𝔼⟨c(σ¹,σ²)⟩`,

`𝔼⟨(H - 𝔼⟨H⟩)²⟩ = d + 2 𝔼⟨c(σ¹,σ²) c(σ¹,σ³)⟩ - 𝔼⟨c(σ¹,σ²)²⟩ - A²`.

Nothing on the right-hand side mentions the Hamiltonian: the fluctuation of the energy of a
Gaussian spin glass is a function of its covariance kernel alone. The three brackets are the
three-replica, two-replica and one-replica averages of the kernel; centring them turns the
right-hand side into `d + 2 𝔼⟨(c₁₂ - A)(c₁₃ - A)⟩ - 𝔼⟨(c₁₂ - A)²⟩`, which is `O(N)` for a mixed
`p`-spin model exactly when the overlap fluctuations cancel — the content of the Ghirlanda–Guerra
identities.

The proof is the cavity identity `integral_gibbs_average_n_det_energy_mul` at two replicas applied
to the covariance kernel itself, removing the last Hamiltonian from
`integral_gibbs_average_sub_mean_sq`. -/
theorem integral_gibbs_average_sub_mean_sq_eq_covariance
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0) {d : ℝ}
    (hdiag : ∀ σ : α, (covarianceOperator μ (std_basis (α := α) σ)) σ = d) :
    (∫ H : EnergySpace α, (∑ σ : α, gibbs_pmf (α := α) H σ
        * (H σ - ∫ H' : EnergySpace α,
            (∑ τ : α, gibbs_pmf (α := α) H' τ * H' τ) ∂μ) ^ 2) ∂μ)
      = d
        + 2 * (∫ H : EnergySpace α,
            (∑ σ : α, gibbs_pmf (α := α) H σ * freshCov μ H σ ^ 2) ∂μ)
        - (∫ H : EnergySpace α, (∑ σ : α, ∑ τ : α, gibbs_pmf (α := α) H σ
            * gibbs_pmf (α := α) H τ
            * ((covarianceOperator μ (std_basis (α := α) σ)) τ) ^ 2) ∂μ)
        - (∫ H : EnergySpace α,
            (∑ σ : α, gibbs_pmf (α := α) H σ * freshCov μ H σ) ∂μ) ^ 2 := by
  classical
  have hK0 : (0 : ℝ) ≤ ‖covarianceOperator μ‖ := norm_nonneg _
  set A : EnergySpace α → ℝ :=
    fun H => ∑ σ : α, gibbs_pmf (α := α) H σ * freshCov μ H σ with hA
  set T : EnergySpace α → ℝ :=
    fun H => ∑ σ : α, gibbs_pmf (α := α) H σ * freshCov μ H σ ^ 2 with hT
  set S : EnergySpace α → ℝ :=
    fun H => ∑ σ : α, ∑ τ : α, gibbs_pmf (α := α) H σ * gibbs_pmf (α := α) H τ
      * ((covarianceOperator μ (std_basis (α := α) σ)) τ) ^ 2 with hS
  -- all three brackets are bounded and continuous, hence integrable
  have hIA : Integrable A μ := by
    refine integrable_of_bounded_growth (μ := μ)
      (continuous_finsetSum _ fun σ _ =>
        (contDiff_gibbs_pmf (α := α) σ).continuous.mul (continuous_freshCov (μ := μ) σ))
      (C := ‖covarianceOperator μ‖) (m := 0) hK0 fun H => ?_
    calc |A H| ≤ ∑ σ : α, |gibbs_pmf (α := α) H σ * freshCov μ H σ| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ σ : α, gibbs_pmf (α := α) H σ * ‖covarianceOperator μ‖ := by
          refine Finset.sum_le_sum fun σ _ => ?_
          rw [abs_mul, abs_of_nonneg (gibbs_pmf_nonneg (α := α) H σ)]
          exact mul_le_mul_of_nonneg_left (abs_freshCov_le (μ := μ) H σ)
            (gibbs_pmf_nonneg (α := α) H σ)
      _ = ‖covarianceOperator μ‖ * (1 + ‖H‖) ^ 0 := by
          rw [← Finset.sum_mul, sum_gibbs_pmf]; simp
  have hIT : Integrable T μ := by
    refine integrable_of_bounded_growth (μ := μ)
      (continuous_finsetSum _ fun σ _ =>
        (contDiff_gibbs_pmf (α := α) σ).continuous.mul
          ((continuous_freshCov (μ := μ) σ).pow 2))
      (C := ‖covarianceOperator μ‖ ^ 2) (m := 0) (by positivity) fun H => ?_
    calc |T H| ≤ ∑ σ : α, |gibbs_pmf (α := α) H σ * freshCov μ H σ ^ 2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ σ : α, gibbs_pmf (α := α) H σ * ‖covarianceOperator μ‖ ^ 2 := by
          refine Finset.sum_le_sum fun σ _ => ?_
          rw [abs_mul, abs_of_nonneg (gibbs_pmf_nonneg (α := α) H σ), abs_pow]
          refine mul_le_mul_of_nonneg_left ?_ (gibbs_pmf_nonneg (α := α) H σ)
          exact pow_le_pow_left₀ (abs_nonneg _) (abs_freshCov_le (μ := μ) H σ) 2
      _ = ‖covarianceOperator μ‖ ^ 2 * (1 + ‖H‖) ^ 0 := by
          rw [← Finset.sum_mul, sum_gibbs_pmf]; simp
  have hIS : Integrable S μ := by
    refine integrable_of_bounded_growth (μ := μ)
      (continuous_finsetSum _ fun σ _ => continuous_finsetSum _ fun τ _ =>
        ((contDiff_gibbs_pmf (α := α) σ).continuous.mul
          (contDiff_gibbs_pmf (α := α) τ).continuous).mul continuous_const)
      (C := ‖covarianceOperator μ‖ ^ 2) (m := 0) (by positivity) fun H => ?_
    have hrow : ∀ σ : α, |∑ τ : α, gibbs_pmf (α := α) H σ * gibbs_pmf (α := α) H τ
        * ((covarianceOperator μ (std_basis (α := α) σ)) τ) ^ 2|
          ≤ gibbs_pmf (α := α) H σ * ‖covarianceOperator μ‖ ^ 2 := by
      intro σ
      calc |∑ τ : α, gibbs_pmf (α := α) H σ * gibbs_pmf (α := α) H τ
              * ((covarianceOperator μ (std_basis (α := α) σ)) τ) ^ 2|
          ≤ ∑ τ : α, |gibbs_pmf (α := α) H σ * gibbs_pmf (α := α) H τ
              * ((covarianceOperator μ (std_basis (α := α) σ)) τ) ^ 2| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ τ : α, (gibbs_pmf (α := α) H σ * gibbs_pmf (α := α) H τ)
              * ‖covarianceOperator μ‖ ^ 2 := by
            refine Finset.sum_le_sum fun τ _ => ?_
            have hpp : (0:ℝ) ≤ gibbs_pmf (α := α) H σ * gibbs_pmf (α := α) H τ :=
              mul_nonneg (gibbs_pmf_nonneg (α := α) H σ) (gibbs_pmf_nonneg (α := α) H τ)
            rw [abs_mul, abs_of_nonneg hpp, abs_pow]
            refine mul_le_mul_of_nonneg_left ?_ hpp
            exact pow_le_pow_left₀ (abs_nonneg _)
              (abs_covarianceOperator_std_basis_apply_le (μ := μ) σ τ) 2
        _ = gibbs_pmf (α := α) H σ * ‖covarianceOperator μ‖ ^ 2 := by
            rw [← Finset.sum_mul, ← Finset.mul_sum, sum_gibbs_pmf, mul_one]
    calc |S H| ≤ ∑ σ : α, |∑ τ : α, gibbs_pmf (α := α) H σ * gibbs_pmf (α := α) H τ
            * ((covarianceOperator μ (std_basis (α := α) σ)) τ) ^ 2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ σ : α, gibbs_pmf (α := α) H σ * ‖covarianceOperator μ‖ ^ 2 :=
          Finset.sum_le_sum fun σ _ => hrow σ
      _ = ‖covarianceOperator μ‖ ^ 2 * (1 + ‖H‖) ^ 0 := by
          rw [← Finset.sum_mul, sum_gibbs_pmf]; simp
  -- the mean energy in terms of `A`
  have hone : (∫ H : EnergySpace α, (∑ σ : α, gibbs_pmf (α := α) H σ * H σ) ∂μ)
      = (∫ H : EnergySpace α, A H ∂μ) - d := by
    have h1 : (∫ H : EnergySpace α,
          gibbs_average_n_det (α := α) (n := 1) H (fun τs => H (τs 0)) ∂μ)
        = ∫ H : EnergySpace α, (∑ σ : α, gibbs_pmf (α := α) H σ * H σ) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun H => gibbs_average_one_energy (α := α) H)
    have h2 : (∫ H : EnergySpace α,
          gibbs_average_n_det (α := α) (n := 1) H (fun τs => freshCov μ H (τs 0)) ∂μ)
        = ∫ H : EnergySpace α, A H ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun H => ?_)
      simp only []
      rw [gibbs_average_one, hA]
      exact Finset.sum_congr rfl fun τ _ => mul_comm _ _
    rw [← h1, ← h2]
    exact integral_gibbs_average_one_energy (μ := μ) hmean0 hdiag
  -- the cavity identity at two replicas, applied to the covariance kernel itself
  have hcav := integral_gibbs_average_n_det_energy_mul (μ := μ) hmean0 2
    (fun σs => (covarianceOperator μ (std_basis (α := α) (σs 0))) (σs 1)) 0
  have hcavL : ∀ H : EnergySpace α,
      gibbs_average_n_det (α := α) (n := 2) H
          (fun σs => H (σs 0) * (covarianceOperator μ (std_basis (α := α) (σs 0))) (σs 1))
        = ∑ σ : α, gibbs_pmf (α := α) H σ * (H σ * freshCov μ H σ) := by
    intro H
    rw [gibbs_average_two (α := α) H
      (fun σ τ => H σ * (covarianceOperator μ (std_basis (α := α) σ)) τ)]
    simp only [freshCov, Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => by ring
  have hcavR : ∀ H : EnergySpace α,
      (((2 : ℕ) : ℝ) * gibbs_average_n_det (α := α) (n := 2) H
            (fun σs => (covarianceOperator μ (std_basis (α := α) (σs 0))) (σs 1)
              * (∑ τ : α, gibbs_pmf (α := α) H τ
                  * (covarianceOperator μ (std_basis (α := α) (σs 0))) τ))
          - ∑ l : Fin 2, gibbs_average_n_det (α := α) (n := 2) H
              (fun σs => (covarianceOperator μ (std_basis (α := α) (σs 0))) (σs 1)
                * (covarianceOperator μ (std_basis (α := α) (σs 0))) (σs l)))
        = 2 * T H - d * A H - S H := by
    intro H
    have e1 : gibbs_average_n_det (α := α) (n := 2) H
        (fun σs => (covarianceOperator μ (std_basis (α := α) (σs 0))) (σs 1)
          * (∑ τ : α, gibbs_pmf (α := α) H τ
              * (covarianceOperator μ (std_basis (α := α) (σs 0))) τ)) = T H := by
      rw [gibbs_average_two (α := α) H (fun σ τ =>
        (covarianceOperator μ (std_basis (α := α) σ)) τ
          * ∑ ρ : α, gibbs_pmf (α := α) H ρ
              * (covarianceOperator μ (std_basis (α := α) σ)) ρ)]
      simp only [hT, freshCov]
      refine Finset.sum_congr rfl fun σ _ => ?_
      have hrow : (∑ τ : α, gibbs_pmf (α := α) H σ * gibbs_pmf (α := α) H τ
            * ((covarianceOperator μ (std_basis (α := α) σ)) τ
              * ∑ ρ : α, gibbs_pmf (α := α) H ρ
                  * (covarianceOperator μ (std_basis (α := α) σ)) ρ))
          = (gibbs_pmf (α := α) H σ * ∑ ρ : α, gibbs_pmf (α := α) H ρ
                * (covarianceOperator μ (std_basis (α := α) σ)) ρ)
            * ∑ τ : α, gibbs_pmf (α := α) H τ
                * (covarianceOperator μ (std_basis (α := α) σ)) τ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun τ _ => by ring
      rw [hrow]
      ring
    have e2 : gibbs_average_n_det (α := α) (n := 2) H
        (fun σs => (covarianceOperator μ (std_basis (α := α) (σs 0))) (σs 1)
          * (covarianceOperator μ (std_basis (α := α) (σs 0))) (σs 0)) = d * A H := by
      rw [gibbs_average_two (α := α) H (fun σ τ =>
        (covarianceOperator μ (std_basis (α := α) σ)) τ
          * (covarianceOperator μ (std_basis (α := α) σ)) σ)]
      simp only [hdiag, hA, freshCov, Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => by ring
    have e3 : gibbs_average_n_det (α := α) (n := 2) H
        (fun σs => (covarianceOperator μ (std_basis (α := α) (σs 0))) (σs 1)
          * (covarianceOperator μ (std_basis (α := α) (σs 0))) (σs 1)) = S H := by
      rw [gibbs_average_two (α := α) H (fun σ τ =>
        (covarianceOperator μ (std_basis (α := α) σ)) τ
          * (covarianceOperator μ (std_basis (α := α) σ)) τ)]
      simp only [hS]
      exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => by ring
    rw [Fin.sum_univ_two, e1, e2, e3]
    ring
  have hmixed : (∫ H : EnergySpace α,
        (∑ σ : α, gibbs_pmf (α := α) H σ * (H σ * freshCov μ H σ)) ∂μ)
      = 2 * (∫ H : EnergySpace α, T H ∂μ) - d * (∫ H : EnergySpace α, A H ∂μ)
        - ∫ H : EnergySpace α, S H ∂μ := by
    rw [← integral_congr_ae (Filter.Eventually.of_forall hcavL), hcav,
      integral_congr_ae (Filter.Eventually.of_forall hcavR)]
    have hIsub : Integrable (fun H : EnergySpace α => 2 * T H - d * A H) μ :=
      (hIT.const_mul 2).sub (hIA.const_mul d)
    rw [MeasureTheory.integral_sub hIsub hIS,
      MeasureTheory.integral_sub (hIT.const_mul 2) (hIA.const_mul d),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [integral_gibbs_average_sub_mean_sq (μ := μ) hmean0 hdiag, hmixed, hone]
  ring

/-- **Ghirlanda–Guerra with a covariance-kernel error term, in closed form.** For a centered
Gaussian Hamiltonian with constant-diagonal covariance kernel `c`, the Ghirlanda–Guerra
combination of an `m`-replica test function bounded by `B` obeys

`|GG(f)| ≤ B √(d + 2 𝔼⟨c₁₂ c₁₃⟩ - 𝔼⟨c₁₂²⟩ - (𝔼⟨c₁₂⟩)²)`

at every finite volume. Neither the Hamiltonian nor the observable appears on the right: the
Ghirlanda–Guerra error of a Gaussian spin glass is bounded by an expression in the covariance
kernel alone, made of the three-, two- and one-replica averages of the kernel. -/
theorem ghirlandaGuerra_error_le_covariance
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0) {d : ℝ}
    (hdiag : ∀ σ : α, (covarianceOperator μ (std_basis (α := α) σ)) σ = d)
    (m : ℕ) (f : ReplicaFun (α := α) m) (i : Fin m) {B : ℝ} (hB : ∀ σs, |f σs| ≤ B) :
    |(m : ℝ) * (∫ H : EnergySpace α,
          gibbs_average_n_det (α := α) (n := m) H
            (fun σs => f σs * freshCov μ H (σs i)) ∂μ)
        - (∫ H : EnergySpace α, gibbs_average_n_det (α := α) (n := m) H f ∂μ)
            * (∫ H : EnergySpace α,
                gibbs_average_n_det (α := α) (n := 1) H (fun τs => freshCov μ H (τs 0)) ∂μ)
        - ∑ l ∈ Finset.univ.erase i, ∫ H : EnergySpace α,
            gibbs_average_n_det (α := α) (n := m) H
              (fun σs => f σs
                * (covarianceOperator μ (std_basis (α := α) (σs i))) (σs l)) ∂μ|
      ≤ B * Real.sqrt (d
          + 2 * (∫ H : EnergySpace α,
              (∑ σ : α, gibbs_pmf (α := α) H σ * freshCov μ H σ ^ 2) ∂μ)
          - (∫ H : EnergySpace α, (∑ σ : α, ∑ τ : α, gibbs_pmf (α := α) H σ
              * gibbs_pmf (α := α) H τ
              * ((covarianceOperator μ (std_basis (α := α) σ)) τ) ^ 2) ∂μ)
          - (∫ H : EnergySpace α,
              (∑ σ : α, gibbs_pmf (α := α) H σ * freshCov μ H σ) ∂μ) ^ 2) := by
  have hmean : (∫ H : EnergySpace α,
        gibbs_average_n_det (α := α) (n := 1) H (fun τs => H (τs 0)) ∂μ)
      = ∫ H : EnergySpace α, (∑ σ : α, gibbs_pmf (α := α) H σ * H σ) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun H => gibbs_average_one_energy (α := α) H)
  have h := ghirlandaGuerra_error_le (μ := μ) hmean0 hdiag m f i hB
  rw [hmean] at h
  rwa [integral_gibbs_average_sub_mean_sq_eq_covariance (μ := μ) hmean0 hdiag] at h

end

end FiniteGibbs

end SpinGlass
