/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.ThermodynamicLimit
import SpinGlass.SKDisorderExists
import SpinGlass.Poincare
import SpinGlass.FiniteGibbs.DerivSelfAveraging
import SpinGlass.FiniteGibbs.GGError
import SpinGlass.FiniteGibbs.DisorderDerivative
import SpinGlass.FiniteGibbs.EnergyFluctuation
import Common.Mathlib.Probability.Distributions.Gaussian.MultivariateScaling
import Common.Mathlib.MeasureTheory.Integral.CauchySchwarz
import Common.Mathlib.Analysis.InnerProductSpace.PositiveRange
import Common.Mathlib.MeasureTheory.Integral.IntervalMarkov
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

/-!
# Self-averaging for an arbitrary bounded Gaussian disorder

Everything Talagrand proves in Vol. II, §12.1–12.2 about the fluctuations of the energy uses only
three properties of the disorder covariance matrix `S`:

* it is positive semidefinite — so it *is* a covariance;
* its diagonal is constant, `S σ σ = D`;
* it is bounded by its diagonal, `|S σ τ| ≤ D`.

Every mixed `p`-spin model satisfies these: `S σ τ = N ξ(R_{στ})` with `ξ` a power series with
nonnegative coefficients gives `D = N ξ(1)` and `|ξ(r)| ≤ ξ(1)` for `|r| ≤ 1`
(`SpinGlass.posSemidef_overlapPolyMatrix` supplies the first). So do Guerra's replica-symmetric
reference kernels. This file proves the whole chain for such an `S`, at every finite volume; the
Sherrington–Kirkpatrick statements in `SpinGlass.FreeEnergyConvexity` and
`SpinGlass.SKGhirlandaGuerra` are the instance `S = skCovMatrix N 1`, `D = N/2`.

The inverse temperature enters as a dilation: the disorder at strength `β` has covariance `β² S`,
which is the law of `β • H` for `H` drawn from the reference field `SpinGlass.gaussField N S`
(`SpinGlass.gaussField_map_smul`). That is what makes the free energy convex in `β` and its
derivative computable.

## Main statements

- `SpinGlass.gaussField`, `gaussField_map_smul`, `covarianceOperator_gaussField_apply`.
- `SpinGlass.gaussFreeEnergy_eq_integral_smul`, `hasDerivAt_gaussFreeEnergy`.
- `SpinGlass.deriv_gaussFreeEnergy_eq` — **Talagrand Vol. I, Lemma 1.3.11**, in general form:
  `∂p_N/∂β = (β/N)(D - 𝔼⟨S(σ¹,σ²)⟩)`.
- `SpinGlass.abs_deriv_gaussFreeEnergy_le` — **Talagrand Vol. II, Lemma 12.1.4**:
  `|∂p_N/∂β| ≤ 2βD/N`, uniform in the volume once `D/N` is.
- `SpinGlass.variance_gaussFreeEnergy_le` — **Talagrand Vol. I, Theorem 1.3.4**:
  `Var[p_N^ω(β)] ≤ β² D/N²`.
-/

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology Set
open scoped Matrix

namespace SpinGlass

noncomputable section

variable {N : ℕ}

/-! ### The reference field -/

/-- The centered Gaussian disorder law with covariance matrix `S`. -/
def gaussField (N : ℕ) (S : Matrix (Config N) (Config N) ℝ) : Measure (EnergySpace N) :=
  multivariateGaussian (0 : EnergySpace N) S

instance isProbabilityMeasure_gaussField (N : ℕ) (S : Matrix (Config N) (Config N) ℝ) :
    IsProbabilityMeasure (gaussField N S) := by unfold gaussField; infer_instance

instance isGaussian_gaussField (N : ℕ) (S : Matrix (Config N) (Config N) ℝ) :
    ProbabilityTheory.IsGaussian (gaussField N S) := by unfold gaussField; infer_instance

lemma integral_id_gaussField (N : ℕ) (S : Matrix (Config N) (Config N) ℝ) :
    (∫ x : EnergySpace N, x ∂(gaussField N S)) = 0 := by simp [gaussField]

lemma integrable_norm_gaussField (N : ℕ) (S : Matrix (Config N) (Config N) ℝ) :
    Integrable (fun H : EnergySpace N => ‖H‖) (gaussField N S) :=
  (ProbabilityTheory.IsGaussian.integrable_id (μ := gaussField N S)).norm

lemma integrable_norm_sq_gaussField (N : ℕ) (S : Matrix (Config N) (Config N) ℝ) :
    Integrable (fun H : EnergySpace N => ‖H‖ ^ 2) (gaussField N S) := by
  have h := ProbabilityTheory.IsGaussian.memLp_two_id (μ := gaussField N S)
  exact (MeasureTheory.memLp_two_iff_integrable_sq_norm h.1).1 h

/-- **The disorder at strength `β` is the reference field dilated by `β`.** -/
lemma gaussField_map_smul {S : Matrix (Config N) (Config N) ℝ} (hS : S.PosSemidef) (β : ℝ) :
    (gaussField N S).map (fun H : EnergySpace N => β • H) = gaussField N ((β ^ 2) • S) := by
  have h := multivariateGaussian_map_smul (0 : EnergySpace N) (S := S) hS β
  rw [smul_zero] at h
  rw [gaussField, h, gaussField]

lemma covarianceOperator_gaussField_apply {S : Matrix (Config N) (Config N) ℝ}
    (hS : S.PosSemidef) (σ τ : Config N) :
    (ProbabilityTheory.covarianceOperator (gaussField N S)
        (FiniteGibbs.std_basis (α := Config N) σ)) τ = S σ τ := by
  have hcov := inner_covarianceOperator_multivariateGaussian_std_basis (N := N) S hS σ τ
  rw [real_inner_comm, inner_std_basis_apply] at hcov
  exact hcov

/-! ### Realising a prescribed sub-kernel as a component of the disorder -/

/-- **Every positive semidefinite kernel dominated by the disorder's own covariance is the cross
kernel of a component of the disorder.**

If `0 ≤ T ≤ S` in the Loewner order then there are directions `w` with
`Cov(⟪H, w σ⟫, H τ) = T σ τ`: the component field `σ ↦ ⟪H, w σ⟫` has cross kernel exactly `T`
against the Hamiltonian. Douglas' lemma
(`Matrix.PosSemidef.exists_mulVec_eq_of_sub_posSemidef`) supplies the directions — `w σ` is the
coefficient vector of the conditional expectation, given `H`, of the component with covariance `T`.

For a mixed `p`-spin model, `S = N ξ(R) = ∑_q a_q N R^q` and `T = a_p N R^p` is one summand, so
this produces the component whose kernel is a **single monomial** — the object Talagrand's
Definition 15.3.4 needs at each monomial test function. -/
theorem exists_directions_covKernel_eq {S T : Matrix (Config N) (Config N) ℝ}
    (hS : S.PosSemidef) (hT : T.PosSemidef) (hle : (S - T).PosSemidef) :
    ∃ w : Config N → EnergySpace N,
      ∀ σ τ : Config N, FiniteGibbs.covKernel (gaussField N S) w σ τ = T σ τ := by
  classical
  choose z hz using fun σ : Config N =>
    hS.exists_mulVec_eq_of_sub_posSemidef hT hle (WithLp.ofLp (std_basis N σ))
  refine ⟨fun σ => WithLp.toLp 2 (z σ), fun σ τ => ?_⟩
  have hco : (ProbabilityTheory.covarianceOperator (gaussField N S)
        (WithLp.toLp 2 (z σ) : EnergySpace N)) τ
      = inner ℝ (ProbabilityTheory.covarianceOperator (gaussField N S)
          (WithLp.toLp 2 (z σ) : EnergySpace N)) (std_basis N τ) := by
    rw [real_inner_comm, inner_std_basis_apply]
  have hvm : (z σ) ᵥ* S = S *ᵥ z σ := by
    have h := Matrix.vecMul_transpose S (z σ)
    rwa [Matrix.PosSemidef.transpose_eq hS] at h
  have h1 : (WithLp.ofLp (WithLp.toLp 2 (z σ) : EnergySpace N))
        ⬝ᵥ (S *ᵥ (WithLp.ofLp (std_basis N τ)))
      = (S *ᵥ z σ) τ := by
    rw [Matrix.dotProduct_mulVec, dotProduct_ofLp_std_basis]
    simpa using congrFun hvm τ
  rw [FiniteGibbs.covKernel_apply, hco, gaussField,
    inner_covarianceOperator_multivariateGaussian (ι := Config N) hS, h1, hz σ,
    mulVec_ofLp_std_basis (N := N) T σ τ, Matrix.PosSemidef.apply_symm hT τ σ]

/-! ### The free energy as a function of the disorder strength -/

/-- The free energy of the disorder at strength `β`, written as an integral against the **fixed**
reference field. -/
theorem gaussFreeEnergy_eq_integral_smul {S : Matrix (Config N) (Config N) ℝ}
    (hS : S.PosSemidef) (β h : ℝ) :
    gaussFreeEnergy N ((β ^ 2) • S) h
      = ∫ H : EnergySpace N, free_energy_density (N := N) (H_field N h + β • H)
          ∂(gaussField N S) := by
  have hcont : Continuous fun H : EnergySpace N =>
      free_energy_density (N := N) (H + H_field N h) :=
    (contDiff_free_energy_density (N := N)).continuous.comp (continuous_id.add continuous_const)
  have hmap := gaussField_map_smul (N := N) hS β
  have hint := MeasureTheory.integral_map (μ := gaussField N S)
    (φ := fun H : EnergySpace N => β • H)
    (f := fun H : EnergySpace N => free_energy_density (N := N) (H + H_field N h))
    (by fun_prop) (by rw [hmap]; exact hcont.aestronglyMeasurable)
  rw [gaussFreeEnergy, gaussField, ← gaussField, ← hmap, hint]
  exact integral_congr_ae (Filter.Eventually.of_forall fun H => by
    change free_energy_density (N := N) (β • H + H_field N h)
        = free_energy_density (N := N) (H_field N h + β • H)
    rw [add_comm])

/-- **The derivative of the free energy in the disorder strength is minus the mean energy.** -/
theorem hasDerivAt_gaussFreeEnergy {S : Matrix (Config N) (Config N) ℝ}
    (hS : S.PosSemidef) (h β : ℝ) :
    HasDerivAt (fun b => gaussFreeEnergy N ((b ^ 2) • S) h)
      (∫ H : EnergySpace N, -(1 / (N : ℝ)) *
          FiniteGibbs.gibbs_average (α := Config N) (H_field N h + β • H) H
          ∂(gaussField N S)) β := by
  have hd := FiniteGibbs.hasDerivAt_integral_free_energy_density
    (α := Config N) (P := gaussField N S) (U := fun _ => H_field N h) (V := id)
    measurable_const measurable_id (integrable_const _) (integrable_norm_gaussField N S) N β
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards with b
  exact gaussFreeEnergy_eq_integral_smul hS b h

theorem differentiableAt_gaussFreeEnergy {S : Matrix (Config N) (Config N) ℝ}
    (hS : S.PosSemidef) (h β : ℝ) :
    DifferentiableAt ℝ (fun b => gaussFreeEnergy N ((b ^ 2) • S) h) β :=
  (hasDerivAt_gaussFreeEnergy hS h β).differentiableAt

/-! ### The covariance gap: Lemma 1.3.11 and Lemma 12.1.4 -/

variable {S : Matrix (Config N) (Config N) ℝ}

lemma gibbs_average_freshCov_gaussField (hS : S.PosSemidef) (K : EnergySpace N) :
    FiniteGibbs.gibbs_average (α := Config N) K
        (fun σ => FiniteGibbs.freshCov (gaussField N S) K σ)
      = gibbs_average₂ (N := N) K (fun σ τ => S σ τ) := by
  classical
  simp only [FiniteGibbs.gibbs_average, FiniteGibbs.freshCov_apply, gibbs_average₂, Finset.mul_sum,
    gibbs_pmf_eq_FiniteGibbs_gibbs_pmf]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
  rw [covarianceOperator_gaussField_apply hS]
  ring

lemma nonneg_of_abs_le_diag {D : ℝ} (hbd : ∀ σ τ : Config N, |S σ τ| ≤ D) :
    0 ≤ D :=
  le_trans (abs_nonneg _) (hbd (Classical.arbitrary (Config N)) (Classical.arbitrary (Config N)))

lemma abs_gibbs_average₂_kernel_le {D : ℝ} (hbd : ∀ σ τ : Config N, |S σ τ| ≤ D)
    (K : EnergySpace N) : |gibbs_average₂ (N := N) K (fun σ τ => S σ τ)| ≤ D :=
  abs_gibbs_average₂_le (N := N) K fun σ τ => hbd σ τ

lemma measurable_gibbs_average₂_kernel {Ω : Type*} [MeasurableSpace Ω]
    {K : Ω → EnergySpace N} (hK : Measurable K) :
    Measurable fun w => gibbs_average₂ (N := N) (K w) (fun σ τ => S σ τ) := by
  classical
  have hp : ∀ σ : Config N, Measurable fun w => gibbs_pmf N (K w) σ := fun σ =>
    (((FiniteGibbs.contDiff_gibbs_pmf (α := Config N) σ).continuous.measurable).comp hK)
  simp only [gibbs_average₂, gibbs_pmf_eq_FiniteGibbs_gibbs_pmf]
  exact Finset.measurable_sum _ fun σ _ => Finset.measurable_sum _ fun τ _ =>
    ((hp σ).mul (hp τ)).mul measurable_const

lemma integrable_gibbs_average₂_kernel {D : ℝ} (hbd : ∀ σ τ : Config N, |S σ τ| ≤ D)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {K : Ω → EnergySpace N} (hK : Measurable K) :
    Integrable (fun w => gibbs_average₂ (N := N) (K w) (fun σ τ => S σ τ)) μ := by
  refine Integrable.of_bound (measurable_gibbs_average₂_kernel hK).aestronglyMeasurable D
    (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs]
  exact abs_gibbs_average₂_kernel_le hbd (K w)

/-- **Talagrand, Vol. I, Lemma 1.3.11, in general form.** The derivative of the mean free energy in
the disorder strength is the covariance gap: `∂p_N/∂β = (β/N)(D - 𝔼⟨S(σ¹,σ²)⟩)`. -/
theorem deriv_gaussFreeEnergy_eq (hS : S.PosSemidef) {D : ℝ}
    (hdiag : ∀ σ : Config N, S σ σ = D) (hbd : ∀ σ τ : Config N, |S σ τ| ≤ D) (h β : ℝ) :
    deriv (fun b => gaussFreeEnergy N ((b ^ 2) • S) h) β
      = (β / (N : ℝ)) * (D - ∫ H : EnergySpace N,
          gibbs_average₂ (N := N) (H_field N h + β • H) (fun σ τ => S σ τ)
          ∂(gaussField N S)) := by
  classical
  have hdiagCov : ∀ σ : Config N,
      (ProbabilityTheory.covarianceOperator (gaussField N S)
        (FiniteGibbs.std_basis (α := Config N) σ)) σ = D := fun σ => by
    rw [covarianceOperator_gaussField_apply hS, hdiag σ]
  have hcomm : ∀ H : EnergySpace N,
      -(1 / (N : ℝ)) * FiniteGibbs.gibbs_average (α := Config N) (H_field N h + β • H) H
        = -(1 / (N : ℝ)) * FiniteGibbs.gibbs_average (α := Config N) (β • H + H_field N h) H :=
    fun H => by rw [add_comm (H_field N h) (β • H)]
  have hderiv : deriv (fun b => gaussFreeEnergy N ((b ^ 2) • S) h) β
      = -(1 / (N : ℝ)) * ∫ H : EnergySpace N,
          FiniteGibbs.gibbs_average (α := Config N) (β • H + H_field N h) H
          ∂(gaussField N S) := by
    rw [(hasDerivAt_gaussFreeEnergy hS h β).deriv, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hcomm)
  have hkey := FiniteGibbs.integral_gibbs_average_self_eq_of_diag
    (α := Config N) (μ := gaussField N S) (integral_id_gaussField N S)
    (d := D) hdiagCov N β (H_field N h)
  have hgap : ∀ H : EnergySpace N,
      (D - FiniteGibbs.gibbs_average (α := Config N) (β • H + H_field N h)
          (fun σ => FiniteGibbs.freshCov (gaussField N S) (β • H + H_field N h) σ))
        = D - gibbs_average₂ (N := N) (β • H + H_field N h) (fun σ τ => S σ τ) := fun H => by
    rw [gibbs_average_freshCov_gaussField hS]
  rw [hderiv, hkey, integral_congr_ae (Filter.Eventually.of_forall hgap)]
  have hcomm₂ : ∀ H : EnergySpace N,
      gibbs_average₂ (N := N) (β • H + H_field N h) (fun σ τ => S σ τ)
        = gibbs_average₂ (N := N) (H_field N h + β • H) (fun σ τ => S σ τ) := fun H => by
    rw [add_comm (β • H) (H_field N h)]
  rw [integral_sub (integrable_const D)
      (integrable_gibbs_average₂_kernel hbd (gaussField N S)
        (K := fun H : EnergySpace N => β • H + H_field N h) (by fun_prop)),
    integral_const, integral_congr_ae (Filter.Eventually.of_forall hcomm₂)]
  have huniv : (gaussField N S).real Set.univ = 1 := by simp [MeasureTheory.measureReal_def]
  rw [huniv]
  simp only [smul_eq_mul, one_mul]
  ring

/-- **Talagrand, Vol. II, Lemma 12.1.4, in general form**: `|∂p_N/∂β| ≤ 2βD/N`, uniform in the
volume as soon as `D/N` is — which for a mixed `p`-spin model it is, `D = N ξ(1)`. -/
theorem abs_deriv_gaussFreeEnergy_le (hS : S.PosSemidef) {D : ℝ}
    (hdiag : ∀ σ : Config N, S σ σ = D) (hbd : ∀ σ τ : Config N, |S σ τ| ≤ D)
    (h : ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    |deriv (fun b => gaussFreeEnergy N ((b ^ 2) • S) h) β| ≤ 2 * β * D / (N : ℝ) := by
  classical
  have hD : 0 ≤ D := nonneg_of_abs_le_diag hbd
  have hbr : |∫ H : EnergySpace N,
      gibbs_average₂ (N := N) (H_field N h + β • H) (fun σ τ => S σ τ)
      ∂(gaussField N S)| ≤ D := by
    have hmono := integral_mono_of_nonneg
      (μ := gaussField N S)
      (f := fun K : EnergySpace N =>
        |gibbs_average₂ (N := N) (H_field N h + β • K) (fun σ τ => S σ τ)|)
      (g := fun _ => D)
      (Filter.Eventually.of_forall fun K => abs_nonneg _) (integrable_const _)
      (Filter.Eventually.of_forall fun K => abs_gibbs_average₂_kernel_le hbd _)
    calc |∫ H : EnergySpace N,
            gibbs_average₂ (N := N) (H_field N h + β • H) (fun σ τ => S σ τ) ∂(gaussField N S)|
        ≤ ∫ H : EnergySpace N,
            |gibbs_average₂ (N := N) (H_field N h + β • H) (fun σ τ => S σ τ)|
            ∂(gaussField N S) := by
          simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
            (μ := gaussField N S) (fun H : EnergySpace N =>
              gibbs_average₂ (N := N) (H_field N h + β • H) (fun σ τ => S σ τ))
      _ ≤ ∫ _H : EnergySpace N, D ∂(gaussField N S) := hmono
      _ = D := by rw [integral_const]; simp [MeasureTheory.measureReal_def]
  rw [deriv_gaussFreeEnergy_eq hS hdiag hbd h β, abs_mul,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ β / (N : ℝ))]
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  calc (β / (N : ℝ)) * |D - ∫ H : EnergySpace N,
        gibbs_average₂ (N := N) (H_field N h + β • H) (fun σ τ => S σ τ) ∂(gaussField N S)|
      ≤ (β / (N : ℝ)) * (2 * D) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (abs_sub _ _).trans ?_
        rw [abs_of_nonneg hD]
        linarith [hbr]
    _ = 2 * β * D / (N : ℝ) := by ring

/-! ### Concentration of the free energy -/

/-- **Talagrand, Vol. I, Theorem 1.3.4, in general form**: `Var[p_N^ω(β)] ≤ β² D / N²`. From the
Dirichlet-energy form of the Gaussian Poincaré inequality — the operator-norm form would give a
bound growing with the number of configurations. -/
theorem variance_gaussFreeEnergy_le (hS : S.PosSemidef) {D : ℝ}
    (hbd : ∀ σ τ : Config N, |S σ τ| ≤ D) (h β : ℝ) :
    Var[(fun H : EnergySpace N => free_energy_density (N := N) (H_field N h + β • H));
      gaussField N S] ≤ β ^ 2 * D / (N : ℝ) ^ 2 := by
  classical
  have hS' : ((β ^ 2) • S).PosSemidef := hS.smul_sq β
  have hmean0 : (∫ x : EnergySpace N, x ∂(gaussField N ((β ^ 2) • S))) = 0 :=
    integral_id_gaussField N _
  have hXcont : Continuous
      fun K : EnergySpace N => free_energy_density (N := N) (K + H_field N h) :=
    (contDiff_free_energy_density (N := N)).continuous.comp (by fun_prop)
  -- Transport the variance along the dilation.
  have hstep1 : Var[(fun H : EnergySpace N =>
        free_energy_density (N := N) (H_field N h + β • H)); gaussField N S]
      = Var[(fun K : EnergySpace N => free_energy_density (N := N) (K + H_field N h));
          gaussField N ((β ^ 2) • S)] := by
    have h1 := ProbabilityTheory.variance_map (μ := gaussField N S)
      (X := fun K : EnergySpace N => free_energy_density (N := N) (K + H_field N h))
      (Y := fun H : EnergySpace N => β • H)
      (by rw [gaussField_map_smul hS]; exact hXcont.measurable.aemeasurable) (by fun_prop)
    rw [gaussField_map_smul hS] at h1
    rw [h1]
    exact (ProbabilityTheory.variance_congr
      (Filter.Eventually.of_forall fun H => congrArg _ (add_comm _ _))).symm
  rw [hstep1]
  refine le_trans (FiniteGibbs.variance_free_energy_density_add_const_le_gibbs_covariance
    (α := Config N) hmean0 N (H_field N h)) ?_
  -- Identify the double sum and bound it by `β² D`.
  have hid : ∀ K : EnergySpace N,
      (∑ σ : Config N, ∑ τ : Config N,
          FiniteGibbs.gibbs_pmf (α := Config N) (K + H_field N h) σ
          * FiniteGibbs.gibbs_pmf (α := Config N) (K + H_field N h) τ
          * (ProbabilityTheory.covarianceOperator (gaussField N ((β ^ 2) • S))
              (FiniteGibbs.std_basis (α := Config N) σ)) τ)
        = gibbs_average₂ (N := N) (K + H_field N h) (fun σ τ => ((β ^ 2) • S) σ τ) := by
    intro K
    simp only [gibbs_average₂, gibbs_pmf_eq_FiniteGibbs_gibbs_pmf]
    exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ =>
      congrArg _ (covarianceOperator_gaussField_apply hS' σ τ)
  have hbd' : ∀ σ τ : Config N, |((β ^ 2) • S) σ τ| ≤ β ^ 2 * D := by
    intro σ τ
    rw [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (sq_nonneg β)]
    exact mul_le_mul_of_nonneg_left (hbd σ τ) (sq_nonneg β)
  have hub : ∀ K : EnergySpace N,
      (∑ σ : Config N, ∑ τ : Config N,
          FiniteGibbs.gibbs_pmf (α := Config N) (K + H_field N h) σ
          * FiniteGibbs.gibbs_pmf (α := Config N) (K + H_field N h) τ
          * (ProbabilityTheory.covarianceOperator (gaussField N ((β ^ 2) • S))
              (FiniteGibbs.std_basis (α := Config N) σ)) τ) ≤ β ^ 2 * D := by
    intro K
    rw [hid K]
    exact gibbs_average₂_le_of_le (N := N) _ fun σ τ => (le_abs_self _).trans (hbd' σ τ)
  have hnn : ∀ K : EnergySpace N, -(β ^ 2 * D) ≤
      (∑ σ : Config N, ∑ τ : Config N,
          FiniteGibbs.gibbs_pmf (α := Config N) (K + H_field N h) σ
          * FiniteGibbs.gibbs_pmf (α := Config N) (K + H_field N h) τ
          * (ProbabilityTheory.covarianceOperator (gaussField N ((β ^ 2) • S))
              (FiniteGibbs.std_basis (α := Config N) σ)) τ) := by
    intro K
    rw [hid K]
    have := abs_gibbs_average₂_le (N := N) (K + H_field N h)
      (f := fun σ τ => ((β ^ 2) • S) σ τ) (C := β ^ 2 * D) hbd'
    exact (abs_le.1 this).1
  have hIntBound : (∫ K : EnergySpace N,
        (∑ σ : Config N, ∑ τ : Config N,
          FiniteGibbs.gibbs_pmf (α := Config N) (K + H_field N h) σ
          * FiniteGibbs.gibbs_pmf (α := Config N) (K + H_field N h) τ
          * (ProbabilityTheory.covarianceOperator (gaussField N ((β ^ 2) • S))
              (FiniteGibbs.std_basis (α := Config N) σ)) τ)
        ∂(gaussField N ((β ^ 2) • S))) ≤ β ^ 2 * D := by
    have hInt : Integrable (fun K : EnergySpace N =>
        ∑ σ : Config N, ∑ τ : Config N,
          FiniteGibbs.gibbs_pmf (α := Config N) (K + H_field N h) σ
          * FiniteGibbs.gibbs_pmf (α := Config N) (K + H_field N h) τ
          * (ProbabilityTheory.covarianceOperator (gaussField N ((β ^ 2) • S))
              (FiniteGibbs.std_basis (α := Config N) σ)) τ)
        (gaussField N ((β ^ 2) • S)) := by
      refine (integrable_gibbs_average₂_kernel (S := (β ^ 2) • S) hbd'
        (gaussField N ((β ^ 2) • S))
        (K := fun K : EnergySpace N => K + H_field N h) (by fun_prop)).congr
        (Filter.Eventually.of_forall fun K => (hid K).symm)
    refine (integral_mono hInt (integrable_const _) hub).trans (le_of_eq ?_)
    rw [integral_const]
    simp [MeasureTheory.measureReal_def]
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp
  · have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    calc (1 / (N : ℝ)) ^ 2 * (∫ K : EnergySpace N, _ ∂(gaussField N ((β ^ 2) • S)))
        ≤ (1 / (N : ℝ)) ^ 2 * (β ^ 2 * D) :=
          mul_le_mul_of_nonneg_left hIntBound (by positivity)
      _ = β ^ 2 * D / (N : ℝ) ^ 2 := by field_simp

/-- **The mean absolute deviation of the free energy is `O(N^{-1/2})`**, with the explicit constant
`|β| √D / N`. -/
theorem integral_abs_gaussFreeEnergy_sub_mean_le (hS : S.PosSemidef) {D : ℝ}
    (hbd : ∀ σ τ : Config N, |S σ τ| ≤ D) (h y : ℝ) :
    (∫ H : EnergySpace N, |free_energy_density (N := N) (H_field N h + y • H)
        - ∫ H' : EnergySpace N, free_energy_density (N := N) (H_field N h + y • H')
            ∂(gaussField N S)| ∂(gaussField N S))
      ≤ |y| * Real.sqrt D / (N : ℝ) := by
  classical
  set X : EnergySpace N → ℝ := fun H => free_energy_density (N := N) (H_field N h + y • H) with hX
  have hXmem : MemLp X 2 (gaussField N S) :=
    FiniteGibbs.memLp_free_energy_density_affine (α := Config N) (μ := gaussField N S) N
      (H_field N h) y
  set m : ℝ := ∫ H : EnergySpace N, X H ∂(gaussField N S) with hm
  have hDmem : MemLp (fun H => X H - m) 2 (gaussField N S) := hXmem.sub (memLp_const m)
  have hCS := MeasureTheory.integral_abs_le_sqrt_measureReal_univ_mul_integral_sq
    (μ := gaussField N S) hDmem
  have huniv : (gaussField N S).real Set.univ = 1 := by simp [MeasureTheory.measureReal_def]
  rw [huniv, one_mul] at hCS
  have hvar : (∫ H : EnergySpace N, (X H - m) ^ 2 ∂(gaussField N S))
      = Var[X; gaussField N S] :=
    (ProbabilityTheory.variance_eq_integral hXmem.1.aemeasurable).symm
  rw [hvar] at hCS
  refine hCS.trans ?_
  have hb : Var[X; gaussField N S] ≤ y ^ 2 * D / (N : ℝ) ^ 2 :=
    variance_gaussFreeEnergy_le hS hbd h y
  have hD : 0 ≤ D := nonneg_of_abs_le_diag hbd
  have hsq : Real.sqrt (y ^ 2 * D / (N : ℝ) ^ 2) = |y| * Real.sqrt D / (N : ℝ) := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul (sq_nonneg y), Real.sqrt_sq_eq_abs,
      Real.sqrt_sq (Nat.cast_nonneg N)]
  rw [← hsq]
  exact Real.sqrt_le_sqrt hb

/-! ### Theorem 12.1.1 for a bounded Gaussian disorder -/

/-- The Gibbs half of Theorem 12.1.1: `∫_a^b 𝔼⟨|H/N - ⟨H/N⟩|⟩ dβ ≤ 2√((b-a) b D)/N`. -/
theorem intervalIntegral_gaussEnergy_fluctuation_le (hS : S.PosSemidef)
    {D : ℝ} (hdiag : ∀ σ : Config N, S σ σ = D) (hbd : ∀ σ τ : Config N, |S σ τ| ≤ D)
    (h : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ β in a..b, ∫ H : EnergySpace N, (1 / (N : ℝ)) *
        FiniteGibbs.gibbs_average (α := Config N) (H_field N h + β • H)
          (fun σ => |H σ - FiniteGibbs.gibbs_average (α := Config N)
            (H_field N h + β • H) H|) ∂(gaussField N S))
      ≤ Real.sqrt ((b - a) * (4 * b * D / (N : ℝ) ^ 2)) := by
  have hkey := FiniteGibbs.intervalIntegral_absFluct_le (α := Config N) (P := gaussField N S)
    (U := fun _ => H_field N h) (V := id) N measurable_const measurable_id
    (integrable_norm_gaussField N S) (integrable_norm_sq_gaussField N S) hab
  refine le_trans hkey (Real.sqrt_le_sqrt ?_)
  simp only [id_eq]
  have hderiv : ∀ x : ℝ, (∫ H : EnergySpace N, -(1 / (N : ℝ)) *
      FiniteGibbs.gibbs_average (α := Config N) (H_field N h + x • H) H ∂(gaussField N S))
        = deriv (fun b => gaussFreeEnergy N ((b ^ 2) • S) h) x := fun x =>
    ((hasDerivAt_gaussFreeEnergy hS h x).deriv).symm
  rw [hderiv a, hderiv b]
  have hD : 0 ≤ D := nonneg_of_abs_le_diag hbd
  have hqb := abs_deriv_gaussFreeEnergy_le hS hdiag hbd h (le_trans ha hab)
  have hqa := abs_deriv_gaussFreeEnergy_le hS hdiag hbd h ha
  have hba : (0 : ℝ) ≤ b - a := by linarith
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hsub : deriv (fun x => gaussFreeEnergy N ((x ^ 2) • S) h) b
      - deriv (fun x => gaussFreeEnergy N ((x ^ 2) • S) h) a ≤ 4 * b * D / (N : ℝ) := by
    have h1 := (abs_le.1 hqb).2
    have h2 := (abs_le.1 hqa).1
    have hmono : 2 * a * D / (N : ℝ) ≤ 2 * b * D / (N : ℝ) := by
      gcongr
    have harith : 2 * b * D / (N : ℝ) + 2 * b * D / (N : ℝ) = 4 * b * D / (N : ℝ) := by ring
    linarith
  refine mul_le_mul_of_nonneg_left ?_ hba
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp
  · have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    calc (1 / (N : ℝ)) * (deriv (fun x => gaussFreeEnergy N ((x ^ 2) • S) h) b
          - deriv (fun x => gaussFreeEnergy N ((x ^ 2) • S) h) a)
        ≤ (1 / (N : ℝ)) * (4 * b * D / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hsub (by positivity)
      _ = 4 * b * D / (N : ℝ) ^ 2 := by field_simp

/-- The disorder half of Theorem 12.1.1. -/
theorem intervalIntegral_gaussMeanEnergy_fluctuation_le (hS : S.PosSemidef) {D : ℝ}
    (hdiag : ∀ σ : Config N, S σ σ = D) (hbd : ∀ σ τ : Config N, |S σ τ| ≤ D)
    (h : ℝ) {δ a b : ℝ} (hδ : 0 < δ) (hab : a ≤ b) (haδ : 0 ≤ a - δ) :
    (∫ β in a..b, ∫ H : EnergySpace N,
        |(1 / (N : ℝ)) * FiniteGibbs.gibbs_average (α := Config N) (H_field N h + β • H) H
          - ∫ H' : EnergySpace N, (1 / (N : ℝ)) *
              FiniteGibbs.gibbs_average (α := Config N) (H_field N h + β • H') H'
              ∂(gaussField N S)| ∂(gaussField N S))
      ≤ 2 * δ * (4 * (b + δ) * D / (N : ℝ))
        + 3 * (b - a) * ((b + δ) * Real.sqrt D / (N : ℝ)) / δ := by
  classical
  have hD : 0 ≤ D := nonneg_of_abs_le_diag hbd
  have hbδ : (0 : ℝ) ≤ b + δ := by linarith
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  -- The concentration constant on the enlarged window.
  have hC : ∀ y ∈ Set.Icc (a - δ) (b + δ),
      (∫ H : EnergySpace N, |free_energy_density (N := N) (H_field N h + y • H)
          - ∫ H' : EnergySpace N, free_energy_density (N := N) (H_field N h + y • H')
              ∂(gaussField N S)| ∂(gaussField N S))
        ≤ (b + δ) * Real.sqrt D / (N : ℝ) := by
    intro y hy
    refine (integral_abs_gaussFreeEnergy_sub_mean_le hS hbd h y).trans ?_
    have hyabs : |y| ≤ b + δ := by
      rw [abs_le]
      exact ⟨by linarith [hy.1], hy.2⟩
    gcongr
  have hkey := FiniteGibbs.intervalIntegral_integral_abs_meanEnergy_sub_le
    (α := Config N) (P := gaussField N S) (U := fun _ => H_field N h) (V := id)
    N measurable_const measurable_id (integrable_const _) (integrable_norm_gaussField N S)
    hδ hab hC
  refine le_trans hkey ?_
  have hderiv_eq : ∀ z : ℝ,
      deriv (fun y : ℝ => ∫ w : EnergySpace N, FiniteGibbs.free_energy_density (α := Config N) N
          ((fun _ => H_field N h) w + y • id w) ∂(gaussField N S)) z
        = deriv (fun y : ℝ => gaussFreeEnergy N ((y ^ 2) • S) h) z := fun z => by
    congr 1
    funext y
    exact (gaussFreeEnergy_eq_integral_smul hS y h).symm
  rw [hderiv_eq, hderiv_eq]
  have hqb := abs_deriv_gaussFreeEnergy_le hS hdiag hbd h hbδ
  have hqa := abs_deriv_gaussFreeEnergy_le hS hdiag hbd h haδ
  have hincr : deriv (fun y : ℝ => gaussFreeEnergy N ((y ^ 2) • S) h) (b + δ)
      - deriv (fun y : ℝ => gaussFreeEnergy N ((y ^ 2) • S) h) (a - δ)
      ≤ 4 * (b + δ) * D / (N : ℝ) := by
    have h1 := (abs_le.1 hqb).2
    have h2 := (abs_le.1 hqa).1
    have hmono : 2 * (a - δ) * D / (N : ℝ) ≤ 2 * (b + δ) * D / (N : ℝ) := by
      gcongr
      linarith
    have harith : 2 * (b + δ) * D / (N : ℝ) + 2 * (b + δ) * D / (N : ℝ)
        = 4 * (b + δ) * D / (N : ℝ) := by ring
    linarith
  have h1 : 2 * δ * (deriv (fun y : ℝ => gaussFreeEnergy N ((y ^ 2) • S) h) (b + δ)
      - deriv (fun y : ℝ => gaussFreeEnergy N ((y ^ 2) • S) h) (a - δ))
      ≤ 2 * δ * (4 * (b + δ) * D / (N : ℝ)) :=
    mul_le_mul_of_nonneg_left hincr (by positivity)
  linarith

/-- **Talagrand, Vol. II, Theorem 12.1.1, for an arbitrary bounded Gaussian disorder.** -/
theorem intervalIntegral_gaussTotalEnergy_fluctuation_le (hS : S.PosSemidef) {D : ℝ}
    (hdiag : ∀ σ : Config N, S σ σ = D) (hbd : ∀ σ τ : Config N, |S σ τ| ≤ D)
    (h : ℝ) {δ a b : ℝ} (hδ : 0 < δ) (hab : a ≤ b) (haδ : 0 ≤ a - δ) :
    (∫ β in a..b, ∫ H : EnergySpace N,
        FiniteGibbs.gibbs_average (α := Config N) (H_field N h + β • H)
          (fun σ => |(1 / (N : ℝ)) * H σ - ∫ H' : EnergySpace N, (1 / (N : ℝ)) *
              FiniteGibbs.gibbs_average (α := Config N) (H_field N h + β • H') H'
              ∂(gaussField N S)|) ∂(gaussField N S))
      ≤ Real.sqrt ((b - a) * (4 * b * D / (N : ℝ) ^ 2))
        + (2 * δ * (4 * (b + δ) * D / (N : ℝ))
          + 3 * (b - a) * ((b + δ) * Real.sqrt D / (N : ℝ)) / δ) := by
  have ha : (0 : ℝ) ≤ a := by linarith
  have hsplit := FiniteGibbs.intervalIntegral_integral_totalFluct_le (α := Config N)
    (P := gaussField N S) (U := fun _ => H_field N h) (V := id) N measurable_const measurable_id
    (integrable_norm_gaussField N S) hab
  refine le_trans hsplit (add_le_add ?_ ?_)
  · exact intervalIntegral_gaussEnergy_fluctuation_le hS hdiag hbd h ha hab
  · exact intervalIntegral_gaussMeanEnergy_fluctuation_le hS hdiag hbd h hδ hab haδ

/-- **Talagrand, Vol. II, Theorem 12.1.1, in Markov form.** Theorem 12.1.1 bounds the energy
fluctuation *on average* over a temperature window; Markov's inequality converts that into a
quantitative statement about *most* temperatures: the set of `β ∈ (a,b]` at which the mean absolute
energy fluctuation exceeds `t` has Lebesgue measure at most `ε/t`, where `ε` is Theorem 12.1.1's
bound. This strengthens the mean-value form (`exists_beta_abs_gaussGhirlandaGuerra_error_le`), which
produces a single good `β`. -/
theorem measureReal_setOf_gaussTotalEnergy_fluctuation_ge_le (hS : S.PosSemidef) {D : ℝ}
    (hdiag : ∀ σ : Config N, S σ σ = D) (hbd : ∀ σ τ : Config N, |S σ τ| ≤ D)
    (h : ℝ) {δ a b t : ℝ} (hδ : 0 < δ) (hab : a ≤ b) (haδ : 0 ≤ a - δ) (ht : 0 < t) :
    volume.real ({β : ℝ | t ≤ ∫ H : EnergySpace N,
        FiniteGibbs.gibbs_average (α := Config N) (H_field N h + β • H)
          (fun σ => |(1 / (N : ℝ)) * H σ - ∫ H' : EnergySpace N, (1 / (N : ℝ)) *
              FiniteGibbs.gibbs_average (α := Config N) (H_field N h + β • H') H'
              ∂(gaussField N S)|) ∂(gaussField N S)} ∩ Set.Ioc a b)
      ≤ (Real.sqrt ((b - a) * (4 * b * D / (N : ℝ) ^ 2))
        + (2 * δ * (4 * (b + δ) * D / (N : ℝ))
          + 3 * (b - a) * ((b + δ) * Real.sqrt D / (N : ℝ)) / δ)) / t := by
  classical
  have hFcont : Continuous fun x : ℝ => ∫ H : EnergySpace N,
      FiniteGibbs.gibbs_average (α := Config N) (H_field N h + x • H)
        (fun σ => |(1 / (N : ℝ)) * H σ - ∫ H' : EnergySpace N, (1 / (N : ℝ)) *
            FiniteGibbs.gibbs_average (α := Config N) (H_field N h + x • H') H'
            ∂(gaussField N S)|) ∂(gaussField N S) :=
    FiniteGibbs.continuous_integral_totalFluct (α := Config N) (P := gaussField N S)
      (U := fun _ => H_field N h) (V := id) N measurable_const measurable_id
      (integrable_norm_gaussField N S)
  have hFnn : ∀ x : ℝ, 0 ≤ ∫ H : EnergySpace N,
      FiniteGibbs.gibbs_average (α := Config N) (H_field N h + x • H)
        (fun σ => |(1 / (N : ℝ)) * H σ - ∫ H' : EnergySpace N, (1 / (N : ℝ)) *
            FiniteGibbs.gibbs_average (α := Config N) (H_field N h + x • H') H'
            ∂(gaussField N S)|) ∂(gaussField N S) := fun x =>
    integral_nonneg fun H => FiniteGibbs.gibbs_average_abs_smul_sub_const_nonneg
      (α := Config N) N (H_field N h + x • H) H _
  have hmk := intervalIntegral.measureReal_setOf_le_le_of_continuous hFcont hFnn hab ht
  refine le_trans hmk ?_
  have hbnd := intervalIntegral_gaussTotalEnergy_fluctuation_le hS hdiag hbd h hδ hab haδ
  gcongr

/-! ### The Ghirlanda–Guerra error -/

lemma gibbs_average_smul_right (K : EnergySpace N) (c : ℝ) (W : EnergySpace N) :
    FiniteGibbs.gibbs_average (α := Config N) K (c • W)
      = c * FiniteGibbs.gibbs_average (α := Config N) K W := by
  simp only [FiniteGibbs.gibbs_average, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The external field vanishes at `h = 0`. -/
@[simp] lemma H_field_zero (N : ℕ) : H_field N (0 : ℝ) = 0 := by
  rw [H_field, magnetic_field_vector]
  rw [WithLp.toLp_eq_zero 2]
  funext σ
  simp

lemma integral_gibbs_average_one_energy_gaussField (hS : S.PosSemidef) (β : ℝ) :
    (∫ K : EnergySpace N, FiniteGibbs.gibbs_average_n_det (α := Config N) (n := 1) K
        (fun τs => K (τs 0)) ∂(gaussField N ((β ^ 2) • S)))
      = β * ∫ H : EnergySpace N,
          FiniteGibbs.gibbs_average (α := Config N) (β • H) H ∂(gaussField N S) := by
  have hcont : Continuous fun K : EnergySpace N =>
      FiniteGibbs.gibbs_average (α := Config N) K K := by
    simp only [FiniteGibbs.gibbs_average]
    exact continuous_finsetSum _ fun σ _ =>
      ((FiniteGibbs.contDiff_gibbs_pmf (α := Config N) σ).continuous).mul
        (FiniteGibbs.evalCLM (α := Config N) σ).continuous
  have hone : ∀ K : EnergySpace N,
      FiniteGibbs.gibbs_average_n_det (α := Config N) (n := 1) K (fun τs => K (τs 0))
        = FiniteGibbs.gibbs_average (α := Config N) K K := fun K =>
    FiniteGibbs.gibbs_average_one_energy (α := Config N) K
  rw [integral_congr_ae (Filter.Eventually.of_forall hone), ← gaussField_map_smul hS β,
    integral_map (μ := gaussField N S) (φ := fun H : EnergySpace N => β • H)
      (f := fun K : EnergySpace N => FiniteGibbs.gibbs_average (α := Config N) K K)
      (by fun_prop) hcont.aestronglyMeasurable, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun H =>
    gibbs_average_smul_right (β • H) β H)

/-- **The dictionary between the two normalisations.** The mean absolute energy fluctuation written
for the Gibbs measure at the Gaussian sample — the normalisation of the Ghirlanda–Guerra error
bound — equals `β N` times the same quantity written along the reference path, which is the
normalisation of Theorem 12.1.1. -/
theorem integral_gibbs_average_abs_sub_mean_gaussField_eq (hS : S.PosSemidef) (hN : N ≠ 0)
    {β : ℝ} (hβ : 0 ≤ β) :
    (∫ K : EnergySpace N, (∑ σ : Config N, FiniteGibbs.gibbs_pmf (α := Config N) K σ
        * |K σ - ∫ K' : EnergySpace N,
            FiniteGibbs.gibbs_average_n_det (α := Config N) (n := 1) K'
              (fun τs => K' (τs 0)) ∂(gaussField N ((β ^ 2) • S))|)
        ∂(gaussField N ((β ^ 2) • S)))
      = β * (N : ℝ) * ∫ H : EnergySpace N,
          FiniteGibbs.gibbs_average (α := Config N) (H_field N 0 + β • H)
            (fun σ => |(1 / (N : ℝ)) * H σ - ∫ H' : EnergySpace N, (1 / (N : ℝ)) *
                FiniteGibbs.gibbs_average (α := Config N) (H_field N 0 + β • H') H'
                ∂(gaussField N S)|) ∂(gaussField N S) := by
  classical
  have hNR : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := Nat.pos_of_ne_zero hN
    exact_mod_cast this
  set q : ℝ := ∫ H' : EnergySpace N, (1 / (N : ℝ)) *
    FiniteGibbs.gibbs_average (α := Config N) (H_field N 0 + β • H') H' ∂(gaussField N S) with hq
  have hqeq : (∫ H : EnergySpace N,
      FiniteGibbs.gibbs_average (α := Config N) (β • H) H ∂(gaussField N S))
      = (N : ℝ) * q := by
    rw [hq, ← integral_const_mul]
    have h1 : ∀ H' : EnergySpace N, (N : ℝ) * ((1 / (N : ℝ)) *
        FiniteGibbs.gibbs_average (α := Config N) (H_field N 0 + β • H') H')
        = FiniteGibbs.gibbs_average (α := Config N) (β • H') H' := by
      intro H'
      rw [H_field_zero, zero_add]
      field_simp
    exact (integral_congr_ae (Filter.Eventually.of_forall h1)).symm
  have hmean : (∫ K' : EnergySpace N,
      FiniteGibbs.gibbs_average_n_det (α := Config N) (n := 1) K'
        (fun τs => K' (τs 0)) ∂(gaussField N ((β ^ 2) • S))) = β * (N : ℝ) * q := by
    rw [integral_gibbs_average_one_energy_gaussField hS β, hqeq]
    ring
  rw [hmean]
  have hcont : Continuous fun K : EnergySpace N =>
      ∑ σ : Config N, FiniteGibbs.gibbs_pmf (α := Config N) K σ
        * |K σ - β * (N : ℝ) * q| := by
    refine continuous_finsetSum _ fun σ _ => ?_
    exact ((FiniteGibbs.contDiff_gibbs_pmf (α := Config N) σ).continuous).mul
      (((FiniteGibbs.evalCLM (α := Config N) σ).continuous.sub continuous_const).abs)
  rw [← gaussField_map_smul hS β]
  rw [integral_map (μ := gaussField N S) (φ := fun H : EnergySpace N => β • H)
    (f := fun K : EnergySpace N => ∑ σ : Config N, FiniteGibbs.gibbs_pmf (α := Config N) K σ
      * |K σ - β * (N : ℝ) * q|)
    (by fun_prop) hcont.aestronglyMeasurable]
  have hpt : ∀ H : EnergySpace N,
      (∑ σ : Config N, FiniteGibbs.gibbs_pmf (α := Config N) (β • H) σ
        * |(β • H : EnergySpace N) σ - β * (N : ℝ) * q|)
      = (β * (N : ℝ)) * FiniteGibbs.gibbs_average (α := Config N) (H_field N 0 + β • H)
          (fun σ => |(1 / (N : ℝ)) * H σ - q|) := by
    intro H
    rw [H_field_zero, zero_add]
    simp only [FiniteGibbs.gibbs_average, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hval : ((β • H) : EnergySpace N) σ = β * H σ := rfl
    have habs : |(β • H : EnergySpace N) σ - β * (N : ℝ) * q|
        = β * (N : ℝ) * |(1 / (N : ℝ)) * H σ - q| := by
      rw [hval, show β * H σ - β * (N : ℝ) * q
          = (β * (N : ℝ)) * ((1 / (N : ℝ)) * H σ - q) from by field_simp,
        abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ β * (N : ℝ))]
    rw [habs]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]

/-- **The Ghirlanda–Guerra error of a bounded Gaussian disorder at strength `β`.** For a test
function `f` of `m` replicas bounded by `B`, the Ghirlanda–Guerra combination built from the
covariance kernel is bounded by `B β N` times the mean absolute fluctuation of the energy per site
— the quantity Theorem 12.1.1 controls. Exact at every finite volume: no limit, no perturbation. -/
theorem abs_gaussGhirlandaGuerra_error_le (hS : S.PosSemidef) {D : ℝ}
    (hdiag : ∀ σ : Config N, S σ σ = D) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (m : ℕ) (f : FiniteGibbs.ReplicaFun (α := Config N) m) (i : Fin m) {B : ℝ}
    (hB : ∀ σs, |f σs| ≤ B) :
    |FiniteGibbs.ghirlandaGuerraCombination (gaussField N ((β ^ 2) • S)) m f i|
      ≤ B * (β * (N : ℝ) * ∫ H : EnergySpace N,
          FiniteGibbs.gibbs_average (α := Config N) (H_field N 0 + β • H)
            (fun σ => |(1 / (N : ℝ)) * H σ - ∫ H' : EnergySpace N, (1 / (N : ℝ)) *
                FiniteGibbs.gibbs_average (α := Config N) (H_field N 0 + β • H') H'
                ∂(gaussField N S)|) ∂(gaussField N S)) := by
  have hS' : ((β ^ 2) • S).PosSemidef := hS.smul_sq β
  have hdiag' : ∀ σ : Config N,
      (ProbabilityTheory.covarianceOperator (gaussField N ((β ^ 2) • S))
        (FiniteGibbs.std_basis (α := Config N) σ)) σ = β ^ 2 * D := fun σ => by
    rw [covarianceOperator_gaussField_apply hS' σ σ, Matrix.smul_apply, smul_eq_mul, hdiag σ]
  have h := FiniteGibbs.ghirlandaGuerra_error_le_integral_abs (α := Config N)
    (μ := gaussField N ((β ^ 2) • S)) (integral_id_gaussField N _)
    (d := β ^ 2 * D) hdiag' m f i hB
  rwa [integral_gibbs_average_abs_sub_mean_gaussField_eq hS hN hβ] at h

/-- **The Ghirlanda–Guerra identities hold up to an explicit `O(N^{-1/4})` error, at some disorder
strength in every window.** The mean value theorem for interval integrals turns Theorem 12.1.1's
*integrated* bound into a bound at a single `β`; this is Talagrand's conclusion "for the typical
value of `x`". -/
theorem exists_beta_abs_gaussGhirlandaGuerra_error_le (hS : S.PosSemidef) {D : ℝ}
    (hdiag : ∀ σ : Config N, S σ σ = D) (hbd : ∀ σ τ : Config N, |S σ τ| ≤ D) (hN : N ≠ 0)
    {δ a b : ℝ} (hδ : 0 < δ) (hab : a < b) (haδ : 0 ≤ a - δ)
    (m : ℕ) (f : FiniteGibbs.ReplicaFun (α := Config N) m) (i : Fin m) {B : ℝ}
    (hB : ∀ σs, |f σs| ≤ B) :
    ∃ β ∈ Set.Icc a b,
      |FiniteGibbs.ghirlandaGuerraCombination (gaussField N ((β ^ 2) • S)) m f i|
        ≤ B * (β * (N : ℝ) *
            ((Real.sqrt ((b - a) * (4 * b * D / (N : ℝ) ^ 2))
              + (2 * δ * (4 * (b + δ) * D / (N : ℝ))
                + 3 * (b - a) * ((b + δ) * Real.sqrt D / (N : ℝ)) / δ)) / (b - a))) := by
  classical
  set F : ℝ → ℝ := fun x => ∫ H : EnergySpace N,
    FiniteGibbs.gibbs_average (α := Config N) (H_field N 0 + x • H)
      (fun σ => |(1 / (N : ℝ)) * H σ - ∫ H' : EnergySpace N, (1 / (N : ℝ)) *
          FiniteGibbs.gibbs_average (α := Config N) (H_field N 0 + x • H') H'
          ∂(gaussField N S)|) ∂(gaussField N S) with hF
  have hba : (0 : ℝ) < b - a := by linarith
  have hFcont : Continuous F :=
    FiniteGibbs.continuous_integral_totalFluct (α := Config N) (P := gaussField N S)
      (U := fun _ => H_field N 0) (V := id) N measurable_const measurable_id
      (integrable_norm_gaussField N S)
  obtain ⟨c, hc, hceq⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg
    (f := F) (g := fun _ : ℝ => (1 : ℝ)) (μ := volume) (a := a) (b := b)
    (hFcont.continuousOn) intervalIntegrable_const (fun x _ => zero_le_one)
  rw [Set.uIcc_of_le hab.le] at hc
  simp only [mul_one, intervalIntegral.integral_const, smul_eq_mul, mul_one] at hceq
  have hbnd := intervalIntegral_gaussTotalEnergy_fluctuation_le hS hdiag hbd (0 : ℝ) hδ hab.le haδ
  have hFint : (∫ x in a..b, F x) ≤ Real.sqrt ((b - a) * (4 * b * D / (N : ℝ) ^ 2))
      + (2 * δ * (4 * (b + δ) * D / (N : ℝ))
        + 3 * (b - a) * ((b + δ) * Real.sqrt D / (N : ℝ)) / δ) := by
    rw [hF]; exact hbnd
  have hFc : F c ≤ (Real.sqrt ((b - a) * (4 * b * D / (N : ℝ) ^ 2))
      + (2 * δ * (4 * (b + δ) * D / (N : ℝ))
        + 3 * (b - a) * ((b + δ) * Real.sqrt D / (N : ℝ)) / δ)) / (b - a) := by
    rw [le_div_iff₀ hba]
    rw [hceq] at hFint
    linarith
  have hc0 : (0 : ℝ) ≤ c := by linarith [hc.1]
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB (fun _ => Classical.arbitrary (Config N)))
  refine ⟨c, hc, le_trans (abs_gaussGhirlandaGuerra_error_le hS hdiag hN hc0 m f i hB) ?_⟩
  have hNR : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  gcongr

/-- **The Ghirlanda–Guerra identities hold at all but a small set of inverse temperatures.**

Combining `abs_gaussGhirlandaGuerra_error_le` with the Markov form of Theorem 12.1.1: the set of
`β ∈ (a,b]` at which the Ghirlanda–Guerra combination of a test function bounded by `B` exceeds
`B β N t` has Lebesgue measure at most `ε/t`, where `ε` is Theorem 12.1.1's bound. Taking
`t = ε^{1/2}` (say) makes both the exceptional set and the error small, which is strictly stronger
than the mean-value form `exists_beta_abs_gaussGhirlandaGuerra_error_le`: the good `β` are not just
nonempty but of almost full measure. -/
theorem measureReal_setOf_gaussGhirlandaGuerra_error_gt_le (hS : S.PosSemidef) {D : ℝ}
    (hdiag : ∀ σ : Config N, S σ σ = D) (hbd : ∀ σ τ : Config N, |S σ τ| ≤ D) (hN : N ≠ 0)
    {δ a b t : ℝ} (hδ : 0 < δ) (hab : a ≤ b) (haδ : 0 ≤ a - δ) (ht : 0 < t)
    (m : ℕ) (f : FiniteGibbs.ReplicaFun (α := Config N) m) (i : Fin m) {B : ℝ}
    (hB : ∀ σs, |f σs| ≤ B) :
    volume.real ({β : ℝ | B * (β * (N : ℝ) * t)
          < |FiniteGibbs.ghirlandaGuerraCombination (gaussField N ((β ^ 2) • S)) m f i|}
        ∩ Set.Ioc a b)
      ≤ (Real.sqrt ((b - a) * (4 * b * D / (N : ℝ) ^ 2))
        + (2 * δ * (4 * (b + δ) * D / (N : ℝ))
          + 3 * (b - a) * ((b + δ) * Real.sqrt D / (N : ℝ)) / δ)) / t := by
  classical
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB fun _ => Classical.arbitrary (Config N))
  have ha0 : (0 : ℝ) < a := by linarith
  have hsub : {β : ℝ | B * (β * (N : ℝ) * t)
          < |FiniteGibbs.ghirlandaGuerraCombination (gaussField N ((β ^ 2) • S)) m f i|}
        ∩ Set.Ioc a b
      ⊆ {β : ℝ | t ≤ ∫ H : EnergySpace N,
            FiniteGibbs.gibbs_average (α := Config N) (H_field N 0 + β • H)
              (fun σ => |(1 / (N : ℝ)) * H σ - ∫ H' : EnergySpace N, (1 / (N : ℝ)) *
                  FiniteGibbs.gibbs_average (α := Config N) (H_field N 0 + β • H') H'
                  ∂(gaussField N S)|) ∂(gaussField N S)}
        ∩ Set.Ioc a b := by
    rintro β ⟨hβ1, hβ2⟩
    simp only [Set.mem_ofPred_eq] at hβ1
    refine ⟨?_, hβ2⟩
    simp only [Set.mem_ofPred_eq]
    by_contra hcon
    rw [not_le] at hcon
    have hb0 : (0 : ℝ) ≤ β := (ha0.trans hβ2.1).le
    have hle := abs_gaussGhirlandaGuerra_error_le hS hdiag hN hb0 m f i hB
    have hmono : B * (β * (N : ℝ) * ∫ H : EnergySpace N,
          FiniteGibbs.gibbs_average (α := Config N) (H_field N 0 + β • H)
            (fun σ => |(1 / (N : ℝ)) * H σ - ∫ H' : EnergySpace N, (1 / (N : ℝ)) *
                FiniteGibbs.gibbs_average (α := Config N) (H_field N 0 + β • H') H'
                ∂(gaussField N S)|) ∂(gaussField N S))
        ≤ B * (β * (N : ℝ) * t) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hcon.le (by positivity)) hB0
    exact absurd (hβ1.trans_le (hle.trans hmono)) (lt_irrefl _)
  exact le_trans
    (measureReal_mono hsub (ne_top_of_le_ne_top (by simp)
      (measure_mono Set.inter_subset_right)))
    (measureReal_setOf_gaussTotalEnergy_fluctuation_ge_le hS hdiag hbd 0 hδ hab haδ ht)

end

end SpinGlass
