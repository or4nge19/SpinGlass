/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.ThermodynamicLimit
import SpinGlass.FiniteGibbs.Convexity
import SpinGlass.FiniteGibbs.FluctuationIntegral
import SpinGlass.FiniteGibbs.DisorderDerivative
import SpinGlass.FiniteGibbs.SelfAveraging
import SpinGlass.FiniteGibbs.DerivSelfAveraging
import SpinGlass.GaussFieldFluctuation
import SpinGlass.SKDisorderExists
import Common.Mathlib.Analysis.Convex.GriffithsLemma
import Common.Mathlib.Probability.Distributions.Gaussian.MultivariateScaling

/-!
# Convexity of the SK free energy in the inverse temperature, and Griffiths' lemma

The SK covariance kernel is `N β² R²/2`: quadratic in `β`. So the disorder at inverse temperature
`β` is `β` times a single `β`-independent Gaussian field, and the free energy is the integral of a
convex function of `β` — Talagrand, *Mean Field Models for Spin Glasses*, Vol. I, (1.81). Together
with the existence of the thermodynamic limit (`SpinGlass.tendsto_skFreeEnergy`, Vol. I,
Theorem 1.3.9) and Griffiths' lemma (`ConvexOn.tendsto_rightDeriv_of_tendsto`) this gives the
statement Talagrand records right after Theorem 1.3.9: **the derivative of the free energy
converges** at every `β` where the limit is differentiable — which is every `β` outside a countable
set, since a convex function is differentiable off a countable set.

## Main statements

- `SpinGlass.skFreeEnergy_eq_integral_smul`: the SK free energy as an integral against **one**
  Gaussian field, with `β` appearing only as a dilation.
- `SpinGlass.convexOn_skFreeEnergy`, `SpinGlass.convexOn_skFreeEnergyLimit`.
- `SpinGlass.tendsto_rightDeriv_skFreeEnergy`: **Griffiths' lemma for the SK free energy.**
-/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace SpinGlass

noncomputable section

variable {N : ℕ}

/-! ### The `β`-dependence is a dilation -/

/-- **The SK covariance matrix scales quadratically in the inverse temperature.** -/
lemma skCovMatrix_eq_smul (N : ℕ) (β : ℝ) :
    skCovMatrix N β = (β ^ 2) • skCovMatrix N 1 := by
  ext σ τ
  simp only [skCovMatrix, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, sk_cov_kernel_eq]
  ring

/-- **The SK free energy is the average of the free energy of a single Gaussian field dilated by
`β`.** Talagrand Vol. I, (1.82): the disorder at inverse temperature `β` is `β u_σ` for a fixed
family `u_σ`. -/
theorem skFreeEnergy_eq_integral_smul (N : ℕ) (β h : ℝ) :
    skFreeEnergy N β h
      = ∫ H : EnergySpace N, free_energy_density (N := N) (β • H + H_field N h)
          ∂(multivariateGaussian (0 : EnergySpace N) (skCovMatrix N 1)) := by
  have hS : (skCovMatrix N 1).PosSemidef := posSemidef_skCovMatrix N 1
  have hmap := multivariateGaussian_map_smul (0 : EnergySpace N) hS β
  rw [smul_zero] at hmap
  have hcont : Continuous fun H : EnergySpace N =>
      free_energy_density (N := N) (H + H_field N h) :=
    (contDiff_free_energy_density (N := N)).continuous.comp (continuous_id.add continuous_const)
  have hint := MeasureTheory.integral_map
    (μ := multivariateGaussian (0 : EnergySpace N) (skCovMatrix N 1))
    (φ := fun H : EnergySpace N => β • H)
    (f := fun H : EnergySpace N => free_energy_density (N := N) (H + H_field N h))
    (by fun_prop) (by rw [hmap]; exact hcont.aestronglyMeasurable)
  rw [skFreeEnergy, gaussFreeEnergy, skCovMatrix_eq_smul N β, ← hmap, hint]

/-! ### Convexity -/

/-- Integrability of the dilated free energy density against the reference Gaussian field. -/
lemma integrable_free_energy_density_smul (N : ℕ) (β h : ℝ) :
    Integrable (fun H : EnergySpace N => free_energy_density (N := N) (β • H + H_field N h))
      (multivariateGaussian (0 : EnergySpace N) (skCovMatrix N 1)) := by
  refine integrable_free_energy_density_of_integrable_norm (N := N) _ (by fun_prop) ?_
  have hid : Integrable (id : EnergySpace N → EnergySpace N)
      (multivariateGaussian (0 : EnergySpace N) (skCovMatrix N 1)) :=
    ProbabilityTheory.IsGaussian.integrable_id
  have hnorm : Integrable (fun H : EnergySpace N => ‖H‖)
      (multivariateGaussian (0 : EnergySpace N) (skCovMatrix N 1)) := hid.norm
  refine Integrable.mono' (((hnorm.const_mul |β|).add (integrable_const ‖H_field N h‖))) ?_ ?_
  · exact (Continuous.norm (by fun_prop)).aestronglyMeasurable
  · filter_upwards with H
    have := norm_add_le (β • H) (H_field N h)
    rw [norm_smul, Real.norm_eq_abs] at this
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using this

/-- **The SK free energy is convex in the inverse temperature.** Talagrand Vol. I, (1.81). -/
theorem convexOn_skFreeEnergy (N : ℕ) (h : ℝ) :
    ConvexOn ℝ (univ : Set ℝ) fun β => skFreeEnergy N β h := by
  refine ⟨convex_univ, fun s _ t _ a b ha hb hab => ?_⟩
  have hpt : ∀ H : EnergySpace N,
      free_energy_density (N := N) ((a * s + b * t) • H + H_field N h)
        ≤ a * free_energy_density (N := N) (s • H + H_field N h)
          + b * free_energy_density (N := N) (t • H + H_field N h) := by
    intro H
    have hconv := FiniteGibbs.convexOn_free_energy_density_comp_affine
      (α := Config N) N (H_field N h) H
    have := hconv.2 (mem_univ s) (mem_univ t) ha hb hab
    have hcomm : ∀ r : ℝ, H_field N h + r • H = r • H + H_field N h := fun r => add_comm _ _
    simpa [FiniteGibbs.free_energy_density, free_energy_density, FiniteGibbs.Z, Z, hcomm,
      smul_eq_mul] using this
  have hmono : (∫ H : EnergySpace N,
        free_energy_density (N := N) ((a * s + b * t) • H + H_field N h)
        ∂(multivariateGaussian (0 : EnergySpace N) (skCovMatrix N 1)))
      ≤ ∫ H : EnergySpace N, (a * free_energy_density (N := N) (s • H + H_field N h)
          + b * free_energy_density (N := N) (t • H + H_field N h))
        ∂(multivariateGaussian (0 : EnergySpace N) (skCovMatrix N 1)) :=
    integral_mono (integrable_free_energy_density_smul N _ h)
      (((integrable_free_energy_density_smul N s h).const_mul a).add
        ((integrable_free_energy_density_smul N t h).const_mul b)) hpt
  rw [integral_add ((integrable_free_energy_density_smul N s h).const_mul a)
      ((integrable_free_energy_density_smul N t h).const_mul b),
    integral_const_mul, integral_const_mul] at hmono
  simpa [skFreeEnergy_eq_integral_smul, smul_eq_mul] using hmono

/-- **The limiting SK free energy is convex in the inverse temperature.** Convexity is a closed
condition, so it survives the thermodynamic limit. -/
theorem convexOn_skFreeEnergyLimit (h : ℝ) :
    ConvexOn ℝ (univ : Set ℝ) fun β => skFreeEnergyLimit β h := by
  refine ⟨convex_univ, fun s _ t _ a b ha hb hab => ?_⟩
  refine le_of_tendsto_of_tendsto (tendsto_skFreeEnergy (a * s + b * t) h)
    (((tendsto_skFreeEnergy s h).const_mul a).add ((tendsto_skFreeEnergy t h).const_mul b)) ?_
  filter_upwards with N
  simpa [smul_eq_mul] using
    (convexOn_skFreeEnergy N h).2 (mem_univ s) (mem_univ t) ha hb hab

/-! ### Griffiths' lemma for the SK free energy -/

/-- **Griffiths' lemma for the SK model.** At every inverse temperature where the limiting free
energy is differentiable — every `β` outside a countable set, since the limit is convex — the
derivative of the finite-volume free energy converges to the derivative of the limit.

Talagrand, *Mean Field Models for Spin Glasses*, Vol. I, §1.3, immediately after Theorem 1.3.9.
Combined with Lemma 1.3.11, `∂p_N/∂β = (β/2)(1 - 𝔼⟨R₁₂²⟩)`, this says that `lim_N 𝔼⟨R₁₂²⟩` exists
at every such `β`. -/
theorem tendsto_rightDeriv_skFreeEnergy (h : ℝ) {β : ℝ}
    (hdiff : derivWithin (fun b => skFreeEnergyLimit b h) (Iio β) β
      = derivWithin (fun b => skFreeEnergyLimit b h) (Ioi β) β) :
    Tendsto (fun N : ℕ => derivWithin (fun b => skFreeEnergy N b h) (Ioi β) β) atTop
      (𝓝 (derivWithin (fun b => skFreeEnergyLimit b h) (Ioi β) β)) := by
  refine ConvexOn.tendsto_rightDeriv_of_tendsto (S := (univ : Set ℝ))
    (fun N => convexOn_skFreeEnergy N h) (convexOn_skFreeEnergyLimit h)
    (fun y _ => tendsto_skFreeEnergy y h) ?_ hdiff
  simp

/-- **Griffiths' lemma holds at all but countably many inverse temperatures.** The exceptional set
is the set where the limiting free energy fails to be differentiable, and a convex function on `ℝ`
is differentiable off a countable set. -/
theorem countable_setOf_not_tendsto_rightDeriv_skFreeEnergy (h : ℝ) :
    {β : ℝ | ¬ Tendsto (fun N : ℕ => derivWithin (fun b => skFreeEnergy N b h) (Ioi β) β) atTop
        (𝓝 (derivWithin (fun b => skFreeEnergyLimit b h) (Ioi β) β))}.Countable := by
  refine Set.Countable.mono ?_
    ((convexOn_skFreeEnergyLimit h).countable_setOf_leftDeriv_ne_rightDeriv)
  intro β hβ
  exact ⟨by simp, fun hdiff => hβ (tendsto_rightDeriv_skFreeEnergy h hdiff)⟩

/-- **Griffiths' lemma for the SK model holds at almost every inverse temperature.** -/
theorem ae_tendsto_rightDeriv_skFreeEnergy (h : ℝ) :
    ∀ᵐ β : ℝ, Tendsto (fun N : ℕ => derivWithin (fun b => skFreeEnergy N b h) (Ioi β) β) atTop
      (𝓝 (derivWithin (fun b => skFreeEnergyLimit b h) (Ioi β) β)) := by
  have := (countable_setOf_not_tendsto_rightDeriv_skFreeEnergy h).measure_zero
    (μ := (volume : Measure ℝ))
  rwa [MeasureTheory.ae_iff]

/-! ### The derivative of the SK free energy, and the integrated energy fluctuation -/

/-- The reference Gaussian disorder of the SK model: the field at inverse temperature `1`. -/
def skField (N : ℕ) : Measure (EnergySpace N) :=
  gaussField N (skCovMatrix N 1)

lemma skField_eq (N : ℕ) : skField N = gaussField N (skCovMatrix N 1) := rfl

/-- The diagonal of the SK covariance matrix at `β = 1` is `N/2`. -/
lemma skCovMatrix_diag (N : ℕ) (σ : Config N) : skCovMatrix N 1 σ σ = (N : ℝ) / 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [skCovMatrix, sk_cov_kernel_eq]
  · simp only [skCovMatrix, Matrix.of_apply, sk_cov_kernel_eq,
      SpinGlass.overlap_self (N := N) hN]
    ring

/-- The SK covariance matrix at `β = 1` is bounded by its diagonal. -/
lemma abs_skCovMatrix_le (N : ℕ) (σ τ : Config N) :
    |skCovMatrix N 1 σ τ| ≤ (N : ℝ) / 2 := by
  simp only [skCovMatrix, Matrix.of_apply, sk_cov_kernel_eq]
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (N : ℝ) * 1 ^ 2 / 2)]
  have hR : |overlap N σ τ ^ 2| ≤ 1 := abs_overlap_sq_le_one N σ τ
  calc (N : ℝ) * 1 ^ 2 / 2 * |overlap N σ τ ^ 2|
      ≤ (N : ℝ) * 1 ^ 2 / 2 * 1 := by
        refine mul_le_mul_of_nonneg_left hR (by positivity)
    _ = (N : ℝ) / 2 := by ring

instance isProbabilityMeasure_skField (N : ℕ) : IsProbabilityMeasure (skField N) := by
  unfold skField; infer_instance

instance isGaussian_skField (N : ℕ) : ProbabilityTheory.IsGaussian (skField N) := by
  unfold skField; infer_instance

lemma integrable_norm_skField (N : ℕ) :
    Integrable (fun H : EnergySpace N => ‖H‖) (skField N) :=
  (ProbabilityTheory.IsGaussian.integrable_id (μ := skField N)).norm

lemma integrable_norm_sq_skField (N : ℕ) :
    Integrable (fun H : EnergySpace N => ‖H‖ ^ 2) (skField N) := by
  have h := ProbabilityTheory.IsGaussian.memLp_two_id (μ := skField N)
  exact (MeasureTheory.memLp_two_iff_integrable_sq_norm h.1).1 h

lemma skFreeEnergy_eq_integral_field (N : ℕ) (β h : ℝ) :
    skFreeEnergy N β h
      = ∫ H : EnergySpace N, free_energy_density (N := N) (H_field N h + β • H) ∂(skField N) := by
  rw [skFreeEnergy_eq_integral_smul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun H => by
    change free_energy_density (N := N) (β • H + H_field N h)
        = free_energy_density (N := N) (H_field N h + β • H)
    rw [add_comm])

/-- **The derivative of the SK free energy in the inverse temperature is minus the mean energy**:
`∂p_N/∂β = -𝔼⟨H⟩/N`, where `H` is the disorder at inverse temperature `1`.
Talagrand Vol. I, (1.83); Vol. II, (12.6). -/
theorem hasDerivAt_skFreeEnergy (N : ℕ) (h β : ℝ) :
    HasDerivAt (fun b => skFreeEnergy N b h)
      (∫ H : EnergySpace N, -(1 / (N : ℝ)) *
          FiniteGibbs.gibbs_average (α := Config N) (H_field N h + β • H) H ∂(skField N)) β := by
  have hd := FiniteGibbs.hasDerivAt_integral_free_energy_density
    (α := Config N) (P := skField N) (U := fun _ => H_field N h) (V := id)
    measurable_const measurable_id (integrable_const _) (integrable_norm_skField N) N β
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards with b
  exact skFreeEnergy_eq_integral_field N b h

theorem differentiableAt_skFreeEnergy (N : ℕ) (h β : ℝ) :
    DifferentiableAt ℝ (fun b => skFreeEnergy N b h) β :=
  (hasDerivAt_skFreeEnergy N h β).differentiableAt

/-- **Griffiths' lemma for the SK model, in two-sided derivative form.** -/
theorem tendsto_deriv_skFreeEnergy (h : ℝ) {β : ℝ}
    (hdiff : DifferentiableAt ℝ (fun b => skFreeEnergyLimit b h) β) :
    Tendsto (fun N : ℕ => deriv (fun b => skFreeEnergy N b h) β) atTop
      (𝓝 (deriv (fun b => skFreeEnergyLimit b h) β)) :=
  ConvexOn.tendsto_deriv_of_tendsto (S := (univ : Set ℝ))
    (fun N => convexOn_skFreeEnergy N h) (convexOn_skFreeEnergyLimit h)
    (fun y _ => tendsto_skFreeEnergy y h) (by simp) hdiff
    (fun N => differentiableAt_skFreeEnergy N h β)

/-- **The limiting SK free energy is differentiable off a countable set of inverse
temperatures.** -/
theorem countable_setOf_not_differentiableAt_skFreeEnergyLimit (h : ℝ) :
    {β : ℝ | ¬ DifferentiableAt ℝ (fun b => skFreeEnergyLimit b h) β}.Countable := by
  refine Set.Countable.mono ?_ ((convexOn_skFreeEnergyLimit h).countable_setOf_not_differentiableAt)
  exact fun β hβ => ⟨by simp, hβ⟩

/-- **Griffiths' lemma for the SK model holds at almost every inverse temperature.** -/
theorem ae_tendsto_deriv_skFreeEnergy (h : ℝ) :
    ∀ᵐ β : ℝ, Tendsto (fun N : ℕ => deriv (fun b => skFreeEnergy N b h) β) atTop
      (𝓝 (deriv (fun b => skFreeEnergyLimit b h) β)) := by
  have hcount : {β : ℝ | ¬ Tendsto (fun N : ℕ => deriv (fun b => skFreeEnergy N b h) β) atTop
      (𝓝 (deriv (fun b => skFreeEnergyLimit b h) β))}.Countable := by
    refine Set.Countable.mono ?_ (countable_setOf_not_differentiableAt_skFreeEnergyLimit h)
    exact fun β hβ hd => hβ (tendsto_deriv_skFreeEnergy h hd)
  have := hcount.measure_zero (μ := (volume : Measure ℝ))
  rwa [MeasureTheory.ae_iff]

/-- **Talagrand Vol. II, equation (12.9), for the SK model.** The Gibbs fluctuation of the energy,
integrated over the inverse temperature, is the increment of the derivative of the free energy:

`∫_a^b 𝔼⟨(H - ⟨H⟩)²⟩/N dβ = ∂p_N/∂β(b) - ∂p_N/∂β(a)`.

The integrand is nonnegative, so this bounds the *total* energy fluctuation over any window of
inverse temperatures by an increment of `∂p_N/∂β`. -/
theorem integral_skFluctuation_eq_sub (N : ℕ) (h a b : ℝ) :
    (∫ β in a..b, ∫ H : EnergySpace N,
        FiniteGibbs.hessian_free_energy (α := Config N) N (H_field N h + β • H) H H ∂(skField N))
      = deriv (fun x => skFreeEnergy N x h) b - deriv (fun x => skFreeEnergy N x h) a := by
  have hEq : ∀ x : ℝ, deriv (fun y => skFreeEnergy N y h) x
      = ∫ H : EnergySpace N, -(1 / (N : ℝ)) *
          FiniteGibbs.gibbs_average (α := Config N) (H_field N h + x • H) H ∂(skField N) := fun x =>
    (hasDerivAt_skFreeEnergy N h x).deriv
  rw [hEq b, hEq a]
  exact FiniteGibbs.integral_fluctuation_eq_sub (α := Config N) (P := skField N)
    (U := fun _ => H_field N h) (V := id) measurable_const measurable_id
    (integrable_norm_skField N) (integrable_norm_sq_skField N) N a b

/-! ### Talagrand's Lemma 1.3.11: the derivative is the mean square overlap -/

lemma integral_id_skField (N : ℕ) : (∫ x : EnergySpace N, x ∂(skField N)) = 0 :=
  integral_id_gaussField N (skCovMatrix N 1)

lemma covarianceOperator_skField_apply (N : ℕ) (σ τ : Config N) :
    (ProbabilityTheory.covarianceOperator (skField N)
        (FiniteGibbs.std_basis (α := Config N) σ)) τ = sk_cov_kernel N 1 σ τ := by
  have h := inner_covarianceOperator_multivariateGaussian_std_basis (N := N)
    (skCovMatrix N 1) (posSemidef_skCovMatrix N 1) σ τ
  rw [real_inner_comm, inner_std_basis_apply] at h
  exact h

lemma covarianceOperator_skField_diag (N : ℕ) (σ : Config N) :
    (ProbabilityTheory.covarianceOperator (skField N)
        (FiniteGibbs.std_basis (α := Config N) σ)) σ = (N : ℝ) / 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [covarianceOperator_skField_apply, sk_cov_kernel_eq]
    simp
  · rw [covarianceOperator_skField_apply, sk_cov_kernel_eq,
      SpinGlass.overlap_self (N := N) hN]
    ring

/-- The fresh-replica covariance of the SK field is `(N/2)` times the squared overlap. -/
lemma gibbs_average_freshCov_skField (N : ℕ) (K : EnergySpace N) :
    FiniteGibbs.gibbs_average (α := Config N) K
        (fun σ => FiniteGibbs.freshCov (skField N) K σ)
      = ((N : ℝ) / 2) * gibbs_average₂ (N := N) K (fun σ τ => overlap N σ τ ^ 2) := by
  classical
  simp only [FiniteGibbs.gibbs_average, FiniteGibbs.freshCov_apply, gibbs_average₂, Finset.mul_sum,
    gibbs_pmf_eq_FiniteGibbs_gibbs_pmf]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
  rw [covarianceOperator_skField_apply, sk_cov_kernel_eq]
  ring

lemma integrable_gibbs_average₂_overlap_sq (N : ℕ) (h β : ℝ) :
    Integrable (fun H : EnergySpace N =>
      gibbs_average₂ (N := N) (β • H + H_field N h) (fun σ τ => overlap N σ τ ^ 2))
      (skField N) := by
  classical
  have hcont : Continuous fun H : EnergySpace N =>
      gibbs_average₂ (N := N) (β • H + H_field N h) (fun σ τ => overlap N σ τ ^ 2) := by
    have hpath : Continuous fun H : EnergySpace N => β • H + H_field N h := by fun_prop
    have hp : ∀ σ : Config N, Continuous fun H : EnergySpace N =>
        gibbs_pmf N (β • H + H_field N h) σ := fun σ =>
      ((FiniteGibbs.contDiff_gibbs_pmf (α := Config N) σ).continuous).comp hpath
    simp only [gibbs_average₂]
    exact continuous_finsetSum _ fun σ _ => continuous_finsetSum _ fun τ _ =>
      ((hp σ).mul (hp τ)).mul continuous_const
  refine Integrable.of_bound hcont.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun H => ?_)
  rw [Real.norm_eq_abs]
  exact abs_gibbs_average₂_le (N := N) _ fun σ τ => abs_overlap_sq_le_one N σ τ

/-- **Talagrand's Lemma 1.3.11**: `∂p_N/∂β = (β/2)(1 - 𝔼⟨R₁₂²⟩)`. One Gaussian integration by
parts: the derivative of the free energy in `β` is minus the mean energy, and the mean energy is
the covariance gap `(N/2)(1 - 𝔼⟨R₁₂²⟩)`. -/
theorem deriv_skFreeEnergy_eq (N : ℕ) (hN : N ≠ 0) (h β : ℝ) :
    deriv (fun b => skFreeEnergy N b h) β
      = (β / 2) * (1 - ∫ H : EnergySpace N,
          gibbs_average₂ (N := N) (β • H + H_field N h)
            (fun σ τ => overlap N σ τ ^ 2) ∂(skField N)) := by
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN
  -- Rewrite the derivative with the Hamiltonian in the order `β H + h`.
  have hcomm : ∀ H : EnergySpace N,
      -(1 / (N : ℝ)) * FiniteGibbs.gibbs_average (α := Config N) (H_field N h + β • H) H
        = -(1 / (N : ℝ)) * FiniteGibbs.gibbs_average (α := Config N) (β • H + H_field N h) H := by
    intro H
    rw [add_comm (H_field N h) (β • H)]
  have hderiv : deriv (fun b => skFreeEnergy N b h) β
      = -(1 / (N : ℝ)) * ∫ H : EnergySpace N,
          FiniteGibbs.gibbs_average (α := Config N) (β • H + H_field N h) H ∂(skField N) := by
    rw [(hasDerivAt_skFreeEnergy N h β).deriv, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hcomm)
  have hkey := FiniteGibbs.integral_gibbs_average_self_eq_of_diag
    (α := Config N) (μ := skField N) (integral_id_skField N)
    (d := (N : ℝ) / 2) (covarianceOperator_skField_diag N) N β (H_field N h)
  have hgap : ∀ H : EnergySpace N,
      ((N : ℝ) / 2 - FiniteGibbs.gibbs_average (α := Config N) (β • H + H_field N h)
          (fun σ => FiniteGibbs.freshCov (skField N) (β • H + H_field N h) σ))
        = ((N : ℝ) / 2) * (1 - gibbs_average₂ (N := N) (β • H + H_field N h)
            (fun σ τ => overlap N σ τ ^ 2)) := by
    intro H
    rw [gibbs_average_freshCov_skField]
    ring
  rw [hderiv, hkey, integral_congr_ae (Filter.Eventually.of_forall hgap), integral_const_mul,
    integral_sub (integrable_const 1) (integrable_gibbs_average₂_overlap_sq N h β),
    integral_const]
  have huniv : (skField N).real Set.univ = 1 := by
    simp [MeasureTheory.measureReal_def]
  simp only [smul_eq_mul, mul_one, huniv]
  field_simp

/-- **The derivative of the SK free energy is between `0` and `β/2`.** Talagrand Vol. II,
Lemma 12.1.4: the derivative of the mean free energy in the disorder strength is bounded uniformly
in the volume. This is what makes the integrated fluctuation identity `(12.9)` useful. -/
theorem deriv_skFreeEnergy_nonneg_le (N : ℕ) (hN : N ≠ 0) (h : ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ deriv (fun b => skFreeEnergy N b h) β
      ∧ deriv (fun b => skFreeEnergy N b h) β ≤ β / 2 := by
  classical
  have hbr : ∀ H : EnergySpace N,
      0 ≤ gibbs_average₂ (N := N) (β • H + H_field N h) (fun σ τ => overlap N σ τ ^ 2)
        ∧ gibbs_average₂ (N := N) (β • H + H_field N h)
            (fun σ τ => overlap N σ τ ^ 2) ≤ 1 := fun H =>
    ⟨gibbs_average₂_nonneg (N := N) _ fun σ τ => sq_nonneg _,
      gibbs_average₂_le_of_le (N := N) _ fun σ τ =>
        (le_abs_self _).trans (abs_overlap_sq_le_one N σ τ)⟩
  have hI : (0 : ℝ) ≤ ∫ H : EnergySpace N,
      gibbs_average₂ (N := N) (β • H + H_field N h)
        (fun σ τ => overlap N σ τ ^ 2) ∂(skField N) :=
    integral_nonneg fun H => (hbr H).1
  have hI1 : (∫ H : EnergySpace N, gibbs_average₂ (N := N) (β • H + H_field N h)
      (fun σ τ => overlap N σ τ ^ 2) ∂(skField N)) ≤ 1 := by
    have := integral_mono (integrable_gibbs_average₂_overlap_sq N h β) (integrable_const 1)
      (fun H => (hbr H).2)
    simpa using this
  rw [deriv_skFreeEnergy_eq N hN h β]
  refine ⟨?_, by nlinarith [hI, hβ]⟩
  have hd : 0 ≤ 1 - ∫ H : EnergySpace N, gibbs_average₂ (N := N) (β • H + H_field N h)
      (fun σ τ => overlap N σ τ ^ 2) ∂(skField N) := by linarith
  positivity

/-! ### Concentration of the SK free energy along the temperature path -/

lemma covarianceOperator_skFieldAt_apply (N : ℕ) (y : ℝ) (σ τ : Config N) :
    (ProbabilityTheory.covarianceOperator
        (multivariateGaussian (0 : EnergySpace N) (skCovMatrix N y))
        (FiniteGibbs.std_basis (α := Config N) σ)) τ = sk_cov_kernel N y σ τ := by
  have hcov := inner_covarianceOperator_multivariateGaussian_std_basis (N := N)
    (skCovMatrix N y) (posSemidef_skCovMatrix N y) σ τ
  rw [real_inner_comm, inner_std_basis_apply] at hcov
  exact hcov

lemma skField_map_smul (N : ℕ) (y : ℝ) :
    (skField N).map (fun H : EnergySpace N => y • H)
      = multivariateGaussian (0 : EnergySpace N) (skCovMatrix N y) := by
  rw [skField_eq, gaussField_map_smul (S := skCovMatrix N 1) (posSemidef_skCovMatrix N 1) y,
    ← skCovMatrix_eq_smul N y, gaussField]

/-- The two-replica bracket of the SK kernel is at most its diagonal `N β²/2`. -/
lemma gibbs_average₂_skKernel_le (N : ℕ) (y : ℝ) (K : EnergySpace N) :
    gibbs_average₂ (N := N) K (fun σ τ => sk_cov_kernel N y σ τ) ≤ (N : ℝ) * y ^ 2 / 2 := by
  refine gibbs_average₂_le_of_le (N := N) K fun σ τ => ?_
  rw [sk_cov_kernel_eq]
  have hR : overlap N σ τ ^ 2 ≤ 1 := (le_abs_self _).trans (abs_overlap_sq_le_one N σ τ)
  have hpos : (0 : ℝ) ≤ (N : ℝ) * y ^ 2 / 2 := by positivity
  nlinarith [hpos, hR]

lemma gibbs_average₂_skKernel_nonneg (N : ℕ) (y : ℝ) (K : EnergySpace N) :
    0 ≤ gibbs_average₂ (N := N) K (fun σ τ => sk_cov_kernel N y σ τ) := by
  refine gibbs_average₂_nonneg (N := N) K fun σ τ => ?_
  rw [sk_cov_kernel_eq]
  positivity

lemma continuous_gibbs_average₂_skKernel (N : ℕ) (y : ℝ) (c₀ : EnergySpace N) :
    Continuous fun K : EnergySpace N =>
      gibbs_average₂ (N := N) (K + c₀) (fun σ τ => sk_cov_kernel N y σ τ) := by
  classical
  have hpath : Continuous fun K : EnergySpace N => K + c₀ := by fun_prop
  have hp : ∀ σ : Config N, Continuous fun K : EnergySpace N =>
      gibbs_pmf N (K + c₀) σ := fun σ =>
    ((FiniteGibbs.contDiff_gibbs_pmf (α := Config N) σ).continuous).comp hpath
  simp only [gibbs_average₂]
  exact continuous_finsetSum _ fun σ _ => continuous_finsetSum _ fun τ _ =>
    ((hp σ).mul (hp τ)).mul continuous_const

/-- **Concentration of the SK free energy**, sharp in the volume: `Var[p_N^ω(β)] ≤ β²/(2N)`.
Talagrand Vol. I, Theorem 1.3.4 for the SK model, from the Dirichlet-energy form of the Gaussian
Poincaré inequality — the operator-norm form would give a bound growing with the number of
configurations. -/
theorem variance_skFreeEnergy_le (N : ℕ) (hN : N ≠ 0) (h y : ℝ) :
    Var[(fun H : EnergySpace N => free_energy_density (N := N) (H_field N h + y • H));
      skField N] ≤ y ^ 2 / (2 * (N : ℝ)) := by
  have hNR : (N : ℝ) ≠ 0 := by
    have h0 : 0 < N := Nat.pos_of_ne_zero hN
    exact_mod_cast h0.ne'
  rw [skField_eq]
  refine (variance_gaussFreeEnergy_le (N := N) (S := skCovMatrix N 1)
    (posSemidef_skCovMatrix N 1) (D := (N : ℝ) / 2) (abs_skCovMatrix_le N) h y).trans
    (le_of_eq ?_)
  field_simp

/-- **The mean absolute deviation of the SK free energy is `O(N^{-1/2})`.** -/
theorem integral_abs_skFreeEnergy_sub_mean_le (N : ℕ) (hN : N ≠ 0) (h y : ℝ) :
    (∫ H : EnergySpace N, |free_energy_density (N := N) (H_field N h + y • H)
        - ∫ H' : EnergySpace N, free_energy_density (N := N) (H_field N h + y • H')
            ∂(skField N)| ∂(skField N))
      ≤ |y| / Real.sqrt (2 * (N : ℝ)) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by
    have h0 : 0 < N := Nat.pos_of_ne_zero hN
    exact_mod_cast h0
  rw [skField_eq]
  refine (integral_abs_gaussFreeEnergy_sub_mean_le (N := N) (S := skCovMatrix N 1)
    (posSemidef_skCovMatrix N 1) (D := (N : ℝ) / 2) (abs_skCovMatrix_le N) h y).trans
    (le_of_eq ?_)
  have hs : (0:ℝ) < Real.sqrt (2 * (N : ℝ)) := Real.sqrt_pos.2 (by positivity)
  rw [div_eq_div_iff (ne_of_gt hNR) (ne_of_gt hs), mul_assoc,
    ← Real.sqrt_mul (by positivity : (0:ℝ) ≤ (N : ℝ) / 2),
    show (N : ℝ) / 2 * (2 * (N : ℝ)) = (N : ℝ) ^ 2 by ring,
    Real.sqrt_sq (Nat.cast_nonneg N)]

/-! ### Self-averaging of the SK energy -/

/-- **The SK energy per site self-averages, at rate `N^{-1/2}`.** Talagrand, Vol. II,
Theorem 12.1.1: the mean absolute Gibbs fluctuation of `H/N`, integrated over an interval of
inverse temperatures, is `O(N^{-1/2})`.

The proof combines Talagrand's `(12.10)` — `SpinGlass.FiniteGibbs.intervalIntegral_absFluct_le`,
three Cauchy–Schwarz steps applied to the identity `(12.9)` — with the uniform bound
`0 ≤ ∂p_N/∂β ≤ β/2` of `deriv_skFreeEnergy_nonneg_le`, which is what makes the right-hand side
vanish in the thermodynamic limit. -/
theorem intervalIntegral_skEnergy_fluctuation_le (N : ℕ) (hN : N ≠ 0) (h : ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ β in a..b, ∫ H : EnergySpace N, (1 / (N : ℝ)) *
        FiniteGibbs.gibbs_average (α := Config N) (H_field N h + β • H)
          (fun σ => |H σ - FiniteGibbs.gibbs_average (α := Config N)
            (H_field N h + β • H) H|) ∂(skField N))
      ≤ Real.sqrt ((b - a) * (b / (2 * (N : ℝ)))) := by
  have hkey := FiniteGibbs.intervalIntegral_absFluct_le (α := Config N) (P := skField N)
    (U := fun _ => H_field N h) (V := id) N measurable_const measurable_id
    (integrable_norm_skField N) (integrable_norm_sq_skField N) hab
  refine le_trans hkey (Real.sqrt_le_sqrt ?_)
  simp only [id_eq]
  -- The bracket is `(1/N)(∂p_N/∂β(b) - ∂p_N/∂β(a))`, and `0 ≤ ∂p_N/∂β ≤ β/2`.
  have hderiv : ∀ x : ℝ, (∫ H : EnergySpace N, -(1 / (N : ℝ)) *
      FiniteGibbs.gibbs_average (α := Config N) (H_field N h + x • H) H ∂(skField N))
        = deriv (fun y => skFreeEnergy N y h) x := fun x =>
    ((hasDerivAt_skFreeEnergy N h x).deriv).symm
  rw [hderiv a, hderiv b]
  have hb := deriv_skFreeEnergy_nonneg_le N hN h (le_trans ha hab)
  have hA := deriv_skFreeEnergy_nonneg_le N hN h ha
  have hN' : (0 : ℝ) < (N : ℝ) := by positivity
  have hsub : deriv (fun y => skFreeEnergy N y h) b
      - deriv (fun y => skFreeEnergy N y h) a ≤ b / 2 := by linarith [hb.2, hA.1]
  have hba : (0 : ℝ) ≤ b - a := by linarith
  calc (b - a) * ((1 / (N : ℝ)) * (deriv (fun y => skFreeEnergy N y h) b
          - deriv (fun y => skFreeEnergy N y h) a))
      ≤ (b - a) * ((1 / (N : ℝ)) * (b / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hba
        exact mul_le_mul_of_nonneg_left hsub (by positivity)
    _ = (b - a) * (b / (2 * (N : ℝ))) := by
        rw [mul_comm (2 : ℝ) (N : ℝ)]
        field_simp

/-- **The mean energy of the SK model self-averages over the disorder** — the second half of
Talagrand's Theorem 12.1.1. For every window width `δ > 0`,

`∫_a^b 𝔼|⟨H/N⟩ - 𝔼⟨H/N⟩| dβ ≤ δ(b+δ) + 3(b-a)(b+δ)/(δ√(2N))`.

Both terms are explicit; choosing `δ = N^{-1/4}` makes the bound `O(N^{-1/4})`, exactly the rate of
Talagrand's Theorem 12.1.1. The first term comes from the increment of `∂p_N/∂β` across the window
(`deriv_skFreeEnergy_nonneg_le`), the second from Gaussian concentration of the free energy
(`integral_abs_skFreeEnergy_sub_mean_le`), and the trade-off between them is the reason the rate is
`N^{-1/4}` rather than `N^{-1/2}`. -/
theorem intervalIntegral_skMeanEnergy_fluctuation_le (N : ℕ) (hN : N ≠ 0) (h : ℝ)
    {δ a b : ℝ} (hδ : 0 < δ) (hab : a ≤ b) (haδ : 0 ≤ a - δ) :
    (∫ β in a..b, ∫ H : EnergySpace N,
        |(1 / (N : ℝ)) * FiniteGibbs.gibbs_average (α := Config N) (H_field N h + β • H) H
          - ∫ H' : EnergySpace N, (1 / (N : ℝ)) *
              FiniteGibbs.gibbs_average (α := Config N) (H_field N h + β • H') H'
              ∂(skField N)| ∂(skField N))
      ≤ δ * (b + δ) + 3 * (b - a) * ((b + δ) / Real.sqrt (2 * (N : ℝ))) / δ := by
  classical
  have hbδ : (0 : ℝ) ≤ b + δ := by linarith
  have hsqrtpos : (0 : ℝ) < Real.sqrt (2 * (N : ℝ)) := by
    refine Real.sqrt_pos.2 ?_
    have : 0 < N := Nat.pos_of_ne_zero hN
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast this
    linarith
  -- The concentration constant on the enlarged window.
  have hC : ∀ y ∈ Set.Icc (a - δ) (b + δ),
      (∫ H : EnergySpace N, |free_energy_density (N := N) (H_field N h + y • H)
          - ∫ H' : EnergySpace N, free_energy_density (N := N) (H_field N h + y • H')
              ∂(skField N)| ∂(skField N))
        ≤ (b + δ) / Real.sqrt (2 * (N : ℝ)) := by
    intro y hy
    refine (integral_abs_skFreeEnergy_sub_mean_le N hN h y).trans ?_
    have hyabs : |y| ≤ b + δ := by
      rw [abs_le]
      exact ⟨by linarith [hy.1], hy.2⟩
    gcongr
  have hkey := FiniteGibbs.intervalIntegral_integral_abs_meanEnergy_sub_le
    (α := Config N) (P := skField N) (U := fun _ => H_field N h) (V := id)
    N measurable_const measurable_id (integrable_const _) (integrable_norm_skField N)
    hδ hab hC
  refine le_trans hkey ?_
  -- Identify the mean free energy with `skFreeEnergy` and bound the derivative increment.
  have hp : ∀ y : ℝ,
      (∫ H : EnergySpace N, free_energy_density (N := N) (H_field N h + y • H) ∂(skField N))
        = skFreeEnergy N y h := fun y => (skFreeEnergy_eq_integral_field N y h).symm
  have hderiv_eq : ∀ z : ℝ,
      deriv (fun y : ℝ => ∫ w : EnergySpace N, FiniteGibbs.free_energy_density (α := Config N) N
          ((fun _ => H_field N h) w + y • id w) ∂(skField N)) z
        = deriv (fun y : ℝ => skFreeEnergy N y h) z := fun z => by
    congr 1
    funext y
    exact hp y
  rw [hderiv_eq, hderiv_eq]
  have hdb := deriv_skFreeEnergy_nonneg_le N hN h hbδ
  have hda := deriv_skFreeEnergy_nonneg_le N hN h haδ
  have hincr : deriv (fun y => skFreeEnergy N y h) (b + δ)
      - deriv (fun y => skFreeEnergy N y h) (a - δ) ≤ (b + δ) / 2 := by
    linarith [hdb.2, hda.1]
  have h1 : 2 * δ * (deriv (fun y => skFreeEnergy N y h) (b + δ)
      - deriv (fun y => skFreeEnergy N y h) (a - δ)) ≤ δ * (b + δ) := by
    calc 2 * δ * (deriv (fun y => skFreeEnergy N y h) (b + δ)
          - deriv (fun y => skFreeEnergy N y h) (a - δ))
        ≤ 2 * δ * ((b + δ) / 2) := mul_le_mul_of_nonneg_left hincr (by positivity)
      _ = δ * (b + δ) := by ring
  linarith

/-- **Talagrand, Vol. II, Theorem 12.1.1, for the SK model.** The total fluctuation of the energy
per site — under the Gibbs measure *and* the disorder — integrated over an interval of inverse
temperatures, is explicitly bounded:

`∫_a^b 𝔼⟨|H/N - 𝔼⟨H/N⟩|⟩ dβ ≤ √((b-a)b/(2N)) + δ(b+δ) + 3(b-a)(b+δ)/(δ√(2N))`

for every window width `δ > 0`. The first summand is the Gibbs fluctuation (equation (12.10),
rate `N^{-1/2}`); the second and third are the disorder fluctuation of `⟨H/N⟩`, and choosing
`δ = N^{-1/4}` balances them at `N^{-1/4}` — Talagrand's rate. -/
theorem intervalIntegral_skTotalEnergy_fluctuation_le (N : ℕ) (hN : N ≠ 0) (h : ℝ)
    {δ a b : ℝ} (hδ : 0 < δ) (hab : a ≤ b) (haδ : 0 ≤ a - δ) :
    (∫ β in a..b, ∫ H : EnergySpace N,
        FiniteGibbs.gibbs_average (α := Config N) (H_field N h + β • H)
          (fun σ => |(1 / (N : ℝ)) * H σ - ∫ H' : EnergySpace N, (1 / (N : ℝ)) *
              FiniteGibbs.gibbs_average (α := Config N) (H_field N h + β • H') H'
              ∂(skField N)|) ∂(skField N))
      ≤ Real.sqrt ((b - a) * (b / (2 * (N : ℝ))))
        + (δ * (b + δ) + 3 * (b - a) * ((b + δ) / Real.sqrt (2 * (N : ℝ))) / δ) := by
  have ha : (0 : ℝ) ≤ a := by linarith
  have hsplit := FiniteGibbs.intervalIntegral_integral_totalFluct_le (α := Config N)
    (P := skField N) (U := fun _ => H_field N h) (V := id) N measurable_const measurable_id
    (integrable_norm_skField N) hab
  refine le_trans hsplit (add_le_add ?_ ?_)
  · exact intervalIntegral_skEnergy_fluctuation_le N hN h ha hab
  · exact intervalIntegral_skMeanEnergy_fluctuation_le N hN h hδ hab haδ

end

end SpinGlass
