import SpinGlass.Defs
import SpinGlass.FiniteGibbs.Calculus
import Common.Mathlib.Probability.Distributions.Gaussian_Divergence
import Common.Mathlib.Probability.Distributions.Gaussian_IBP2_Hilbert
import Common.Mathlib.Probability.Distributions.Gaussian_IBP_Temperate

/-!
# Talagrand's covariance/Hessian trace identity, from the general divergence identity

`EnergySpace α` is `EuclideanSpace ℝ α`, whose Dirac basis `std_basis` is Mathlib's
`EuclideanSpace.basisFun`. Specializing the general Gaussian divergence identity
`IsGaussian.integral_fderiv_apply_self_eq_sum_integral_fderiv2` to that orthonormal basis gives
exactly the shape Talagrand uses in every interpolation computation:

`∫ (DF x) x ∂μ = ∑ σ, ∫ (D²F x) (C e_σ) (e_σ) ∂μ`.

Together with `IsGaussian.integral_inner_mul_inner_mul_eq_covariance_add_integral_fderiv2`
(Price's theorem) this is the complete second-order Gaussian calculus underlying Vol. I, §1.3 and
Vol. II, §8.2.

## Main statements

- `std_basis_eq_basisFun`: the Dirac basis is Mathlib's `EuclideanSpace.basisFun`.
- `integral_fderiv_apply_self_eq_sum_std_basis`: the trace identity in the Dirac basis.
- `integral_inner_mul_inner_mul_std_basis`: Price's theorem in the Dirac basis.
- `integral_fderiv_comp_clm_apply_self_std_basis`: **the interpolation trace identity** — for a
  Hamiltonian obtained as a linear image `A x + c` of the disorder, the trace is taken against the
  pushforward covariance `covarianceOperator (μ.map A)`, read in the Dirac basis. This is the
  general form of Talagrand's Eq. (1.65).
- `integral_fderiv_free_energy_density_comp_clm_apply_self` and
  `integral_fderiv_free_energy_density_clm_add_apply_clm`: the same for the free-energy density,
  with every growth hypothesis discharged. The second is the **two-map** form
  `∫ (DF_n (A x + c)) (B x) = ∑ i ∫ ((D²F_n (A x + c)) (A (C bᵢ))) (B bᵢ)`, which is what an
  interpolation derivative consumes (`A` the interpolation map, `B` its time derivative).
-/

open MeasureTheory ProbabilityTheory BigOperators
open scoped InnerProductSpace

namespace SpinGlass

namespace FiniteGibbs

noncomputable section

variable {α : Type*} [Fintype α]

/-- The Dirac basis `std_basis` is Mathlib's orthonormal basis `EuclideanSpace.basisFun`. -/
lemma std_basis_eq_basisFun (σ : α) :
    std_basis (α := α) σ = EuclideanSpace.basisFun α ℝ σ := by
  classical
  rw [std_basis_eq_single σ, EuclideanSpace.basisFun_apply]

/-! ### The free-energy density has degree-`0` polynomial growth in its derivatives

The general Gaussian trace identities are stated with explicit polynomial bounds
`‖DF z‖ ≤ C (1 + ‖z‖) ^ m`. For the free-energy density the derivative bounds are *uniform*
(`‖DF_n‖ ≤ 1/n`, `‖D²F_n‖ ≤ 2/n`), so `m = 0` and `C = 2/n` works for both; these lemmas package
that so every downstream application discharges its hypotheses by name. -/

/-- The free-energy density is `C²` (it is `C^∞`). -/
lemma contDiff_two_free_energy_density [Nonempty α] (n : ℕ) :
    ContDiff ℝ 2 (fun H : EnergySpace α => free_energy_density (α := α) n H) :=
  (contDiff_free_energy_density (α := α) n).of_le (by simp)

lemma norm_fderiv_free_energy_density_growth_nonneg (n : ℕ) : (0 : ℝ) ≤ 2 / (n : ℝ) := by
  positivity

/-- `‖DF_n‖ ≤ (2/n) (1 + ‖H‖) ^ 0`: the degree-`0` polynomial growth bound. -/
lemma norm_fderiv_free_energy_density_growth [Nonempty α] (n : ℕ) (z : EnergySpace α) :
    ‖fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H) z‖
      ≤ (2 / (n : ℝ)) * (1 + ‖z‖) ^ 0 := by
  have h12 : (1 : ℝ) / (n : ℝ) ≤ 2 / (n : ℝ) := by
    gcongr
    norm_num
  simpa using (norm_fderiv_free_energy_density_le (α := α) n z).trans h12

/-- `‖D²F_n‖ ≤ (2/n) (1 + ‖H‖) ^ 0`: the degree-`0` polynomial growth bound. -/
lemma norm_fderiv_fderiv_free_energy_density_growth [Nonempty α] (n : ℕ) (z : EnergySpace α) :
    ‖fderiv ℝ (fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H)) z‖
      ≤ (2 / (n : ℝ)) * (1 + ‖z‖) ^ 0 := by
  simpa using norm_fderiv_fderiv_free_energy_density_le (α := α) n z

variable [MeasurableSpace (EnergySpace α)] [BorelSpace (EnergySpace α)]
variable (μ : Measure (EnergySpace α)) [IsGaussian μ]

/-- **Talagrand's covariance/Hessian trace identity.** For a centered Gaussian `μ` on
`EnergySpace α` and `F` of class `C²` with polynomial growth of `DF` and `D²F`,

`∫ (DF x) x ∂μ = ∑ σ, ∫ (D²F x) (C e_σ) (e_σ) ∂μ`.

This is the general Gaussian divergence identity read in the Dirac basis; it is the identity that
turns an interpolation derivative into a covariance-weighted Hessian trace.
Talagrand Vol. I, §1.3, Eq. (1.65). -/
theorem integral_fderiv_apply_self_eq_sum_std_basis
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0)
    (F : EnergySpace α → ℝ) (hF_c2 : ContDiff ℝ 2 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF'_growth : ∀ x, ‖fderiv ℝ F x‖ ≤ C * (1 + ‖x‖) ^ m)
    (hF''_growth : ∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ C * (1 + ‖x‖) ^ m) :
    (∫ x : EnergySpace α, (fderiv ℝ F x) x ∂μ)
      = ∑ σ : α, ∫ x : EnergySpace α,
          ((fderiv ℝ (fderiv ℝ F) x) (covarianceOperator μ (std_basis (α := α) σ)))
            (std_basis (α := α) σ) ∂μ := by
  have hgen := ProbabilityTheory.IsGaussian.integral_fderiv_apply_self_eq_sum_integral_fderiv2
    (μ := μ) hmean0 (EuclideanSpace.basisFun α ℝ) F hF_c2 hC hF'_growth hF''_growth
  rw [hgen]
  exact Finset.sum_congr rfl fun σ _ => by rw [std_basis_eq_basisFun σ]

/-- **Price's theorem in the Dirac basis.** For a centered Gaussian `μ` on `EnergySpace α`, the
second-order Gaussian integration-by-parts formula at two Dirac directions. -/
theorem integral_inner_mul_inner_mul_std_basis
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0) (σ τ : α)
    (F : EnergySpace α → ℝ) (hF_meas : Measurable F) (hF_c2 : ContDiff ℝ 2 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ x, |F x| ≤ C * (1 + ‖x‖) ^ m)
    (hF'_growth : ∀ x, ‖fderiv ℝ F x‖ ≤ C * (1 + ‖x‖) ^ m)
    (hF''_growth : ∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ C * (1 + ‖x‖) ^ m) :
    (∫ x : EnergySpace α, x σ * (x τ * F x) ∂μ)
      = ⟪covarianceOperator μ (std_basis (α := α) σ), std_basis (α := α) τ⟫_ℝ
          * (∫ x : EnergySpace α, F x ∂μ)
        + ∫ x : EnergySpace α,
            ((fderiv ℝ (fderiv ℝ F) x) (covarianceOperator μ (std_basis (α := α) τ)))
              (covarianceOperator μ (std_basis (α := α) σ)) ∂μ := by
  have hgen :=
    ProbabilityTheory.IsGaussian.integral_inner_mul_inner_mul_eq_covariance_add_integral_fderiv2
      (μ := μ) hmean0 (std_basis (α := α) σ) (std_basis (α := α) τ) F hF_meas hF_c2 hC
      hF_growth hF'_growth hF''_growth
  have hcoord : ∀ (x : EnergySpace α) (ρ : α), ⟪x, std_basis (α := α) ρ⟫_ℝ = x ρ := by
    intro x ρ
    rw [real_inner_comm]
    exact inner_std_basis_apply (α := α) ρ x
  rw [← hgen]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hcoord x σ, hcoord x τ]

/-! ### The interpolation trace identity -/

section Substitution

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D] [CompleteSpace D]
variable [MeasurableSpace D] [BorelSpace D] [SecondCountableTopology D]

/-- **Talagrand's interpolation trace identity, general form.** Let `ν` be a centered Gaussian
disorder law on a Hilbert space `D`, let the Hamiltonian be the affine image `A x + c` of the
disorder under a continuous linear map `A : D →L[ℝ] EnergySpace α`, and let `F` be a functional of
temperate growth on `EnergySpace α` (e.g. the free energy density). Then

`∫ (DF (A x + c)) (A x) ∂ν = ∑ σ, ∫ ((D²F (A x + c)) (C' e_σ)) e_σ ∂ν`

where `C' = covarianceOperator (ν.map A)` is the covariance of the Hamiltonian and `e_σ` is the
Dirac basis. The left side is what Gaussian integration by parts produces from an interpolation
derivative; the right side is the covariance-weighted Hessian trace.
Talagrand Vol. I, §1.3, Eq. (1.65). -/
theorem integral_fderiv_comp_clm_apply_self_std_basis
    (ν : Measure D) [IsGaussian ν] (hmean0 : (∫ x : D, x ∂ν) = 0)
    (A : D →L[ℝ] EnergySpace α) (c : EnergySpace α)
    (F : EnergySpace α → ℝ) (hF : Function.HasTemperateGrowth F) :
    (∫ x : D, (fderiv ℝ F (A x + c)) (A x) ∂ν)
      = ∑ σ : α, ∫ x : D,
          ((fderiv ℝ (fderiv ℝ F) (A x + c))
            (covarianceOperator (ν.map A) (std_basis (α := α) σ)))
            (std_basis (α := α) σ) ∂ν := by
  have hgen := ProbabilityTheory.IsGaussian.integral_fderiv_comp_clm_apply_self
    (μ := ν) hmean0 A c (EuclideanSpace.basisFun α ℝ) F hF
  rw [hgen]
  exact Finset.sum_congr rfl fun σ _ => by rw [std_basis_eq_basisFun σ]

/-- **Talagrand's interpolation trace identity for the free-energy density.** Every hypothesis of
the general theorem is discharged here: the free-energy density is `C^∞`
(`contDiff_free_energy_density`), its derivative is bounded by `1/n`
(`norm_fderiv_free_energy_density_le`) and its second derivative by `2/n`
(`norm_fderiv_fderiv_free_energy_density_le`), all uniformly in the Hamiltonian — so the growth is
polynomial of degree `0`.

For a centered Gaussian disorder `ν` on `D` and a Hamiltonian `A x + c` obtained as an affine image
of the disorder,

`∫ (DF_n (A x + c)) (A x) ∂ν = ∑ σ, ∫ ((D²F_n (A x + c)) (C' e_σ)) e_σ ∂ν`,

with `C' = covarianceOperator (ν.map A)` the covariance of the Hamiltonian.
Talagrand Vol. I, §1.3, Eq. (1.65). -/
theorem integral_fderiv_free_energy_density_comp_clm_apply_self [Nonempty α]
    (ν : Measure D) [IsGaussian ν] (hmean0 : (∫ x : D, x ∂ν) = 0)
    (A : D →L[ℝ] EnergySpace α) (c : EnergySpace α) (n : ℕ) :
    (∫ x : D, (fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H)
          (A x + c)) (A x) ∂ν)
      = ∑ σ : α, ∫ x : D,
          ((fderiv ℝ (fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H))
            (A x + c)) (covarianceOperator (ν.map A) (std_basis (α := α) σ)))
            (std_basis (α := α) σ) ∂ν := by
  classical
  have hgen := ProbabilityTheory.IsGaussian.integral_fderiv_comp_clm_apply_self_eq_sum
    (μ := ν) hmean0 A c (EuclideanSpace.basisFun α ℝ)
    (fun H : EnergySpace α => free_energy_density (α := α) n H)
    (contDiff_two_free_energy_density (α := α) n) (norm_fderiv_free_energy_density_growth_nonneg n)
    (norm_fderiv_free_energy_density_growth n) (norm_fderiv_fderiv_free_energy_density_growth n)
  rw [hgen]
  exact Finset.sum_congr rfl fun σ _ => by rw [std_basis_eq_basisFun σ]

omit [MeasurableSpace (EnergySpace α)] [BorelSpace (EnergySpace α)] in
/-- **Talagrand's interpolation trace identity for the free-energy density, two-map form.**
This is the identity an interpolation derivative consumes: `A` is the interpolation map
`x ↦ √t·x₁ + √(1-t)·x₂` and `B` is its time derivative, so that

`∫ (DF_n (A x + c)) (B x) ∂ν = ∑ i, ∫ ((D²F_n (A x + c)) (A (C bᵢ))) (B bᵢ) ∂ν`

with `C = covarianceOperator ν` and `(bᵢ)` any orthonormal basis of the disorder space. Every
growth hypothesis of the general theorem is discharged: the free-energy density is `C^∞` with
`‖DF_n‖ ≤ 1/n` and `‖D²F_n‖ ≤ 2/n` uniformly, so the growth is polynomial of degree `0`.
Talagrand Vol. I, §1.3, Eq. (1.65). -/
theorem integral_fderiv_free_energy_density_clm_add_apply_clm [Nonempty α]
    {ι : Type*} [Fintype ι]
    (ν : Measure D) [IsGaussian ν] (hmean0 : (∫ x : D, x ∂ν) = 0)
    (b : OrthonormalBasis ι ℝ D)
    (A B : D →L[ℝ] EnergySpace α) (c : EnergySpace α) (n : ℕ) :
    (∫ x : D, (fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H)
          (A x + c)) (B x) ∂ν)
      = ∑ i : ι, ∫ x : D,
          ((fderiv ℝ (fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H))
            (A x + c)) (A (covarianceOperator ν (b i)))) (B (b i)) ∂ν :=
  ProbabilityTheory.IsGaussian.integral_fderiv_clm_add_apply_clm_eq_sum
    (μ := ν) hmean0 b A B c (fun H : EnergySpace α => free_energy_density (α := α) n H)
    (contDiff_two_free_energy_density (α := α) n) (norm_fderiv_free_energy_density_growth_nonneg n)
    (norm_fderiv_free_energy_density_growth n) (norm_fderiv_fderiv_free_energy_density_growth n)

end Substitution

end

end FiniteGibbs

end SpinGlass
