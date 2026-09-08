/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.GaussianTrace
import SpinGlass.FiniteGibbs.GGDefect
import SpinGlass.FiniteGibbs.ParameterDerivative

/-!
# The derivative of the mean free energy in the disorder strength

For a centered Gaussian disorder `H` with covariance kernel `c` and a deterministic field `c₀`, the
derivative of the mean free energy of `β H + c₀` in `β` is the **covariance gap**:

`∂/∂β 𝔼 F_n(β H + c₀) = (β/n) · 𝔼( ⟨c(σ, σ)⟩ - ⟨c(σ¹, σ²)⟩ )`.

Talagrand, *Mean Field Models for Spin Glasses*, Vol. I, Lemma 1.3.11; Vol. II, Lemma 12.1.4. The
mechanism is one Gaussian integration by parts, in the two-map trace form
(`integral_fderiv_free_energy_density_clm_add_apply_clm`): the derivative of the free energy is
`-⟨H⟩/n` (`hasDerivAt_free_energy_density_add_smul`), and integrating `⟨H⟩` by parts against the
Gaussian trades the Hamiltonian for the Hessian of the free energy contracted with the covariance,
which is exactly the difference between the diagonal bracket and the two-replica bracket.

For a mixed `p`-spin model, `c σ τ = n ξ(R_{στ})` and `c σ σ = n ξ(1)`, so the identity reads
`∂p_n/∂β = β(ξ(1) - 𝔼⟨ξ(R₁₂)⟩)`; for the SK model, `ξ(r) = r²/2` and it is
`∂p_n/∂β = (β/2)(1 - 𝔼⟨R₁₂²⟩)`, Talagrand's Lemma 1.3.11 verbatim.

## Main statements

- `SpinGlass.FiniteGibbs.hessian_free_energy_covarianceOperator_std_basis` — the Hessian of the free
  energy contracted with `(C e_σ, e_σ)` is `(p_σ c(σ,σ) - p_σ ⟨c(σ, ·)⟩)/n`.
- `SpinGlass.FiniteGibbs.integral_gibbs_average_self_eq_covariance_gap` — the identity above.
- `SpinGlass.FiniteGibbs.integral_gibbs_average_self_eq_of_diag` — its constant-diagonal form.
-/

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology

namespace SpinGlass

namespace FiniteGibbs

noncomputable section

variable {α : Type*} [Fintype α] [Nonempty α]
variable {μ : Measure (EnergySpace α)} [IsGaussian μ]

/-! ### The Hessian contracted against a covariance direction -/

omit [Nonempty α] [IsGaussian μ] in
/-- **The Hessian of the free energy in a covariance direction.** Contracting the Gibbs covariance
form with `(C e_σ, e_σ)` produces the Gibbs weight of `σ` times the gap between the diagonal
`c(σ,σ)` and the fresh-replica covariance `⟨c(σ, ·)⟩`. -/
lemma hessian_free_energy_covarianceOperator_std_basis (n : ℕ) (K : EnergySpace α) (σ : α) :
    hessian_free_energy (α := α) n K (covarianceOperator μ (std_basis (α := α) σ))
        (std_basis (α := α) σ)
      = (1 / (n : ℝ)) *
          (gibbs_pmf (α := α) K σ * (covarianceOperator μ (std_basis (α := α) σ)) σ
            - gibbs_pmf (α := α) K σ * freshCov μ K σ) := by
  classical
  have h1 : (∑ ρ : α, gibbs_pmf (α := α) K ρ
        * (covarianceOperator μ (std_basis (α := α) σ)) ρ * (std_basis (α := α) σ) ρ)
      = gibbs_pmf (α := α) K σ * (covarianceOperator μ (std_basis (α := α) σ)) σ := by
    rw [Finset.sum_eq_single_of_mem σ (Finset.mem_univ σ)]
    · simp [std_basis]
    · intro ρ _ hρ
      simp [std_basis, Ne.symm hρ]
  have h2 : (∑ ρ : α, gibbs_pmf (α := α) K ρ * (std_basis (α := α) σ) ρ)
      = gibbs_pmf (α := α) K σ := sum_gibbs_pmf_mul_std_basis (α := α) K σ
  simp only [hessian_free_energy, freshCov_apply]
  rw [h1, h2]
  ring

/-! ### The covariance gap -/

/-- The integrand of the covariance gap: the diagonal bracket minus the two-replica bracket. -/
def covarianceGap (μ : Measure (EnergySpace α)) (K : EnergySpace α) : ℝ :=
  gibbs_average (α := α) K (fun σ => (covarianceOperator μ (std_basis (α := α) σ)) σ)
    - gibbs_average (α := α) K (fun σ => freshCov μ K σ)

omit [Nonempty α] [IsGaussian μ] in
/-- The two-replica bracket form of the covariance gap. -/
lemma covarianceGap_eq (K : EnergySpace α) :
    covarianceGap μ K
      = gibbs_average (α := α) K (fun σ => (covarianceOperator μ (std_basis (α := α) σ)) σ)
        - ∑ σ : α, ∑ τ : α, gibbs_pmf (α := α) K σ * gibbs_pmf (α := α) K τ
            * (covarianceOperator μ (std_basis (α := α) σ)) τ := by
  classical
  rw [covarianceGap]
  congr 1
  simp only [gibbs_average, freshCov_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => by ring

omit [IsGaussian μ] in
lemma abs_covarianceGap_le (K : EnergySpace α) :
    |covarianceGap μ K| ≤ 2 * ‖covarianceOperator μ‖ := by
  classical
  have hnorm : ∀ σ : α, |(covarianceOperator μ (std_basis (α := α) σ)) σ|
      ≤ ‖covarianceOperator μ‖ := by
    intro σ
    refine (abs_apply_le_norm (α := α) _ σ).trans ?_
    calc ‖covarianceOperator μ (std_basis (α := α) σ)‖
        ≤ ‖covarianceOperator μ‖ * ‖std_basis (α := α) σ‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖covarianceOperator μ‖ := by rw [norm_std_basis (α := α) σ, mul_one]
  have hd : |gibbs_average (α := α) K
      (fun σ => (covarianceOperator μ (std_basis (α := α) σ)) σ)| ≤ ‖covarianceOperator μ‖ := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc (∑ σ : α, |gibbs_pmf (α := α) K σ
            * (covarianceOperator μ (std_basis (α := α) σ)) σ|)
        ≤ ∑ σ : α, gibbs_pmf (α := α) K σ * ‖covarianceOperator μ‖ := by
          refine Finset.sum_le_sum fun σ _ => ?_
          rw [abs_mul, abs_of_nonneg (gibbs_pmf_nonneg (α := α) K σ)]
          exact mul_le_mul_of_nonneg_left (hnorm σ) (gibbs_pmf_nonneg (α := α) K σ)
      _ = ‖covarianceOperator μ‖ := by
          rw [← Finset.sum_mul, sum_gibbs_pmf (α := α) K, one_mul]
  have hf : |gibbs_average (α := α) K (fun σ => freshCov μ K σ)|
      ≤ ‖covarianceOperator μ‖ := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc (∑ σ : α, |gibbs_pmf (α := α) K σ * freshCov μ K σ|)
        ≤ ∑ σ : α, gibbs_pmf (α := α) K σ * ‖covarianceOperator μ‖ := by
          refine Finset.sum_le_sum fun σ _ => ?_
          rw [abs_mul, abs_of_nonneg (gibbs_pmf_nonneg (α := α) K σ)]
          exact mul_le_mul_of_nonneg_left (abs_freshCov_le (μ := μ) K σ)
            (gibbs_pmf_nonneg (α := α) K σ)
      _ = ‖covarianceOperator μ‖ := by
          rw [← Finset.sum_mul, sum_gibbs_pmf (α := α) K, one_mul]
  calc |covarianceGap μ K| ≤ _ := abs_sub _ _
    _ ≤ 2 * ‖covarianceOperator μ‖ := by linarith

/-! ### The identity -/

omit [IsGaussian μ] in
lemma continuous_covarianceGap : Continuous fun K : EnergySpace α => covarianceGap μ K := by
  classical
  simp only [covarianceGap, gibbs_average]
  refine Continuous.sub (continuous_finsetSum _ fun σ _ => ?_)
    (continuous_finsetSum _ fun σ _ => ?_)
  · exact ((contDiff_gibbs_pmf (α := α) σ).continuous).mul continuous_const
  · exact ((contDiff_gibbs_pmf (α := α) σ).continuous).mul (continuous_freshCov (μ := μ) σ)

/-- **The derivative of the mean free energy in the disorder strength is the covariance gap.**
Talagrand, Vol. I, Lemma 1.3.11; Vol. II, Lemma 12.1.4:

`∂/∂β 𝔼 F_n(β H + c₀) = (β/n) · 𝔼( ⟨c(σ,σ)⟩ - ⟨c(σ¹,σ²)⟩ )`,

with the left-hand side written as `-𝔼⟨H⟩/n`, which is what
`hasDerivAt_free_energy_density_add_smul` computes it to be. One Gaussian integration by parts, in
the two-map trace form. -/
theorem integral_gibbs_average_self_eq_covariance_gap
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0) (n : ℕ) (β : ℝ) (c₀ : EnergySpace α) :
    (-(1 / (n : ℝ)) * ∫ x : EnergySpace α, gibbs_average (α := α) (β • x + c₀) x ∂μ)
      = β * ((1 / (n : ℝ)) * ∫ x : EnergySpace α, covarianceGap μ (β • x + c₀) ∂μ) := by
  classical
  set F : EnergySpace α → ℝ := fun H => free_energy_density (α := α) n H with hF
  set A : EnergySpace α →L[ℝ] EnergySpace α := β • ContinuousLinearMap.id ℝ (EnergySpace α) with hA
  set B : EnergySpace α →L[ℝ] EnergySpace α := ContinuousLinearMap.id ℝ (EnergySpace α) with hB
  have hAx : ∀ x : EnergySpace α, A x = β • x := fun x => by simp [hA, hB]
  have hBx : ∀ x : EnergySpace α, B x = x := fun x => by simp [hB]
  have htrace := integral_fderiv_free_energy_density_clm_add_apply_clm
    (α := α) (D := EnergySpace α) μ hmean0 (EuclideanSpace.basisFun α ℝ) A B c₀ n
  -- The left-hand side is `-𝔼⟨H⟩/n`.
  have hpt : ∀ x : EnergySpace α, (fderiv ℝ F (A x + c₀)) (B x)
      = -(1 / (n : ℝ)) * gibbs_average (α := α) (β • x + c₀) x := by
    intro x
    rw [hAx x, hBx x]
    simpa [gibbs_average] using
      fderiv_free_energy_density_apply (α := α) n (β • x + c₀) x
  have hL : (∫ x : EnergySpace α, (fderiv ℝ F (A x + c₀)) (B x) ∂μ)
      = -(1 / (n : ℝ)) * ∫ x : EnergySpace α, gibbs_average (α := α) (β • x + c₀) x ∂μ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  -- The right-hand side is `β/n` times the covariance gap.
  have hbound : ∀ (σ : α) (x : EnergySpace α),
      ‖β * ((1 / (n : ℝ)) * (gibbs_pmf (α := α) (β • x + c₀) σ
            * (covarianceOperator μ (std_basis (α := α) σ)) σ
          - gibbs_pmf (α := α) (β • x + c₀) σ * freshCov μ (β • x + c₀) σ))‖
        ≤ |β| * ((1 / (n : ℝ)) * (2 * ‖covarianceOperator μ‖)) := by
    intro σ x
    have hnorm : |(covarianceOperator μ (std_basis (α := α) σ)) σ| ≤ ‖covarianceOperator μ‖ := by
      refine (abs_apply_le_norm (α := α) _ σ).trans ?_
      calc ‖covarianceOperator μ (std_basis (α := α) σ)‖
          ≤ ‖covarianceOperator μ‖ * ‖std_basis (α := α) σ‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖covarianceOperator μ‖ := by rw [norm_std_basis (α := α) σ, mul_one]
    have hp0 := gibbs_pmf_nonneg (α := α) (β • x + c₀) σ
    have hp1 := gibbs_pmf_le_one (α := α) (β • x + c₀) σ
    have hf := abs_freshCov_le (μ := μ) (β • x + c₀) σ
    have hd : |gibbs_pmf (α := α) (β • x + c₀) σ
        * (covarianceOperator μ (std_basis (α := α) σ)) σ| ≤ ‖covarianceOperator μ‖ := by
      rw [abs_mul, abs_of_nonneg hp0]
      calc gibbs_pmf (α := α) (β • x + c₀) σ
              * |(covarianceOperator μ (std_basis (α := α) σ)) σ|
          ≤ 1 * ‖covarianceOperator μ‖ := by
            exact mul_le_mul hp1 hnorm (abs_nonneg _) zero_le_one
        _ = ‖covarianceOperator μ‖ := one_mul _
    have hfr : |gibbs_pmf (α := α) (β • x + c₀) σ * freshCov μ (β • x + c₀) σ|
        ≤ ‖covarianceOperator μ‖ := by
      rw [abs_mul, abs_of_nonneg hp0]
      calc gibbs_pmf (α := α) (β • x + c₀) σ * |freshCov μ (β • x + c₀) σ|
          ≤ 1 * ‖covarianceOperator μ‖ := mul_le_mul hp1 hf (abs_nonneg _) zero_le_one
        _ = ‖covarianceOperator μ‖ := one_mul _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (n:ℝ))]
    gcongr
    calc |gibbs_pmf (α := α) (β • x + c₀) σ
              * (covarianceOperator μ (std_basis (α := α) σ)) σ
            - gibbs_pmf (α := α) (β • x + c₀) σ * freshCov μ (β • x + c₀) σ|
        ≤ _ := abs_sub _ _
      _ ≤ 2 * ‖covarianceOperator μ‖ := by linarith
  have hint : ∀ σ : α, Integrable (fun x : EnergySpace α =>
      β * ((1 / (n : ℝ)) * (gibbs_pmf (α := α) (β • x + c₀) σ
            * (covarianceOperator μ (std_basis (α := α) σ)) σ
          - gibbs_pmf (α := α) (β • x + c₀) σ * freshCov μ (β • x + c₀) σ))) μ := by
    intro σ
    refine Integrable.of_bound ?_ _ (Filter.Eventually.of_forall (hbound σ))
    have hc : Continuous fun x : EnergySpace α => gibbs_pmf (α := α) (β • x + c₀) σ :=
      ((contDiff_gibbs_pmf (α := α) σ).continuous).comp (by fun_prop)
    have hc2 : Continuous fun x : EnergySpace α => freshCov μ (β • x + c₀) σ :=
      (continuous_freshCov (μ := μ) σ).comp (by fun_prop)
    exact (((hc.mul continuous_const).sub (hc.mul hc2)).const_mul _).const_mul _
      |>.aestronglyMeasurable
  have hR : (∑ σ : α, ∫ x : EnergySpace α,
        ((fderiv ℝ (fderiv ℝ F) (A x + c₀))
            (A (covarianceOperator μ (EuclideanSpace.basisFun α ℝ σ))))
          (B (EuclideanSpace.basisFun α ℝ σ)) ∂μ)
      = β * ((1 / (n : ℝ)) * ∫ x : EnergySpace α, covarianceGap μ (β • x + c₀) ∂μ) := by
    have hterm : ∀ (σ : α) (x : EnergySpace α),
        ((fderiv ℝ (fderiv ℝ F) (A x + c₀))
            (A (covarianceOperator μ (EuclideanSpace.basisFun α ℝ σ))))
          (B (EuclideanSpace.basisFun α ℝ σ))
          = β * ((1 / (n : ℝ)) * (gibbs_pmf (α := α) (β • x + c₀) σ
                * (covarianceOperator μ (std_basis (α := α) σ)) σ
              - gibbs_pmf (α := α) (β • x + c₀) σ * freshCov μ (β • x + c₀) σ)) := by
      intro σ x
      rw [← std_basis_eq_basisFun σ, hAx x, hA, hB]
      simp only [smul_apply, ContinuousLinearMap.coe_id', id_eq,
        ContinuousLinearMap.map_smul, smul_eq_mul]
      rw [show (fderiv ℝ (fderiv ℝ F) (β • x + c₀))
            (covarianceOperator μ (std_basis (α := α) σ)) (std_basis (α := α) σ)
          = hessian_free_energy (α := α) n (β • x + c₀)
              (covarianceOperator μ (std_basis (α := α) σ)) (std_basis (α := α) σ) from
        hessian_free_energy_fderiv_eq_hessian_free_energy (α := α) n (β • x + c₀) _ _,
        hessian_free_energy_covarianceOperator_std_basis (μ := μ) n (β • x + c₀) σ]
    calc (∑ σ : α, ∫ x : EnergySpace α,
          ((fderiv ℝ (fderiv ℝ F) (A x + c₀))
              (A (covarianceOperator μ (EuclideanSpace.basisFun α ℝ σ))))
            (B (EuclideanSpace.basisFun α ℝ σ)) ∂μ)
        = ∑ σ : α, ∫ x : EnergySpace α,
            β * ((1 / (n : ℝ)) * (gibbs_pmf (α := α) (β • x + c₀) σ
                  * (covarianceOperator μ (std_basis (α := α) σ)) σ
                - gibbs_pmf (α := α) (β • x + c₀) σ * freshCov μ (β • x + c₀) σ)) ∂μ :=
          Finset.sum_congr rfl fun σ _ =>
            integral_congr_ae (Filter.Eventually.of_forall fun x => hterm σ x)
      _ = ∫ x : EnergySpace α, ∑ σ : α,
            β * ((1 / (n : ℝ)) * (gibbs_pmf (α := α) (β • x + c₀) σ
                  * (covarianceOperator μ (std_basis (α := α) σ)) σ
                - gibbs_pmf (α := α) (β • x + c₀) σ * freshCov μ (β • x + c₀) σ)) ∂μ :=
          (integral_finsetSum _ fun σ _ => hint σ).symm
      _ = β * ((1 / (n : ℝ)) * ∫ x : EnergySpace α, covarianceGap μ (β • x + c₀) ∂μ) := by
          rw [← integral_const_mul, ← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only [covarianceGap, gibbs_average, ← Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [← hL, ← hR]
  exact htrace

/-- **The covariance gap for a kernel with constant diagonal.** For every mixed `p`-spin model the
diagonal `c σ σ` is the constant `n ξ(1)`, and the identity becomes
`∂p_n/∂β = β(ξ(1) - 𝔼⟨ξ(R₁₂)⟩)`. -/
theorem integral_gibbs_average_self_eq_of_diag
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0) {d : ℝ}
    (hdiag : ∀ σ : α, (covarianceOperator μ (std_basis (α := α) σ)) σ = d)
    (n : ℕ) (β : ℝ) (c₀ : EnergySpace α) :
    (-(1 / (n : ℝ)) * ∫ x : EnergySpace α, gibbs_average (α := α) (β • x + c₀) x ∂μ)
      = β * ((1 / (n : ℝ)) *
          ∫ x : EnergySpace α, (d - gibbs_average (α := α) (β • x + c₀)
            (fun σ => freshCov μ (β • x + c₀) σ)) ∂μ) := by
  have hpt : ∀ x : EnergySpace α, covarianceGap μ (β • x + c₀)
      = d - gibbs_average (α := α) (β • x + c₀) (fun σ => freshCov μ (β • x + c₀) σ) := by
    intro x
    have hgap : covarianceGap μ (β • x + c₀)
        = gibbs_average (α := α) (β • x + c₀)
              (fun σ => (covarianceOperator μ (std_basis (α := α) σ)) σ)
          - gibbs_average (α := α) (β • x + c₀)
              (fun σ => freshCov μ (β • x + c₀) σ) := rfl
    rw [hgap]
    congr 1
    simp only [gibbs_average, hdiag]
    rw [← Finset.sum_mul, sum_gibbs_pmf (α := α) (β • x + c₀), one_mul]
  rw [integral_gibbs_average_self_eq_covariance_gap hmean0 n β c₀]
  congr 2
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

end

end FiniteGibbs

end SpinGlass
