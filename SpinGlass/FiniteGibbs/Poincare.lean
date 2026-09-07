import SpinGlass.FiniteGibbs.Calculus
import Common.Mathlib.Probability.Distributions.Gaussian_Poincare

/-!
# `L²` self-averaging for the finite-volume free energy

The Gaussian Poincaré inequality
`ProbabilityTheory.IsGaussian.variance_le_opNorm_covarianceOperator_mul_sq` applied to
`free_energy_density`, whose derivative is bounded by `1/n` uniformly
(`norm_fderiv_free_energy_density_le`). The resulting variance bound is `‖C‖ / n²`, so the free
energy density self-averages at rate `n⁻¹` in `L²` whenever the disorder covariance operator has
bounded norm.
-/

open scoped BigOperators ENNReal NNReal ProbabilityTheory RealInnerProductSpace Topology

open MeasureTheory Filter Real
open scoped Gradient

namespace SpinGlass

namespace FiniteGibbs

noncomputable section


/-!
## `L²` self-averaging for `FiniteGibbs.free_energy_density`
-/

open scoped BigOperators

variable {α : Type*} [Fintype α] [Nonempty α]

variable {μ : Measure (EnergySpace α)} [ProbabilityTheory.IsGaussian μ]

/-- The free energy density is square-integrable (`L²`) under any Gaussian law on `EnergySpace
α`. -/
theorem memLp_free_energy_density (n : ℕ) :
    MemLp (fun H : EnergySpace α => free_energy_density (α := α) n H) 2 μ := by
  classical
  have hmeas :
      AEStronglyMeasurable (fun H : EnergySpace α => free_energy_density (α := α) n H) μ := by
    have hF : Measurable (fun H : EnergySpace α => free_energy_density (α := α) n H) :=
      (contDiff_free_energy_density (α := α) (n := n)).continuous.measurable
    exact hF.aestronglyMeasurable
  have hIntSq :
      Integrable (fun H : EnergySpace α => (free_energy_density (α := α) n H) ^ 2) μ := by
    let C0 : ℝ := Real.log (Fintype.card α) + 1
    have hF_sq_meas :
        Measurable (fun H : EnergySpace α => (free_energy_density (α := α) n H) ^ 2) := by
      have hF : Measurable (fun H : EnergySpace α => free_energy_density (α := α) n H) :=
        (contDiff_free_energy_density (α := α) (n := n)).continuous.measurable
      simpa using (hF.pow_const 2)
    refine ProbabilityTheory.IsGaussian.integrable_of_abs_le_mul_one_add_norm_pow (μ := μ)
      (E := EnergySpace α)
      (F := fun H : EnergySpace α => (free_energy_density (α := α) n H) ^ 2)
      hF_sq_meas (C := C0 ^ 2) (m := 2) (hC := by positivity) ?_
    intro H
    have habs : |free_energy_density (α := α) n H| ≤ C0 * (1 + ‖H‖) := by
      simpa [C0] using (abs_free_energy_density_le (α := α) (n := n) (H := H))
    have hpow :
        |free_energy_density (α := α) n H| ^ 2 ≤ (C0 * (1 + ‖H‖)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) habs 2
    calc
      |(free_energy_density (α := α) n H) ^ 2|
          = |free_energy_density (α := α) n H| ^ 2 := by simp
      _ ≤ (C0 * (1 + ‖H‖)) ^ 2 := hpow
      _ = (C0 ^ 2) * (1 + ‖H‖) ^ 2 := by ring
  exact (memLp_two_iff_integrable_sq hmeas).2 hIntSq

/-- `Var[free_energy_density; μ] ≤ ‖covarianceOperator μ‖ / n²`. -/
theorem variance_free_energy_density_le
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0) (n : ℕ) :
    Var[(fun H : EnergySpace α => free_energy_density (α := α) n H); μ]
      ≤ ‖ProbabilityTheory.covarianceOperator μ‖ * (1 / (n : ℝ)) ^ 2 := by
  have hfInf :
      ContDiff ℝ (⊤ : ℕ∞) (fun H : EnergySpace α => free_energy_density (α := α) n H) := by
    simpa using (contDiff_free_energy_density (α := α) (n := n))
  have hf :
      ContDiff ℝ 1 (fun H : EnergySpace α => free_energy_density (α := α) n H) :=
    hfInf.of_le (by simp)
  have hderiv :
      ∀ x : EnergySpace α,
        ‖fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H) x‖ ≤
          (1 / (n : ℝ)) := by
    intro x
    simpa using (norm_fderiv_free_energy_density_le (α := α) (n := n) x)
  simpa using
    (ProbabilityTheory.IsGaussian.variance_le_opNorm_covarianceOperator_mul_sq
      (H := EnergySpace α) (μ := μ) hmean0 hf (K := (1 / (n : ℝ))) hderiv)

/-- An `L²`-form of self-averaging: the centered second moment is bounded by the same RHS. -/
theorem
    integral_sub_mean_sq_free_energy_density_le
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0) (n : ℕ) :
    (∫ H : EnergySpace α,
        (free_energy_density (α := α) n H -
            μ[fun H : EnergySpace α => free_energy_density (α := α) n H]) ^ 2 ∂μ)
      ≤ ‖ProbabilityTheory.covarianceOperator μ‖ * (1 / (n : ℝ)) ^ 2 := by
  let F : EnergySpace α → ℝ := fun H => free_energy_density (α := α) n H
  have hF_mem : MemLp F 2 μ := memLp_free_energy_density (μ := μ) (α := α) n
  have hF_meas : AEMeasurable F μ := hF_mem.1.aemeasurable
  have hVarEq : Var[F; μ] = ∫ H, (F H - μ[F]) ^ 2 ∂μ :=
    ProbabilityTheory.variance_eq_integral (μ := μ) hF_meas
  have hVar :
      Var[F; μ] ≤ ‖ProbabilityTheory.covarianceOperator μ‖ * (1 / (n : ℝ)) ^ 2 :=
    variance_free_energy_density_le
      (α := α) (μ := μ) hmean0 n
  simpa [F, hVarEq] using hVar

/-- A Chebyshev-type tail bound for the free energy density under a Gaussian law. -/
theorem meas_ge_le_free_energy_density_sub_mean_div_sq
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    μ {H : EnergySpace α |
        c ≤
          |free_energy_density (α := α) n H
            - μ[fun H : EnergySpace α => free_energy_density (α := α) n H]|}
      ≤ ENNReal.ofReal
          ((‖ProbabilityTheory.covarianceOperator μ‖ * (1 / (n : ℝ)) ^ 2) / c ^ 2) := by
  let F : EnergySpace α → ℝ := fun H => free_energy_density (α := α) n H
  let C : ℝ := ‖ProbabilityTheory.covarianceOperator μ‖ * (1 / (n : ℝ)) ^ 2
  have hF_mem : MemLp F 2 μ := memLp_free_energy_density (μ := μ) (α := α) n
  have hCheb :
      μ {H : EnergySpace α | c ≤ |F H - μ[F]|}
        ≤ ENNReal.ofReal (Var[F; μ] / c ^ 2) :=
    ProbabilityTheory.meas_ge_le_variance_div_sq (μ := μ) (X := F) hF_mem hc
  have hVar : Var[F; μ] ≤ C :=
    (variance_free_energy_density_le
      (α := α) (μ := μ) hmean0 n)
  have hDiv : Var[F; μ] / c ^ 2 ≤ C / c ^ 2 :=
    div_le_div_of_nonneg_right hVar (sq_nonneg c)
  have hOfReal : ENNReal.ofReal (Var[F; μ] / c ^ 2) ≤ ENNReal.ofReal (C / c ^ 2) :=
    ENNReal.ofReal_le_ofReal hDiv
  have htail : μ {H : EnergySpace α | c ≤ |F H - μ[F]|} ≤ ENNReal.ofReal (C / c ^ 2) :=
    le_trans hCheb hOfReal
  simpa [F, C] using htail

/-! ### The sharp form: the Dirichlet energy is a two-replica covariance

`ProbabilityTheory.IsGaussian.variance_le_opNorm_covarianceOperator_mul_sq` bounds the variance by
`‖covarianceOperator μ‖ / n²`, which is correct but blunt: the operator norm of the covariance on
`EnergySpace α` grows with the *number of configurations*. The sharp Poincaré inequality
`variance_le_integral_inner_covarianceOperator_gradient` bounds it instead by the Dirichlet energy
of the free energy density, and that quantity is a genuinely thermodynamic one — the Gibbs average
of the covariance kernel over two independent replicas, which for a mixed `p`-spin model is
`N ξ(R₁₂)`. -/

/-- **The gradient of the free energy density is the Gibbs measure**, scaled by `-1/n`:
`∇F_n(H) = -(1/n) ∑_σ ⟨σ⟩ e_σ`. -/
lemma gradient_free_energy_density (n : ℕ) (H : EnergySpace α) :
    ∇ (fun H' : EnergySpace α => free_energy_density (α := α) n H') H
      = -(1 / (n : ℝ)) • ∑ σ : α, gibbs_pmf (α := α) H σ • std_basis (α := α) σ := by
  classical
  refine ext_inner_right ℝ fun h => ?_
  rw [inner_gradient_left, fderiv_free_energy_density_apply, real_inner_smul_left, sum_inner]
  simp only [real_inner_smul_left, inner_std_basis_apply, Finset.mul_sum]

/-- **Self-averaging of the free energy density, sharp form.** The variance is bounded by the
disorder average of the Gibbs average of the covariance kernel over two independent replicas,
divided by `n²`. For a mixed `p`-spin model the inner double sum is `N ξ(R₁₂)`, so this is a
bound of order `1/n`, whereas the operator-norm form
(`variance_free_energy_density_le`) is of the order of the number of configurations. -/
theorem variance_free_energy_density_le_gibbs_covariance
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0) (n : ℕ) :
    Var[(fun H : EnergySpace α => free_energy_density (α := α) n H); μ]
      ≤ (1 / (n : ℝ)) ^ 2 * ∫ H : EnergySpace α,
          (∑ σ : α, ∑ τ : α, gibbs_pmf (α := α) H σ * gibbs_pmf (α := α) H τ
            * (ProbabilityTheory.covarianceOperator μ (std_basis (α := α) σ)) τ) ∂μ := by
  classical
  have hf : ContDiff ℝ 1 (fun H : EnergySpace α => free_energy_density (α := α) n H) :=
    (contDiff_free_energy_density (α := α) (n := n)).of_le (by simp)
  have hderiv : ∀ x : EnergySpace α,
      ‖fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H) x‖
        ≤ (1 / (n : ℝ)) := fun x => norm_fderiv_free_energy_density_le (α := α) (n := n) x
  refine le_trans
    (ProbabilityTheory.IsGaussian.variance_le_integral_inner_covarianceOperator_gradient
      (μ := μ) hmean0 hf hderiv) (le_of_eq ?_)
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun H => ?_)
  set v : EnergySpace α := ∑ σ : α, gibbs_pmf (α := α) H σ • std_basis (α := α) σ with hv
  have hCv : ⟪ProbabilityTheory.covarianceOperator μ v, v⟫
      = ∑ σ : α, ∑ τ : α, gibbs_pmf (α := α) H σ * gibbs_pmf (α := α) H τ
          * (ProbabilityTheory.covarianceOperator μ (std_basis (α := α) σ)) τ := by
    have hmap : ProbabilityTheory.covarianceOperator μ v
        = ∑ σ : α, gibbs_pmf (α := α) H σ
            • ProbabilityTheory.covarianceOperator μ (std_basis (α := α) σ) := by
      rw [hv, map_sum]
      exact Finset.sum_congr rfl fun σ _ => map_smul _ _ _
    rw [hmap, sum_inner]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [real_inner_smul_left, hv, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [real_inner_smul_right, real_inner_comm, inner_std_basis_apply]
    ring
  simp only []
  rw [gradient_free_energy_density (α := α) n H, ← hv, map_smul, real_inner_smul_left,
    real_inner_smul_right, hCv]
  ring

end

end FiniteGibbs

end SpinGlass
