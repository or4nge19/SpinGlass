import SpinGlass.Defs
import SpinGlass.FiniteGibbs.Poincare

/-!
# Gaussian Poincaré / `L²` self-averaging for `SpinGlass.free_energy_density`

This file specializes the model-agnostic results in
`SpinGlass.FiniteGibbs.Poincare` to `Config N` .
-/

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology
open scoped ENNReal NNReal

namespace SpinGlass

noncomputable section

variable {N : ℕ}

variable {μ : Measure (EnergySpace N)} [ProbabilityTheory.IsGaussian μ]

/-- `free_energy_density` is square-integrable (`L²`) under any Gaussian law. -/
theorem memLp_free_energy_density :
    MemLp (fun H : EnergySpace N => free_energy_density (N := N) H) 2 μ := by
  simpa [free_energy_density, Z, FiniteGibbs.free_energy_density, FiniteGibbs.Z] using
    (SpinGlass.FiniteGibbs.memLp_free_energy_density (α := Config N) (μ := μ) (n := N))

/-- **Gaussian `L²` self-averaging for `SpinGlass.free_energy_density`.**

This is the `Config N` specialization of
`SpinGlass.FiniteGibbs.variance_free_energy_density_le_pi_sq_div_eight_mul_opNorm_covarianceOperator_div_n_sq`. -/
theorem variance_free_energy_density_le_pi_sq_div_eight_mul_opNorm_covarianceOperator_div_N_sq
    (hmean0 : (∫ x : EnergySpace N, x ∂μ) = 0) :
    Var[(fun H : EnergySpace N => free_energy_density (N := N) H); μ]
      ≤ (Real.pi ^ 2 / 8) * ‖ProbabilityTheory.covarianceOperator μ‖ * (1 / (N : ℝ)) ^ 2 := by
  simpa [free_energy_density, Z, FiniteGibbs.free_energy_density, FiniteGibbs.Z] using
    (SpinGlass.FiniteGibbs.variance_free_energy_density_le_pi_sq_div_eight_mul_opNorm_covarianceOperator_div_n_sq
      (α := Config N) (μ := μ) hmean0 N)

/-- An `L²`-form of self-averaging: the centered second moment is bounded by the same RHS. -/
theorem integral_sub_mean_sq_free_energy_density_le_pi_sq_div_eight_mul_opNorm_covarianceOperator_div_N_sq
    (hmean0 : (∫ x : EnergySpace N, x ∂μ) = 0) :
    (∫ H : EnergySpace N,
        (free_energy_density (N := N) H -
            μ[fun H : EnergySpace N => free_energy_density (N := N) H]) ^ 2 ∂μ)
      ≤ (Real.pi ^ 2 / 8) * ‖ProbabilityTheory.covarianceOperator μ‖ * (1 / (N : ℝ)) ^ 2 := by
  let F : EnergySpace N → ℝ := fun H => free_energy_density (N := N) H
  have hF_mem : MemLp F 2 μ := (memLp_free_energy_density (N := N) (μ := μ))
  have hF_meas : AEMeasurable F μ := hF_mem.1.aemeasurable
  have hVarEq : Var[F; μ] = ∫ H, (F H - μ[F]) ^ 2 ∂μ :=
    ProbabilityTheory.variance_eq_integral (μ := μ) hF_meas
  have hVar : Var[F; μ] ≤ (Real.pi ^ 2 / 8) * ‖ProbabilityTheory.covarianceOperator μ‖ * (1 / (N : ℝ)) ^ 2 :=
    variance_free_energy_density_le_pi_sq_div_eight_mul_opNorm_covarianceOperator_div_N_sq
      (N := N) (μ := μ) hmean0
  simpa [F, hVarEq] using hVar

/-- A Chebyshev-type tail bound for `SpinGlass.free_energy_density` under a Gaussian law. -/
theorem meas_ge_le_free_energy_density_sub_mean_div_sq
    (hmean0 : (∫ x : EnergySpace N, x ∂μ) = 0) {c : ℝ} (hc : 0 < c) :
    μ {H : EnergySpace N |
        c ≤ |free_energy_density (N := N) H - μ[fun H : EnergySpace N => free_energy_density (N := N) H]|}
      ≤ ENNReal.ofReal
          (((Real.pi ^ 2 / 8) * ‖ProbabilityTheory.covarianceOperator μ‖ * (1 / (N : ℝ)) ^ 2) / c ^ 2) := by
  let F : EnergySpace N → ℝ := fun H => free_energy_density (N := N) H
  let C : ℝ :=
    (Real.pi ^ 2 / 8) * ‖ProbabilityTheory.covarianceOperator μ‖ * (1 / (N : ℝ)) ^ 2
  have hF_mem : MemLp F 2 μ := (memLp_free_energy_density (N := N) (μ := μ))
  have hCheb :
      μ {H : EnergySpace N | c ≤ |F H - μ[F]|} ≤ ENNReal.ofReal (Var[F; μ] / c ^ 2) :=
    ProbabilityTheory.meas_ge_le_variance_div_sq (μ := μ) (X := F) hF_mem hc
  have hVar : Var[F; μ] ≤ C :=
    variance_free_energy_density_le_pi_sq_div_eight_mul_opNorm_covarianceOperator_div_N_sq
      (N := N) (μ := μ) hmean0
  have hDiv : Var[F; μ] / c ^ 2 ≤ C / c ^ 2 :=
    div_le_div_of_nonneg_right hVar (sq_nonneg c)
  have hOfReal : ENNReal.ofReal (Var[F; μ] / c ^ 2) ≤ ENNReal.ofReal (C / c ^ 2) :=
    ENNReal.ofReal_le_ofReal hDiv
  have htail : μ {H : EnergySpace N | c ≤ |F H - μ[F]|} ≤ ENNReal.ofReal (C / c ^ 2) :=
    le_trans hCheb hOfReal
  simpa [F, C] using htail

end

end SpinGlass
