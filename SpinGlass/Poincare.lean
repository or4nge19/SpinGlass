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

end

end SpinGlass
