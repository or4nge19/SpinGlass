import SpinGlass.Defs
import SpinGlass.FiniteGibbs.Poincare

/-!
# Gaussian Poincaré for `free_energy_density`

`Config N` instance of `SpinGlass.FiniteGibbs.Poincare`.
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

/-- `Config N` instance of `FiniteGibbs` Gaussian self-averaging for `free_energy_density`. -/
theorem variance_free_energy_density_le
    (hmean0 : (∫ x : EnergySpace N, x ∂μ) = 0) :
    Var[(fun H : EnergySpace N => free_energy_density (N := N) H); μ]
      ≤ ‖ProbabilityTheory.covarianceOperator μ‖ * (1 / (N : ℝ)) ^ 2 := by
  simpa [free_energy_density, Z, FiniteGibbs.free_energy_density, FiniteGibbs.Z] using
    (SpinGlass.FiniteGibbs.variance_free_energy_density_le
      (α := Config N) (μ := μ) hmean0 N)

/-- An `L²`-form of self-averaging: the centered second moment is bounded by the same RHS. -/
theorem
    integral_sub_mean_sq_free_energy_density_le
    (hmean0 : (∫ x : EnergySpace N, x ∂μ) = 0) :
    (∫ H : EnergySpace N,
        (free_energy_density (N := N) H -
            μ[fun H : EnergySpace N => free_energy_density (N := N) H]) ^ 2 ∂μ)
      ≤ ‖ProbabilityTheory.covarianceOperator μ‖ * (1 / (N : ℝ)) ^ 2 := by
  let F : EnergySpace N → ℝ := fun H => free_energy_density (N := N) H
  have hF_mem : MemLp F 2 μ := (memLp_free_energy_density (N := N) (μ := μ))
  have hF_meas : AEMeasurable F μ := hF_mem.1.aemeasurable
  have hVarEq : Var[F; μ] = ∫ H, (F H - μ[F]) ^ 2 ∂μ :=
    ProbabilityTheory.variance_eq_integral (μ := μ) hF_meas
  have hVar : Var[F; μ] ≤ ‖ProbabilityTheory.covarianceOperator μ‖ * (1 / (N : ℝ)) ^ 2 :=
    variance_free_energy_density_le
      (N := N) (μ := μ) hmean0
  simpa [F, hVarEq] using hVar

/-- A Chebyshev-type tail bound for `SpinGlass.free_energy_density` under a Gaussian law. -/
theorem meas_ge_le_free_energy_density_sub_mean_div_sq
    (hmean0 : (∫ x : EnergySpace N, x ∂μ) = 0) {c : ℝ} (hc : 0 < c) :
    μ {H : EnergySpace N |
        c ≤ |free_energy_density (N := N) H - μ[fun H : EnergySpace N => free_energy_density (N :=
          N) H]|}
      ≤ ENNReal.ofReal
          ((‖ProbabilityTheory.covarianceOperator μ‖ * (1 / (N : ℝ)) ^ 2) / c ^ 2) := by
  let F : EnergySpace N → ℝ := fun H => free_energy_density (N := N) H
  let C : ℝ := ‖ProbabilityTheory.covarianceOperator μ‖ * (1 / (N : ℝ)) ^ 2
  have hF_mem : MemLp F 2 μ := (memLp_free_energy_density (N := N) (μ := μ))
  have hCheb :
      μ {H : EnergySpace N | c ≤ |F H - μ[F]|} ≤ ENNReal.ofReal (Var[F; μ] / c ^ 2) :=
    ProbabilityTheory.meas_ge_le_variance_div_sq (μ := μ) (X := F) hF_mem hc
  have hVar : Var[F; μ] ≤ C :=
    variance_free_energy_density_le
      (N := N) (μ := μ) hmean0
  have hDiv : Var[F; μ] / c ^ 2 ≤ C / c ^ 2 :=
    div_le_div_of_nonneg_right hVar (sq_nonneg c)
  have hOfReal : ENNReal.ofReal (Var[F; μ] / c ^ 2) ≤ ENNReal.ofReal (C / c ^ 2) :=
    ENNReal.ofReal_le_ofReal hDiv
  have htail : μ {H : EnergySpace N | c ≤ |F H - μ[F]|} ≤ ENNReal.ofReal (C / c ^ 2) :=
    le_trans hCheb hOfReal
  simpa [F, C] using htail

/-! ### The sharp form -/

/-- **`Config N` instance of the sharp Poincaré bound.** The variance of the free energy density is
at most the disorder average of the two-replica Gibbs bracket of the covariance kernel, divided by
`N²`:

`Var[F_N] ≤ (1/N²) 𝔼 ⟨c(σ¹, σ²)⟩`.

For a mixed `p`-spin model `c(σ, τ) = N ξ(R_{στ})`, so the right-hand side is `O(1/N)`. Compare
`variance_free_energy_density_le`, which replaces the bracket by `‖covarianceOperator μ‖` — an
operator norm over the whole configuration space, and therefore far larger. -/
theorem variance_free_energy_density_le_gibbs_covariance
    (hmean0 : (∫ x : EnergySpace N, x ∂μ) = 0) :
    Var[(fun H : EnergySpace N => free_energy_density (N := N) H); μ]
      ≤ (1 / (N : ℝ)) ^ 2 * ∫ H : EnergySpace N,
          gibbs_average₂ N H
            (fun σ τ => (ProbabilityTheory.covarianceOperator μ (std_basis N σ)) τ) ∂μ := by
  simpa [free_energy_density, Z, FiniteGibbs.free_energy_density, FiniteGibbs.Z,
    gibbs_average₂, gibbs_pmf, FiniteGibbs.gibbs_pmf, std_basis] using
    (SpinGlass.FiniteGibbs.variance_free_energy_density_le_gibbs_covariance
      (α := Config N) (μ := μ) hmean0 N)

end

end SpinGlass
