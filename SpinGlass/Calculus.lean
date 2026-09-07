import SpinGlass.Defs
import SpinGlass.FiniteGibbs.Calculus
import SpinGlass.FiniteGibbs.Integrability
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Common.Mathlib.Probability.Distributions.Gaussian.IntegrationByParts

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology

open scoped ContDiff
open scoped ProbabilityTheory

namespace SpinGlass

variable {N : ℕ}

/-!
# Free-energy calculus

Fréchet derivatives of `Z`, `gibbs_pmf`, and `free_energy_density`. Main:
`hessian_free_energy_eq_variance`. Talagrand Vol. I, §1.3.
-/

section Derivatives

/-! ### Smoothness of `Z` and the free energy -/

/-- `Z` is `C^∞`. Talagrand Vol. I, §1.3. -/
lemma contDiff_Z (N : ℕ) : ContDiff ℝ (∞) (fun H : EnergySpace N => Z N H) := by
  simpa [Z, FiniteGibbs.Z] using (FiniteGibbs.contDiff_Z (α := Config N))

/-- `gibbs_pmf` is `C^∞`. -/
lemma contDiff_gibbs_pmf (N : ℕ) (σ : Config N) :
    ContDiff ℝ (∞) (fun H : EnergySpace N => gibbs_pmf N H σ) := by
  simpa [gibbs_pmf_eq_FiniteGibbs_gibbs_pmf] using
    (FiniteGibbs.contDiff_gibbs_pmf (α := Config N) (σ := σ))

/-- `Z(H) > 0` for every `H`. -/
lemma Z_pos_everywhere (H : EnergySpace N) : 0 < Z N H :=
  Z_pos (N := N) (H := H)

/-- `free_energy_density` is `C^∞`. Talagrand Vol. I, §1.3. -/
lemma contDiff_free_energy_density (N : ℕ) :
    ContDiff ℝ (∞) (fun H : EnergySpace N => free_energy_density (N := N) H) := by
  simpa [free_energy_density, Z, FiniteGibbs.free_energy_density, FiniteGibbs.Z, smul_eq_mul, mul_assoc] using
    (FiniteGibbs.contDiff_free_energy_density (α := Config N) (n := N))

/-!
### Fréchet derivatives

`D(log Z)(h) = -⟨h⟩`, `D²(log Z)(h,k) = ⟨hk⟩ - ⟨h⟩⟨k⟩`.
-/

/-- `D F_N(H)[v] = -(1/N) ⟨v⟩_H`. Talagrand Vol. I, §1.3. -/
lemma fderiv_free_energy_apply (H h : EnergySpace N) :
    fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H) H h =
      -(1 / (N : ℝ)) * ∑ σ : Config N, (gibbs_pmf N H σ) * h σ :=
  fderiv_free_energy_density_apply (N := N) (H := H) (h := h)

/-- Global Lipschitz bound for the free energy density. -/
lemma abs_free_energy_density_sub_le (H₁ H₂ : EnergySpace N) :
    |free_energy_density (N := N) H₂ - free_energy_density (N := N) H₁|
      ≤ (1 / (N : ℝ)) * ‖H₂ - H₁‖ := by
  simpa [free_energy_density, Z, FiniteGibbs.free_energy_density, FiniteGibbs.Z] using
    (FiniteGibbs.abs_free_energy_density_sub_le (α := Config N) (n := N) H₁ H₂)

/-- Hessian of `free_energy_density` equals Gibbs covariance. Talagrand Vol. I, §1.3. -/
lemma hessian_free_energy_eq_variance (H h k : EnergySpace N) :
    (hessian_logZ (N := N) H) h k
      = (1 / (N : ℝ)) *
          ((∑ σ : Config N, gibbs_pmf N H σ * h σ * k σ) -
            (∑ σ : Config N, gibbs_pmf N H σ * h σ) * (∑ τ : Config N, gibbs_pmf N H τ * k τ)) := by
  simpa [gibbs_covariance, hessian_free_energy] using
    (hessian_eq_covariance (N := N) (H := H) (h := h) (k := k))

end Derivatives

/-! ### Polynomial growth / integrability -/

section GaussianIntegrability

open scoped BigOperators

variable (N)

lemma abs_apply_le_norm (H : EnergySpace N) (σ : Config N) : |H σ| ≤ ‖H‖ := by
  simpa using (FiniteGibbs.abs_apply_le_norm (α := Config N) (H := H) (σ := σ))

lemma Z_le_card_mul_exp_norm (H : EnergySpace N) :
    Z N H ≤ (Fintype.card (Config N) : ℝ) * Real.exp (‖H‖) := by
  simpa [Z, FiniteGibbs.Z] using (FiniteGibbs.Z_le_card_mul_exp_norm (α := Config N) (H := H))

lemma Z_ge_exp_neg_norm (H : EnergySpace N) :
    Real.exp (-‖H‖) ≤ Z N H := by
  simpa [Z, FiniteGibbs.Z] using (FiniteGibbs.Z_ge_exp_neg_norm (α := Config N) (H := H))

lemma abs_free_energy_density_le
    (H : EnergySpace N) :
    |free_energy_density (N := N) H|
      ≤ (Real.log (Fintype.card (Config N)) + 1) * (1 + ‖H‖) := by
  simpa [free_energy_density, Z, FiniteGibbs.free_energy_density, FiniteGibbs.Z] using
    (FiniteGibbs.abs_free_energy_density_le (α := Config N) (n := N) (H := H))

/-! ### Integrability under Gaussian disorder -/
lemma integrable_free_energy_density_of_isGaussian
    {Ω : Type*} [MeasureSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {g : Ω → EnergySpace N} (hg_meas : Measurable g)
    (hg_gauss : ProbabilityTheory.IsGaussian (P.map g)) :
    Integrable (fun w : Ω => free_energy_density (N := N) (g w)) P := by
  simpa [free_energy_density, Z, FiniteGibbs.free_energy_density, FiniteGibbs.Z] using
    (FiniteGibbs.integrable_free_energy_density_of_isGaussian_map (α := Config N) (P := P) (n := N)
      (g := g) hg_meas hg_gauss)

end GaussianIntegrability

end SpinGlass
