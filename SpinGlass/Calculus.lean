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
## Calculus bridge for the free energy (Talagrand)

This file packages the **calculus layer** needed to connect:

- the *abstract* Fréchet-derivative API used by the Gaussian IBP library; and
- the *explicit* Gibbs-average / covariance formulas used in the SK algebra.

The key statement is `hessian_free_energy_eq_variance`, asserting that the (abstract)
Hessian of the free energy density is exactly the Gibbs covariance bilinear form.

### References
- M. Talagrand, *Mean Field Models for Spin Glasses*, Vol. I, Ch. 1, §1.3 (differentiation of
  \(\log Z\) and the Gibbs covariance/Hessian identity used in the Guerra interpolation).
-/

section Derivatives

/-!
### Smoothness of the partition function and free energy

These are the (finite-dimensional) smoothness facts used to justify the Fréchet derivatives.
They correspond to standard computations in Talagrand’s Appendix on differentiation of
the free energy functional.
-/

/--
`Z` is smooth (`C^∞`) as a finite sum of exponentials of linear forms.

This is the finite-volume regularity input behind Talagrand’s differentiation of the free energy
functional (Vol. I, Ch. 1, §1.3).
-/
lemma contDiff_Z (N : ℕ) : ContDiff ℝ (∞) (fun H : EnergySpace N => Z N H) := by
  classical
  -- Thin wrapper around the model-agnostic `FiniteGibbs` smoothness lemma.
  simpa [Z, FiniteGibbs.Z] using (FiniteGibbs.contDiff_Z (α := Config N))

/--
`gibbs_pmf` is smooth (`C^∞`) as a quotient of smooth functions, since `Z(H) ≠ 0`.
-/
lemma contDiff_gibbs_pmf (N : ℕ) (σ : Config N) :
    ContDiff ℝ (∞) (fun H : EnergySpace N => gibbs_pmf N H σ) := by
  classical
  -- Thin wrapper around the model-agnostic `FiniteGibbs` smoothness lemma.
  simpa [gibbs_pmf, Z, FiniteGibbs.gibbs_pmf, FiniteGibbs.Z] using
    (FiniteGibbs.contDiff_gibbs_pmf (α := Config N) (σ := σ))

/--
`Z(H) > 0` for every Hamiltonian `H`.

This is the positivity condition needed to differentiate `log (Z H)` (as in Talagrand, Vol. I,
Ch. 1, §1.3).
-/
lemma Z_pos_everywhere (H : EnergySpace N) : 0 < Z N H :=
  Z_pos (N := N) (H := H)

/--
The free energy density `H ↦ (1/N) log Z(H)` is smooth.

Reference: Talagrand, Vol. I, Ch. 1, §1.3 (differentiation of the free energy).
-/
lemma contDiff_free_energy_density (N : ℕ) :
    ContDiff ℝ (∞) (fun H : EnergySpace N => free_energy_density (N := N) H) := by
  classical
  -- Thin wrapper around the model-agnostic `FiniteGibbs` smoothness lemma.
  simpa [free_energy_density, Z, FiniteGibbs.free_energy_density, FiniteGibbs.Z, smul_eq_mul, mul_assoc] using
    (FiniteGibbs.contDiff_free_energy_density (α := Config N) (n := N))

/-!
### First and second Fréchet derivatives (Talagrand: Gibbs averages and covariances)

These are the formal counterparts of the standard identities:

* \(D(\log Z)(h) = -\langle h \rangle\),
* \(D^2(\log Z)(h,k) = \langle hk \rangle - \langle h \rangle \langle k \rangle\).
-/

/--
**First derivative of the free energy density.**

This is Talagrand’s “\(D\log Z = -\langle \cdot\rangle\)” identity for the Gibbs measure,
with the extra \(1/N\) normalization of the free energy density.

Reference: Talagrand, Vol. I, Ch. 1, §1.3 (first derivative of \(\log Z\)).
-/
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

/--
**Second derivative / Hessian equals Gibbs covariance** (Talagrand).

This is the main “bridge” identity: the abstract Hessian (Fréchet second derivative)
agrees with the explicit Gibbs covariance formula.

In Talagrand’s notation, this is the identification of \(D^2 \log Z\) with the Gibbs
variance/covariance (used implicitly throughout the Guerra interpolation).

Reference: Talagrand, Vol. I, Ch. 1, §1.3 (second derivative of \(\log Z\) as a covariance).
-/
lemma hessian_free_energy_eq_variance (H h k : EnergySpace N) :
    (hessian_logZ (N := N) H) h k
      = (1 / (N : ℝ)) *
          ((∑ σ : Config N, gibbs_pmf N H σ * h σ * k σ) -
            (∑ σ : Config N, gibbs_pmf N H σ * h σ) * (∑ τ : Config N, gibbs_pmf N H τ * k τ)) := by
  simpa [gibbs_covariance, hessian_free_energy] using
    (hessian_eq_covariance (N := N) (H := H) (h := h) (k := k))

end Derivatives

/-!
### Moderate growth / integrability package (for Gaussian IBP)

For Gaussian inputs, we only need explicit polynomial-growth bounds on `free_energy_density` and
its Fréchet derivative. This is the Mathlib-idiomatic formulation used by the Cameron–Martin IBP.
-/

section GaussianIntegrability

open scoped BigOperators

variable (N)

lemma abs_apply_le_norm (H : EnergySpace N) (σ : Config N) : |H σ| ≤ ‖H‖ := by
  -- Vol II backend: the same statement holds for any finite configuration space.
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
  -- Vol II backend: use the model-agnostic linear growth bound.
  simpa [free_energy_density, Z, FiniteGibbs.free_energy_density, FiniteGibbs.Z] using
    (FiniteGibbs.abs_free_energy_density_le (α := Config N) (n := N) (H := H))

/-! A convenient integrability corollary for Gaussian disorder. -/
lemma integrable_free_energy_density_of_isGaussian
    {Ω : Type*} [MeasureSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {g : Ω → EnergySpace N} (hg_meas : Measurable g)
    (hg_gauss : ProbabilityTheory.IsGaussian (P.map g)) :
    Integrable (fun w : Ω => free_energy_density (N := N) (g w)) P := by
  -- Vol II backend: use the model-agnostic Gaussian integrability lemma.
  simpa [free_energy_density, Z, FiniteGibbs.free_energy_density, FiniteGibbs.Z] using
    (FiniteGibbs.integrable_free_energy_density_of_isGaussian_map (α := Config N) (P := P) (n := N)
      (g := g) hg_meas hg_gauss)

end GaussianIntegrability

end SpinGlass
