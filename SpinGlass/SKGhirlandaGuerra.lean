/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.FreeEnergyConvexity

/-!
# The Ghirlanda–Guerra identities for the SK model, with an `O(N^{-1/4})` error

The general statements live in `SpinGlass.GaussFieldFluctuation`, for an arbitrary positive
semidefinite covariance matrix with constant diagonal `D` bounded by `|S σ τ| ≤ D`. The
Sherrington–Kirkpatrick model is the instance `S = skCovMatrix N 1`, `D = N/2`
(`SpinGlass.skCovMatrix_diag`, `SpinGlass.abs_skCovMatrix_le`), and every mixed `p`-spin model is
another instance by `SpinGlass.posSemidef_overlapPolyMatrix`.

Nothing here is asymptotic and no perturbation is added: the bounds hold at every finite volume.

## Main statements

- `SpinGlass.abs_skGhirlandaGuerra_error_le` — the Ghirlanda–Guerra error of the SK model at
  inverse temperature `β`, bounded by `B β N` times the fluctuation of Theorem 12.1.1.
- `SpinGlass.exists_beta_abs_skGhirlandaGuerra_error_le` — the identities hold up to an explicit
  `O(N^{-1/4})` error at some inverse temperature in every window.
-/

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology Set

namespace SpinGlass

noncomputable section

variable {N : ℕ}

/-- The disorder law of the SK Hamiltonian at inverse temperature `β`: the reference field dilated
by `β`, a centered Gaussian with covariance kernel `sk_cov_kernel N β`. -/
def skFieldAt (N : ℕ) (β : ℝ) : Measure (EnergySpace N) :=
  gaussField N ((β ^ 2) • skCovMatrix N 1)

lemma skFieldAt_eq (N : ℕ) (β : ℝ) :
    skFieldAt N β = multivariateGaussian (0 : EnergySpace N) (skCovMatrix N β) := by
  rw [skFieldAt, ← skCovMatrix_eq_smul N β, gaussField]

lemma skField_map_smul_eq_skFieldAt (N : ℕ) (β : ℝ) :
    (skField N).map (fun H : EnergySpace N => β • H) = skFieldAt N β := by
  rw [skField_eq, skFieldAt, gaussField_map_smul (S := skCovMatrix N 1)
    (posSemidef_skCovMatrix N 1) β]

/-! ### The Ghirlanda–Guerra error of the SK model -/

/-- **The Ghirlanda–Guerra error of the SK model at inverse temperature `β`.** For a test function
`f` of `m` replicas bounded by `B`, the Ghirlanda–Guerra combination built from the SK covariance
kernel is bounded by `B β N` times the mean absolute fluctuation of the energy per site — the
quantity Talagrand's Theorem 12.1.1 shows is `O(N^{-1/4})` on average over `β`. Dividing by `N`,
the kernel's own scale, makes the left-hand side the normalised combination and the bound
`B β · O(N^{-1/4})`.

Exact at every finite volume: no limit is taken and no perturbation is added. -/
theorem abs_skGhirlandaGuerra_error_le (N : ℕ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (m : ℕ) (f : FiniteGibbs.ReplicaFun (α := Config N) m) (i : Fin m) {B : ℝ}
    (hB : ∀ σs, |f σs| ≤ B) :
    |FiniteGibbs.ghirlandaGuerraCombination (skFieldAt N β) m f i|
      ≤ B * (β * (N : ℝ) * ∫ H : EnergySpace N,
          FiniteGibbs.gibbs_average (α := Config N) (H_field N 0 + β • H)
            (fun σ => |(1 / (N : ℝ)) * H σ - ∫ H' : EnergySpace N, (1 / (N : ℝ)) *
                FiniteGibbs.gibbs_average (α := Config N) (H_field N 0 + β • H') H'
                ∂(skField N)|) ∂(skField N)) := by
  rw [skFieldAt]
  exact abs_gaussGhirlandaGuerra_error_le (S := skCovMatrix N 1) (posSemidef_skCovMatrix N 1)
    (D := (N : ℝ) / 2) (skCovMatrix_diag N) hN hβ m f i hB

/-- **The Ghirlanda–Guerra identities hold for the SK model up to an explicit `O(N^{-1/4})` error,
at some inverse temperature in every window.**

The bracket on the right is `O(N^{-1/4})` at `δ = N^{-1/4}`; dividing by `N`, the scale of the
kernel, the normalised Ghirlanda–Guerra combination is `O(N^{-1/4})`. This is Talagrand's
conclusion "for the typical value of `x`". -/
theorem exists_beta_abs_skGhirlandaGuerra_error_le (N : ℕ) (hN : N ≠ 0)
    {δ a b : ℝ} (hδ : 0 < δ) (hab : a < b) (haδ : 0 ≤ a - δ)
    (m : ℕ) (f : FiniteGibbs.ReplicaFun (α := Config N) m) (i : Fin m) {B : ℝ}
    (hB : ∀ σs, |f σs| ≤ B) :
    ∃ β ∈ Set.Icc a b,
      |FiniteGibbs.ghirlandaGuerraCombination (skFieldAt N β) m f i|
        ≤ B * (β * (N : ℝ) *
            ((Real.sqrt ((b - a) * (4 * b * ((N : ℝ) / 2) / (N : ℝ) ^ 2))
              + (2 * δ * (4 * (b + δ) * ((N : ℝ) / 2) / (N : ℝ))
                + 3 * (b - a) * ((b + δ) * Real.sqrt ((N : ℝ) / 2) / (N : ℝ)) / δ))
              / (b - a))) := by
  obtain ⟨β, hβmem, hβbd⟩ := exists_beta_abs_gaussGhirlandaGuerra_error_le
    (S := skCovMatrix N 1) (posSemidef_skCovMatrix N 1) (D := (N : ℝ) / 2)
    (skCovMatrix_diag N) (abs_skCovMatrix_le N) hN hδ hab haδ m f i hB
  refine ⟨β, hβmem, ?_⟩
  rw [skFieldAt]
  exact hβbd

end

end SpinGlass
