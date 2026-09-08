/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.FiniteGibbs
import Common.Mathlib.Analysis.SpecialFunctions.LogSumExpConvex

/-!
# Convexity of the finite-volume free energy

`H ↦ log Z(H) = log ∑_σ exp(-H σ)` is a convex function of the Hamiltonian, because log-sum-exp is
convex and `H ↦ -H` is linear. Talagrand records this as equation (1.81) of Vol. I and as
equation (12.8) of Vol. II, and calls it "a fact that will turn out to be essential much later":
it is what makes Griffiths' lemma (`ConvexOn.tendsto_rightDeriv_of_tendsto`) applicable to the free
energy, and hence what turns the existence of the thermodynamic limit into convergence of its
derivatives — the mean overlap, the mean energy, and every other observable obtained by
differentiating in a parameter that enters the Hamiltonian affinely.

The statement here is the sharpest one: convexity **in the Hamiltonian itself**, on the whole
energy space. Convexity in any parameter — the inverse temperature, an external field, the strength
of a perturbation — is then the composition with an affine path, `ConvexOn.comp_affineMap`.

## Main statements

- `SpinGlass.FiniteGibbs.convexOn_log_Z`: `H ↦ log Z(H)` is convex.
- `SpinGlass.FiniteGibbs.convexOn_free_energy_density`.
- `SpinGlass.FiniteGibbs.convexOn_free_energy_density_comp_affine`: convexity along an affine path
  `t ↦ H₀ + t • V` in the Hamiltonian — the form every parameter derivative uses.
-/

open Set

namespace SpinGlass

namespace FiniteGibbs

variable {α : Type*} [Fintype α]

/-- **`log Z` is convex in the Hamiltonian.** Talagrand Vol. I, (1.81); Vol. II, (12.8). -/
theorem convexOn_log_Z :
    ConvexOn ℝ (univ : Set (EnergySpace α)) fun H => Real.log (Z (α := α) H) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hZ : ∀ H : EnergySpace α, Real.log (Z (α := α) H)
      = Real.log (∑ σ : α, Real.exp ((fun σ => -H σ) σ)) := fun H => rfl
  have hcoord : ∀ σ : α, -((a • x + b • y) σ) = a * (-x σ) + b * (-y σ) := by
    intro σ
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  change Real.log (Z (α := α) (a • x + b • y))
      ≤ a * Real.log (Z (α := α) x) + b * Real.log (Z (α := α) y)
  rw [hZ, hZ, hZ]
  have hlse := Real.log_sum_exp_le (fun σ : α => -x σ) (fun σ : α => -y σ) ha hb hab
  refine le_trans (le_of_eq ?_) hlse
  exact congrArg Real.log (Finset.sum_congr rfl fun σ _ => by
    simp only []; rw [hcoord σ])

/-- **The free energy density is convex in the Hamiltonian.** -/
theorem convexOn_free_energy_density (n : ℕ) :
    ConvexOn ℝ (univ : Set (EnergySpace α)) (free_energy_density (α := α) n) := by
  have h := convexOn_log_Z (α := α)
  have hsmul := h.smul (c := 1 / (n : ℝ)) (by positivity)
  exact hsmul

/-- **Convexity along an affine path in the Hamiltonian.** Every parameter that enters the
Hamiltonian affinely — the inverse temperature, an external field, the strength of a perturbation
— makes the free energy a convex function of that parameter. -/
theorem convexOn_free_energy_density_comp_affine (n : ℕ) (H₀ V : EnergySpace α) :
    ConvexOn ℝ (univ : Set ℝ) fun t => free_energy_density (α := α) n (H₀ + t • V) := by
  refine ⟨convex_univ, fun s _ t _ a b ha hb hab => ?_⟩
  have h1 : a • (H₀ + s • V) + b • (H₀ + t • V) = (a + b) • H₀ + (a * s + b * t) • V := by
    module
  have hpath : H₀ + (a * s + b * t) • V = a • (H₀ + s • V) + b • (H₀ + t • V) := by
    rw [h1, hab, one_smul]
  change free_energy_density (α := α) n (H₀ + (a * s + b * t) • V)
      ≤ a * free_energy_density (α := α) n (H₀ + s • V)
        + b * free_energy_density (α := α) n (H₀ + t • V)
  rw [hpath]
  exact (convexOn_free_energy_density (α := α) n).2 (mem_univ _) (mem_univ _) ha hb hab

end FiniteGibbs

end SpinGlass
