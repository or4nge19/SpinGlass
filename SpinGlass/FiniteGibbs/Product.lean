/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.FiniteGibbs

/-!
# Non-interacting composite systems

Two subsystems that do not interact: the configuration space of the composite is a product of the
two configuration spaces, and the Hamiltonian is the sum of the two subsystem Hamiltonians, each
depending only on its own block of spins. Three facts:

* `FiniteGibbs.sumEnergy`: the assembly map `(H₁, H₂) ↦ (σ ↦ H₁ (e σ).1 + H₂ (e σ).2)` along a
  relabelling `e : α ≃ β × γ` is a **continuous linear map**, so it transports Gaussian laws and
  covariance operators;
* `FiniteGibbs.Z_sumEnergy`: the partition function **factorises**, `Z = Z₁ · Z₂`;
* `FiniteGibbs.log_Z_sumEnergy`: hence the (unnormalized) free energies add.

This is the `t = 0` endpoint of the Guerra–Toninelli splitting interpolation (Talagrand Vol. I,
Theorem 1.3.9): there the interpolating system at `t = 0` is the pair of independent subsystems,
and its free energy is the sum of the two subsystem free energies.
-/

open Real BigOperators

namespace SpinGlass

namespace FiniteGibbs

noncomputable section

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-! ### The assembly map -/

/-- **The Hamiltonian of a non-interacting composite system.** Given a relabelling
`e : α ≃ β × γ` of a configuration space as a pair of subsystems, `sumEnergy e` assembles a pair of
subsystem Hamiltonians into the composite Hamiltonian `σ ↦ H₁ (e σ).1 + H₂ (e σ).2`, with no
interaction term. It is linear in the pair, hence (finite dimensions) continuous linear. -/
def sumEnergy (e : α ≃ β × γ) :
    (EnergySpace β × EnergySpace γ) →L[ℝ] EnergySpace α :=
  LinearMap.toContinuousLinearMap
    { toFun := fun H => WithLp.toLp 2 fun σ : α => H.1 (e σ).1 + H.2 (e σ).2
      map_add' := by intro H K; ext σ; simp; ring
      map_smul' := by intro c H; ext σ; simp [mul_add] }

@[simp] lemma sumEnergy_apply (e : α ≃ β × γ) (H : EnergySpace β × EnergySpace γ) (σ : α) :
    (sumEnergy e H) σ = H.1 (e σ).1 + H.2 (e σ).2 := rfl

/-! ### Factorisation of the partition function -/

/-- **The partition function of a non-interacting composite factorises.** Talagrand Vol. I,
§1.3. -/
lemma Z_sumEnergy (e : α ≃ β × γ) (H₁ : EnergySpace β) (H₂ : EnergySpace γ) :
    Z (α := α) (sumEnergy e (H₁, H₂)) = Z (α := β) H₁ * Z (α := γ) H₂ := by
  classical
  have hpt : ∀ σ : α, Real.exp (-((sumEnergy e (H₁, H₂)) σ))
      = Real.exp (-(H₁ (e σ).1)) * Real.exp (-(H₂ (e σ).2)) := by
    intro σ
    rw [sumEnergy_apply, neg_add, Real.exp_add]
  calc Z (α := α) (sumEnergy e (H₁, H₂))
      = ∑ σ : α, (fun p : β × γ => Real.exp (-(H₁ p.1)) * Real.exp (-(H₂ p.2))) (e σ) := by
        simpa [Z] using Finset.sum_congr rfl fun σ _ => hpt σ
    _ = ∑ p : β × γ, Real.exp (-(H₁ p.1)) * Real.exp (-(H₂ p.2)) :=
        Fintype.sum_equiv e _ _ fun _ => rfl
    _ = Z (α := β) H₁ * Z (α := γ) H₂ := by
        rw [Fintype.sum_prod_type, Z, Z, Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by simp [← Finset.mul_sum]

/-- **The free energies of non-interacting subsystems add.** Talagrand Vol. I, §1.3. -/
lemma log_Z_sumEnergy [Nonempty β] [Nonempty γ] (e : α ≃ β × γ)
    (H₁ : EnergySpace β) (H₂ : EnergySpace γ) :
    Real.log (Z (α := α) (sumEnergy e (H₁, H₂)))
      = Real.log (Z (α := β) H₁) + Real.log (Z (α := γ) H₂) := by
  rw [Z_sumEnergy, Real.log_mul (Z_pos (α := β) H₁).ne' (Z_pos (α := γ) H₂).ne']

/-- The free-energy densities of non-interacting subsystems add, after undoing the normalisation:
`n · F_n(H₁ ⊕ H₂) = n₁ · F_{n₁}(H₁) + n₂ · F_{n₂}(H₂)`. -/
lemma mul_free_energy_density_sumEnergy [Nonempty β] [Nonempty γ] (e : α ≃ β × γ)
    {n n₁ n₂ : ℕ} (hn : n ≠ 0) (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0)
    (H₁ : EnergySpace β) (H₂ : EnergySpace γ) :
    (n : ℝ) * free_energy_density (α := α) n (sumEnergy e (H₁, H₂))
      = (n₁ : ℝ) * free_energy_density (α := β) n₁ H₁
        + (n₂ : ℝ) * free_energy_density (α := γ) n₂ H₂ := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hn₁' : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn₁
  have hn₂' : (n₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn₂
  simp only [free_energy_density, log_Z_sumEnergy e H₁ H₂]
  field_simp

end

end FiniteGibbs

end SpinGlass
