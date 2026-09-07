/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Split
import SpinGlass.GuerraInequality

/-!
# Guerra–Toninelli superadditivity

Talagrand Vol. I, Theorem 1.3.9. Comparing a system of `N₁ + N₂` sites with the pair of
independent subsystems on the first `N₁` and the last `N₂` sites, Guerra's interpolation gives

`N₁ p_{N₁} + N₂ p_{N₂} ≤ (N₁ + N₂) p_{N₁ + N₂}`,

so `N ↦ N p_N` is superadditive and Fekete's lemma produces the thermodynamic limit.

The two inputs are already available in general form:

* the **algebraic** input is `SpinGlass.trace_le_trace_of_kernel_le` at the pair of kernels
  compared in `SpinGlass.sk_cov_kernel_le_splitCovKernel` (domination) and
  `SpinGlass.sk_cov_kernel_diag_eq_splitCovKernel` (equality on the diagonal);
* the **analytic** input is `SpinGlass.integral_free_energy_density_le`, Guerra's comparison for an
  arbitrary independent pair of centered Gaussian Hamiltonians, here used with vanishing defect
  `C = 0`.

## Main statements

- `SpinGlass.H_field_eq_sumEnergy`: the external field has no interaction between the blocks.
- `SpinGlass.mul_free_energy_density_sumEnergy`: `N F_N = N₁ F_{N₁} + N₂ F_{N₂}` for a
  non-interacting composite Hamiltonian.
- `SpinGlass.guerraTrace_splitCovKernel_nonpos`: the Guerra trace of the split comparison is
  nonpositive.
- `SpinGlass.mul_integral_free_energy_density_add_le`: **Guerra–Toninelli superadditivity.**
-/

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology
open scoped ENNReal NNReal

namespace SpinGlass

noncomputable section

/-! ### The external field of a split system -/

/-- The magnetization of a split configuration is the sum of the two block magnetizations. -/
lemma magnetization_split (N₁ N₂ : ℕ) (σ : Config (N₁ + N₂)) :
    magnetization (N₁ + N₂) σ
      = magnetization N₁ (configSplit N₁ N₂ σ).1
        + magnetization N₂ (configSplit N₁ N₂ σ).2 := by
  simpa [magnetization, magnetizationOf, spinOf] using
    Fin.sum_univ_add (fun i : Fin (N₁ + N₂) => isingSpin (σ i))

/-- **The external field does not couple the two blocks**: it is the non-interacting composite of
the two block fields. -/
lemma H_field_eq_sumEnergy (N₁ N₂ : ℕ) (h : ℝ) :
    H_field (N₁ + N₂) h
      = FiniteGibbs.sumEnergy (configSplit N₁ N₂) (H_field N₁ h, H_field N₂ h) := by
  ext σ
  simp [H_field, magnetic_field_vector, magnetization_split, mul_add]

/-! ### The free energy of a non-interacting composite -/

/-- `N F_N(H₁ ⊕ H₂) = N₁ F_{N₁}(H₁) + N₂ F_{N₂}(H₂)`: the free energies of two non-interacting
subsystems add. -/
lemma mul_free_energy_density_sumEnergy {N₁ N₂ : ℕ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (H₁ : EnergySpace N₁) (H₂ : EnergySpace N₂) :
    ((N₁ + N₂ : ℕ) : ℝ) * free_energy_density (N := N₁ + N₂)
        (FiniteGibbs.sumEnergy (configSplit N₁ N₂) (H₁, H₂))
      = (N₁ : ℝ) * free_energy_density (N := N₁) H₁
        + (N₂ : ℝ) * free_energy_density (N := N₂) H₂ :=
  FiniteGibbs.mul_free_energy_density_sumEnergy (configSplit N₁ N₂)
    (Nat.add_pos_left hN₁ N₂).ne' hN₁.ne' hN₂.ne' H₁ H₂

/-! ### The Guerra trace of the split comparison -/

/-- **The Guerra trace of the splitting interpolation is nonpositive.** The SK kernel of the whole
system is dominated by the split kernel and agrees with it on the diagonal, so the Gaussian
comparison `trace_le_trace_of_kernel_le` reverses the two Hessian traces.
Talagrand Vol. I, Theorem 1.3.9. -/
theorem guerraTrace_splitCovKernel_nonpos {N₁ N₂ : ℕ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (β : ℝ)
    (H : EnergySpace (N₁ + N₂)) :
    guerraTrace (N := N₁ + N₂)
        (splitCovKernel N₁ N₂ (sk_cov_kernel N₁ β) (sk_cov_kernel N₂ β))
        (sk_cov_kernel (N₁ + N₂) β) H ≤ 0 := by
  have htr := trace_le_trace_of_kernel_le (N := N₁ + N₂) H
    (Cov₁ := sk_cov_kernel (N₁ + N₂) β)
    (Cov₂ := splitCovKernel N₁ N₂ (sk_cov_kernel N₁ β) (sk_cov_kernel N₂ β))
    (sk_cov_kernel_diag_eq_splitCovKernel hN₁ hN₂ β)
    (fun σ τ => sk_cov_kernel_le_splitCovKernel hN₁ hN₂ β σ τ)
  simp only [guerraTrace]
  linarith

/-! ### Integrability of the free energy under a Gaussian disorder -/

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The free-energy density of a Gaussian Hamiltonian shifted by a deterministic field is
integrable. -/
lemma GaussianDisorder.integrable_free_energy_density_add
    {N : ℕ} {K : Config N → Config N → ℝ}
    (G : GaussianDisorder (Ω := Ω) N (ℙ : Measure Ω) K) (c : EnergySpace N) :
    Integrable (fun ω => free_energy_density (N := N) (G.U ω + c)) (ℙ : Measure Ω) := by
  have hg : Measurable (fun ω => G.U ω + c) := G.measU.add_const c
  have hmap : (ℙ : Measure Ω).map (fun ω => G.U ω + c)
      = ((ℙ : Measure Ω).map G.U).map (fun x => x + c) := by
    rw [Measure.map_map (by fun_prop) G.measU]; rfl
  have hgauss : ProbabilityTheory.IsGaussian ((ℙ : Measure Ω).map G.U) := G.isGaussian
  exact integrable_free_energy_density_of_isGaussian (N := N) (ℙ : Measure Ω) hg
    (by rw [hmap]; infer_instance)

/-! ### Superadditivity -/

/-- **Guerra–Toninelli superadditivity (finite `N`).** For independent SK disorders on the first
`N₁` sites, the last `N₂` sites, and the whole system of `N₁ + N₂` sites,

`N₁ 𝔼F_{N₁} + N₂ 𝔼F_{N₂} ≤ (N₁ + N₂) 𝔼F_{N₁+N₂}`.

The two subsystem free energies are the `t = 0` end of Guerra's interpolation between the
non-interacting composite Hamiltonian and the SK Hamiltonian of the whole system; the derivative of
the interpolation is nonpositive by `guerraTrace_splitCovKernel_nonpos`.
Talagrand Vol. I, Theorem 1.3.9. -/
theorem mul_integral_free_energy_density_add_le
    {N₁ N₂ : ℕ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) {β : ℝ} (h : ℝ)
    (G₁ : SKDisorder (Ω := Ω) N₁ β) (G₂ : SKDisorder (Ω := Ω) N₂ β)
    (G : SKDisorder (Ω := Ω) (N₁ + N₂) β)
    (h12 : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U)
    (hsplit : (GaussianDisorder.split G₁ G₂ h12).U ⟂ᵢ[(ℙ : Measure Ω)] G.U) :
    (N₁ : ℝ) * (∫ ω, free_energy_density (N := N₁) (G₁.U ω + H_field N₁ h) ∂ℙ)
        + (N₂ : ℝ) * (∫ ω, free_energy_density (N := N₂) (G₂.U ω + H_field N₂ h) ∂ℙ)
      ≤ ((N₁ + N₂ : ℕ) : ℝ)
          * ∫ ω, free_energy_density (N := N₁ + N₂) (G.U ω + H_field (N₁ + N₂) h) ∂ℙ := by
  classical
  have hM : 0 < N₁ + N₂ := Nat.add_pos_left hN₁ N₂
  have hMR : (0 : ℝ) < ((N₁ + N₂ : ℕ) : ℝ) := by exact_mod_cast hM
  -- Guerra's comparison, with vanishing defect.
  have hcmp := integral_free_energy_density_le (Ω := Ω) (N := N₁ + N₂) (h := h)
    (G₁ := GaussianDisorder.split G₁ G₂ h12) (G₂ := G) hsplit
    (splitCovKernel_comm (sk_cov_kernel_comm (N := N₁) (β := β))
      (sk_cov_kernel_comm (N := N₂) (β := β)))
    (sk_cov_kernel_comm (N := N₁ + N₂) (β := β))
    (C := 0) (guerraTrace_splitCovKernel_nonpos hN₁ hN₂ β)
  -- The composite Hamiltonian plus the field is the composite of the two shifted Hamiltonians.
  have hpt : ∀ ω : Ω,
      free_energy_density (N := N₁ + N₂)
          ((GaussianDisorder.split G₁ G₂ h12).U ω + H_field (N₁ + N₂) h)
        = (1 / ((N₁ + N₂ : ℕ) : ℝ)) *
            ((N₁ : ℝ) * free_energy_density (N := N₁) (G₁.U ω + H_field N₁ h)
              + (N₂ : ℝ) * free_energy_density (N := N₂) (G₂.U ω + H_field N₂ h)) := by
    intro ω
    have hsum : (GaussianDisorder.split G₁ G₂ h12).U ω + H_field (N₁ + N₂) h
        = FiniteGibbs.sumEnergy (configSplit N₁ N₂)
            (G₁.U ω + H_field N₁ h, G₂.U ω + H_field N₂ h) := by
      rw [GaussianDisorder.split_U, GaussianDisorder.splitU, H_field_eq_sumEnergy,
        ← map_add]
      rfl
    rw [hsum, ← mul_free_energy_density_sumEnergy hN₁ hN₂]
    field_simp
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)] at hcmp
  have hI₁ := GaussianDisorder.integrable_free_energy_density_add G₁ (H_field N₁ h)
  have hI₂ := GaussianDisorder.integrable_free_energy_density_add G₂ (H_field N₂ h)
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add (hI₁.const_mul _) (hI₂.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, add_zero] at hcmp
  have hmul := mul_le_mul_of_nonneg_left hcmp hMR.le
  rw [← mul_assoc, mul_one_div, div_self hMR.ne', one_mul] at hmul
  exact hmul

end

end SpinGlass
