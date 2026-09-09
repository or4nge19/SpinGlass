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

* the **algebraic** input is `SpinGlass.trace_le_trace_of_kernel_le` at a pair of kernels with
  the whole-system kernel dominated by the split kernel and equal to it on the diagonal; for an
  overlap-driven kernel `N ξ(R)` this is Jensen's inequality for a convex profile
  (`SpinGlass.overlapCovKernel_le_splitCovKernel`), and the SK model is the case `ξ = β² r²/2`;
* the **analytic** input is `SpinGlass.integral_free_energy_density_le`, Guerra's comparison for an
  arbitrary independent pair of centered Gaussian Hamiltonians, here used with vanishing defect
  `C = 0`.

## Main statements

- `SpinGlass.H_field_eq_sumEnergy`: the external field has no interaction between the blocks.
- `SpinGlass.mul_free_energy_density_sumEnergy`: `N F_N = N₁ F_{N₁} + N₂ F_{N₂}` for a
  non-interacting composite Hamiltonian.
- `SpinGlass.guerraTrace_splitCovKernel_nonpos_of_le`: the Guerra trace of the split comparison
  is nonpositive for every kernel dominated by the split kernel.
- `SpinGlass.mul_integral_free_energy_density_add_le_of_kernel_le`: **Guerra–Toninelli
  superadditivity** for every dominated kernel; `mul_integral_free_energy_density_add_le` is the
  SK case and `mul_integral_free_energy_density_add_le_overlapCovKernel` the mixed `p`-spin case
  with a profile convex on `[-1,1]`.
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

/-- **The Guerra trace of a splitting interpolation is nonpositive** whenever the kernel `K` of the
whole system is dominated by the non-interacting split kernel and agrees with it on the diagonal:
the Gaussian comparison `trace_le_trace_of_kernel_le` reverses the two Hessian traces.
Talagrand Vol. I, Theorem 1.3.9. -/
theorem guerraTrace_splitCovKernel_nonpos_of_le {N₁ N₂ : ℕ}
    {K₁ : Config N₁ → Config N₁ → ℝ} {K₂ : Config N₂ → Config N₂ → ℝ}
    {K : Config (N₁ + N₂) → Config (N₁ + N₂) → ℝ}
    (hdiag : ∀ σ, K σ σ = splitCovKernel N₁ N₂ K₁ K₂ σ σ)
    (hle : ∀ σ τ, K σ τ ≤ splitCovKernel N₁ N₂ K₁ K₂ σ τ) (H : EnergySpace (N₁ + N₂)) :
    guerraTrace (N := N₁ + N₂) (splitCovKernel N₁ N₂ K₁ K₂) K H ≤ 0 := by
  have htr := trace_le_trace_of_kernel_le (N := N₁ + N₂) H (Cov₁ := K)
    (Cov₂ := splitCovKernel N₁ N₂ K₁ K₂) hdiag hle
  simp only [guerraTrace]
  linarith

/-- **The Guerra trace of the SK splitting interpolation is nonpositive.**
Talagrand Vol. I, Theorem 1.3.9. -/
theorem guerraTrace_splitCovKernel_nonpos {N₁ N₂ : ℕ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (β : ℝ)
    (H : EnergySpace (N₁ + N₂)) :
    guerraTrace (N := N₁ + N₂)
        (splitCovKernel N₁ N₂ (sk_cov_kernel N₁ β) (sk_cov_kernel N₂ β))
        (sk_cov_kernel (N₁ + N₂) β) H ≤ 0 :=
  guerraTrace_splitCovKernel_nonpos_of_le (sk_cov_kernel_diag_eq_splitCovKernel hN₁ hN₂ β)
    (sk_cov_kernel_le_splitCovKernel hN₁ hN₂ β) H

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

/-- **Guerra–Toninelli superadditivity (finite `N`), for an arbitrary dominated kernel.** Let
`G₁`, `G₂`, `G` be independent centered Gaussian Hamiltonians on the first `N₁` sites, the last
`N₂` sites and the whole system of `N₁ + N₂` sites, with symmetric kernels `K₁`, `K₂`, `K`. If `K`
is dominated by the non-interacting split kernel of `K₁`, `K₂` and agrees with it on the diagonal,
then

`N₁ 𝔼F_{N₁} + N₂ 𝔼F_{N₂} ≤ (N₁ + N₂) 𝔼F_{N₁+N₂}`.

The two subsystem free energies are the `t = 0` end of Guerra's interpolation between the
non-interacting composite Hamiltonian and the Hamiltonian of the whole system; the derivative of
the interpolation is nonpositive by `guerraTrace_splitCovKernel_nonpos_of_le`.
Talagrand Vol. I, Theorem 1.3.9; Vol. II, §12.1. -/
theorem mul_integral_free_energy_density_add_le_of_kernel_le
    {N₁ N₂ : ℕ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (h : ℝ)
    {K₁ : Config N₁ → Config N₁ → ℝ} {K₂ : Config N₂ → Config N₂ → ℝ}
    {K : Config (N₁ + N₂) → Config (N₁ + N₂) → ℝ}
    (hK₁ : ∀ σ τ, K₁ σ τ = K₁ τ σ) (hK₂ : ∀ σ τ, K₂ σ τ = K₂ τ σ) (hK : ∀ σ τ, K σ τ = K τ σ)
    (hdiag : ∀ σ, K σ σ = splitCovKernel N₁ N₂ K₁ K₂ σ σ)
    (hle : ∀ σ τ, K σ τ ≤ splitCovKernel N₁ N₂ K₁ K₂ σ τ)
    (G₁ : GaussianDisorder (Ω := Ω) N₁ (ℙ : Measure Ω) K₁)
    (G₂ : GaussianDisorder (Ω := Ω) N₂ (ℙ : Measure Ω) K₂)
    (G : GaussianDisorder (Ω := Ω) (N₁ + N₂) (ℙ : Measure Ω) K)
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
    (splitCovKernel_comm hK₁ hK₂) hK
    (C := 0) (guerraTrace_splitCovKernel_nonpos_of_le hdiag hle)
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

/-- **Guerra–Toninelli superadditivity for the SK model (finite `N`).** For independent SK
disorders on the first `N₁` sites, the last `N₂` sites, and the whole system of `N₁ + N₂` sites,

`N₁ 𝔼F_{N₁} + N₂ 𝔼F_{N₂} ≤ (N₁ + N₂) 𝔼F_{N₁+N₂}`.

The case `ξ(r) = β² r²/2` of `mul_integral_free_energy_density_add_le_of_kernel_le`.
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
          * ∫ ω, free_energy_density (N := N₁ + N₂) (G.U ω + H_field (N₁ + N₂) h) ∂ℙ :=
  mul_integral_free_energy_density_add_le_of_kernel_le hN₁ hN₂ h
    (sk_cov_kernel_comm (N := N₁) (β := β)) (sk_cov_kernel_comm (N := N₂) (β := β))
    (sk_cov_kernel_comm (N := N₁ + N₂) (β := β))
    (sk_cov_kernel_diag_eq_splitCovKernel hN₁ hN₂ β)
    (sk_cov_kernel_le_splitCovKernel hN₁ hN₂ β) G₁ G₂ G h12 hsplit

/-! ### Overlap-driven kernels with a convex profile -/

/-- An overlap-driven kernel is symmetric. -/
lemma overlapCovKernel_comm {N : ℕ} (ξ : ℝ → ℝ) (σ τ : Config N) :
    overlapCovKernel (N := N) ξ σ τ = overlapCovKernel (N := N) ξ τ σ := by
  rw [overlapCovKernel_apply, overlapCovKernel_apply, overlap_comm]

/-- **Guerra–Toninelli superadditivity for a mixed `p`-spin model (finite `N`).** For a profile
`ξ` convex on `[-1,1]` and independent centered Gaussian Hamiltonians with the overlap-driven
kernels `N ξ(R)` on the first `N₁` sites, the last `N₂` sites and the whole system,

`N₁ 𝔼F_{N₁} + N₂ 𝔼F_{N₂} ≤ (N₁ + N₂) 𝔼F_{N₁+N₂}`.

Talagrand Vol. I, Theorem 1.3.9; Vol. II, §12.1. -/
theorem mul_integral_free_energy_density_add_le_overlapCovKernel
    {N₁ N₂ : ℕ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) {ξ : ℝ → ℝ}
    (hξ : ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) ξ) (h : ℝ)
    (G₁ : GaussianDisorder (Ω := Ω) N₁ (ℙ : Measure Ω) (overlapCovKernel (N := N₁) ξ))
    (G₂ : GaussianDisorder (Ω := Ω) N₂ (ℙ : Measure Ω) (overlapCovKernel (N := N₂) ξ))
    (G : GaussianDisorder (Ω := Ω) (N₁ + N₂) (ℙ : Measure Ω)
      (overlapCovKernel (N := N₁ + N₂) ξ))
    (h12 : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U)
    (hsplit : (GaussianDisorder.split G₁ G₂ h12).U ⟂ᵢ[(ℙ : Measure Ω)] G.U) :
    (N₁ : ℝ) * (∫ ω, free_energy_density (N := N₁) (G₁.U ω + H_field N₁ h) ∂ℙ)
        + (N₂ : ℝ) * (∫ ω, free_energy_density (N := N₂) (G₂.U ω + H_field N₂ h) ∂ℙ)
      ≤ ((N₁ + N₂ : ℕ) : ℝ)
          * ∫ ω, free_energy_density (N := N₁ + N₂) (G.U ω + H_field (N₁ + N₂) h) ∂ℙ :=
  mul_integral_free_energy_density_add_le_of_kernel_le hN₁ hN₂ h
    (overlapCovKernel_comm ξ) (overlapCovKernel_comm ξ) (overlapCovKernel_comm ξ)
    (overlapCovKernel_diag_eq_splitCovKernel hN₁ hN₂ ξ)
    (overlapCovKernel_le_splitCovKernel hN₁ hN₂ hξ) G₁ G₂ G h12 hsplit

end

end SpinGlass
