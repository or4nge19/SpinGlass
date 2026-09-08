/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.MixedPSpin
import SpinGlass.SKDisorderExists

/-!
# A single `p`-spin term as a component of the disorder

A mixed `p`-spin Hamiltonian splits as `H = H_A + H_B` with `H_A`, `H_B` independent centered
Gaussians of covariances `N(ξ - aₚrᵖ)(R)` and `aₚ N Rᵖ`. Along the affine interpolation
`t ↦ H_A + t H_B` — again a mixed `p`-spin model, passing through the model at `t = 1` — the
`p`-spin term is a *component* of the disorder in the sense of
`SpinGlass.FiniteGibbs.crossKernel`, with cross kernel `t aₚ N Rᵖ`: symmetric, constant diagonal
`t aₚ N`, and dominated by it.

This file assembles that instance and reads off **Talagrand, Vol. II, Lemma 12.1.4 for the
`p`-spin component**: the mean `p`-spin energy per site is bounded by `2 t aₚ`, uniformly in the
volume. That is the input the second half of Theorem 12.1.1 consumes.

## Main statements

- `SpinGlass.pairAffine`: the interpolation map `(x, y) ↦ x + t y`, as a continuous linear map.
- `SpinGlass.crossKernel_pairAffine_std_basis_right`: the cross kernel of the second block is
  `t K₂`.
- `SpinGlass.abs_integral_gibbs_average_component_le`: **Lemma 12.1.4 for a component.**
-/

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology Set
open scoped InnerProductSpace ENNReal

namespace SpinGlass

noncomputable section

variable {N : ℕ}

/-! ### The affine interpolation map on the disorder pair space -/

/-- **The affine interpolation map `(x, y) ↦ x + t y`** on the `L²`-product of two copies of the
energy space, as a continuous linear map. Unlike `ProbabilityTheory.gaussianInterp` this path is
*affine in the Hamiltonian*, so the free energy is convex along it — which is what Griffiths'
lemma and the second half of Theorem 12.1.1 require. -/
def pairAffine (N : ℕ) (t : ℝ) : DisorderSpace (N := N) →L[ℝ] EnergySpace N :=
  (WithLp.fstL (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (α := EnergySpace N) (β := EnergySpace N))
    + t • (WithLp.sndL (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (α := EnergySpace N) (β := EnergySpace N))

@[simp] lemma pairAffine_apply (N : ℕ) (t : ℝ) (p : DisorderSpace (N := N)) :
    pairAffine N t p = (WithLp.ofLp p).1 + t • (WithLp.ofLp p).2 := by
  simp [pairAffine]

@[simp] lemma pairAffine_std_basis_right (N : ℕ) (t : ℝ) (τ : Config N) :
    pairAffine N t (std_basis_right (N := N) τ) = t • std_basis N τ := by
  simp [pairAffine_apply, std_basis_right]

@[simp] lemma pairAffine_std_basis_left (N : ℕ) (t : ℝ) (τ : Config N) :
    pairAffine N t (std_basis_left (N := N) τ) = std_basis N τ := by
  simp [pairAffine_apply, std_basis_left]

/-- **The adjoint directions of `pairAffine`**: the disorder direction representing the `σ`-th
coordinate of the interpolated Hamiltonian, `Aᵀ e_σ = e_σ^{left} + t e_σ^{right}`. -/
def pairDir (N : ℕ) (t : ℝ) (σ : Config N) : DisorderSpace (N := N) :=
  std_basis_left (N := N) σ + t • std_basis_right (N := N) σ

lemma inner_pairDir (N : ℕ) (t : ℝ) (p : DisorderSpace (N := N)) (σ : Config N) :
    ⟪p, pairDir N t σ⟫_ℝ = (pairAffine N t p) σ := by
  rw [pairDir, inner_add_right, real_inner_smul_right,
    inner_apply_std_basis_left (N := N) σ p, inner_apply_std_basis_right (N := N) σ p,
    pairAffine_apply]
  simp

/-- The Dirac vectors of the second block are unit vectors. -/
@[simp] lemma norm_std_basis_right (N : ℕ) (σ : Config N) :
    ‖std_basis_right (N := N) σ‖ = 1 := by
  have h : ‖std_basis_right (N := N) σ‖ ^ 2 = 1 := by
    have := real_inner_self_eq_norm_sq (std_basis_right (N := N) σ)
    rw [← this, inner_apply_std_basis_right (N := N) σ (std_basis_right (N := N) σ)]
    simp [std_basis_right, std_basis]
  have h0 : (0 : ℝ) ≤ ‖std_basis_right (N := N) σ‖ := norm_nonneg _
  nlinarith [h, h0]

section Pair

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {K₁ K₂ : Config N → Config N → ℝ}
variable (G₁ : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K₁)
variable (G₂ : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K₂)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- **The cross kernel of the second block against the interpolated Hamiltonian is `t K₂`.**
This is `Cov(H_B(σ), (H_A + t H_B)(τ)) = t K₂(σ, τ)` — the covariance of the second summand alone,
scaled by the coupling. -/
theorem crossKernel_pairAffine_std_basis_right
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) (t : ℝ) (σ τ : Config N) :
    FiniteGibbs.crossKernel (disorderPairLaw (Ω := Ω) (N := N) G₁ G₂) (pairAffine N t)
        (std_basis_right (N := N)) σ τ
      = t * K₂ σ τ := by
  classical
  rw [FiniteGibbs.crossKernel_apply,
    covarianceOperator_disorderPairLaw_std_basis_right_eq_sum (Ω := Ω) (N := N) G₁ G₂ hindep σ,
    map_sum]
  have hterm : ∀ ρ : Config N,
      pairAffine N t ((K₂ σ ρ) • std_basis_right (N := N) ρ)
        = (t * K₂ σ ρ) • std_basis N ρ := by
    intro ρ
    rw [map_smul, pairAffine_std_basis_right, smul_smul]
    ring_nf
  rw [Finset.sum_congr rfl fun ρ _ => hterm ρ]
  have hsum : ((∑ ρ : Config N, (t * K₂ σ ρ) • std_basis N ρ : EnergySpace N)) τ
      = t * K₂ σ τ := by
    classical
    rw [show ((∑ ρ : Config N, (t * K₂ σ ρ) • std_basis N ρ : EnergySpace N)) τ
        = ∑ ρ : Config N, (t * K₂ σ ρ) * (std_basis N ρ) τ from by
      simp [WithLp.ofLp_sum]]
    rw [Finset.sum_eq_single_of_mem τ (Finset.mem_univ τ)]
    · simp [std_basis]
    · intro ρ _ hρ
      rw [show (std_basis N ρ) τ = 0 from
        FiniteGibbs.std_basis_apply_of_ne (α := Config N) hρ]
      ring
  exact hsum

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- **The cross kernel of the interpolated Hamiltonian against itself is `K₁ + t² K₂`.** -/
theorem crossKernel_pairAffine_pairDir
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) (t : ℝ) (σ τ : Config N) :
    FiniteGibbs.crossKernel (disorderPairLaw (Ω := Ω) (N := N) G₁ G₂) (pairAffine N t)
        (pairDir N t) σ τ
      = K₁ σ τ + t ^ 2 * K₂ σ τ := by
  classical
  rw [FiniteGibbs.crossKernel_apply, pairDir, map_add, map_smul,
    covarianceOperator_disorderPairLaw_std_basis_left_eq_sum (Ω := Ω) (N := N) G₁ G₂ hindep σ,
    covarianceOperator_disorderPairLaw_std_basis_right_eq_sum (Ω := Ω) (N := N) G₁ G₂ hindep σ]
  rw [map_add, map_smul, map_sum, map_sum]
  have hL : ∀ ρ : Config N,
      pairAffine N t ((K₁ σ ρ) • std_basis_left (N := N) ρ) = (K₁ σ ρ) • std_basis N ρ := by
    intro ρ; rw [map_smul, pairAffine_std_basis_left]
  have hR : ∀ ρ : Config N,
      pairAffine N t ((K₂ σ ρ) • std_basis_right (N := N) ρ)
        = (t * K₂ σ ρ) • std_basis N ρ := by
    intro ρ; rw [map_smul, pairAffine_std_basis_right, smul_smul]; ring_nf
  rw [Finset.sum_congr rfl fun ρ _ => hL ρ, Finset.sum_congr rfl fun ρ _ => hR ρ]
  have hsum : ∀ (v : Config N → ℝ),
      ((∑ ρ : Config N, (v ρ) • std_basis N ρ : EnergySpace N)) τ = v τ := by
    intro v
    rw [show ((∑ ρ : Config N, (v ρ) • std_basis N ρ : EnergySpace N)) τ
        = ∑ ρ : Config N, (v ρ) * (std_basis N ρ) τ from by simp [WithLp.ofLp_sum]]
    rw [Finset.sum_eq_single_of_mem τ (Finset.mem_univ τ)]
    · simp [std_basis]
    · intro ρ _ hρ
      rw [show (std_basis N ρ) τ = 0 from
        FiniteGibbs.std_basis_apply_of_ne (α := Config N) hρ]
      ring
  have hadd : ((∑ ρ : Config N, (K₁ σ ρ) • std_basis N ρ : EnergySpace N)
        + t • (∑ ρ : Config N, (t * K₂ σ ρ) • std_basis N ρ : EnergySpace N)) τ
      = K₁ σ τ + t ^ 2 * K₂ σ τ := by
    have h1 := hsum (fun ρ => K₁ σ ρ)
    have h2 := hsum (fun ρ => t * K₂ σ ρ)
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      h1, h2]
    ring
  exact hadd

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- **The interpolated Hamiltonian is a mixed model with covariance kernel `K₁ + t² K₂`.**

The law of `H_A + t H_B` on the energy space has covariance kernel `K₁ + t² K₂` — read off directly
from the covariance operator, with no identification of the law itself. For a mixed `p`-spin model
with `K₁ = N(ξ - aₚrᵖ)(R)` and `K₂ = aₚ N Rᵖ` this is `N(ξ - (1-t²)aₚrᵖ)(R)`: again overlap-driven
with nonnegative coefficients for every real `t`, hence with constant diagonal and dominated by
it. -/
theorem covarianceOperator_map_pairAffine_std_basis
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) (t : ℝ) (σ τ : Config N) :
    (ProbabilityTheory.covarianceOperator
        ((disorderPairLaw (Ω := Ω) (N := N) G₁ G₂).map (pairAffine N t))
        (std_basis N σ)) τ
      = K₁ σ τ + t ^ 2 * K₂ σ τ := by
  have hgauss : ProbabilityTheory.IsGaussian
      (disorderPairLaw (Ω := Ω) (N := N) G₁ G₂) :=
    isGaussian_disorderPairLaw_of_indep (Ω := Ω) (N := N) G₁ G₂ hindep
  rw [std_basis, FiniteGibbs.covarianceOperator_map_std_basis_eq_crossKernel
      (P := disorderPairLaw (Ω := Ω) (N := N) G₁ G₂) (pairAffine N t)
      (w := pairDir N t) (fun p σ => inner_pairDir N t p σ) σ τ,
    crossKernel_pairAffine_pairDir (Ω := Ω) (N := N) G₁ G₂ hindep t σ τ]

/-! ### Concentration of the free energy along the interpolation -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The interpolated Hamiltonian is centered. -/
theorem integral_id_map_pairAffine
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) (t : ℝ) :
    (∫ K : EnergySpace N,
        K ∂((disorderPairLaw (Ω := Ω) (N := N) G₁ G₂).map (pairAffine N t))) = 0 := by
  have hgauss : ProbabilityTheory.IsGaussian
      (disorderPairLaw (Ω := Ω) (N := N) G₁ G₂) :=
    isGaussian_disorderPairLaw_of_indep (Ω := Ω) (N := N) G₁ G₂ hindep
  have hint : Integrable (id : DisorderSpace (N := N) → DisorderSpace (N := N))
      (disorderPairLaw (Ω := Ω) (N := N) G₁ G₂) :=
    ProbabilityTheory.IsGaussian.integrable_id
  rw [MeasureTheory.integral_map (μ := disorderPairLaw (Ω := Ω) (N := N) G₁ G₂)
      (φ := pairAffine N t) (f := fun K : EnergySpace N => K)
      (pairAffine N t).continuous.measurable.aemeasurable
      (measurable_id.aestronglyMeasurable)]
  have h := ContinuousLinearMap.integral_comp_comm (pairAffine N t)
    (φ := (id : DisorderSpace (N := N) → DisorderSpace (N := N))) hint
  simpa [disorderPairLaw_mean0 (Ω := Ω) (N := N) G₁ G₂] using h

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- **The free energy concentrates along the interpolation.** The mean absolute deviation of the
free energy of `H_A + t H_B` from its disorder average is at most `√(M₁ + t² M₂)/N`, where `M₁` and
`M₂` bound the two kernels. For a mixed `p`-spin model `M₁ + t² M₂ = N(ξ(1) - (1-t²)aₚ)`, so the
bound is `√((ξ(1) - (1-t²)aₚ)/N)` — the `O(N^{-1/2})` free-energy concentration, uniformly along
the path. -/
theorem integral_abs_free_energy_density_pairAffine_sub_mean_le
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) (t : ℝ) (c₀ : EnergySpace N)
    {M₁ M₂ : ℝ} (hk₁ : ∀ σ τ : Config N, |K₁ σ τ| ≤ M₁)
    (hk₂ : ∀ σ τ : Config N, |K₂ σ τ| ≤ M₂) :
    (∫ p : DisorderSpace (N := N),
        |free_energy_density (N := N) (pairAffine N t p + c₀)
          - ∫ p' : DisorderSpace (N := N),
              free_energy_density (N := N) (pairAffine N t p' + c₀)
              ∂(disorderPairLaw (Ω := Ω) (N := N) G₁ G₂)|
        ∂(disorderPairLaw (Ω := Ω) (N := N) G₁ G₂))
      ≤ Real.sqrt (M₁ + t ^ 2 * M₂) / (N : ℝ) := by
  classical
  set P : Measure (DisorderSpace (N := N)) := disorderPairLaw (Ω := Ω) (N := N) G₁ G₂ with hP
  set μ : Measure (EnergySpace N) := P.map (pairAffine N t) with hμ
  have hgauss : ProbabilityTheory.IsGaussian P :=
    isGaussian_disorderPairLaw_of_indep (Ω := Ω) (N := N) G₁ G₂ hindep
  have hgμ : ProbabilityTheory.IsGaussian μ := by
    rw [hμ]; exact ProbabilityTheory.isGaussian_map (μ := P) (pairAffine N t)
  have hmean0 : (∫ K : EnergySpace N, K ∂μ) = 0 := by
    rw [hμ, hP]; exact integral_id_map_pairAffine (Ω := Ω) (N := N) G₁ G₂ hindep t
  -- the variance bound from Gaussian Poincaré, with the interpolated kernel
  have hker : ∀ σ τ : Config N,
      |(ProbabilityTheory.covarianceOperator μ (FiniteGibbs.std_basis (α := Config N) σ)) τ|
        ≤ M₁ + t ^ 2 * M₂ := by
    intro σ τ
    have hE : (ProbabilityTheory.covarianceOperator μ
        (FiniteGibbs.std_basis (α := Config N) σ)) τ = K₁ σ τ + t ^ 2 * K₂ σ τ := by
      rw [hμ, hP, show FiniteGibbs.std_basis (α := Config N) σ = std_basis N σ from rfl]
      exact covarianceOperator_map_pairAffine_std_basis (Ω := Ω) (N := N) G₁ G₂ hindep t σ τ
    rw [hE, abs_le]
    have h1 := abs_le.1 (hk₁ σ τ)
    have h2 := abs_le.1 (hk₂ σ τ)
    have ht : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, ht]
  have hM0 : (0 : ℝ) ≤ M₁ + t ^ 2 * M₂ :=
    le_trans (abs_nonneg _) (hker (Classical.arbitrary (Config N)) (Classical.arbitrary _))
  have hvarμ : Var[(fun H : EnergySpace N => free_energy_density (N := N) (H + c₀)); μ]
      ≤ (1 / (N : ℝ)) ^ 2 * (M₁ + t ^ 2 * M₂) := by
    refine le_trans (FiniteGibbs.variance_free_energy_density_add_const_le_gibbs_covariance
      (α := Config N) (μ := μ) hmean0 N c₀) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hpt : ∀ H : EnergySpace N,
        (∑ σ : Config N, ∑ τ : Config N,
            FiniteGibbs.gibbs_pmf (α := Config N) (H + c₀) σ
              * FiniteGibbs.gibbs_pmf (α := Config N) (H + c₀) τ
              * (ProbabilityTheory.covarianceOperator μ
                  (FiniteGibbs.std_basis (α := Config N) σ)) τ)
          ≤ M₁ + t ^ 2 * M₂ := by
      intro H
      have h := abs_gibbs_average₂_le (N := N) (H + c₀)
        (f := fun σ τ => (ProbabilityTheory.covarianceOperator μ
          (FiniteGibbs.std_basis (α := Config N) σ)) τ) hker
      have heq : gibbs_average₂ (N := N) (H + c₀)
          (fun σ τ => (ProbabilityTheory.covarianceOperator μ
            (FiniteGibbs.std_basis (α := Config N) σ)) τ)
          = ∑ σ : Config N, ∑ τ : Config N,
              FiniteGibbs.gibbs_pmf (α := Config N) (H + c₀) σ
                * FiniteGibbs.gibbs_pmf (α := Config N) (H + c₀) τ
                * (ProbabilityTheory.covarianceOperator μ
                    (FiniteGibbs.std_basis (α := Config N) σ)) τ := rfl
      rw [heq] at h
      exact (abs_le.1 h).2
    have hIle := MeasureTheory.norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun H : EnergySpace N => ∑ σ : Config N, ∑ τ : Config N,
        FiniteGibbs.gibbs_pmf (α := Config N) (H + c₀) σ
          * FiniteGibbs.gibbs_pmf (α := Config N) (H + c₀) τ
          * (ProbabilityTheory.covarianceOperator μ
              (FiniteGibbs.std_basis (α := Config N) σ)) τ)
      (C := M₁ + t ^ 2 * M₂) (Filter.Eventually.of_forall fun H => by
        have h : |gibbs_average₂ (N := N) (H + c₀)
            (fun σ τ => (ProbabilityTheory.covarianceOperator μ
              (FiniteGibbs.std_basis (α := Config N) σ)) τ)| ≤ M₁ + t ^ 2 * M₂ :=
          abs_gibbs_average₂_le (N := N) (H + c₀) hker
        rw [Real.norm_eq_abs]
        exact h)
    have := (le_abs_self (∫ H : EnergySpace N, ∑ σ : Config N, ∑ τ : Config N,
        FiniteGibbs.gibbs_pmf (α := Config N) (H + c₀) σ
          * FiniteGibbs.gibbs_pmf (α := Config N) (H + c₀) τ
          * (ProbabilityTheory.covarianceOperator μ
              (FiniteGibbs.std_basis (α := Config N) σ)) τ ∂μ))
    have hnorm : |∫ H : EnergySpace N, ∑ σ : Config N, ∑ τ : Config N,
        FiniteGibbs.gibbs_pmf (α := Config N) (H + c₀) σ
          * FiniteGibbs.gibbs_pmf (α := Config N) (H + c₀) τ
          * (ProbabilityTheory.covarianceOperator μ
              (FiniteGibbs.std_basis (α := Config N) σ)) τ ∂μ| ≤ M₁ + t ^ 2 * M₂ := by
      simpa [Real.norm_eq_abs, measure_univ] using hIle
    linarith [(abs_le.1 hnorm).2]
  -- transport the variance to `P`
  have hXcont : Continuous fun p : DisorderSpace (N := N) =>
      free_energy_density (N := N) (pairAffine N t p + c₀) :=
    (contDiff_free_energy_density (N := N)).continuous.comp
      ((pairAffine N t).continuous.add continuous_const)
  have hvarP : Var[(fun p : DisorderSpace (N := N) =>
      free_energy_density (N := N) (pairAffine N t p + c₀)); P]
      ≤ (1 / (N : ℝ)) ^ 2 * (M₁ + t ^ 2 * M₂) := by
    have hmap := ProbabilityTheory.variance_map (μ := P)
      (X := fun H : EnergySpace N => free_energy_density (N := N) (H + c₀))
      (Y := fun p : DisorderSpace (N := N) => pairAffine N t p)
      (by
        have : ProbabilityTheory.IsGaussian μ := hgμ
        exact ((contDiff_free_energy_density (N := N)).continuous.comp
          (continuous_id.add continuous_const)).measurable.aemeasurable)
      (pairAffine N t).continuous.measurable.aemeasurable
    rw [← hμ] at hmap
    simpa [Function.comp_def] using hmap.symm.trans_le hvarμ
  -- Cauchy–Schwarz: mean absolute deviation ≤ √variance
  set X : DisorderSpace (N := N) → ℝ := fun p =>
    free_energy_density (N := N) (pairAffine N t p + c₀) with hX
  have hXmem : MemLp X 2 P := by
    have h : MemLp (fun H : EnergySpace N => free_energy_density (N := N) (c₀ + (1 : ℝ) • H))
        2 μ := FiniteGibbs.memLp_free_energy_density_affine (α := Config N) (μ := μ) N c₀ 1
    have hfun : (fun H : EnergySpace N => free_energy_density (N := N) (c₀ + (1 : ℝ) • H))
        = fun H : EnergySpace N => free_energy_density (N := N) (H + c₀) := by
      funext H; rw [one_smul, add_comm]
    rw [hfun] at h
    have h' : MemLp (fun H : EnergySpace N => free_energy_density (N := N) (H + c₀)) 2 μ := h
    rw [hμ] at h'
    have h2 := h'.comp_of_map (pairAffine N t).continuous.measurable.aemeasurable
    simpa [hX, Function.comp_def] using h2
  set m : ℝ := ∫ p : DisorderSpace (N := N), X p ∂P with hm
  have hDmem : MemLp (fun p => X p - m) 2 P := hXmem.sub (memLp_const m)
  have hCS := MeasureTheory.integral_abs_le_sqrt_measureReal_univ_mul_integral_sq
    (μ := P) hDmem
  have huniv : P.real Set.univ = 1 := by simp [MeasureTheory.measureReal_def]
  rw [huniv, one_mul] at hCS
  have hvar : (∫ p : DisorderSpace (N := N), (X p - m) ^ 2 ∂P) = Var[X; P] :=
    (ProbabilityTheory.variance_eq_integral hXmem.1.aemeasurable).symm
  rw [hvar] at hCS
  refine hCS.trans ?_
  have hsq : Real.sqrt ((1 / (N : ℝ)) ^ 2 * (M₁ + t ^ 2 * M₂))
      = Real.sqrt (M₁ + t ^ 2 * M₂) / (N : ℝ) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity : (0:ℝ) ≤ 1 / (N : ℝ))]
    ring
  rw [← hsq]
  exact Real.sqrt_le_sqrt hvarP

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- **Talagrand, Vol. II, Lemma 12.1.4, for a component of the disorder.**

Along the affine interpolation `H_A + t H_B`, the disorder-averaged Gibbs mean of the *second*
Hamiltonian is bounded by twice the size of its own covariance kernel, scaled by `t`:

`|𝔼⟨H_B⟩| ≤ 2 |t| M₂` whenever `|K₂ σ τ| ≤ M₂`.

For a mixed `p`-spin model `K₂ = aₚ N Rᵖ`, so `M₂ = aₚ N` and the bound on the mean *energy per
site* is `2|t| aₚ` — a constant, uniform in the volume. This is the bound the second half of
Theorem 12.1.1 consumes. -/
theorem abs_integral_gibbs_average_component_le
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) (t : ℝ) (c₀ : EnergySpace N)
    {d M₂ : ℝ} (hdiag : ∀ σ : Config N, t * K₂ σ σ = d)
    (hker : ∀ σ τ : Config N, |K₂ σ τ| ≤ M₂) :
    |∫ p : DisorderSpace (N := N),
        FiniteGibbs.gibbs_average (α := Config N) (pairAffine N t p + c₀)
          ((WithLp.ofLp p).2) ∂(disorderPairLaw (Ω := Ω) (N := N) G₁ G₂)|
      ≤ 2 * (|t| * M₂) := by
  classical
  have hgauss : ProbabilityTheory.IsGaussian
      (disorderPairLaw (Ω := Ω) (N := N) G₁ G₂) :=
    isGaussian_disorderPairLaw_of_indep (Ω := Ω) (N := N) G₁ G₂ hindep
  have hmean0 : (∫ p : DisorderSpace (N := N), p
      ∂(disorderPairLaw (Ω := Ω) (N := N) G₁ G₂)) = 0 :=
    disorderPairLaw_mean0 (Ω := Ω) (N := N) G₁ G₂
  have hcross := crossKernel_pairAffine_std_basis_right (Ω := Ω) (N := N) G₁ G₂ hindep t
  have hdiag' : ∀ σ : Config N,
      FiniteGibbs.crossKernel (disorderPairLaw (Ω := Ω) (N := N) G₁ G₂) (pairAffine N t)
        (std_basis_right (N := N)) σ σ = d := fun σ => by
    rw [hcross σ σ]; exact hdiag σ
  have hker' : ∀ σ τ : Config N,
      |FiniteGibbs.crossKernel (disorderPairLaw (Ω := Ω) (N := N) G₁ G₂) (pairAffine N t)
        (std_basis_right (N := N)) σ τ| ≤ |t| * M₂ := fun σ τ => by
    rw [hcross σ τ, abs_mul]
    exact mul_le_mul_of_nonneg_left (hker σ τ) (abs_nonneg t)
  have hbase := FiniteGibbs.abs_integral_gibbs_average_one_inner_comp_le
    (P := disorderPairLaw (Ω := Ω) (N := N) G₁ G₂) hmean0 (pairAffine N t) c₀
    (w := std_basis_right (N := N)) (Mw := 1)
    (fun σ => le_of_eq (norm_std_basis_right N σ)) hdiag' hker'
  have hbridge : ∀ p : DisorderSpace (N := N),
      FiniteGibbs.gibbs_average_n_det (α := Config N) (n := 1) (pairAffine N t p + c₀)
          (fun τs => ⟪p, std_basis_right (N := N) (τs 0)⟫_ℝ)
        = FiniteGibbs.gibbs_average (α := Config N) (pairAffine N t p + c₀)
            ((WithLp.ofLp p).2) := by
    intro p
    rw [FiniteGibbs.gibbs_average_one, FiniteGibbs.gibbs_average]
    exact Finset.sum_congr rfl fun τ _ => by
      rw [inner_apply_std_basis_right (N := N) τ p]; ring
  rwa [integral_congr_ae (Filter.Eventually.of_forall hbridge)] at hbase

/-! ### Theorem 12.1.1 for a component of the disorder -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The coordinate projections of the disorder pair, along the interpolation. -/
lemma pairU_add_smul (c₀ : EnergySpace N) (x : ℝ) (p : DisorderSpace (N := N)) :
    ((WithLp.ofLp p).1 + c₀) + x • (WithLp.ofLp p).2 = pairAffine N x p + c₀ := by
  rw [pairAffine_apply]; abel

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma measurable_pair_fst (c₀ : EnergySpace N) :
    Measurable fun p : DisorderSpace (N := N) => (WithLp.ofLp p).1 + c₀ := by
  fun_prop

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma measurable_pair_snd :
    Measurable fun p : DisorderSpace (N := N) => (WithLp.ofLp p).2 := by
  fun_prop

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The second block of the disorder pair has integrable norm. -/
lemma integrable_norm_pair_snd (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) :
    Integrable (fun p : DisorderSpace (N := N) => ‖(WithLp.ofLp p).2‖)
      (disorderPairLaw (Ω := Ω) (N := N) G₁ G₂) := by
  have hgauss : ProbabilityTheory.IsGaussian (disorderPairLaw (Ω := Ω) (N := N) G₁ G₂) :=
    isGaussian_disorderPairLaw_of_indep (Ω := Ω) (N := N) G₁ G₂ hindep
  have hdom := ProbabilityTheory.IsGaussian.integrable_one_add_norm_pow
    (μ := disorderPairLaw (Ω := Ω) (N := N) G₁ G₂) 2
  have hcS0 : (0 : ℝ) ≤ ‖WithLp.sndL (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
      (α := EnergySpace N) (β := EnergySpace N)‖ := norm_nonneg _
  refine Integrable.mono' (hdom.const_mul ‖WithLp.sndL (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
      (α := EnergySpace N) (β := EnergySpace N)‖)
    ((measurable_pair_snd (N := N)).norm.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun p => ?_)
  have h := (WithLp.sndL (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
    (α := EnergySpace N) (β := EnergySpace N)).le_opNorm p
  have h0 : (0 : ℝ) ≤ ‖p‖ := norm_nonneg p
  have hkey : ‖p‖ ≤ (1 + ‖p‖) ^ 2 := by nlinarith [h0, sq_nonneg ‖p‖]
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg ((WithLp.ofLp p).2))]
  calc ‖(WithLp.ofLp p).2‖ ≤ ‖WithLp.sndL (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
          (α := EnergySpace N) (β := EnergySpace N)‖ * ‖p‖ := h
    _ ≤ ‖WithLp.sndL (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
          (α := EnergySpace N) (β := EnergySpace N)‖ * (1 + ‖p‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hkey hcS0

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- **The fluctuation integrand on the pair space, pulled back to the sample space.** Every
`disorderPairLaw`-integral of the total-fluctuation integrand is the corresponding `ℙ`-integral
along `(G₁.U, G₂.U)`. -/
theorem integral_disorderPairLaw_totalFluct (c₀ : EnergySpace N) (y : ℝ) :
    (∫ p : DisorderSpace (N := N),
        FiniteGibbs.gibbs_average (α := Config N)
          (((WithLp.ofLp p).1 + c₀) + y • (WithLp.ofLp p).2)
          (fun σ => |(1 / (N : ℝ)) * ((WithLp.ofLp p).2) σ
            - ∫ p' : DisorderSpace (N := N), (1 / (N : ℝ)) *
                FiniteGibbs.gibbs_average (α := Config N)
                  (((WithLp.ofLp p').1 + c₀) + y • (WithLp.ofLp p').2)
                  ((WithLp.ofLp p').2)
                ∂(disorderPairLaw (Ω := Ω) (N := N) G₁ G₂)|)
        ∂(disorderPairLaw (Ω := Ω) (N := N) G₁ G₂))
      = ∫ ω, FiniteGibbs.gibbs_average (α := Config N) ((G₁.U ω + c₀) + y • G₂.U ω)
          (fun σ => |(1 / (N : ℝ)) * (G₂.U ω) σ
            - ∫ ω', (1 / (N : ℝ)) * FiniteGibbs.gibbs_average (α := Config N)
                ((G₁.U ω' + c₀) + y • G₂.U ω') (G₂.U ω') ∂(ℙ : Measure Ω)|) ∂(ℙ : Measure Ω) := by
  have hmeasdp : Measurable (disorderPair (Ω := Ω) (N := N) G₁ G₂) :=
    measurable_disorderPair (Ω := Ω) (N := N) G₁ G₂
  have hinner : (∫ p' : DisorderSpace (N := N), (1 / (N : ℝ)) *
        FiniteGibbs.gibbs_average (α := Config N)
          (((WithLp.ofLp p').1 + c₀) + y • (WithLp.ofLp p').2) ((WithLp.ofLp p').2)
        ∂(disorderPairLaw (Ω := Ω) (N := N) G₁ G₂))
      = ∫ ω', (1 / (N : ℝ)) * FiniteGibbs.gibbs_average (α := Config N)
          ((G₁.U ω' + c₀) + y • G₂.U ω') (G₂.U ω') ∂(ℙ : Measure Ω) := by
    rw [disorderPairLaw, integral_map hmeasdp.aemeasurable
      ((FiniteGibbs.measurable_gibbs_average_path (α := Config N)
        (measurable_pair_fst (N := N) c₀) (measurable_pair_snd (N := N)) y).const_mul
          _).aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω' => ?_)
    simp only [disorderPair, WithLp.ofLp_toLp]
  rw [disorderPairLaw, integral_map hmeasdp.aemeasurable
    (FiniteGibbs.measurable_totalFluct_path (α := Config N) N
      (measurable_pair_fst (N := N) c₀) (measurable_pair_snd (N := N)) y).aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [disorderPair, WithLp.ofLp_toLp, hinner]

set_option maxHeartbeats 1600000 in
-- The two halves of Theorem 12.1.1 are combined here; the statement carries several nested
-- integrals over the disorder pair space, so elaborating the final `add_le_add` chain needs more
-- than the default budget.
omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- **Talagrand, Vol. II, Theorem 12.1.1, for a component of the disorder.**

Along the affine interpolation `H_A + x H_B`, the mean absolute fluctuation of the *second*
Hamiltonian per site, integrated over `x ∈ [a,b]`, is bounded by an explicit sum of three terms:
a Gibbs term `O(√(M₂)/N)`, a `δ`-term `O(δ M₂/N)`, and a `1/δ` term `O(√(M₁ + B²M₂)/(δN))`.

For a mixed `p`-spin model `M₁, M₂ = O(N)`, so the three terms are `O(N^{-1/2})`, `O(δ)` and
`O(N^{-1/2}/δ)`: choosing `δ = N^{-1/4}` gives `O(N^{-1/4})`, Talagrand's rate. This is what makes
the `p`-spin component self-average, hence the Ghirlanda–Guerra identity hold at the monomial
`φ(r) = rᵖ`. -/
theorem intervalIntegral_component_fluctuation_le
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) (c₀ : EnergySpace N)
    {δ a b : ℝ} (hδ : 0 < δ) (hab : a ≤ b) {d M₁ M₂ : ℝ}
    (hdiag : ∀ σ : Config N, K₂ σ σ = d)
    (hk₁ : ∀ σ τ : Config N, |K₁ σ τ| ≤ M₁) (hk₂ : ∀ σ τ : Config N, |K₂ σ τ| ≤ M₂) :
    (∫ x in a..b, ∫ p : DisorderSpace (N := N),
        FiniteGibbs.gibbs_average (α := Config N)
          (((WithLp.ofLp p).1 + c₀) + x • (WithLp.ofLp p).2)
          (fun σ => |(1 / (N : ℝ)) * ((WithLp.ofLp p).2) σ
            - ∫ p' : DisorderSpace (N := N), (1 / (N : ℝ)) *
                FiniteGibbs.gibbs_average (α := Config N)
                  (((WithLp.ofLp p').1 + c₀) + x • (WithLp.ofLp p').2)
                  ((WithLp.ofLp p').2)
                ∂(disorderPairLaw (Ω := Ω) (N := N) G₁ G₂)|)
        ∂(disorderPairLaw (Ω := Ω) (N := N) G₁ G₂))
      ≤ Real.sqrt ((b - a) * ((1 / (N : ℝ)) * (2 * ((|a| + |b|) * M₂) / (N : ℝ))))
        + (2 * δ * (2 * ((|a| + |b| + 2 * δ) * M₂) / (N : ℝ))
          + 3 * (b - a)
              * (Real.sqrt (M₁ + (|a| + |b| + δ) ^ 2 * M₂) / (N : ℝ)) / δ) := by
  classical
  set P : Measure (DisorderSpace (N := N)) := disorderPairLaw (Ω := Ω) (N := N) G₁ G₂ with hP
  set U : DisorderSpace (N := N) → EnergySpace N :=
    fun p => (WithLp.ofLp p).1 + c₀ with hU
  set V : DisorderSpace (N := N) → EnergySpace N := fun p => (WithLp.ofLp p).2 with hV
  have hgauss : ProbabilityTheory.IsGaussian P := by
    rw [hP]; exact isGaussian_disorderPairLaw_of_indep (Ω := Ω) (N := N) G₁ G₂ hindep
  have hmean0 : (∫ p : DisorderSpace (N := N), p ∂P) = 0 := by
    rw [hP]; exact disorderPairLaw_mean0 (Ω := Ω) (N := N) G₁ G₂
  have hUm : Measurable U := measurable_pair_fst (N := N) c₀
  have hVm : Measurable V := measurable_pair_snd (N := N)
  -- Gaussian moments
  have hdom := ProbabilityTheory.IsGaussian.integrable_one_add_norm_pow (μ := P) 2
  set cS : ℝ := ‖WithLp.sndL (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
    (α := EnergySpace N) (β := EnergySpace N)‖ with hcS
  set cF : ℝ := ‖WithLp.fstL (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
    (α := EnergySpace N) (β := EnergySpace N)‖ with hcF
  have hcS0 : (0 : ℝ) ≤ cS := norm_nonneg _
  have hcF0 : (0 : ℝ) ≤ cF := norm_nonneg _
  have hsnd : ∀ p : DisorderSpace (N := N), ‖V p‖ ≤ cS * ‖p‖ := fun p =>
    (WithLp.sndL (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
      (α := EnergySpace N) (β := EnergySpace N)).le_opNorm p
  have hfst : ∀ p : DisorderSpace (N := N), ‖U p‖ ≤ cF * ‖p‖ + ‖c₀‖ := by
    intro p
    refine le_trans (norm_add_le _ _) (add_le_add ?_ le_rfl)
    exact (WithLp.fstL (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
      (α := EnergySpace N) (β := EnergySpace N)).le_opNorm p
  have hVi : Integrable (fun p : DisorderSpace (N := N) => ‖V p‖) P := by
    refine Integrable.mono' (hdom.const_mul cS) (hVm.norm.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => ?_)
    have h := hsnd p
    have h0 : (0 : ℝ) ≤ ‖p‖ := norm_nonneg p
    have hkey : ‖p‖ ≤ (1 + ‖p‖) ^ 2 := by nlinarith [h0, sq_nonneg ‖p‖]
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (V p))]
    calc ‖V p‖ ≤ cS * ‖p‖ := h
      _ ≤ cS * (1 + ‖p‖) ^ 2 := mul_le_mul_of_nonneg_left hkey hcS0
  have hVi2 : Integrable (fun p : DisorderSpace (N := N) => ‖V p‖ ^ 2) P := by
    refine Integrable.mono' (hdom.const_mul (cS ^ 2)) ((hVm.norm.pow_const 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => ?_)
    have h := hsnd p
    have h0 : (0 : ℝ) ≤ ‖p‖ := norm_nonneg p
    have hVn : (0 : ℝ) ≤ ‖V p‖ := norm_nonneg (V p)
    have hkey : ‖p‖ ^ 2 ≤ (1 + ‖p‖) ^ 2 := by nlinarith [h0]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖V p‖ ^ 2 ≤ (cS * ‖p‖) ^ 2 := pow_le_pow_left₀ hVn h 2
      _ = cS ^ 2 * ‖p‖ ^ 2 := by ring
      _ ≤ cS ^ 2 * (1 + ‖p‖) ^ 2 := mul_le_mul_of_nonneg_left hkey (by positivity)
  have hUi : Integrable (fun p : DisorderSpace (N := N) => ‖U p‖) P := by
    refine Integrable.mono' (hdom.const_mul (cF + ‖c₀‖)) (hUm.norm.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => ?_)
    have h := hfst p
    have h0 : (0 : ℝ) ≤ ‖p‖ := norm_nonneg p
    have h1 : (1 : ℝ) ≤ (1 + ‖p‖) ^ 2 := by nlinarith [h0]
    have hkey : ‖p‖ ≤ (1 + ‖p‖) ^ 2 := by nlinarith [h0, sq_nonneg ‖p‖]
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (U p))]
    calc ‖U p‖ ≤ cF * ‖p‖ + ‖c₀‖ := h
      _ ≤ cF * (1 + ‖p‖) ^ 2 + ‖c₀‖ * (1 + ‖p‖) ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left hkey hcF0)
            (by nlinarith [norm_nonneg c₀, h1])
      _ = (cF + ‖c₀‖) * (1 + ‖p‖) ^ 2 := by ring
  -- the derivative bound: Lemma 12.1.4 for the component
  have hM₂0 : (0 : ℝ) ≤ M₂ :=
    le_trans (abs_nonneg _) (hk₂ (Classical.arbitrary (Config N)) (Classical.arbitrary _))
  have hderiv : ∀ y : ℝ,
      |∫ p : DisorderSpace (N := N), -(1 / (N : ℝ)) *
          FiniteGibbs.gibbs_average (α := Config N) (U p + y • V p) (V p) ∂P|
        ≤ (1 / (N : ℝ)) * (2 * (|y| * M₂)) := by
    intro y
    have hpt : ∀ p : DisorderSpace (N := N),
        -(1 / (N : ℝ)) * FiniteGibbs.gibbs_average (α := Config N) (U p + y • V p) (V p)
          = -(1 / (N : ℝ)) * FiniteGibbs.gibbs_average (α := Config N)
              (pairAffine N y p + c₀) ((WithLp.ofLp p).2) := by
      intro p
      rw [hU, hV, pairU_add_smul (N := N) c₀ y p]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), MeasureTheory.integral_const_mul,
      abs_mul]
    have hbase : |∫ p : DisorderSpace (N := N),
        FiniteGibbs.gibbs_average (α := Config N) (pairAffine N y p + c₀)
          ((WithLp.ofLp p).2) ∂P| ≤ 2 * (|y| * M₂) := by
      rw [hP]
      exact abs_integral_gibbs_average_component_le (Ω := Ω) (N := N) G₁ G₂ hindep y c₀
        (d := y * d) (fun σ => by rw [hdiag σ]) hk₂
    calc |-(1 / (N : ℝ))| * |∫ p : DisorderSpace (N := N),
            FiniteGibbs.gibbs_average (α := Config N) (pairAffine N y p + c₀)
              ((WithLp.ofLp p).2) ∂P|
        ≤ |-(1 / (N : ℝ))| * (2 * (|y| * M₂)) :=
          mul_le_mul_of_nonneg_left hbase (abs_nonneg _)
      _ = (1 / (N : ℝ)) * (2 * (|y| * M₂)) := by
          rw [abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (N : ℝ))]
  -- the concentration hypothesis
  have hC : ∀ y ∈ Set.Icc (a - δ) (b + δ),
      (∫ p : DisorderSpace (N := N), |free_energy_density (N := N) (U p + y • V p)
          - ∫ p' : DisorderSpace (N := N), free_energy_density (N := N) (U p' + y • V p') ∂P| ∂P)
        ≤ Real.sqrt (M₁ + (|a| + |b| + δ) ^ 2 * M₂) / (N : ℝ) := by
    intro y hy
    have hpt : ∀ p : DisorderSpace (N := N),
        free_energy_density (N := N) (U p + y • V p)
          = free_energy_density (N := N) (pairAffine N y p + c₀) := by
      intro p; rw [hU, hV, pairU_add_smul (N := N) c₀ y p]
    have hyb : |y| ≤ |a| + |b| + δ := by
      obtain ⟨h1, h2⟩ := hy
      rcases abs_cases y with ⟨he, _⟩ | ⟨he, _⟩
      · rw [he]
        rcases abs_cases b with ⟨hb, _⟩ | ⟨hb, _⟩ <;> nlinarith [abs_nonneg a, abs_nonneg b,
          le_abs_self b, neg_abs_le b, le_abs_self a, neg_abs_le a]
      · rw [he]
        nlinarith [abs_nonneg a, abs_nonneg b, le_abs_self a, neg_abs_le a, le_abs_self b,
          neg_abs_le b]
    have hmono : Real.sqrt (M₁ + y ^ 2 * M₂) ≤ Real.sqrt (M₁ + (|a| + |b| + δ) ^ 2 * M₂) := by
      refine Real.sqrt_le_sqrt ?_
      have hsq : y ^ 2 ≤ (|a| + |b| + δ) ^ 2 := by
        have h0 : (0 : ℝ) ≤ |a| + |b| + δ := by
          have := abs_nonneg a; have := abs_nonneg b; linarith
        calc y ^ 2 = |y| ^ 2 := (sq_abs y).symm
          _ ≤ (|a| + |b| + δ) ^ 2 := pow_le_pow_left₀ (abs_nonneg y) hyb 2
      nlinarith [hM₂0, hsq]
    calc (∫ p : DisorderSpace (N := N), |free_energy_density (N := N) (U p + y • V p)
            - ∫ p' : DisorderSpace (N := N),
                free_energy_density (N := N) (U p' + y • V p') ∂P| ∂P)
        = ∫ p : DisorderSpace (N := N),
            |free_energy_density (N := N) (pairAffine N y p + c₀)
              - ∫ p' : DisorderSpace (N := N),
                  free_energy_density (N := N) (pairAffine N y p' + c₀) ∂P| ∂P := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          simp only [hpt p, integral_congr_ae (Filter.Eventually.of_forall hpt)]
      _ ≤ Real.sqrt (M₁ + y ^ 2 * M₂) / (N : ℝ) := by
          rw [hP]
          exact integral_abs_free_energy_density_pairAffine_sub_mean_le (Ω := Ω) (N := N)
            G₁ G₂ hindep y c₀ hk₁ hk₂
      _ ≤ Real.sqrt (M₁ + (|a| + |b| + δ) ^ 2 * M₂) / (N : ℝ) := by
          have hNn : (0 : ℝ) ≤ ((N : ℝ))⁻¹ := by positivity
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hmono hNn
  -- the two halves
  have hsplit := FiniteGibbs.intervalIntegral_integral_totalFluct_le (α := Config N)
    (P := P) (U := U) (V := V) N hUm hVm hVi hab
  have hgibbs := FiniteGibbs.intervalIntegral_absFluct_le (α := Config N)
    (P := P) (U := U) (V := V) N hUm hVm hVi hVi2 hab
  have hdis := FiniteGibbs.intervalIntegral_integral_abs_meanEnergy_sub_le (α := Config N)
    (P := P) (U := U) (V := V) N hUm hVm hUi hVi hδ hab hC
  -- the endpoint derivative bound
  have hDbound : ∀ y : ℝ,
      |∫ p : DisorderSpace (N := N), -(1 / (N : ℝ)) *
          FiniteGibbs.gibbs_average (α := Config N) (U p + y • V p) (V p) ∂P|
        ≤ 2 * (|y| * M₂) / (N : ℝ) := by
    intro y
    refine (hderiv y).trans ?_
    rw [div_eq_mul_inv]
    ring_nf
    exact le_rfl
  have hderivEq : ∀ y : ℝ,
      deriv (fun z : ℝ => ∫ p : DisorderSpace (N := N),
          FiniteGibbs.free_energy_density (α := Config N) N (U p + z • V p) ∂P) y
        = ∫ p : DisorderSpace (N := N), -(1 / (N : ℝ)) *
            FiniteGibbs.gibbs_average (α := Config N) (U p + y • V p) (V p) ∂P := by
    intro y
    rw [FiniteGibbs.deriv_integral_free_energy_density (α := Config N)
      (P := P) (U := U) (V := V) N hUm hVm hUi hVi y, ← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
  have hM₂0' : (0 : ℝ) ≤ M₂ := hM₂0
  have hNpos : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  -- (1) the Gibbs half
  have hGibbs :
      (∫ x in a..b, ∫ p : DisorderSpace (N := N), (1 / (N : ℝ)) *
          FiniteGibbs.gibbs_average (α := Config N) (U p + x • V p)
            (fun σ => |V p σ - FiniteGibbs.gibbs_average (α := Config N)
              (U p + x • V p) (V p)|) ∂P)
        ≤ Real.sqrt ((b - a) * ((1 / (N : ℝ)) * (2 * ((|a| + |b|) * M₂) / (N : ℝ)))) := by
    refine hgibbs.trans (Real.sqrt_le_sqrt ?_)
    have hb := abs_le.1 (hDbound b)
    have ha := abs_le.1 (hDbound a)
    have hstep : ((∫ p : DisorderSpace (N := N), -(1 / (N : ℝ)) *
              FiniteGibbs.gibbs_average (α := Config N) (U p + b • V p) (V p) ∂P)
            - ∫ p : DisorderSpace (N := N), -(1 / (N : ℝ)) *
              FiniteGibbs.gibbs_average (α := Config N) (U p + a • V p) (V p) ∂P)
          ≤ 2 * ((|a| + |b|) * M₂) / (N : ℝ) := by
      have h1 := hb.2
      have h2 := ha.1
      have harith : 2 * (|b| * M₂) / (N : ℝ) + 2 * (|a| * M₂) / (N : ℝ)
          = 2 * ((|a| + |b|) * M₂) / (N : ℝ) := by ring
      linarith [h1, h2, harith]
    have hba : (0 : ℝ) ≤ b - a := by linarith
    have hinv : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep hinv) hba
  -- (2) the disorder half
  have hDisorder :
      (∫ x in a..b, ∫ p : DisorderSpace (N := N),
          |(1 / (N : ℝ)) * FiniteGibbs.gibbs_average (α := Config N) (U p + x • V p) (V p)
            - ∫ p' : DisorderSpace (N := N), (1 / (N : ℝ)) *
                FiniteGibbs.gibbs_average (α := Config N) (U p' + x • V p') (V p') ∂P| ∂P)
        ≤ 2 * δ * (2 * ((|a| + |b| + 2 * δ) * M₂) / (N : ℝ))
          + 3 * (b - a) * (Real.sqrt (M₁ + (|a| + |b| + δ) ^ 2 * M₂) / (N : ℝ)) / δ := by
    refine hdis.trans (add_le_add ?_ le_rfl)
    have hb := abs_le.1 (hDbound (b + δ))
    have ha := abs_le.1 (hDbound (a - δ))
    have hbd : |b + δ| ≤ |b| + δ := by
      rcases abs_cases (b + δ) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
        [linarith [le_abs_self b]; linarith [neg_abs_le b, hδ]]
    have had : |a - δ| ≤ |a| + δ := by
      rcases abs_cases (a - δ) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
        [linarith [le_abs_self a, hδ]; linarith [neg_abs_le a]]
    have hmb : 2 * (|b + δ| * M₂) / (N : ℝ) ≤ 2 * ((|b| + δ) * M₂) / (N : ℝ) := by
      have hmul : |b + δ| * M₂ ≤ (|b| + δ) * M₂ := mul_le_mul_of_nonneg_right hbd hM₂0'
      have hn : (0 : ℝ) ≤ ((N : ℝ))⁻¹ := by positivity
      rw [div_eq_mul_inv, div_eq_mul_inv]
      nlinarith [hmul, hn]
    have hma : 2 * (|a - δ| * M₂) / (N : ℝ) ≤ 2 * ((|a| + δ) * M₂) / (N : ℝ) := by
      have hmul : |a - δ| * M₂ ≤ (|a| + δ) * M₂ := mul_le_mul_of_nonneg_right had hM₂0'
      have hn : (0 : ℝ) ≤ ((N : ℝ))⁻¹ := by positivity
      rw [div_eq_mul_inv, div_eq_mul_inv]
      nlinarith [hmul, hn]
    have harith : 2 * ((|b| + δ) * M₂) / (N : ℝ) + 2 * ((|a| + δ) * M₂) / (N : ℝ)
        = 2 * ((|a| + |b| + 2 * δ) * M₂) / (N : ℝ) := by ring
    have hstep : (deriv (fun z : ℝ => ∫ p : DisorderSpace (N := N),
              FiniteGibbs.free_energy_density (α := Config N) N (U p + z • V p) ∂P) (b + δ)
            - deriv (fun z : ℝ => ∫ p : DisorderSpace (N := N),
              FiniteGibbs.free_energy_density (α := Config N) N (U p + z • V p) ∂P) (a - δ))
          ≤ 2 * ((|a| + |b| + 2 * δ) * M₂) / (N : ℝ) := by
      rw [hderivEq (b + δ), hderivEq (a - δ)]
      linarith [hb.2, ha.1, hmb, hma, harith]
    have hδ0 : (0 : ℝ) ≤ 2 * δ := by linarith
    exact mul_le_mul_of_nonneg_left hstep hδ0
  exact hsplit.trans (add_le_add hGibbs hDisorder)

/-! ### The Ghirlanda–Guerra error of the component, in Theorem 12.1.1's quantity -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- **The Ghirlanda–Guerra error of the `p`-spin component is `B N` times the quantity Theorem
12.1.1 controls.**

The right-hand side is exactly the integrand of
`SpinGlass.intervalIntegral_component_fluctuation_le`, so composing the two bounds the
Ghirlanda–Guerra combination of the monomial kernel by `B N ·O(N^{-1/4})` on average over the
coupling. Exact at every finite volume: no limit, no perturbation. -/
theorem abs_ghirlandaGuerraCombinationOf_component_le
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) (hN : N ≠ 0) (x : ℝ) (c₀ : EnergySpace N)
    {d : ℝ} (hdiag : ∀ σ : Config N, K₂ σ σ = d)
    (m : ℕ) (f : FiniteGibbs.ReplicaFun (α := Config N) m) (i : Fin m) {B : ℝ}
    (hB : ∀ σs, |f σs| ≤ B) :
    |FiniteGibbs.ghirlandaGuerraCombinationOf
        ((disorderPairLaw (Ω := Ω) (N := N) G₁ G₂).map
          (fun p : DisorderSpace (N := N) => pairAffine N x p + c₀))
        (FiniteGibbs.crossKernel (disorderPairLaw (Ω := Ω) (N := N) G₁ G₂)
          (pairAffine N x) (std_basis_right (N := N))) m f i|
      ≤ B * ((N : ℝ) * ∫ p : DisorderSpace (N := N),
          FiniteGibbs.gibbs_average (α := Config N)
            (((WithLp.ofLp p).1 + c₀) + x • (WithLp.ofLp p).2)
            (fun σ => |(1 / (N : ℝ)) * ((WithLp.ofLp p).2) σ
              - ∫ p' : DisorderSpace (N := N), (1 / (N : ℝ)) *
                  FiniteGibbs.gibbs_average (α := Config N)
                    (((WithLp.ofLp p').1 + c₀) + x • (WithLp.ofLp p').2)
                    ((WithLp.ofLp p').2)
                  ∂(disorderPairLaw (Ω := Ω) (N := N) G₁ G₂)|)
          ∂(disorderPairLaw (Ω := Ω) (N := N) G₁ G₂)) := by
  classical
  set P : Measure (DisorderSpace (N := N)) := disorderPairLaw (Ω := Ω) (N := N) G₁ G₂ with hP
  have hgauss : ProbabilityTheory.IsGaussian P := by
    rw [hP]; exact isGaussian_disorderPairLaw_of_indep (Ω := Ω) (N := N) G₁ G₂ hindep
  have hmean0 : (∫ p : DisorderSpace (N := N), p ∂P) = 0 := by
    rw [hP]; exact disorderPairLaw_mean0 (Ω := Ω) (N := N) G₁ G₂
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hcross := crossKernel_pairAffine_std_basis_right (Ω := Ω) (N := N) G₁ G₂ hindep x
  have hdiag' : ∀ σ : Config N,
      FiniteGibbs.crossKernel P (pairAffine N x) (std_basis_right (N := N)) σ σ = x * d := by
    intro σ
    rw [hP, hcross σ σ, hdiag σ]
  have hw : ∀ σ : Config N, ‖std_basis_right (N := N) σ‖ ≤ 1 :=
    fun σ => le_of_eq (norm_std_basis_right N σ)
  have hbase := FiniteGibbs.ghirlandaGuerra_error_of_comp_le_integral_abs (P := P) hmean0
    (pairAffine N x) c₀ hw hdiag' m f i hB
  -- rewrite the mean of the component field
  have hbridge : ∀ p' : DisorderSpace (N := N),
      FiniteGibbs.gibbs_average_n_det (α := Config N) (n := 1) (pairAffine N x p' + c₀)
          (fun τs => ⟪p', std_basis_right (N := N) (τs 0)⟫_ℝ)
        = FiniteGibbs.gibbs_average (α := Config N) (pairAffine N x p' + c₀)
            ((WithLp.ofLp p').2) := by
    intro p'
    rw [FiniteGibbs.gibbs_average_one, FiniteGibbs.gibbs_average]
    exact Finset.sum_congr rfl fun τ _ => by
      rw [inner_apply_std_basis_right (N := N) τ p']; ring
  set c : ℝ := ∫ p' : DisorderSpace (N := N), (1 / (N : ℝ)) *
    FiniteGibbs.gibbs_average (α := Config N) (pairAffine N x p' + c₀)
      ((WithLp.ofLp p').2) ∂P with hcdef
  have hameq : (∫ p' : DisorderSpace (N := N),
        FiniteGibbs.gibbs_average_n_det (α := Config N) (n := 1) (pairAffine N x p' + c₀)
          (fun τs => ⟪p', std_basis_right (N := N) (τs 0)⟫_ℝ) ∂P)
      = (N : ℝ) * c := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hbridge), hcdef,
      MeasureTheory.integral_const_mul]
    field_simp
  -- rewrite the fluctuation integrand
  have hptwise : ∀ p : DisorderSpace (N := N),
      (∑ σ : Config N, FiniteGibbs.gibbs_pmf (α := Config N) (pairAffine N x p + c₀) σ
          * |⟪p, std_basis_right (N := N) σ⟫_ℝ - (N : ℝ) * c|)
        = (N : ℝ) * FiniteGibbs.gibbs_average (α := Config N) (pairAffine N x p + c₀)
            (fun σ => |(1 / (N : ℝ)) * ((WithLp.ofLp p).2) σ - c|) := by
    intro p
    rw [FiniteGibbs.gibbs_average, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [inner_apply_std_basis_right (N := N) σ p]
    have habs : |((WithLp.ofLp p).2) σ - (N : ℝ) * c|
        = (N : ℝ) * |(1 / (N : ℝ)) * ((WithLp.ofLp p).2) σ - c| := by
      rw [show (1 / (N : ℝ)) * ((WithLp.ofLp p).2) σ - c
          = (1 / (N : ℝ)) * (((WithLp.ofLp p).2) σ - (N : ℝ) * c) from by field_simp,
        abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (N : ℝ))]
      field_simp
    rw [habs]
    ring
  rw [hameq, integral_congr_ae (Filter.Eventually.of_forall hptwise),
    MeasureTheory.integral_const_mul] at hbase
  -- finally, match the two forms of the Hamiltonian
  have hHam : ∀ p : DisorderSpace (N := N),
      ((WithLp.ofLp p).1 + c₀) + x • (WithLp.ofLp p).2 = pairAffine N x p + c₀ :=
    fun p => pairU_add_smul (N := N) c₀ x p
  have hcc : (∫ p' : DisorderSpace (N := N), (1 / (N : ℝ)) *
        FiniteGibbs.gibbs_average (α := Config N)
          (((WithLp.ofLp p').1 + c₀) + x • (WithLp.ofLp p').2)
          ((WithLp.ofLp p').2) ∂P) = c := by
    rw [hcdef]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p' => by simp only [hHam p'])
  rw [hP]
  rw [show (∫ p : DisorderSpace (N := N),
        FiniteGibbs.gibbs_average (α := Config N)
          (((WithLp.ofLp p).1 + c₀) + x • (WithLp.ofLp p).2)
          (fun σ => |(1 / (N : ℝ)) * ((WithLp.ofLp p).2) σ
            - ∫ p' : DisorderSpace (N := N), (1 / (N : ℝ)) *
                FiniteGibbs.gibbs_average (α := Config N)
                  (((WithLp.ofLp p').1 + c₀) + x • (WithLp.ofLp p').2)
                  ((WithLp.ofLp p').2) ∂P|) ∂P)
      = ∫ p : DisorderSpace (N := N),
          FiniteGibbs.gibbs_average (α := Config N) (pairAffine N x p + c₀)
            (fun σ => |(1 / (N : ℝ)) * ((WithLp.ofLp p).2) σ - c|) ∂P from by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [hHam p, hcc]]
  exact hbase

/-! ### The Ghirlanda–Guerra identity for the component at a typical coupling -/

set_option maxHeartbeats 1600000 in
-- The statement composes Theorem 12.1.1 with the Ghirlanda–Guerra error bound; both carry several
-- nested integrals over the disorder pair space, so elaboration needs more than the default budget.
omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- **The Ghirlanda–Guerra identity for a component of the disorder, with an explicit rate, at
some coupling in every window.**

Composing `SpinGlass.intervalIntegral_component_fluctuation_le` (Theorem 12.1.1 for the component)
with `SpinGlass.abs_ghirlandaGuerraCombinationOf_component_le` and the mean value theorem for
interval integrals: at some coupling `x ∈ [a,b]` the Ghirlanda–Guerra combination of the
component's cross kernel is at most `B N` times `ε/(b-a)`, where `ε` is Theorem 12.1.1's bound.

For a mixed `p`-spin model `M₁, M₂ = O(N)` and `ε = O(N^{-1/4})` at `δ = N^{-1/4}`; dividing by the
kernel scale `x aₚ N` — which is what
`SpinGlass.abs_ghirlandaGuerra_defect_of_le` does — gives the defect in Talagrand's identity
(15.40) at the monomial `φ(r) = rᵖ`, to order `N^{-1/4}`. Exact at every finite volume: no limit
and no perturbation. -/
theorem exists_coupling_abs_ghirlandaGuerraCombinationOf_component_le
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) (hN : N ≠ 0) (c₀ : EnergySpace N)
    {δ a b : ℝ} (hδ : 0 < δ) (hab : a < b) {d M₁ M₂ : ℝ}
    (hdiag : ∀ σ : Config N, K₂ σ σ = d)
    (hk₁ : ∀ σ τ : Config N, |K₁ σ τ| ≤ M₁) (hk₂ : ∀ σ τ : Config N, |K₂ σ τ| ≤ M₂) :
    ∃ x ∈ Set.Icc a b, ∀ (m : ℕ) (f : FiniteGibbs.ReplicaFun (α := Config N) m) (i : Fin m)
      {B : ℝ}, (∀ σs, |f σs| ≤ B) →
      |FiniteGibbs.ghirlandaGuerraCombinationOf
          ((disorderPairLaw (Ω := Ω) (N := N) G₁ G₂).map
            (fun p : DisorderSpace (N := N) => pairAffine N x p + c₀))
          (FiniteGibbs.crossKernel (disorderPairLaw (Ω := Ω) (N := N) G₁ G₂)
            (pairAffine N x) (std_basis_right (N := N))) m f i|
        ≤ B * ((N : ℝ) *
            ((Real.sqrt ((b - a) * ((1 / (N : ℝ)) * (2 * ((|a| + |b|) * M₂) / (N : ℝ))))
              + (2 * δ * (2 * ((|a| + |b| + 2 * δ) * M₂) / (N : ℝ))
                + 3 * (b - a)
                    * (Real.sqrt (M₁ + (|a| + |b| + δ) ^ 2 * M₂) / (N : ℝ)) / δ))
              / (b - a))) := by
  classical
  set P : Measure (DisorderSpace (N := N)) := disorderPairLaw (Ω := Ω) (N := N) G₁ G₂ with hP
  set F : ℝ → ℝ := fun y => ∫ p : DisorderSpace (N := N),
    FiniteGibbs.gibbs_average (α := Config N)
      (((WithLp.ofLp p).1 + c₀) + y • (WithLp.ofLp p).2)
      (fun σ => |(1 / (N : ℝ)) * ((WithLp.ofLp p).2) σ
        - ∫ p' : DisorderSpace (N := N), (1 / (N : ℝ)) *
            FiniteGibbs.gibbs_average (α := Config N)
              (((WithLp.ofLp p').1 + c₀) + y • (WithLp.ofLp p').2)
              ((WithLp.ofLp p').2) ∂P|) ∂P with hF
  have hFapp : ∀ y : ℝ, F y = ∫ p : DisorderSpace (N := N),
      FiniteGibbs.gibbs_average (α := Config N)
        (((WithLp.ofLp p).1 + c₀) + y • (WithLp.ofLp p).2)
        (fun σ => |(1 / (N : ℝ)) * ((WithLp.ofLp p).2) σ
          - ∫ p' : DisorderSpace (N := N), (1 / (N : ℝ)) *
              FiniteGibbs.gibbs_average (α := Config N)
                (((WithLp.ofLp p').1 + c₀) + y • (WithLp.ofLp p').2)
                ((WithLp.ofLp p').2) ∂P|) ∂P := fun y => rfl
  have hgaussP : ProbabilityTheory.IsGaussian P := by
    rw [hP]; exact isGaussian_disorderPairLaw_of_indep (Ω := Ω) (N := N) G₁ G₂ hindep
  have hVi : Integrable (fun p : DisorderSpace (N := N) => ‖(WithLp.ofLp p).2‖) P := by
    rw [hP]; exact integrable_norm_pair_snd (Ω := Ω) (N := N) G₁ G₂ hindep
  have hFcont : Continuous F :=
    FiniteGibbs.continuous_integral_totalFluct (α := Config N) (P := P)
      (U := fun p : DisorderSpace (N := N) => (WithLp.ofLp p).1 + c₀)
      (V := fun p : DisorderSpace (N := N) => (WithLp.ofLp p).2) N
      (measurable_pair_fst (N := N) c₀) (measurable_pair_snd (N := N)) hVi
  have hFnn : ∀ y : ℝ, 0 ≤ F y := fun y =>
    integral_nonneg fun p => FiniteGibbs.gibbs_average_abs_smul_sub_const_nonneg
      (α := Config N) N _ _ _
  have hba : (0 : ℝ) < b - a := by linarith
  obtain ⟨x, hx, hxeq⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg
    (f := F) (g := fun _ : ℝ => (1 : ℝ)) (μ := volume) (a := a) (b := b)
    (hFcont.continuousOn) intervalIntegrable_const (fun y _ => zero_le_one)
  rw [Set.uIcc_of_le hab.le] at hx
  simp only [mul_one, intervalIntegral.integral_const, smul_eq_mul, mul_one] at hxeq
  have hbnd : (∫ y in a..b, F y)
      ≤ Real.sqrt ((b - a) * ((1 / (N : ℝ)) * (2 * ((|a| + |b|) * M₂) / (N : ℝ))))
        + (2 * δ * (2 * ((|a| + |b| + 2 * δ) * M₂) / (N : ℝ))
          + 3 * (b - a) * (Real.sqrt (M₁ + (|a| + |b| + δ) ^ 2 * M₂) / (N : ℝ)) / δ) := by
    rw [hF, hP]
    exact intervalIntegral_component_fluctuation_le (Ω := Ω) (N := N) G₁ G₂ hindep c₀ hδ hab.le
      hdiag hk₁ hk₂
  have hFx : F x
      ≤ (Real.sqrt ((b - a) * ((1 / (N : ℝ)) * (2 * ((|a| + |b|) * M₂) / (N : ℝ))))
          + (2 * δ * (2 * ((|a| + |b| + 2 * δ) * M₂) / (N : ℝ))
            + 3 * (b - a) * (Real.sqrt (M₁ + (|a| + |b| + δ) ^ 2 * M₂) / (N : ℝ)) / δ))
        / (b - a) := by
    rw [le_div_iff₀ hba, ← hxeq]
    exact hbnd
  refine ⟨x, hx, fun m f i B hB => ?_⟩
  have hcomb := abs_ghirlandaGuerraCombinationOf_component_le (Ω := Ω) (N := N) G₁ G₂ hindep hN
    x c₀ hdiag m f i hB
  rw [← hP, ← hFapp x] at hcomb
  refine hcomb.trans ?_
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB (fun _ => Classical.arbitrary (Config N)))
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  gcongr

end Pair

end

end SpinGlass
