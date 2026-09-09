/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.SKModel
import SpinGlass.FiniteGibbs.Product
import Mathlib.Analysis.Convex.Mul

/-!
# Splitting a system into two blocks

Guerra–Toninelli's proof that the free energy per site converges compares a system of `N₁ + N₂`
sites with the pair of independent subsystems on the first `N₁` and the last `N₂` sites
(Talagrand Vol. I, Theorem 1.3.9). This file provides the deterministic half of that comparison:

* `configSplit`: the relabelling `Config (N₁ + N₂) ≃ Config N₁ × Config N₂`;
* `cast_mul_overlap_split`: the overlap decomposes, `N R = N₁ R₁ + N₂ R₂`;
* `splitCovKernel`: the covariance kernel of the non-interacting composite;
* `sk_cov_kernel_le_splitCovKernel` and `sk_cov_kernel_diag_eq_splitCovKernel`: the SK kernel is
  **dominated** by the split kernel, with **equality on the diagonal** — the two hypotheses of the
  Gaussian comparison `trace_le_trace_of_kernel_le`. The domination is Sedrakyan's inequality
  `(N₁R₁ + N₂R₂)²/(N₁+N₂) ≤ N₁R₁² + N₂R₂²`.
-/

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ENNReal

namespace SpinGlass

noncomputable section

/-! ### The splitting of the configuration space -/

/-- **Splitting the configuration space.** A configuration of `N₁ + N₂` sites is a pair of
configurations, on the first `N₁` and the last `N₂` sites. -/
def configSplit (N₁ N₂ : ℕ) : Config (N₁ + N₂) ≃ Config N₁ × Config N₂ :=
  (Fin.appendEquiv N₁ N₂).symm

@[simp] lemma configSplit_fst (N₁ N₂ : ℕ) (σ : Config (N₁ + N₂)) (i : Fin N₁) :
    (configSplit N₁ N₂ σ).1 i = σ (Fin.castAdd N₂ i) := rfl

@[simp] lemma configSplit_snd (N₁ N₂ : ℕ) (σ : Config (N₁ + N₂)) (i : Fin N₂) :
    (configSplit N₁ N₂ σ).2 i = σ (Fin.natAdd N₁ i) := rfl

/-! ### The overlap of a split configuration -/

/-- The unnormalised overlap `∑ᵢ σᵢτᵢ` is `N` times the overlap, for every `N` (including `0`,
where both sides vanish). -/
lemma cast_mul_overlap (N : ℕ) (σ τ : Config N) :
    (N : ℝ) * overlap N σ τ = ∑ i : Fin N, spin N σ i * spin N τ i := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [overlap, overlapOf]
  · have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    simp only [overlap, overlapOf, spin, spinOf]
    field_simp

/-- **The overlap decomposes along a splitting**: `N R = N₁ R₁ + N₂ R₂`. Talagrand Vol. I,
§1.3. -/
theorem cast_mul_overlap_split (N₁ N₂ : ℕ) (σ τ : Config (N₁ + N₂)) :
    ((N₁ + N₂ : ℕ) : ℝ) * overlap (N₁ + N₂) σ τ
      = (N₁ : ℝ) * overlap N₁ (configSplit N₁ N₂ σ).1 (configSplit N₁ N₂ τ).1
        + (N₂ : ℝ) * overlap N₂ (configSplit N₁ N₂ σ).2 (configSplit N₁ N₂ τ).2 := by
  rw [cast_mul_overlap, cast_mul_overlap, cast_mul_overlap]
  simpa [spin, spinOf] using
    Fin.sum_univ_add
      (fun i : Fin (N₁ + N₂) => spin (N₁ + N₂) σ i * spin (N₁ + N₂) τ i)

/-! ### The covariance kernel of the non-interacting composite -/

/-- **The covariance kernel of the non-interacting composite system**: the sum of the two
subsystem kernels, each evaluated on its own block of spins. It is the covariance kernel of
`FiniteGibbs.sumEnergy (configSplit N₁ N₂)` applied to two independent subsystem Hamiltonians. -/
def splitCovKernel (N₁ N₂ : ℕ) (K₁ : Config N₁ → Config N₁ → ℝ)
    (K₂ : Config N₂ → Config N₂ → ℝ) (σ τ : Config (N₁ + N₂)) : ℝ :=
  K₁ (configSplit N₁ N₂ σ).1 (configSplit N₁ N₂ τ).1
    + K₂ (configSplit N₁ N₂ σ).2 (configSplit N₁ N₂ τ).2

/-- The split kernel is symmetric when its two blocks are. -/
lemma splitCovKernel_comm {N₁ N₂ : ℕ} {K₁ : Config N₁ → Config N₁ → ℝ}
    {K₂ : Config N₂ → Config N₂ → ℝ} (h₁ : ∀ σ τ, K₁ σ τ = K₁ τ σ)
    (h₂ : ∀ σ τ, K₂ σ τ = K₂ τ σ) (σ τ : Config (N₁ + N₂)) :
    splitCovKernel N₁ N₂ K₁ K₂ σ τ = splitCovKernel N₁ N₂ K₁ K₂ τ σ := by
  simp [splitCovKernel, h₁, h₂]

/-! ### Overlap-driven kernels with a convex profile -/

/-- **An overlap-driven kernel with a convex profile is dominated by the split kernel.** The
overlap of the whole system is the convex combination `R = (N₁/N) R₁ + (N₂/N) R₂` of the two block
overlaps, so Jensen's inequality for a profile `ξ` convex on `[-1,1]` gives
`N ξ(R) ≤ N₁ ξ(R₁) + N₂ ξ(R₂)`. This is the only model-dependent input of Guerra–Toninelli
superadditivity. Talagrand Vol. I, Theorem 1.3.9; Vol. II, §12.1. -/
theorem overlapCovKernel_le_splitCovKernel {N₁ N₂ : ℕ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    {ξ : ℝ → ℝ} (hξ : ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) ξ) (σ τ : Config (N₁ + N₂)) :
    overlapCovKernel (N := N₁ + N₂) ξ σ τ
      ≤ splitCovKernel N₁ N₂ (overlapCovKernel (N := N₁) ξ) (overlapCovKernel (N := N₂) ξ) σ τ := by
  have hx : (0 : ℝ) < (N₁ : ℝ) := by exact_mod_cast hN₁
  have hy : (0 : ℝ) < (N₂ : ℝ) := by exact_mod_cast hN₂
  have hM : (0 : ℝ) < (N₁ : ℝ) + (N₂ : ℝ) := by positivity
  have hM' : (N₁ : ℝ) + (N₂ : ℝ) ≠ 0 := hM.ne'
  simp only [splitCovKernel, overlapCovKernel_apply]
  push_cast
  set R := overlap (N₁ + N₂) σ τ with hR
  set R₁ := overlap N₁ (configSplit N₁ N₂ σ).1 (configSplit N₁ N₂ τ).1 with hR₁
  set R₂ := overlap N₂ (configSplit N₁ N₂ σ).2 (configSplit N₁ N₂ τ).2 with hR₂
  have hsum : ((N₁ : ℝ) + (N₂ : ℝ)) * R = (N₁ : ℝ) * R₁ + (N₂ : ℝ) * R₂ := by
    have := cast_mul_overlap_split N₁ N₂ σ τ
    push_cast at this
    simpa [hR, hR₁, hR₂] using this
  have hRab : R = ((N₁ : ℝ) / ((N₁ : ℝ) + N₂)) * R₁ + ((N₂ : ℝ) / ((N₁ : ℝ) + N₂)) * R₂ := by
    field_simp
    linear_combination hsum
  have hmem₁ : R₁ ∈ Set.Icc (-1 : ℝ) 1 := by
    have := abs_le.mp (abs_overlap_le_one N₁ (configSplit N₁ N₂ σ).1 (configSplit N₁ N₂ τ).1)
    exact ⟨this.1, this.2⟩
  have hmem₂ : R₂ ∈ Set.Icc (-1 : ℝ) 1 := by
    have := abs_le.mp (abs_overlap_le_one N₂ (configSplit N₁ N₂ σ).2 (configSplit N₁ N₂ τ).2)
    exact ⟨this.1, this.2⟩
  have hconv := hξ.2 hmem₁ hmem₂ (by positivity : (0 : ℝ) ≤ (N₁ : ℝ) / ((N₁ : ℝ) + N₂))
    (by positivity : (0 : ℝ) ≤ (N₂ : ℝ) / ((N₁ : ℝ) + N₂)) (by field_simp)
  simp only [smul_eq_mul] at hconv
  rw [← hRab] at hconv
  have hmul := mul_le_mul_of_nonneg_left hconv hM.le
  have hrhs : ((N₁ : ℝ) + (N₂ : ℝ)) * ((N₁ : ℝ) / ((N₁ : ℝ) + N₂) * ξ R₁
      + (N₂ : ℝ) / ((N₁ : ℝ) + N₂) * ξ R₂) = (N₁ : ℝ) * ξ R₁ + (N₂ : ℝ) * ξ R₂ := by
    field_simp
  linarith

/-- **An overlap-driven kernel agrees with the split kernel on the diagonal**: both are
`N ξ(1)`, since every configuration has self-overlap `1`. -/
theorem overlapCovKernel_diag_eq_splitCovKernel {N₁ N₂ : ℕ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (ξ : ℝ → ℝ) (σ : Config (N₁ + N₂)) :
    overlapCovKernel (N := N₁ + N₂) ξ σ σ
      = splitCovKernel N₁ N₂ (overlapCovKernel (N := N₁) ξ) (overlapCovKernel (N := N₂) ξ) σ σ := by
  have hN : 0 < N₁ + N₂ := Nat.add_pos_left hN₁ N₂
  simp only [splitCovKernel, overlapCovKernel_apply, overlap_self (N := N₁ + N₂) hN,
    overlap_self (N := N₁) hN₁, overlap_self (N := N₂) hN₂]
  push_cast
  ring

/-! ### The SK model as a corollary -/

/-- The SK profile `β² r²/2` is convex. -/
lemma convexOn_skCovXi (β : ℝ) : ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) (skCovXi β) := by
  have h : skCovXi β = fun x : ℝ => (β ^ 2 / 2) • x ^ 2 := by
    funext x; simp only [skCovXi, smul_eq_mul]; ring
  rw [h]
  exact ((Even.convexOn_pow (𝕜 := ℝ) even_two).smul (by positivity)).subset (Set.subset_univ _)
    (convex_Icc _ _)

/-- **The SK kernel is dominated by the split kernel**: the case `ξ(r) = β² r²/2` of
`overlapCovKernel_le_splitCovKernel`. Talagrand Vol. I, Theorem 1.3.9. -/
theorem sk_cov_kernel_le_splitCovKernel {N₁ N₂ : ℕ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (β : ℝ)
    (σ τ : Config (N₁ + N₂)) :
    sk_cov_kernel (N₁ + N₂) β σ τ
      ≤ splitCovKernel N₁ N₂ (sk_cov_kernel N₁ β) (sk_cov_kernel N₂ β) σ τ :=
  overlapCovKernel_le_splitCovKernel hN₁ hN₂ (convexOn_skCovXi β) σ τ

/-- **The SK kernel agrees with the split kernel on the diagonal.** Both are `(N₁+N₂)β²/2`.
Talagrand Vol. I, Theorem 1.3.9. -/
theorem sk_cov_kernel_diag_eq_splitCovKernel {N₁ N₂ : ℕ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (β : ℝ)
    (σ : Config (N₁ + N₂)) :
    sk_cov_kernel (N₁ + N₂) β σ σ
      = splitCovKernel N₁ N₂ (sk_cov_kernel N₁ β) (sk_cov_kernel N₂ β) σ σ :=
  overlapCovKernel_diag_eq_splitCovKernel hN₁ hN₂ (skCovXi β) σ

/-! ### The disorder of the non-interacting composite -/

namespace GaussianDisorder

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {N₁ N₂ : ℕ} {K₁ : Config N₁ → Config N₁ → ℝ} {K₂ : Config N₂ → Config N₂ → ℝ}
variable (G₁ : GaussianDisorder (Ω := Ω) (N := N₁) (ℙ : Measure Ω) K₁)
variable (G₂ : GaussianDisorder (Ω := Ω) (N := N₂) (ℙ : Measure Ω) K₂)

/-- **The Hamiltonian of the non-interacting composite of two disorders**: each subsystem carries
its own Hamiltonian, and there is no interaction term. -/
def splitU : Ω → EnergySpace (N₁ + N₂) :=
  fun ω => FiniteGibbs.sumEnergy (configSplit N₁ N₂) (G₁.U ω, G₂.U ω)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
@[simp] lemma splitU_apply (ω : Ω) (σ : Config (N₁ + N₂)) :
    splitU G₁ G₂ ω σ
      = G₁.U ω (configSplit N₁ N₂ σ).1 + G₂.U ω (configSplit N₁ N₂ σ).2 := rfl

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma measurable_splitU : Measurable (splitU G₁ G₂) :=
  (FiniteGibbs.sumEnergy (configSplit N₁ N₂)).continuous.measurable.comp
    (G₁.measU.prodMk G₂.measU)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The composite Hamiltonian is Gaussian: it is a continuous linear image of the jointly Gaussian
pair of subsystem Hamiltonians. -/
lemma hasGaussianLaw_splitU (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) :
    ProbabilityTheory.HasGaussianLaw (splitU G₁ G₂) (ℙ : Measure Ω) :=
  (ProbabilityTheory.IndepFun.hasGaussianLaw (P := (ℙ : Measure Ω)) G₁.hU G₂.hU
    hindep).map_fun (FiniteGibbs.sumEnergy (configSplit N₁ N₂))

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The composite Hamiltonian is centered. -/
lemma integral_splitU : (∫ ω, splitU G₁ G₂ ω ∂(ℙ : Measure Ω)) = 0 := by
  have hpair : Integrable (fun ω => (G₁.U ω, G₂.U ω)) (ℙ : Measure Ω) :=
    G₁.integrable.prodMk G₂.integrable
  have hcomm := (FiniteGibbs.sumEnergy (configSplit N₁ N₂)).integral_comp_comm
    (μ := (ℙ : Measure Ω)) hpair
  rw [show (fun ω => splitU G₁ G₂ ω)
      = fun ω => FiniteGibbs.sumEnergy (configSplit N₁ N₂) (G₁.U ω, G₂.U ω) from rfl, hcomm,
    GaussianDisorder.integral_prodMk_eq_zero G₁ G₂]
  exact map_zero _

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- **The covariance kernel of the non-interacting composite is the split kernel.** The joint law
of the two subsystem Hamiltonians is block diagonal, and the composite Hamiltonian pairs the Dirac
basis vector `e_σ` with the pair `(e_{σ¹}, e_{σ²})` of Dirac vectors of the two blocks. -/
lemma inner_covarianceOperator_splitU (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U)
    (σ τ : Config (N₁ + N₂)) :
    inner ℝ (ProbabilityTheory.covarianceOperator
        ((ℙ : Measure Ω).map (splitU G₁ G₂)) (std_basis (N₁ + N₂) σ)) (std_basis (N₁ + N₂) τ)
      = splitCovKernel N₁ N₂ K₁ K₂ σ τ := by
  classical
  have hg1 : ProbabilityTheory.IsGaussian ((ℙ : Measure Ω).map G₁.U) := G₁.isGaussian
  have hg2 : ProbabilityTheory.IsGaussian ((ℙ : Measure Ω).map G₂.U) := G₂.isGaussian
  have hgS : ProbabilityTheory.IsGaussian ((ℙ : Measure Ω).map (splitU G₁ G₂)) :=
    (hasGaussianLaw_splitU G₁ G₂ hindep).isGaussian_map
  have hgD : ProbabilityTheory.IsGaussian
      ((ℙ : Measure Ω).map fun ω => WithLp.toLp 2 (G₁.U ω, G₂.U ω)) :=
    ProbabilityTheory.isGaussian_map_toLp_prodMk G₁.hU G₂.hU hindep
  have hmeasD : Measurable (fun ω => WithLp.toLp 2 (G₁.U ω, G₂.U ω)) :=
    ProbabilityTheory.measurable_toLp_prodMk G₁.measU G₂.measU
  -- The Dirac vector of the composite, read on the `L²` product of the two blocks.
  set w : Config (N₁ + N₂) → WithLp 2 (EnergySpace N₁ × EnergySpace N₂) := fun ρ =>
    WithLp.toLp 2 (std_basis N₁ (configSplit N₁ N₂ ρ).1, std_basis N₂ (configSplit N₁ N₂ ρ).2)
    with hwdef
  have hpt : ∀ (ρ : Config (N₁ + N₂)) (ω : Ω),
      inner ℝ (std_basis (N₁ + N₂) ρ) (splitU G₁ G₂ ω)
        = inner ℝ (w ρ) (WithLp.toLp 2 (G₁.U ω, G₂.U ω)) := by
    intro ρ ω
    simp [hwdef, WithLp.prod_inner_apply, inner_std_basis_apply]
  rw [ProbabilityTheory.inner_covarianceOperator_map (measurable_splitU G₁ G₂)
      (std_basis (N₁ + N₂) σ) (std_basis (N₁ + N₂) τ),
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun ω => by rw [hpt σ ω, hpt τ ω]),
    ← ProbabilityTheory.inner_covarianceOperator_map hmeasD (w σ) (w τ),
    ProbabilityTheory.covarianceOperator_map_toLp_prodMk G₁.measU G₂.measU hindep
      G₁.integral_eq_zero G₂.integral_eq_zero (w σ)]
  simp [hwdef, WithLp.prod_inner_apply, splitCovKernel, G₁.cov_eq, G₂.cov_eq]

/-- **The non-interacting composite disorder.** Two independent Gaussian disorders, on the first
`N₁` and the last `N₂` sites, assembled into a centered Gaussian Hamiltonian on the composite
configuration space, with covariance kernel `splitCovKernel`. This is the `t = 0` end of the
Guerra–Toninelli splitting interpolation. Talagrand Vol. I, Theorem 1.3.9. -/
def split (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) :
    GaussianDisorder (Ω := Ω) (N := N₁ + N₂) (ℙ : Measure Ω) (splitCovKernel N₁ N₂ K₁ K₂) where
  U := splitU G₁ G₂
  measU := measurable_splitU G₁ G₂
  hU := hasGaussianLaw_splitU G₁ G₂ hindep
  mean0 := by
    have hmap : (∫ x : EnergySpace (N₁ + N₂), x ∂((ℙ : Measure Ω).map (splitU G₁ G₂)))
        = ∫ ω, splitU G₁ G₂ ω ∂(ℙ : Measure Ω) := by
      simpa using (MeasureTheory.integral_map (μ := (ℙ : Measure Ω)) (φ := splitU G₁ G₂)
        (measurable_splitU G₁ G₂).aemeasurable measurable_id.aestronglyMeasurable)
    rw [hmap, integral_splitU G₁ G₂]
  cov_eq := inner_covarianceOperator_splitU G₁ G₂ hindep

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
@[simp] lemma split_U (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) :
    (split G₁ G₂ hindep).U = splitU G₁ G₂ := rfl

end GaussianDisorder

end

end SpinGlass
