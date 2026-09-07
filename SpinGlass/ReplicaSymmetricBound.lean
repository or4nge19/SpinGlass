/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.ThermodynamicLimit

/-!
# Guerra's replica-symmetric bound, explicitly

Guerra's comparison bounds the SK free energy by that of the replica-symmetric reference model,
whose covariance kernel `N β² q R` is **additive over sites**: it is exactly the split kernel of
`SpinGlass.splitCovKernel`. Hence the reference free energy is *additive*, not merely
superadditive, so `N ↦ N p^ref_N` is linear and `p^ref_N = p^ref_1` for every `N ≥ 1`.

Together with `SpinGlass.tendsto_skFreeEnergy` this turns Guerra's bound into an explicit,
`N`-independent upper bound for the free energy in the thermodynamic limit.

## Main statements

- `SpinGlass.simple_cov_kernel_eq_splitCovKernel`: the reference kernel is its own split kernel.
- `SpinGlass.mul_refFreeEnergy_add`: `(N₁+N₂) p^ref_{N₁+N₂} = N₁ p^ref_{N₁} + N₂ p^ref_{N₂}`.
- `SpinGlass.refFreeEnergy_eq_one`: `p^ref_N = p^ref_1` for `N ≥ 1`.
-/

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology
open scoped ENNReal NNReal

namespace SpinGlass

noncomputable section

/-! ### The reference free energy -/

/-- **The replica-symmetric reference free energy** at size `N`, inverse temperature `β`, order
parameter `q` and external field `h`. -/
def refFreeEnergy (N : ℕ) (β q h : ℝ) : ℝ := gaussFreeEnergy N (refCovMatrix N β q) h

/-- **The replica-symmetric kernel is additive over sites**: on `N₁ + N₂` sites it is exactly the
split kernel of its restrictions to the two blocks. This is what makes the reference free energy
additive, and it is a direct consequence of the overlap decomposition
`N R = N₁ R₁ + N₂ R₂`. -/
theorem simple_cov_kernel_eq_splitCovKernel (N₁ N₂ : ℕ) (β q : ℝ) (σ τ : Config (N₁ + N₂)) :
    splitCovKernel N₁ N₂ (simple_cov_kernel N₁ β fun r => q * r)
        (simple_cov_kernel N₂ β fun r => q * r) σ τ
      = simple_cov_kernel (N₁ + N₂) β (fun r => q * r) σ τ := by
  simp only [splitCovKernel, simple_cov_kernel_eq]
  have hR := cast_mul_overlap_split N₁ N₂ σ τ
  push_cast at hR ⊢
  linear_combination (-(β ^ 2 * q)) * hR

/-! ### Additivity of the reference free energy -/

/-- **The reference free energy is additive.** Talagrand Vol. I, §1.3. -/
theorem mul_refFreeEnergy_add {N₁ N₂ : ℕ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (β q h : ℝ)
    (hq : 0 ≤ q) :
    ((N₁ + N₂ : ℕ) : ℝ) * refFreeEnergy (N₁ + N₂) β q h
      = (N₁ : ℝ) * refFreeEnergy N₁ β q h + (N₂ : ℝ) * refFreeEnergy N₂ β q h := by
  classical
  obtain ⟨Ω, instΩ, instP, G₁, G₂, -, h12, -⟩ :=
    exists_disorder_triple N₁ N₂ (posSemidef_refCovMatrix N₁ β q hq)
      (posSemidef_refCovMatrix N₂ β q hq) (posSemidef_refCovMatrix (N₁ + N₂) β q hq)
  set Gs := GaussianDisorder.split G₁ G₂ h12 with hGs
  have hker : ∀ σ τ, splitCovKernel N₁ N₂ (fun σ τ => refCovMatrix N₁ β q σ τ)
      (fun σ τ => refCovMatrix N₂ β q σ τ) σ τ = refCovMatrix (N₁ + N₂) β q σ τ :=
    fun σ τ => simple_cov_kernel_eq_splitCovKernel N₁ N₂ β q σ τ
  have hL : (∫ ω, free_energy_density (N := N₁ + N₂) (Gs.U ω + H_field (N₁ + N₂) h) ∂ℙ)
      = refFreeEnergy (N₁ + N₂) β q h :=
    integral_free_energy_density_eq_gaussFreeEnergy
      (posSemidef_refCovMatrix (N₁ + N₂) β q hq) hker h Gs
  have h1 : (∫ ω, free_energy_density (N := N₁) (G₁.U ω + H_field N₁ h) ∂ℙ)
      = refFreeEnergy N₁ β q h :=
    integral_free_energy_density_eq_gaussFreeEnergy
      (posSemidef_refCovMatrix N₁ β q hq) (fun _ _ => rfl) h G₁
  have h2 : (∫ ω, free_energy_density (N := N₂) (G₂.U ω + H_field N₂ h) ∂ℙ)
      = refFreeEnergy N₂ β q h :=
    integral_free_energy_density_eq_gaussFreeEnergy
      (posSemidef_refCovMatrix N₂ β q hq) (fun _ _ => rfl) h G₂
  -- The composite Hamiltonian splits, so the free energies add pointwise.
  have hpt : ∀ ω : Ω, ((N₁ + N₂ : ℕ) : ℝ) *
      free_energy_density (N := N₁ + N₂) (Gs.U ω + H_field (N₁ + N₂) h)
        = (N₁ : ℝ) * free_energy_density (N := N₁) (G₁.U ω + H_field N₁ h)
          + (N₂ : ℝ) * free_energy_density (N := N₂) (G₂.U ω + H_field N₂ h) := by
    intro ω
    have hsum : Gs.U ω + H_field (N₁ + N₂) h
        = FiniteGibbs.sumEnergy (configSplit N₁ N₂)
            (G₁.U ω + H_field N₁ h, G₂.U ω + H_field N₂ h) := by
      rw [hGs, GaussianDisorder.split_U, GaussianDisorder.splitU, H_field_eq_sumEnergy,
        ← map_add]
      rfl
    rw [hsum]
    exact mul_free_energy_density_sumEnergy hN₁ hN₂ _ _
  have hI₁ := GaussianDisorder.integrable_free_energy_density_add G₁ (H_field N₁ h)
  have hI₂ := GaussianDisorder.integrable_free_energy_density_add G₂ (H_field N₂ h)
  calc ((N₁ + N₂ : ℕ) : ℝ) * refFreeEnergy (N₁ + N₂) β q h
      = ∫ ω, ((N₁ + N₂ : ℕ) : ℝ) *
          free_energy_density (N := N₁ + N₂) (Gs.U ω + H_field (N₁ + N₂) h) ∂ℙ := by
        rw [MeasureTheory.integral_const_mul, hL]
    _ = ∫ ω, ((N₁ : ℝ) * free_energy_density (N := N₁) (G₁.U ω + H_field N₁ h)
          + (N₂ : ℝ) * free_energy_density (N := N₂) (G₂.U ω + H_field N₂ h)) ∂ℙ :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (N₁ : ℝ) * refFreeEnergy N₁ β q h + (N₂ : ℝ) * refFreeEnergy N₂ β q h := by
        rw [MeasureTheory.integral_add (hI₁.const_mul _) (hI₂.const_mul _),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, h1, h2]

/-- **The reference free energy does not depend on the system size.** Talagrand Vol. I, §1.3. -/
theorem refFreeEnergy_eq_one {N : ℕ} (hN : N ≠ 0) (β q h : ℝ) (hq : 0 ≤ q) :
    refFreeEnergy N β q h = refFreeEnergy 1 β q h := by
  have key : ∀ n : ℕ, (n : ℝ) * refFreeEnergy n β q h = (n : ℝ) * refFreeEnergy 1 β q h := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · norm_num
      · have hadd := mul_refFreeEnergy_add hm Nat.one_pos β q h hq
        push_cast at hadd ih ⊢
        rw [hadd, ih]
        ring
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have := key N
  field_simp at this
  exact this

/-! ### The one-site reference free energy in closed form

On a single site the reference Hamiltonian is `V(σ) = β√q z σ` for a standard Gaussian `z`, so the
partition function is `2 cosh(β√q z + h)` and the reference free energy is
`𝔼 log (2 cosh(β√q z + h))`. -/

/-- The one-site spin vector `σ ↦ σ₀` in `EnergySpace 1`. -/
def oneSiteSpin : EnergySpace 1 := WithLp.toLp 2 fun σ : Config 1 => isingSpin (σ 0)

@[simp] lemma oneSiteSpin_apply (σ : Config 1) : oneSiteSpin σ = isingSpin (σ 0) := rfl

@[simp] lemma overlap_one (σ τ : Config 1) :
    overlap 1 σ τ = isingSpin (σ 0) * isingSpin (τ 0) := by
  simp [overlap, overlapOf, spinOf]

@[simp] lemma magnetization_one (σ : Config 1) : magnetization 1 σ = isingSpin (σ 0) := by
  simp [magnetization, magnetizationOf, spinOf]

/-- The one-site reference Hamiltonian `V(σ) = β√q z σ` as a continuous linear map of the standard
Gaussian variable `z`. -/
def oneSiteRefCLM (β q : ℝ) : ℝ →L[ℝ] EnergySpace 1 :=
  ContinuousLinearMap.toSpanSingleton ℝ ((β * Real.sqrt q) • oneSiteSpin)

/-- The one-site reference Hamiltonian `V(σ) = β√q z σ`. -/
def oneSiteRefU (β q : ℝ) : ℝ → EnergySpace 1 := fun z => oneSiteRefCLM β q z

@[simp] lemma oneSiteRefU_apply (β q z : ℝ) (σ : Config 1) :
    oneSiteRefU β q z σ = β * Real.sqrt q * z * isingSpin (σ 0) := by
  simp [oneSiteRefU, oneSiteRefCLM, ContinuousLinearMap.toSpanSingleton_apply, oneSiteSpin]
  ring

lemma continuous_oneSiteRefU (β q : ℝ) : Continuous (oneSiteRefU β q) :=
  (oneSiteRefCLM β q).continuous

lemma measurable_oneSiteRefU (β q : ℝ) : Measurable (oneSiteRefU β q) :=
  (continuous_oneSiteRefU β q).measurable

lemma hasGaussianLaw_oneSiteRefU (β q : ℝ) :
    ProbabilityTheory.HasGaussianLaw (oneSiteRefU β q) (gaussianReal 0 1) := by
  have hid : ProbabilityTheory.HasGaussianLaw (id : ℝ → ℝ) (gaussianReal 0 1) := by
    have : ProbabilityTheory.IsGaussian ((gaussianReal 0 1).map (id : ℝ → ℝ)) := by
      rw [Measure.map_id]; infer_instance
    exact ProbabilityTheory.IsGaussian.hasGaussianLaw
  exact hid.map_fun (oneSiteRefCLM β q)

/-- `∫ z² = 1` for the standard Gaussian. -/
private lemma integral_sq_gaussianReal_one :
    (∫ z : ℝ, z ^ 2 ∂(gaussianReal 0 1)) = 1 := by
  have hvar := ProbabilityTheory.variance_id_gaussianReal (μ := 0) (v := 1)
  rw [ProbabilityTheory.variance_eq_integral (μ := gaussianReal 0 1) (X := id)
    aemeasurable_id] at hvar
  simpa using hvar

/-- **The one-site reference disorder.** `V(σ) = β√q z σ` is a centered Gaussian Hamiltonian on one
site with the replica-symmetric covariance kernel. -/
def oneSiteRefDisorder (β q : ℝ) (hq : 0 ≤ q) :
    GaussianDisorder (Ω := ℝ) 1 (gaussianReal 0 1)
      (simple_cov_kernel 1 β fun r => q * r) where
  U := oneSiteRefU β q
  measU := measurable_oneSiteRefU β q
  hU := hasGaussianLaw_oneSiteRefU β q
  mean0 := by
    have hint : Integrable (id : ℝ → ℝ) (gaussianReal 0 1) :=
      (ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)
    have hmap : (∫ x : EnergySpace 1, x ∂((gaussianReal 0 1).map (oneSiteRefU β q)))
        = ∫ z, oneSiteRefU β q z ∂(gaussianReal 0 1) := by
      simpa using (MeasureTheory.integral_map (μ := gaussianReal 0 1) (φ := oneSiteRefU β q)
        (measurable_oneSiteRefU β q).aemeasurable measurable_id.aestronglyMeasurable)
    have hcomm := (oneSiteRefCLM β q).integral_comp_comm (μ := gaussianReal 0 1) hint
    have hid : (∫ z : ℝ, id z ∂(gaussianReal 0 1)) = 0 := by
      simp [ProbabilityTheory.integral_id_gaussianReal (μ := 0) (v := 1)]
    rw [hmap]
    calc (∫ z, oneSiteRefU β q z ∂(gaussianReal 0 1))
        = ∫ z, oneSiteRefCLM β q (id z) ∂(gaussianReal 0 1) := rfl
      _ = oneSiteRefCLM β q (∫ z : ℝ, id z ∂(gaussianReal 0 1)) := hcomm
      _ = 0 := by rw [hid, map_zero]
  cov_eq := fun σ τ => by
    have : ProbabilityTheory.IsGaussian ((gaussianReal 0 1).map (oneSiteRefU β q)) :=
      (hasGaussianLaw_oneSiteRefU β q).isGaussian_map
    rw [ProbabilityTheory.inner_covarianceOperator_map (measurable_oneSiteRefU β q)]
    have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq
    have hpt : ∀ z : ℝ,
        inner ℝ (std_basis 1 σ) (oneSiteRefU β q z) * inner ℝ (std_basis 1 τ) (oneSiteRefU β q z)
          = (β ^ 2 * q * (isingSpin (σ 0) * isingSpin (τ 0))) * z ^ 2 := by
      intro z
      rw [inner_std_basis_apply, inner_std_basis_apply, oneSiteRefU_apply, oneSiteRefU_apply]
      linear_combination (β ^ 2 * z ^ 2 * (isingSpin (σ 0) * isingSpin (τ 0))) * hsq
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
      MeasureTheory.integral_const_mul, integral_sq_gaussianReal_one]
    simp only [simple_cov_kernel_eq, overlap_one, mul_one, Nat.cast_one, one_mul]
    ring

@[simp] lemma oneSiteRefDisorder_U (β q : ℝ) (hq : 0 ≤ q) :
    (oneSiteRefDisorder β q hq).U = oneSiteRefU β q := rfl

/-- The one-site partition function is `2 cosh(β√q z + h)`. -/
lemma Z_one_oneSiteRef (β q h z : ℝ) :
    Z 1 (oneSiteRefU β q z + H_field 1 h)
      = 2 * Real.cosh (β * Real.sqrt q * z + h) := by
  classical
  have hval : ∀ σ : Config 1, (oneSiteRefU β q z + H_field 1 h) σ
      = (β * Real.sqrt q * z + h) * isingSpin (σ 0) := by
    intro σ
    simp [H_field, magnetic_field_vector]
    ring
  calc Z 1 (oneSiteRefU β q z + H_field 1 h)
      = ∑ σ : Config 1, Real.exp (-((β * Real.sqrt q * z + h) * isingSpin (σ 0))) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [hval σ]
    _ = ∑ b : Bool, Real.exp (-((β * Real.sqrt q * z + h) * isingSpin b)) :=
        (Fintype.sum_equiv (Equiv.funUnique (Fin 1) Bool) _ _ fun σ => rfl)
    _ = 2 * Real.cosh (β * Real.sqrt q * z + h) := by
        rw [Fintype.sum_bool]
        simp [Real.cosh_eq]
        ring

/-- **The one-site reference free energy in closed form**:
`p^ref_1 = 𝔼 log (2 cosh(β√q z + h))`, `z` a standard Gaussian. Talagrand Vol. I, §1.3,
Eq. (1.73). -/
theorem refFreeEnergy_one_eq (β q h : ℝ) (hq : 0 ≤ q) :
    refFreeEnergy 1 β q h
      = ∫ z : ℝ, Real.log (2 * Real.cosh (β * Real.sqrt q * z + h)) ∂(gaussianReal 0 1) := by
  have hcomp := integral_free_energy_density_eq_gaussFreeEnergy
    (P := gaussianReal 0 1) (posSemidef_refCovMatrix 1 β q hq) (fun _ _ => rfl) h
    (oneSiteRefDisorder β q hq)
  have hrf : refFreeEnergy 1 β q h
      = ∫ ω : ℝ, free_energy_density (N := 1)
          ((oneSiteRefDisorder β q hq).U ω + H_field 1 h) ∂(gaussianReal 0 1) := hcomp.symm
  rw [hrf]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [free_energy_density, oneSiteRefDisorder_U]
  rw [Z_one_oneSiteRef]
  norm_num

/-! ### Guerra's bound at every system size, and in the limit -/

/-- **Guerra's replica-symmetric bound in terms of the reference free energy.** -/
theorem skFreeEnergy_le_refFreeEnergy {N : ℕ} (hN : 0 < N) (β q h : ℝ) (hq : 0 ≤ q) :
    skFreeEnergy N β h ≤ refFreeEnergy N β q h + β ^ 2 / 4 * (1 - q) ^ 2 := by
  classical
  obtain ⟨Ω, instΩ, instP, sk, sim, hindep⟩ :=
    exists_skDisorder_simpleDisorder_indepFun N β q hq
  have hle := integral_free_energy_density_le_rs (Ω := Ω) h hN sk sim hindep
  rw [integral_free_energy_density_eq_skFreeEnergy h sk,
    integral_free_energy_density_eq_gaussFreeEnergy
      (posSemidef_refCovMatrix N β q hq) (fun _ _ => rfl) h sim] at hle
  exact hle

/-- **Guerra's replica-symmetric bound in the thermodynamic limit.** For every order parameter
`q ≥ 0`, the limiting SK free energy is at most the (size-independent) replica-symmetric reference
free energy plus `(β²/4)(1-q)²`. Talagrand Vol. I, Theorem 1.3.7 combined with Theorem 1.3.9. -/
theorem skFreeEnergyLimit_le (β q h : ℝ) (hq : 0 ≤ q) :
    skFreeEnergyLimit β h ≤ refFreeEnergy 1 β q h + β ^ 2 / 4 * (1 - q) ^ 2 := by
  refine le_of_tendsto (tendsto_skFreeEnergy β h) ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with N hN
  calc skFreeEnergy N β h ≤ refFreeEnergy N β q h + β ^ 2 / 4 * (1 - q) ^ 2 :=
        skFreeEnergy_le_refFreeEnergy hN β q h hq
    _ = refFreeEnergy 1 β q h + β ^ 2 / 4 * (1 - q) ^ 2 := by
        rw [refFreeEnergy_eq_one hN.ne' β q h hq]

/-- **Guerra's replica-symmetric bound, in closed form, at every system size.** For every order
parameter `q ≥ 0`,
`p_N(β,h) ≤ 𝔼 log (2 cosh(β√q z + h)) + (β²/4)(1-q)²`, `z` a standard Gaussian.
Talagrand Vol. I, §1.3, Theorem 1.3.7 and Eq. (1.73). -/
theorem skFreeEnergy_le_rs {N : ℕ} (hN : 0 < N) (β q h : ℝ) (hq : 0 ≤ q) :
    skFreeEnergy N β h
      ≤ (∫ z : ℝ, Real.log (2 * Real.cosh (β * Real.sqrt q * z + h)) ∂(gaussianReal 0 1))
        + β ^ 2 / 4 * (1 - q) ^ 2 := by
  rw [← refFreeEnergy_one_eq β q h hq, ← refFreeEnergy_eq_one hN.ne' β q h hq]
  exact skFreeEnergy_le_refFreeEnergy hN β q h hq

/-- **Guerra's replica-symmetric bound in the thermodynamic limit, in closed form.** For every
order parameter `q ≥ 0`,
`p(β,h) ≤ 𝔼 log (2 cosh(β√q z + h)) + (β²/4)(1-q)²`, `z` a standard Gaussian.
This is the replica-symmetric upper bound for the Sherrington–Kirkpatrick free energy.
Talagrand Vol. I, §1.3, Theorem 1.3.7 combined with Theorem 1.3.9. -/
theorem skFreeEnergyLimit_le_rs (β q h : ℝ) (hq : 0 ≤ q) :
    skFreeEnergyLimit β h
      ≤ (∫ z : ℝ, Real.log (2 * Real.cosh (β * Real.sqrt q * z + h)) ∂(gaussianReal 0 1))
        + β ^ 2 / 4 * (1 - q) ^ 2 := by
  rw [← refFreeEnergy_one_eq β q h hq]
  exact skFreeEnergyLimit_le β q h hq

end

end SpinGlass
