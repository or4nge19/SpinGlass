/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.MixedPSpinLimit
import Mathlib.Analysis.Convex.Integral

/-!
# The free energy under an independent Gaussian perturbation

Talagrand, Vol. II, Lemma 12.2.1: adding to a Gaussian Hamiltonian an *independent* centered
Gaussian perturbation whose variance per configuration is at most `D` raises the mean free energy
per site by at least `0` and at most `D/(2N)`. The lower bound is Jensen's inequality for the convex
free energy; the upper bound is Jensen's inequality for the logarithm together with the Gaussian
exponential moment `𝔼 exp(−V(σ)) = exp(Var V(σ)/2)`.

In the law-level formulation the statement is about `gaussFreeEnergy N S h` and
`gaussFreeEnergy N (S + T) h`: the covariance of the sum of independent fields is the sum of the
covariances (`ProbabilityTheory.multivariateGaussian_map_add_prod`).

## Main statements

- `SpinGlass.integral_exp_mul_apply_gaussField`: `𝔼 exp(t H(σ)) = exp(T σ σ t²/2)` for the field
  with covariance `T`.
- `SpinGlass.integral_free_energy_density_add_le`, `le_integral_free_energy_density_add`: the two
  bounds at a fixed first Hamiltonian.
- `SpinGlass.gaussFreeEnergy_le_gaussFreeEnergy_add`,
  `SpinGlass.gaussFreeEnergy_add_le`: **Lemma 12.2.1**,
  `gaussFreeEnergy N S h ≤ gaussFreeEnergy N (S+T) h ≤ gaussFreeEnergy N S h + D/(2N)`.
- `SpinGlass.abs_gaussFreeEnergy_perturbedProfile_sub_le`: for a mixed `p`-spin model perturbed by
  the monomial components with weights `w`, the free energy moves by at most `(∑ₛ wₛ²)/2`.
-/

open MeasureTheory ProbabilityTheory Filter Topology BigOperators
open scoped InnerProductSpace

namespace SpinGlass

noncomputable section

variable {N : ℕ}

/-! ### Exponential moments of the coordinates of a Gaussian field -/

/-- **The exponential moment of a coordinate of the Gaussian field**:
`𝔼 exp(t H(σ)) = exp(T σ σ t²/2)`. -/
theorem integral_exp_mul_apply_gaussField {T : Matrix (Config N) (Config N) ℝ}
    (hT : T.PosSemidef) (σ : Config N) (t : ℝ) :
    (∫ v : EnergySpace N, Real.exp (t * v σ) ∂(gaussField N T))
      = Real.exp (T σ σ * t ^ 2 / 2) := by
  classical
  set μ : Measure (EnergySpace N) := gaussField N T with hμ
  set L : StrongDual ℝ (EnergySpace N) := EuclideanSpace.proj σ with hL
  have hLapply : ∀ v : EnergySpace N, L v = v σ := fun v => rfl
  have hmean : μ[L] = 0 := by
    have h := L.integral_comp_comm (μ := μ) (φ := id) ProbabilityTheory.IsGaussian.integrable_id
    simp only [id] at h
    rw [show (fun x : EnergySpace N => L x) = ⇑L from rfl] at h
    rw [h, show (∫ x : EnergySpace N, x ∂μ) = 0 from integral_id_gaussField N T, map_zero]
  have hmem : MemLp (id : EnergySpace N → EnergySpace N) 2 μ :=
    ProbabilityTheory.IsGaussian.memLp_two_id
  have hvar : Var[L; μ] = T σ σ := by
    have h1 : Var[L; μ]
        = Var[fun u : EnergySpace N => ⟪EuclideanSpace.single σ (1 : ℝ), u⟫_ℝ; μ] := by
      congr 1
      funext u
      rw [hLapply, EuclideanSpace.inner_single_left]
      simp
    rw [h1, ← covarianceBilin_self hmem, hμ, gaussField, covarianceBilin_multivariateGaussian hT]
    simp
  have hnn : 0 ≤ T σ σ := hvar ▸ variance_nonneg L μ
  have hmap : μ.map L = gaussianReal 0 (T σ σ).toNNReal := by
    rw [IsGaussian.map_eq_gaussianReal L, hmean, hvar]
  have hmgf := mgf_gaussianReal hmap t
  rw [Real.coe_toNNReal _ hnn, zero_mul, zero_add] at hmgf
  rw [← hmgf, mgf]
  rfl

/-- The coordinates of a Gaussian field have integrable exponential moments. -/
theorem integrable_exp_mul_apply_gaussField (T : Matrix (Config N) (Config N) ℝ)
    (σ : Config N) (t : ℝ) :
    Integrable (fun v : EnergySpace N => Real.exp (t * v σ)) (gaussField N T) := by
  classical
  set μ : Measure (EnergySpace N) := gaussField N T with hμ
  set L : StrongDual ℝ (EnergySpace N) := EuclideanSpace.proj σ with hL
  have hmean : μ[L] = 0 := by
    have h := L.integral_comp_comm (μ := μ) (φ := id) ProbabilityTheory.IsGaussian.integrable_id
    simp only [id] at h
    rw [show (fun x : EnergySpace N => L x) = ⇑L from rfl] at h
    rw [h, show (∫ x : EnergySpace N, x ∂μ) = 0 from integral_id_gaussField N T, map_zero]
  have hmap : μ.map L = gaussianReal 0 (Var[L; μ]).toNNReal := by
    rw [IsGaussian.map_eq_gaussianReal L, hmean]
  have h := integrable_exp_mul_gaussianReal (μ := 0) (v := (Var[L; μ]).toNNReal) t
  rw [← hmap] at h
  exact (integrable_map_measure h.aestronglyMeasurable L.continuous.measurable.aemeasurable).1 h

/-! ### The two bounds at a fixed first Hamiltonian -/

/-- Integrability of the perturbed free energy. -/
lemma integrable_free_energy_density_add_gaussField (T : Matrix (Config N) (Config N) ℝ)
    (u : EnergySpace N) :
    Integrable (fun v : EnergySpace N => free_energy_density (N := N) (u + v))
      (gaussField N T) := by
  refine FiniteGibbs.integrable_free_energy_density_of_integrable_norm (α := Config N)
    (gaussField N T) N (measurable_const.add measurable_id) ?_
  refine Integrable.mono' ((integrable_const ‖u‖).add (integrable_norm_gaussField N T))
    (measurable_const.add measurable_id).norm.aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact norm_add_le _ _

/-- **The lower bound** (Jensen for the convex free energy): adding an independent centered Gaussian
perturbation cannot lower the mean free energy. -/
theorem le_integral_free_energy_density_add (T : Matrix (Config N) (Config N) ℝ)
    (u : EnergySpace N) :
    free_energy_density (N := N) u
      ≤ ∫ v : EnergySpace N, free_energy_density (N := N) (u + v) ∂(gaussField N T) := by
  have hconv := FiniteGibbs.convexOn_free_energy_density (α := Config N) N
  have hint : Integrable (fun v : EnergySpace N => u + v) (gaussField N T) :=
    (integrable_const u).add ProbabilityTheory.IsGaussian.integrable_id
  have hmean : (∫ v : EnergySpace N, u + v ∂(gaussField N T)) = u := by
    have h := integral_add (μ := gaussField N T) (f := fun _ => u) (g := fun v => v)
      (integrable_const u) ProbabilityTheory.IsGaussian.integrable_id
    rw [h, integral_const, integral_id_gaussField, add_zero, probReal_univ, one_smul]
  have h := ConvexOn.map_integral_le hconv (μ := gaussField N T) (f := fun v => u + v)
    (FiniteGibbs.contDiff_free_energy_density (α := Config N) N).continuous.continuousOn
    isClosed_univ (Eventually.of_forall fun _ => Set.mem_univ _) hint
    (integrable_free_energy_density_add_gaussField T u)
  rwa [hmean] at h

/-- **The upper bound** (Jensen for the logarithm and the Gaussian exponential moment): a
perturbation of variance at most `D` per configuration raises the mean free energy by at most
`D/(2N)`. -/
theorem integral_free_energy_density_add_le (hN : N ≠ 0) {T : Matrix (Config N) (Config N) ℝ}
    (hT : T.PosSemidef) {D : ℝ} (hD : ∀ σ, T σ σ ≤ D) (u : EnergySpace N) :
    (∫ v : EnergySpace N, free_energy_density (N := N) (u + v) ∂(gaussField N T))
      ≤ free_energy_density (N := N) u + D / (2 * (N : ℝ)) := by
  classical
  set μ : Measure (EnergySpace N) := gaussField N T with hμ
  -- the partition function of the perturbed Hamiltonian, and its mean
  have hZ : ∀ v : EnergySpace N, FiniteGibbs.Z (α := Config N) (u + v)
      = ∑ σ : Config N, Real.exp (-u σ) * Real.exp ((-1) * v σ) := by
    intro v
    unfold FiniteGibbs.Z
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← Real.exp_add]
    congr 1
    simp only [PiLp.add_apply]
    ring
  have hZint : Integrable (fun v : EnergySpace N => FiniteGibbs.Z (α := Config N) (u + v)) μ := by
    simp only [hZ]
    exact integrable_finsetSum _ fun σ _ =>
      (integrable_exp_mul_apply_gaussField T σ (-1)).const_mul _
  have hZmean : (∫ v : EnergySpace N, FiniteGibbs.Z (α := Config N) (u + v) ∂μ)
      ≤ Real.exp (D / 2) * FiniteGibbs.Z (α := Config N) u := by
    simp only [hZ]
    rw [integral_finsetSum _ fun σ _ => (integrable_exp_mul_apply_gaussField T σ (-1)).const_mul _]
    unfold FiniteGibbs.Z
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun σ _ => ?_
    rw [integral_const_mul, integral_exp_mul_apply_gaussField hT σ (-1)]
    have : T σ σ * (-1 : ℝ) ^ 2 / 2 ≤ D / 2 := by nlinarith [hD σ]
    calc Real.exp (-u σ) * Real.exp (T σ σ * (-1) ^ 2 / 2)
        ≤ Real.exp (-u σ) * Real.exp (D / 2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 this) (Real.exp_pos _).le
      _ = Real.exp (D / 2) * Real.exp (-u σ) := mul_comm _ _
  have hZmean_pos : 0 < ∫ v : EnergySpace N, FiniteGibbs.Z (α := Config N) (u + v) ∂μ := by
    refine integral_pos_iff_support_of_nonneg (fun v => (FiniteGibbs.Z_pos _).le) hZint |>.2 ?_
    have : Function.support (fun v : EnergySpace N => FiniteGibbs.Z (α := Config N) (u + v))
        = Set.univ := Set.eq_univ_of_forall fun v => (FiniteGibbs.Z_pos _).ne'
    rw [this, measure_univ]
    exact one_pos
  set I : ℝ := ∫ v : EnergySpace N, FiniteGibbs.Z (α := Config N) (u + v) ∂μ with hI
  -- Jensen for the logarithm via the tangent line at `I`
  have hlog : ∀ v : EnergySpace N, Real.log (FiniteGibbs.Z (α := Config N) (u + v))
      ≤ FiniteGibbs.Z (α := Config N) (u + v) / I - 1 + Real.log I := by
    intro v
    have hpos := FiniteGibbs.Z_pos (α := Config N) (u + v)
    have h1 := Real.log_le_sub_one_of_pos (div_pos hpos hZmean_pos)
    rw [Real.log_div hpos.ne' hZmean_pos.ne'] at h1
    linarith
  have hlogint : Integrable (fun v : EnergySpace N =>
      Real.log (FiniteGibbs.Z (α := Config N) (u + v))) μ := by
    have h := (integrable_free_energy_density_add_gaussField T u).const_mul (N : ℝ)
    have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    refine h.congr (Eventually.of_forall fun v => ?_)
    simp only [free_energy_density]
    field_simp
    rfl
  have hint_le : (∫ v : EnergySpace N, Real.log (FiniteGibbs.Z (α := Config N) (u + v)) ∂μ)
      ≤ Real.log I := by
    have hf2 : Integrable (fun v : EnergySpace N => FiniteGibbs.Z (α := Config N) (u + v) / I) μ :=
      hZint.div_const I
    have hf1 : Integrable
        (fun v : EnergySpace N => FiniteGibbs.Z (α := Config N) (u + v) / I - 1) μ :=
      hf2.sub (integrable_const 1)
    have hf3 : Integrable
        (fun v : EnergySpace N => FiniteGibbs.Z (α := Config N) (u + v) / I - 1 + Real.log I) μ :=
      hf1.add (integrable_const (Real.log I))
    have h := integral_mono hlogint hf3 hlog
    have hII : (∫ v : EnergySpace N, FiniteGibbs.Z (α := Config N) (u + v) ∂μ) / I = 1 :=
      div_self hZmean_pos.ne'
    rw [integral_add hf1 (integrable_const _), integral_sub hf2 (integrable_const 1), integral_div,
      hII, integral_const, integral_const, probReal_univ, one_smul, one_smul] at h
    linarith
  have hlogI : Real.log I ≤ D / 2 + Real.log (FiniteGibbs.Z (α := Config N) u) := by
    have := Real.log_le_log hZmean_pos hZmean
    rwa [Real.log_mul (Real.exp_pos _).ne' (FiniteGibbs.Z_pos _).ne', Real.log_exp] at this
  -- divide by `N`
  simp only [free_energy_density]
  rw [integral_const_mul]
  have hNnn : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  calc (1 / (N : ℝ)) * ∫ v : EnergySpace N, Real.log (FiniteGibbs.Z (α := Config N) (u + v)) ∂μ
      ≤ (1 / (N : ℝ)) * (D / 2 + Real.log (FiniteGibbs.Z (α := Config N) u)) :=
        mul_le_mul_of_nonneg_left (hint_le.trans hlogI) hNnn
    _ = (1 / (N : ℝ)) * Real.log (FiniteGibbs.Z (α := Config N) u) + D / (2 * (N : ℝ)) := by
        ring

/-! ### Lemma 12.2.1: the free energy under an independent Gaussian perturbation -/

section Assembly

variable {S T : Matrix (Config N) (Config N) ℝ}

lemma integrable_free_energy_density_shift (S : Matrix (Config N) (Config N) ℝ) (h : ℝ) :
    Integrable (fun u : EnergySpace N => free_energy_density (N := N) (u + H_field N h))
      (gaussField N S) := by
  refine FiniteGibbs.integrable_free_energy_density_of_integrable_norm (α := Config N)
    (gaussField N S) N (measurable_id.add measurable_const) ?_
  refine Integrable.mono' ((integrable_norm_gaussField N S).add (integrable_const ‖H_field N h‖))
    (measurable_id.add measurable_const).norm.aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact norm_add_le _ _

/-- The free energy of the sum of two independent fields as a double integral. -/
lemma gaussFreeEnergy_add_eq_integral_integral (hS : S.PosSemidef) (hT : T.PosSemidef) (h : ℝ) :
    gaussFreeEnergy N (S + T) h
      = ∫ u : EnergySpace N, ∫ v : EnergySpace N,
          free_energy_density (N := N) ((u + H_field N h) + v) ∂(gaussField N T)
            ∂(gaussField N S) := by
  have hmap := multivariateGaussian_map_add_prod (ι := Config N) hS hT
  have hadd : Measurable fun p : EnergySpace N × EnergySpace N => p.1 + p.2 := by fun_prop
  have hcont : Continuous fun w : EnergySpace N => free_energy_density (N := N) (w + H_field N h) :=
    (FiniteGibbs.contDiff_free_energy_density (α := Config N) N).continuous.comp
      (continuous_id.add continuous_const)
  have hintST : Integrable (fun w : EnergySpace N => free_energy_density (N := N) (w + H_field N h))
      (multivariateGaussian (0 : EnergySpace N) (S + T)) :=
    integrable_free_energy_density_shift (S + T) h
  rw [← hmap] at hintST
  have hint : Integrable (fun p : EnergySpace N × EnergySpace N =>
      free_energy_density (N := N) (p.1 + p.2 + H_field N h))
      ((gaussField N S).prod (gaussField N T)) :=
    (integrable_map_measure hcont.aestronglyMeasurable hadd.aemeasurable).1 hintST
  have hfun : (fun p : EnergySpace N × EnergySpace N =>
      free_energy_density (N := N) (p.1 + p.2 + H_field N h))
      = fun p => free_energy_density (N := N) ((p.1 + H_field N h) + p.2) := by
    funext p
    congr 1
    abel
  unfold gaussFreeEnergy
  rw [← hmap, integral_map hadd.aemeasurable hcont.aestronglyMeasurable]
  rw [hfun] at hint ⊢
  exact integral_prod _ hint

/-- Joint integrability of the perturbed free energy over the pair of fields. -/
lemma integrable_free_energy_density_add_prod (hS : S.PosSemidef) (hT : T.PosSemidef) (h : ℝ) :
    Integrable (fun p : EnergySpace N × EnergySpace N =>
        free_energy_density (N := N) ((p.1 + H_field N h) + p.2))
      ((gaussField N S).prod (gaussField N T)) := by
  have hmap := multivariateGaussian_map_add_prod (ι := Config N) hS hT
  have hadd : Measurable fun p : EnergySpace N × EnergySpace N => p.1 + p.2 := by fun_prop
  have hcont : Continuous fun w : EnergySpace N => free_energy_density (N := N) (w + H_field N h) :=
    (FiniteGibbs.contDiff_free_energy_density (α := Config N) N).continuous.comp
      (continuous_id.add continuous_const)
  have hintST : Integrable (fun w : EnergySpace N => free_energy_density (N := N) (w + H_field N h))
      (multivariateGaussian (0 : EnergySpace N) (S + T)) :=
    integrable_free_energy_density_shift (S + T) h
  rw [← hmap] at hintST
  have hint : Integrable (fun p : EnergySpace N × EnergySpace N =>
      free_energy_density (N := N) (p.1 + p.2 + H_field N h))
      ((gaussField N S).prod (gaussField N T)) :=
    (integrable_map_measure hcont.aestronglyMeasurable hadd.aemeasurable).1 hintST
  have hfun : (fun p : EnergySpace N × EnergySpace N =>
      free_energy_density (N := N) (p.1 + p.2 + H_field N h))
      = fun p => free_energy_density (N := N) ((p.1 + H_field N h) + p.2) := by
    funext p
    congr 1
    abel
  rw [hfun] at hint
  exact hint

/-- **Lemma 12.2.1, lower bound**: an independent Gaussian perturbation cannot lower the free
energy. -/
theorem gaussFreeEnergy_le_gaussFreeEnergy_add (hS : S.PosSemidef) (hT : T.PosSemidef) (h : ℝ) :
    gaussFreeEnergy N S h ≤ gaussFreeEnergy N (S + T) h := by
  rw [gaussFreeEnergy_add_eq_integral_integral hS hT h]
  have hout := (integrable_free_energy_density_add_prod hS hT h).integral_prod_left
  exact integral_mono (integrable_free_energy_density_shift S h) hout
    fun u => le_integral_free_energy_density_add T (u + H_field N h)

/-- **Lemma 12.2.1, upper bound**: an independent Gaussian perturbation of variance at most `D`
per configuration raises the free energy per site by at most `D/(2N)`. Talagrand, Vol. II,
Lemma 12.2.1. -/
theorem gaussFreeEnergy_add_le (hN : N ≠ 0) (hS : S.PosSemidef) (hT : T.PosSemidef) {D : ℝ}
    (hD : ∀ σ, T σ σ ≤ D) (h : ℝ) :
    gaussFreeEnergy N (S + T) h ≤ gaussFreeEnergy N S h + D / (2 * (N : ℝ)) := by
  rw [gaussFreeEnergy_add_eq_integral_integral hS hT h]
  have hout := (integrable_free_energy_density_add_prod hS hT h).integral_prod_left
  have hf : Integrable (fun u : EnergySpace N =>
      free_energy_density (N := N) (u + H_field N h) + D / (2 * (N : ℝ))) (gaussField N S) :=
    (integrable_free_energy_density_shift S h).add (integrable_const _)
  have hmono := integral_mono hout hf
    fun u => integral_free_energy_density_add_le hN hT hD (u + H_field N h)
  rw [integral_add (integrable_free_energy_density_shift S h) (integrable_const _), integral_const,
    probReal_univ, one_smul] at hmono
  exact hmono

end Assembly

/-! ### Mixed `p`-spin models: the perturbation moves the free energy by at most `∑ wₛ²/2` -/

section MixedPSpin

variable {m : ℕ}

/-- The perturbed profile splits the kernel into the model's and the perturbation's. -/
lemma overlapCovMatrix_perturbedProfile (ξ : ℝ → ℝ) (w : Fin (m + 1) → ℝ) :
    overlapCovMatrix N (perturbedProfile ξ w)
      = overlapCovMatrix N ξ
        + overlapCovMatrix N (fun r => ∑ s : Fin (m + 1), (w s) ^ 2 * r ^ ((s : ℕ) + 1)) := by
  ext σ τ
  simp [overlapCovMatrix_apply, perturbedProfile, mul_add]

/-- The perturbation kernel is a nonnegative combination of monomial kernels. -/
lemma overlapCovMatrix_monomialSum (w : Fin (m + 1) → ℝ) :
    overlapCovMatrix N (fun r => ∑ s : Fin (m + 1), (w s) ^ 2 * r ^ ((s : ℕ) + 1))
      = ∑ s : Fin (m + 1), (w s) ^ 2 • overlapCovMatrix N (fun r => r ^ ((s : ℕ) + 1)) := by
  ext σ τ
  simp only [overlapCovMatrix_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

lemma posSemidef_overlapCovMatrix_monomialSum (w : Fin (m + 1) → ℝ) :
    (overlapCovMatrix N
      (fun r => ∑ s : Fin (m + 1), (w s) ^ 2 * r ^ ((s : ℕ) + 1))).PosSemidef := by
  rw [overlapCovMatrix_monomialSum]
  exact Finset.sum_induction _ Matrix.PosSemidef (fun _ _ ha hb => ha.add hb)
    Matrix.PosSemidef.zero fun s _ => (posSemidef_overlapCovMatrix_pow _).smul_sq (w s)

/-- **The perturbation moves the free energy by at most half its variance per site**: for a mixed
`p`-spin model perturbed by the monomial components with weights `w`,
`|p_N(perturbed) − p_N| ≤ (∑ₛ wₛ²)/2`. Talagrand, Vol. II, Lemma 12.2.1. -/
theorem abs_gaussFreeEnergy_perturbedProfile_sub_le (hN : N ≠ 0) {P : Polynomial ℝ}
    (hP : ∀ k, 0 ≤ P.coeff k) (w : Fin (m + 1) → ℝ) (h : ℝ) :
    |gaussFreeEnergy N (overlapCovMatrix N (perturbedProfile (fun r => P.eval r) w)) h
        - gaussFreeEnergy N (overlapCovMatrix N fun r => P.eval r) h|
      ≤ (∑ s : Fin (m + 1), (w s) ^ 2) / 2 := by
  rw [overlapCovMatrix_perturbedProfile]
  have hS := posSemidef_overlapCovMatrix_of_polynomial N hP
  have hT := posSemidef_overlapCovMatrix_monomialSum (N := N) w
  have hD : ∀ σ : Config N,
      overlapCovMatrix N (fun r => ∑ s : Fin (m + 1), (w s) ^ 2 * r ^ ((s : ℕ) + 1)) σ σ
        ≤ (N : ℝ) * ∑ s : Fin (m + 1), (w s) ^ 2 := by
    intro σ
    rw [overlapCovMatrix_diag]
    simp
  have h1 := gaussFreeEnergy_le_gaussFreeEnergy_add hS hT h
  have h2 := gaussFreeEnergy_add_le hN hS hT hD h
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hdiv : ((N : ℝ) * ∑ s : Fin (m + 1), (w s) ^ 2) / (2 * (N : ℝ))
      = (∑ s : Fin (m + 1), (w s) ^ 2) / 2 := by
    field_simp
  rw [hdiv] at h2
  rw [abs_le]
  constructor <;> linarith [Finset.sum_nonneg fun s (_ : s ∈ Finset.univ) => sq_nonneg (w s)]

end MixedPSpin

end

end SpinGlass
