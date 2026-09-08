/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.GaussFieldFluctuation
import Common.Mathlib.Algebra.Polynomial.EvalBound
import Common.Mathlib.Probability.Distributions.Gaussian.MultivariateSum

/-!
# Mixed `p`-spin models

Talagrand's realizability criterion (Vol. II, Eq. (14.57)) says that an overlap-driven kernel
`c(σ, τ) = N ξ(R_{στ})` is the covariance of a centered Gaussian Hamiltonian as soon as `ξ` is a
power series with nonnegative coefficients — the **mixed `p`-spin** models. This file records that
family as an instance of the three hypotheses under which
`SpinGlass.GaussFieldFluctuation` proves the whole of Vol. II, §12.1–12.2:

* positive semidefiniteness, from `SpinGlass.posSemidef_overlapPolyMatrix`;
* constant diagonal `D = N ξ(1)`, because `R_{σσ} = 1`;
* `|c(σ,τ)| ≤ D`, because `|ξ(r)| ≤ ξ(1)` for `|r| ≤ 1`
  (`Polynomial.abs_eval_le_eval_one_of_nonneg_coeff`).

Every capstone of the self-averaging theory therefore holds for every mixed `p`-spin model, with
`D/N = ξ(1)` in place of the SK value `1/2`. The Sherrington–Kirkpatrick model is `ξ(r) = r²/2`.

## Main statements

- `SpinGlass.overlapCovMatrix`, `overlapCovMatrix_diag`, `abs_overlapCovMatrix_le`,
  `posSemidef_overlapCovMatrix_of_polynomial` — the model and its three properties.
- `SpinGlass.deriv_mixedPSpinFreeEnergy_eq` — **Talagrand Vol. I, Lemma 1.3.11 for a mixed
  `p`-spin model**: `∂p_N/∂β = β(ξ(1) - 𝔼⟨ξ(R₁₂)⟩)`.
- `SpinGlass.abs_deriv_mixedPSpinFreeEnergy_le` — `|∂p_N/∂β| ≤ 2βξ(1)`, uniform in the volume.
- `SpinGlass.variance_mixedPSpinFreeEnergy_le` — `Var[p_N^ω(β)] ≤ β²ξ(1)/N`.
- `SpinGlass.intervalIntegral_mixedPSpinTotalEnergy_fluctuation_le` — **Theorem 12.1.1**.
- `SpinGlass.exists_beta_abs_mixedPSpinGhirlandaGuerra_error_le` — **the Ghirlanda–Guerra
  identities up to `O(N^{-1/4})`.**
-/

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology Set

namespace SpinGlass

noncomputable section

variable {N : ℕ}

/-! ### The overlap-driven covariance matrix -/

/-- The overlap-driven covariance matrix `N ξ(R_{στ})` of a mean-field spin glass. -/
def overlapCovMatrix (N : ℕ) (ξ : ℝ → ℝ) : Matrix (Config N) (Config N) ℝ :=
  Matrix.of fun σ τ => overlapCovKernel (N := N) ξ σ τ

@[simp] lemma overlapCovMatrix_apply (N : ℕ) (ξ : ℝ → ℝ) (σ τ : Config N) :
    overlapCovMatrix N ξ σ τ = (N : ℝ) * ξ (overlap N σ τ) := rfl

/-- **The diagonal of an overlap-driven kernel is the constant `N ξ(1)`**, because the self-overlap
is `1`. -/
lemma overlapCovMatrix_diag (N : ℕ) (ξ : ℝ → ℝ) (σ : Config N) :
    overlapCovMatrix N ξ σ σ = (N : ℝ) * ξ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · rw [overlapCovMatrix_apply, SpinGlass.overlap_self (N := N) hN]

/-- **An overlap-driven kernel is bounded by its diagonal** as soon as its profile is: the overlap
lies in `[-1,1]`. -/
lemma abs_overlapCovMatrix_le (N : ℕ) {ξ : ℝ → ℝ}
    (hξ : ∀ r : ℝ, |r| ≤ 1 → |ξ r| ≤ ξ 1) (σ τ : Config N) :
    |overlapCovMatrix N ξ σ τ| ≤ (N : ℝ) * ξ 1 := by
  have hξ1 : 0 ≤ ξ 1 := le_trans (abs_nonneg _) (hξ 1 (by simp))
  rw [overlapCovMatrix_apply, abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
  exact mul_le_mul_of_nonneg_left (hξ _ (abs_overlap_le_one N σ τ)) (Nat.cast_nonneg N)

/-- **Talagrand's realizability criterion, Vol. II, Eq. (14.57).** An overlap-driven kernel with a
nonnegative-coefficient polynomial profile is a covariance. -/
theorem posSemidef_overlapCovMatrix_of_polynomial (N : ℕ) {P : Polynomial ℝ}
    (hP : ∀ n, 0 ≤ P.coeff n) :
    (overlapCovMatrix N (fun r => P.eval r)).PosSemidef := by
  classical
  have hEq : overlapCovMatrix N (fun r => P.eval r)
      = Matrix.of fun σ τ : Config N =>
          (N : ℝ) * ∑ p ∈ Finset.range (P.natDegree + 1),
            P.coeff p * (overlap N σ τ) ^ p := by
    ext σ τ
    rw [overlapCovMatrix_apply, Matrix.of_apply, Polynomial.eval_eq_sum_range]
  rw [hEq]
  exact posSemidef_overlapPolyMatrix N P.coeff hP (Finset.range (P.natDegree + 1))

/-- The profile of a nonnegative-coefficient polynomial is bounded by its value at `1` on the
overlap range. -/
lemma abs_polynomial_profile_le {P : Polynomial ℝ} (hP : ∀ n, 0 ≤ P.coeff n) :
    ∀ r : ℝ, |r| ≤ 1 → |P.eval r| ≤ P.eval 1 :=
  fun _ hr => Polynomial.abs_eval_le_eval_one_of_nonneg_coeff hP hr

/-! ### Arithmetic of the mixed `p`-spin scale `D = N ξ(1)` -/

/-- `√(N c)/N = √c/√N`: the shape every `O(N^{-1/2})` constant takes once `D = N ξ(1)`. -/
lemma sqrt_natCast_mul_div_self (N : ℕ) (hN : N ≠ 0) (c : ℝ) :
    Real.sqrt ((N : ℝ) * c) / (N : ℝ) = Real.sqrt c / Real.sqrt (N : ℝ) := by
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hs : (0 : ℝ) < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNR
  rw [div_eq_div_iff hNR.ne' hs.ne', Real.sqrt_mul (Nat.cast_nonneg N),
    show Real.sqrt (N : ℝ) * Real.sqrt c * Real.sqrt (N : ℝ)
      = Real.sqrt c * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) from by ring,
    Real.mul_self_sqrt hNR.le]

/-! ### The capstones of Vol. I, §1.3 and Vol. II, §12.1 for a mixed `p`-spin model

`S = overlapCovMatrix N ξ` with `ξ` a nonnegative-coefficient polynomial satisfies the three
hypotheses of `SpinGlass.GaussFieldFluctuation` with `D = N ξ(1)`, so `D/N = ξ(1)` is a constant:
every bound below is uniform in the volume, and the fluctuation bounds vanish. -/

variable {P : Polynomial ℝ}

/-- **Talagrand, Vol. I, Lemma 1.3.11, for a mixed `p`-spin model.** The derivative of the mean
free energy in the disorder strength is `β (ξ(1) - 𝔼⟨ξ(R_{1,2})⟩)`. For the SK model
`ξ(r) = r²/2` this is `(β/2)(1 - 𝔼⟨R²_{1,2}⟩)`. -/
theorem deriv_mixedPSpinFreeEnergy_eq (hP : ∀ n, 0 ≤ P.coeff n) (hN : N ≠ 0) (h β : ℝ) :
    deriv (fun b => gaussFreeEnergy N ((b ^ 2) • overlapCovMatrix N (fun r => P.eval r)) h) β
      = β * (P.eval 1 - ∫ H : EnergySpace N,
          gibbs_average₂ (N := N) (H_field N h + β • H)
            (fun σ τ => P.eval (overlap N σ τ))
          ∂(gaussField N (overlapCovMatrix N fun r => P.eval r))) := by
  have hS := posSemidef_overlapCovMatrix_of_polynomial N hP
  have hbd := abs_overlapCovMatrix_le N (abs_polynomial_profile_le hP)
  have hpt : ∀ H : EnergySpace N,
      gibbs_average₂ (N := N) (H_field N h + β • H)
          (fun σ τ => overlapCovMatrix N (fun r => P.eval r) σ τ)
        = (N : ℝ) * gibbs_average₂ (N := N) (H_field N h + β • H)
            (fun σ τ => P.eval (overlap N σ τ)) := fun H => by
    simpa only [overlapCovMatrix_apply] using
      gibbs_average₂_const_mul (N := N) (H_field N h + β • H) (N : ℝ)
        (fun σ τ => P.eval (overlap N σ τ))
  rw [deriv_gaussFreeEnergy_eq hS (overlapCovMatrix_diag N _) hbd h β,
    integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
  have hNR : ((N : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hN
  field_simp

/-- **Talagrand, Vol. II, Lemma 12.1.4, for a mixed `p`-spin model**: `|∂p_N/∂β| ≤ 2βξ(1)`,
*uniformly in the volume*. This is where the mixed `p`-spin normalisation `D = N ξ(1)` pays: the
general bound `2βD/N` is a constant. -/
theorem abs_deriv_mixedPSpinFreeEnergy_le (hP : ∀ n, 0 ≤ P.coeff n) (hN : N ≠ 0)
    (h : ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    |deriv (fun b => gaussFreeEnergy N ((b ^ 2) • overlapCovMatrix N (fun r => P.eval r)) h) β|
      ≤ 2 * β * P.eval 1 := by
  have hS := posSemidef_overlapCovMatrix_of_polynomial N hP
  have hbd := abs_overlapCovMatrix_le N (abs_polynomial_profile_le hP)
  have hkey := abs_deriv_gaussFreeEnergy_le hS (overlapCovMatrix_diag N _) hbd h hβ
  have hNR : ((N : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rwa [show 2 * β * ((N : ℝ) * P.eval 1) / (N : ℝ) = 2 * β * P.eval 1 from by
    field_simp] at hkey

/-- **Talagrand, Vol. I, Theorem 1.3.4, for a mixed `p`-spin model**: the free energy of *any*
mixed `p`-spin model concentrates, `Var[p_N^ω(β)] ≤ β²ξ(1)/N`. -/
theorem variance_mixedPSpinFreeEnergy_le (hP : ∀ n, 0 ≤ P.coeff n) (h β : ℝ) :
    Var[(fun H : EnergySpace N => free_energy_density (N := N) (H_field N h + β • H));
      gaussField N (overlapCovMatrix N fun r => P.eval r)]
      ≤ β ^ 2 * P.eval 1 / (N : ℝ) := by
  have hS := posSemidef_overlapCovMatrix_of_polynomial N hP
  have hbd := abs_overlapCovMatrix_le N (abs_polynomial_profile_le hP)
  have hkey := variance_gaussFreeEnergy_le hS hbd h β
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simpa using hkey
  · have hNR : ((N : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    rwa [show β ^ 2 * ((N : ℝ) * P.eval 1) / (N : ℝ) ^ 2 = β ^ 2 * P.eval 1 / (N : ℝ) from by
      field_simp] at hkey

/-- **The mean absolute deviation of a mixed `p`-spin free energy is `√(ξ(1)/N)`**, with the
explicit constant `|β| √ξ(1) / √N`. -/
theorem integral_abs_mixedPSpinFreeEnergy_sub_mean_le (hP : ∀ n, 0 ≤ P.coeff n) (hN : N ≠ 0)
    (h y : ℝ) :
    (∫ H : EnergySpace N, |free_energy_density (N := N) (H_field N h + y • H)
        - ∫ H' : EnergySpace N, free_energy_density (N := N) (H_field N h + y • H')
            ∂(gaussField N (overlapCovMatrix N fun r => P.eval r))|
        ∂(gaussField N (overlapCovMatrix N fun r => P.eval r)))
      ≤ |y| * (Real.sqrt (P.eval 1) / Real.sqrt (N : ℝ)) := by
  have hS := posSemidef_overlapCovMatrix_of_polynomial N hP
  have hbd := abs_overlapCovMatrix_le N (abs_polynomial_profile_le hP)
  have hkey := integral_abs_gaussFreeEnergy_sub_mean_le hS hbd h y
  rwa [mul_div_assoc, sqrt_natCast_mul_div_self N hN] at hkey

/-- **Talagrand, Vol. II, Theorem 12.1.1, for a mixed `p`-spin model.** The mean absolute
fluctuation of the energy per site, integrated over a temperature window, is bounded by an
explicit sum of a `√((b-a)ξ(1)/N)` term, a `δ`-term and a `1/(δ√N)`-term; choosing
`δ = N^{-1/4}` balances the last two at `N^{-1/4}`, which is Talagrand's rate. -/
theorem intervalIntegral_mixedPSpinTotalEnergy_fluctuation_le (hP : ∀ n, 0 ≤ P.coeff n)
    (hN : N ≠ 0) (h : ℝ) {δ a b : ℝ} (hδ : 0 < δ) (hab : a ≤ b) (haδ : 0 ≤ a - δ) :
    (∫ β in a..b, ∫ H : EnergySpace N,
        FiniteGibbs.gibbs_average (α := Config N) (H_field N h + β • H)
          (fun σ => |(1 / (N : ℝ)) * H σ - ∫ H' : EnergySpace N, (1 / (N : ℝ)) *
              FiniteGibbs.gibbs_average (α := Config N) (H_field N h + β • H') H'
              ∂(gaussField N (overlapCovMatrix N fun r => P.eval r))|)
        ∂(gaussField N (overlapCovMatrix N fun r => P.eval r)))
      ≤ Real.sqrt ((b - a) * (4 * b * P.eval 1 / (N : ℝ)))
        + (8 * δ * (b + δ) * P.eval 1
          + 3 * (b - a) * ((b + δ) * (Real.sqrt (P.eval 1) / Real.sqrt (N : ℝ))) / δ) := by
  have hS := posSemidef_overlapCovMatrix_of_polynomial N hP
  have hbd := abs_overlapCovMatrix_le N (abs_polynomial_profile_le hP)
  have hkey := intervalIntegral_gaussTotalEnergy_fluctuation_le hS
    (overlapCovMatrix_diag N _) hbd h hδ hab haδ
  have hNR : ((N : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have e1 : (b - a) * (4 * b * ((N : ℝ) * P.eval 1) / (N : ℝ) ^ 2)
      = (b - a) * (4 * b * P.eval 1 / (N : ℝ)) := by field_simp
  have e2 : 2 * δ * (4 * (b + δ) * ((N : ℝ) * P.eval 1) / (N : ℝ))
      = 8 * δ * (b + δ) * P.eval 1 := by field_simp; ring
  have e3 : (b + δ) * Real.sqrt ((N : ℝ) * P.eval 1) / (N : ℝ)
      = (b + δ) * (Real.sqrt (P.eval 1) / Real.sqrt (N : ℝ)) := by
    rw [mul_div_assoc, sqrt_natCast_mul_div_self N hN]
  rwa [e1, e2, e3] at hkey

/-- **The Ghirlanda–Guerra identities hold for every mixed `p`-spin model up to an explicit
`O(N^{-1/4})` error, at some inverse temperature in every window.** The bracket on the right is
`O(N^{-1/4})` at `δ = N^{-1/4}`; dividing by `N`, the scale of the covariance kernel, the
normalised Ghirlanda–Guerra combination is `O(N^{-1/4})`. Talagrand, Vol. II, §12.2. -/
theorem exists_beta_abs_mixedPSpinGhirlandaGuerra_error_le (hP : ∀ n, 0 ≤ P.coeff n) (hN : N ≠ 0)
    {δ a b : ℝ} (hδ : 0 < δ) (hab : a < b) (haδ : 0 ≤ a - δ)
    (m : ℕ) (f : FiniteGibbs.ReplicaFun (α := Config N) m) (i : Fin m) {B : ℝ}
    (hB : ∀ σs, |f σs| ≤ B) :
    ∃ β ∈ Set.Icc a b,
      |FiniteGibbs.ghirlandaGuerraCombination
          (gaussField N ((β ^ 2) • overlapCovMatrix N fun r => P.eval r)) m f i|
        ≤ B * (β * (N : ℝ) *
            ((Real.sqrt ((b - a) * (4 * b * P.eval 1 / (N : ℝ)))
              + (8 * δ * (b + δ) * P.eval 1
                + 3 * (b - a) * ((b + δ) * (Real.sqrt (P.eval 1) / Real.sqrt (N : ℝ)))
                  / δ)) / (b - a))) := by
  have hS := posSemidef_overlapCovMatrix_of_polynomial N hP
  have hbd := abs_overlapCovMatrix_le N (abs_polynomial_profile_le hP)
  have hkey := exists_beta_abs_gaussGhirlandaGuerra_error_le hS
    (overlapCovMatrix_diag N _) hbd hN hδ hab haδ m f i hB
  have hNR : ((N : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have e1 : (b - a) * (4 * b * ((N : ℝ) * P.eval 1) / (N : ℝ) ^ 2)
      = (b - a) * (4 * b * P.eval 1 / (N : ℝ)) := by field_simp
  have e2 : 2 * δ * (4 * (b + δ) * ((N : ℝ) * P.eval 1) / (N : ℝ))
      = 8 * δ * (b + δ) * P.eval 1 := by field_simp; ring
  have e3 : (b + δ) * Real.sqrt ((N : ℝ) * P.eval 1) / (N : ℝ)
      = (b + δ) * (Real.sqrt (P.eval 1) / Real.sqrt (N : ℝ)) := by
    rw [mul_div_assoc, sqrt_natCast_mul_div_self N hN]
  rwa [e1, e2, e3] at hkey

/-! ### Interpolating between two mixed `p`-spin profiles -/

/-- Overlap-driven kernels add, and the profile adds with them. -/
lemma overlapCovMatrix_add_smul (N : ℕ) (A B : Polynomial ℝ) (c : ℝ) :
    overlapCovMatrix N (fun r => A.eval r) + c • overlapCovMatrix N (fun r => B.eval r)
      = overlapCovMatrix N (fun r => (A + c • B).eval r) := by
  ext σ τ
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, overlapCovMatrix_apply,
    Polynomial.eval_add, Polynomial.eval_smul]
  ring

/-- The interpolated profile again has nonnegative coefficients: an interpolation between two
mixed `p`-spin models is a mixed `p`-spin model. -/
lemma nonneg_coeff_add_smul_sq {A B : Polynomial ℝ} (hA : ∀ k, 0 ≤ A.coeff k)
    (hB : ∀ k, 0 ≤ B.coeff k) (t : ℝ) (k : ℕ) : 0 ≤ (A + (t ^ 2) • B).coeff k := by
  rw [Polynomial.coeff_add, Polynomial.coeff_smul, smul_eq_mul]
  have := hA k
  have := hB k
  positivity

/-- **The interpolating field of two independent mixed `p`-spin disorders is again a mixed `p`-spin
disorder**, with profile `A + t² B`.

This is the device that isolates one summand of a mixed Hamiltonian: taking `B = aₚ rᵖ` and
`A = ξ - aₚ rᵖ`, the family passes through the model at `t = 1`, its covariance is
`N(A + t²B)(R)` — overlap-driven with nonnegative coefficients, hence with constant diagonal and
dominated by it, for every `t` — and differentiating in `t` differentiates in the coupling of the
`p`-spin term alone. -/
theorem map_add_smul_prod_gaussField_overlapCovMatrix (N : ℕ) {A B : Polynomial ℝ}
    (hA : ∀ k, 0 ≤ A.coeff k) (hB : ∀ k, 0 ≤ B.coeff k) (t : ℝ) :
    ((gaussField N (overlapCovMatrix N fun r => A.eval r)).prod
        (gaussField N (overlapCovMatrix N fun r => B.eval r))).map (fun q => q.1 + t • q.2)
      = gaussField N (overlapCovMatrix N fun r => (A + (t ^ 2) • B).eval r) := by
  have hSA := posSemidef_overlapCovMatrix_of_polynomial N hA
  have hSB := posSemidef_overlapCovMatrix_of_polynomial N hB
  rw [gaussField, gaussField, gaussField,
    ProbabilityTheory.multivariateGaussian_map_add_smul_prod hSA hSB t,
    overlapCovMatrix_add_smul N A B (t ^ 2)]

end

end SpinGlass
