/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.MixedPSpin
import SpinGlass.Limit.GhirlandaGuerraFinite

/-!
# The Ghirlanda–Guerra identity of a mixed `p`-spin model, in Talagrand's asymptotic form

`SpinGlass.exists_beta_abs_mixedPSpinGhirlandaGuerra_error_le` bounds the Ghirlanda–Guerra
combination of the *finite replica calculus*;
`SpinGlass.ghirlandaGuerra_defect_eq_combination` identifies that combination with the defect in
Talagrand's Definition 15.3.4, Eq. (15.40), divided by the scale `n κ` of the covariance kernel.
Composing the two gives the quantitative asymptotic statement:

**for a mixed `p`-spin model, the defect in (15.40) at the model's own profile `φ = ξ` is at most
`‖g‖ / (n β)` times the mean absolute fluctuation of the energy per site**,

which Theorem 12.1.1 shows is `O(N^{-1/4})` on average over the inverse temperature. In
particular the identity holds in the thermodynamic limit for `φ = ξ` along any sequence of
temperatures where the fluctuation vanishes.

## Main statements

- `SpinGlass.overlapProfileCM`: the profile `ξ` as a bundled continuous map on `[-1,1]`.
- `SpinGlass.covarianceOperator_gaussField_overlapCovMatrix`: a mixed `p`-spin disorder has
  covariance kernel `β² N ξ(R_{στ})`.
- `SpinGlass.exists_beta_abs_mixedPSpinGhirlandaGuerra_defect_le`: **the capstone.**
-/

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology Set

namespace SpinGlass

noncomputable section

/-- The profile of a mixed `p`-spin model as a bundled continuous map on the overlap range. -/
def overlapProfileCM (P : Polynomial ℝ) : C(OverlapValue, ℝ) :=
  ⟨fun r => P.eval (r : ℝ), P.continuous.comp continuous_subtype_val⟩

@[simp] lemma overlapProfileCM_apply (P : Polynomial ℝ) (r : OverlapValue) :
    overlapProfileCM P r = P.eval (r : ℝ) := rfl

/-- **The covariance kernel of a mixed `p`-spin disorder at strength `β` is `β² N ξ(R_{στ})`.** -/
lemma covarianceOperator_gaussField_overlapCovMatrix (N : ℕ) {P : Polynomial ℝ}
    (hP : ∀ k, 0 ≤ P.coeff k) (β : ℝ) (σ τ : Config N) :
    (ProbabilityTheory.covarianceOperator
        (gaussField N ((β ^ 2) • overlapCovMatrix N fun r => P.eval r))
        (FiniteGibbs.std_basis (α := Config N) σ)) τ
      = (β ^ 2 * (N : ℝ)) * overlapProfileCM P (overlapUnit N σ τ) := by
  have hS := posSemidef_overlapCovMatrix_of_polynomial N hP
  rw [covarianceOperator_gaussField_apply (hS.smul_sq β) σ τ, Matrix.smul_apply, smul_eq_mul,
    overlapCovMatrix_apply, overlapProfileCM_apply, overlapUnit_coe]
  ring

/-- **The Ghirlanda–Guerra identity of a mixed `p`-spin model, with an explicit rate.**

At some inverse temperature in every window `[a,b]` with `a > δ > 0`, the defect in Talagrand's
identity (15.40) — for the model's own profile `ξ` and an arbitrary continuous test function `g` of
the `n × n` overlap block — is at most `‖g‖/(nβ)` times the bracket of Theorem 12.1.1, which is
`O(N^{-1/4})` at `δ = N^{-1/4}`.

Talagrand, *Mean Field Models for Spin Glasses*, Vol. II, §12.2 and Definition 15.3.4. -/
theorem exists_beta_abs_mixedPSpinGhirlandaGuerra_defect_le (N : ℕ) (hN : N ≠ 0)
    {P : Polynomial ℝ} (hP : ∀ k, 0 ≤ P.coeff k)
    {δ a b : ℝ} (hδ : 0 < δ) (hab : a < b) (haδ : 0 ≤ a - δ)
    {n : ℕ} (hn : 0 < n) (g : C(Fin n → Fin n → OverlapValue, ℝ)) :
    ∃ β ∈ Set.Icc a b,
      |(∫ R, overlapProfileCM P (R 0 n) * g (blockRestrict n R)
            ∂((gaussField N ((β ^ 2) • overlapCovMatrix N fun r => P.eval r)).bind
              (overlapArrayLaw N)))
          - ((1 / (n : ℝ)) * ((∫ R, overlapProfileCM P (R 0 n)
                  ∂((gaussField N ((β ^ 2) • overlapCovMatrix N fun r => P.eval r)).bind
                    (overlapArrayLaw N)))
                * ∫ R, g (blockRestrict n R)
                  ∂((gaussField N ((β ^ 2) • overlapCovMatrix N fun r => P.eval r)).bind
                    (overlapArrayLaw N)))
            + (1 / (n : ℝ)) * ∑ l ∈ Finset.Ico 1 n,
                ∫ R, overlapProfileCM P (R 0 l) * g (blockRestrict n R)
                  ∂((gaussField N ((β ^ 2) • overlapCovMatrix N fun r => P.eval r)).bind
                    (overlapArrayLaw N)))|
        ≤ ‖g‖ * ((Real.sqrt ((b - a) * (4 * b * P.eval 1 / (N : ℝ)))
              + (8 * δ * (b + δ) * P.eval 1
                + 3 * (b - a) * ((b + δ) * (Real.sqrt (P.eval 1) / Real.sqrt (N : ℝ)))
                  / δ)) / (b - a)) / ((n : ℝ) * β) := by
  obtain ⟨β, hβmem, hβbd⟩ := exists_beta_abs_mixedPSpinGhirlandaGuerra_error_le hP hN hδ hab haδ
    n (overlapReplicaFun N g) ⟨0, hn⟩ (abs_overlapReplicaFun_le N g)
  refine ⟨β, hβmem, ?_⟩
  have ha0 : (0 : ℝ) < a := by linarith
  have hβ0 : (0 : ℝ) < β := lt_of_lt_of_le ha0 hβmem.1
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hκpos : (0 : ℝ) < β ^ 2 * (N : ℝ) := mul_pos (pow_pos hβ0 2) hNR
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hdefect := abs_ghirlandaGuerra_defect_le hn
    (gaussField N ((β ^ 2) • overlapCovMatrix N fun r => P.eval r)) hκpos.ne'
    (overlapProfileCM P) (covarianceOperator_gaussField_overlapCovMatrix N hP β) g hβbd
  rw [abs_of_pos hκpos] at hdefect
  refine hdefect.trans_eq ?_
  field_simp

/-! ### Single monomials as components of the disorder -/

/-- The monomial test function `r ↦ rᵖ` on the overlap range, as a bundled continuous map. -/
def overlapMonomialCM (p : ℕ) : C(OverlapValue, ℝ) :=
  ⟨fun r => (r : ℝ) ^ p, continuous_subtype_val.pow p⟩

@[simp] lemma overlapMonomialCM_apply (p : ℕ) (r : OverlapValue) :
    overlapMonomialCM p r = (r : ℝ) ^ p := rfl

/-- **A single monomial of a mixed `p`-spin covariance is the cross kernel of a component of the
disorder.** Since `aₚ N Rᵖ ≤ N ξ(R)` in the Loewner order (the difference is again an
overlap-driven kernel with nonnegative coefficients), Douglas' lemma produces directions `w` whose
component field `σ ↦ ⟪H, w σ⟫` has cross kernel exactly the `p`-th monomial. -/
theorem exists_directions_covKernel_monomial (N : ℕ) {P : Polynomial ℝ}
    (hP : ∀ k, 0 ≤ P.coeff k) (p : ℕ) :
    ∃ w : Config N → EnergySpace N, ∀ σ τ : Config N,
      FiniteGibbs.covKernel (gaussField N (overlapCovMatrix N fun r => P.eval r)) w σ τ
        = (N : ℝ) * (P.coeff p * (overlap N σ τ) ^ p) := by
  classical
  have hQc : ∀ k, 0 ≤ (Polynomial.monomial p (P.coeff p)).coeff k := by
    intro k
    rw [Polynomial.coeff_monomial]
    split
    · exact hP p
    · exact le_rfl
  have hRc : ∀ k, 0 ≤ (P - Polynomial.monomial p (P.coeff p)).coeff k := by
    intro k
    rw [Polynomial.coeff_sub, Polynomial.coeff_monomial]
    by_cases hk : p = k
    · subst hk; simp
    · simp [hk, hP k]
  have hS := posSemidef_overlapCovMatrix_of_polynomial N hP
  have hT := posSemidef_overlapCovMatrix_of_polynomial N hQc
  have hR := posSemidef_overlapCovMatrix_of_polynomial N hRc
  have hsub : overlapCovMatrix N (fun r => P.eval r)
        - overlapCovMatrix N (fun r => (Polynomial.monomial p (P.coeff p)).eval r)
      = overlapCovMatrix N (fun r => (P - Polynomial.monomial p (P.coeff p)).eval r) := by
    ext σ τ
    simp only [Matrix.sub_apply, overlapCovMatrix_apply, Polynomial.eval_sub]
    ring
  obtain ⟨w, hw⟩ := exists_directions_covKernel_eq hS hT (by rw [hsub]; exact hR)
  refine ⟨w, fun σ τ => ?_⟩
  rw [hw σ τ, overlapCovMatrix_apply, Polynomial.eval_monomial]

/-- **The Ghirlanda–Guerra identity at a single monomial test function, for a mixed `p`-spin
model.**

The defect in Talagrand's Definition 15.3.4 / Eq. (15.40) at the test function `φ(r) = rᵖ` is at
most `‖g‖ / (n aₚ N)` times the **mean absolute fluctuation of the `p`-spin component field**
`σ ↦ ⟪H, w σ⟫` around its mean. This reduces the identities at every monomial — hence, by
`SpinGlass.satisfiesGhirlandaGuerra_of_monomial`, at every continuous test function — to the
self-averaging of that single field. Exact at every finite volume, no perturbation added. -/
theorem abs_ghirlandaGuerra_defect_le_of_covKernel_monomial (N : ℕ) (hN : N ≠ 0)
    {P : Polynomial ℝ} (hP : ∀ k, 0 ≤ P.coeff k) (p : ℕ) (hap : P.coeff p ≠ 0)
    {w : Config N → EnergySpace N}
    (hw : ∀ σ τ : Config N,
      FiniteGibbs.covKernel (gaussField N (overlapCovMatrix N fun r => P.eval r)) w σ τ
        = (N : ℝ) * (P.coeff p * (overlap N σ τ) ^ p))
    {n : ℕ} (hn : 0 < n) (g : C(Fin n → Fin n → OverlapValue, ℝ)) :
      |(∫ R, overlapMonomialCM p (R 0 n) * g (blockRestrict n R)
            ∂((gaussField N (overlapCovMatrix N fun r => P.eval r)).bind (overlapArrayLaw N)))
          - ((1 / (n : ℝ)) * ((∫ R, overlapMonomialCM p (R 0 n)
                  ∂((gaussField N (overlapCovMatrix N fun r => P.eval r)).bind
                    (overlapArrayLaw N)))
                * ∫ R, g (blockRestrict n R)
                  ∂((gaussField N (overlapCovMatrix N fun r => P.eval r)).bind
                    (overlapArrayLaw N)))
            + (1 / (n : ℝ)) * ∑ l ∈ Finset.Ico 1 n,
                ∫ R, overlapMonomialCM p (R 0 l) * g (blockRestrict n R)
                  ∂((gaussField N (overlapCovMatrix N fun r => P.eval r)).bind
                    (overlapArrayLaw N)))|
        ≤ (‖g‖ * ∫ H : EnergySpace N, (∑ σ : Config N,
              FiniteGibbs.gibbs_pmf (α := Config N) H σ
                * |inner ℝ H (w σ) - ∫ H' : EnergySpace N,
                    FiniteGibbs.gibbs_average_n_det (α := Config N) (n := 1) H'
                      (fun τs => inner ℝ H' (w (τs 0)))
                    ∂(gaussField N (overlapCovMatrix N fun r => P.eval r))|)
            ∂(gaussField N (overlapCovMatrix N fun r => P.eval r)))
          / ((n : ℝ) * ((N : ℝ) * P.coeff p)) := by
  classical
  set μ : Measure (EnergySpace N) := gaussField N (overlapCovMatrix N fun r => P.eval r) with hμ
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hap0 : (0 : ℝ) < P.coeff p := lt_of_le_of_ne (hP p) (Ne.symm hap)
  have hκ : ((N : ℝ) * P.coeff p) ≠ 0 := ne_of_gt (mul_pos hNR hap0)
  -- the kernel realised by the component field
  have hc : ∀ σ τ : Config N, FiniteGibbs.covKernel μ w σ τ
      = ((N : ℝ) * P.coeff p) * overlapMonomialCM p (overlapUnit N σ τ) := by
    intro σ τ
    rw [hw σ τ, overlapMonomialCM_apply, overlapUnit_coe]
    ring
  have hdiag : ∀ σ : Config N,
      (ProbabilityTheory.covarianceOperator μ (w σ)) σ = (N : ℝ) * P.coeff p := by
    intro σ
    have h := hw σ σ
    rw [FiniteGibbs.covKernel_apply] at h
    rw [h, SpinGlass.overlap_self (N := N) (Nat.pos_of_ne_zero hN), one_pow, mul_one]
  obtain ⟨Mw, hMw⟩ := Finite.exists_le fun σ : Config N => ‖w σ‖
  -- the component Ghirlanda–Guerra error bound
  have herr := FiniteGibbs.ghirlandaGuerra_error_of_le_integral_abs (μ := μ)
    (integral_id_gaussField N _) hMw hdiag n (overlapReplicaFun N g) ⟨0, hn⟩
    (abs_overlapReplicaFun_le N g)
  -- transport it to the kernel `c`
  have hker : FiniteGibbs.covKernel μ w
      = fun σ τ => ((N : ℝ) * P.coeff p) * overlapMonomialCM p (overlapUnit N σ τ) :=
    funext fun σ => funext fun τ => hc σ τ
  rw [hker] at herr
  have hfinal := abs_ghirlandaGuerra_defect_of_le hn μ hκ (overlapMonomialCM p)
    (fun σ τ => rfl) g herr
  rwa [abs_of_pos (mul_pos hNR hap0)] at hfinal

/-- **The existence form**: some component of the disorder realises the `p`-th monomial kernel, and
the defect in Talagrand's (15.40) at `φ(r) = rᵖ` is controlled by that component's fluctuation. -/
theorem exists_abs_ghirlandaGuerra_defect_monomial_le (N : ℕ) (hN : N ≠ 0) {P : Polynomial ℝ}
    (hP : ∀ k, 0 ≤ P.coeff k) (p : ℕ) (hap : P.coeff p ≠ 0)
    {n : ℕ} (hn : 0 < n) (g : C(Fin n → Fin n → OverlapValue, ℝ)) :
    ∃ w : Config N → EnergySpace N,
      |(∫ R, overlapMonomialCM p (R 0 n) * g (blockRestrict n R)
            ∂((gaussField N (overlapCovMatrix N fun r => P.eval r)).bind (overlapArrayLaw N)))
          - ((1 / (n : ℝ)) * ((∫ R, overlapMonomialCM p (R 0 n)
                  ∂((gaussField N (overlapCovMatrix N fun r => P.eval r)).bind
                    (overlapArrayLaw N)))
                * ∫ R, g (blockRestrict n R)
                  ∂((gaussField N (overlapCovMatrix N fun r => P.eval r)).bind
                    (overlapArrayLaw N)))
            + (1 / (n : ℝ)) * ∑ l ∈ Finset.Ico 1 n,
                ∫ R, overlapMonomialCM p (R 0 l) * g (blockRestrict n R)
                  ∂((gaussField N (overlapCovMatrix N fun r => P.eval r)).bind
                    (overlapArrayLaw N)))|
        ≤ (‖g‖ * ∫ H : EnergySpace N, (∑ σ : Config N,
              FiniteGibbs.gibbs_pmf (α := Config N) H σ
                * |inner ℝ H (w σ) - ∫ H' : EnergySpace N,
                    FiniteGibbs.gibbs_average_n_det (α := Config N) (n := 1) H'
                      (fun τs => inner ℝ H' (w (τs 0)))
                    ∂(gaussField N (overlapCovMatrix N fun r => P.eval r))|)
            ∂(gaussField N (overlapCovMatrix N fun r => P.eval r)))
          / ((n : ℝ) * ((N : ℝ) * P.coeff p)) := by
  obtain ⟨w, hw⟩ := exists_directions_covKernel_monomial N hP p
  exact ⟨w, abs_ghirlandaGuerra_defect_le_of_covKernel_monomial N hN hP p hap hw hn g⟩

end

end SpinGlass
