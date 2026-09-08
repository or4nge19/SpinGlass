/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.MultiComponent

/-!
# The extended Ghirlanda–Guerra identities for mixed `p`-spin models at finite volume

Talagrand, Vol. II, Theorem 12.2.2, instantiated: a mixed `p`-spin model with profile `ξ`
(nonnegative coefficients) is perturbed by independent components with kernels `wₛ² N Rˢ⁺¹`,
`s = 0, …, m`, at couplings `βₛ ∈ [a,b]`. The perturbed model is again a mixed `p`-spin model,
with profile `ξ(r) + ∑ₛ (βₛ wₛ)² rˢ⁺¹`, and `exists_couplings_abs_ghirlandaGuerra_defect_family_le`
exhibits couplings at which the Ghirlanda–Guerra identity holds at **every monomial** `r, …, rᵐ⁺¹`
simultaneously, for every test function, with the explicit rate.

## Main statements

- `SpinGlass.monomialPerturbationKernel`: the family of kernels `(N ξ(R), (wₛ² N Rˢ⁺¹)ₛ)`.
- `SpinGlass.exists_couplings_abs_ghirlandaGuerra_defect_mixedPSpin_monomials_le`: **the extended
  identities at finite volume for a mixed `p`-spin model.**
-/

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology Set
open scoped InnerProductSpace ENNReal

namespace SpinGlass

noncomputable section

variable {N : ℕ}

section Kernels

variable {m : ℕ}

/-- The family of kernels of a mixed `p`-spin model with profile `ξ`, perturbed by the monomial
components `wₛ² N Rˢ⁺¹`, `s = 0, …, m`: coordinate `0` is the model, coordinate `s.succ` the
`(s+1)`-spin perturbation with weight `wₛ`. -/
def monomialPerturbationKernel (N : ℕ) (ξ : ℝ → ℝ) (w : Fin (m + 1) → ℝ) :
    Fin (m + 1 + 1) → Matrix (Config N) (Config N) ℝ :=
  Fin.cons (overlapCovMatrix N ξ)
    (fun s : Fin (m + 1) => (w s) ^ 2 • overlapCovMatrix N (fun r => r ^ ((s : ℕ) + 1)))

@[simp] lemma monomialPerturbationKernel_zero (ξ : ℝ → ℝ) (w : Fin (m + 1) → ℝ) :
    monomialPerturbationKernel N ξ w 0 = overlapCovMatrix N ξ := rfl

@[simp] lemma monomialPerturbationKernel_succ (ξ : ℝ → ℝ) (w : Fin (m + 1) → ℝ) (s : Fin (m + 1)) :
    monomialPerturbationKernel N ξ w s.succ
      = (w s) ^ 2 • overlapCovMatrix N (fun r => r ^ ((s : ℕ) + 1)) := rfl

/-- The monomial profile `r ↦ rᵖ` is the evaluation of `X ^ p`. -/
lemma overlapCovMatrix_pow_eq (p : ℕ) :
    overlapCovMatrix N (fun r : ℝ => r ^ p)
      = overlapCovMatrix N (fun r => ((Polynomial.X : Polynomial ℝ) ^ p).eval r) := by
  simp [Polynomial.eval_pow, Polynomial.eval_X]

lemma posSemidef_overlapCovMatrix_pow (p : ℕ) :
    (overlapCovMatrix N (fun r : ℝ => r ^ p)).PosSemidef := by
  rw [overlapCovMatrix_pow_eq]
  refine posSemidef_overlapCovMatrix_of_polynomial N fun k => ?_
  rw [Polynomial.coeff_X_pow]
  split_ifs <;> norm_num

/-- Every kernel of the perturbed family is positive semidefinite. -/
lemma posSemidef_monomialPerturbationKernel {P : Polynomial ℝ} (hP : ∀ k, 0 ≤ P.coeff k)
    (w : Fin (m + 1) → ℝ) (i : Fin (m + 1 + 1)) :
    (monomialPerturbationKernel N (fun r => P.eval r) w i).PosSemidef := by
  refine Fin.cases ?_ (fun s => ?_) i
  · exact posSemidef_overlapCovMatrix_of_polynomial N hP
  · rw [monomialPerturbationKernel_succ]
    exact (posSemidef_overlapCovMatrix_pow _).smul_sq (w s)

/-- The perturbed kernel is again overlap-driven: **the perturbed model is a mixed `p`-spin model**
with profile `ξ(r) + ∑ₛ (βₛ wₛ)² rˢ⁺¹`. -/
lemma monomialPerturbationKernel_zero_add_sum (ξ : ℝ → ℝ) (w β : Fin (m + 1) → ℝ) :
    monomialPerturbationKernel N ξ w 0
        + ∑ s, (β s) ^ 2 • monomialPerturbationKernel N ξ w s.succ
      = overlapCovMatrix N
          (fun r => ξ r + ∑ s : Fin (m + 1), (β s * w s) ^ 2 * r ^ ((s : ℕ) + 1)) := by
  ext σ τ
  simp only [monomialPerturbationKernel_zero, monomialPerturbationKernel_succ, Matrix.add_apply,
    Matrix.sum_apply, Matrix.smul_apply, overlapCovMatrix_apply, smul_eq_mul, mul_add,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun s _ => by ring

end Kernels

section Capstone

variable {m : ℕ}

set_option maxHeartbeats 1600000 in
-- The statement carries the (15.40) defect with its nested integrals.
/-- **Talagrand, Vol. II, Theorem 12.2.2, for a mixed `p`-spin model at finite volume.**

Let `ξ` be a mixed `p`-spin profile (nonnegative coefficients), `h` an external field, and let the
model be perturbed by independent components with kernels `wₛ² N Rˢ⁺¹`, `s = 0, …, m`, all
`wₛ ≠ 0`. For every window `[a,b] ⊂ (0,∞)` and `δ > 0` there are couplings `β ∈ [a,b]^{m+1}` such
that the perturbed model — the mixed `p`-spin model with profile `ξ(r) + ∑ₛ (βₛ wₛ)² rˢ⁺¹` —
satisfies the Ghirlanda–Guerra identity of Definition 15.3.4, Eq. (15.40), at **every monomial**
`φ(r) = rˢ⁺¹`, `s = 0, …, m`, and for every test function, up to

`‖g‖ N (∑ₚ εₚ) / ((b-a) k βₛ wₛ² N)`,

`εₚ` being Theorem 12.1.1's bound with `M₁ = N ξ(1) + b² N ∑ wₛ²` and `M₂ = wₚ² N`. At
`δ = N^{-1/4}` and `wₛ = c_N 2^{-(s+1)}` this is Talagrand's `O(N^{-1/4} c_N^{-2})` rate. Exact at
every finite volume, for the canonical field, with the couplings exhibited. -/
theorem exists_couplings_abs_ghirlandaGuerra_defect_mixedPSpin_monomials_le (N : ℕ) (hN : N ≠ 0)
    {P : Polynomial ℝ} (hP : ∀ k, 0 ≤ P.coeff k) (h : ℝ) {w : Fin (m + 1) → ℝ}
    (hw : ∀ s, w s ≠ 0) {δ a b : ℝ} (hδ : 0 < δ) (hab : a < b) (ha : 0 < a) :
    ∃ β : Fin (m + 1) → ℝ, (∀ s, β s ∈ Set.Icc a b) ∧
      ∀ (s : Fin (m + 1)) {k : ℕ}, 0 < k → ∀ g : C(Fin k → Fin k → OverlapValue, ℝ),
        |(∫ R, overlapMonomialCM ((s : ℕ) + 1) (R 0 k) * g (blockRestrict k R)
              ∂(((gaussField N (overlapCovMatrix N fun r =>
                    P.eval r + ∑ p : Fin (m + 1), (β p * w p) ^ 2 * r ^ ((p : ℕ) + 1))).map
                  (fun H : EnergySpace N => H + H_field N h)).bind (overlapArrayLaw N)))
            - ((1 / (k : ℝ)) * ((∫ R, overlapMonomialCM ((s : ℕ) + 1) (R 0 k)
                    ∂(((gaussField N (overlapCovMatrix N fun r =>
                          P.eval r + ∑ p : Fin (m + 1), (β p * w p) ^ 2 * r ^ ((p : ℕ) + 1))).map
                        (fun H : EnergySpace N => H + H_field N h)).bind (overlapArrayLaw N)))
                  * ∫ R, g (blockRestrict k R)
                    ∂(((gaussField N (overlapCovMatrix N fun r =>
                          P.eval r + ∑ p : Fin (m + 1), (β p * w p) ^ 2 * r ^ ((p : ℕ) + 1))).map
                        (fun H : EnergySpace N => H + H_field N h)).bind (overlapArrayLaw N)))
              + (1 / (k : ℝ)) * ∑ l ∈ Finset.Ico 1 k,
                  ∫ R, overlapMonomialCM ((s : ℕ) + 1) (R 0 l) * g (blockRestrict k R)
                    ∂(((gaussField N (overlapCovMatrix N fun r =>
                          P.eval r + ∑ p : Fin (m + 1), (β p * w p) ^ 2 * r ^ ((p : ℕ) + 1))).map
                        (fun H : EnergySpace N => H + H_field N h)).bind (overlapArrayLaw N)))|
          ≤ (‖g‖ * ((N : ℝ) *
                ((∑ p : Fin (m + 1), energyFluctuationBound N δ a b
                    ((N : ℝ) * P.eval 1 + b ^ 2 * ∑ q : Fin (m + 1), (w q) ^ 2 * (N : ℝ))
                    ((w p) ^ 2 * (N : ℝ))) / (b - a))))
              / ((k : ℝ) * |β s * ((w s) ^ 2 * (N : ℝ))|) := by
  classical
  set T := monomialPerturbationKernel N (fun r => P.eval r) w with hT
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hTpsd : ∀ i, (T i).PosSemidef := posSemidef_monomialPerturbationKernel hP w
  have hk₀ : ∀ σ τ : Config N, |T 0 σ τ| ≤ (N : ℝ) * P.eval 1 := fun σ τ =>
    abs_overlapCovMatrix_le N (abs_polynomial_profile_le hP) σ τ
  have hpow : ∀ p : ℕ, ∀ r : ℝ, |r| ≤ 1 → |(fun r : ℝ => r ^ p) r| ≤ (fun r : ℝ => r ^ p) 1 := by
    intro p r hr
    simp only [one_pow, abs_pow]
    exact pow_le_one₀ (abs_nonneg r) hr
  have hTs : ∀ (s : Fin (m + 1)) (σ τ : Config N),
      T s.succ σ τ
        = ((w s) ^ 2 * (N : ℝ)) * overlapMonomialCM ((s : ℕ) + 1) (overlapUnit N σ τ) := by
    intro s σ τ
    rw [hT, monomialPerturbationKernel_succ, Matrix.smul_apply, overlapCovMatrix_apply,
      overlapMonomialCM_apply, overlapUnit_coe, smul_eq_mul]
    ring
  have hdiag : ∀ (s : Fin (m + 1)) (σ : Config N), T s.succ σ σ = (w s) ^ 2 * (N : ℝ) := by
    intro s σ
    rw [hT, monomialPerturbationKernel_succ, Matrix.smul_apply, overlapCovMatrix_diag, one_pow,
      mul_one, smul_eq_mul]
  have hk₂ : ∀ (s : Fin (m + 1)) (σ τ : Config N), |T s.succ σ τ| ≤ (w s) ^ 2 * (N : ℝ) := by
    intro s σ τ
    rw [hT, monomialPerturbationKernel_succ, Matrix.smul_apply, smul_eq_mul, abs_mul,
      abs_of_nonneg (sq_nonneg (w s))]
    have := abs_overlapCovMatrix_le N (hpow ((s : ℕ) + 1)) σ τ
    simp only [one_pow, mul_one] at this
    exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
  have hκ : ∀ s : Fin (m + 1), (w s) ^ 2 * (N : ℝ) ≠ 0 := fun s =>
    mul_ne_zero (pow_ne_zero 2 (hw s)) (ne_of_gt hNR)
  obtain ⟨β, hβ, hbnd⟩ := exists_couplings_abs_ghirlandaGuerra_defect_family_le (N := N) T hTpsd hN
    (H_field N h) hδ hab ha hk₀ hκ (fun s => overlapMonomialCM ((s : ℕ) + 1)) hTs hdiag hk₂
  refine ⟨β, hβ, fun s {k} hk g => ?_⟩
  have hb := hbnd s hk g
  rwa [hT, monomialPerturbationKernel_zero_add_sum] at hb

end Capstone

end

end SpinGlass
