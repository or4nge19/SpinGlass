/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.MixedPSpinComponent
import SpinGlass.MixedPSpinGhirlandaGuerra
import Common.Mathlib.Probability.Distributions.Gaussian.MultivariateUniqueness

/-!
# The Ghirlanda–Guerra identity at the profile of a disorder component

Composing the two halves already in place:

* `SpinGlass.exists_coupling_abs_ghirlandaGuerraCombinationOf_component_le` bounds the
  Ghirlanda–Guerra combination of a component's cross kernel at some coupling in every window, by
  `B N` times Theorem 12.1.1's bound divided by the window width;
* `SpinGlass.abs_ghirlandaGuerra_defect_of_le` converts a bound on that combination into a bound on
  the **defect in Talagrand's Definition 15.3.4, Eq. (15.40)**, divided by the scale `n κ` of the
  kernel.

The result is an explicit finite-volume rate for the identity at the profile `φ` of the component:
no limit, no perturbation, no unproved hypothesis.

## Main statements

- `SpinGlass.exists_coupling_abs_ghirlandaGuerra_defect_component_le`: **the identity at the
  component's profile, with an explicit rate, at some coupling in every window.**
- `SpinGlass.map_pairAffine_disorderPairLaw`: the law of the interpolated Hamiltonian *is* the
  centered Gaussian field with kernel `K₁ + t² K₂` (through
  `ProbabilityTheory.IsGaussian.eq_multivariateGaussian`).
- `SpinGlass.exists_coupling_abs_ghirlandaGuerra_defect_mixedPSpin_le`: **the mixed `p`-spin
  instance**, stated for the canonical field `gaussField N (overlapCovMatrix N ξₓ)` with
  `ξₓ = ξ + (x² - 1) aₚ rᵖ` — the model with its `p`-th coefficient rescaled by `x²` — at the
  monomial `φ(r) = rᵖ`, with no coupling space in the statement.
-/

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology Set
open scoped InnerProductSpace ENNReal

namespace SpinGlass

noncomputable section

variable {N : ℕ}

section Component

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {K₁ K₂ : Config N → Config N → ℝ}
variable (G₁ : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K₁)
variable (G₂ : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K₂)

set_option maxHeartbeats 1600000 in
-- The statement composes Theorem 12.1.1, the Ghirlanda–Guerra error bound and the §15.3
-- translation; each carries several nested integrals, so elaboration needs more than the default.
omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- **The Ghirlanda–Guerra identity at the profile of a disorder component, with an explicit
rate, at some coupling in every window.**

Let the disorder split as `H_A + x H_B` with independent centered Gaussian pieces of kernels `K₁`
and `K₂`, and let the second kernel be overlap-driven, `K₂ = κ₀ φ(R_{στ})`. Then at some coupling
`x ∈ [a,b]` the defect in Talagrand's Definition 15.3.4, Eq. (15.40), at the test function `φ` is
at most

`‖g‖ · N · ε / ((b-a) · n · |x κ₀|)`,

where `ε` is Theorem 12.1.1's bound for the component. **The coupling `x` is uniform over all test
functions**: it depends only on the fluctuation functional of the component, so a single `x` serves
every `n` and `g` — as the passage to `SatisfiesGhirlandaGuerra` requires. For a mixed `p`-spin
model `κ₀ = aₚ N`, `M₁, M₂ = O(N)` and `ε = O(N^{-1/4})` at `δ = N^{-1/4}`, so the bound is
`O(N^{-1/4})`. Exact at every finite volume. -/
theorem exists_coupling_abs_ghirlandaGuerra_defect_component_le
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) (hN : N ≠ 0) (c₀ : EnergySpace N)
    {δ a b : ℝ} (hδ : 0 < δ) (hab : a < b) (ha : 0 < a)
    {d κ₀ M₁ M₂ : ℝ} (hκ₀ : κ₀ ≠ 0) (φ : C(OverlapValue, ℝ))
    (hdiag : ∀ σ : Config N, K₂ σ σ = d)
    (hK₂ : ∀ σ τ : Config N, K₂ σ τ = κ₀ * φ (overlapUnit N σ τ))
    (hk₁ : ∀ σ τ : Config N, |K₁ σ τ| ≤ M₁) (hk₂ : ∀ σ τ : Config N, |K₂ σ τ| ≤ M₂) :
    ∃ x ∈ Set.Icc a b, ∀ {n : ℕ}, 0 < n → ∀ g : C(Fin n → Fin n → OverlapValue, ℝ),
      |(∫ R, φ (R 0 n) * g (blockRestrict n R)
            ∂(((disorderPairLaw (Ω := Ω) (N := N) G₁ G₂).map
                (fun q : DisorderSpace (N := N) => pairAffine N x q + c₀)).bind
              (overlapArrayLaw N)))
          - ((1 / (n : ℝ)) * ((∫ R, φ (R 0 n)
                  ∂(((disorderPairLaw (Ω := Ω) (N := N) G₁ G₂).map
                      (fun q : DisorderSpace (N := N) => pairAffine N x q + c₀)).bind
                    (overlapArrayLaw N)))
                * ∫ R, g (blockRestrict n R)
                  ∂(((disorderPairLaw (Ω := Ω) (N := N) G₁ G₂).map
                      (fun q : DisorderSpace (N := N) => pairAffine N x q + c₀)).bind
                    (overlapArrayLaw N)))
            + (1 / (n : ℝ)) * ∑ l ∈ Finset.Ico 1 n,
                ∫ R, φ (R 0 l) * g (blockRestrict n R)
                  ∂(((disorderPairLaw (Ω := Ω) (N := N) G₁ G₂).map
                      (fun q : DisorderSpace (N := N) => pairAffine N x q + c₀)).bind
                    (overlapArrayLaw N)))|
        ≤ (‖g‖ * ((N : ℝ) *
              ((Real.sqrt ((b - a) * ((1 / (N : ℝ)) * (2 * ((|a| + |b|) * M₂) / (N : ℝ))))
                + (2 * δ * (2 * ((|a| + |b| + 2 * δ) * M₂) / (N : ℝ))
                  + 3 * (b - a)
                      * (Real.sqrt (M₁ + (|a| + |b| + δ) ^ 2 * M₂) / (N : ℝ)) / δ))
                / (b - a))))
            / ((n : ℝ) * |x * κ₀|) := by
  classical
  obtain ⟨x, hx, hbnd⟩ := exists_coupling_abs_ghirlandaGuerraCombinationOf_component_le
    (Ω := Ω) (N := N) G₁ G₂ hindep hN c₀ hδ hab hdiag hk₁ hk₂
  refine ⟨x, hx, fun {n} hn g => ?_⟩
  have hbnd' := hbnd n (overlapReplicaFun N g) ⟨0, hn⟩ (abs_overlapReplicaFun_le N g)
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha hx.1
  have hκ : x * κ₀ ≠ 0 := mul_ne_zero (ne_of_gt hx0) hκ₀
  have hgaussP : ProbabilityTheory.IsGaussian (disorderPairLaw (Ω := Ω) (N := N) G₁ G₂) :=
    isGaussian_disorderPairLaw_of_indep (Ω := Ω) (N := N) G₁ G₂ hindep
  have hprob : IsProbabilityMeasure
      ((disorderPairLaw (Ω := Ω) (N := N) G₁ G₂).map
        (fun q : DisorderSpace (N := N) => pairAffine N x q + c₀)) :=
    MeasureTheory.Measure.isProbabilityMeasure_map
      ((pairAffine N x).continuous.add continuous_const).measurable.aemeasurable
  have hc : ∀ σ τ : Config N,
      FiniteGibbs.crossKernel (disorderPairLaw (Ω := Ω) (N := N) G₁ G₂)
          (pairAffine N x) (std_basis_right (N := N)) σ τ
        = (x * κ₀) * φ (overlapUnit N σ τ) := by
    intro σ τ
    rw [crossKernel_pairAffine_std_basis_right (Ω := Ω) (N := N) G₁ G₂ hindep x σ τ, hK₂ σ τ]
    ring
  exact abs_ghirlandaGuerra_defect_of_le hn
    ((disorderPairLaw (Ω := Ω) (N := N) G₁ G₂).map
      (fun q : DisorderSpace (N := N) => pairAffine N x q + c₀)) hκ φ hc g hbnd'

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- **The law of the interpolated Hamiltonian is the centered Gaussian field with kernel
`K₁ + t² K₂`.** `covarianceOperator_map_pairAffine_std_basis` reads the kernel off the covariance
operator; `ProbabilityTheory.IsGaussian.eq_multivariateGaussian_of_inner_covarianceOperator`
identifies the law. -/
theorem map_pairAffine_disorderPairLaw (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) (t : ℝ) :
    (disorderPairLaw (Ω := Ω) (N := N) G₁ G₂).map (pairAffine N t)
      = gaussField N (Matrix.of fun σ τ : Config N => K₁ σ τ + t ^ 2 * K₂ σ τ) := by
  classical
  have hgauss : ProbabilityTheory.IsGaussian (disorderPairLaw (Ω := Ω) (N := N) G₁ G₂) :=
    isGaussian_disorderPairLaw_of_indep (Ω := Ω) (N := N) G₁ G₂ hindep
  have hmap : ProbabilityTheory.IsGaussian
      ((disorderPairLaw (Ω := Ω) (N := N) G₁ G₂).map (pairAffine N t)) :=
    ProbabilityTheory.isGaussian_map (μ := disorderPairLaw (Ω := Ω) (N := N) G₁ G₂)
      (pairAffine N t)
  rw [gaussField]
  refine ProbabilityTheory.IsGaussian.eq_multivariateGaussian_of_inner_covarianceOperator _
    (integral_id_map_pairAffine (Ω := Ω) (N := N) G₁ G₂ hindep t) fun σ τ => ?_
  have hsingle : ∀ ρ : Config N, EuclideanSpace.single ρ (1 : ℝ) = std_basis N ρ :=
    fun ρ => (FiniteGibbs.std_basis_eq_single (α := Config N) ρ).symm
  have h2 : inner ℝ (std_basis N τ)
      (ProbabilityTheory.covarianceOperator
        ((disorderPairLaw (Ω := Ω) (N := N) G₁ G₂).map (pairAffine N t)) (std_basis N σ))
      = K₁ σ τ + t ^ 2 * K₂ σ τ := by
    rw [inner_std_basis_apply]
    exact covarianceOperator_map_pairAffine_std_basis (Ω := Ω) (N := N) G₁ G₂ hindep t σ τ
  rw [real_inner_comm] at h2
  rw [Matrix.of_apply, hsingle, hsingle]
  exact h2

end Component

/-! ### The mixed `p`-spin instance -/

section MixedPSpin

/-- Removing one monomial from a nonnegative-coefficient polynomial keeps the coefficients
nonnegative. -/
lemma nonneg_coeff_sub_monomial {P : Polynomial ℝ} (hP : ∀ k, 0 ≤ P.coeff k) (p k : ℕ) :
    0 ≤ (P - Polynomial.monomial p (P.coeff p)).coeff k := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_monomial]
  split_ifs with h
  · subst h; simp
  · simpa using hP k

/-- A monomial with a nonnegative coefficient has nonnegative coefficients. -/
lemma nonneg_coeff_monomial_of_nonneg {c : ℝ} (hc : 0 ≤ c) (p k : ℕ) :
    0 ≤ (Polynomial.monomial p c).coeff k := by
  rw [Polynomial.coeff_monomial]
  split_ifs
  · exact hc
  · exact le_rfl

/-- The pair kernel `K₁ + t² K₂` of two overlap-driven models is overlap-driven with the
interpolated profile. -/
lemma of_overlapCovMatrix_add_sq_mul (N : ℕ) (A B : Polynomial ℝ) (t : ℝ) :
    (Matrix.of fun σ τ : Config N =>
        overlapCovMatrix N (fun r => A.eval r) σ τ
          + t ^ 2 * overlapCovMatrix N (fun r => B.eval r) σ τ)
      = overlapCovMatrix N (fun r => (A + (t ^ 2) • B).eval r) := by
  rw [← overlapCovMatrix_add_smul]
  ext σ τ
  simp

set_option maxHeartbeats 1600000 in
-- The statement carries the composed §12.1 bound with several nested integrals.
/-- **The Ghirlanda–Guerra identity for a mixed `p`-spin model at the monomial `φ(r) = rᵖ`,
with an explicit finite-volume rate, at some rescaling of the `p`-th coefficient in every
window.**

For the mixed `p`-spin model with profile `ξ` (nonnegative coefficients, `aₚ = ξ.coeff p ≠ 0`)
and external field `h`, and every window `[a,b] ⊂ (0,∞)`, there is `x ∈ [a,b]` such that the
model with profile `ξₓ = ξ + (x² - 1) aₚ rᵖ` — the `p`-th coefficient rescaled by `x²` —
satisfies the identity of Talagrand's Definition 15.3.4, Eq. (15.40), at `φ(r) = rᵖ` up to

`‖g‖ · N · ε / ((b-a) · n · x aₚ N)`,

where `ε` is Theorem 12.1.1's bound with `M₁ = N(ξ(1) - aₚ)`, `M₂ = aₚ N`; at `δ = N^{-1/4}` this is
`O(N^{-1/4})`. The statement is about the canonical field `gaussField N (overlapCovMatrix N ξₓ)`:
no coupling space, no perturbation, no unproved hypothesis. -/
theorem exists_coupling_abs_ghirlandaGuerra_defect_mixedPSpin_le (N : ℕ) (hN : N ≠ 0)
    {P : Polynomial ℝ} (hP : ∀ k, 0 ≤ P.coeff k) (p : ℕ) (hap : P.coeff p ≠ 0) (h : ℝ)
    {δ a b : ℝ} (hδ : 0 < δ) (hab : a < b) (ha : 0 < a) :
    ∃ x ∈ Set.Icc a b, ∀ {n : ℕ}, 0 < n → ∀ g : C(Fin n → Fin n → OverlapValue, ℝ),
      |(∫ R, overlapMonomialCM p (R 0 n) * g (blockRestrict n R)
            ∂(((gaussField N (overlapCovMatrix N fun r =>
                  (P + (x ^ 2 - 1) • Polynomial.monomial p (P.coeff p)).eval r)).map
                (fun H : EnergySpace N => H + H_field N h)).bind (overlapArrayLaw N)))
          - ((1 / (n : ℝ)) * ((∫ R, overlapMonomialCM p (R 0 n)
                  ∂(((gaussField N (overlapCovMatrix N fun r =>
                        (P + (x ^ 2 - 1) • Polynomial.monomial p (P.coeff p)).eval r)).map
                      (fun H : EnergySpace N => H + H_field N h)).bind (overlapArrayLaw N)))
                * ∫ R, g (blockRestrict n R)
                  ∂(((gaussField N (overlapCovMatrix N fun r =>
                        (P + (x ^ 2 - 1) • Polynomial.monomial p (P.coeff p)).eval r)).map
                      (fun H : EnergySpace N => H + H_field N h)).bind (overlapArrayLaw N)))
            + (1 / (n : ℝ)) * ∑ l ∈ Finset.Ico 1 n,
                ∫ R, overlapMonomialCM p (R 0 l) * g (blockRestrict n R)
                  ∂(((gaussField N (overlapCovMatrix N fun r =>
                        (P + (x ^ 2 - 1) • Polynomial.monomial p (P.coeff p)).eval r)).map
                      (fun H : EnergySpace N => H + H_field N h)).bind (overlapArrayLaw N)))|
        ≤ (‖g‖ * ((N : ℝ) *
              ((Real.sqrt ((b - a) * ((1 / (N : ℝ))
                    * (2 * ((|a| + |b|) * ((N : ℝ) * P.coeff p)) / (N : ℝ))))
                + (2 * δ * (2 * ((|a| + |b| + 2 * δ) * ((N : ℝ) * P.coeff p)) / (N : ℝ))
                  + 3 * (b - a)
                      * (Real.sqrt ((N : ℝ) * (P.eval 1 - P.coeff p)
                          + (|a| + |b| + δ) ^ 2 * ((N : ℝ) * P.coeff p)) / (N : ℝ)) / δ))
                / (b - a))))
            / ((n : ℝ) * |x * ((N : ℝ) * P.coeff p)|) := by
  classical
  set Q : Polynomial ℝ := Polynomial.monomial p (P.coeff p) with hQ
  set A : Polynomial ℝ := P - Q with hA
  have hAc : ∀ k, 0 ≤ A.coeff k := nonneg_coeff_sub_monomial hP p
  have hQc : ∀ k, 0 ≤ Q.coeff k := nonneg_coeff_monomial_of_nonneg (hP p) p
  have hS := posSemidef_overlapCovMatrix_of_polynomial N hAc
  have hT := posSemidef_overlapCovMatrix_of_polynomial N hQc
  obtain ⟨Ω, _, _, G₁, G₂, hindep⟩ := exists_gaussianDisorder_pair_indepFun N hS hT
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hap0 : (0 : ℝ) < P.coeff p := lt_of_le_of_ne (hP p) (Ne.symm hap)
  have hκ₀ : (N : ℝ) * P.coeff p ≠ 0 := ne_of_gt (mul_pos hNR hap0)
  have hQ1 : Q.eval 1 = P.coeff p := by simp [hQ, Polynomial.eval_monomial]
  have hA1 : A.eval 1 = P.eval 1 - P.coeff p := by
    simp [hA, hQ, Polynomial.eval_sub, Polynomial.eval_monomial]
  have hdiag : ∀ σ : Config N, overlapCovMatrix N (fun r => Q.eval r) σ σ = (N : ℝ) * P.coeff p :=
    fun σ => by rw [overlapCovMatrix_diag, hQ1]
  have hK₂ : ∀ σ τ : Config N, overlapCovMatrix N (fun r => Q.eval r) σ τ
      = ((N : ℝ) * P.coeff p) * overlapMonomialCM p (overlapUnit N σ τ) := by
    intro σ τ
    rw [overlapCovMatrix_apply, overlapMonomialCM_apply, overlapUnit_coe, hQ,
      Polynomial.eval_monomial]
    ring
  have hk₁ : ∀ σ τ : Config N, |overlapCovMatrix N (fun r => A.eval r) σ τ|
      ≤ (N : ℝ) * (P.eval 1 - P.coeff p) := by
    intro σ τ
    rw [← hA1]
    exact abs_overlapCovMatrix_le N (abs_polynomial_profile_le hAc) σ τ
  have hk₂ : ∀ σ τ : Config N, |overlapCovMatrix N (fun r => Q.eval r) σ τ|
      ≤ (N : ℝ) * P.coeff p := by
    intro σ τ
    rw [← hQ1]
    exact abs_overlapCovMatrix_le N (abs_polynomial_profile_le hQc) σ τ
  obtain ⟨x, hx, hbnd⟩ := exists_coupling_abs_ghirlandaGuerra_defect_component_le
    (Ω := Ω) (N := N) G₁ G₂ hindep hN (H_field N h) hδ hab ha hκ₀ (overlapMonomialCM p)
    hdiag hK₂ hk₁ hk₂
  -- identify the law of the interpolated model
  have hlaw : (disorderPairLaw (Ω := Ω) (N := N) G₁ G₂).map
        (fun q : DisorderSpace (N := N) => pairAffine N x q + H_field N h)
      = (gaussField N (overlapCovMatrix N fun r =>
          (P + (x ^ 2 - 1) • Polynomial.monomial p (P.coeff p)).eval r)).map
          (fun H : EnergySpace N => H + H_field N h) := by
    have hcomp : (fun q : DisorderSpace (N := N) => pairAffine N x q + H_field N h)
        = (fun H : EnergySpace N => H + H_field N h) ∘ (pairAffine N x) := rfl
    rw [hcomp, ← MeasureTheory.Measure.map_map (measurable_add_const _)
      (pairAffine N x).continuous.measurable,
      map_pairAffine_disorderPairLaw (Ω := Ω) (N := N) G₁ G₂ hindep x,
      of_overlapCovMatrix_add_sq_mul]
    congr 3
    funext r
    congr 1
    rw [hA, hQ, sub_smul, one_smul]
    abel
  refine ⟨x, hx, fun {n} hn g => ?_⟩
  have hb := hbnd hn g
  rw [hlaw] at hb
  exact hb

set_option maxHeartbeats 1600000 in
-- The statement carries the composed §12.1 bound with several nested integrals.
/-- **The Ghirlanda–Guerra identity at the profile of any overlap-driven summand.** Split the
profile as `ξ = A + B` with both parts having nonnegative coefficients. Then at some `x ∈ [a,b]`
the model with profile `A + x² B` satisfies the identity of Definition 15.3.4, Eq. (15.40), at
`φ = B` up to `‖g‖ · N · ε / ((b-a) · n · x N)`, with `M₁ = N A(1)`, `M₂ = N B(1)`. The monomial
statement `exists_coupling_abs_ghirlandaGuerra_defect_mixedPSpin_le` is the case `B = aₚ rᵖ`,
normalised by `aₚ`. -/
theorem exists_coupling_abs_ghirlandaGuerra_defect_split_le (N : ℕ) (hN : N ≠ 0)
    {A B : Polynomial ℝ} (hA : ∀ k, 0 ≤ A.coeff k) (hB : ∀ k, 0 ≤ B.coeff k) (h : ℝ)
    {δ a b : ℝ} (hδ : 0 < δ) (hab : a < b) (ha : 0 < a) :
    ∃ x ∈ Set.Icc a b, ∀ {n : ℕ}, 0 < n → ∀ g : C(Fin n → Fin n → OverlapValue, ℝ),
      |(∫ R, overlapProfileCM B (R 0 n) * g (blockRestrict n R)
            ∂(((gaussField N (overlapCovMatrix N fun r => (A + (x ^ 2) • B).eval r)).map
                (fun H : EnergySpace N => H + H_field N h)).bind (overlapArrayLaw N)))
          - ((1 / (n : ℝ)) * ((∫ R, overlapProfileCM B (R 0 n)
                  ∂(((gaussField N (overlapCovMatrix N fun r => (A + (x ^ 2) • B).eval r)).map
                      (fun H : EnergySpace N => H + H_field N h)).bind (overlapArrayLaw N)))
                * ∫ R, g (blockRestrict n R)
                  ∂(((gaussField N (overlapCovMatrix N fun r => (A + (x ^ 2) • B).eval r)).map
                      (fun H : EnergySpace N => H + H_field N h)).bind (overlapArrayLaw N)))
            + (1 / (n : ℝ)) * ∑ l ∈ Finset.Ico 1 n,
                ∫ R, overlapProfileCM B (R 0 l) * g (blockRestrict n R)
                  ∂(((gaussField N (overlapCovMatrix N fun r => (A + (x ^ 2) • B).eval r)).map
                      (fun H : EnergySpace N => H + H_field N h)).bind (overlapArrayLaw N)))|
        ≤ (‖g‖ * ((N : ℝ) *
              ((Real.sqrt ((b - a) * ((1 / (N : ℝ))
                    * (2 * ((|a| + |b|) * ((N : ℝ) * B.eval 1)) / (N : ℝ))))
                + (2 * δ * (2 * ((|a| + |b| + 2 * δ) * ((N : ℝ) * B.eval 1)) / (N : ℝ))
                  + 3 * (b - a)
                      * (Real.sqrt ((N : ℝ) * A.eval 1
                          + (|a| + |b| + δ) ^ 2 * ((N : ℝ) * B.eval 1)) / (N : ℝ)) / δ))
                / (b - a))))
            / ((n : ℝ) * |x * (N : ℝ)|) := by
  classical
  have hS := posSemidef_overlapCovMatrix_of_polynomial N hA
  have hT := posSemidef_overlapCovMatrix_of_polynomial N hB
  obtain ⟨Ω, _, _, G₁, G₂, hindep⟩ := exists_gaussianDisorder_pair_indepFun N hS hT
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hdiag : ∀ σ : Config N, overlapCovMatrix N (fun r => B.eval r) σ σ = (N : ℝ) * B.eval 1 :=
    fun σ => overlapCovMatrix_diag N _ σ
  have hK₂ : ∀ σ τ : Config N, overlapCovMatrix N (fun r => B.eval r) σ τ
      = (N : ℝ) * overlapProfileCM B (overlapUnit N σ τ) := by
    intro σ τ
    rw [overlapCovMatrix_apply, overlapProfileCM_apply, overlapUnit_coe]
  obtain ⟨x, hx, hbnd⟩ := exists_coupling_abs_ghirlandaGuerra_defect_component_le
    (Ω := Ω) (N := N) G₁ G₂ hindep hN (H_field N h) hδ hab ha hNR (overlapProfileCM B)
    hdiag hK₂ (fun σ τ => abs_overlapCovMatrix_le N (abs_polynomial_profile_le hA) σ τ)
    (fun σ τ => abs_overlapCovMatrix_le N (abs_polynomial_profile_le hB) σ τ)
  have hlaw : (disorderPairLaw (Ω := Ω) (N := N) G₁ G₂).map
        (fun q : DisorderSpace (N := N) => pairAffine N x q + H_field N h)
      = (gaussField N (overlapCovMatrix N fun r => (A + (x ^ 2) • B).eval r)).map
          (fun H : EnergySpace N => H + H_field N h) := by
    have hcomp : (fun q : DisorderSpace (N := N) => pairAffine N x q + H_field N h)
        = (fun H : EnergySpace N => H + H_field N h) ∘ (pairAffine N x) := rfl
    rw [hcomp, ← MeasureTheory.Measure.map_map (measurable_add_const _)
      (pairAffine N x).continuous.measurable,
      map_pairAffine_disorderPairLaw (Ω := Ω) (N := N) G₁ G₂ hindep x,
      of_overlapCovMatrix_add_sq_mul]
  refine ⟨x, hx, fun {n} hn g => ?_⟩
  have hb := hbnd hn g
  rw [hlaw] at hb
  exact hb

end MixedPSpin

end

end SpinGlass
