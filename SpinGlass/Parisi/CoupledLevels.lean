/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.CoupledInterpolation
import SpinGlass.Parisi.CoupledBranch
import SpinGlass.Parisi.PairLevels

/-!
# The coupled scheme along the branches: the bound as a level sum

The interpolating Hamiltonian of the coupled scheme at time `t` (`coupledTruncHam`), evaluated at
`(σ, α)`, is the branch Hamiltonian `pairBranchHamX` with `H = √t H_N`, no `λ`, and the factors
`√(1-t) L + L'` at the marks of the branch `α` (`coupledTruncHam_apply`). With the weights
`u*_α 1_{R_{1,2} = u}` (`coupledWt`), the constrained partial partition functions are the branch
functions `pairBranchZX` (`wCondZ_coupledTruncHam`), and the integrand of Lemma 14.6.1 is the level
sum `levelBound` of the truncated pair fractions of `exp F_t`
(`treeBoundIntegrand_coupled_eq_levelBound`) — Talagrand's reduction of `⟨θ(ρ_{(α,γ)})⟩_s` to the
cascade pair fractions, (14.137).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N : ℕ) {κ : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
variable {Ω : Type*} [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]

omit N [Fintype J] [DecidableEq J] in
/-- The mark of the node of `α` at depth `p + 1` is the `p`-th mark along the branch. -/
lemma truncMarks_branchNode {T : Type*} (M : ℕ) (z : CascadeMarks T κ) (α : TruncBranch κ M)
    (p : Fin κ) :
    truncMarks κ M z (branchNode κ M α p) = branchMarks κ z (truncBranchCoe κ M α) p := by
  rw [branchMarks_eq_nodeMark]
  rfl

omit N [Fintype J] [DecidableEq J] in
lemma truncMarks_branchNode_fun {T : Type*} (M : ℕ) (z : CascadeMarks T κ)
    (α : TruncBranch κ M) :
    (fun p => truncMarks κ M z (branchNode κ M α p)) = branchMarks κ z (truncBranchCoe κ M α) :=
  funext fun p => truncMarks_branchNode M z α p

omit [DecidableEq J] in
/-- The coupled mark is linear in the factors. -/
lemma pairBranchMark_smul_add (s : ℝ) (L₀ L₀' : Fin 2 → J → ℝ) (L L' : Fin κ → Fin 2 → J → ℝ)
    (z₀ : Fin N × J → ℝ) (x : Fin κ → Fin N × J → ℝ) (l : Fin 2) (i : Fin N) :
    s * pairBranchMark N κ L₀ L z₀ x l i + pairBranchMark N κ L₀' L' z₀ x l i
      = pairBranchMark N κ (s • L₀ + L₀') (fun p => s • L p + L' p) z₀ x l i := by
  unfold pairBranchMark
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]
  ring

/-! ### The interpolating Hamiltonian along the branches -/

/-- The interpolating Hamiltonian of the coupled scheme at time `t`:
`√t (H_N(σ¹) + H_N(σ²)) + √(1-t) H(σ¹,σ²,α) + H⁰(σ¹,σ²,α)`. -/
def coupledTruncHam (M : ℕ) (t : ℝ) (ξ : ℝ → ℝ)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (L₀ L₀' : Fin 2 → J → ℝ) (L L' : Fin κ → Fin 2 → J → ℝ)
    (a : Fin N × Fin 2 → ℝ) (ω : Ω × SiteMarksSpace (Fin N × J) κ) :
    FiniteGibbs.EnergySpace (PairConfig N (TruncBranch κ M)) :=
  gaussianInterp t (pair (coupledModelField N M ξ G₀ v₀ vs)
    (coupledTreeField N M Pm v₀ vs L₀ L) ω) + coupledExtField N M Pm v₀ vs L₀' L' a ω

/-- **The interpolating Hamiltonian along a branch**: at `(σ, α)` it is the branch Hamiltonian
with `H = √t H_N`, factors `√(1-t) L + L'`, and the marks of `α`. -/
theorem coupledTruncHam_apply (M : ℕ) (t : ℝ) (ξ : ℝ → ℝ)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (L₀ L₀' : Fin 2 → J → ℝ) (L L' : Fin κ → Fin 2 → J → ℝ)
    (a : Fin N × Fin 2 → ℝ) (ω : Ω × SiteMarksSpace (Fin N × J) κ)
    (x : PairConfig N (TruncBranch κ M)) :
    coupledTruncHam N M t ξ G₀ v₀ vs L₀ L₀' L L' a ω x
      = pairBranchHamX N κ (Real.sqrt t • G₀.U ω.1) 0 a (Real.sqrt (1 - t) • L₀ + L₀')
          (fun p => Real.sqrt (1 - t) • L p + L' p) ω.2.1
          (branchMarks κ ω.2.2 (truncBranchCoe κ M x.2)) x.1 := by
  set m := branchMarks κ ω.2.2 (truncBranchCoe κ M x.2) with hm
  have hK : ∀ l i, pairBranchMark N κ (Real.sqrt (1 - t) • L₀ + L₀')
      (fun p => Real.sqrt (1 - t) • L p + L' p) ω.2.1 m l i
      = Real.sqrt (1 - t) * pairBranchMark N κ L₀ L ω.2.1 m l i
        + pairBranchMark N κ L₀' L' ω.2.1 m l i := fun l i =>
    (pairBranchMark_smul_add N (Real.sqrt (1 - t)) L₀ L₀' L L' ω.2.1 m l i).symm
  have hsum : ∑ l : Fin 2, ∑ i, isingSpin (x.1 l i) * (a (i, l)
        + (Real.sqrt (1 - t) * pairBranchMark N κ L₀ L ω.2.1 m l i
          + pairBranchMark N κ L₀' L' ω.2.1 m l i))
      = (∑ l : Fin 2, ∑ i, isingSpin (x.1 l i) * a (i, l))
        + Real.sqrt (1 - t) * ∑ l : Fin 2, ∑ i, isingSpin (x.1 l i)
            * pairBranchMark N κ L₀ L ω.2.1 m l i
        + ∑ l : Fin 2, ∑ i, isingSpin (x.1 l i) * pairBranchMark N κ L₀' L' ω.2.1 m l i := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm (Real.sqrt (1 - t))]
    ring
  unfold coupledTruncHam pairBranchHamX coupledExtField
  rw [gaussianInterp_apply]
  simp only [pair, coupledModelField, coupledTreeField, GaussianField.prodLeft_U,
    GaussianField.prodRight_U, pairModelFieldOverlap, GaussianField.copy_U,
    GaussianField.pairModel_U, pairTreeField_U, pairFieldHam, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, pairTreeLin_siteTreeCoords_apply, truncMarks_branchNode_fun, ← hm, hK, hsum]
  ring

/-! ### The constrained weights -/

/-- The constraint `1_{R_{1,2} = u}` of (14.125), as a weight on the pairs of configurations. -/
def constraintR (u : ℝ) (σ : Fin 2 → Config N) : ℝ :=
  if overlap N (σ 0) (σ 1) = u then 1 else 0

lemma constraintR_nonneg (u : ℝ) (σ : Fin 2 → Config N) : 0 ≤ constraintR N u σ := by
  unfold constraintR
  split_ifs <;> norm_num

lemma constraintR_le_one (u : ℝ) (σ : Fin 2 → Config N) : constraintR N u σ ≤ 1 := by
  unfold constraintR
  split_ifs <;> norm_num

lemma overlap_eq_of_constraintR_ne_zero {u : ℝ} {σ : Fin 2 → Config N}
    (h : constraintR N u σ ≠ 0) : overlap N (σ 0) (σ 1) = u := by
  unfold constraintR at h
  by_contra hc
  exact h (by rw [ite_eq_right hc])

lemma constraintR_pos_of_overlap_eq {u : ℝ} {σ : Fin 2 → Config N}
    (h : overlap N (σ 0) (σ 1) = u) : 0 < constraintR N u σ := by
  unfold constraintR
  rw [ite_eq_left h]
  exact one_pos

/-- The weights `u*_α 1_{R_{1,2} = u}` of the coupled scheme on the truncated tree. -/
def coupledWt (M : ℕ) (w : CascadeWeights κ) (u : ℝ) : PairConfig N (TruncBranch κ M) → ℝ :=
  fun p => truncWt κ M w p.2 * constraintR N u p.1

lemma coupledWt_nonneg (M : ℕ) (w : CascadeWeights κ) (u : ℝ) (p : PairConfig N (TruncBranch κ M)) :
    0 ≤ coupledWt N M w u p :=
  mul_nonneg (truncWt_nonneg κ M w p.2) (constraintR_nonneg N u p.1)

lemma overlap_eq_of_coupledWt_ne_zero (M : ℕ) (w : CascadeWeights κ) (u : ℝ)
    {p : PairConfig N (TruncBranch κ M)} (h : coupledWt N M w u p ≠ 0) :
    overlap N (p.1 0) (p.1 1) = u :=
  overlap_eq_of_constraintR_ne_zero N (right_ne_zero_of_mul h)

lemma exists_coupledWt_ne_zero (M : ℕ) (w : CascadeWeights κ) (u : ℝ)
    (hne : ∃ β : TruncBranch κ M, truncWt κ M w β ≠ 0)
    (hu : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    ∃ p, coupledWt N M w u p ≠ 0 := by
  obtain ⟨β, hβ⟩ := hne
  obtain ⟨σ, hσ⟩ := hu
  exact ⟨(σ, β), mul_ne_zero hβ (constraintR_pos_of_overlap_eq N hσ).ne'⟩

/-! ### The branch partition functions and the level sum -/

/-- The constrained partial partition function of the interpolating Hamiltonian at the branch `α`
is the branch function `pairBranchZX`. -/
lemma wCondZ_coupledTruncHam (M : ℕ) (t : ℝ) (ξ : ℝ → ℝ)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (L₀ L₀' : Fin 2 → J → ℝ) (L L' : Fin κ → Fin 2 → J → ℝ)
    (a : Fin N × Fin 2 → ℝ) (c : (Fin 2 → Config N) → ℝ) (ω : Ω × SiteMarksSpace (Fin N × J) κ)
    (α : TruncBranch κ M) :
    wCondZ c (coupledTruncHam N M t ξ G₀ v₀ vs L₀ L₀' L L' a ω) α
      = pairBranchZX N κ c (Real.sqrt t • G₀.U ω.1) 0 a (Real.sqrt (1 - t) • L₀ + L₀')
          (fun p => Real.sqrt (1 - t) • L p + L' p) ω.2.1
          (branchMarks κ ω.2.2 (truncBranchCoe κ M α)) := by
  unfold wCondZ pairBranchZX
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [coupledTruncHam_apply]

/-- **The integrand of Lemma 14.6.1 as a level sum** (Talagrand's reduction of
`⟨θ(ρ_{(α,γ)})⟩_s` to the cascade pair fractions, (14.137)): with the weights `u*_α 1_{R = u}`,
`(1/2) c₀ + (1/2) ⟨θ(ρ_{(α,γ)})⟩_s = levelBound κ c₀ θ (truncPair …)` for the branch weights
`exp F_s(α) = pairBranchZX(1_{R=u}, …)`. -/
theorem treeBoundIntegrand_coupled_eq_levelBound (M : ℕ) (t : ℝ) (ξ : ℝ → ℝ)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (L₀ L₀' : Fin 2 → J → ℝ) (L L' : Fin κ → Fin 2 → J → ℝ)
    (a : Fin N × Fin 2 → ℝ) (w : CascadeWeights κ) (hw : ∀ α, branchWeight κ w α ≠ ∞) (u : ℝ)
    (c₀ : ℝ) (θ : ℕ → ℝ) (ω : Ω × SiteMarksSpace (Fin N × J) κ) :
    treeBoundIntegrand (coupledWt N M w u) c₀ (fun x y => θ (branchLevel x.2 y.2))
        (coupledTruncHam N M t ξ G₀ v₀ vs L₀ L₀' L L' a ω)
      = levelBound κ c₀ θ (fun r => truncPair κ M r
          (pairHamG N κ (constraintR N u) (Real.sqrt t • G₀.U ω.1) 0 a
            (Real.sqrt (1 - t) • L₀ + L₀') (fun p => Real.sqrt (1 - t) • L p + L' p) ω.2.1)
          w ω.2.2) := by
  refine treeBoundIntegrand_prod_eq_levelBound κ M (constraintR N u)
    (coupledTruncHam N M t ξ G₀ v₀ vs L₀ L₀' L L' a ω) c₀ θ w hw ω.2.2 _
    (fun α => ?_) (fun α => ?_)
  · rw [pairHamG, wCondZ_coupledTruncHam]
  · rw [wCondZ_coupledTruncHam]
    exact pairBranchZX_nonneg N κ (constraintR_nonneg N u) _ _ _ _ _ _ _

end

end SpinGlass
