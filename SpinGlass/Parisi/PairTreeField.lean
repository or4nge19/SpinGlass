/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.SiteTreeFieldLaw
import SpinGlass.FiniteGibbs.GaussianFieldCoords
import SpinGlass.Parisi.TreeCov
import SpinGlass.Parisi.CoupledTrace

/-!
# The Gaussian field of the coupled copies: the interpolating Hamiltonian of (14.135)

Talagrand, Vol. II, §14.6, (14.130)–(14.135). At each level `p` of the tree a pair of centered
Gaussians `(y_p^1, y_p^2)` with covariance `𝔼 y_p^ℓ y_p^{ℓ'} = ξ'(ρ_{p+1}^{ℓ,ℓ'}) - ξ'(ρ_p^{ℓ,ℓ'})`
is attached to every site and every node; the Hamiltonian of the pair `(σ¹, σ²)` on the branch
`α` is `H(σ¹, σ², α) = ∑_{ℓ} ∑_i σ_i^ℓ ∑_p y^ℓ_{i,p,α|_p}`, and its covariance is (14.127),
`(1/N) 𝔼 H(σ¹,σ²,α) H(τ¹,τ²,γ) = ∑_{ℓ,ℓ'} R^{ℓ,ℓ'} ξ'(ρ^{ℓ,ℓ'}_{(α,γ)})`.

A centered Gaussian pair with covariance `C` is `L g` for independent standard Gaussians `g` and
any `L` with `L Lᵀ = C`, so the field is the linear image (`GaussianField.ofCoords`) of the
independent coordinates of a cascade with site type `Fin N × Fin 2` (`SiteTreeFieldLaw`), with
per-level factors `L₀`, `L_p` (`pairTreeCoeff`), and its kernel is
`∑_{ℓ,ℓ'} (∑_i σ_i^ℓ τ_i^{ℓ'}) · pairTreeCov ℓ ℓ' α γ` with
`pairTreeCov ℓ ℓ' α γ = v₀ (L₀L₀ᵀ)_{ℓℓ'} + ∑_{p : α|_{p+1} = γ|_{p+1}} v_p (L_pL_pᵀ)_{ℓℓ'}`
(`sum_coordVar_pairTreeCoeff`). When the per-level covariances are the increments of `ξ' ∘ ρ`,
the sum telescopes to `ξ'(ρ^{ℓ,ℓ'}_{(α,γ)})` and the kernel is `pairTreeKernel`
(`pairTreeFieldKernel_eq_pairTreeKernel`), the hypothesis of Lemma 14.6.1.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k M : ℕ)

/-! ### An algebraic identity -/

omit N k M in
/-- The Gram entries `(L Lᵀ)_{ℓℓ'} = ∑_j L ℓ j L ℓ' j`. -/
def gram {J : Type*} [Fintype J] (L : Fin 2 → J → ℝ) (l l' : Fin 2) : ℝ := ∑ j, L l j * L l' j

omit N k M in
/-- `∑_{i,j} v (∑_ℓ a_ℓ(i) L_{ℓj})(∑_{ℓ'} b_{ℓ'}(i) L_{ℓ'j})
  = ∑_{ℓ,ℓ'} (∑_i a_ℓ(i) b_{ℓ'}(i)) · v (LLᵀ)_{ℓℓ'}`. -/
lemma sum_prod_mul_sum_mul_sum {ι J : Type*} [Fintype ι] [Fintype J] (v : ℝ)
    (a b : Fin 2 → ι → ℝ) (L : Fin 2 → J → ℝ) :
    ∑ c : ι × J, v * (∑ l, a l c.1 * L l c.2) * (∑ l', b l' c.1 * L l' c.2)
      = ∑ l, ∑ l', (∑ i, a l i * b l' i) * (v * gram L l l') := by
  have h1 : ∀ c : ι × J, v * (∑ l, a l c.1 * L l c.2) * (∑ l', b l' c.1 * L l' c.2)
      = ∑ l, ∑ l', v * (a l c.1 * L l c.2) * (b l' c.1 * L l' c.2) := by
    intro c
    rw [mul_assoc, sum_mul_sum, mul_sum]
    refine sum_congr rfl fun l _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun l' _ => ?_
    ring
  simp_rw [h1]
  rw [sum_comm]
  refine sum_congr rfl fun l _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun l' _ => ?_
  rw [Fintype.sum_prod_type, gram, mul_sum, sum_mul]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  ring

/-! ### The coefficients and the covariance -/

/-- The coefficients of the coupled field with per-level factors `L₀`, `L`: at a level-`0`
coordinate `(i, j)` the value `∑_ℓ σ_i^ℓ (L₀)_{ℓj}`, at a node coordinate `(v, (i, j))` the value
`∑_ℓ σ_i^ℓ (L_{v.1})_{ℓj}` if `v` is the node of `α` at its depth and `0` otherwise. -/
def pairTreeCoeff (L₀ : Fin 2 → Fin 2 → ℝ) (L : Fin k → Fin 2 → Fin 2 → ℝ)
    (x : PairConfig N (TruncBranch k M)) : SiteTreeCoord (Fin N × Fin 2) k M → ℝ :=
  Sum.elim (fun c => ∑ l : Fin 2, isingSpin (x.1 l c.1) * L₀ l c.2)
    fun c => if c.1 = branchNode k M x.2 c.1.1
      then ∑ l : Fin 2, isingSpin (x.1 l c.2.1) * L c.1.1 l c.2.2 else 0

omit N in
/-- The covariance of two branches for the copies `ℓ, ℓ'`:
`v₀ (L₀L₀ᵀ)_{ℓℓ'} + ∑_{p : α|_{p+1} = γ|_{p+1}} v_p (L_pL_pᵀ)_{ℓℓ'}`. -/
def pairTreeCov (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) (L₀ : Fin 2 → Fin 2 → ℝ)
    (L : Fin k → Fin 2 → Fin 2 → ℝ) (l l' : Fin 2) (α γ : TruncBranch k M) : ℝ :=
  (v₀ : ℝ) * gram L₀ l l'
    + ∑ p : Fin k, if branchNode k M α p = branchNode k M γ p then (vs p : ℝ) * gram (L p) l l'
        else 0

/-- **The covariance of the coupled field**:
`∑_c var_c A x c A y c = ∑_{ℓ,ℓ'} (∑_i σ_i^ℓ τ_i^{ℓ'}) · pairTreeCov ℓ ℓ' α γ`. -/
theorem sum_coordVar_pairTreeCoeff (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) (L₀ : Fin 2 → Fin 2 → ℝ)
    (L : Fin k → Fin 2 → Fin 2 → ℝ) (x y : PairConfig N (TruncBranch k M)) :
    ∑ c, (siteCoordVar (Fin N × Fin 2) k M v₀ vs c : ℝ) * pairTreeCoeff N k M L₀ L x c
        * pairTreeCoeff N k M L₀ L y c
      = ∑ l : Fin 2, ∑ l' : Fin 2, (∑ i, isingSpin (x.1 l i) * isingSpin (y.1 l' i))
          * pairTreeCov k M v₀ vs L₀ L l l' x.2 y.2 := by
  classical
  rw [Fintype.sum_sum_type (f := fun c => (siteCoordVar (Fin N × Fin 2) k M v₀ vs c : ℝ)
    * pairTreeCoeff N k M L₀ L x c * pairTreeCoeff N k M L₀ L y c)]
  rw [Fintype.sum_prod_type (f := fun c : TruncNode k M × (Fin N × Fin 2) =>
    (siteCoordVar (Fin N × Fin 2) k M v₀ vs (Sum.inr c) : ℝ)
      * pairTreeCoeff N k M L₀ L x (Sum.inr c) * pairTreeCoeff N k M L₀ L y (Sum.inr c))]
  simp only [siteCoordVar, pairTreeCoeff, Sum.elim_inl, Sum.elim_inr]
  -- the level-`0` block
  rw [sum_prod_mul_sum_mul_sum (v₀ : ℝ) (fun l i => isingSpin (x.1 l i))
    (fun l i => isingSpin (y.1 l i)) L₀]
  -- the node blocks
  have hinner : ∀ v : TruncNode k M,
      (∑ c : Fin N × Fin 2, (vs v.1 : ℝ)
        * (if v = branchNode k M x.2 v.1 then ∑ l : Fin 2, isingSpin (x.1 l c.1) * L v.1 l c.2
            else 0)
        * (if v = branchNode k M y.2 v.1 then ∑ l : Fin 2, isingSpin (y.1 l c.1) * L v.1 l c.2
            else 0))
      = ∑ l : Fin 2, ∑ l' : Fin 2, (∑ i, isingSpin (x.1 l i) * isingSpin (y.1 l' i))
          * (if branchNode k M x.2 v.1 = branchNode k M y.2 v.1 ∧ v = branchNode k M x.2 v.1
              then (vs v.1 : ℝ) * gram (L v.1) l l' else 0) := by
    intro v
    by_cases hx : v = branchNode k M x.2 v.1
    · by_cases hy : v = branchNode k M y.2 v.1
      · have hxy : branchNode k M x.2 v.1 = branchNode k M y.2 v.1 := hx.symm.trans hy
        simp only [ite_eq_left hx, ite_eq_left hy, ite_eq_left (And.intro hxy hx)]
        exact sum_prod_mul_sum_mul_sum (vs v.1 : ℝ) (fun l i => isingSpin (x.1 l i))
          (fun l i => isingSpin (y.1 l i)) (L v.1)
      · have hxy : ¬ (branchNode k M x.2 v.1 = branchNode k M y.2 v.1
            ∧ v = branchNode k M x.2 v.1) := fun h => hy (hx.trans h.1)
        simp only [ite_eq_left hx, ite_eq_right hy, ite_eq_right hxy, mul_zero, sum_const_zero]
    · have hxy : ¬ (branchNode k M x.2 v.1 = branchNode k M y.2 v.1
          ∧ v = branchNode k M x.2 v.1) := fun h => hx h.2
      simp only [ite_eq_right hx, ite_eq_right hxy, mul_zero, zero_mul, sum_const_zero]
  simp_rw [hinner]
  have hnode : (∑ v : TruncNode k M, ∑ l : Fin 2, ∑ l' : Fin 2,
        (∑ i, isingSpin (x.1 l i) * isingSpin (y.1 l' i))
          * (if branchNode k M x.2 v.1 = branchNode k M y.2 v.1 ∧ v = branchNode k M x.2 v.1
              then (vs v.1 : ℝ) * gram (L v.1) l l' else 0))
      = ∑ l : Fin 2, ∑ l' : Fin 2, (∑ i, isingSpin (x.1 l i) * isingSpin (y.1 l' i))
          * ∑ v : TruncNode k M,
              (if branchNode k M x.2 v.1 = branchNode k M y.2 v.1 ∧ v = branchNode k M x.2 v.1
                then (vs v.1 : ℝ) * gram (L v.1) l l' else 0) := by
    rw [sum_comm]
    refine sum_congr rfl fun l _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun l' _ => ?_
    rw [← mul_sum]
  rw [hnode, ← sum_add_distrib]
  refine sum_congr rfl fun l _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun l' _ => ?_
  rw [sum_truncNode_ite k M x.2 y.2 (fun p => (vs p : ℝ) * gram (L p) l l'), pairTreeCov, mul_add]

/-! ### The Gaussian field -/

/-- The kernel of the coupled marks field. -/
def pairTreeFieldKernel (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) (L₀ : Fin 2 → Fin 2 → ℝ)
    (L : Fin k → Fin 2 → Fin 2 → ℝ) (x y : PairConfig N (TruncBranch k M)) : ℝ :=
  ∑ l : Fin 2, ∑ l' : Fin 2, (∑ i, isingSpin (x.1 l i) * isingSpin (y.1 l' i))
    * pairTreeCov k M v₀ vs L₀ L l l' x.2 y.2

/-- **The interpolating Hamiltonian of the coupled copies** (Talagrand's (14.135)), as a centered
Gaussian field on the pairs with kernel `pairTreeFieldKernel`. -/
def pairTreeField (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) (L₀ : Fin 2 → Fin 2 → ℝ)
    (L : Fin k → Fin 2 → Fin 2 → ℝ) :
    GaussianField (α := PairConfig N (TruncBranch k M)) (siteMarksLaw (Fin N × Fin 2) k v₀ vs)
      (pairTreeFieldKernel N k M v₀ vs L₀ L) :=
  (GaussianField.ofCoords (pairTreeCoeff N k M L₀ L) (siteCoordVar (Fin N × Fin 2) k M v₀ vs)
    (siteTreeCoords (Fin N × Fin 2) k M) (measurable_siteTreeCoords _ k M)
    (siteTreeCoords_law _ k M v₀ vs)).copy _
    fun x y => (sum_coordVar_pairTreeCoeff N k M v₀ vs L₀ L x y).symm

/-! ### The telescoping identity and the kernel of (14.127) -/

omit N in
/-- When the per-level covariances are the increments of `ξ' ∘ ρ^{ℓ,ℓ'}` (Talagrand's (14.130)),
the branch covariance telescopes: `pairTreeCov ℓ ℓ' α γ = ξ'(ρ^{ℓ,ℓ'}_{(α,γ)}) - ξ'(ρ^{ℓ,ℓ'}_0)`. -/
theorem pairTreeCov_eq_deriv (ξ : ℝ → ℝ) (ρ : Fin 2 → Fin 2 → ℕ → ℝ) (v₀ : ℝ≥0)
    (vs : Fin k → ℝ≥0) (L₀ : Fin 2 → Fin 2 → ℝ) (L : Fin k → Fin 2 → Fin 2 → ℝ)
    (hC0 : ∀ l l', (v₀ : ℝ) * gram L₀ l l' = deriv ξ (ρ l l' 1) - deriv ξ (ρ l l' 0))
    (hC : ∀ (p : Fin k) l l', (vs p : ℝ) * gram (L p) l l'
      = deriv ξ (ρ l l' (p.val + 2)) - deriv ξ (ρ l l' (p.val + 1)))
    (l l' : Fin 2) (α γ : TruncBranch k M) :
    pairTreeCov k M v₀ vs L₀ L l l' α γ
      = deriv ξ (ρ l l' (branchLevel α γ + 1)) - deriv ξ (ρ l l' 0) := by
  classical
  unfold pairTreeCov
  simp_rw [branchNode_eq_iff_lt_branchLevel, hC]
  have hlev := branchLevel_le α γ
  rw [hC0]
  have hsum : (∑ p : Fin k, if p.val < branchLevel α γ
        then deriv ξ (ρ l l' (p.val + 2)) - deriv ξ (ρ l l' (p.val + 1)) else 0)
      = ∑ i ∈ range (branchLevel α γ),
          (deriv ξ (ρ l l' (i + 2)) - deriv ξ (ρ l l' (i + 1))) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => if i < branchLevel α γ
      then deriv ξ (ρ l l' (i + 2)) - deriv ξ (ρ l l' (i + 1)) else 0) k, ← sum_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_range]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨by omega, h⟩
  rw [hsum, sum_range_sub (fun i => deriv ξ (ρ l l' (i + 1)))]
  ring

/-- **The kernel of the coupled marks field is the kernel of (14.127)**,
`N ∑_{ℓ,ℓ'} R^{ℓ,ℓ'} ξ'(ρ^{ℓ,ℓ'}_{(α,γ)})`, when `ρ^{ℓ,ℓ'}_0 = 0`, `ξ'(0) = 0` and the per-level
covariances are the increments of `ξ' ∘ ρ`. -/
theorem pairTreeFieldKernel_eq_pairTreeKernel (hN : 0 < N) (ξ : ℝ → ℝ)
    (ρ : Fin 2 → Fin 2 → ℕ → ℝ) (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) (L₀ : Fin 2 → Fin 2 → ℝ)
    (L : Fin k → Fin 2 → Fin 2 → ℝ) (hρ0 : ∀ l l', ρ l l' 0 = 0) (h0 : deriv ξ 0 = 0)
    (hC0 : ∀ l l', (v₀ : ℝ) * gram L₀ l l' = deriv ξ (ρ l l' 1) - deriv ξ (ρ l l' 0))
    (hC : ∀ (p : Fin k) l l', (vs p : ℝ) * gram (L p) l l'
      = deriv ξ (ρ l l' (p.val + 2)) - deriv ξ (ρ l l' (p.val + 1))) :
    pairTreeFieldKernel N k M v₀ vs L₀ L
      = pairTreeKernel N ξ fun α γ l l' => ρ l l' (branchLevel α γ + 1) := by
  funext x y
  unfold pairTreeFieldKernel pairTreeKernel
  rw [mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun l' _ => ?_
  rw [pairTreeCov_eq_deriv k M ξ ρ v₀ vs L₀ L hC0 hC, hρ0, h0, sub_zero]
  have hR : (∑ i, isingSpin (x.1 l i) * isingSpin (y.1 l' i))
      = (N : ℝ) * pairOverlap N x y l l' := by
    unfold pairOverlap overlap overlapOf spinOf
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  rw [hR]
  ring

end

end SpinGlass
