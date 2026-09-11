/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.TreeFieldLaw
import SpinGlass.Parisi.TreeTrace
import SpinGlass.FiniteGibbs.GaussianFieldCoords

/-!
# The Gaussian field of the marks of a truncated cascade

Talagrand, Vol. II, (14.73)–(14.74): the Hamiltonian `-H(σ, α) = ∑ᵢ σᵢ ∑_{0 ≤ p ≤ k} z_{i,p,α}`
of the branch `α`, where `z_{i,0,α} = z_{i,0}` and `z_{i,p,α}` is the mark of the node `α|_p`,
is a centered Gaussian field on `Σ_N × A` with covariance
`(1/N) 𝔼 H(σ¹,α) H(σ²,γ) = R_{1,2} ∑_{p < (α,γ)} 𝔼 z_p²`.

Here the branches are those of the tree truncated to indices `< M` (`TruncBranch`), the field
is the linear image `treeLin` of the Gaussian coordinates `treeCoords` of `TreeFieldLaw`, and
`treeField` packages it as a `GaussianField` with kernel `(∑ᵢ σᵢτᵢ) · treeCov α γ`, where
`treeCov α γ = v₀ + ∑_{p : α|_{p+1} = γ|_{p+1}} v_p` (`sum_coordVar_treeCoeff`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k M : ℕ)

/-- The branches of the truncated tree. -/
abbrev TruncBranch (k M : ℕ) : Type := Fin k → Fin M × Fin M

/-- The node of depth `p + 1` along a truncated branch. -/
def branchNode (α : TruncBranch k M) (p : Fin k) : TruncNode k M :=
  ⟨p, fun i => α ⟨i.val, by omega⟩⟩

omit N in
lemma branchNode_eq_iff (α γ : TruncBranch k M) (p : Fin k) :
    branchNode k M α p = branchNode k M γ p
      ↔ (fun i : Fin (p.val + 1) => α ⟨i.val, by omega⟩)
        = fun i : Fin (p.val + 1) => γ ⟨i.val, by omega⟩ := by
  simp [branchNode]

/-- The coefficients of the field: `A (σ,α) (inl i) = σᵢ`,
`A (σ,α) (inr (v, i)) = σᵢ · 1_{v = α|_{v.1+1}}`. -/
def treeCoeff (x : Config N × TruncBranch k M) : TreeCoord N k M → ℝ :=
  Sum.elim (fun i => isingSpin (x.1 i))
    fun c => if c.1 = branchNode k M x.2 c.1.1 then isingSpin (x.1 c.2) else 0

/-- The field as a continuous linear map of the coordinates: `(L w)(σ, α) = ∑_c A (σ,α) c · w c`. -/
abbrev treeLin : EuclideanSpace ℝ (TreeCoord N k M) →L[ℝ]
    FiniteGibbs.EnergySpace (Config N × TruncBranch k M) :=
  coordLin (treeCoeff N k M)

lemma treeLin_apply (w : EuclideanSpace ℝ (TreeCoord N k M)) (x : Config N × TruncBranch k M) :
    treeLin N k M w x = ∑ c, treeCoeff N k M x c * w c := rfl

/-- The adjoint on Dirac vectors: `L† e_x = A x`. -/
lemma adjoint_treeLin_std_basis (x : Config N × TruncBranch k M) :
    (treeLin N k M).adjoint (FiniteGibbs.std_basis (α := Config N × TruncBranch k M) x)
      = WithLp.toLp 2 (treeCoeff N k M x) :=
  adjoint_coordLin_std_basis _ x

omit N in
/-- Summing over the truncated nodes an indicator "`v` is a node of `α`" collapses to a sum over
the depths. -/
lemma sum_truncNode_branchNode (α : TruncBranch k M) (g : TruncNode k M → ℝ) :
    ∑ v : TruncNode k M, (if v = branchNode k M α v.1 then g v else 0)
      = ∑ p : Fin k, g (branchNode k M α p) := by
  classical
  rw [Fintype.sum_sigma (f := fun v : TruncNode k M => if v = branchNode k M α v.1 then g v else 0)]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [branchNode, Sigma.mk.injEq, heq_iff_eq, true_and]
  rw [Finset.sum_eq_single (fun i : Fin (p.val + 1) => α ⟨i.val, by omega⟩)]
  · rw [ite_eq_left rfl]
  · intro u _ hu
    rw [ite_eq_right hu]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The mark of a branch at a site: `z₀ᵢ + ∑ₚ z_{i,p,α}`. -/
def treeMark (ω : MarksSpace N k) (α : TruncBranch k M) (i : Fin N) : ℝ :=
  ω.1 i + ∑ p : Fin k, truncMarks k M ω.2 (branchNode k M α p) i

/-- The field at `(σ, α)` is `∑ᵢ σᵢ (z₀ᵢ + ∑ₚ z_{i,p,α})`, Talagrand's (14.73). -/
theorem treeLin_treeCoords_apply (ω : MarksSpace N k) (x : Config N × TruncBranch k M) :
    treeLin N k M (treeCoords N k M ω) x = ∑ i, isingSpin (x.1 i) * treeMark N k M ω x.2 i := by
  classical
  rw [treeLin_apply, Fintype.sum_sum_type (f := fun c => treeCoeff N k M x c
    * treeCoords N k M ω c)]
  rw [Fintype.sum_prod_type (f := fun c : TruncNode k M × Fin N =>
    treeCoeff N k M x (Sum.inr c) * treeCoords N k M ω (Sum.inr c))]
  simp only [treeCoeff, treeCoords, siteTreeCoords, Sum.elim_inl, Sum.elim_inr, treeMark, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsum : (∑ v : TruncNode k M, (if v = branchNode k M x.2 v.1 then isingSpin (x.1 i) else 0)
      * truncMarks k M ω.2 v i)
      = ∑ v : TruncNode k M, (if v = branchNode k M x.2 v.1
          then isingSpin (x.1 i) * truncMarks k M ω.2 v i else 0) := by
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : v = branchNode k M x.2 v.1
    · rw [ite_eq_left hv, ite_eq_left hv]
    · rw [ite_eq_right hv, ite_eq_right hv, zero_mul]
  rw [hsum, sum_truncNode_branchNode]

/-! ### The tree covariance -/

/-- The covariance of two branches: `v₀ + ∑_{p : α|_{p+1} = γ|_{p+1}} v_p`. -/
def treeCov (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) (α γ : TruncBranch k M) : ℝ :=
  (v₀ : ℝ) + ∑ p : Fin k, if branchNode k M α p = branchNode k M γ p then (vs p : ℝ) else 0

omit N in
/-- Summing over the truncated nodes an indicator of "`v` is the node of depth `v.1 + 1` of both
`α` and `γ`" collapses to a sum over the depths. -/
lemma sum_truncNode_ite (α γ : TruncBranch k M) (f : Fin k → ℝ) :
    ∑ v : TruncNode k M, (if branchNode k M α v.1 = branchNode k M γ v.1 ∧ v = branchNode k M α v.1
        then f v.1 else 0)
      = ∑ p : Fin k, if branchNode k M α p = branchNode k M γ p then f p else 0 := by
  classical
  rw [Fintype.sum_sigma (f := fun v : TruncNode k M =>
    if branchNode k M α v.1 = branchNode k M γ v.1 ∧ v = branchNode k M α v.1 then f v.1 else 0)]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [branchNode, Sigma.mk.injEq, heq_iff_eq, true_and]
  by_cases h : (fun i : Fin (p.val + 1) => α ⟨i.val, by omega⟩)
      = fun i : Fin (p.val + 1) => γ ⟨i.val, by omega⟩
  · simp only [h, true_and, ite_true]
    rw [Finset.sum_ite_eq']
    simp
  · simp [h]

/-- **The covariance of the field**: `∑_c var_c A x c A y c = (∑ᵢ σᵢ τᵢ) · treeCov α γ`. -/
theorem sum_coordVar_treeCoeff (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) (x y : Config N × TruncBranch k M) :
    ∑ c, (coordVar N k M v₀ vs c : ℝ) * treeCoeff N k M x c * treeCoeff N k M y c
      = (∑ i, isingSpin (x.1 i) * isingSpin (y.1 i)) * treeCov k M v₀ vs x.2 y.2 := by
  classical
  rw [Fintype.sum_sum_type (f := fun c => (coordVar N k M v₀ vs c : ℝ) * treeCoeff N k M x c
    * treeCoeff N k M y c)]
  rw [Fintype.sum_prod_type (f := fun c : TruncNode k M × Fin N =>
    (coordVar N k M v₀ vs (Sum.inr c) : ℝ) * treeCoeff N k M x (Sum.inr c)
      * treeCoeff N k M y (Sum.inr c))]
  simp only [coordVar, siteCoordVar, treeCoeff, Sum.elim_inl, Sum.elim_inr]
  have hinner : ∀ v : TruncNode k M, (∑ i, (vs v.1 : ℝ)
      * (if v = branchNode k M x.2 v.1 then isingSpin (x.1 i) else 0)
      * (if v = branchNode k M y.2 v.1 then isingSpin (y.1 i) else 0))
      = (if branchNode k M x.2 v.1 = branchNode k M y.2 v.1 ∧ v = branchNode k M x.2 v.1
          then (vs v.1 : ℝ) else 0) * ∑ i, isingSpin (x.1 i) * isingSpin (y.1 i) := by
    intro v
    by_cases hx : v = branchNode k M x.2 v.1
    · by_cases hy : v = branchNode k M y.2 v.1
      · have hxy : branchNode k M x.2 v.1 = branchNode k M y.2 v.1 := hx.symm.trans hy
        simp only [ite_eq_left hx, ite_eq_left hy, ite_eq_left (And.intro hxy hx), Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      · have hxy : ¬ (branchNode k M x.2 v.1 = branchNode k M y.2 v.1
            ∧ v = branchNode k M x.2 v.1) :=
          fun h => hy (hx.trans h.1)
        simp only [ite_eq_left hx, ite_eq_right hy, ite_eq_right hxy, mul_zero,
          Finset.sum_const_zero, zero_mul]
    · have hxy : ¬ (branchNode k M x.2 v.1 = branchNode k M y.2 v.1 ∧ v = branchNode k M x.2 v.1) :=
        fun h => hx h.2
      simp only [ite_eq_right hx, ite_eq_right hxy, mul_zero, zero_mul, Finset.sum_const_zero]
  simp_rw [hinner]
  rw [← Finset.sum_mul, sum_truncNode_ite k M x.2 y.2 (fun p => (vs p : ℝ))]
  unfold treeCov
  rw [mul_add, Finset.sum_mul]
  congr 1
  · rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => mul_comm _ _

/-! ### The Gaussian field -/

/-- The kernel of the marks field: `(∑ᵢ σᵢ τᵢ) · treeCov α γ`. -/
def treeFieldKernel (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) (x y : Config N × TruncBranch k M) : ℝ :=
  (∑ i, isingSpin (x.1 i) * isingSpin (y.1 i)) * treeCov k M v₀ vs x.2 y.2

lemma isGaussian_marksLaw_map_treeCoords (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) :
    IsGaussian ((marksLaw N k v₀ vs).map (treeCoords N k M)) := by
  rw [treeCoords_law]
  infer_instance

/-- **The marks field of the truncated cascade**, Talagrand's `H(σ, α)` of (14.73), as a centered
Gaussian field on `Σ_N × A` with kernel `(∑ᵢ σᵢ τᵢ) · treeCov α γ`: the linear image
(`GaussianField.ofCoords`) of the independent coordinates `treeCoords`. -/
def treeField (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) :
    GaussianField (α := Config N × TruncBranch k M) (marksLaw N k v₀ vs)
      (treeFieldKernel N k M v₀ vs) :=
  (GaussianField.ofCoords (treeCoeff N k M) (coordVar N k M v₀ vs) (treeCoords N k M)
    (measurable_treeCoords N k M) (treeCoords_law N k M v₀ vs)).copy _
    fun x y => (sum_coordVar_treeCoeff N k M v₀ vs x y).symm

@[simp] lemma treeField_U (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) (ω : MarksSpace N k) :
    (treeField N k M v₀ vs).U ω = treeLin N k M (treeCoords N k M ω) := rfl

end

end SpinGlass
