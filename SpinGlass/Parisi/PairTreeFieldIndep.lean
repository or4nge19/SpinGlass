/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.PairTreeField
import Common.Mathlib.Probability.Independence.PiBlocks

/-!
# Independence of coupled tree fields with disjoint factor columns

Two coupled marks fields `pairTreeField` built on the same cascade over the sites `Fin N × J`
are independent when their per-level factors use disjoint sets of columns of `J`
(`indepFun_pairTreeField_of_disjoint`): each field is a function of the coordinates of its own
columns, and disjoint blocks of coordinates of a product of Gaussians are independent
(`ProbabilityTheory.indepFun_restrict_pi`). This is how the external field `H⁰` of Talagrand's
(14.136), a second coupled field attached to the same cascade, is made independent of the
interpolating field of (14.135).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k M : ℕ) {J : Type*} [Fintype J] [DecidableEq J]

/-- The column of a coordinate of the truncated tree over the sites `Fin N × J`. -/
def siteTreeCoordCol (c : SiteTreeCoord (Fin N × J) k M) : J :=
  Sum.elim (fun s => s.2) (fun q => q.2.2) c

omit [Fintype J] [DecidableEq J] in
/-- The coefficients of a coupled field whose factors are supported on the columns satisfying
`p` vanish on the other columns. -/
lemma pairTreeCoeff_eq_zero_of_col {p : J → Prop} {L₀ : Fin 2 → J → ℝ}
    {L : Fin k → Fin 2 → J → ℝ} (hL0 : ∀ l j, ¬ p j → L₀ l j = 0)
    (hL : ∀ q l j, ¬ p j → L q l j = 0) (x : PairConfig N (TruncBranch k M))
    {c : SiteTreeCoord (Fin N × J) k M} (hc : ¬ p (siteTreeCoordCol N k M c)) :
    pairTreeCoeff N k M L₀ L x c = 0 := by
  rcases c with s | q
  · simp only [pairTreeCoeff, Sum.elim_inl]
    exact Finset.sum_eq_zero fun l _ => by rw [hL0 l s.2 hc, mul_zero]
  · simp only [pairTreeCoeff, Sum.elim_inr]
    split_ifs
    · exact Finset.sum_eq_zero fun l _ => by rw [hL q.1.1 l q.2.2 hc, mul_zero]
    · rfl

/-- The linear map reading a field from a block of coordinates. -/
def blockLin (S : Finset (SiteTreeCoord (Fin N × J) k M))
    (A : PairConfig N (TruncBranch k M) → SiteTreeCoord (Fin N × J) k M → ℝ)
    (v : S → ℝ) : FiniteGibbs.EnergySpace (PairConfig N (TruncBranch k M)) :=
  WithLp.toLp 2 fun x => ∑ c : S, A x c * v c

omit [Fintype J] [DecidableEq J] in
lemma measurable_blockLin (S : Finset (SiteTreeCoord (Fin N × J) k M))
    (A : PairConfig N (TruncBranch k M) → SiteTreeCoord (Fin N × J) k M → ℝ) :
    Measurable (blockLin N k M S A) := by
  unfold blockLin
  have h : Continuous fun v : S → ℝ => fun x : PairConfig N (TruncBranch k M) =>
      ∑ c : S, A x c * v c := by fun_prop
  exact ((PiLp.continuous_toLp (p := (2 : ℝ≥0∞))
    (β := fun _ : PairConfig N (TruncBranch k M) => ℝ)).comp h).measurable

omit [DecidableEq J] in
/-- A field whose coefficients are supported on a block `S` of coordinates is the block map of
those coordinates. -/
lemma coordLin_eq_blockLin (S : Finset (SiteTreeCoord (Fin N × J) k M))
    (A : PairConfig N (TruncBranch k M) → SiteTreeCoord (Fin N × J) k M → ℝ)
    (hA : ∀ x c, c ∉ S → A x c = 0) (w : EuclideanSpace ℝ (SiteTreeCoord (Fin N × J) k M)) :
    coordLin A w = blockLin N k M S A (fun c : S => w c) := by
  ext x
  rw [coordLin_apply]
  change _ = ∑ c : S, A x c * w c
  rw [Finset.sum_coe_sort S (fun c => A x c * w c)]
  exact (Finset.sum_subset (Finset.subset_univ S) fun c _ hc => by rw [hA x c hc, zero_mul]).symm

omit [DecidableEq J] in
/-- **Two coupled fields with disjoint factor columns are independent.** -/
theorem indepFun_coordLin_pairTreeCoeff (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) {J₁ : Finset J}
    {L₀ L₀' : Fin 2 → J → ℝ} {L L' : Fin k → Fin 2 → J → ℝ}
    (hL0 : ∀ l j, j ∉ J₁ → L₀ l j = 0) (hL : ∀ p l j, j ∉ J₁ → L p l j = 0)
    (hL0' : ∀ l j, j ∈ J₁ → L₀' l j = 0) (hL' : ∀ p l j, j ∈ J₁ → L' p l j = 0) :
    IndepFun (fun ω => coordLin (pairTreeCoeff N k M L₀ L) (siteTreeCoords (Fin N × J) k M ω))
      (fun ω => coordLin (pairTreeCoeff N k M L₀' L') (siteTreeCoords (Fin N × J) k M ω))
      (siteMarksLaw (Fin N × J) k v₀ vs) := by
  classical
  set S : Finset (SiteTreeCoord (Fin N × J) k M) :=
    univ.filter fun c => siteTreeCoordCol N k M c ∈ J₁ with hS
  set T : Finset (SiteTreeCoord (Fin N × J) k M) :=
    univ.filter fun c => siteTreeCoordCol N k M c ∉ J₁ with hT
  have hST : Disjoint S T := by
    rw [hS, hT, Finset.disjoint_filter]
    exact fun c _ h h' => h' h
  -- the coordinates, as a function with values in `ℝ^C`
  set X : SiteMarksSpace (Fin N × J) k → (SiteTreeCoord (Fin N × J) k M → ℝ) :=
    fun ω => WithLp.ofLp (siteTreeCoords (Fin N × J) k M ω) with hX
  have hofLp : Measurable (WithLp.ofLp : EuclideanSpace ℝ (SiteTreeCoord (Fin N × J) k M)
      → (SiteTreeCoord (Fin N × J) k M → ℝ)) :=
    (PiLp.continuous_ofLp (p := (2 : ℝ≥0∞))
      (β := fun _ : SiteTreeCoord (Fin N × J) k M => ℝ)).measurable
  have hXm : Measurable X := hofLp.comp (measurable_siteTreeCoords (Fin N × J) k M)
  have hlaw : (siteMarksLaw (Fin N × J) k v₀ vs).map X
      = Measure.pi fun c => gaussianReal 0 (siteCoordVar (Fin N × J) k M v₀ vs c) := by
    have hcomp : X = WithLp.ofLp ∘ siteTreeCoords (Fin N × J) k M := rfl
    rw [hcomp, ← Measure.map_map hofLp (measurable_siteTreeCoords (Fin N × J) k M),
      siteTreeCoords_law, Measure.map_map hofLp (PiLp.continuous_toLp (p := (2 : ℝ≥0∞))
        (β := fun _ : SiteTreeCoord (Fin N × J) k M => ℝ)).measurable]
    have hid : (WithLp.ofLp ∘ WithLp.toLp 2 : (SiteTreeCoord (Fin N × J) k M → ℝ) → _) = id := rfl
    rw [hid, Measure.map_id]
  have hind := indepFun_restrict_pi (fun c => gaussianReal 0 (siteCoordVar (Fin N × J) k M v₀ vs c))
    S T hST
  rw [← hlaw] at hind
  have hind' := hind.comp_map hXm
    (measurable_pi_lambda (fun w (c : S) => w c) fun c =>
      measurable_pi_apply (c : SiteTreeCoord (Fin N × J) k M))
    (measurable_pi_lambda (fun w (c : T) => w c) fun c =>
      measurable_pi_apply (c : SiteTreeCoord (Fin N × J) k M))
  have hsuppS : ∀ x c, c ∉ S → pairTreeCoeff N k M L₀ L x c = 0 := fun x c hc =>
    pairTreeCoeff_eq_zero_of_col N k M (p := fun j => j ∈ J₁) hL0 hL x
      (by simpa only [hS, Finset.mem_filter, Finset.mem_univ, true_and] using hc)
  have hsuppT : ∀ x c, c ∉ T → pairTreeCoeff N k M L₀' L' x c = 0 := fun x c hc =>
    pairTreeCoeff_eq_zero_of_col N k M (p := fun j => j ∉ J₁)
      (fun l j hj => hL0' l j (not_not.1 hj)) (fun q l j hj => hL' q l j (not_not.1 hj)) x
      (by simpa only [hT, Finset.mem_filter, Finset.mem_univ, true_and] using hc)
  have e₁ : (fun ω => coordLin (pairTreeCoeff N k M L₀ L) (siteTreeCoords (Fin N × J) k M ω))
      = blockLin N k M S (pairTreeCoeff N k M L₀ L) ∘ ((fun w (c : S) => w c) ∘ X) :=
    funext fun ω => coordLin_eq_blockLin N k M S _ hsuppS _
  have e₂ : (fun ω => coordLin (pairTreeCoeff N k M L₀' L') (siteTreeCoords (Fin N × J) k M ω))
      = blockLin N k M T (pairTreeCoeff N k M L₀' L') ∘ ((fun w (c : T) => w c) ∘ X) :=
    funext fun ω => coordLin_eq_blockLin N k M T _ hsuppT _
  rw [e₁, e₂]
  exact hind'.comp (measurable_blockLin N k M S _) (measurable_blockLin N k M T _)

/-- **Two coupled tree fields with disjoint factor columns are independent.** -/
theorem indepFun_pairTreeField_of_disjoint (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) {J₁ : Finset J}
    {L₀ L₀' : Fin 2 → J → ℝ} {L L' : Fin k → Fin 2 → J → ℝ}
    (hL0 : ∀ l j, j ∉ J₁ → L₀ l j = 0) (hL : ∀ p l j, j ∉ J₁ → L p l j = 0)
    (hL0' : ∀ l j, j ∈ J₁ → L₀' l j = 0) (hL' : ∀ p l j, j ∈ J₁ → L' p l j = 0) :
    (pairTreeField N k M v₀ vs L₀ L).U ⟂ᵢ[siteMarksLaw (Fin N × J) k v₀ vs]
      (pairTreeField N k M v₀ vs L₀' L').U := by
  have e : ∀ (L₀ : Fin 2 → J → ℝ) (L : Fin k → Fin 2 → J → ℝ),
      (pairTreeField N k M v₀ vs L₀ L).U
        = fun ω => coordLin (pairTreeCoeff N k M L₀ L) (siteTreeCoords (Fin N × J) k M ω) :=
    fun L₀ L => funext fun ω => pairTreeField_U N k M v₀ vs L₀ L ω
  rw [e L₀ L, e L₀' L']
  exact indepFun_coordLin_pairTreeCoeff N k M v₀ vs hL0 hL hL0' hL'

end

end SpinGlass
