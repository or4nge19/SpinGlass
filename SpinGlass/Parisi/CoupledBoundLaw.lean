/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.CoupledLevels
import SpinGlass.Parisi.LevelBoundLaw

/-!
# The coupled scheme as an instance of the level-sum bound

The branch functions of the coupled scheme (`coupledG`): the constrained branch partition function
`pairHamG` at time `t`, given the disorder `H_N` and the root marks `z₀`. They are jointly
measurable, positive and have finite Gaussian moments, so the generic layer `LevelBoundLaw`
applies: the bound of Lemma 14.6.1 for the tree truncated at `M` is `truncLevelBoundLaw`
(`integral_treeBoundIntegrand_coupled_eq`), continuous in `t`, and the truncated free-energy
comparison reads (`coupled_truncated`)

`𝔼 F_w(H_N(σ¹) + H_N(σ²) + H⁰) - 𝔼 F_w(H + H⁰) ≤ ∫₀¹ truncLevelBoundLaw … w t dt`,

for the weights `u*_α 1_{R_{1,2} = u}` of the branches `α ∈ A_M`.
-/

open MeasureTheory ProbabilityTheory Finset Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
variable (N : ℕ) {κ : ℕ} {J : Type u} [Fintype J] [DecidableEq J]

/-- The law of the root marks: independent Gaussians of variance `v₀` at every site. -/
abbrev rootMarksLaw (v₀ : ℝ≥0) : Measure (Fin N × J → ℝ) :=
  Measure.pi fun _ : Fin N × J => gaussianReal 0 v₀

/-- **The branch functions of the coupled scheme**: the constrained branch partition function at
time `t`, given the disorder `H_N` and the root marks `z₀`, as a function of the marks along the
branch. -/
def coupledG (u : ℝ) (a : Fin N × Fin 2 → ℝ) (L₀ L₀' : Fin 2 → J → ℝ)
    (L L' : Fin κ → Fin 2 → J → ℝ) (ξ : ℝ → ℝ)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ)) (t : ℝ)
    (θ : Ω × (Fin N × J → ℝ)) (x : Fin κ → Fin N × J → ℝ) : ℝ≥0∞ :=
  pairHamG N κ (constraintR N u) (Real.sqrt t • G₀.U θ.1) 0 a (Real.sqrt (1 - t) • L₀ + L₀')
    (fun p => Real.sqrt (1 - t) • L p + L' p) θ.2 x

/-- The parameters of the branch Hamiltonian at time `t`, from the time, the disorder, the root
marks and the marks along the branch. -/
def coupledParam (L₀ L₀' : Fin 2 → J → ℝ) (L L' : Fin κ → Fin 2 → J → ℝ) (ξ : ℝ → ℝ)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (q : (ℝ × (Ω × (Fin N × J → ℝ))) × (Fin κ → Fin N × J → ℝ)) : PairBranchParam N κ J :=
  ((Real.sqrt q.1.1 • G₀.U q.1.2.1, Real.sqrt (1 - q.1.1) • L₀ + L₀',
    fun p => Real.sqrt (1 - q.1.1) • L p + L' p), (q.1.2.2, q.2))

omit [IsProbabilityMeasure Pm] [Fintype J] [DecidableEq J] in
lemma measurable_coupledParam (L₀ L₀' : Fin 2 → J → ℝ) (L L' : Fin κ → Fin 2 → J → ℝ)
    (ξ : ℝ → ℝ) (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ)) :
    Measurable (coupledParam N L₀ L₀' L L' ξ G₀) := by
  unfold coupledParam
  have ht : Measurable fun q : (ℝ × (Ω × (Fin N × J → ℝ))) × (Fin κ → Fin N × J → ℝ) =>
      q.1.1 := measurable_fst.comp measurable_fst
  have h1 : Measurable fun q : (ℝ × (Ω × (Fin N × J → ℝ))) × (Fin κ → Fin N × J → ℝ) =>
      Real.sqrt q.1.1 • G₀.U q.1.2.1 :=
    (Real.continuous_sqrt.measurable.comp ht).smul
      (G₀.measU.comp (measurable_fst.comp (measurable_snd.comp measurable_fst)))
  have hs : Measurable fun q : (ℝ × (Ω × (Fin N × J → ℝ))) × (Fin κ → Fin N × J → ℝ) =>
      Real.sqrt (1 - q.1.1) := Real.continuous_sqrt.measurable.comp (measurable_const.sub ht)
  have h2 : Measurable fun q : (ℝ × (Ω × (Fin N × J → ℝ))) × (Fin κ → Fin N × J → ℝ) =>
      Real.sqrt (1 - q.1.1) • L₀ + L₀' := by
    refine measurable_pi_lambda _ fun l => measurable_pi_lambda _ fun j => ?_
    change Measurable fun q : (ℝ × (Ω × (Fin N × J → ℝ))) × (Fin κ → Fin N × J → ℝ) =>
      Real.sqrt (1 - q.1.1) * L₀ l j + L₀' l j
    exact (hs.mul_const _).add_const _
  have h3 : Measurable fun q : (ℝ × (Ω × (Fin N × J → ℝ))) × (Fin κ → Fin N × J → ℝ) =>
      fun p => Real.sqrt (1 - q.1.1) • L p + L' p := by
    refine measurable_pi_lambda _ fun p => measurable_pi_lambda _ fun l =>
      measurable_pi_lambda _ fun j => ?_
    change Measurable fun q : (ℝ × (Ω × (Fin N × J → ℝ))) × (Fin κ → Fin N × J → ℝ) =>
      Real.sqrt (1 - q.1.1) * L p l j + L' p l j
    exact (hs.mul_const _).add_const _
  exact (h1.prodMk (h2.prodMk h3)).prodMk
    ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)

omit [IsProbabilityMeasure Pm] [DecidableEq J] in
lemma measurable_coupledG (u : ℝ) (a : Fin N × Fin 2 → ℝ) (L₀ L₀' : Fin 2 → J → ℝ)
    (L L' : Fin κ → Fin 2 → J → ℝ) (ξ : ℝ → ℝ)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ)) :
    Measurable fun q : (ℝ × (Ω × (Fin N × J → ℝ))) × (Fin κ → Fin N × J → ℝ) =>
      coupledG N u a L₀ L₀' L L' ξ G₀ q.1.1 q.1.2 q.2 := by
  have h := (measurable_pairHamG N κ (constraintR N u) 0 a).comp
    (measurable_coupledParam N L₀ L₀' L L' ξ G₀)
  exact h

omit [IsProbabilityMeasure Pm] [DecidableEq J] in
lemma coupledG_pos (u : ℝ) (hu : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u)
    (a : Fin N × Fin 2 → ℝ) (L₀ L₀' : Fin 2 → J → ℝ) (L L' : Fin κ → Fin 2 → J → ℝ)
    (ξ : ℝ → ℝ) (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (t : ℝ) (θ : Ω × (Fin N × J → ℝ)) (x : Fin κ → Fin N × J → ℝ) :
    0 < coupledG N u a L₀ L₀' L L' ξ G₀ t θ x :=
  pairHamG_pos N κ (constraintR_nonneg N u)
    (hu.elim fun σ hσ => ⟨σ, constraintR_pos_of_overlap_eq N hσ⟩) _ _ _ _ _ _ _

omit [IsProbabilityMeasure Pm] [DecidableEq J] in
lemma lintegral_coupledG_ne_top (vs : Fin κ → ℝ≥0) (u : ℝ) (a : Fin N × Fin 2 → ℝ)
    (L₀ L₀' : Fin 2 → J → ℝ) (L L' : Fin κ → Fin 2 → J → ℝ) (ξ : ℝ → ℝ)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ)) (t : ℝ)
    (θ : Ω × (Fin N × J → ℝ)) :
    ∫⁻ x, coupledG N u a L₀ L₀' L L' ξ G₀ t θ x
      ∂Measure.pi (siteGaussianMarks (Fin N × J) κ vs) ≠ ∞ :=
  lintegral_pairHamG_ne_top N κ vs (constraintR_nonneg N u) _ _ _ _ _ _

omit [IsProbabilityMeasure Pm] [DecidableEq J] in
lemma cascadeRec_coupledG_ne_top (ns : Fin κ → ℝ) (vs : Fin κ → ℝ≥0) (hpos : ∀ i, 0 < ns i)
    (hle : ∀ i, ns i ≤ 1) (u : ℝ) (a : Fin N × Fin 2 → ℝ) (L₀ L₀' : Fin 2 → J → ℝ)
    (L L' : Fin κ → Fin 2 → J → ℝ) (ξ : ℝ → ℝ)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ)) (t : ℝ)
    (θ : Ω × (Fin N × J → ℝ)) :
    cascadeRec κ ns (siteGaussianMarks (Fin N × J) κ vs) (coupledG N u a L₀ L₀' L L' ξ G₀ t θ)
      ≠ ∞ :=
  cascadeRec_pairHamG_ne_top N κ ns vs hpos hle (constraintR_nonneg N u) _ _ _ _ _ _

/-! ### The bound of Lemma 14.6.1 as the generic truncated level bound -/

omit [DecidableEq J] in
/-- The marks law is the product of the root law with the cascade marks law, reassociated with
the model law. -/
lemma prod_siteMarksLaw_eq (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) :
    Pm.prod (siteMarksLaw (Fin N × J) κ v₀ vs)
      = ((Pm.prod (rootMarksLaw N v₀)).prod
          (cascadeMarksLaw κ (siteGaussianMarks (Fin N × J) κ vs))).map
            MeasurableEquiv.prodAssoc :=
  (Measure.prodAssoc_prod (μ := Pm) (ν := rootMarksLaw N v₀)
    (τ := cascadeMarksLaw κ (siteGaussianMarks (Fin N × J) κ vs))).symm

lemma measurable_coupledTruncHam (M : ℕ) (t : ℝ) (ξ : ℝ → ℝ)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (L₀ L₀' : Fin 2 → J → ℝ) (L L' : Fin κ → Fin 2 → J → ℝ)
    (a : Fin N × Fin 2 → ℝ) :
    Measurable (coupledTruncHam N M t ξ G₀ v₀ vs L₀ L₀' L L' a) :=
  ((gaussianInterp t).continuous.measurable.comp (measurable_pair _ _)).add
    (measurable_coupledExtField N M v₀ vs L₀' L' a)

/-- **The bound of Lemma 14.6.1 for the truncated tree is the truncated level bound** of the
coupled branch functions. -/
theorem integral_treeBoundIntegrand_coupled_eq (M : ℕ) (t : ℝ) (ξ : ℝ → ℝ)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (L₀ L₀' : Fin 2 → J → ℝ) (L L' : Fin κ → Fin 2 → J → ℝ)
    (a : Fin N × Fin 2 → ℝ) (w : CascadeWeights κ) (hw : ∀ α, branchWeight κ w α ≠ ∞) (u : ℝ)
    (c₀ : ℝ) (θf : ℕ → ℝ) :
    (∫ ω, treeBoundIntegrand (coupledWt N M w u) c₀ (fun x y => θf (branchLevel x.2 y.2))
        (coupledTruncHam N M t ξ G₀ v₀ vs L₀ L₀' L L' a ω)
        ∂Pm.prod (siteMarksLaw (Fin N × J) κ v₀ vs))
      = truncLevelBoundLaw κ (Pm.prod (rootMarksLaw N v₀)) (siteGaussianMarks (Fin N × J) κ vs)
          (coupledG N u a L₀ L₀' L L' ξ G₀) M c₀ θf w t := by
  simp_rw [treeBoundIntegrand_coupled_eq_levelBound N M t ξ G₀ v₀ vs L₀ L₀' L L' a w hw u c₀ θf]
  unfold truncLevelBoundLaw
  have hmeas : Measurable fun ω : Ω × SiteMarksSpace (Fin N × J) κ =>
      levelBound κ c₀ θf (fun r => truncPair κ M r
        (coupledG N u a L₀ L₀' L L' ξ G₀ t (ω.1, ω.2.1)) w ω.2.2) := by
    have := (measurable_levelBound_truncPair_of κ (coupledG N u a L₀ L₀' L L' ξ G₀)
      (measurable_coupledG N u a L₀ L₀' L L' ξ G₀) M c₀ θf w t).comp
      ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd) :
          Measurable fun ω : Ω × SiteMarksSpace (Fin N × J) κ => ((ω.1, ω.2.1), ω.2.2))
    exact this
  change (∫ ω : Ω × SiteMarksSpace (Fin N × J) κ, levelBound κ c₀ θf (fun r => truncPair κ M r
      (coupledG N u a L₀ L₀' L L' ξ G₀ t (ω.1, ω.2.1)) w ω.2.2)
      ∂Pm.prod (siteMarksLaw (Fin N × J) κ v₀ vs)) = _
  rw [prod_siteMarksLaw_eq N v₀ vs, integral_map MeasurableEquiv.prodAssoc.measurable.aemeasurable
    hmeas.aestronglyMeasurable]
  rfl

/-- The truncated level bound of the coupled scheme is continuous in `t`. -/
lemma continuous_truncLevelBoundLaw_coupled (M : ℕ) (ξ : ℝ → ℝ)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (L₀ L₀' : Fin 2 → J → ℝ) (L L' : Fin κ → Fin 2 → J → ℝ)
    (a : Fin N × Fin 2 → ℝ) (w : CascadeWeights κ) (hw : ∀ α, branchWeight κ w α ≠ ∞) (u : ℝ)
    (hne : ∃ p, coupledWt N M w u p ≠ 0) (c₀ : ℝ) (θf : ℕ → ℝ) :
    Continuous (truncLevelBoundLaw κ (Pm.prod (rootMarksLaw N v₀))
      (siteGaussianMarks (Fin N × J) κ vs) (coupledG N u a L₀ L₀' L L' ξ G₀) M c₀ θf w) := by
  have hwt : ∀ p, 0 ≤ coupledWt N M w u p := coupledWt_nonneg N M w u
  set θq : PairConfig N (TruncBranch κ M) → PairConfig N (TruncBranch κ M) → ℝ :=
    fun x y => θf (branchLevel x.2 y.2) with hθq
  have h : truncLevelBoundLaw κ (Pm.prod (rootMarksLaw N v₀)) (siteGaussianMarks (Fin N × J) κ vs)
      (coupledG N u a L₀ L₀' L L' ξ G₀) M c₀ θf w
      = fun t => ∫ ω, treeBoundIntegrand (coupledWt N M w u) c₀ θq
          (coupledTruncHam N M t ξ G₀ v₀ vs L₀ L₀' L L' a ω)
          ∂Pm.prod (siteMarksLaw (Fin N × J) κ v₀ vs) :=
    funext fun t => (integral_treeBoundIntegrand_coupled_eq N M t ξ G₀ v₀ vs L₀ L₀' L L' a w hw u
      c₀ θf).symm
  rw [h]
  refine continuous_of_dominated (fun t => ?_)
    (bound := fun _ => (1 / 2) * |c₀| + (1 / 2) * ∑ x, ∑ y, |θq x y|)
    (fun t => Filter.Eventually.of_forall fun ω => ?_) (integrable_const _)
    (Filter.Eventually.of_forall fun ω => ?_)
  · exact ((continuous_treeBoundIntegrand _ hwt hne c₀ θq).measurable.comp
      (measurable_coupledTruncHam N M t ξ G₀ v₀ vs L₀ L₀' L L' a)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact abs_treeBoundIntegrand_le _ hwt hne c₀ θq _
  · exact (continuous_treeBoundIntegrand _ hwt hne c₀ θq).comp
      ((continuous_gaussianInterp_apply _).add continuous_const)

/-- **Lemma 14.6.1 for the tree truncated at `M`, with the bound as a level sum**
(Talagrand's (14.139) for the truncated tree): for the weights `u*_α 1_{R_{1,2} = u}`,

`𝔼 F_w(H_N(σ¹) + H_N(σ²) + H⁰) - 𝔼 F_w(H + H⁰) ≤ ∫₀¹ truncLevelBoundLaw … w t dt`. -/
theorem coupled_truncated (M : ℕ) (hN : 0 < N) (ξ : ℝ → ℝ) (ρ : Fin 2 → Fin 2 → ℕ → ℝ) (u : ℝ)
    (hρ0 : ∀ l l', ρ l l' 0 = 0) {S : Set ℝ} (hρS : ∀ l l' r, ρ l l' r ∈ S)
    (htan : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ q ∈ S, ξ q + (x - q) * deriv ξ q ≤ ξ x) (h0 : deriv ξ 0 = 0)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) {J₁ : Finset J} {L₀ L₀' : Fin 2 → J → ℝ}
    {L L' : Fin κ → Fin 2 → J → ℝ}
    (hC0 : ∀ l l', (v₀ : ℝ) * gram L₀ l l' = deriv ξ (ρ l l' 1) - deriv ξ (ρ l l' 0))
    (hC : ∀ (p : Fin κ) l l', (vs p : ℝ) * gram (L p) l l'
      = deriv ξ (ρ l l' (p.val + 2)) - deriv ξ (ρ l l' (p.val + 1)))
    (hL0 : ∀ l j, j ∉ J₁ → L₀ l j = 0) (hL : ∀ p l j, j ∉ J₁ → L p l j = 0)
    (hL0' : ∀ l j, j ∈ J₁ → L₀' l j = 0) (hL' : ∀ p l j, j ∈ J₁ → L' p l j = 0)
    (a : Fin N × Fin 2 → ℝ) (w : CascadeWeights κ) (hW : weightSum κ w ≠ ∞)
    (hne : ∃ β : TruncBranch κ M, truncWt κ M w β ≠ 0)
    (hu : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    (∫ ω, wFreeEnergy (coupledWt N M w u) N ((coupledModelField N M ξ G₀ v₀ vs).U ω
          + coupledExtField N M Pm v₀ vs L₀' L' a ω) ∂Pm.prod (siteMarksLaw (Fin N × J) κ v₀ vs))
        - (∫ ω, wFreeEnergy (coupledWt N M w u) N ((coupledTreeField N M Pm v₀ vs L₀ L).U ω
          + coupledExtField N M Pm v₀ vs L₀' L' a ω) ∂Pm.prod (siteMarksLaw (Fin N × J) κ v₀ vs))
      ≤ ∫ t in (0 : ℝ)..1, truncLevelBoundLaw κ (Pm.prod (rootMarksLaw N v₀))
          (siteGaussianMarks (Fin N × J) κ vs) (coupledG N u a L₀ L₀' L L' ξ G₀) M
          (pairDiagConst ξ u fun l l' => ρ l l' (κ + 1))
          (fun r => ∑ l : Fin 2, ∑ l' : Fin 2, parisiTheta ξ (ρ l l' (r + 1))) w t := by
  have hw : ∀ α, branchWeight κ w α ≠ ∞ :=
    fun α => ne_top_of_le_ne_top hW (branchWeight_le_weightSum κ w α)
  refine (wFreeEnergy_coupledScheme_sub_le N M hN ξ ρ u hρ0 hρS htan h0 G₀ v₀ vs hC0 hC
    hL0 hL hL0' hL' a (coupledWt N M w u) (coupledWt_nonneg N M w u)
    (exists_coupledWt_ne_zero N M w u hne hu)
    (fun p hp => overlap_eq_of_coupledWt_ne_zero N M w u hp)).trans (le_of_eq ?_)
  refine intervalIntegral.integral_congr fun t _ => ?_
  exact integral_treeBoundIntegrand_coupled_eq N M t ξ G₀ v₀ vs L₀ L₀' L L' a w hw u
    (pairDiagConst ξ u fun l l' => ρ l l' (κ + 1))
    (fun r => ∑ l : Fin 2, ∑ l' : Fin 2, parisiTheta ξ (ρ l l' (r + 1)))

end

end SpinGlass
