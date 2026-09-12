/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.PointProcess.CascadeTrunc
import Common.Mathlib.Probability.Distributions.Gaussian.PiGaussian
import Common.Mathlib.Probability.ProductMeasureProd

/-!
# The Gaussian coordinates of a truncated cascade with Gaussian marks, over a site type

The marks of the cascades of Talagrand's interpolation schemes (Vol. II, §14.4 and §14.6) are
Gaussian vectors indexed by a finite **site type** `S` — `Fin N` for the one-dimensional scheme
(14.73), `Fin N × Fin 2` for the coupled copies of (14.135) — with independent coordinates of
variance `vs p` at level `p + 1`, together with an independent level-`0` vector. The coordinates
seen by the tree truncated to indices `< M` form a finite family indexed by
`S ⊕ (TruncNode k M × S)`, and under the product of the level-`0` law with `cascadeMarksLaw` this
family is a product of real Gaussians (`siteTreeCoords_law`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SpinGlass

noncomputable section

variable (S : Type*) [Fintype S] (k M : ℕ)

/-- The coordinates of the truncated tree over the sites `S`: the level-`0` marks (one per site)
and the marks of the truncated nodes (one per node and site). -/
abbrev SiteTreeCoord : Type _ := S ⊕ (TruncNode k M × S)

/-- The sample space of the marks: the level-`0` vector and the cascade marks, vectors in `ℝ^S`. -/
abbrev SiteMarksSpace : Type _ := (S → ℝ) × CascadeMarks (S → ℝ) k

/-- The marks laws with independent Gaussian coordinates of variances `vs p` at level `p + 1`. -/
def siteGaussianMarks (vs : Fin k → ℝ≥0) (p : Fin k) : Measure (S → ℝ) :=
  Measure.pi fun _ : S => gaussianReal 0 (vs p)

instance (vs : Fin k → ℝ≥0) (p : Fin k) : IsProbabilityMeasure (siteGaussianMarks S k vs p) := by
  unfold siteGaussianMarks; infer_instance

/-- The law of the marks: independent level-`0` Gaussian vector of variance `v₀` and cascade
marks with variances `vs`. -/
def siteMarksLaw (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) : Measure (SiteMarksSpace S k) :=
  (Measure.pi fun _ : S => gaussianReal 0 v₀).prod (cascadeMarksLaw k (siteGaussianMarks S k vs))

/-- Named, so that it can be applied at a literal index `k + 1`, where instance search does not
find it. -/
instance isProbabilityMeasure_siteMarksLaw (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) :
    IsProbabilityMeasure (siteMarksLaw S k v₀ vs) := by
  unfold siteMarksLaw; infer_instance

/-- The variance of each coordinate of the truncated tree. -/
def siteCoordVar (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) : SiteTreeCoord S k M → ℝ≥0 :=
  Sum.elim (fun _ => v₀) fun p => vs p.1.1

/-- Extracting the coordinates of the truncated tree from the marks. -/
def siteTreeCoords (ω : SiteMarksSpace S k) : EuclideanSpace ℝ (SiteTreeCoord S k M) :=
  WithLp.toLp 2 (Sum.elim ω.1 fun c => truncMarks k M ω.2 c.1 c.2)

omit [Fintype S] in
lemma measurable_siteTreeCoords : Measurable (siteTreeCoords S k M) := by
  refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_lambda _ fun c => ?_)
  rcases c with i | ⟨v, i⟩
  · exact (measurable_pi_apply i).comp measurable_fst
  · exact (measurable_pi_apply i).comp ((measurable_pi_apply v).comp
      ((measurable_truncMarks k M).comp measurable_snd))

/-- **The coordinates of the truncated tree are independent real Gaussians** with variances
`siteCoordVar`. -/
theorem siteTreeCoords_law (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) :
    (siteMarksLaw S k v₀ vs).map (siteTreeCoords S k M)
      = (Measure.pi fun c : SiteTreeCoord S k M =>
          gaussianReal 0 (siteCoordVar S k M v₀ vs c)).map (WithLp.toLp 2) := by
  -- the marks of the truncated nodes, site by site
  have h1 : (cascadeMarksLaw k (siteGaussianMarks S k vs)).map
        ((MeasurableEquiv.curry (TruncNode k M) S ℝ).symm ∘ truncMarks k M)
      = Measure.pi fun p : TruncNode k M × S => gaussianReal 0 (vs p.1.1) := by
    rw [← Measure.map_map (MeasurableEquiv.measurable _) (measurable_truncMarks k M),
      cascadeMarksLaw_map_truncMarks]
    have h := Measure.infinitePi_map_curry (fun (v : TruncNode k M) (_ : S) =>
      gaussianReal 0 (vs v.1))
    simp only [Measure.infinitePi_eq_pi] at h
    change (Measure.pi fun v : TruncNode k M => siteGaussianMarks S k vs v.1).map _ = _
    unfold siteGaussianMarks
    symm
    rw [← MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq]
    exact h
  -- the pair `(z₀, node marks)`
  have h2 : (siteMarksLaw S k v₀ vs).map
        (Prod.map id ((MeasurableEquiv.curry (TruncNode k M) S ℝ).symm ∘ truncMarks k M))
      = (Measure.pi fun _ : S => gaussianReal 0 v₀).prod
          (Measure.pi fun p : TruncNode k M × S => gaussianReal 0 (vs p.1.1)) := by
    unfold siteMarksLaw
    rw [← Measure.map_prod_map _ _ measurable_id
      ((MeasurableEquiv.measurable _).comp (measurable_truncMarks k M)), Measure.map_id, h1]
  -- assemble the coordinates
  have hmp := (measurePreserving_sumPiEquivProdPi
    (fun c : SiteTreeCoord S k M => gaussianReal 0 (siteCoordVar S k M v₀ vs c))).symm
    (MeasurableEquiv.sumPiEquivProdPi fun _ : SiteTreeCoord S k M => ℝ)
  have hfun : siteTreeCoords S k M = WithLp.toLp 2 ∘
      (MeasurableEquiv.sumPiEquivProdPi fun _ : SiteTreeCoord S k M => ℝ).symm ∘
      Prod.map id ((MeasurableEquiv.curry (TruncNode k M) S ℝ).symm ∘ truncMarks k M) := by
    funext ω
    unfold siteTreeCoords
    congr 1
  rw [hfun, ← Measure.map_map (WithLp.measurable_toLp 2 _)
      ((MeasurableEquiv.measurable _).comp (measurable_id.prodMap
        ((MeasurableEquiv.measurable _).comp (measurable_truncMarks k M)))),
    ← Measure.map_map (MeasurableEquiv.measurable _) (measurable_id.prodMap
        ((MeasurableEquiv.measurable _).comp (measurable_truncMarks k M))), h2]
  have hmp' := hmp.map_eq
  simp only [siteCoordVar, Sum.elim_inl, Sum.elim_inr] at hmp'
  rw [hmp']
  rfl

/-! ### Exponential moments of affine forms of the marks -/

omit M in
lemma measurable_ofReal_exp_add_sum_mul (a : ℝ) (B : Fin k → S → ℝ) :
    Measurable fun z : Fin k → S → ℝ =>
      ENNReal.ofReal (Real.exp (a + ∑ p, ∑ s, B p s * z p s)) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.add
    (Finset.measurable_sum _ fun p _ => Finset.measurable_sum _ fun s _ => measurable_const.mul
      ((measurable_pi_apply s).comp (measurable_pi_apply p)))))

omit M in
/-- **The exponential moment of an affine form of Gaussian marks**:
`∫ exp (a + ∑_p ∑_s B p s · z_p(s)) d⊗ N(0, v_p) = e^a exp (∑_p ∑_s v_p B p s² / 2)`. -/
lemma lintegral_ofReal_exp_add_siteGaussianMarks (vs : Fin k → ℝ≥0) (a : ℝ) (B : Fin k → S → ℝ) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (a + ∑ p, ∑ s, B p s * z p s))
        ∂Measure.pi (siteGaussianMarks S k vs)
      = ENNReal.ofReal (Real.exp a)
        * ENNReal.ofReal (Real.exp (∑ p, ∑ s, (vs p : ℝ) * B p s ^ 2 / 2)) := by
  have hm : Measurable fun z : Fin k → S → ℝ =>
      ENNReal.ofReal (Real.exp (∑ p, ∑ s, B p s * z p s)) := by
    simpa using measurable_ofReal_exp_add_sum_mul S k 0 B
  simp_rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [lintegral_const_mul _ hm]
  unfold siteGaussianMarks
  rw [lintegral_ofReal_exp_sum_mul_pi_pi_gaussianReal]

omit M in
/-- **Exponential moments of affine forms of Gaussian marks are finite**, for any finite family of
affine forms with nonnegative coefficients:
`∫ ∑_x C x exp (A x + ∑_p ∑_s B x p s · z_p(s)) d⊗ N(0, v_p) < ∞`. This is Talagrand's
hypothesis (14.4) for every (constrained) branch partition function of a Gaussian marks field. -/
lemma lintegral_sum_ofReal_mul_ofReal_exp_siteGaussianMarks {X : Type*} [Fintype X]
    (vs : Fin k → ℝ≥0) (C A : X → ℝ) (B : X → Fin k → S → ℝ) :
    ∫⁻ z, ∑ x : X, ENNReal.ofReal (C x)
        * ENNReal.ofReal (Real.exp (A x + ∑ p, ∑ s, B x p s * z p s))
        ∂Measure.pi (siteGaussianMarks S k vs) ≠ ∞ := by
  rw [lintegral_finsetSum _ fun x _ => (measurable_ofReal_exp_add_sum_mul S k (A x) (B x)).const_mul _]
  refine ENNReal.sum_ne_top.2 fun x _ => ?_
  rw [lintegral_const_mul _ (measurable_ofReal_exp_add_sum_mul S k (A x) (B x)),
    lintegral_ofReal_exp_add_siteGaussianMarks]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)

omit M in
/-- The case of unit coefficients. -/
lemma lintegral_sum_ofReal_exp_siteGaussianMarks {X : Type*} [Fintype X] (vs : Fin k → ℝ≥0)
    (A : X → ℝ) (B : X → Fin k → S → ℝ) :
    ∫⁻ z, ∑ x : X, ENNReal.ofReal (Real.exp (A x + ∑ p, ∑ s, B x p s * z p s))
        ∂Measure.pi (siteGaussianMarks S k vs) ≠ ∞ := by
  have := lintegral_sum_ofReal_mul_ofReal_exp_siteGaussianMarks S k vs (fun _ => 1) A B
  simpa only [ENNReal.ofReal_one, one_mul] using this

end

end SpinGlass
