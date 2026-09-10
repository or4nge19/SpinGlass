/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.PointProcess.CascadeTrunc
import Common.Mathlib.Probability.Distributions.Gaussian.PiGaussian
import Common.Mathlib.Probability.ProductMeasureProd

/-!
# The Gaussian coordinates of a truncated cascade with Gaussian marks

For Guerra's broken replica-symmetry bound (Talagrand, Vol. II, §14.4) the marks of the cascade
are Gaussian vectors `z_p ∈ ℝ^N` with independent coordinates of variance `𝔼 z_p² = ξ'(q_{p+1}) -
ξ'(q_p)`, together with an independent level-`0` vector `z₀`. The coordinates that the truncated
tree sees — `z₀` and the marks of the nodes of `TruncNode k M`, site by site — form a finite
family indexed by `Fin N ⊕ (TruncNode k M × Fin N)`, and this file shows that under the product
of the level-`0` law with `cascadeMarksLaw` this family is a product of real Gaussians
(`treeCoords_law`), hence a Gaussian vector with diagonal covariance in `EuclideanSpace`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SpinGlass

noncomputable section

variable (N k M : ℕ)

/-- The coordinates of the truncated tree: the level-`0` marks `z₀` (one per site) and the
marks of the truncated nodes (one per node and site). -/
abbrev TreeCoord : Type := Fin N ⊕ (TruncNode k M × Fin N)

/-- The sample space of the marks: the level-`0` vector and the marks of the cascade, whose
marks are vectors in `ℝ^N`. -/
abbrev MarksSpace : Type := (Fin N → ℝ) × CascadeMarks (Fin N → ℝ) k

/-- The marks laws with independent Gaussian coordinates of variances `vs p` at level `p + 1`. -/
def gaussianMarks (vs : Fin k → ℝ≥0) (p : Fin k) : Measure (Fin N → ℝ) :=
  Measure.pi fun _ : Fin N => gaussianReal 0 (vs p)

instance (vs : Fin k → ℝ≥0) (p : Fin k) : IsProbabilityMeasure (gaussianMarks N k vs p) := by
  unfold gaussianMarks; infer_instance

/-- The law of the marks: independent level-`0` Gaussian vector of variance `v₀` and cascade
marks with variances `vs`. -/
def marksLaw (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) : Measure (MarksSpace N k) :=
  (Measure.pi fun _ : Fin N => gaussianReal 0 v₀).prod (cascadeMarksLaw k (gaussianMarks N k vs))

instance (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) : IsProbabilityMeasure (marksLaw N k v₀ vs) := by
  unfold marksLaw; infer_instance

/-- The variance of each coordinate of the truncated tree. -/
def coordVar (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) : TreeCoord N k M → ℝ≥0 :=
  Sum.elim (fun _ => v₀) fun p => vs p.1.1

/-- Extracting the coordinates of the truncated tree from the marks. -/
def treeCoords (ω : MarksSpace N k) : EuclideanSpace ℝ (TreeCoord N k M) :=
  WithLp.toLp 2 (Sum.elim ω.1 fun c => truncMarks k M ω.2 c.1 c.2)

lemma measurable_treeCoords : Measurable (treeCoords N k M) := by
  refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_lambda _ fun c => ?_)
  rcases c with i | ⟨v, i⟩
  · exact (measurable_pi_apply i).comp measurable_fst
  · exact (measurable_pi_apply i).comp ((measurable_pi_apply v).comp
      ((measurable_truncMarks k M).comp measurable_snd))

/-- **The coordinates of the truncated tree are independent real Gaussians** with variances
`coordVar`. -/
theorem treeCoords_law (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) :
    (marksLaw N k v₀ vs).map (treeCoords N k M)
      = (Measure.pi fun c : TreeCoord N k M => gaussianReal 0 (coordVar N k M v₀ vs c)).map
          (WithLp.toLp 2) := by
  -- the marks of the truncated nodes, site by site
  have h1 : (cascadeMarksLaw k (gaussianMarks N k vs)).map
        ((MeasurableEquiv.curry (TruncNode k M) (Fin N) ℝ).symm ∘ truncMarks k M)
      = Measure.pi fun p : TruncNode k M × Fin N => gaussianReal 0 (vs p.1.1) := by
    rw [← Measure.map_map (MeasurableEquiv.measurable _) (measurable_truncMarks k M),
      cascadeMarksLaw_map_truncMarks]
    have h := Measure.infinitePi_map_curry (fun (v : TruncNode k M) (_ : Fin N) =>
      gaussianReal 0 (vs v.1))
    simp only [Measure.infinitePi_eq_pi] at h
    show (Measure.pi fun v : TruncNode k M => gaussianMarks N k vs v.1).map _ = _
    unfold gaussianMarks
    symm
    rw [← MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq]
    exact h
  -- the pair `(z₀, node marks)`
  have h2 : (marksLaw N k v₀ vs).map
        (Prod.map id ((MeasurableEquiv.curry (TruncNode k M) (Fin N) ℝ).symm ∘ truncMarks k M))
      = (Measure.pi fun _ : Fin N => gaussianReal 0 v₀).prod
          (Measure.pi fun p : TruncNode k M × Fin N => gaussianReal 0 (vs p.1.1)) := by
    unfold marksLaw
    rw [← Measure.map_prod_map _ _ measurable_id
      ((MeasurableEquiv.measurable _).comp (measurable_truncMarks k M)), Measure.map_id, h1]
  -- assemble the coordinates
  have hmp := (measurePreserving_sumPiEquivProdPi
    (fun c : TreeCoord N k M => gaussianReal 0 (coordVar N k M v₀ vs c))).symm
    (MeasurableEquiv.sumPiEquivProdPi fun _ : TreeCoord N k M => ℝ)
  have hfun : treeCoords N k M = WithLp.toLp 2 ∘
      (MeasurableEquiv.sumPiEquivProdPi fun _ : TreeCoord N k M => ℝ).symm ∘
      Prod.map id ((MeasurableEquiv.curry (TruncNode k M) (Fin N) ℝ).symm ∘ truncMarks k M) := by
    funext ω
    unfold treeCoords
    congr 1
  rw [hfun, ← Measure.map_map (WithLp.measurable_toLp 2 _)
      ((MeasurableEquiv.measurable _).comp (measurable_id.prodMap
        ((MeasurableEquiv.measurable _).comp (measurable_truncMarks k M)))),
    ← Measure.map_map (MeasurableEquiv.measurable _) (measurable_id.prodMap
        ((MeasurableEquiv.measurable _).comp (measurable_truncMarks k M))), h2]
  have hmp' := hmp.map_eq
  simp only [coordVar, Sum.elim_inl, Sum.elim_inr] at hmp'
  rw [hmp']
  rfl

end

end SpinGlass
