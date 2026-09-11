/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.SiteTreeFieldLaw

/-!
# The Gaussian coordinates of a truncated cascade with Gaussian marks

For Guerra's broken replica-symmetry bound (Talagrand, Vol. II, §14.4) the marks of the cascade
are Gaussian vectors `z_p ∈ ℝ^N` with independent coordinates of variance `𝔼 z_p² = ξ'(q_{p+1}) -
ξ'(q_p)`, together with an independent level-`0` vector `z₀`. The coordinates that the truncated
tree sees — `z₀` and the marks of the nodes of `TruncNode k M`, site by site — form a finite
family indexed by `Fin N ⊕ (TruncNode k M × Fin N)`, and under the product of the level-`0` law
with `cascadeMarksLaw` this family is a product of real Gaussians (`treeCoords_law`). This is the
case `S = Fin N` of `SiteTreeFieldLaw`; the names below are kept as the interface of the
one-dimensional scheme.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SpinGlass

noncomputable section

variable (N k M : ℕ)

/-- The coordinates of the truncated tree over the sites `Fin N` (`SiteTreeCoord`). -/
abbrev TreeCoord : Type := SiteTreeCoord (Fin N) k M

/-- The sample space of the marks over the sites `Fin N` (`SiteMarksSpace`). -/
abbrev MarksSpace : Type := SiteMarksSpace (Fin N) k

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

lemma marksLaw_eq_siteMarksLaw (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) :
    marksLaw N k v₀ vs = siteMarksLaw (Fin N) k v₀ vs := rfl

/-- The variance of each coordinate of the truncated tree. -/
abbrev coordVar (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) : TreeCoord N k M → ℝ≥0 :=
  siteCoordVar (Fin N) k M v₀ vs

/-- Extracting the coordinates of the truncated tree from the marks. -/
abbrev treeCoords (ω : MarksSpace N k) : EuclideanSpace ℝ (TreeCoord N k M) :=
  siteTreeCoords (Fin N) k M ω

lemma measurable_treeCoords : Measurable (treeCoords N k M) :=
  measurable_siteTreeCoords (Fin N) k M

/-- **The coordinates of the truncated tree are independent real Gaussians** with variances
`coordVar`. -/
theorem treeCoords_law (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) :
    (marksLaw N k v₀ vs).map (treeCoords N k M)
      = (Measure.pi fun c : TreeCoord N k M => gaussianReal 0 (coordVar N k M v₀ vs c)).map
          (WithLp.toLp 2) :=
  siteTreeCoords_law (Fin N) k M v₀ vs

end

end SpinGlass
