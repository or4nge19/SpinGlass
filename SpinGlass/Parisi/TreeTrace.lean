/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.FiniteGibbs.WeightedInterpolation
import SpinGlass.ParisiFunctional

/-!
# The Guerra trace of a model kernel against a tree kernel

Talagrand, Vol. II, §14.4, Lemma 14.4.1 and (14.79). On the state space `Σ_N × A` of
configurations and branches, the model kernel is `N ξ(R_{στ})` and the tree kernel of (14.63) is
`N R_{στ} ξ'(q_{α,γ})`, with `q_{α,α} = q̄`. The weighted Guerra trace of the two is, exactly,
`(1/2)(ξ(1) - ξ'(q̄)) - (1/2)⟨ξ(R) - R ξ'(q_{α,γ})⟩`, and when `ξ` lies above its tangents on
`[-1,1]` (convexity, (14.61)) it is at most
`(1/2)(ξ(1) - ξ'(q̄)) + (1/2)⟨θ(q_{α,γ})⟩`, `θ(x) = xξ'(x) - ξ(x)` (`wGuerraTrace_tree_le`).
-/

open MeasureTheory Set
open scoped BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable {N : ℕ} {A : Type*} [Fintype A]

/-- The model kernel `N ξ(R_{στ})` on `Σ_N × A`. -/
def modelKernel (N : ℕ) (ξ : ℝ → ℝ) (x y : Config N × A) : ℝ :=
  (N : ℝ) * ξ (overlap N x.1 y.1)

/-- The tree kernel `N R_{στ} ξ'(q_{α,γ})` of (14.63). -/
def treeKernel (N : ℕ) (ξ : ℝ → ℝ) (qt : A → A → ℝ) (x y : Config N × A) : ℝ :=
  (N : ℝ) * overlap N x.1 y.1 * deriv ξ (qt x.2 y.2)

/-- **The weighted Guerra trace of the model kernel against a tree kernel** ((14.68) in weighted
form): `(1/2)(ξ(1) - ξ'(q̄)) - (1/2) ∑_{x,y} g_x g_y (ξ(R_{xy}) - R_{xy} ξ'(q_{α,γ}))`. -/
theorem wGuerraTrace_tree_eq (hN : 0 < N) (ξ : ℝ → ℝ) (qt : A → A → ℝ) (qbar : ℝ)
    (hqt : ∀ α, qt α α = qbar) (wt : Config N × A → ℝ) (hwt : ∀ x, 0 ≤ wt x)
    (hne : ∃ x, wt x ≠ 0) (H : FiniteGibbs.EnergySpace (Config N × A)) :
    wGuerraTrace wt (modelKernel N ξ) (treeKernel N ξ qt) N H
      = (1 / 2) * (ξ 1 - deriv ξ qbar)
        - (1 / 2) * ∑ x, ∑ y, wGibbs wt H x * wGibbs wt H y
            * (ξ (overlap N x.1 y.1) - overlap N x.1 y.1 * deriv ξ (qt x.2 y.2)) := by
  unfold wGuerraTrace
  have hdiag : ∀ x : Config N × A, modelKernel N ξ x x - treeKernel N ξ qt x x
      = (N : ℝ) * (ξ 1 - deriv ξ qbar) := by
    intro x
    simp only [modelKernel, treeKernel, overlap_self N hN, hqt]
    ring
  have hoff : ∀ x y : Config N × A, (modelKernel N ξ x y - treeKernel N ξ qt x y)
      * (wGibbs wt H x * wGibbs wt H y)
      = (N : ℝ) * (wGibbs wt H x * wGibbs wt H y
          * (ξ (overlap N x.1 y.1) - overlap N x.1 y.1 * deriv ξ (qt x.2 y.2))) := by
    intro x y
    simp only [modelKernel, treeKernel]
    ring
  simp_rw [hdiag, hoff]
  rw [← Finset.mul_sum, sum_wGibbs wt hwt hne H, mul_one]
  simp_rw [← Finset.mul_sum]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- **The convexity bound (14.79)**: if `ξ` lies above its tangents at points of `[0,1]` on
`[-1,1]`, then the weighted Guerra trace of the model kernel against a tree kernel with
`q_{α,γ} ∈ [0,1]` is at most `(1/2)(ξ(1) - ξ'(q̄)) + (1/2) ⟨θ(q_{α,γ})⟩`. -/
theorem wGuerraTrace_tree_le (hN : 0 < N) (ξ : ℝ → ℝ) (qt : A → A → ℝ) (qbar : ℝ)
    (hqt : ∀ α, qt α α = qbar) (hq01 : ∀ α γ, qt α γ ∈ Icc (0 : ℝ) 1)
    (htan : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1, ξ q + (x - q) * deriv ξ q ≤ ξ x)
    (wt : Config N × A → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (H : FiniteGibbs.EnergySpace (Config N × A)) :
    wGuerraTrace wt (modelKernel N ξ) (treeKernel N ξ qt) N H
      ≤ (1 / 2) * (ξ 1 - deriv ξ qbar)
        + (1 / 2) * ∑ x, ∑ y, wGibbs wt H x * wGibbs wt H y * parisiTheta ξ (qt x.2 y.2) := by
  rw [wGuerraTrace_tree_eq hN ξ qt qbar hqt wt hwt hne H, sub_eq_add_neg, ← mul_neg,
    ← Finset.sum_neg_distrib]
  simp_rw [← Finset.sum_neg_distrib]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ =>
    Finset.sum_le_sum fun y _ => ?_) (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have hg : 0 ≤ wGibbs wt H x * wGibbs wt H y :=
    mul_nonneg (wGibbs_nonneg wt hwt hne H x) (wGibbs_nonneg wt hwt hne H y)
  have hR : overlap N x.1 y.1 ∈ Icc (-1 : ℝ) 1 := abs_le.1 (abs_overlap_le_one N _ _)
  have h := htan _ hR _ (hq01 x.2 y.2)
  rw [← mul_neg]
  refine mul_le_mul_of_nonneg_left ?_ hg
  unfold parisiTheta
  linarith

end

end SpinGlass
