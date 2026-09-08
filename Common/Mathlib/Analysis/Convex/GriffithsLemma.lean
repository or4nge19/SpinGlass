/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Continuous

/-!
# Griffiths' lemma: derivatives of convex functions pass to pointwise limits

If a family of convex functions converges pointwise, the limit is convex, but nothing about
derivatives follows from pointwise convergence alone. Convexity changes that completely: the
derivative of a convex function is squeezed between its own difference quotients, and a difference
quotient is a *finite* linear combination of values, so it converges. This is the statement that
statistical mechanics calls **Griffiths' lemma** (Talagrand, *Mean Field Models for Spin Glasses*,
Vol. I, §1.3, after Theorem 1.3.9), and its quantitative form is Talagrand Vol. II, Lemma 12.1.5.

Mathlib has the full one-sided derivative calculus for convex functions
(`ConvexOn.rightDeriv_le_slope`, `ConvexOn.slope_le_leftDeriv`, …) but not this consequence. We
prove it here in the sharpest form the Mathlib API allows:

* no differentiability hypothesis on the approximating functions — the conclusion is about their
  right derivatives, which exist at every interior point of a convex domain;
* no differentiability hypothesis on the limit either — only that its one-sided derivatives at the
  point agree, which for a convex function *is* differentiability there;
* an explicit error bound at every scale `b`, not just the limit statement.

## Main statements

- `ConvexOn.rightDeriv_le_slope_add`, `ConvexOn.sub_le_rightDeriv`: **the two-scale sandwich.** The
  right derivative of `θ` at `x` lies between the difference quotients of *any* comparison function
  `p`, up to `‖θ - p‖ / b` at the three points `x - b, x, x + b`.
- `ConvexOn.abs_rightDeriv_sub_le`: Talagrand Vol. II, Lemma 12.1.5.
- `ConvexOn.tendsto_rightDeriv_of_tendsto`: **Griffiths' lemma.**
- `ConvexOn.tendsto_deriv_of_tendsto`: the same for two-sided derivatives.
-/

open Set Filter Topology

namespace ConvexOn

variable {S : Set ℝ} {θ p : ℝ → ℝ} {x b : ℝ}

/-! ### The two-scale sandwich

For a convex `θ`, the right derivative at `x` is at most the slope to the right and at least the
slope to the left; replacing `θ` by a comparison function `p` in those slopes costs the sup-norm of
`θ - p` at the endpoints, divided by the step `b`. -/

/-- **Upper half of the quantitative Griffiths lemma.** -/
theorem rightDeriv_le_slope_add (hθ : ConvexOn ℝ S θ) (hxi : x ∈ interior S)
    (hr : x + b ∈ S) (hb : 0 < b) (p : ℝ → ℝ) :
    derivWithin θ (Ioi x) x
      ≤ slope p x (x + b) + (|θ (x + b) - p (x + b)| + |θ x - p x|) / b := by
  have hxS : x ∈ S := interior_subset hxi
  have hlt : x < x + b := by linarith
  have h1 : derivWithin θ (Ioi x) x ≤ slope θ x (x + b) :=
    hθ.rightDeriv_le_slope hxS hr hlt (hθ.differentiableWithinAt_Ioi_of_mem_interior hxi)
  refine h1.trans ?_
  rw [slope_def_field, slope_def_field, add_sub_cancel_left, ← add_div]
  gcongr
  linarith [le_abs_self (θ (x + b) - p (x + b)), neg_le_abs (θ x - p x)]

/-- **Lower half of the quantitative Griffiths lemma.** -/
theorem sub_le_rightDeriv (hθ : ConvexOn ℝ S θ) (hxi : x ∈ interior S)
    (hl : x - b ∈ S) (hb : 0 < b) (p : ℝ → ℝ) :
    slope p (x - b) x - (|θ (x - b) - p (x - b)| + |θ x - p x|) / b
      ≤ derivWithin θ (Ioi x) x := by
  have hxS : x ∈ S := interior_subset hxi
  have hlt : x - b < x := by linarith
  have h1 : slope θ (x - b) x ≤ derivWithin θ (Iio x) x :=
    hθ.slope_le_leftDeriv hl hxS hlt (hθ.differentiableWithinAt_Iio_of_mem_interior hxi)
  have h2 : derivWithin θ (Iio x) x ≤ derivWithin θ (Ioi x) x :=
    hθ.leftDeriv_le_rightDeriv_of_mem_interior hxi
  refine le_trans ?_ (h1.trans h2)
  rw [slope_def_field, slope_def_field, sub_sub_cancel, sub_le_iff_le_add, ← add_div]
  gcongr
  linarith [le_abs_self (θ (x - b) - p (x - b)), neg_le_abs (θ x - p x)]

/-- **The quantitative Griffiths lemma**, Talagrand, *Mean Field Models for Spin Glasses*,
Vol. II, Lemma 12.1.5, in one-sided form: no differentiability is assumed anywhere. The error is
the increment of the one-sided derivatives of `p` across the window `[x - b, x + b]`, plus the
sup-distance of `θ` to `p` at the three window points, divided by the window width. -/
theorem abs_rightDeriv_sub_le (hθ : ConvexOn ℝ S θ) (hp : ConvexOn ℝ S p)
    (hxi : x ∈ interior S) (hli : x - b ∈ interior S) (hri : x + b ∈ interior S) (hb : 0 < b) :
    |derivWithin θ (Ioi x) x - derivWithin p (Ioi x) x|
      ≤ (derivWithin p (Iio (x + b)) (x + b) - derivWithin p (Ioi (x - b)) (x - b))
        + (|θ (x + b) - p (x + b)| + |θ (x - b) - p (x - b)| + |θ x - p x|) / b := by
  have hxS : x ∈ S := interior_subset hxi
  have hlS : x - b ∈ S := interior_subset hli
  have hrS : x + b ∈ S := interior_subset hri
  have hltr : x < x + b := by linarith
  have hltl : x - b < x := by linarith
  set W := (|θ (x + b) - p (x + b)| + |θ (x - b) - p (x - b)| + |θ x - p x|) / b with hW
  have hb' : (0:ℝ) ≤ b := hb.le
  -- The window slopes of `p` are trapped between its one-sided derivatives.
  have hs1 : slope p x (x + b) ≤ derivWithin p (Iio (x + b)) (x + b) :=
    hp.slope_le_leftDeriv hxS hrS hltr (hp.differentiableWithinAt_Iio_of_mem_interior hri)
  have hs2 : derivWithin p (Ioi (x - b)) (x - b) ≤ slope p (x - b) x :=
    hp.rightDeriv_le_slope hlS hxS hltl (hp.differentiableWithinAt_Ioi_of_mem_interior hli)
  have hs3 : derivWithin p (Ioi x) x ≤ derivWithin p (Iio (x + b)) (x + b) :=
    le_trans (hp.rightDeriv_le_slope hxS hrS hltr
      (hp.differentiableWithinAt_Ioi_of_mem_interior hxi)) hs1
  have hs4 : derivWithin p (Ioi (x - b)) (x - b) ≤ derivWithin p (Ioi x) x :=
    le_trans hs2 (le_trans
      (hp.slope_le_leftDeriv hlS hxS hltl (hp.differentiableWithinAt_Iio_of_mem_interior hxi))
      (hp.leftDeriv_le_rightDeriv_of_mem_interior hxi))
  -- The two halves of the sandwich, with the two partial errors bounded by `W`.
  have hup : derivWithin θ (Ioi x) x ≤ slope p x (x + b) + W := by
    refine (hθ.rightDeriv_le_slope_add hxi hrS hb p).trans ?_
    have hle : (|θ (x + b) - p (x + b)| + |θ x - p x|) / b ≤ W := by
      rw [hW]; gcongr; linarith [abs_nonneg (θ (x - b) - p (x - b))]
    linarith
  have hlo : slope p (x - b) x - W ≤ derivWithin θ (Ioi x) x := by
    refine le_trans ?_ (hθ.sub_le_rightDeriv hxi hlS hb p)
    have hle : (|θ (x - b) - p (x - b)| + |θ x - p x|) / b ≤ W := by
      rw [hW]; gcongr; linarith [abs_nonneg (θ (x + b) - p (x + b))]
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- **Talagrand Vol. II, Lemma 12.1.5**, in the differentiable form he states it: for convex `θ`
and `p` differentiable at `x` and at `x ± b`,

`|θ'(x) - p'(x)| ≤ (p'(x+b) - p'(x-b)) + (‖θ - p‖ at the three window points)/b`. -/
theorem abs_deriv_sub_le (hθ : ConvexOn ℝ S θ) (hp : ConvexOn ℝ S p)
    (hxi : x ∈ interior S) (hli : x - b ∈ interior S) (hri : x + b ∈ interior S) (hb : 0 < b)
    {dθ dp dpl dpr : ℝ} (hθd : HasDerivAt θ dθ x) (hpd : HasDerivAt p dp x)
    (hpl : HasDerivAt p dpl (x - b)) (hpr : HasDerivAt p dpr (x + b)) :
    |dθ - dp| ≤ (dpr - dpl)
      + (|θ (x + b) - p (x + b)| + |θ (x - b) - p (x - b)| + |θ x - p x|) / b := by
  have h := hθ.abs_rightDeriv_sub_le hp hxi hli hri hb
  rw [hθd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x),
    hpd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x),
    hpr.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio (x + b)),
    hpl.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi (x - b))] at h
  exact h

/-! ### Griffiths' lemma -/

/-- **Griffiths' lemma.** If a family of convex functions converges pointwise on `S` to `p`, then
at every interior point where `p` is differentiable — equivalently, where its one-sided derivatives
agree — the right derivatives converge as well.

Talagrand, *Mean Field Models for Spin Glasses*, Vol. I, §1.3 (stated right after Theorem 1.3.9).
No differentiability is assumed of the approximating functions: their right derivatives exist
automatically at interior points. -/
theorem tendsto_rightDeriv_of_tendsto {ι : Type*} {L : Filter ι} {θ : ι → ℝ → ℝ}
    (hθ : ∀ i, ConvexOn ℝ S (θ i)) (hp : ConvexOn ℝ S p)
    (hconv : ∀ y ∈ S, Tendsto (fun i => θ i y) L (𝓝 (p y)))
    (hxi : x ∈ interior S)
    (hdiff : derivWithin p (Iio x) x = derivWithin p (Ioi x) x) :
    Tendsto (fun i => derivWithin (θ i) (Ioi x) x) L (𝓝 (derivWithin p (Ioi x) x)) := by
  -- The slopes of `p` at `x` converge to its one-sided derivatives.
  have hR : Tendsto (slope p x) (𝓝[>] x) (𝓝 (derivWithin p (Ioi x) x)) := by
    have h := hp.hasDerivWithinAt_rightDeriv_of_mem_interior hxi
    rw [hasDerivWithinAt_iff_tendsto_slope] at h
    simpa [Set.sdiff_singleton_eq_self (Set.self_notMem_Ioi (a := x))] using h
  have hL : Tendsto (slope p x) (𝓝[<] x) (𝓝 (derivWithin p (Iio x) x)) := by
    have h := hp.hasDerivWithinAt_leftDeriv_of_mem_interior hxi
    rw [hasDerivWithinAt_iff_tendsto_slope] at h
    simpa [Set.sdiff_singleton_eq_self (Set.self_notMem_Iio (a := x))] using h
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ₁, hδ₁, H₁⟩ := Metric.tendsto_nhdsWithin_nhds.1 hR (ε / 3) (by positivity)
  obtain ⟨δ₂, hδ₂, H₂⟩ := Metric.tendsto_nhdsWithin_nhds.1 hL (ε / 3) (by positivity)
  obtain ⟨δ₃, hδ₃, H₃⟩ := Metric.isOpen_iff.1 isOpen_interior x hxi
  set b : ℝ := min δ₁ (min δ₂ δ₃) / 2 with hbdef
  have hmin : 0 < min δ₁ (min δ₂ δ₃) := lt_min hδ₁ (lt_min hδ₂ hδ₃)
  have hb : 0 < b := by rw [hbdef]; linarith
  have hb1 : b < δ₁ := by
    have h : min δ₁ (min δ₂ δ₃) ≤ δ₁ := min_le_left _ _
    rw [hbdef]; linarith
  have hb2 : b < δ₂ := by
    have h : min δ₁ (min δ₂ δ₃) ≤ δ₂ := (min_le_right _ _).trans (min_le_left _ _)
    rw [hbdef]; linarith
  have hb3 : b < δ₃ := by
    have h : min δ₁ (min δ₂ δ₃) ≤ δ₃ := (min_le_right _ _).trans (min_le_right _ _)
    rw [hbdef]; linarith
  -- The window sits inside `S`.
  have hdr : dist (x + b) x = b := by
    rw [Real.dist_eq, show x + b - x = b by ring, abs_of_pos hb]
  have hdl : dist (x - b) x = b := by
    rw [Real.dist_eq, show x - b - x = -b by ring, abs_neg, abs_of_pos hb]
  have hrS : x + b ∈ S := interior_subset (H₃ (by rw [Metric.mem_ball, hdr]; exact hb3))
  have hlS : x - b ∈ S := interior_subset (H₃ (by rw [Metric.mem_ball, hdl]; exact hb3))
  -- The window slopes of `p` are within `ε/3` of the derivative.
  have hslr : |slope p x (x + b) - derivWithin p (Ioi x) x| < ε / 3 := by
    have h := H₁ (x := x + b) (by simp [hb]) (by rw [hdr]; exact hb1)
    simpa [Real.dist_eq] using h
  have hsll : |slope p (x - b) x - derivWithin p (Ioi x) x| < ε / 3 := by
    have h := H₂ (x := x - b) (by simp [hb]) (by rw [hdl]; exact hb2)
    rw [hdiff] at h
    simpa [Real.dist_eq, slope_comm] using h
  -- The comparison error tends to `0`.
  have habs : ∀ y ∈ S, Tendsto (fun i => |θ i y - p y|) L (𝓝 0) := fun y hy => by
    have h0 : Tendsto (fun i => θ i y - p y) L (𝓝 0) := by
      simpa using (hconv y hy).sub (tendsto_const_nhds (x := p y))
    simpa using h0.abs
  have hW : Tendsto (fun i =>
      (|θ i (x + b) - p (x + b)| + |θ i (x - b) - p (x - b)| + |θ i x - p x|) / b) L (𝓝 0) := by
    have := (((habs (x + b) hrS).add (habs (x - b) hlS)).add
      (habs x (interior_subset hxi))).div_const b
    simpa using this
  filter_upwards [Metric.tendsto_nhds.1 hW (ε / 3) (by positivity)] with i hi
  have hWi : (|θ i (x + b) - p (x + b)| + |θ i (x - b) - p (x - b)| + |θ i x - p x|) / b
      < ε / 3 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hi
    exact hi
  have hup : derivWithin (θ i) (Ioi x) x
      ≤ slope p x (x + b)
        + (|θ i (x + b) - p (x + b)| + |θ i (x - b) - p (x - b)| + |θ i x - p x|) / b := by
    refine ((hθ i).rightDeriv_le_slope_add hxi hrS hb p).trans ?_
    have hle : (|θ i (x + b) - p (x + b)| + |θ i x - p x|) / b
        ≤ (|θ i (x + b) - p (x + b)| + |θ i (x - b) - p (x - b)| + |θ i x - p x|) / b := by
      gcongr
      linarith [abs_nonneg (θ i (x - b) - p (x - b))]
    linarith
  have hlo : slope p (x - b) x
        - (|θ i (x + b) - p (x + b)| + |θ i (x - b) - p (x - b)| + |θ i x - p x|) / b
      ≤ derivWithin (θ i) (Ioi x) x := by
    refine le_trans ?_ ((hθ i).sub_le_rightDeriv hxi hlS hb p)
    have : (|θ i (x - b) - p (x - b)| + |θ i x - p x|) / b
        ≤ (|θ i (x + b) - p (x + b)| + |θ i (x - b) - p (x - b)| + |θ i x - p x|) / b := by
      gcongr
      linarith [abs_nonneg (θ i (x + b) - p (x + b))]
    linarith
  rw [Real.dist_eq, abs_lt]
  rw [abs_lt] at hslr hsll
  constructor <;> linarith

/-! ### The exceptional set is countable

Griffiths' lemma has a hypothesis — differentiability of the limit at the point. For a convex
function that hypothesis holds off a countable set, because the "jump intervals"
`(leftDeriv f x, rightDeriv f x)` at distinct points are pairwise disjoint. -/

/-- **A convex function on `ℝ` is differentiable outside a countable subset of the interior of its
domain.** -/
theorem countable_setOf_leftDeriv_ne_rightDeriv (hp : ConvexOn ℝ S p) :
    {x ∈ interior S | derivWithin p (Iio x) x ≠ derivWithin p (Ioi x) x}.Countable := by
  set A := {x ∈ interior S | derivWithin p (Iio x) x ≠ derivWithin p (Ioi x) x} with hA
  have hlt : ∀ x ∈ A, derivWithin p (Iio x) x < derivWithin p (Ioi x) x := by
    rintro x ⟨hxi, hxne⟩
    exact lt_of_le_of_ne (hp.leftDeriv_le_rightDeriv_of_mem_interior hxi) hxne
  -- For `x < y` the right derivative at `x` does not exceed the left derivative at `y`.
  have hstep : ∀ x ∈ A, ∀ y ∈ A, x < y →
      derivWithin p (Ioi x) x ≤ derivWithin p (Iio y) y := by
    rintro x ⟨hxi, -⟩ y ⟨hyi, -⟩ hxy
    exact le_trans
      (hp.rightDeriv_le_slope (interior_subset hxi) (interior_subset hyi) hxy
        (hp.differentiableWithinAt_Ioi_of_mem_interior hxi))
      (hp.slope_le_leftDeriv (interior_subset hxi) (interior_subset hyi) hxy
        (hp.differentiableWithinAt_Iio_of_mem_interior hyi))
  refine Set.PairwiseDisjoint.countable_of_isOpen
    (s := fun x => Ioo (derivWithin p (Iio x) x) (derivWithin p (Ioi x) x))
    (a := A) ?_ (fun x _ => isOpen_Ioo) (fun x hx => nonempty_Ioo.2 (hlt x hx))
  intro x hx y hy hxy
  refine Set.disjoint_left.2 fun z hz hz' => ?_
  rcases lt_or_gt_of_ne hxy with hlt' | hlt'
  · have := hstep x hx y hy hlt'
    exact absurd (hz.2.trans_le (this.trans hz'.1.le)) (lt_irrefl _)
  · have := hstep y hy x hx hlt'
    exact absurd (hz'.2.trans_le (this.trans hz.1.le)) (lt_irrefl _)

/-- **Equal one-sided derivatives is differentiability**, for a convex function at an interior
point. Together with `countable_setOf_leftDeriv_ne_rightDeriv` this says a convex function on `ℝ`
is differentiable off a countable set. -/
theorem hasDerivAt_of_leftDeriv_eq_rightDeriv (hp : ConvexOn ℝ S p) (hx : x ∈ interior S)
    (h : derivWithin p (Iio x) x = derivWithin p (Ioi x) x) :
    HasDerivAt p (derivWithin p (Ioi x) x) x := by
  have hl : HasDerivWithinAt p (derivWithin p (Ioi x) x) (Iio x) x := by
    rw [← h]; exact hp.hasDerivWithinAt_leftDeriv_of_mem_interior hx
  have hr : HasDerivWithinAt p (derivWithin p (Ioi x) x) (Ioi x) x :=
    hp.hasDerivWithinAt_rightDeriv_of_mem_interior hx
  have hu : HasDerivWithinAt p (derivWithin p (Ioi x) x) (Iio x ∪ Ioi x) x := hl.union hr
  rw [Set.Iio_union_Ioi, Set.compl_eq_univ_sdiff] at hu
  rw [← hasDerivWithinAt_univ]
  exact hasFDerivWithinAt_sdiff_singleton_self.1 hu

/-- **A convex function on `ℝ` is differentiable outside a countable subset of the interior of its
domain.** -/
theorem countable_setOf_not_differentiableAt (hp : ConvexOn ℝ S p) :
    {x ∈ interior S | ¬ DifferentiableAt ℝ p x}.Countable := by
  refine Set.Countable.mono ?_ hp.countable_setOf_leftDeriv_ne_rightDeriv
  rintro x ⟨hxi, hxd⟩
  refine ⟨hxi, fun hEq => hxd ?_⟩
  exact (hp.hasDerivAt_of_leftDeriv_eq_rightDeriv hxi hEq).differentiableAt

/-- **Griffiths' lemma for two-sided derivatives.** -/
theorem tendsto_deriv_of_tendsto {ι : Type*} {L : Filter ι} {θ : ι → ℝ → ℝ}
    (hθ : ∀ i, ConvexOn ℝ S (θ i)) (hp : ConvexOn ℝ S p)
    (hconv : ∀ y ∈ S, Tendsto (fun i => θ i y) L (𝓝 (p y)))
    (hxi : x ∈ interior S) (hpd : DifferentiableAt ℝ p x)
    (hθd : ∀ i, DifferentiableAt ℝ (θ i) x) :
    Tendsto (fun i => deriv (θ i) x) L (𝓝 (deriv p x)) := by
  have key : ∀ f : ℝ → ℝ, DifferentiableAt ℝ f x → derivWithin f (Ioi x) x = deriv f x :=
    fun f hf => hf.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x)
  have hpl : derivWithin p (Iio x) x = derivWithin p (Ioi x) x := by
    rw [hpd.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio x), key p hpd]
  have h := tendsto_rightDeriv_of_tendsto hθ hp hconv hxi hpl
  rw [key p hpd] at h
  exact h.congr fun i => key (θ i) (hθd i)

end ConvexOn
