/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Convex.Deriv

/-!
# Convexity is preserved under pointwise limits

A pointwise limit of convex (concave) real functions on a convex set is convex (concave):
`convexOn_of_tendsto`, `concaveOn_of_tendsto`. The defining inequality is closed.
-/

open Filter Topology Set

variable {ι E : Type*} {l : Filter ι} [l.NeBot] [AddCommGroup E] [Module ℝ E] {s : Set E}
  {f : ι → E → ℝ} {g : E → ℝ}

/-- A pointwise limit of convex functions on a convex set is convex. -/
theorem convexOn_of_tendsto (hs : Convex ℝ s) (hf : ∀ i, ConvexOn ℝ s (f i))
    (hlim : ∀ x ∈ s, Tendsto (fun i => f i x) l (𝓝 (g x))) : ConvexOn ℝ s g := by
  refine ⟨hs, fun x hx y hy a b ha hb hab => ?_⟩
  refine le_of_tendsto_of_tendsto' (hlim _ (hs hx hy ha hb hab))
    (((hlim x hx).const_mul a).add ((hlim y hy).const_mul b)) fun i => ?_
  exact (hf i).2 hx hy ha hb hab

/-- A pointwise limit of concave functions on a convex set is concave. -/
theorem concaveOn_of_tendsto (hs : Convex ℝ s) (hf : ∀ i, ConcaveOn ℝ s (f i))
    (hlim : ∀ x ∈ s, Tendsto (fun i => f i x) l (𝓝 (g x))) : ConcaveOn ℝ s g := by
  have h := convexOn_of_tendsto hs (f := fun i => -f i) (g := -g) (fun i => (hf i).neg)
    fun x hx => (hlim x hx).neg
  simpa using h.neg
