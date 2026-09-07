/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Probability.ProductMeasure

/-!
# Finite-dimensional marginals of an infinite product measure

Mathlib records the marginals of `MeasureTheory.Measure.infinitePi` along the canonical restriction
to a `Finset` (`MeasureTheory.Measure.infinitePi_map_restrict`). What one actually uses is the
marginal along an arbitrary *injective reindexing* `f : κ → ι` of a finite index type: reading `κ`
prescribed coordinates of an i.i.d. family gives `κ` i.i.d. copies. This is the statement that
turns a statement about an infinite i.i.d. array — a replica array, in spin-glass language — into
one about finitely many replicas.

## Main statements

- `MeasureTheory.Measure.map_comp_infinitePi_const`: `(⨂ᵢ ν).map (ω ↦ ω ∘ f) = ⨂_κ ν` for `f`
  injective on a finite index type.
-/

open Set MeasureTheory

namespace MeasureTheory.Measure

variable {ι κ E : Type*} [Fintype κ] [MeasurableSpace E]

/-- **Finite-dimensional marginals of an i.i.d. infinite product.** Reading the coordinates
`f j`, `j : κ`, of an i.i.d. family indexed by `ι` gives `κ` independent copies, provided the
reindexing `f` is injective. -/
theorem map_comp_infinitePi_const (ν : Measure E) [IsProbabilityMeasure ν]
    {f : κ → ι} (hf : Function.Injective f) :
    (Measure.infinitePi fun _ : ι => ν).map (fun ω j => ω (f j))
      = Measure.pi fun _ : κ => ν := by
  classical
  have hmeas : Measurable fun ω : ι → E => fun j : κ => ω (f j) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply (f j)
  refine (Measure.pi_eq fun t ht => ?_).symm
  -- The preimage of a box is a box supported on the image of `f`.
  set s : Finset ι := Finset.image f Finset.univ with hs
  set u : ι → Set E := fun i => ⋂ j ∈ {j : κ | f j = i}, t j with hu
  have huf : ∀ j : κ, u (f j) = t j := by
    intro j
    change (⋂ j' ∈ {j' : κ | f j' = f j}, t j') = t j
    refine Set.Subset.antisymm ?_ (Set.subset_iInter₂ fun j' hj' => ?_)
    · exact Set.iInter₂_subset (s := fun j' (_ : f j' = f j) => t j') j rfl
    · exact subset_of_eq (congrArg t (hf hj')).symm
  have hpre : (fun ω : ι → E => fun j : κ => ω (f j)) ⁻¹' (Set.univ.pi t)
      = Set.pi (↑s : Set ι) u := by
    ext ω
    constructor
    · intro hω i hi
      simp only [hs, Finset.coe_image, Finset.coe_univ, image_univ, mem_range] at hi
      obtain ⟨j, rfl⟩ := hi
      rw [huf j]
      exact hω j (mem_univ j)
    · intro hω j _
      have hi : f j ∈ (↑s : Set ι) := by
        simp only [hs, Finset.coe_image, Finset.coe_univ, image_univ, mem_range]
        exact ⟨j, rfl⟩
      simpa [huf j] using hω (f j) hi
  have hmu : ∀ i ∈ s, MeasurableSet (u i) := fun i _ =>
    MeasurableSet.biInter (Set.to_countable _) fun j _ => ht j
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi ht), hpre,
    Measure.infinitePi_pi (μ := fun _ : ι => ν) hmu, hs,
    Finset.prod_image fun a _ b _ h => hf h]
  exact Finset.prod_congr rfl fun j _ => by rw [huf j]

end MeasureTheory.Measure
