/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Independence of blocks of coordinates of a product measure

* `ProbabilityTheory.iIndepFun_eval_pi`: the coordinates of a finite product of probability
  measures are mutually independent.
* `ProbabilityTheory.indepFun_restrict_pi`: two disjoint blocks of coordinates are independent.
* `ProbabilityTheory.IndepFun.comp_map`: independence under a pushforward pulls back along the map.
* `ProbabilityTheory.IndepFun.prodMk_fst_comp_snd`: on a product `μ ⊗ ν`, the pair
  `(ω₁, f ω₂)` is independent of `g ω₂` whenever `f` and `g` are independent under `ν`.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

section Pi

variable {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- **The coordinates of a product of probability measures are independent.** -/
theorem iIndepFun_eval_pi : iIndepFun (fun i (w : ∀ i, X i) => w i) (Measure.pi μ) := by
  classical
  rw [iIndepFun_iff_map_fun_eq_pi_map fun i => (measurable_pi_apply i).aemeasurable]
  have h1 : (Measure.pi μ).map (fun (w : ∀ i, X i) i => w i) = Measure.pi μ := by
    rw [show (fun (w : ∀ i, X i) i => w i) = id from rfl, Measure.map_id]
  have h2 : ∀ i, (Measure.pi μ).map (fun w : ∀ i, X i => w i) = μ i := by
    intro i
    rw [show (fun w : ∀ i, X i => w i) = Function.eval i from rfl, Measure.pi_map_eval]
    simp
  rw [h1]
  congr 1
  funext i
  exact (h2 i).symm

/-- **Disjoint blocks of coordinates are independent.** -/
theorem indepFun_restrict_pi (S T : Finset ι) (hST : Disjoint S T) :
    IndepFun (fun (w : ∀ i, X i) (i : S) => w i) (fun (w : ∀ i, X i) (i : T) => w i)
      (Measure.pi μ) :=
  (iIndepFun_eval_pi μ).indepFun_finset S T hST fun i => measurable_pi_apply i

end Pi

section Map

variable {Ω Ω' β β' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace β]
  [MeasurableSpace β'] {P : Measure Ω}

/-- Independence under the pushforward `P.map φ` pulls back along `φ`. -/
theorem IndepFun.comp_map {φ : Ω → Ω'} (hφ : Measurable φ) {f : Ω' → β} {g : Ω' → β'}
    (hf : Measurable f) (hg : Measurable g) (h : IndepFun f g (P.map φ)) :
    IndepFun (f ∘ φ) (g ∘ φ) P := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  have := h s t hs ht
  rw [Measure.map_apply hφ ((hf hs).inter (hg ht)), Measure.map_apply hφ (hf hs),
    Measure.map_apply hφ (hg ht)] at this
  simpa only [Set.preimage_inter, Set.preimage_comp] using this

end Map

section Prod

variable {α Ω β β' : Type*} [MeasurableSpace α] [MeasurableSpace Ω] [MeasurableSpace β]
  [MeasurableSpace β']

/-- On a product `μ ⊗ ν` with `μ` a probability measure, `(ω₁, f ω₂)` is independent of `g ω₂`
whenever `f` and `g` are independent under `ν`. -/
theorem IndepFun.prodMk_fst_comp_snd (μ : Measure α) [IsProbabilityMeasure μ] {ν : Measure Ω}
    [SFinite ν] {f : Ω → β} {g : Ω → β'} (hf : Measurable f) (hg : Measurable g)
    (h : IndepFun f g ν) :
    IndepFun (fun ω : α × Ω => (ω.1, f ω.2)) (fun ω : α × Ω => g ω.2) (μ.prod ν) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  have hm1 : Measurable fun ω : α × Ω => (ω.1, f ω.2) :=
    measurable_fst.prodMk (hf.comp measurable_snd)
  have hm2 : Measurable fun ω : α × Ω => g ω.2 := hg.comp measurable_snd
  rw [Measure.prod_apply ((hm1 hs).inter (hm2 ht)), Measure.prod_apply (hm1 hs),
    Measure.prod_apply (hm2 ht)]
  have hsec2 : ∀ x : α, Prod.mk x ⁻¹' ((fun ω : α × Ω => g ω.2) ⁻¹' t) = g ⁻¹' t := by
    intro x
    ext y
    simp
  have hind : ∀ x : α, ν (Prod.mk x ⁻¹' ((fun ω : α × Ω => (ω.1, f ω.2)) ⁻¹' s
        ∩ (fun ω : α × Ω => g ω.2) ⁻¹' t))
      = ν (Prod.mk x ⁻¹' ((fun ω : α × Ω => (ω.1, f ω.2)) ⁻¹' s)) * ν (g ⁻¹' t) := by
    intro x
    have hsec : Prod.mk x ⁻¹' ((fun ω : α × Ω => (ω.1, f ω.2)) ⁻¹' s
        ∩ (fun ω : α × Ω => g ω.2) ⁻¹' t) = f ⁻¹' (Prod.mk x ⁻¹' s) ∩ g ⁻¹' t := by
      ext y
      simp
    have hsec1 : Prod.mk x ⁻¹' ((fun ω : α × Ω => (ω.1, f ω.2)) ⁻¹' s)
        = f ⁻¹' (Prod.mk x ⁻¹' s) := by
      ext y
      simp
    rw [hsec, hsec1]
    exact h _ _ (measurable_prodMk_left hs) ht
  simp_rw [hind, hsec2]
  rw [lintegral_mul_const _ (measurable_measure_prodMk_left (hm1 hs)), lintegral_const,
    measure_univ, mul_one]

end Prod

end ProbabilityTheory
