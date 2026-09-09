/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.PointProcess.CascadeNodeMarks

/-!
# The marks of a truncated tree

The tree of a `k`-level cascade truncated to the indices `< M` at every level has finitely many
nodes (`TruncNode k M`), and the marks of these nodes (`truncMarks`) are, under the law of the
marks, an independent family with the laws of their levels
(`cascadeMarksLaw_map_truncMarks`, a finite `Measure.pi`), by restriction of the infinite product
of all node marks (`cascadeMarksLaw_map_nodeMarks`).
-/

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace ProbabilityTheory

noncomputable section

universe u

/-- The nodes of the tree truncated to the indices `< M`. -/
abbrev TruncNode (k M : ℕ) : Type := Σ p : Fin k, (Fin (p.val + 1) → Fin M × Fin M)

/-- A node of the truncated tree, as a node of the tree. -/
def truncNodeEmb (k M : ℕ) (v : TruncNode k M) : CascadeNode k :=
  ⟨v.1, fun i => ((v.2 i).1, (v.2 i).2)⟩

lemma truncNodeEmb_injective (k M : ℕ) : Function.Injective (truncNodeEmb k M) := by
  rintro ⟨p, u⟩ ⟨q, w⟩ h
  simp only [truncNodeEmb, Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  refine Sigma.ext rfl (heq_of_eq ?_)
  funext i
  have := congrFun (eq_of_heq h) i
  ext <;> simp only [Prod.mk.injEq] at this
  · exact_mod_cast this.1
  · exact_mod_cast this.2

variable {T : Type u} [MeasurableSpace T]

/-- The marks of the nodes of the truncated tree. -/
def truncMarks (k M : ℕ) (z : CascadeMarks T k) : TruncNode k M → T :=
  fun v => nodeMark k z (truncNodeEmb k M v)

lemma measurable_truncMarks (k M : ℕ) : Measurable (truncMarks (T := T) k M) :=
  measurable_pi_lambda _ fun v => (measurable_pi_apply (truncNodeEmb k M v)).comp
    (measurable_nodeMarks k)

/-- **The marks of the truncated tree are independent, with the laws of their levels.** -/
theorem cascadeMarksLaw_map_truncMarks (k M : ℕ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] :
    (cascadeMarksLaw k μs).map (truncMarks k M)
      = Measure.pi (fun v : TruncNode k M => μs v.1) := by
  classical
  set I : Finset (CascadeNode k) :=
    Finset.univ.map ⟨truncNodeEmb k M, truncNodeEmb_injective k M⟩ with hI
  have hrange : Set.range (truncNodeEmb k M) = (I : Set (CascadeNode k)) := by
    rw [hI, Finset.coe_map, Finset.coe_univ, Set.image_univ]
    rfl
  let e : TruncNode k M ≃ I :=
    (Equiv.ofInjective _ (truncNodeEmb_injective k M)).trans (Equiv.setCongr hrange)
  have he : ∀ v, (e v : CascadeNode k) = truncNodeEmb k M v := fun v => rfl
  have hfun : truncMarks (T := T) k M
      = (fun f : (i : I) → T => fun v => f (e v)) ∘ I.restrict ∘ nodeMarks k := by
    funext z v
    rfl
  have hA : Measurable fun f : (i : I) → T => fun v => f (e v) :=
    measurable_pi_lambda _ fun v => measurable_pi_apply (e v)
  have hB : Measurable (I.restrict : (CascadeNode k → T) → (i : I) → T) := measurable_restrict _
  rw [hfun, ← Measure.map_map hA (hB.comp (measurable_nodeMarks k)),
    ← Measure.map_map hB (measurable_nodeMarks k),
    cascadeMarksLaw_map_nodeMarks, Measure.infinitePi_map_restrict]
  have hmp := (measurePreserving_piCongrLeft (fun i : I => μs (i : CascadeNode k).1) e).symm
    (MeasurableEquiv.piCongrLeft (fun _ => T) e)
  have hcoe : (fun f : (i : I) → T => fun v => f (e v))
      = ⇑(MeasurableEquiv.piCongrLeft (fun _ => T) e).symm := by
    funext f v
    rfl
  rw [hcoe, hmp.map_eq]
  rfl

end

end ProbabilityTheory
