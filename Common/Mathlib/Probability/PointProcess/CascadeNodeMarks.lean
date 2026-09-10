/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.PointProcess.CascadeBranches

/-!
# The marks of a cascade, node by node

The **nodes** of a `k`-level tree are the addresses `⟨p, u⟩` with `p < k` and
`u : Fin (p+1) → ℕ × ℕ`; the mark of the node `⟨p, u⟩` is Talagrand's `z_{p+1, u}`, extracted
from the marks `CascadeMarks T k` by `nodeMark`. The main theorem, `cascadeMarksLaw_map_nodeMarks`,
says that under the law of the marks the family of all node marks is an **infinite product**
`⊗_{⟨p,u⟩} μ_p` — the marks of distinct nodes are independent, with the law of their level. In
particular (`infinitePi_map_restrict`) the marks of any finite set of nodes — the nodes of a
truncated tree — have the product law `⊗ μ_p`; for Gaussian levels this is the Gaussian family
`(z_{p,α})` of Guerra's broken replica-symmetry bound (Talagrand, Vol. II, (14.72)–(14.74)).
-/

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace ProbabilityTheory

noncomputable section

universe u

/-! ### Nodes -/

/-- The nodes of a `k`-level tree: an address of depth `p + 1`, `p < k`. -/
abbrev CascadeNode (k : ℕ) : Type := Σ p : Fin k, (Fin (p.val + 1) → ℕ × ℕ)

/-- A node of a `(k+1)`-level tree is either a node of depth `1`, i.e. an index `(n, j)`, or an
index `(n, j)` followed by a node of the `k`-level sub-tree. -/
def cascadeNodeSuccEquiv (k : ℕ) : CascadeNode (k + 1) ≃ (ℕ × ℕ) ⊕ ((ℕ × ℕ) × CascadeNode k) where
  toFun v := Fin.cases (motive := fun p : Fin (k + 1) => (Fin (p.val + 1) → ℕ × ℕ) →
      (ℕ × ℕ) ⊕ ((ℕ × ℕ) × CascadeNode k))
    (fun u => Sum.inl (u 0)) (fun q u => Sum.inr (u 0, ⟨q, Fin.tail u⟩)) v.1 v.2
  invFun := Sum.elim (fun nj => ⟨0, fun _ => nj⟩) (fun p => ⟨p.2.1.succ, Fin.cons p.1 p.2.2⟩)
  left_inv := by
    rintro ⟨p, u⟩
    induction p using Fin.cases with
    | zero =>
      simp only [Fin.cases_zero, Sum.elim_inl]
      refine Sigma.ext rfl (heq_of_eq ?_)
      funext i
      have hi : i = 0 := Fin.ext (Nat.lt_one_iff.1 (by simpa using i.isLt))
      rw [hi]
    | succ q =>
      simp only [Fin.cases_succ, Sum.elim_inr, Fin.cons_self_tail]
  right_inv := by
    rintro (nj | ⟨nj, q, u⟩)
    · rfl
    · simp only [Sum.elim_inr, Fin.cases_succ, Fin.cons_zero, Fin.tail_cons]

variable {T : Type u} [MeasurableSpace T]

/-! ### Node marks -/

/-- The mark `z_{p+1, u}` of the node `⟨p, u⟩`. -/
def nodeMark : (k : ℕ) → CascadeMarks T k → CascadeNode k → T
  | 0, _, v => v.1.elim0
  | k + 1, z, v =>
    Fin.cases (motive := fun p : Fin (k + 1) => (Fin (p.val + 1) → ℕ × ℕ) → T)
      (fun u => z.1 (u 0).1 (u 0).2) (fun q u => nodeMark k (z.2 (u 0).1 (u 0).2) ⟨q, Fin.tail u⟩)
      v.1 v.2

/-- All node marks, as a function on the nodes. -/
def nodeMarks (k : ℕ) (z : CascadeMarks T k) : CascadeNode k → T := nodeMark k z

/-- The node marks of a `(k+1)`-level cascade in terms of the first level and the sub-trees. -/
def nodeMarksStep (k : ℕ) (a : ℕ → ℕ → T) (b : ℕ → ℕ → CascadeNode k → T) :
    CascadeNode (k + 1) → T := fun v =>
  Fin.cases (motive := fun p : Fin (k + 1) => (Fin (p.val + 1) → ℕ × ℕ) → T)
    (fun u => a (u 0).1 (u 0).2) (fun q u => b (u 0).1 (u 0).2 ⟨q, Fin.tail u⟩) v.1 v.2

omit [MeasurableSpace T] in
lemma nodeMarks_succ (k : ℕ) (z : CascadeMarks T (k + 1)) :
    nodeMarks (k + 1) z = nodeMarksStep k z.1 (fun n j => nodeMarks k (z.2 n j)) := rfl

lemma measurable_nodeMarks : ∀ k, Measurable (nodeMarks (T := T) k)
  | 0 => by
    refine measurable_pi_lambda _ fun v => ?_
    exact v.1.elim0
  | k + 1 => by
    have ih := measurable_nodeMarks k
    refine measurable_pi_lambda _ fun v => ?_
    rcases v with ⟨p, u⟩
    induction p using Fin.cases with
    | zero =>
      exact (measurable_pi_apply (u 0).2).comp ((measurable_pi_apply (u 0).1).comp measurable_fst)
    | succ q =>
      exact (measurable_pi_apply (⟨q, Fin.tail u⟩ : CascadeNode k)).comp
        (ih.comp ((measurable_pi_apply (u 0).2).comp
          ((measurable_pi_apply (u 0).1).comp measurable_snd)))

lemma measurable_nodeMarksStep (k : ℕ) :
    Measurable fun q : (ℕ → ℕ → T) × (ℕ → ℕ → CascadeNode k → T) => nodeMarksStep k q.1 q.2 := by
  refine measurable_pi_lambda _ fun v => ?_
  rcases v with ⟨p, u⟩
  induction p using Fin.cases with
  | zero =>
    exact (measurable_pi_apply (u 0).2).comp ((measurable_pi_apply (u 0).1).comp measurable_fst)
  | succ q =>
    exact (measurable_pi_apply (⟨q, Fin.tail u⟩ : CascadeNode k)).comp
      ((measurable_pi_apply (u 0).2).comp ((measurable_pi_apply (u 0).1).comp measurable_snd))

/-! ### The law of the node marks -/

/-- **The node marks of a cascade form an infinite product**: under `cascadeMarksLaw k μs`, the
family `(z_{p+1,u})_{⟨p,u⟩}` of all node marks has law `⊗_{⟨p,u⟩} μs p`. -/
theorem cascadeMarksLaw_map_nodeMarks : ∀ (k : ℕ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)],
    (cascadeMarksLaw k μs).map (nodeMarks k)
      = Measure.infinitePi (fun v : CascadeNode k => μs v.1)
  | 0, μs, _ => by
    refine Measure.ext fun s hs => ?_
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    · have hs' : s = univ := Set.eq_univ_of_forall fun x => by
        obtain ⟨y, hy⟩ := hne
        rwa [Subsingleton.elim x y]
      have hZ0 : cascadeMarksLaw 0 μs univ = 1 :=
        (cascadeMarksLawAux 0 fun i => ⟨μs i, inferInstance⟩).2.measure_univ
      have hP : Measure.infinitePi (fun v : CascadeNode 0 => μs v.1) univ = 1 := measure_univ
      rw [hs', Measure.map_apply (measurable_nodeMarks 0) MeasurableSet.univ, Set.preimage_univ,
        hZ0, hP]
  | k + 1, μs, _ => by
    rw [cascadeMarksLaw_succ]
    -- (1) the sub-trees: `ΠΠ Z_k` maps to `ΠΠ (⊗ ν_k)`
    have hZ := cascadeMarksLaw_map_nodeMarks k (Fin.tail μs)
    have h1 : (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
          cascadeMarksLaw k (Fin.tail μs)).map (fun y n j => nodeMarks k (y n j))
        = Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
            Measure.infinitePi (fun v : CascadeNode k => Fin.tail μs v.1) := by
      have hm : Measurable fun y : ℕ → CascadeMarks T k => fun j => nodeMarks k (y j) :=
        measurable_pi_lambda _ fun j => (measurable_nodeMarks k).comp (measurable_pi_apply j)
      rw [Measure.infinitePi_map_pi (fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
        cascadeMarksLaw k (Fin.tail μs)) (f := fun _ => fun y j => nodeMarks k (y j)) (fun _ => hm)]
      simp_rw [Measure.infinitePi_map_pi (fun _ : ℕ => cascadeMarksLaw k (Fin.tail μs))
        (f := fun _ => nodeMarks k) (fun _ => measurable_nodeMarks k), hZ]
    -- (2) flatten the sub-tree marks and the first-level marks
    have h2 : (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi (fun v : CascadeNode k => Fin.tail μs v.1))
        = (Measure.infinitePi fun p : (ℕ × ℕ) × CascadeNode k => Fin.tail μs p.2.1).map
            ((MeasurableEquiv.curry ℕ ℕ (CascadeNode k → T))
              ∘ (MeasurableEquiv.curry (ℕ × ℕ) (CascadeNode k) T)) := by
      rw [← Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _),
        Measure.infinitePi_map_curry (fun (_ : ℕ × ℕ) (v : CascadeNode k) => Fin.tail μs v.1),
        Measure.infinitePi_map_curry (fun (_ : ℕ) (_ : ℕ) =>
          Measure.infinitePi fun v : CascadeNode k => Fin.tail μs v.1)]
    have h3 : (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => μs 0)
        = (Measure.infinitePi fun _ : ℕ × ℕ => μs 0).map (MeasurableEquiv.curry ℕ ℕ T) :=
      (Measure.infinitePi_map_curry (fun (_ : ℕ) (_ : ℕ) => μs 0)).symm
    -- (3) the node marks factor through the first level and the sub-trees
    have hg₁ : Measurable fun y : ℕ → ℕ → CascadeMarks T k => fun n j => nodeMarks k (y n j) :=
      measurable_pi_lambda _ fun n => measurable_pi_lambda _ fun j =>
        (measurable_nodeMarks k).comp ((measurable_pi_apply j).comp (measurable_pi_apply n))
    have hfun : (nodeMarks (k + 1) : CascadeMarks T (k + 1) → CascadeNode (k + 1) → T)
        = (fun q : (ℕ → ℕ → T) × (ℕ → ℕ → CascadeNode k → T) => nodeMarksStep k q.1 q.2)
          ∘ Prod.map id (fun y n j => nodeMarks k (y n j)) := by
      funext z
      rfl
    rw [hfun, ← Measure.map_map (measurable_nodeMarksStep k) (measurable_id.prodMap hg₁),
      ← Measure.map_prod_map _ _ measurable_id hg₁, Measure.map_id, h1, h2, h3,
      Measure.map_prod_map _ _ (MeasurableEquiv.measurable _)
        ((MeasurableEquiv.measurable _).comp (MeasurableEquiv.measurable _)),
      Measure.infinitePi_prod_infinitePi_eq_map,
      ← Measure.infinitePi_map_piCongrLeft _ (cascadeNodeSuccEquiv k)]
    -- (4) identify the family and the composite map
    have hfam : Measure.infinitePi (fun v : CascadeNode (k + 1) =>
        Sum.elim (fun _ : ℕ × ℕ => μs 0) (fun p : (ℕ × ℕ) × CascadeNode k => Fin.tail μs p.2.1)
          (cascadeNodeSuccEquiv k v))
        = Measure.infinitePi (fun v : CascadeNode (k + 1) => μs v.1) := by
      refine Measure.infinitePi_congr fun v => ?_
      rcases v with ⟨p, u⟩
      induction p using Fin.cases with
      | zero => rfl
      | succ q => rfl
    rw [hfam, Measure.map_map (measurable_nodeMarksStep k)
        ((MeasurableEquiv.measurable _).prodMap
          ((MeasurableEquiv.measurable _).comp (MeasurableEquiv.measurable _))),
      Measure.map_map ((measurable_nodeMarksStep k).comp ((MeasurableEquiv.measurable _).prodMap
          ((MeasurableEquiv.measurable _).comp (MeasurableEquiv.measurable _))))
        (MeasurableEquiv.measurable _),
      Measure.map_map (((measurable_nodeMarksStep k).comp ((MeasurableEquiv.measurable _).prodMap
          ((MeasurableEquiv.measurable _).comp (MeasurableEquiv.measurable _)))).comp
            (MeasurableEquiv.measurable _)) (MeasurableEquiv.measurable _)]
    have hid : ((((fun q : (ℕ → ℕ → T) × (ℕ → ℕ → CascadeNode k → T) => nodeMarksStep k q.1 q.2)
        ∘ Prod.map (MeasurableEquiv.curry ℕ ℕ T)
            ((MeasurableEquiv.curry ℕ ℕ (CascadeNode k → T))
              ∘ (MeasurableEquiv.curry (ℕ × ℕ) (CascadeNode k) T)))
        ∘ (MeasurableEquiv.sumPiEquivProdPi fun _ : (ℕ × ℕ) ⊕ ((ℕ × ℕ) × CascadeNode k) => T))
        ∘ (MeasurableEquiv.piCongrLeft (fun _ => T) (cascadeNodeSuccEquiv k)))
        = id := by
      funext f
      funext v
      rcases v with ⟨p, u⟩
      induction p using Fin.cases with
      | zero =>
        have := Equiv.piCongrLeft_apply_apply (fun _ => T) (cascadeNodeSuccEquiv k) f ⟨0, u⟩
        exact this
      | succ q =>
        have := Equiv.piCongrLeft_apply_apply (fun _ => T) (cascadeNodeSuccEquiv k) f ⟨q.succ, u⟩
        exact this
    rw [hid, Measure.map_id]

/-! ### Branch marks are node marks at the prefixes -/

/-- The prefix of length `p + 1` of a branch: the node `α|_{p+1}`. -/
def branchPrefix {k : ℕ} (α : Fin k → ℕ × ℕ) (p : Fin k) : Fin (p.val + 1) → ℕ × ℕ :=
  fun i => α ⟨i.val, by omega⟩

omit [MeasurableSpace T] in
/-- The mark at level `p + 1` along the branch `α` is the mark of the node `α|_{p+1}`. -/
theorem branchMarks_eq_nodeMark : ∀ (k : ℕ) (z : CascadeMarks T k) (α : Fin k → ℕ × ℕ)
    (p : Fin k), branchMarks k z α p = nodeMark k z ⟨p, branchPrefix α p⟩
  | 0, _, _, p => p.elim0
  | k + 1, z, α, p => by
    induction p using Fin.cases with
    | zero => rfl
    | succ q =>
      show branchMarks k (z.2 (α 0).1 (α 0).2) (Fin.tail α) q = _
      rw [branchMarks_eq_nodeMark k]
      rfl

end

end ProbabilityTheory
