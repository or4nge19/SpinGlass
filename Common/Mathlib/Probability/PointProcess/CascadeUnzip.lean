/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.PointProcess.Cascade
import Common.Mathlib.Probability.PointProcess.Marking

/-!
# Unzipping a cascade into its weights and its marks

A `k`-level Poisson–Dirichlet cascade (`cascadeLaw`) is a Poisson–Dirichlet process whose marks
are `(z, sub-cascade)`. Unzipping every level with the marking representation
(`pdSampleLaw_eq_map`) exhibits the cascade sample as the image of a **product**
`(weights) ⊗ (marks)`: the weights `CascadeWeights k` are the unmarked Poisson–Dirichlet samples
of every node of the tree, the marks `CascadeMarks T k` are an i.i.d. array of marks of every
node, and they are independent (`cascadeLaw_eq_map_cascadeZip`). This is the form in which one
can condition a cascade on its weights: for fixed weights the marks are still i.i.d. — for
Gaussian marks, a Gaussian family — which is what Guerra's broken replica-symmetry bound needs
(Talagrand, Vol. II, §14.4).
-/

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace ProbabilityTheory

noncomputable section

universe u

/-! ### The weights and the marks of a cascade -/

/-- The weights of a `k`-level cascade: at each level, the unmarked Poisson–Dirichlet sample of
the level and the weights of the sub-cascades attached to the (indexed) points. -/
abbrev CascadeWeights : ℕ → Type
  | 0 => PUnit
  | k + 1 => SuperSample ℝ × (ℕ → ℕ → CascadeWeights k)

/-- The marks of a `k`-level cascade with marks in `T`: at each level, the array of marks of the
(indexed) points and the marks of the sub-cascades. -/
abbrev CascadeMarks (T : Type u) : ℕ → Type u
  | 0 => PUnit
  | k + 1 => (ℕ → ℕ → T) × (ℕ → ℕ → CascadeMarks T k)

instance instMeasurableSpaceCascadeWeights : ∀ k, MeasurableSpace (CascadeWeights k)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | k + 1 =>
    letI := instMeasurableSpaceCascadeWeights k
    inferInstanceAs (MeasurableSpace (SuperSample ℝ × (ℕ → ℕ → CascadeWeights k)))

variable {T : Type u} [MeasurableSpace T]

instance instMeasurableSpaceCascadeMarks : ∀ k, MeasurableSpace (CascadeMarks T k)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | k + 1 =>
    letI := instMeasurableSpaceCascadeMarks k
    inferInstanceAs (MeasurableSpace ((ℕ → ℕ → T) × (ℕ → ℕ → CascadeMarks T k)))

/-- Zipping weights and marks into a cascade sample. -/
def cascadeZip : (k : ℕ) → CascadeWeights k × CascadeMarks T k → CascadeSpace T k
  | 0, _ => PUnit.unit
  | k + 1, q => superZip (q.1.1, fun n j => (q.2.1 n j, cascadeZip k (q.1.2 n j, q.2.2 n j)))

omit [MeasurableSpace T] in
lemma cascadeZip_succ (k : ℕ) (q : CascadeWeights (k + 1) × CascadeMarks T (k + 1)) :
    cascadeZip (k + 1) q
      = superZip (q.1.1, fun n j => (q.2.1 n j, cascadeZip k (q.1.2 n j, q.2.2 n j))) := rfl

lemma measurable_cascadeZip : ∀ k, Measurable (cascadeZip (T := T) k)
  | 0 => measurable_const
  | k + 1 => by
    have ih := measurable_cascadeZip k
    refine measurable_superZip.comp ((measurable_fst.comp measurable_fst).prodMk ?_)
    refine measurable_pi_lambda _ fun n => measurable_pi_lambda _ fun j => ?_
    refine ((measurable_pi_apply j).comp ((measurable_pi_apply n).comp
      (measurable_fst.comp measurable_snd))).prodMk ?_
    exact ih.comp (((measurable_pi_apply j).comp ((measurable_pi_apply n).comp
      (measurable_snd.comp measurable_fst))).prodMk ((measurable_pi_apply j).comp
      ((measurable_pi_apply n).comp (measurable_snd.comp measurable_snd))))

/-! ### The laws of the weights and of the marks -/

/-- The law of the weights, bundled with its probability-measure proof for the recursion. -/
def cascadeWeightsLawAux : (k : ℕ) → (Fin k → ℝ) →
    {P : Measure (CascadeWeights k) // IsProbabilityMeasure P}
  | 0, _ => ⟨Measure.dirac PUnit.unit, inferInstance⟩
  | k + 1, ms =>
    haveI := (cascadeWeightsLawAux k (Fin.tail ms)).2
    ⟨(pdWeightsLaw (ms 0)).prod (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
        (cascadeWeightsLawAux k (Fin.tail ms)).1), inferInstance⟩

/-- **The law of the weights of a `k`-level cascade** with parameters `ms`: independent unmarked
Poisson–Dirichlet samples at every node of the tree. -/
def cascadeWeightsLaw (k : ℕ) (ms : Fin k → ℝ) : Measure (CascadeWeights k) :=
  (cascadeWeightsLawAux k ms).1

instance (k : ℕ) (ms : Fin k → ℝ) : IsProbabilityMeasure (cascadeWeightsLaw k ms) :=
  (cascadeWeightsLawAux k ms).2

lemma cascadeWeightsLaw_zero (ms : Fin 0 → ℝ) :
    cascadeWeightsLaw 0 ms = Measure.dirac PUnit.unit := rfl

lemma cascadeWeightsLaw_succ (k : ℕ) (ms : Fin (k + 1) → ℝ) :
    cascadeWeightsLaw (k + 1) ms
      = (pdWeightsLaw (ms 0)).prod (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
          cascadeWeightsLaw k (Fin.tail ms)) := rfl

/-- The law of the marks, bundled with its probability-measure proof for the recursion. -/
def cascadeMarksLawAux : (k : ℕ) → (Fin k → {μ : Measure T // IsProbabilityMeasure μ}) →
    {P : Measure (CascadeMarks T k) // IsProbabilityMeasure P}
  | 0, _ => ⟨Measure.dirac PUnit.unit, inferInstance⟩
  | k + 1, μs =>
    haveI := (μs 0).2
    haveI := (cascadeMarksLawAux k (Fin.tail μs)).2
    ⟨(Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => (μs 0).1).prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
          (cascadeMarksLawAux k (Fin.tail μs)).1), inferInstance⟩

/-- **The law of the marks of a `k`-level cascade** with mark laws `μs`: an independent i.i.d.
array of marks at every level. -/
def cascadeMarksLaw (k : ℕ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)] :
    Measure (CascadeMarks T k) :=
  (cascadeMarksLawAux k fun i => ⟨μs i, inferInstance⟩).1

instance (k : ℕ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)] :
    IsProbabilityMeasure (cascadeMarksLaw k μs) :=
  (cascadeMarksLawAux k fun i => ⟨μs i, inferInstance⟩).2

lemma cascadeMarksLaw_zero (μs : Fin 0 → Measure T) [∀ i, IsProbabilityMeasure (μs i)] :
    cascadeMarksLaw 0 μs = Measure.dirac PUnit.unit := rfl

lemma cascadeMarksLaw_succ (k : ℕ) (μs : Fin (k + 1) → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] :
    cascadeMarksLaw (k + 1) μs
      = (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => μs 0).prod
          (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
            cascadeMarksLaw k (Fin.tail μs)) := rfl

/-! ### The unzipping theorem -/

variable [Nonempty T]

/-- **A cascade is its weights zipped with its marks, and they are independent**:
`cascadeLaw k ms μs = ((cascadeWeightsLaw k ms) ⊗ (cascadeMarksLaw k μs)).map (cascadeZip k)`. -/
theorem cascadeLaw_eq_map_cascadeZip : ∀ (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)],
    cascadeLaw k ms μs = ((cascadeWeightsLaw k ms).prod (cascadeMarksLaw k μs)).map (cascadeZip k)
  | 0, ms, μs, _ => by
    have hW : cascadeWeightsLaw 0 ms univ = 1 := (cascadeWeightsLawAux 0 ms).2.measure_univ
    have hZ : cascadeMarksLaw 0 μs univ = 1 :=
      (cascadeMarksLawAux 0 fun i => ⟨μs i, inferInstance⟩).2.measure_univ
    have huniv : ((cascadeWeightsLaw 0 ms).prod (cascadeMarksLaw 0 μs)) univ = 1 := by
      rw [← Set.univ_prod_univ, Measure.prod_prod, hW, hZ, mul_one]
    rw [cascadeLaw_zero, show cascadeZip (T := T) 0 = fun _ => PUnit.unit from rfl,
      Measure.map_const, huniv, one_smul]
  | k + 1, ms, μs, _ => by
    rw [cascadeLaw_succ, pdSampleLaw_eq_map,
      cascadeLaw_eq_map_cascadeZip k (Fin.tail ms) (Fin.tail μs),
      cascadeWeightsLaw_succ, cascadeMarksLaw_succ]
    have hzk := measurable_cascadeZip (T := T) k
    have hg : Measurable (Prod.map (id : T → T) (cascadeZip (T := T) k)) :=
      measurable_id.prodMap hzk
    -- (1) A ⊗ ((B ⊗ C).map zk) = (A ⊗ (B ⊗ C)).map (Prod.map id zk)
    have h1 : (μs 0).prod (((cascadeWeightsLaw k (Fin.tail ms)).prod
          (cascadeMarksLaw k (Fin.tail μs))).map (cascadeZip k))
        = ((μs 0).prod ((cascadeWeightsLaw k (Fin.tail ms)).prod
            (cascadeMarksLaw k (Fin.tail μs)))).map (Prod.map id (cascadeZip k)) := by
      rw [← Measure.map_prod_map _ _ measurable_id hzk, Measure.map_id]
    -- (2) ΠΠ (X.map g) = (ΠΠ X).map (x n j ↦ g (x n j))
    have hg1 : Measurable fun x : ℕ → T × (CascadeWeights k × CascadeMarks T k) =>
        fun i => Prod.map id (cascadeZip k) (x i) :=
      measurable_pi_lambda _ fun i => hg.comp (measurable_pi_apply i)
    have h2 : (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
          ((μs 0).prod ((cascadeWeightsLaw k (Fin.tail ms)).prod
            (cascadeMarksLaw k (Fin.tail μs)))).map (Prod.map id (cascadeZip k)))
        = (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
            (μs 0).prod ((cascadeWeightsLaw k (Fin.tail ms)).prod
              (cascadeMarksLaw k (Fin.tail μs)))).map
            (fun x n j => Prod.map id (cascadeZip k) (x n j)) := by
      simp_rw [Measure.infinitePi_map_eq _ (fun _ => hg)]
      rw [Measure.infinitePi_map_eq (fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
        (μs 0).prod ((cascadeWeightsLaw k (Fin.tail ms)).prod (cascadeMarksLaw k (Fin.tail μs))))
        (f := fun _ => fun x i => Prod.map id (cascadeZip k) (x i)) (fun _ => hg1)]
    -- (3), (4) the two-level zips
    have h3 := Measure.infinitePi_infinitePi_prod_eq_map (fun _ _ : ℕ => μs 0)
      (fun _ _ : ℕ => (cascadeWeightsLaw k (Fin.tail ms)).prod (cascadeMarksLaw k (Fin.tail μs)))
    have h4 := Measure.infinitePi_infinitePi_prod_eq_map
      (fun _ _ : ℕ => cascadeWeightsLaw k (Fin.tail ms)) (fun _ _ : ℕ => cascadeMarksLaw k (Fin.tail μs))
    -- (5) ΠΠA ⊗ (Y.map zip) = (ΠΠA ⊗ Y).map (Prod.map id zip)
    have hzipBC : Measurable fun p : (ℕ → ℕ → CascadeWeights k) × (ℕ → ℕ → CascadeMarks T k) =>
        fun i j => (p.1 i j, p.2 i j) := Measure.measurable_zip₂
    have h5 : (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => μs 0).prod
          (((Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
              cascadeWeightsLaw k (Fin.tail ms)).prod
            (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
              cascadeMarksLaw k (Fin.tail μs))).map
            (fun p : (ℕ → ℕ → CascadeWeights k) × (ℕ → ℕ → CascadeMarks T k) =>
              fun i j => (p.1 i j, p.2 i j)))
        = ((Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => μs 0).prod
            ((Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
                cascadeWeightsLaw k (Fin.tail ms)).prod
              (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
                cascadeMarksLaw k (Fin.tail μs)))).map
            (Prod.map id (fun p : (ℕ → ℕ → CascadeWeights k) × (ℕ → ℕ → CascadeMarks T k) =>
              fun i j => (p.1 i j, p.2 i j))) := by
      rw [← Measure.map_prod_map _ _ measurable_id hzipBC, Measure.map_id]
    -- (6) swap: ΠΠA ⊗ (ΠΠB ⊗ ΠΠC) = (ΠΠB ⊗ (ΠΠA ⊗ ΠΠC)).map s₃
    have h6 := Measure.prod_swap_left₃
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => μs 0)
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => cascadeWeightsLaw k (Fin.tail ms))
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => cascadeMarksLaw k (Fin.tail μs))
    rw [h1, h2, h3, h4, h5, h6]
    -- (7) merge the maps of the marks part
    have hs₃ : Measurable fun p : (ℕ → ℕ → CascadeWeights k) × ((ℕ → ℕ → T) × (ℕ → ℕ → CascadeMarks T k)) =>
        (p.2.1, (p.1, p.2.2)) :=
      (measurable_fst.comp measurable_snd).prodMk (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
    have hzipA : Measurable fun p : (ℕ → ℕ → T) × (ℕ → ℕ → CascadeWeights k × CascadeMarks T k) =>
        fun i j => (p.1 i j, p.2 i j) := Measure.measurable_zip₂
    have hg2 : Measurable fun x : ℕ → ℕ → T × (CascadeWeights k × CascadeMarks T k) =>
        fun n j => Prod.map id (cascadeZip k) (x n j) :=
      measurable_pi_lambda _ fun n => measurable_pi_lambda _ fun j =>
        hg.comp ((measurable_pi_apply j).comp (measurable_pi_apply n))
    rw [Measure.map_map (measurable_id.prodMap hzipBC) hs₃,
      Measure.map_map hzipA ((measurable_id.prodMap hzipBC).comp hs₃),
      Measure.map_map hg2 (hzipA.comp ((measurable_id.prodMap hzipBC).comp hs₃))]
    -- (8) W ⊗ (Y.map F) = (W ⊗ Y).map (Prod.map id F), and reassociate
    have hF : Measurable ((fun x : ℕ → ℕ → T × (CascadeWeights k × CascadeMarks T k) =>
        fun n j => Prod.map id (cascadeZip k) (x n j)) ∘
        ((fun p : (ℕ → ℕ → T) × (ℕ → ℕ → CascadeWeights k × CascadeMarks T k) =>
          fun i j => (p.1 i j, p.2 i j)) ∘
        ((Prod.map id fun p : (ℕ → ℕ → CascadeWeights k) × (ℕ → ℕ → CascadeMarks T k) =>
          fun i j => (p.1 i j, p.2 i j)) ∘
        (fun p : (ℕ → ℕ → CascadeWeights k) × ((ℕ → ℕ → T) × (ℕ → ℕ → CascadeMarks T k)) =>
          (p.2.1, (p.1, p.2.2)))))) :=
      hg2.comp (hzipA.comp ((measurable_id.prodMap hzipBC).comp hs₃))
    have h8 : (pdWeightsLaw (ms 0)).prod
          (((Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
              cascadeWeightsLaw k (Fin.tail ms)).prod
            ((Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => μs 0).prod
              (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
                cascadeMarksLaw k (Fin.tail μs)))).map
            ((fun x : ℕ → ℕ → T × (CascadeWeights k × CascadeMarks T k) =>
              fun n j => Prod.map id (cascadeZip k) (x n j)) ∘
            ((fun p : (ℕ → ℕ → T) × (ℕ → ℕ → CascadeWeights k × CascadeMarks T k) =>
              fun i j => (p.1 i j, p.2 i j)) ∘
            ((Prod.map id fun p : (ℕ → ℕ → CascadeWeights k) × (ℕ → ℕ → CascadeMarks T k) =>
              fun i j => (p.1 i j, p.2 i j)) ∘
            (fun p : (ℕ → ℕ → CascadeWeights k) × ((ℕ → ℕ → T) × (ℕ → ℕ → CascadeMarks T k)) =>
              (p.2.1, (p.1, p.2.2)))))))
        = ((pdWeightsLaw (ms 0)).prod
            ((Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
                cascadeWeightsLaw k (Fin.tail ms)).prod
              ((Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => μs 0).prod
                (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
                  cascadeMarksLaw k (Fin.tail μs))))).map
            (Prod.map id ((fun x : ℕ → ℕ → T × (CascadeWeights k × CascadeMarks T k) =>
              fun n j => Prod.map id (cascadeZip k) (x n j)) ∘
            ((fun p : (ℕ → ℕ → T) × (ℕ → ℕ → CascadeWeights k × CascadeMarks T k) =>
              fun i j => (p.1 i j, p.2 i j)) ∘
            ((Prod.map id fun p : (ℕ → ℕ → CascadeWeights k) × (ℕ → ℕ → CascadeMarks T k) =>
              fun i j => (p.1 i j, p.2 i j)) ∘
            (fun p : (ℕ → ℕ → CascadeWeights k) × ((ℕ → ℕ → T) × (ℕ → ℕ → CascadeMarks T k)) =>
              (p.2.1, (p.1, p.2.2))))))) := by
      rw [← Measure.map_prod_map _ _ measurable_id hF, Measure.map_id]
    rw [h8, ← Measure.prodAssoc_prod (μ := pdWeightsLaw (ms 0))
        (ν := Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
          cascadeWeightsLaw k (Fin.tail ms))
        (τ := (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => μs 0).prod
          (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
            cascadeMarksLaw k (Fin.tail μs))),
      Measure.map_map (measurable_id.prodMap hF) MeasurableEquiv.prodAssoc.measurable,
      Measure.map_map measurable_superZip ((measurable_id.prodMap hF).comp
        MeasurableEquiv.prodAssoc.measurable)]
    rfl

end

end ProbabilityTheory
