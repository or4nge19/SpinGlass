/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.PointProcess.PoissonDirichlet
import Common.Mathlib.Probability.ProductMeasureProd

/-!
# The marking representation of a marked Poisson point process

A Poisson point process with a **product** intensity `Λ ⊗ η`, `η` a probability measure, is the
process with intensity `Λ` whose points carry i.i.d. marks of law `η`, independent of the points.
In the sample space of the superposition (`SuperSample`), when each piece of the decomposition is a
product `νₙ ⊗ η` with `νₙ ≠ 0`, this is an identity between measures on the sample space:

* `positionLaw (ν ⊗ η) = positionLaw ν ⊗ η` (`ProbabilityTheory.positionLaw_prod`);
* the sample of a finite piece with intensity `ν ⊗ η` is the sample with intensity `ν` zipped with
  an i.i.d. sequence of marks (`ProbabilityTheory.poissonSampleLaw_prod`);
* the sample of the superposition of the pieces `νₙ ⊗ η` is the superposition of the `νₙ` zipped
  with an i.i.d. array of marks (`ProbabilityTheory.superSampleLaw_prod`).

For the marked Poisson–Dirichlet process this gives `ProbabilityTheory.pdSampleLaw_eq_map`:
the marked sample is the (unmarked) weights sample `pdWeightsLaw m` zipped with an i.i.d. array of
marks — the weights and the marks are independent by construction. This is what allows one to
condition a Poisson–Dirichlet cascade on its weights, as in Guerra's broken replica-symmetry
bound (Talagrand, Vol. II, §14.4).
-/

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace ProbabilityTheory

noncomputable section

variable {E M : Type*} [MeasurableSpace E] [MeasurableSpace M] [Nonempty E] [Nonempty M]

/-! ### Marking a finite piece -/

/-- The position law of a product `ν ⊗ η`, `η` a probability measure, is the product of the
position law of `ν` with `η`. -/
lemma positionLaw_prod (ν : Measure E) [IsFiniteMeasure ν] (hν : ν univ ≠ 0) (η : Measure M)
    [IsProbabilityMeasure η] : positionLaw (ν.prod η) = (positionLaw ν).prod η := by
  have h : (ν.prod η) univ = ν univ := by
    rw [← Set.univ_prod_univ, Measure.prod_prod, measure_univ (μ := η), mul_one]
  unfold positionLaw
  rw [h]
  simp only [hν, ↓reduceIte]
  rw [Measure.prod_smul_left]

/-- Zipping the positions of a finite Poisson sample with a sequence of marks. -/
def pieceZip (q : PoissonSample E × (ℕ → M)) : PoissonSample (E × M) :=
  ((fun j => (q.1.1 j, q.2 j)), q.1.2)

omit [Nonempty E] [Nonempty M] in
lemma measurable_pieceZip :
    Measurable (pieceZip : PoissonSample E × (ℕ → M) → PoissonSample (E × M)) :=
  (measurable_pi_lambda _ fun j => ((measurable_pi_apply j).comp
    (measurable_fst.comp measurable_fst)).prodMk ((measurable_pi_apply j).comp measurable_snd)).prodMk
    (measurable_snd.comp measurable_fst)

/-- **Marking a finite Poisson process**: the sample of the process with intensity `ν ⊗ η` is the
sample of the process with intensity `ν`, zipped with an independent i.i.d. sequence of marks of
law `η`. -/
theorem poissonSampleLaw_prod (ν : Measure E) [IsFiniteMeasure ν] (hν : ν univ ≠ 0)
    (η : Measure M) [IsProbabilityMeasure η] :
    poissonSampleLaw (ν.prod η)
      = ((poissonSampleLaw ν).prod (Measure.infinitePi fun _ : ℕ => η)).map pieceZip := by
  have huniv : (ν.prod η) univ = ν univ := by
    rw [← Set.univ_prod_univ, Measure.prod_prod, measure_univ (μ := η), mul_one]
  unfold poissonSampleLaw
  rw [positionLaw_prod ν hν η, huniv,
    Measure.infinitePi_prod_eq_map (fun _ : ℕ => positionLaw ν) (fun _ : ℕ => η),
    ← Measure.map_id (μ := poissonMeasure (ν univ).toNNReal),
    Measure.map_prod_map _ _ (MeasurableEquiv.arrowProdEquivProdArrow E M ℕ).symm.measurable
      measurable_id, Measure.map_id,
    Measure.prod_prod_swap_right]
  have hswap : Measurable fun p : ((ℕ → E) × ℕ) × (ℕ → M) => ((p.1.1, p.2), p.1.2) :=
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
      (measurable_snd.comp measurable_fst)
  rw [Measure.map_map
    ((MeasurableEquiv.arrowProdEquivProdArrow E M ℕ).symm.measurable.prodMap measurable_id) hswap]
  rfl

/-! ### Marking the superposition -/

/-- Zipping the pieces of a superposition sample with an array of marks. -/
def superZip (q : SuperSample E × (ℕ → ℕ → M)) : SuperSample (E × M) :=
  fun n => pieceZip (q.1 n, q.2 n)

omit [Nonempty E] [Nonempty M] in
lemma measurable_superZip :
    Measurable (superZip : SuperSample E × (ℕ → ℕ → M) → SuperSample (E × M)) :=
  measurable_pi_lambda _ fun n => measurable_pieceZip.comp
    (((measurable_pi_apply n).comp measurable_fst).prodMk ((measurable_pi_apply n).comp measurable_snd))

/-- **Marking a superposition**: the sample of the superposition of the product pieces `νₙ ⊗ η`
is the sample of the superposition of the `νₙ`, zipped with an independent i.i.d. array of marks
of law `η`. -/
theorem superSampleLaw_prod (ν : ℕ → Measure E) [∀ n, IsFiniteMeasure (ν n)]
    (hν : ∀ n, ν n univ ≠ 0) (η : Measure M) [IsProbabilityMeasure η] :
    superSampleLaw (fun n => (ν n).prod η)
      = ((superSampleLaw ν).prod
          (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => η)).map superZip := by
  unfold superSampleLaw
  simp_rw [poissonSampleLaw_prod (ν _) (hν _) η]
  have h1 := Measure.infinitePi_map_pi
    (fun n => (poissonSampleLaw (ν n)).prod (Measure.infinitePi fun _ : ℕ => η))
    (f := fun _ => pieceZip) (fun _ => measurable_pieceZip)
  rw [← h1, Measure.infinitePi_prod_eq_map (fun n => poissonSampleLaw (ν n))
      (fun _ => Measure.infinitePi fun _ : ℕ => η)]
  have hm1 : Measurable fun x : ℕ → PoissonSample E × (ℕ → M) => fun n => pieceZip (x n) :=
    measurable_pi_lambda _ fun n => measurable_pieceZip.comp (measurable_pi_apply n)
  have hm2 : Measurable
      (MeasurableEquiv.arrowProdEquivProdArrow (PoissonSample E) (ℕ → M) ℕ).symm :=
    MeasurableEquiv.measurable _
  have hfun : ((fun x : ℕ → PoissonSample E × (ℕ → M) => fun n => pieceZip (x n))
      ∘ (MeasurableEquiv.arrowProdEquivProdArrow (PoissonSample E) (ℕ → M) ℕ).symm)
      = (superZip : SuperSample E × (ℕ → ℕ → M) → SuperSample (E × M)) := by
    funext q
    rfl
  rw [Measure.map_map hm1 hm2, hfun]

/-! ### The marked Poisson–Dirichlet process -/

/-- The sample law of the **unmarked** Poisson–Dirichlet weights: the superposition of the
explicit pieces `stableSeq m n` of `μ_m`. -/
def pdWeightsLaw (m : ℝ) : Measure (SuperSample ℝ) := superSampleLaw (stableSeq m)

instance (m : ℝ) : IsProbabilityMeasure (pdWeightsLaw m) := by
  unfold pdWeightsLaw; infer_instance

/-- **The marking representation of the Poisson–Dirichlet process**: the marked sample is the
weights sample zipped with an independent i.i.d. array of marks of law `η`. -/
theorem pdSampleLaw_eq_map (m : ℝ) (η : Measure M) [IsProbabilityMeasure η] :
    pdSampleLaw m η
      = ((pdWeightsLaw m).prod
          (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => η)).map superZip :=
  superSampleLaw_prod (stableSeq m) (stableSeq_univ_ne_zero m) η

omit [Nonempty E] [Nonempty M] in
/-- The sum over the marked points, in the marking representation. -/
lemma lintegral_superCounting_superZip (q : SuperSample E × (ℕ → ℕ → M)) (φ : E × M → ℝ≥0∞)
    (hφ : Measurable φ) :
    ∫⁻ p, φ p ∂superCounting (superZip q)
      = ∑' n, ∑ j ∈ Finset.range (q.1 n).2, φ ((q.1 n).1 j, q.2 n j) := by
  rw [lintegral_superCounting]
  refine tsum_congr fun n => ?_
  rw [lintegral_countingMeasure _ hφ]
  rfl

end

end ProbabilityTheory
