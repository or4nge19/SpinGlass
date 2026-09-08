/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Limit.AsymptoticArrayLaws
import Common.Mathlib.Probability.InfinitePiMarginal
import GibbsMeasure.Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Overlap-array integrals are finite Gibbs brackets

Talagrand states the Ghirlanda–Guerra identities and ultrametricity as properties of the *law of
the overlap array* (Vol. II, Ch. 15), and proves them by the *finite replica calculus* (Vol. II,
§12.2). Those are two different languages for the same numbers, and this file is the dictionary:

`∫ g(R_{l,l'})_{l,l' < n} d(overlapArrayLaw N H) = ⟨g((R(σˡ, σˡ'))_{l,l' < n})⟩_n`,

the right-hand side being `SpinGlass.FiniteGibbs.gibbs_average_n_det`. The proof is the
identification of the first `n` coordinates of an i.i.d. array with the `n`-fold product measure
(`SpinGlass.map_take_configReplicaArrayLaw`) followed by the change of variables.

Averaging over the disorder is the corresponding statement for
`SpinGlass.annealedOverlapArrayLaw`, and needs the Bochner integral against a measure bind
(`MeasureTheory.Measure.integral_bind`).

## Main statements

- `SpinGlass.map_take_configReplicaArrayLaw`: the first `n` replicas of the i.i.d. replica array
  form the finite `n`-replica Gibbs measure.
- `SpinGlass.integral_overlapArrayLaw_comp_blockRestrict`: **the dictionary**.
- `SpinGlass.integral_bind_overlapArrayLaw_comp_take`,
  `SpinGlass.integral_annealedOverlapArrayLaw_comp_take`: its disorder-averaged forms.
-/

open Filter Topology MeasureTheory MeasureTheory.GibbsMeasure
open scoped ProbabilityTheory

namespace SpinGlass

noncomputable section

/-! ### The finite marginals of the i.i.d. replica array -/

/-- **Any finite injectively-indexed family of replicas of the i.i.d. replica array is the finite
replica Gibbs measure.** This is the bridge between the asymptotic layer, where the array law
lives, and `SpinGlass.FiniteGibbs.ReplicaMeasure`, where the Gibbs brackets and the
Ghirlanda–Guerra combination live. -/
theorem map_take_configReplicaArrayLaw (N k : ℕ) (H : EnergySpace N) {e : Fin k → ℕ}
    (he : Function.Injective e) :
    (configReplicaArrayLaw N H).map (fun ω (l : Fin k) => ω (e l))
      = FiniteGibbs.replicaGibbsMeasure (α := Config N) k H := by
  rw [configReplicaArrayLaw,
    Measure.map_comp_infinitePi_const (ν := FiniteGibbs.gibbsMeasure (α := Config N) H)
      (f := e) he, FiniteGibbs.replicaGibbsMeasure]

lemma measurable_take_config (N k : ℕ) (e : Fin k → ℕ) :
    Measurable fun ω : ℕ → Config N => fun l : Fin k => ω (e l) :=
  measurable_pi_lambda _ fun l => measurable_pi_apply (e l)

lemma measurable_select_entries (k : ℕ) (e : Fin k → ℕ) :
    Measurable fun R : ℕ → ℕ → OverlapValue => fun l l' => R (e l) (e l') :=
  measurable_pi_lambda _ fun l => measurable_pi_lambda _ fun l' =>
    (measurable_pi_apply (e l')).comp (measurable_pi_apply (e l))

/-! ### The dictionary -/

/-- **Overlap-array integrals are finite Gibbs brackets.** For any injective indexing `e` of `k`
replica labels, a test function of the selected `k × k` overlap block integrates against the
overlap array law to the `k`-replica Gibbs average of the same function of the pairwise overlaps.

The generality in `e` is what makes the dictionary usable: the four terms of Talagrand's identity
(15.40) involve the overlap blocks on the labels `{0, …, n-1}`, on `{0, …, n}` and on the pair
`{0, n}`, all at once. -/
theorem integral_overlapArrayLaw_comp_take (N k : ℕ) (H : EnergySpace N) {e : Fin k → ℕ}
    (he : Function.Injective e) {g : (Fin k → Fin k → OverlapValue) → ℝ} (hg : Measurable g) :
    (∫ R, g (fun l l' => R (e l) (e l')) ∂(overlapArrayLaw N H))
      = FiniteGibbs.gibbs_average_n_det (α := Config N) (n := k) H
          (fun σs => g fun l l' => overlapUnit N (σs l) (σs l')) := by
  have hpair : Measurable (pairArray (overlapUnit N)) :=
    measurable_pairArray Measurable.of_discrete
  rw [overlapArrayLaw, integral_map (μ := configReplicaArrayLaw N H)
      (φ := pairArray (overlapUnit N)) (f := fun R => g (fun l l' => R (e l) (e l')))
      hpair.aemeasurable (hg.comp (measurable_select_entries k e)).aestronglyMeasurable]
  have hcomp : ∀ ω : ℕ → Config N,
      g (fun l l' => pairArray (overlapUnit N) ω (e l) (e l'))
        = (fun σs : FiniteGibbs.ReplicaSpace (α := Config N) k =>
            g fun l l' => overlapUnit N (σs l) (σs l')) (fun l : Fin k => ω (e l)) := fun ω => rfl
  rw [integral_congr_ae (Filter.Eventually.of_forall hcomp),
    ← integral_map (μ := configReplicaArrayLaw N H)
      (φ := fun ω : ℕ → Config N => fun l : Fin k => ω (e l))
      (f := fun σs : FiniteGibbs.ReplicaSpace (α := Config N) k =>
        g fun l l' => overlapUnit N (σs l) (σs l'))
      (measurable_take_config N k e).aemeasurable
      (StronglyMeasurable.of_discrete).aestronglyMeasurable,
    map_take_configReplicaArrayLaw N k H he]
  exact FiniteGibbs.integral_replicaGibbsMeasure_eq_gibbs_average_n_det (α := Config N) k H _

/-- The dictionary for the first `n × n` block: the case `e = Fin.val` of
`SpinGlass.integral_overlapArrayLaw_comp_take`. -/
theorem integral_overlapArrayLaw_comp_blockRestrict (N n : ℕ) (H : EnergySpace N)
    {g : (Fin n → Fin n → OverlapValue) → ℝ} (hg : Measurable g) :
    (∫ R, g (blockRestrict n R) ∂(overlapArrayLaw N H))
      = FiniteGibbs.gibbs_average_n_det (α := Config N) (n := n) H
          (fun σs => g fun l l' => overlapUnit N (σs l) (σs l')) :=
  integral_overlapArrayLaw_comp_take N n H Fin.val_injective hg

/-- The continuous-test-function form of the dictionary. -/
theorem integral_overlapArrayLaw_comp_take_continuousMap (N k : ℕ) (H : EnergySpace N)
    {e : Fin k → ℕ} (he : Function.Injective e)
    (g : C(Fin k → Fin k → OverlapValue, ℝ)) :
    (∫ R, g (fun l l' => R (e l) (e l')) ∂(overlapArrayLaw N H))
      = FiniteGibbs.gibbs_average_n_det (α := Config N) (n := k) H
          (fun σs => g fun l l' => overlapUnit N (σs l) (σs l')) :=
  integral_overlapArrayLaw_comp_take N k H he g.continuous.measurable

lemma continuous_select_entries (k : ℕ) (e : Fin k → ℕ) :
    Continuous fun R : ℕ → ℕ → OverlapValue => fun l l' => R (e l) (e l') :=
  continuous_pi fun l => continuous_pi fun l' =>
    (continuous_apply (e l')).comp (continuous_apply (e l))

/-! ### Averaging over the disorder -/

/-- **The disorder-averaged dictionary.** Mixing the overlap array law over a Hamiltonian law `ν`
integrates a test function of a `k × k` overlap block to the `ν`-average of the `k`-replica Gibbs
bracket — exactly the quantity `SpinGlass.FiniteGibbs.ghirlandaGuerraCombination` is built from. -/
theorem integral_bind_overlapArrayLaw_comp_take (N k : ℕ) (ν : Measure (EnergySpace N))
    [IsProbabilityMeasure ν] {e : Fin k → ℕ} (he : Function.Injective e)
    (g : C(Fin k → Fin k → OverlapValue, ℝ)) :
    (∫ R, g (fun l l' => R (e l) (e l')) ∂(ν.bind (overlapArrayLaw N)))
      = ∫ K, FiniteGibbs.gibbs_average_n_det (α := Config N) (n := k) K
          (fun σs => g fun l l' => overlapUnit N (σs l) (σs l')) ∂ν := by
  have hmeas : Measurable (overlapArrayLaw N) := measurable_overlapArrayLaw N
  have hprob : IsProbabilityMeasure (ν.bind (overlapArrayLaw N)) :=
    isProbabilityMeasure_bind hmeas.aemeasurable
      (Filter.Eventually.of_forall fun _ => inferInstance)
  have hint : Integrable (fun R => g (fun l l' => R (e l) (e l')))
      (ν.bind (overlapArrayLaw N)) :=
    integrable_of_continuous (μ := ν.bind (overlapArrayLaw N))
      (g.continuous.comp (continuous_select_entries k e))
  calc (∫ R, g (fun l l' => R (e l) (e l')) ∂(ν.bind (overlapArrayLaw N)))
      = ∫ K, ∫ R, g (fun l l' => R (e l) (e l')) ∂(overlapArrayLaw N K) ∂ν :=
        MeasureTheory.Measure.integral_bind
          (κ := (⟨overlapArrayLaw N, hmeas⟩ : ProbabilityTheory.Kernel (EnergySpace N) _)) hint
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun K =>
        integral_overlapArrayLaw_comp_take_continuousMap N k K he g)

section Random

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The annealed form of the dictionary, for a random Hamiltonian `U` on a probability space. -/
theorem integral_annealedOverlapArrayLaw_comp_take (N k : ℕ) {U : Ω → EnergySpace N}
    (hU : Measurable U) {e : Fin k → ℕ} (he : Function.Injective e)
    (g : C(Fin k → Fin k → OverlapValue, ℝ)) :
    (∫ R, g (fun l l' => R (e l) (e l')) ∂(annealedOverlapArrayLaw N U))
      = ∫ ω, FiniteGibbs.gibbs_average_n_det (α := Config N) (n := k) (U ω)
          (fun σs => g fun l l' => overlapUnit N (σs l) (σs l')) ∂(ℙ : Measure Ω) := by
  have hmeas : Measurable fun ω => overlapArrayLaw N (U ω) :=
    (measurable_overlapArrayLaw N).comp hU
  have hprob : IsProbabilityMeasure (annealedOverlapArrayLaw N U) :=
    isProbabilityMeasure_annealedOverlapArrayLaw N hU
  have hint : Integrable (fun R => g (fun l l' => R (e l) (e l')))
      (annealedOverlapArrayLaw N U) :=
    integrable_of_continuous (μ := annealedOverlapArrayLaw N U)
      (g.continuous.comp (continuous_select_entries k e))
  calc (∫ R, g (fun l l' => R (e l) (e l')) ∂(annealedOverlapArrayLaw N U))
      = ∫ ω, ∫ R, g (fun l l' => R (e l) (e l')) ∂(overlapArrayLaw N (U ω)) ∂(ℙ : Measure Ω) :=
        MeasureTheory.Measure.integral_bind
          (κ := (⟨fun ω => overlapArrayLaw N (U ω), hmeas⟩ : ProbabilityTheory.Kernel Ω _)) hint
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        integral_overlapArrayLaw_comp_take_continuousMap N k (U ω) he g)

end Random

end

end SpinGlass
