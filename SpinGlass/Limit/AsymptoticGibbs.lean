/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Limit.Exchangeability
import SpinGlass.FiniteGibbs.ReplicaMeasure
import SpinGlass.Defs
import Common.Mathlib.Probability.InfinitePiMarginal

/-!
# The asymptotic Gibbs measure

Talagrand Vol. II, Ch. 12–15 and Panchenko's book both start from the same object: the limit, as
`N → ∞`, of the law of the i.i.d. **replica array** `(σ¹, σ², …)` drawn from the finite-volume
Gibbs measure. A configuration of `N` sites is read as an infinite spin configuration, so all these
laws live on the one compact metrizable space `(ℕ → Bool)^ℕ`; each of them is exchangeable in the
replica index because the replicas are i.i.d.; and Prokhorov's theorem supplies limit points.
Exchangeability survives the limit (`MeasureTheory.GibbsMeasure.isExchangeable_of_tendsto`), so de
Finetti's theorem represents every limit point as a mixture

`∫ λ^{⊗ℕ} m(dλ)`

of i.i.d. product measures over a **unique** probability measure `m` on the space of probability
measures on the spin space. That `m` is the *asymptotic Gibbs measure*: a random measure on spin
configurations, which is the object all of Vol. II's Ghirlanda–Guerra / ultrametricity theory is
about.

## Main statements

- `SpinGlass.spinLaw`, `SpinGlass.replicaArrayLaw`: the one-replica and replica-array laws, read on
  the space of infinite spin configurations.
- `SpinGlass.isExchangeable_replicaArrayLaw`: the replica array is exchangeable.
- `SpinGlass.map_take_replicaArrayLaw`: the first `n` replicas are the finite `n`-replica Gibbs
  measure — the bridge to `SpinGlass.FiniteGibbs.ReplicaMeasure`.
- `SpinGlass.annealedReplicaArrayLaw`, `SpinGlass.isExchangeable_annealedReplicaArrayLaw`: the
  disorder-averaged replica array of a *random* Hamiltonian, and its exchangeability.
- `SpinGlass.exists_asymptoticGibbsMeasure` and
  `SpinGlass.exists_asymptoticGibbsMeasure_random`: **the asymptotic Gibbs measure exists**, for an
  arbitrary sequence of (random) Hamiltonians and with no hypotheses whatsoever.
-/

open Filter Topology MeasureTheory MeasureTheory.GibbsMeasure
open scoped ProbabilityTheory

namespace SpinGlass

noncomputable section

/-- The space of infinite spin configurations — Talagrand's `Σ = {-1,1}^ℕ`, coded by `Bool`. It is
compact, metrizable and standard Borel, which is what makes every limit argument below work. -/
abbrev SpinSpace : Type := ℕ → Bool

/-- A configuration of `N` sites read as an infinite spin configuration, by freezing the sites
beyond `N`. This is the canonical embedding; every statement below is proved for an *arbitrary*
family of embeddings, so no convention is built into the theory. -/
def configExtend (N : ℕ) (σ : Config N) : SpinSpace :=
  fun i => if h : i < N then σ ⟨i, h⟩ else true

lemma measurable_configExtend (N : ℕ) : Measurable (configExtend N) := Measurable.of_discrete

/-! ### The replica array of a finite-volume Gibbs measure -/

section Finite

variable (N : ℕ) (H : EnergySpace N) (e : Config N → SpinSpace)

/-- The law of a single replica drawn from the size-`N` Gibbs measure, read on the space of
infinite spin configurations along an embedding `e`. -/
def spinLaw : Measure SpinSpace := (FiniteGibbs.gibbsMeasure (α := Config N) H).map e

instance isProbabilityMeasure_spinLaw : IsProbabilityMeasure (spinLaw N H e) :=
  Measure.isProbabilityMeasure_map (Measurable.of_discrete (f := e)).aemeasurable

/-- The law of the i.i.d. **replica array** `(σ¹, σ², …)` drawn from the size-`N` Gibbs measure. -/
def replicaArrayLaw : Measure (ℕ → SpinSpace) :=
  Measure.infinitePi fun _ : ℕ => spinLaw N H e

instance isProbabilityMeasure_replicaArrayLaw :
    IsProbabilityMeasure (replicaArrayLaw N H e) := by
  rw [replicaArrayLaw]; infer_instance

/-- **The replica array is exchangeable**: the replicas are i.i.d., so permuting finitely many of
them leaves the law unchanged. -/
theorem isExchangeable_replicaArrayLaw : IsExchangeable (replicaArrayLaw N H e) :=
  isExchangeable_infinitePi

/-- The replica-array law as a `ProbabilityMeasure`, the form the weak topology consumes. -/
def replicaArray : ProbabilityMeasure (ℕ → SpinSpace) :=
  ⟨replicaArrayLaw N H e, isProbabilityMeasure_replicaArrayLaw N H e⟩

@[simp] lemma replicaArray_toMeasure :
    (replicaArray N H e : Measure (ℕ → SpinSpace)) = replicaArrayLaw N H e := rfl

/-- **The first `n` replicas of the replica array are the finite `n`-replica Gibbs measure**,
transported along the embedding of configurations into the spin space. This is the bridge between
the finite replica calculus of `SpinGlass.FiniteGibbs.ReplicaMeasure` — where the Gibbs brackets
`gibbs_average_n_det` and the Ghirlanda–Guerra identities live — and the asymptotic layer. -/
theorem map_take_replicaArrayLaw (n : ℕ) :
    (replicaArrayLaw N H e).map (fun ω (l : Fin n) => ω (l : ℕ))
      = (FiniteGibbs.replicaGibbsMeasure (α := Config N) n H).map
          (fun σs (l : Fin n) => e (σs l)) := by
  rw [replicaArrayLaw,
    Measure.map_comp_infinitePi_const (ν := spinLaw N H e) (f := fun l : Fin n => (l : ℕ))
      Fin.val_injective,
    FiniteGibbs.replicaGibbsMeasure,
    Measure.pi_map_pi (f := fun _ : Fin n => e)
      (fun _ => (Measurable.of_discrete (f := e)).aemeasurable)]
  rfl

end Finite

/-! ### Random Hamiltonians: the annealed replica array

For a *random* Hamiltonian the Gibbs measure is random, and the object Talagrand and Panchenko
work with is the disorder-averaged replica-array law. Averaging preserves exchangeability
(`isExchangeable_bind`), so de Finetti applies to its limit points as well — and there the mixing
measure `m` is precisely the **law of the random asymptotic Gibbs measure**. -/

section Random

variable (N : ℕ) (e : Config N → SpinSpace)
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

lemma measurable_spinLaw : Measurable fun K : EnergySpace N => spinLaw N K e :=
  (Measure.measurable_map e (Measurable.of_discrete (f := e))).comp
    (FiniteGibbs.measurable_gibbsMeasure (α := Config N))

lemma measurable_replicaArrayLaw : Measurable fun K : EnergySpace N => replicaArrayLaw N K e :=
  Measure.measurable_infinitePi fun _ => measurable_spinLaw N e

/-- The **disorder-averaged (annealed) replica-array law** of a random Hamiltonian `U`. -/
def annealedReplicaArrayLaw (U : Ω → EnergySpace N) : Measure (ℕ → SpinSpace) :=
  (ℙ : Measure Ω).bind fun ω => replicaArrayLaw N (U ω) e

lemma isProbabilityMeasure_annealedReplicaArrayLaw {U : Ω → EnergySpace N} (hU : Measurable U) :
    IsProbabilityMeasure (annealedReplicaArrayLaw N e U) :=
  isProbabilityMeasure_bind ((measurable_replicaArrayLaw N e).comp hU).aemeasurable
    (Filter.Eventually.of_forall fun _ => inferInstance)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- **The annealed replica array is exchangeable.** Averaging over the disorder is a mixture, and a
mixture of exchangeable laws is exchangeable. -/
theorem isExchangeable_annealedReplicaArrayLaw {U : Ω → EnergySpace N} (hU : Measurable U) :
    IsExchangeable (annealedReplicaArrayLaw N e U) :=
  isExchangeable_bind ((measurable_replicaArrayLaw N e).comp hU)
    fun ω => isExchangeable_replicaArrayLaw N (U ω) e

/-- The annealed replica-array law as a `ProbabilityMeasure`. -/
def annealedReplicaArray {U : Ω → EnergySpace N} (hU : Measurable U) :
    ProbabilityMeasure (ℕ → SpinSpace) :=
  ⟨annealedReplicaArrayLaw N e U, isProbabilityMeasure_annealedReplicaArrayLaw N e hU⟩

@[simp] lemma annealedReplicaArray_toMeasure {U : Ω → EnergySpace N} (hU : Measurable U) :
    (annealedReplicaArray N e hU : Measure (ℕ → SpinSpace)) = annealedReplicaArrayLaw N e U :=
  rfl

/-- **The asymptotic Gibbs measure of a random Hamiltonian exists.** For an arbitrary sequence of
*random* Hamiltonians `U N : Ω → EnergySpace N` and an arbitrary family of embeddings, some
subsequence of the disorder-averaged replica-array laws converges in distribution, and the limit is
the mixture `∫ λ^{⊗ℕ} m(dλ)` over a **unique** probability measure `m` on the probability measures
of the spin space.

Here `m` is the **law of the random asymptotic Gibbs measure**: de Finetti's mixing measure of the
annealed replica array is exactly the distribution of the limiting (random) Gibbs measure. This is
the object of Talagrand Vol. II, Ch. 12–15 and of Panchenko's book. Unconditional. -/
theorem exists_asymptoticGibbsMeasure_random
    (U : ∀ N : ℕ, Ω → EnergySpace N) (hU : ∀ N, Measurable (U N))
    (emb : ∀ N : ℕ, Config N → SpinSpace) :
    ∃ (μ : ProbabilityMeasure (ℕ → SpinSpace)) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun k => annealedReplicaArray (φ k) (emb (φ k)) (hU (φ k))) atTop (𝓝 μ) ∧
      ∃! m : Measure (Measure SpinSpace), IsProbabilityMeasure m
        ∧ m {lam : Measure SpinSpace | IsProbabilityMeasure lam}ᶜ = 0
        ∧ m.bind (fun lam => Measure.infinitePi fun _ : ℕ => lam)
            = (μ : Measure (ℕ → SpinSpace)) :=
  exists_subseq_tendsto_mixing (E := SpinSpace)
    (fun N => annealedReplicaArray N (emb N) (hU N))
    fun N => isExchangeable_annealedReplicaArrayLaw N (emb N) (hU N)

end Random

/-! ### The asymptotic Gibbs measure -/

/-- **The asymptotic Gibbs measure exists.** For an arbitrary sequence of Hamiltonians `H N` on
`Config N` and an arbitrary family of embeddings `e N` of the finite configuration spaces into the
spin space, some subsequence of the replica-array laws converges in distribution, and the limit is
the mixture `∫ λ^{⊗ℕ} m(dλ)` of i.i.d. product measures over a **unique** probability measure `m`
on the space of probability measures on the spin space.

`m` is Talagrand's / Panchenko's asymptotic Gibbs measure. No hypothesis is placed on the data:
compactness of the spin space provides the limit point, exchangeability of the i.i.d. replica array
survives the limit (`isExchangeable_of_tendsto`), and de Finetti (Georgii (7.31), Dynkin's version)
supplies the representation and its uniqueness. Talagrand Vol. II, Ch. 12. -/
theorem exists_asymptoticGibbsMeasure (H : ∀ N : ℕ, EnergySpace N)
    (e : ∀ N : ℕ, Config N → SpinSpace) :
    ∃ (μ : ProbabilityMeasure (ℕ → SpinSpace)) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun k => replicaArray (φ k) (H (φ k)) (e (φ k))) atTop (𝓝 μ) ∧
      ∃! m : Measure (Measure SpinSpace), IsProbabilityMeasure m
        ∧ m {lam : Measure SpinSpace | IsProbabilityMeasure lam}ᶜ = 0
        ∧ m.bind (fun lam => Measure.infinitePi fun _ : ℕ => lam)
            = (μ : Measure (ℕ → SpinSpace)) :=
  exists_subseq_tendsto_mixing (E := SpinSpace) (fun N => replicaArray N (H N) (e N))
    fun N => isExchangeable_replicaArrayLaw N (H N) (e N)

end

end SpinGlass
