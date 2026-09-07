/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Limit.Exchangeability
import SpinGlass.FiniteGibbs.GibbsMeasure
import SpinGlass.Defs

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
- `SpinGlass.exists_asymptoticGibbsMeasure`: **the asymptotic Gibbs measure exists**, for an
  arbitrary sequence of Hamiltonians and with no hypotheses whatsoever.
-/

open Filter Topology MeasureTheory MeasureTheory.GibbsMeasure

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
