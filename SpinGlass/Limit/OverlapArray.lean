/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Limit.ExchangeableArray
import SpinGlass.Split
import SpinGlass.FiniteGibbs.ReplicaMeasure

/-!
# The overlap array and its thermodynamic limit

The object all of Talagrand Vol. II Ch. 12–15 is about is the **overlap array**
`R_{l,l'} = R(σ^l, σ^{l'})` of a system of replicas drawn independently from the Gibbs measure.
Its law lives on `[-1,1]^{ℕ×ℕ}`, which is compact metrizable *independently of `N`*, so the
thermodynamic limit is taken there rather than on the configuration space.

Three facts make the limit usable, and all three are proved here:

* the array is **jointly exchangeable** — the replicas are i.i.d., hence exchangeable, and the
  array of their pairwise overlaps inherits invariance under the diagonal action
  (`MeasureTheory.GibbsMeasure.isJointlyExchangeable_map_of_isExchangeable`);
* the array is a **Gram array** — symmetric, unit diagonal, positive semidefinite — because
  `R(σ, τ) = (1/N)⟨σ, τ⟩` is an inner product;
* the Gram condition is **closed**, so it survives the weak limit, and joint exchangeability does
  too.

The conclusion, `SpinGlass.exists_asymptoticOverlapArray`, is exactly the hypothesis of the
Dovbysh–Sudakov theorem: a weakly exchangeable Gram array.

## Main statements

- `SpinGlass.abs_overlap_le_one`, `SpinGlass.overlapUnit`: the overlap valued in `[-1,1]`.
- `SpinGlass.overlapArrayLaw`, `SpinGlass.isJointlyExchangeable_overlapArrayLaw`.
- `SpinGlass.gramArray`, `SpinGlass.isClosed_gramArray`,
  `SpinGlass.pairArray_overlapUnit_mem_gramArray`.
- `SpinGlass.exists_asymptoticOverlapArray`: **the asymptotic overlap array exists**, is jointly
  exchangeable, and is almost surely a Gram array.
-/

open Filter Topology MeasureTheory MeasureTheory.GibbsMeasure
open scoped ProbabilityTheory

namespace SpinGlass

noncomputable section

/-! ### The overlap takes values in `[-1,1]` -/

/-- The compact interval `[-1,1]` in which overlaps take their values. -/
abbrev OverlapValue : Type := Set.Icc (-1 : ℝ) 1

/-- Registering `-1 ≤ 1` unlocks Mathlib's order-theoretic API for `Set.Icc (-1) 1`: it is a
bounded order, hence in particular nonempty — which is what makes it a legitimate target for a
regular conditional distribution (`ProbabilityTheory.condDistrib` requires `Nonempty`). -/
instance : Fact ((-1 : ℝ) ≤ 1) := ⟨by norm_num⟩

/-- The overlap, valued in `[-1,1]`. -/
def overlapUnit (N : ℕ) (σ τ : Config N) : OverlapValue :=
  ⟨overlap N σ τ, by
    have := abs_overlap_le_one N σ τ
    rw [abs_le] at this
    exact ⟨this.1, this.2⟩⟩

@[simp] lemma overlapUnit_coe (N : ℕ) (σ τ : Config N) :
    ((overlapUnit N σ τ : OverlapValue) : ℝ) = overlap N σ τ := rfl

/-! ### The replica array and its overlap array -/

variable (N : ℕ) (H : EnergySpace N)

/-- The law of the i.i.d. replica array on the configuration space of `N` sites. -/
def configReplicaArrayLaw : Measure (ℕ → Config N) :=
  Measure.infinitePi fun _ : ℕ => FiniteGibbs.gibbsMeasure (α := Config N) H

instance isProbabilityMeasure_configReplicaArrayLaw :
    IsProbabilityMeasure (configReplicaArrayLaw N H) := by
  rw [configReplicaArrayLaw]; infer_instance

theorem isExchangeable_configReplicaArrayLaw : IsExchangeable (configReplicaArrayLaw N H) :=
  isExchangeable_infinitePi

/-- **The overlap array law**: the law of `(R(σ^l, σ^{l'}))_{l,l'}` for replicas drawn
independently from the size-`N` Gibbs measure. -/
def overlapArrayLaw : Measure (ℕ → ℕ → OverlapValue) :=
  (configReplicaArrayLaw N H).map (pairArray (overlapUnit N))

instance isProbabilityMeasure_overlapArrayLaw :
    IsProbabilityMeasure (overlapArrayLaw N H) := by
  rw [overlapArrayLaw]
  exact Measure.isProbabilityMeasure_map
    (measurable_pairArray (Measurable.of_discrete)).aemeasurable

/-- **The overlap array is jointly exchangeable.** The replicas are i.i.d., hence exchangeable, and
the array of their pairwise overlaps inherits invariance under the diagonal action. -/
theorem isJointlyExchangeable_overlapArrayLaw :
    IsJointlyExchangeable (overlapArrayLaw N H) :=
  isJointlyExchangeable_map_of_isExchangeable (isExchangeable_configReplicaArrayLaw N H)
    (Measurable.of_discrete)

/-- The overlap array law as a `ProbabilityMeasure`. -/
def overlapArray : ProbabilityMeasure (ℕ → ℕ → OverlapValue) :=
  ⟨overlapArrayLaw N H, isProbabilityMeasure_overlapArrayLaw N H⟩

@[simp] lemma overlapArray_toMeasure :
    (overlapArray N H : Measure (ℕ → ℕ → OverlapValue)) = overlapArrayLaw N H := rfl

/-! ### Gram arrays -/

end

/-- The entry maps of an array are continuous. -/
lemma continuous_entry (l l' : ℕ) :
    Continuous fun R : ℕ → ℕ → OverlapValue => ((R l l' : OverlapValue) : ℝ) :=
  continuous_subtype_val.comp ((continuous_apply l').comp (continuous_apply l))

/-- The set of **Gram arrays**: symmetric, with unit diagonal, and positive semidefinite. These are
exactly the arrays of pairwise inner products of a family of unit vectors, and together with joint
exchangeability they are the hypothesis of the Dovbysh–Sudakov theorem. -/
def gramArray : Set (ℕ → ℕ → OverlapValue) :=
  ((⋂ l, ⋂ l', {R : ℕ → ℕ → OverlapValue | ((R l l' : OverlapValue) : ℝ) = ((R l' l : _) : ℝ)}) ∩
    ⋂ l, {R : ℕ → ℕ → OverlapValue | ((R l l : OverlapValue) : ℝ) = 1}) ∩
  ⋂ (s : Finset ℕ), ⋂ (c : ℕ → ℝ),
    {R : ℕ → ℕ → OverlapValue |
      0 ≤ ∑ l ∈ s, ∑ l' ∈ s, c l * c l' * ((R l l' : OverlapValue) : ℝ)}

/-- **The Gram condition is closed**, hence survives a weak limit. -/
theorem isClosed_gramArray : IsClosed gramArray := by
  refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
  · exact isClosed_iInter fun l => isClosed_iInter fun l' =>
      isClosed_eq (continuous_entry l l') (continuous_entry l' l)
  · exact isClosed_iInter fun l => isClosed_eq (continuous_entry l l) continuous_const
  · refine isClosed_iInter fun s => isClosed_iInter fun c => isClosed_le continuous_const ?_
    exact continuous_finsetSum _ fun l _ =>
      continuous_finsetSum _ fun l' _ => (continuous_entry l l').const_mul _

noncomputable section

variable (N : ℕ) (H : EnergySpace N)

/-- **The overlap array of any system of replicas is a Gram array.** Symmetry and unit diagonal are
`overlap_comm` and `overlap_self`; positive semidefiniteness is the identity
`∑_{l,l'} c_l c_{l'} R(σ^l, σ^{l'}) = (1/N) ∑_i (∑_l c_l σ^l_i)²`. -/
theorem pairArray_overlapUnit_mem_gramArray (hN : 0 < N) (σs : ℕ → Config N) :
    pairArray (overlapUnit N) σs ∈ gramArray := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact Set.mem_iInter.2 fun l => Set.mem_iInter.2 fun l' => overlap_comm N (σs l) (σs l')
  · exact Set.mem_iInter.2 fun l => overlap_self (N := N) hN (σs l)
  · refine Set.mem_iInter.2 fun s => Set.mem_iInter.2 fun c => ?_
    set a : ℕ → Fin N → ℝ := fun l i => c l * spin N (σs l) i with ha
    have hexp : ∀ i : Fin N, (∑ l ∈ s, a l i) ^ 2 = ∑ l ∈ s, ∑ l' ∈ s, a l i * a l' i :=
      fun i => by rw [sq, Finset.sum_mul_sum]
    have key : (1 / (N : ℝ)) * ∑ i : Fin N, (∑ l ∈ s, a l i) ^ 2
        = ∑ l ∈ s, ∑ l' ∈ s, c l * c l' * overlap N (σs l) (σs l') := by
      calc (1 / (N : ℝ)) * ∑ i : Fin N, (∑ l ∈ s, a l i) ^ 2
          = (1 / (N : ℝ)) * ∑ i : Fin N, ∑ l ∈ s, ∑ l' ∈ s, a l i * a l' i :=
            congrArg _ (Finset.sum_congr rfl fun i _ => hexp i)
        _ = (1 / (N : ℝ)) * ∑ l ∈ s, ∑ i : Fin N, ∑ l' ∈ s, a l i * a l' i := by
            rw [Finset.sum_comm]
        _ = (1 / (N : ℝ)) * ∑ l ∈ s, ∑ l' ∈ s, ∑ i : Fin N, a l i * a l' i :=
            congrArg _ (Finset.sum_congr rfl fun l _ => Finset.sum_comm)
        _ = ∑ l ∈ s, ∑ l' ∈ s, c l * c l' * overlap N (σs l) (σs l') := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun l' _ => ?_
            have hov : overlap N (σs l) (σs l')
                = (1 / (N : ℝ)) * ∑ i : Fin N, spin N (σs l) i * spin N (σs l') i := rfl
            have hterm : ∀ i : Fin N,
                a l i * a l' i = c l * c l' * (spin N (σs l) i * spin N (σs l') i) := fun i => by
              simp only [ha]; ring
            rw [hov, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hterm i,
              ← Finset.mul_sum]
            ring
    have hnn : (0 : ℝ) ≤ ∑ i : Fin N, (∑ l ∈ s, a l i) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    change (0 : ℝ) ≤ ∑ l ∈ s, ∑ l' ∈ s, c l * c l' * overlap N (σs l) (σs l')
    rw [← key]
    exact mul_nonneg (by positivity) hnn

/-- The finite-`N` overlap array law is carried by the Gram arrays. -/
theorem overlapArrayLaw_gramArray (hN : 0 < N) : overlapArrayLaw N H gramArray = 1 := by
  have hpre : (pairArray (overlapUnit N)) ⁻¹' gramArray = Set.univ :=
    Set.eq_univ_of_forall fun σs => pairArray_overlapUnit_mem_gramArray N hN σs
  rw [overlapArrayLaw, Measure.map_apply (measurable_pairArray Measurable.of_discrete)
    isClosed_gramArray.measurableSet, hpre, measure_univ]

end

/-! ### Random Hamiltonians -/

noncomputable section Random

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

lemma measurable_configReplicaArrayLaw (N : ℕ) :
    Measurable fun K : EnergySpace N => configReplicaArrayLaw N K :=
  Measure.measurable_infinitePi fun _ => FiniteGibbs.measurable_gibbsMeasure

lemma measurable_overlapArrayLaw (N : ℕ) :
    Measurable fun K : EnergySpace N => overlapArrayLaw N K :=
  (Measure.measurable_map _ (measurable_pairArray Measurable.of_discrete)).comp
    (measurable_configReplicaArrayLaw N)

/-- The **disorder-averaged overlap array law** of a random Hamiltonian. -/
def annealedOverlapArrayLaw (N : ℕ) (U : Ω → EnergySpace N) :
    Measure (ℕ → ℕ → OverlapValue) :=
  (ℙ : Measure Ω).bind fun ω => overlapArrayLaw N (U ω)

lemma isProbabilityMeasure_annealedOverlapArrayLaw (N : ℕ) {U : Ω → EnergySpace N}
    (hU : Measurable U) : IsProbabilityMeasure (annealedOverlapArrayLaw N U) :=
  isProbabilityMeasure_bind (((measurable_overlapArrayLaw N).comp hU).aemeasurable)
    (Filter.Eventually.of_forall fun _ => inferInstance)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The annealed overlap array is jointly exchangeable. -/
theorem isJointlyExchangeable_annealedOverlapArrayLaw (N : ℕ) {U : Ω → EnergySpace N}
    (hU : Measurable U) : IsJointlyExchangeable (annealedOverlapArrayLaw N U) :=
  isJointlyExchangeable_bind ((measurable_overlapArrayLaw N).comp hU)
    fun ω => isJointlyExchangeable_overlapArrayLaw N (U ω)

/-- The annealed overlap array is carried by the Gram arrays. -/
theorem annealedOverlapArrayLaw_gramArray (N : ℕ) (hN : 0 < N) {U : Ω → EnergySpace N}
    (hU : Measurable U) : annealedOverlapArrayLaw N U gramArray = 1 := by
  have hmeas : Measurable fun ω => overlapArrayLaw N (U ω) :=
    (measurable_overlapArrayLaw N).comp hU
  rw [annealedOverlapArrayLaw,
    Measure.bind_apply (f := fun ω => overlapArrayLaw N (U ω))
      isClosed_gramArray.measurableSet hmeas.aemeasurable]
  simp [overlapArrayLaw_gramArray _ _ hN]

/-- The annealed overlap array law as a `ProbabilityMeasure`. -/
def annealedOverlapArray (N : ℕ) {U : Ω → EnergySpace N} (hU : Measurable U) :
    ProbabilityMeasure (ℕ → ℕ → OverlapValue) :=
  ⟨annealedOverlapArrayLaw N U, isProbabilityMeasure_annealedOverlapArrayLaw N hU⟩

@[simp] lemma annealedOverlapArray_toMeasure (N : ℕ) {U : Ω → EnergySpace N}
    (hU : Measurable U) :
    (annealedOverlapArray N hU : Measure (ℕ → ℕ → OverlapValue))
      = annealedOverlapArrayLaw N U := rfl

/-- **The asymptotic overlap array of a random Hamiltonian exists**, is jointly exchangeable, and
is almost surely a Gram array. This is the hypothesis of the Dovbysh–Sudakov theorem for the
Sherrington–Kirkpatrick model and its relatives. Talagrand Vol. II, Ch. 12–15; Panchenko. -/
theorem exists_asymptoticOverlapArray_random (n : ℕ → ℕ) (hn : ∀ k, 0 < n k)
    (U : ∀ k : ℕ, Ω → EnergySpace (n k)) (hU : ∀ k, Measurable (U k)) :
    ∃ (μ : ProbabilityMeasure (ℕ → ℕ → OverlapValue)) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun k => annealedOverlapArray (n (φ k)) (hU (φ k))) atTop (𝓝 μ) ∧
      IsJointlyExchangeable (μ : Measure (ℕ → ℕ → OverlapValue)) ∧
      (μ : Measure (ℕ → ℕ → OverlapValue)) gramArray = 1 := by
  obtain ⟨μ, φ, hφ, hlim, hex⟩ :=
    exists_subseq_tendsto_jointlyExchangeable (fun k => annealedOverlapArray (n k) (hU k))
      fun k => isJointlyExchangeable_annealedOverlapArrayLaw (n k) (hU k)
  refine ⟨μ, φ, hφ, hlim, hex, ?_⟩
  exact ProbabilityMeasure.measure_eq_one_of_tendsto_of_isClosed hlim isClosed_gramArray
    (Filter.Eventually.of_forall fun k =>
      annealedOverlapArrayLaw_gramArray (n (φ k)) (hn _) (hU (φ k)))

end Random

/-! ### The asymptotic overlap array -/

noncomputable section

/-- **The asymptotic overlap array exists.** For an arbitrary sequence of positive system sizes and
Hamiltonians, some subsequence of the overlap array laws converges in distribution, and the limit
is **jointly exchangeable** and almost surely a **Gram array**: symmetric, unit diagonal, positive
semidefinite.

That is exactly the hypothesis of the Dovbysh–Sudakov theorem, which represents such an array as
the Gram array of an i.i.d. sample from a random measure on a Hilbert space — Talagrand Vol. II,
Ch. 12–15; Panchenko. Unconditional. -/
theorem exists_asymptoticOverlapArray (n : ℕ → ℕ) (hn : ∀ k, 0 < n k)
    (H : ∀ k : ℕ, EnergySpace (n k)) :
    ∃ (μ : ProbabilityMeasure (ℕ → ℕ → OverlapValue)) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun k => overlapArray (n (φ k)) (H (φ k))) atTop (𝓝 μ) ∧
      IsJointlyExchangeable (μ : Measure (ℕ → ℕ → OverlapValue)) ∧
      (μ : Measure (ℕ → ℕ → OverlapValue)) gramArray = 1 := by
  obtain ⟨μ, φ, hφ, hlim, hex⟩ :=
    exists_subseq_tendsto_jointlyExchangeable (fun k => overlapArray (n k) (H k))
      fun k => isJointlyExchangeable_overlapArrayLaw (n k) (H k)
  refine ⟨μ, φ, hφ, hlim, hex, ?_⟩
  exact ProbabilityMeasure.measure_eq_one_of_tendsto_of_isClosed hlim isClosed_gramArray
    (Filter.Eventually.of_forall fun k => overlapArrayLaw_gramArray (n (φ k)) (H (φ k)) (hn _))

end

end SpinGlass
