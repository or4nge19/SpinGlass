/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Limit.OverlapArray

/-!
# The limiting law of the overlaps: symmetry, ultrametricity, Ghirlanda–Guerra

Talagrand Vol. II, §15.3 fixes the three properties that the limiting law `μ*` of the overlap
array is expected to have, and around which the whole of Chapters 12–16 is organised:

* *symmetric* (Definition 15.3.1) — in the literature on random arrays, **weakly exchangeable**;
  this is `MeasureTheory.GibbsMeasure.IsJointlyExchangeable`, already proved for the limit laws
  produced by `SpinGlass.exists_asymptoticOverlapArray`;
* *ultrametric* (Definition 15.3.2), in the two equivalent forms (15.38) and (15.39);
* the *Ghirlanda–Guerra identities* (Definition 15.3.4).

Talagrand's Research Problem 15.3.7 — do the Ghirlanda–Guerra identities on `𝓒⁺` imply
ultrametricity? — was answered affirmatively by Panchenko (*The Parisi ultrametricity conjecture*,
Ann. of Math. **177** (2013), Theorem 1). This file supplies the ontology in which that statement
lives, together with everything that is structurally true about it:

* the two forms of ultrametricity agree (Talagrand asserts the equivalence);
* all pairwise overlaps of a weakly exchangeable array are equidistributed — the fact behind
  Talagrand's (15.41);
* ultrametricity and the Ghirlanda–Guerra identities are **closed conditions** in the topology of
  convergence in distribution, so they pass to weak limits exactly as symmetry and the Gram
  condition do;
* the Ghirlanda–Guerra identities are stable under an entrywise continuous change of variable
  (Talagrand, Exercise 15.3.5).

## Main statements

- `SpinGlass.oneOverlapLaw`, `SpinGlass.map_entry_eq_oneOverlapLaw`.
- `SpinGlass.IsUltrametric`, `SpinGlass.isUltrametric_iff_forall`,
  `SpinGlass.isClosed_ultrametricSet`, `SpinGlass.isUltrametric_of_tendsto`.
- `SpinGlass.SatisfiesGhirlandaGuerra`, `SpinGlass.isClosed_setOf_satisfiesGhirlandaGuerra`,
  `SpinGlass.satisfiesGhirlandaGuerra_of_tendsto`.
- `SpinGlass.satisfiesGhirlandaGuerra_map_entrywise` (Exercise 15.3.5).
-/

open Filter Topology MeasureTheory MeasureTheory.GibbsMeasure
open scoped ENNReal

namespace SpinGlass

noncomputable section

/-! ### Entries -/

/-- The `(l, l')` entry of an overlap array, as a real number. -/
def entry (R : ℕ → ℕ → OverlapValue) (l l' : ℕ) : ℝ := (R l l' : ℝ)

/-- The `(l, l')` entry as a bundled continuous map. -/
def entryCM (l l' : ℕ) : C(ℕ → ℕ → OverlapValue, ℝ) :=
  ⟨fun R => entry R l l', continuous_entry l l'⟩

@[simp] lemma entryCM_apply (l l' : ℕ) (R : ℕ → ℕ → OverlapValue) :
    entryCM l l' R = entry R l l' := rfl

/-! ### All pairwise overlaps are equidistributed -/

/-- A transposition of `ℕ` is a finitary permutation. -/
lemma swap_mem_finitaryPerm (a b : ℕ) : Equiv.swap a b ∈ finitaryPerm :=
  finPerm_le_finitaryPerm (max a b + 1)
    (swap_mem_finPerm (Nat.lt_succ_of_le (le_max_left a b))
      (Nat.lt_succ_of_le (le_max_right a b)))

/-- For distinct `l, l'` there is a finitary permutation carrying `0` to `l` and `1` to `l'`. -/
theorem exists_finitaryPerm_zero_one {l l' : ℕ} (h : l ≠ l') :
    ∃ σ ∈ finitaryPerm, σ 0 = l ∧ σ 1 = l' := by
  classical
  set π : Equiv.Perm ℕ := Equiv.swap 0 l with hπ
  have hπ0 : π 0 = l := Equiv.swap_apply_left 0 l
  have hπl : π l = 0 := Equiv.swap_apply_right 0 l
  set m : ℕ := π l' with hm
  have hm0 : m ≠ 0 := by
    intro hcon
    have hml : π l' = π l := by rw [← hm, hπl]; exact hcon
    exact h (π.injective hml).symm
  refine ⟨π * Equiv.swap 1 m, Subgroup.mul_mem _ (swap_mem_finitaryPerm 0 l)
    (swap_mem_finitaryPerm 1 m), ?_, ?_⟩
  · have h0 : Equiv.swap (1 : ℕ) m 0 = 0 :=
      Equiv.swap_apply_of_ne_of_ne (by omega) (Ne.symm hm0)
    rw [Equiv.Perm.mul_apply, h0, hπ0]
  · have h1 : Equiv.swap (1 : ℕ) m 1 = m := Equiv.swap_apply_left 1 m
    rw [Equiv.Perm.mul_apply, h1, hm, hπ]
    exact Equiv.swap_apply_self 0 l l'

/-- The law of a single overlap `R_{0,1}` — Talagrand's `μ` of (15.41). -/
def oneOverlapLaw (μ : Measure (ℕ → ℕ → OverlapValue)) : Measure OverlapValue :=
  μ.map fun R => R 0 1

/-- **All pairwise overlaps of a weakly exchangeable array are equidistributed.** This is the fact
behind Talagrand's (15.41): the "limiting law of the overlap" is well defined. -/
theorem map_entry_eq_oneOverlapLaw {μ : Measure (ℕ → ℕ → OverlapValue)}
    (hμ : IsJointlyExchangeable μ) {l l' : ℕ} (h : l ≠ l') :
    (μ.map fun R => R l l') = oneOverlapLaw μ := by
  obtain ⟨σ, hσ, hσ0, hσ1⟩ := exists_finitaryPerm_zero_one h
  have hm : Measurable fun R : ℕ → ℕ → OverlapValue => R 0 1 :=
    (measurable_pi_apply 1).comp (measurable_pi_apply 0)
  calc (μ.map fun R => R l l') = ((μ.map (permuteArray σ)).map fun R => R 0 1) := by
        rw [Measure.map_map hm (measurable_permuteArray σ)]
        congr 1
        funext R
        simp only [Function.comp_def, permuteArray, hσ0, hσ1]
    _ = oneOverlapLaw μ := by rw [hμ σ hσ]; rfl

/-! ### Ultrametricity (Talagrand Vol. II, Definition 15.3.2) -/

/-- The ultrametric set `{R_{0,1} ≥ min(R_{0,2}, R_{1,2})}`; Panchenko (1.3). -/
def ultrametricSet : Set (ℕ → ℕ → OverlapValue) :=
  {R | min (entry R 0 2) (entry R 1 2) ≤ entry R 0 1}

lemma isClosed_ultrametricSet : IsClosed ultrametricSet :=
  isClosed_le ((continuous_entry 0 2).min (continuous_entry 1 2)) (continuous_entry 0 1)

/-- **Ultrametricity**, Talagrand Vol. II, Definition 15.3.2, form (15.38); Panchenko (1.3). -/
def IsUltrametric (μ : Measure (ℕ → ℕ → OverlapValue)) : Prop := μ ultrametricSet = 1

/-- The equivalent form (15.39) of Definition 15.3.2. -/
theorem isUltrametric_iff_forall (μ : Measure (ℕ → ℕ → OverlapValue))
    [IsProbabilityMeasure μ] :
    IsUltrametric μ ↔
      ∀ a : ℝ, μ {R | a ≤ entry R 0 2 ∧ a ≤ entry R 1 2 ∧ entry R 0 1 < a} = 0 := by
  classical
  have hmeas : ∀ a : ℝ,
      MeasurableSet {R : ℕ → ℕ → OverlapValue |
        a ≤ entry R 0 2 ∧ a ≤ entry R 1 2 ∧ entry R 0 1 < a} := by
    intro a
    exact ((measurableSet_le measurable_const (continuous_entry 0 2).measurable).inter
      (((measurableSet_le measurable_const (continuous_entry 1 2).measurable)).inter
        (measurableSet_lt (continuous_entry 0 1).measurable measurable_const)))
  have hsub : ∀ a : ℝ,
      {R : ℕ → ℕ → OverlapValue | a ≤ entry R 0 2 ∧ a ≤ entry R 1 2 ∧ entry R 0 1 < a}
        ⊆ ultrametricSetᶜ := by
    intro a R hR
    simp only [ultrametricSet, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
    exact lt_of_lt_of_le hR.2.2 (le_min hR.1 hR.2.1)
  constructor
  · intro hU a
    have hnull : μ ultrametricSetᶜ = 0 := by
      rw [measure_compl isClosed_ultrametricSet.measurableSet (measure_ne_top _ _), hU,
        measure_univ, tsub_self]
    exact measure_mono_null (hsub a) hnull
  · intro h
    have hcover : ultrametricSetᶜ
        ⊆ ⋃ q : ℚ, {R : ℕ → ℕ → OverlapValue |
            (q : ℝ) ≤ entry R 0 2 ∧ (q : ℝ) ≤ entry R 1 2 ∧ entry R 0 1 < (q : ℝ)} := by
      intro R hR
      simp only [ultrametricSet, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hR
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hR
      exact Set.mem_iUnion.2 ⟨q, le_of_lt (lt_of_lt_of_le hq2 (min_le_left _ _)),
        le_of_lt (lt_of_lt_of_le hq2 (min_le_right _ _)), hq1⟩
    have hnull : μ ultrametricSetᶜ = 0 :=
      measure_mono_null hcover (measure_iUnion_null fun q => h (q : ℝ))
    have hc := measure_compl isClosed_ultrametricSet.measurableSet (measure_ne_top μ _)
    rw [hnull, measure_univ] at hc
    have h1 : μ ultrametricSet ≤ 1 := prob_le_one
    have h2 : (1 : ℝ≥0∞) ≤ μ ultrametricSet := by
      rw [← tsub_eq_zero_iff_le]
      exact hc.symm
    exact le_antisymm h1 h2

/-- **Ultrametricity passes to weak limits**, since the ultrametric set is closed. -/
theorem isUltrametric_of_tendsto {ι : Type*} {L : Filter ι} [L.NeBot]
    {μs : ι → ProbabilityMeasure (ℕ → ℕ → OverlapValue)}
    {μ : ProbabilityMeasure (ℕ → ℕ → OverlapValue)} (hlim : Tendsto μs L (𝓝 μ))
    (hU : ∀ᶠ i in L, IsUltrametric (μs i : Measure (ℕ → ℕ → OverlapValue))) :
    IsUltrametric (μ : Measure (ℕ → ℕ → OverlapValue)) :=
  ProbabilityMeasure.measure_eq_one_of_tendsto_of_isClosed hlim isClosed_ultrametricSet hU

/-! ### The Ghirlanda–Guerra identities (Talagrand Vol. II, Definition 15.3.4) -/

/-- Evaluation of an entry, as a bundled continuous map into `[-1,1]`. -/
def evalCM (l l' : ℕ) : C(ℕ → ℕ → OverlapValue, OverlapValue) :=
  ⟨fun R => R l l', (continuous_apply l').comp (continuous_apply l)⟩

@[simp] lemma evalCM_apply (l l' : ℕ) (R : ℕ → ℕ → OverlapValue) : evalCM l l' R = R l l' := rfl

/-- `f` depends only on the entries `x_{l,l'}` with `l, l' < n` — Talagrand's restriction on the
test function in Definition 15.3.4. -/
def DependsOnFirst (n : ℕ) (f : (ℕ → ℕ → OverlapValue) → ℝ) : Prop :=
  ∀ R R' : ℕ → ℕ → OverlapValue, (∀ l < n, ∀ l' < n, R l l' = R' l l') → f R = f R'

/-- **The Ghirlanda–Guerra identities**, Talagrand Vol. II, Definition 15.3.4, equation (15.40),
in `0`-based replica indices: the replicas are `0, …, n-1` and the new replica is `n`. Panchenko
(*The Parisi ultrametricity conjecture*, Ann. of Math. **177** (2013)) writes the same identities
as (1.1); the test functions are taken continuous, as in Talagrand's definition, and range over
`[-1,1]` because that is where the overlaps live. -/
def SatisfiesGhirlandaGuerra (μ : Measure (ℕ → ℕ → OverlapValue)) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ f : C(ℕ → ℕ → OverlapValue, ℝ), DependsOnFirst n f →
    ∀ φ : C(OverlapValue, ℝ),
      (∫ R, φ (R 0 n) * f R ∂μ)
        = (1 / (n : ℝ)) * ((∫ R, φ (R 0 n) ∂μ) * ∫ R, f R ∂μ)
          + (1 / (n : ℝ)) * ∑ l ∈ Finset.Ico 1 n, ∫ R, φ (R 0 l) * f R ∂μ

/-- **The Ghirlanda–Guerra identities pass to weak limits.** Every term of (15.40) is the integral
of a fixed continuous function against the measure, hence a continuous function of the measure in
the topology of convergence in distribution; the identity is therefore a closed condition. -/
theorem satisfiesGhirlandaGuerra_of_tendsto {ι : Type*} {L : Filter ι} [L.NeBot]
    {μs : ι → ProbabilityMeasure (ℕ → ℕ → OverlapValue)}
    {μ : ProbabilityMeasure (ℕ → ℕ → OverlapValue)} (hlim : Tendsto μs L (𝓝 μ))
    (hgg : ∀ᶠ i in L, SatisfiesGhirlandaGuerra (μs i : Measure (ℕ → ℕ → OverlapValue))) :
    SatisfiesGhirlandaGuerra (μ : Measure (ℕ → ℕ → OverlapValue)) := by
  intro n hn f hf φ
  have hcontL : Continuous fun ν : ProbabilityMeasure (ℕ → ℕ → OverlapValue) =>
      ∫ R, φ (R 0 n) * f R ∂(ν : Measure (ℕ → ℕ → OverlapValue)) :=
    ProbabilityMeasure.continuous_integral_continuousMap ((φ.comp (evalCM 0 n)) * f)
  have hcontG : Continuous fun ν : ProbabilityMeasure (ℕ → ℕ → OverlapValue) =>
      (1 / (n : ℝ)) * ((∫ R, φ (R 0 n) ∂(ν : Measure (ℕ → ℕ → OverlapValue)))
          * ∫ R, f R ∂(ν : Measure (ℕ → ℕ → OverlapValue)))
        + (1 / (n : ℝ)) * ∑ l ∈ Finset.Ico 1 n,
            ∫ R, φ (R 0 l) * f R ∂(ν : Measure (ℕ → ℕ → OverlapValue)) := by
    refine Continuous.add (continuous_const.mul (Continuous.mul ?_ ?_))
      (continuous_const.mul (continuous_finsetSum _ fun l _ => ?_))
    · exact ProbabilityMeasure.continuous_integral_continuousMap (φ.comp (evalCM 0 n))
    · exact ProbabilityMeasure.continuous_integral_continuousMap f
    · exact ProbabilityMeasure.continuous_integral_continuousMap ((φ.comp (evalCM 0 l)) * f)
  refine tendsto_nhds_unique (((hcontL.tendsto μ).comp hlim).congr' ?_)
    ((hcontG.tendsto μ).comp hlim)
  filter_upwards [hgg] with i hi
  exact hi n hn f hf φ

/-! ### Entrywise change of variable (Talagrand Vol. II, Exercise 15.3.5) -/

/-- Applying a continuous map to every entry of an array. -/
def mapEntrywise (ψ : C(OverlapValue, OverlapValue)) :
    C(ℕ → ℕ → OverlapValue, ℕ → ℕ → OverlapValue) :=
  ⟨fun R l l' => ψ (R l l'),
    continuous_pi fun l => continuous_pi fun l' =>
      ψ.continuous.comp ((continuous_apply l').comp (continuous_apply l))⟩

@[simp] lemma mapEntrywise_apply (ψ : C(OverlapValue, OverlapValue))
    (R : ℕ → ℕ → OverlapValue) (l l' : ℕ) : mapEntrywise ψ R l l' = ψ (R l l') := rfl

/-- **Talagrand Vol. II, Exercise 15.3.5**: the image of a measure satisfying the Ghirlanda–Guerra
identities under an entrywise continuous change of variable satisfies them too. -/
theorem satisfiesGhirlandaGuerra_map {μ : Measure (ℕ → ℕ → OverlapValue)}
    (hμ : SatisfiesGhirlandaGuerra μ) (ψ : C(OverlapValue, OverlapValue)) :
    SatisfiesGhirlandaGuerra (μ.map (mapEntrywise ψ)) := by
  intro n hn f hf φ
  have hΨ : Measurable (mapEntrywise ψ) := (mapEntrywise ψ).continuous.measurable
  have hf' : DependsOnFirst n (f.comp (mapEntrywise ψ)) := by
    intro R R' hRR'
    exact hf _ _ fun l hl l' hl' => by simp [hRR' l hl l' hl']
  have hpush : ∀ g : C(ℕ → ℕ → OverlapValue, ℝ),
      (∫ R, g R ∂(μ.map (mapEntrywise ψ))) = ∫ R, g (mapEntrywise ψ R) ∂μ := fun g =>
    MeasureTheory.integral_map hΨ.aemeasurable g.continuous.aestronglyMeasurable
  have e1 : (∫ R, φ (R 0 n) * f R ∂(μ.map (mapEntrywise ψ)))
      = ∫ R, φ ((mapEntrywise ψ R) 0 n) * f (mapEntrywise ψ R) ∂μ :=
    hpush ((φ.comp (evalCM 0 n)) * f)
  have e2 : (∫ R, φ (R 0 n) ∂(μ.map (mapEntrywise ψ)))
      = ∫ R, φ ((mapEntrywise ψ R) 0 n) ∂μ := hpush (φ.comp (evalCM 0 n))
  have e3 : (∫ R, f R ∂(μ.map (mapEntrywise ψ))) = ∫ R, f (mapEntrywise ψ R) ∂μ := hpush f
  have e4 : ∀ l ∈ Finset.Ico 1 n, (∫ R, φ (R 0 l) * f R ∂(μ.map (mapEntrywise ψ)))
      = ∫ R, φ ((mapEntrywise ψ R) 0 l) * f (mapEntrywise ψ R) ∂μ :=
    fun l _ => hpush ((φ.comp (evalCM 0 l)) * f)
  rw [e1, e2, e3, Finset.sum_congr rfl e4]
  exact hμ n hn (f.comp (mapEntrywise ψ)) hf' (φ.comp ψ)

/-! ### `DependsOnFirst` is factorisation through the finite overlap block

Talagrand's restriction on the test function — that it depend only on `x_{l,l'}` for `l, l' ≤ n` —
says exactly that it factors through the `n × n` block of the array. Making that precise turns the
predicate from an ad hoc side condition into a usable one: *every* continuous function of the
finite overlap matrix is an admissible test function, and the admissible ones form an algebra. -/

/-- Restriction of an array to its first `n × n` block. -/
def blockRestrict (n : ℕ) : C(ℕ → ℕ → OverlapValue, Fin n → Fin n → OverlapValue) :=
  ⟨fun R l l' => R l l',
    continuous_pi fun l => continuous_pi fun l' =>
      (continuous_apply (l' : ℕ)).comp (continuous_apply (l : ℕ))⟩

@[simp] lemma blockRestrict_apply (n : ℕ) (R : ℕ → ℕ → OverlapValue) (l l' : Fin n) :
    blockRestrict n R l l' = R l l' := rfl

/-- Extension of an `n × n` block to a full array, constant outside the block. -/
def blockExtend (n : ℕ) (d : OverlapValue) :
    C(Fin n → Fin n → OverlapValue, ℕ → ℕ → OverlapValue) :=
  ⟨fun x l l' => if h : l < n ∧ l' < n then x ⟨l, h.1⟩ ⟨l', h.2⟩ else d, by
    refine continuous_pi fun l => continuous_pi fun l' => ?_
    by_cases h : l < n ∧ l' < n
    · have hfun : (fun x : Fin n → Fin n → OverlapValue =>
          if h' : l < n ∧ l' < n then x ⟨l, h'.1⟩ ⟨l', h'.2⟩ else d)
          = fun x => x ⟨l, h.1⟩ ⟨l', h.2⟩ := by
        funext x; simp [h]
      rw [hfun]
      exact (continuous_apply _).comp (continuous_apply _)
    · have hfun : (fun x : Fin n → Fin n → OverlapValue =>
          if h' : l < n ∧ l' < n then x ⟨l, h'.1⟩ ⟨l', h'.2⟩ else d)
          = fun _ => d := by
        funext x; simp [h]
      rw [hfun]
      exact continuous_const⟩

lemma blockExtend_apply_of_lt (n : ℕ) (d : OverlapValue)
    (x : Fin n → Fin n → OverlapValue) {l l' : ℕ} (hl : l < n) (hl' : l' < n) :
    blockExtend n d x l l' = x ⟨l, hl⟩ ⟨l', hl'⟩ := by
  simp [blockExtend, hl, hl']

/-- **`DependsOnFirst n f` means `f` factors through the `n × n` overlap block.** -/
theorem dependsOnFirst_iff_exists (n : ℕ) (f : C(ℕ → ℕ → OverlapValue, ℝ)) :
    DependsOnFirst n f ↔
      ∃ g : C(Fin n → Fin n → OverlapValue, ℝ), ∀ R, f R = g (blockRestrict n R) := by
  constructor
  · intro hf
    refine ⟨f.comp (blockExtend n ⟨0, by norm_num⟩), fun R => ?_⟩
    exact hf R _ fun l hl l' hl' =>
      (blockExtend_apply_of_lt n _ (blockRestrict n R) hl hl').symm
  · rintro ⟨g, hg⟩ R R' hRR'
    rw [hg, hg]
    congr 1
    funext l l'
    exact hRR' l l.2 l' l'.2

/-- Every continuous function of the `n × n` overlap block is an admissible test function. -/
theorem dependsOnFirst_comp_blockRestrict (n : ℕ)
    (g : C(Fin n → Fin n → OverlapValue, ℝ)) :
    DependsOnFirst n (g.comp (blockRestrict n)) :=
  (dependsOnFirst_iff_exists n (g.comp (blockRestrict n))).2 ⟨g, fun _ => rfl⟩

lemma dependsOnFirst_const (n : ℕ) (c : ℝ) :
    DependsOnFirst n (fun _ : ℕ → ℕ → OverlapValue => c) := fun _ _ _ => rfl

lemma dependsOnFirst_entry (n : ℕ) {l l' : ℕ} (hl : l < n) (hl' : l' < n)
    (φ : C(OverlapValue, ℝ)) :
    DependsOnFirst n fun R : ℕ → ℕ → OverlapValue => φ (R l l') := by
  intro R R' h
  simp only []
  rw [h l hl l' hl']

lemma DependsOnFirst.add {n : ℕ} {f g : (ℕ → ℕ → OverlapValue) → ℝ}
    (hf : DependsOnFirst n f) (hg : DependsOnFirst n g) : DependsOnFirst n (f + g) :=
  fun R R' h => by simp [Pi.add_apply, hf R R' h, hg R R' h]

lemma DependsOnFirst.mul {n : ℕ} {f g : (ℕ → ℕ → OverlapValue) → ℝ}
    (hf : DependsOnFirst n f) (hg : DependsOnFirst n g) : DependsOnFirst n (f * g) :=
  fun R R' h => by simp [Pi.mul_apply, hf R R' h, hg R R' h]

lemma DependsOnFirst.smul {n : ℕ} {f : (ℕ → ℕ → OverlapValue) → ℝ} (c : ℝ)
    (hf : DependsOnFirst n f) : DependsOnFirst n (c • f) :=
  fun R R' h => by simp [Pi.smul_apply, hf R R' h]

lemma DependsOnFirst.mono {m n : ℕ} (hmn : m ≤ n) {f : (ℕ → ℕ → OverlapValue) → ℝ}
    (hf : DependsOnFirst m f) : DependsOnFirst n f :=
  fun R R' h => hf R R' fun l hl l' hl' => h l (hl.trans_le hmn) l' (hl'.trans_le hmn)

/-! ### Reduction to a dense set of test functions

The identities (15.40) are **linear in the test function `φ`** and each term is bounded by
`‖φ‖ ‖f‖`, so for fixed `n` and `f` the set of `φ` satisfying them is closed. It therefore suffices
to verify them for `φ` ranging over a dense subset of `C([-1,1], ℝ)` — for instance the polynomials
(Stone–Weierstrass). This is what lets a family of models whose covariance profiles span the
polynomials produce the identities for every continuous `φ`. -/

lemma integrable_continuousMap {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (g : C(X, ℝ)) : Integrable (fun x => g x) μ :=
  Integrable.of_bound g.continuous.aestronglyMeasurable ‖g‖
    (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using g.norm_coe_le_norm x)

/-- A continuous real function on a compact space is integrable against any finite measure: it is
bounded. The unbundled form of `SpinGlass.integrable_continuousMap`. -/
lemma integrable_of_continuous {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Continuous f) : Integrable f μ :=
  integrable_continuousMap (μ := μ) ⟨f, hf⟩

/-- For a fixed weight `g`, the linear functional `φ ↦ ∫ φ(R_{l,l'}) g(R) dμ` is Lipschitz in the
uniform norm, with constant `‖g‖`. -/
lemma lipschitzWith_integral_comp_mul (μ : Measure (ℕ → ℕ → OverlapValue))
    [IsProbabilityMeasure μ] (g : C(ℕ → ℕ → OverlapValue, ℝ)) (l l' : ℕ) :
    LipschitzWith ‖g‖₊ fun φ : C(OverlapValue, ℝ) => ∫ R, φ (R l l') * g R ∂μ := by
  refine LipschitzWith.of_dist_le_mul fun φ₁ φ₂ => ?_
  have hi : ∀ φ : C(OverlapValue, ℝ),
      Integrable (fun R => φ (R l l') * g R) μ := fun φ =>
    integrable_continuousMap (μ := μ) ((φ.comp (evalCM l l')) * g)
  have hsub : (∫ R, φ₁ (R l l') * g R ∂μ) - ∫ R, φ₂ (R l l') * g R ∂μ
      = ∫ R, (φ₁ (R l l') - φ₂ (R l l')) * g R ∂μ := by
    rw [← MeasureTheory.integral_sub (hi φ₁) (hi φ₂)]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun R => by ring)
  have hbd : ∀ R : ℕ → ℕ → OverlapValue,
      ‖(φ₁ (R l l') - φ₂ (R l l')) * g R‖ ≤ dist φ₁ φ₂ * ‖g‖ := by
    intro R
    rw [norm_mul]
    refine mul_le_mul ?_ (g.norm_coe_le_norm R) (norm_nonneg _) dist_nonneg
    have : ‖φ₁ (R l l') - φ₂ (R l l')‖ ≤ ‖φ₁ - φ₂‖ := by
      simpa using (φ₁ - φ₂).norm_coe_le_norm (R l l')
    simpa [dist_eq_norm] using this
  calc dist (∫ R, φ₁ (R l l') * g R ∂μ) (∫ R, φ₂ (R l l') * g R ∂μ)
      = ‖∫ R, (φ₁ (R l l') - φ₂ (R l l')) * g R ∂μ‖ := by rw [dist_eq_norm, hsub]
    _ ≤ dist φ₁ φ₂ * ‖g‖ := by
        have := MeasureTheory.norm_integral_le_of_norm_le_const (μ := μ)
          (C := dist φ₁ φ₂ * ‖g‖) (Filter.Eventually.of_forall hbd)
        simpa using this
    _ = ↑‖g‖₊ * dist φ₁ φ₂ := by rw [coe_nnnorm]; ring

/-- The functional `φ ↦ ∫ φ(R_{l,l'}) g(R) dμ` is additive. -/
lemma integral_comp_mul_add (μ : Measure (ℕ → ℕ → OverlapValue)) [IsProbabilityMeasure μ]
    (g : C(ℕ → ℕ → OverlapValue, ℝ)) (l l' : ℕ) (φ₁ φ₂ : C(OverlapValue, ℝ)) :
    (∫ R, (φ₁ + φ₂) (R l l') * g R ∂μ)
      = (∫ R, φ₁ (R l l') * g R ∂μ) + ∫ R, φ₂ (R l l') * g R ∂μ := by
  have hi : ∀ φ : C(OverlapValue, ℝ), Integrable (fun R => φ (R l l') * g R) μ := fun φ =>
    integrable_continuousMap (μ := μ) ((φ.comp (evalCM l l')) * g)
  rw [← MeasureTheory.integral_add (hi φ₁) (hi φ₂)]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun R => by
    simp [ContinuousMap.add_apply]; ring)

/-- The functional `φ ↦ ∫ φ(R_{l,l'}) g(R) dμ` is homogeneous. -/
lemma integral_comp_mul_smul (μ : Measure (ℕ → ℕ → OverlapValue)) [IsProbabilityMeasure μ]
    (g : C(ℕ → ℕ → OverlapValue, ℝ)) (l l' : ℕ) (c : ℝ) (φ : C(OverlapValue, ℝ)) :
    (∫ R, (c • φ) (R l l') * g R ∂μ) = c * ∫ R, φ (R l l') * g R ∂μ := by
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun R => by
    simp [ContinuousMap.smul_apply]; ring)

/-- **The Ghirlanda–Guerra identities need only be checked on a set whose *span* is dense.** For
fixed `n` and `f` the identity is a *linear* condition on the test function `φ` and a closed one, so
it propagates from `S` to `span S` and then to its closure. The span is what matters: the monomials
`x ↦ xᵖ` are not dense in `C([-1,1], ℝ)`, but they span a dense subspace, and monomials are exactly
what a family of models produces. -/
theorem satisfiesGhirlandaGuerra_of_denseSpan {μ : Measure (ℕ → ℕ → OverlapValue)}
    [IsProbabilityMeasure μ] {S : Set C(OverlapValue, ℝ)}
    (hS : Dense ((Submodule.span ℝ S : Submodule ℝ C(OverlapValue, ℝ)) :
      Set C(OverlapValue, ℝ)))
    (h : ∀ (n : ℕ), 0 < n → ∀ f : C(ℕ → ℕ → OverlapValue, ℝ), DependsOnFirst n f →
      ∀ φ ∈ S,
        (∫ R, φ (R 0 n) * f R ∂μ)
          = (1 / (n : ℝ)) * ((∫ R, φ (R 0 n) ∂μ) * ∫ R, f R ∂μ)
            + (1 / (n : ℝ)) * ∑ l ∈ Finset.Ico 1 n, ∫ R, φ (R 0 l) * f R ∂μ) :
    SatisfiesGhirlandaGuerra μ := by
  intro n hn f hf
  set A : C(OverlapValue, ℝ) → ℝ := fun φ => ∫ R, φ (R 0 n) * f R ∂μ with hA
  set B : C(OverlapValue, ℝ) → ℝ := fun φ =>
    (1 / (n : ℝ)) * ((∫ R, φ (R 0 n) ∂μ) * ∫ R, f R ∂μ)
      + (1 / (n : ℝ)) * ∑ l ∈ Finset.Ico 1 n, ∫ R, φ (R 0 l) * f R ∂μ with hB
  have hone : ∀ φ : C(OverlapValue, ℝ), (∫ R, φ (R 0 n) ∂μ)
      = ∫ R, φ (R 0 n) * (1 : C(ℕ → ℕ → OverlapValue, ℝ)) R ∂μ := by
    intro φ; simp
  have hcA : Continuous A := (lipschitzWith_integral_comp_mul μ f 0 n).continuous
  have hcB : Continuous B := by
    refine Continuous.add (continuous_const.mul (Continuous.mul ?_ continuous_const))
      (continuous_const.mul (continuous_finsetSum _ fun l _ => ?_))
    · refine ((lipschitzWith_integral_comp_mul μ
        (1 : C(ℕ → ℕ → OverlapValue, ℝ)) 0 n).continuous).congr fun φ => ?_
      simp
    · exact (lipschitzWith_integral_comp_mul μ f 0 l).continuous
  -- the identity is linear in `φ`
  have hAadd : ∀ φ₁ φ₂, A (φ₁ + φ₂) = A φ₁ + A φ₂ := fun φ₁ φ₂ =>
    integral_comp_mul_add μ f 0 n φ₁ φ₂
  have hAsmul : ∀ (c : ℝ) φ, A (c • φ) = c * A φ := fun c φ =>
    integral_comp_mul_smul μ f 0 n c φ
  have hBadd : ∀ φ₁ φ₂, B (φ₁ + φ₂) = B φ₁ + B φ₂ := by
    intro φ₁ φ₂
    simp only [hB, hone]
    rw [integral_comp_mul_add μ 1 0 n φ₁ φ₂,
      Finset.sum_congr rfl fun l _ => integral_comp_mul_add μ f 0 l φ₁ φ₂,
      Finset.sum_add_distrib]
    ring
  have hBsmul : ∀ (c : ℝ) φ, B (c • φ) = c * B φ := by
    intro c φ
    simp only [hB, hone]
    rw [integral_comp_mul_smul μ 1 0 n c φ,
      Finset.sum_congr rfl fun l _ => integral_comp_mul_smul μ f 0 l c φ,
      ← Finset.mul_sum]
    ring
  have hspan : ((Submodule.span ℝ S : Submodule ℝ C(OverlapValue, ℝ)) :
      Set C(OverlapValue, ℝ)) ⊆ {φ | A φ = B φ} := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => exact h n hn f hf x hx
    | zero =>
        have hA0 : A 0 = 0 := by simp [hA]
        have hB0 : B 0 = 0 := by simp [hB]
        simp [hA0, hB0]
    | add x y _ _ ihx ihy => simp only [Set.mem_ofPred_eq] at *; rw [hAadd, hBadd, ihx, ihy]
    | smul c x _ ih => simp only [Set.mem_ofPred_eq] at *; rw [hAsmul, hBsmul, ih]
  have hall : (Set.univ : Set C(OverlapValue, ℝ)) ⊆ {φ | A φ = B φ} := by
    rw [← hS.closure_eq]
    exact (isClosed_eq hcA hcB).closure_subset_iff.2 hspan
  exact fun φ => hall (Set.mem_univ φ)

/-- **The Ghirlanda–Guerra identities need only be checked on a dense set of test functions.** -/
theorem satisfiesGhirlandaGuerra_of_dense {μ : Measure (ℕ → ℕ → OverlapValue)}
    [IsProbabilityMeasure μ] {S : Set C(OverlapValue, ℝ)} (hS : Dense S)
    (h : ∀ (n : ℕ), 0 < n → ∀ f : C(ℕ → ℕ → OverlapValue, ℝ), DependsOnFirst n f →
      ∀ φ ∈ S,
        (∫ R, φ (R 0 n) * f R ∂μ)
          = (1 / (n : ℝ)) * ((∫ R, φ (R 0 n) ∂μ) * ∫ R, f R ∂μ)
            + (1 / (n : ℝ)) * ∑ l ∈ Finset.Ico 1 n, ∫ R, φ (R 0 l) * f R ∂μ) :
    SatisfiesGhirlandaGuerra μ :=
  satisfiesGhirlandaGuerra_of_denseSpan (hS.mono Submodule.subset_span) h

/-! ### Polynomial and monomial test functions -/

lemma dense_polynomialFunctions :
    Dense ((polynomialFunctions (Set.Icc (-1 : ℝ) 1) :
      Subalgebra ℝ C(Set.Icc (-1 : ℝ) 1, ℝ)) : Set C(Set.Icc (-1 : ℝ) 1, ℝ)) := by
  rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe,
    polynomialFunctions_closure_eq_top (-1 : ℝ) 1]
  rfl

/-- The polynomial functions on `[-1,1]` lie in the span of the monomials. -/
lemma polynomialFunctions_subset_span_monomials :
    ((polynomialFunctions (Set.Icc (-1 : ℝ) 1) :
        Subalgebra ℝ C(Set.Icc (-1 : ℝ) 1, ℝ)) : Set C(Set.Icc (-1 : ℝ) 1, ℝ))
      ⊆ ((Submodule.span ℝ (Set.range fun p : ℕ =>
          ((Polynomial.X : Polynomial ℝ) ^ p).toContinuousMapOn (Set.Icc (-1 : ℝ) 1)) :
        Submodule ℝ C(Set.Icc (-1 : ℝ) 1, ℝ)) : Set C(Set.Icc (-1 : ℝ) 1, ℝ)) := by
  rw [polynomialFunctions_coe]
  rintro _ ⟨p, rfl⟩
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have : (Polynomial.toContinuousMapOnAlgHom (Set.Icc (-1 : ℝ) 1)) (p + q)
          = (Polynomial.toContinuousMapOnAlgHom (Set.Icc (-1 : ℝ) 1)) p
            + (Polynomial.toContinuousMapOnAlgHom (Set.Icc (-1 : ℝ) 1)) q := map_add _ _ _
      rw [this]
      exact Submodule.add_mem _ hp hq
  | monomial k a =>
      have hmon : (Polynomial.toContinuousMapOnAlgHom (Set.Icc (-1 : ℝ) 1))
            (Polynomial.monomial k a)
          = a • ((Polynomial.X : Polynomial ℝ) ^ k).toContinuousMapOn (Set.Icc (-1 : ℝ) 1) := by
        ext x
        simp [Polynomial.toContinuousMapOnAlgHom, Polynomial.toContinuousMapOn,
          Polynomial.eval_monomial]
      rw [hmon]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- **Monomial test functions suffice.** The monomials `x ↦ xᵖ` are not dense in `C([-1,1], ℝ)`,
but they span a dense subspace (Stone–Weierstrass), and the identity is linear in the test function.
This is the sharpest usable form: a mixed `p`-spin family has covariance profile
`ξ(r) = ∑ₚ βₚ² rᵖ`, and differentiating in the couplings isolates the individual monomials. -/
theorem satisfiesGhirlandaGuerra_of_monomial {μ : Measure (ℕ → ℕ → OverlapValue)}
    [IsProbabilityMeasure μ]
    (h : ∀ (n : ℕ), 0 < n → ∀ f : C(ℕ → ℕ → OverlapValue, ℝ), DependsOnFirst n f →
      ∀ p : ℕ,
        (∫ R, entry R 0 n ^ p * f R ∂μ)
          = (1 / (n : ℝ)) * ((∫ R, entry R 0 n ^ p ∂μ) * ∫ R, f R ∂μ)
            + (1 / (n : ℝ)) * ∑ l ∈ Finset.Ico 1 n, ∫ R, entry R 0 l ^ p * f R ∂μ) :
    SatisfiesGhirlandaGuerra μ := by
  refine satisfiesGhirlandaGuerra_of_denseSpan
    (dense_polynomialFunctions.mono polynomialFunctions_subset_span_monomials) ?_
  rintro n hn f hf φ ⟨p, rfl⟩
  have hval : ∀ (R : ℕ → ℕ → OverlapValue) (l : ℕ),
      (((Polynomial.X : Polynomial ℝ) ^ p).toContinuousMapOn (Set.Icc (-1 : ℝ) 1)) (R 0 l)
        = entry R 0 l ^ p := by
    intro R l
    simp [Polynomial.toContinuousMapOn, entry]
  simp only [hval]
  exact h n hn f hf p

/-- **Polynomial test functions suffice.** -/
theorem satisfiesGhirlandaGuerra_of_polynomial {μ : Measure (ℕ → ℕ → OverlapValue)}
    [IsProbabilityMeasure μ]
    (h : ∀ (n : ℕ), 0 < n → ∀ f : C(ℕ → ℕ → OverlapValue, ℝ), DependsOnFirst n f →
      ∀ p : Polynomial ℝ,
        (∫ R, p.eval (entry R 0 n) * f R ∂μ)
          = (1 / (n : ℝ)) * ((∫ R, p.eval (entry R 0 n) ∂μ) * ∫ R, f R ∂μ)
            + (1 / (n : ℝ)) * ∑ l ∈ Finset.Ico 1 n, ∫ R, p.eval (entry R 0 l) * f R ∂μ) :
    SatisfiesGhirlandaGuerra μ := by
  refine satisfiesGhirlandaGuerra_of_dense (S := Set.range fun p : Polynomial ℝ =>
    p.toContinuousMapOn (Set.Icc (-1 : ℝ) 1)) ?_ ?_
  · have hcoe : ((polynomialFunctions (Set.Icc (-1 : ℝ) 1) :
        Subalgebra ℝ C(Set.Icc (-1 : ℝ) 1, ℝ)) : Set C(Set.Icc (-1 : ℝ) 1, ℝ))
        = Set.range fun p : Polynomial ℝ => p.toContinuousMapOn (Set.Icc (-1 : ℝ) 1) :=
      polynomialFunctions_coe _
    rw [← hcoe]
    exact dense_polynomialFunctions
  · rintro n hn f hf φ ⟨p, rfl⟩
    exact h n hn f hf p

/-! ### Panchenko's form of the identities

Panchenko writes the first term of (15.40) as `E⟨ψ(R_{1,2})⟩` rather than `E⟨ψ(R_{1,n+1})⟩`. For a
weakly exchangeable law the two agree, because all pairwise overlaps are equidistributed. -/

/-- The Ghirlanda–Guerra identities in Panchenko's form (1.1): the first factor on the right is the
expectation of `ψ` at the **first** overlap. -/
def SatisfiesGhirlandaGuerra' (μ : Measure (ℕ → ℕ → OverlapValue)) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ f : C(ℕ → ℕ → OverlapValue, ℝ), DependsOnFirst n f →
    ∀ φ : C(OverlapValue, ℝ),
      (∫ R, φ (R 0 n) * f R ∂μ)
        = (1 / (n : ℝ)) * ((∫ R, φ (R 0 1) ∂μ) * ∫ R, f R ∂μ)
          + (1 / (n : ℝ)) * ∑ l ∈ Finset.Ico 1 n, ∫ R, φ (R 0 l) * f R ∂μ

/-- **Talagrand's (15.40) and Panchenko's (1.1) agree for a weakly exchangeable law.** -/
theorem satisfiesGhirlandaGuerra_iff_of_isJointlyExchangeable
    {μ : Measure (ℕ → ℕ → OverlapValue)} (hμ : IsJointlyExchangeable μ) :
    SatisfiesGhirlandaGuerra μ ↔ SatisfiesGhirlandaGuerra' μ := by
  have key : ∀ (φ : C(OverlapValue, ℝ)) (n : ℕ), 0 < n →
      (∫ R, φ (R 0 n) ∂μ) = ∫ R, φ (R 0 1) ∂μ := by
    intro φ n hn
    have hm : ∀ l : ℕ, Measurable fun R : ℕ → ℕ → OverlapValue => R 0 l :=
      fun l => (measurable_pi_apply l).comp (measurable_pi_apply 0)
    have h1 : (∫ R, φ (R 0 n) ∂μ) = ∫ y, φ y ∂(μ.map fun R => R 0 n) :=
      (MeasureTheory.integral_map (hm n).aemeasurable
        φ.continuous.aestronglyMeasurable).symm
    have h2 : (∫ R, φ (R 0 1) ∂μ) = ∫ y, φ y ∂(μ.map fun R => R 0 1) :=
      (MeasureTheory.integral_map (hm 1).aemeasurable
        φ.continuous.aestronglyMeasurable).symm
    rw [h1, h2, map_entry_eq_oneOverlapLaw hμ (Nat.ne_of_lt hn),
      map_entry_eq_oneOverlapLaw hμ (by omega : (0 : ℕ) ≠ 1)]
  constructor
  · intro h n hn f hf φ
    rw [← key φ n hn]
    exact h n hn f hf φ
  · intro h n hn f hf φ
    rw [key φ n hn]
    exact h n hn f hf φ

/-! ### Mixtures -/

/-- Ultrametricity is preserved by mixtures: it is an almost-sure property. -/
theorem isUltrametric_bind {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {κ : Ω → Measure (ℕ → ℕ → OverlapValue)} (hκ : Measurable κ)
    (hU : ∀ ω, IsUltrametric (κ ω)) : IsUltrametric (P.bind κ) := by
  rw [IsUltrametric, Measure.bind_apply isClosed_ultrametricSet.measurableSet hκ.aemeasurable]
  have hone : ∀ ω, κ ω ultrametricSet = 1 := hU
  simp [hone, measure_univ]

/-! ### The replica-symmetric array: the ontology is non-vacuous

For `q ∈ [0,1]` the array with all off-diagonal entries equal to `q` satisfies **every** property of
§15.3 at once: it is weakly exchangeable, a Gram array, ultrametric, and it satisfies the
Ghirlanda–Guerra identities, with one-overlap law `δ_q`. This is the replica-symmetric `μ*` of
Talagrand's Theorem 15.3.6 at `μ = δ_q`. -/

/-- The replica-symmetric array: distinct replicas have overlap `q`, the diagonal is `1`. -/
def constArray (q : OverlapValue) : ℕ → ℕ → OverlapValue :=
  fun l l' => if l = l' then ⟨1, by norm_num⟩ else q

@[simp] lemma constArray_self (q : OverlapValue) (l : ℕ) :
    constArray q l l = ⟨1, by norm_num⟩ := by simp [constArray]

@[simp] lemma constArray_of_ne (q : OverlapValue) {l l' : ℕ} (h : l ≠ l') :
    constArray q l l' = q := by simp [constArray, h]

/-- The replica-symmetric array law. -/
def rsArrayLaw (q : OverlapValue) : Measure (ℕ → ℕ → OverlapValue) :=
  Measure.dirac (constArray q)

instance isProbabilityMeasure_rsArrayLaw (q : OverlapValue) :
    IsProbabilityMeasure (rsArrayLaw q) := by rw [rsArrayLaw]; infer_instance

theorem isJointlyExchangeable_rsArrayLaw (q : OverlapValue) :
    IsJointlyExchangeable (rsArrayLaw q) := by
  intro σ hσ
  have hfix : permuteArray σ (constArray q) = constArray q := by
    funext l l'
    by_cases h : l = l'
    · subst h; simp [permuteArray]
    · have hne : σ l ≠ σ l' := fun hc => h (σ.injective hc)
      simp [permuteArray, constArray, h, hne]
  rw [rsArrayLaw, Measure.map_dirac' (measurable_permuteArray σ), hfix]

theorem constArray_mem_gramArray {q : OverlapValue} (hq : 0 ≤ (q : ℝ)) :
    constArray q ∈ gramArray := by
  classical
  have hq1 : (q : ℝ) ≤ 1 := q.2.2
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine Set.mem_iInter.2 fun l => Set.mem_iInter.2 fun l' => ?_
    by_cases h : l = l'
    · subst h; rfl
    · have h' : l' ≠ l := Ne.symm h
      simp [constArray, h, h']
  · exact Set.mem_iInter.2 fun l => by simp [constArray]
  · refine Set.mem_iInter.2 fun s => Set.mem_iInter.2 fun c => ?_
    have hterm : ∀ l l' : ℕ, c l * c l' * ((constArray q l l' : OverlapValue) : ℝ)
        = (q : ℝ) * (c l * c l') + (1 - (q : ℝ)) * (if l = l' then c l ^ 2 else 0) := by
      intro l l'
      by_cases h : l = l'
      · subst h; simp [constArray]; ring
      · simp [constArray, h]; ring
    have hA : ∑ l ∈ s, ∑ l' ∈ s, (q : ℝ) * (c l * c l')
        = (q : ℝ) * ((∑ l ∈ s, c l) * ∑ l' ∈ s, c l') := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]
    have hB : ∑ l ∈ s, ∑ l' ∈ s, (1 - (q : ℝ)) * (if l = l' then c l ^ 2 else 0)
        = (1 - (q : ℝ)) * ∑ l ∈ s, c l ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [← Finset.mul_sum, Finset.sum_ite_eq s l fun _ => c l ^ 2]
      simp [hl]
    have hsplit : ∑ l ∈ s, ∑ l' ∈ s, c l * c l' * ((constArray q l l' : OverlapValue) : ℝ)
        = (q : ℝ) * ((∑ l ∈ s, c l) * ∑ l' ∈ s, c l') + (1 - (q : ℝ)) * ∑ l ∈ s, c l ^ 2 := by
      calc ∑ l ∈ s, ∑ l' ∈ s, c l * c l' * ((constArray q l l' : OverlapValue) : ℝ)
          = ∑ l ∈ s, ∑ l' ∈ s, ((q : ℝ) * (c l * c l')
              + (1 - (q : ℝ)) * (if l = l' then c l ^ 2 else 0)) :=
            Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => hterm l l'
        _ = (∑ l ∈ s, ∑ l' ∈ s, (q : ℝ) * (c l * c l'))
              + ∑ l ∈ s, ∑ l' ∈ s, (1 - (q : ℝ)) * (if l = l' then c l ^ 2 else 0) := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun l _ => Finset.sum_add_distrib
        _ = (q : ℝ) * ((∑ l ∈ s, c l) * ∑ l' ∈ s, c l')
              + (1 - (q : ℝ)) * ∑ l ∈ s, c l ^ 2 := by rw [hA, hB]
    change (0 : ℝ) ≤ ∑ l ∈ s, ∑ l' ∈ s, c l * c l' * ((constArray q l l' : OverlapValue) : ℝ)
    rw [hsplit]
    have h1 : (0 : ℝ) ≤ (q : ℝ) * ((∑ l ∈ s, c l) * ∑ l' ∈ s, c l') := by
      rw [← sq]; exact mul_nonneg hq (sq_nonneg _)
    have h2 : (0 : ℝ) ≤ (1 - (q : ℝ)) * ∑ l ∈ s, c l ^ 2 :=
      mul_nonneg (by linarith) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    linarith

theorem gramArray_rsArrayLaw {q : OverlapValue} (hq : 0 ≤ (q : ℝ)) :
    rsArrayLaw q gramArray = 1 :=
  Measure.dirac_apply_of_mem (constArray_mem_gramArray hq)

theorem isUltrametric_rsArrayLaw (q : OverlapValue) : IsUltrametric (rsArrayLaw q) := by
  refine Measure.dirac_apply_of_mem ?_
  simp [ultrametricSet, entry, constArray]

theorem oneOverlapLaw_rsArrayLaw (q : OverlapValue) :
    oneOverlapLaw (rsArrayLaw q) = Measure.dirac q := by
  have hm : Measurable fun R : ℕ → ℕ → OverlapValue => R 0 1 :=
    (measurable_pi_apply 1).comp (measurable_pi_apply 0)
  rw [oneOverlapLaw, rsArrayLaw, Measure.map_dirac' hm]
  simp [constArray]

/-- **The Ghirlanda–Guerra identities hold for the replica-symmetric array.** Both sides evaluate
to `φ(q) f(C)`, the right-hand side because the sum over `Finset.Ico 1 n` has `n - 1` terms. -/
theorem satisfiesGhirlandaGuerra_rsArrayLaw (q : OverlapValue) :
    SatisfiesGhirlandaGuerra (rsArrayLaw q) := by
  intro n hn f hf φ
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hd : ∀ g : C(ℕ → ℕ → OverlapValue, ℝ),
      (∫ R, g R ∂(rsArrayLaw q)) = g (constArray q) := fun g => by
    rw [rsArrayLaw]; exact integral_dirac' _ _ g.continuous.stronglyMeasurable
  have e1 : (∫ R, φ (R 0 n) * f R ∂(rsArrayLaw q)) = φ q * f (constArray q) := by
    have := hd ((φ.comp (evalCM 0 n)) * f)
    simpa [constArray_of_ne q (Nat.ne_of_lt hn)] using this
  have e2 : (∫ R, φ (R 0 n) ∂(rsArrayLaw q)) = φ q := by
    have := hd (φ.comp (evalCM 0 n))
    simpa [constArray_of_ne q (Nat.ne_of_lt hn)] using this
  have e3 : (∫ R, f R ∂(rsArrayLaw q)) = f (constArray q) := hd f
  have e4 : ∀ l ∈ Finset.Ico 1 n, (∫ R, φ (R 0 l) * f R ∂(rsArrayLaw q))
      = φ q * f (constArray q) := by
    intro l hl
    have hl0 : (0 : ℕ) ≠ l := by
      have := (Finset.mem_Ico.1 hl).1; omega
    have := hd ((φ.comp (evalCM 0 l)) * f)
    simpa [constArray_of_ne q hl0] using this
  rw [e1, e2, e3, Finset.sum_congr rfl e4, Finset.sum_const, Nat.card_Ico]
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have : (1 : ℕ) ≤ n := hn
    push_cast [Nat.cast_sub this]
    ring
  rw [nsmul_eq_mul, hcast]
  field_simp
  ring

/-! ### The limiting law of a spin glass -/

/-- **The class of laws Talagrand Vol. II, §15.3 is about is stable under weak limits**: weak
exchangeability, the Gram condition, ultrametricity and the Ghirlanda–Guerra identities all pass to
the limit. Consequently they may be verified along any approximating sequence. -/
theorem tendsto_asymptoticArrayLaw {ι : Type*} {L : Filter ι} [L.NeBot]
    {μs : ι → ProbabilityMeasure (ℕ → ℕ → OverlapValue)}
    {μ : ProbabilityMeasure (ℕ → ℕ → OverlapValue)} (hlim : Tendsto μs L (𝓝 μ))
    (hex : ∀ᶠ i in L, IsJointlyExchangeable (μs i : Measure (ℕ → ℕ → OverlapValue)))
    (hgram : ∀ᶠ i in L, (μs i : Measure (ℕ → ℕ → OverlapValue)) gramArray = 1)
    (hU : ∀ᶠ i in L, IsUltrametric (μs i : Measure (ℕ → ℕ → OverlapValue)))
    (hgg : ∀ᶠ i in L, SatisfiesGhirlandaGuerra (μs i : Measure (ℕ → ℕ → OverlapValue))) :
    IsJointlyExchangeable (μ : Measure (ℕ → ℕ → OverlapValue))
      ∧ (μ : Measure (ℕ → ℕ → OverlapValue)) gramArray = 1
      ∧ IsUltrametric (μ : Measure (ℕ → ℕ → OverlapValue))
      ∧ SatisfiesGhirlandaGuerra (μ : Measure (ℕ → ℕ → OverlapValue)) :=
  ⟨isJointlyExchangeable_of_tendsto hlim hex,
    ProbabilityMeasure.measure_eq_one_of_tendsto_of_isClosed hlim isClosed_gramArray hgram,
    isUltrametric_of_tendsto hlim hU,
    satisfiesGhirlandaGuerra_of_tendsto hlim hgg⟩

end

end SpinGlass
