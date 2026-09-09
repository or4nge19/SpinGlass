/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Limit.AsymptoticArrayLaws
import SpinGlass.MixedPSpinGhirlandaGuerra

/-!
# From approximate to exact Ghirlanda–Guerra identities

At finite volume the Ghirlanda–Guerra identities hold only up to a defect (Talagrand, Vol. II,
Theorems 12.1.10 and 12.2.2); in the limit they hold exactly (Definition 15.3.4). This file makes
that passage formal.

* `SpinGlass.ggDefect ν n φ g` is **the defect in Talagrand's (15.40)** for the law `ν`, the test
  function `φ` of one overlap and the observable `g` of the first `n` replicas.
* `SpinGlass.continuous_ggDefect`: the defect is a continuous function of the law in the topology
  of convergence in distribution.
* `SpinGlass.satisfiesGhirlandaGuerra_iff_ggDefect`: the identities are the vanishing of the
  defect at every block observable.
* `SpinGlass.satisfiesGhirlandaGuerra_of_tendsto_ggDefect`: **approximate identities pass to the
  limit** — if the defects at every monomial tend to `0` along a convergent family of laws, the
  limit satisfies the identities at every continuous test function.
* `SpinGlass.exists_subseq_tendsto_satisfiesGhirlandaGuerra`: for a sequence of jointly
  exchangeable Gram array laws with vanishing monomial defects, some subsequence converges to a
  jointly exchangeable Gram law satisfying the Ghirlanda–Guerra identities.
-/

open MeasureTheory ProbabilityTheory Filter Topology BigOperators MeasureTheory.GibbsMeasure

namespace SpinGlass

noncomputable section

/-- **The Ghirlanda–Guerra defect** of a law `ν` of overlap arrays, at the test function `φ` of one
overlap and the observable `g` of the first `n` replicas: the difference between the two sides of
Talagrand's Definition 15.3.4, Eq. (15.40). The identities hold iff it vanishes. -/
def ggDefect (ν : Measure (ℕ → ℕ → OverlapValue)) (n : ℕ) (φ : C(OverlapValue, ℝ))
    (g : C(Fin n → Fin n → OverlapValue, ℝ)) : ℝ :=
  (∫ R, φ (R 0 n) * g (blockRestrict n R) ∂ν)
    - ((1 / (n : ℝ)) * ((∫ R, φ (R 0 n) ∂ν) * ∫ R, g (blockRestrict n R) ∂ν)
      + (1 / (n : ℝ)) * ∑ l ∈ Finset.Ico 1 n, ∫ R, φ (R 0 l) * g (blockRestrict n R) ∂ν)

/-- **The defect is continuous in the law**, in the topology of convergence in distribution: every
term of (15.40) is the integral of a fixed continuous function. -/
theorem continuous_ggDefect (n : ℕ) (φ : C(OverlapValue, ℝ))
    (g : C(Fin n → Fin n → OverlapValue, ℝ)) :
    Continuous fun ν : ProbabilityMeasure (ℕ → ℕ → OverlapValue) =>
      ggDefect (ν : Measure (ℕ → ℕ → OverlapValue)) n φ g := by
  unfold ggDefect
  refine Continuous.sub ?_ (Continuous.add (continuous_const.mul (Continuous.mul ?_ ?_))
    (continuous_const.mul (continuous_finsetSum _ fun l _ => ?_)))
  · exact ProbabilityMeasure.continuous_integral_continuousMap
      ((φ.comp (evalCM 0 n)) * g.comp (blockRestrict n))
  · exact ProbabilityMeasure.continuous_integral_continuousMap (φ.comp (evalCM 0 n))
  · exact ProbabilityMeasure.continuous_integral_continuousMap (g.comp (blockRestrict n))
  · exact ProbabilityMeasure.continuous_integral_continuousMap
      ((φ.comp (evalCM 0 l)) * g.comp (blockRestrict n))

/-- **The identities are the vanishing of the defect** at every block observable. -/
theorem satisfiesGhirlandaGuerra_iff_ggDefect (μ : Measure (ℕ → ℕ → OverlapValue)) :
    SatisfiesGhirlandaGuerra μ ↔
      ∀ n, 0 < n → ∀ (φ : C(OverlapValue, ℝ)) (g : C(Fin n → Fin n → OverlapValue, ℝ)),
        ggDefect μ n φ g = 0 := by
  constructor
  · intro h n hn φ g
    have := h n hn (g.comp (blockRestrict n)) (dependsOnFirst_comp_blockRestrict n g) φ
    simp only [ContinuousMap.comp_apply] at this
    unfold ggDefect
    exact sub_eq_zero.2 this
  · intro h n hn f hf φ
    obtain ⟨g, hg⟩ := (dependsOnFirst_iff_exists n f).1 hf
    have := h n hn φ g
    unfold ggDefect at this
    simp only [hg]
    exact sub_eq_zero.1 this

/-- The defect vanishes identically at the constant test function `φ = 1`, for every probability
law: both sides of (15.40) are `∫ g`. -/
theorem ggDefect_monomial_zero (ν : Measure (ℕ → ℕ → OverlapValue)) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 0 < n) (g : C(Fin n → Fin n → OverlapValue, ℝ)) :
    ggDefect ν n (overlapMonomialCM 0) g = 0 := by
  unfold ggDefect
  simp only [overlapMonomialCM_apply, pow_zero, one_mul, integral_const, probReal_univ,
    smul_eq_mul, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hn' : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have : (1 : ℕ) ≤ n := hn
    push_cast [Nat.cast_sub this]
    ring
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [hn']
  field_simp
  ring

/-- **Approximate Ghirlanda–Guerra identities pass to the limit.** If `μs → μ` in distribution and
the defect of `μs i` at every monomial `rᵖ` and every block observable tends to `0`, then `μ`
satisfies the identities at every continuous test function
(`satisfiesGhirlandaGuerra_of_monomial`). -/
theorem satisfiesGhirlandaGuerra_of_tendsto_ggDefect {ι : Type*} {L : Filter ι} [L.NeBot]
    {μs : ι → ProbabilityMeasure (ℕ → ℕ → OverlapValue)}
    {μ : ProbabilityMeasure (ℕ → ℕ → OverlapValue)} (hlim : Tendsto μs L (𝓝 μ))
    (hdef : ∀ n, 0 < n → ∀ (p : ℕ) (g : C(Fin n → Fin n → OverlapValue, ℝ)),
      Tendsto (fun i => ggDefect (μs i : Measure (ℕ → ℕ → OverlapValue)) n
        (overlapMonomialCM p) g) L (𝓝 0)) :
    SatisfiesGhirlandaGuerra (μ : Measure (ℕ → ℕ → OverlapValue)) := by
  refine satisfiesGhirlandaGuerra_of_monomial fun n hn f hf p => ?_
  obtain ⟨g, hg⟩ := (dependsOnFirst_iff_exists n f).1 hf
  have h0 : ggDefect (μ : Measure (ℕ → ℕ → OverlapValue)) n (overlapMonomialCM p) g = 0 :=
    tendsto_nhds_unique
      (((continuous_ggDefect n (overlapMonomialCM p) g).tendsto μ).comp hlim) (hdef n hn p g)
  unfold ggDefect at h0
  simp only [overlapMonomialCM_apply] at h0
  simp only [hg, entry]
  exact sub_eq_zero.1 h0

/-- **From approximate identities at finite volume to exact identities in the limit.** For a
sequence of jointly exchangeable Gram array laws whose defects at every monomial and every block
observable tend to `0`, some subsequence converges in distribution to a law that is jointly
exchangeable, carried by the Gram arrays, and satisfies the Ghirlanda–Guerra identities. -/
theorem exists_subseq_tendsto_satisfiesGhirlandaGuerra
    (μs : ℕ → ProbabilityMeasure (ℕ → ℕ → OverlapValue))
    (hex : ∀ k, IsJointlyExchangeable (μs k : Measure (ℕ → ℕ → OverlapValue)))
    (hgram : ∀ k, (μs k : Measure (ℕ → ℕ → OverlapValue)) gramArray = 1)
    (hdef : ∀ n, 0 < n → ∀ (p : ℕ) (g : C(Fin n → Fin n → OverlapValue, ℝ)),
      Tendsto (fun k => ggDefect (μs k : Measure (ℕ → ℕ → OverlapValue)) n
        (overlapMonomialCM p) g) atTop (𝓝 0)) :
    ∃ (μ : ProbabilityMeasure (ℕ → ℕ → OverlapValue)) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun k => μs (φ k)) atTop (𝓝 μ) ∧
      IsJointlyExchangeable (μ : Measure (ℕ → ℕ → OverlapValue)) ∧
      (μ : Measure (ℕ → ℕ → OverlapValue)) gramArray = 1 ∧
      SatisfiesGhirlandaGuerra (μ : Measure (ℕ → ℕ → OverlapValue)) := by
  obtain ⟨μ, φ, hφ, hlim, hexμ⟩ := exists_subseq_tendsto_jointlyExchangeable μs hex
  refine ⟨μ, φ, hφ, hlim, hexμ, ?_, ?_⟩
  · exact ProbabilityMeasure.measure_eq_one_of_tendsto_of_isClosed hlim isClosed_gramArray
      (Eventually.of_forall fun k => hgram (φ k))
  · exact satisfiesGhirlandaGuerra_of_tendsto_ggDefect hlim
      fun n hn p g => (hdef n hn p g).comp hφ.tendsto_atTop

/-! ### Linearity and boundedness of the defect -/

section Linear

variable (ν : Measure (ℕ → ℕ → OverlapValue)) [IsProbabilityMeasure ν] {n : ℕ}
variable (g : C(Fin n → Fin n → OverlapValue, ℝ))

lemma integral_comp_entry_mul_sub (φ ψ : C(OverlapValue, ℝ)) (l : ℕ) :
    (∫ R, (φ - ψ) (R 0 l) * g (blockRestrict n R) ∂ν)
      = (∫ R, φ (R 0 l) * g (blockRestrict n R) ∂ν)
        - ∫ R, ψ (R 0 l) * g (blockRestrict n R) ∂ν := by
  have hφ : Integrable (fun R : ℕ → ℕ → OverlapValue => φ (R 0 l) * g (blockRestrict n R)) ν :=
    integrable_continuousMap ((φ.comp (evalCM 0 l)) * g.comp (blockRestrict n))
  have hψ : Integrable (fun R : ℕ → ℕ → OverlapValue => ψ (R 0 l) * g (blockRestrict n R)) ν :=
    integrable_continuousMap ((ψ.comp (evalCM 0 l)) * g.comp (blockRestrict n))
  rw [← integral_sub hφ hψ]
  refine integral_congr_ae (Eventually.of_forall fun R => ?_)
  simp only [ContinuousMap.sub_apply]
  ring

omit [IsProbabilityMeasure ν] in
lemma integral_comp_entry_mul_smul (c : ℝ) (φ : C(OverlapValue, ℝ)) (l : ℕ) :
    (∫ R, (c • φ) (R 0 l) * g (blockRestrict n R) ∂ν)
      = c * ∫ R, φ (R 0 l) * g (blockRestrict n R) ∂ν := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun R => ?_)
  simp only [ContinuousMap.smul_apply, smul_eq_mul]
  ring

lemma integral_comp_entry_sub (φ ψ : C(OverlapValue, ℝ)) (l : ℕ) :
    (∫ R, (φ - ψ) (R 0 l) ∂ν) = (∫ R, φ (R 0 l) ∂ν) - ∫ R, ψ (R 0 l) ∂ν := by
  have hφ : Integrable (fun R : ℕ → ℕ → OverlapValue => φ (R 0 l)) ν :=
    integrable_continuousMap (φ.comp (evalCM 0 l))
  have hψ : Integrable (fun R : ℕ → ℕ → OverlapValue => ψ (R 0 l)) ν :=
    integrable_continuousMap (ψ.comp (evalCM 0 l))
  rw [← integral_sub hφ hψ]
  rfl

omit [IsProbabilityMeasure ν] in
lemma integral_comp_entry_smul (c : ℝ) (φ : C(OverlapValue, ℝ)) (l : ℕ) :
    (∫ R, (c • φ) (R 0 l) ∂ν) = c * ∫ R, φ (R 0 l) ∂ν := by
  rw [← integral_const_mul]
  rfl

/-- The defect is linear in the test function: differences. -/
theorem ggDefect_sub (φ ψ : C(OverlapValue, ℝ)) :
    ggDefect ν n (φ - ψ) g = ggDefect ν n φ g - ggDefect ν n ψ g := by
  unfold ggDefect
  simp only [integral_comp_entry_mul_sub ν g, integral_comp_entry_sub ν, Finset.sum_sub_distrib]
  ring

omit [IsProbabilityMeasure ν] in
/-- The defect is linear in the test function: scalars. -/
theorem ggDefect_smul (c : ℝ) (φ : C(OverlapValue, ℝ)) :
    ggDefect ν n (c • φ) g = c * ggDefect ν n φ g := by
  unfold ggDefect
  simp only [integral_comp_entry_mul_smul ν g, integral_comp_entry_smul ν, ← Finset.mul_sum]
  ring

/-- The defect is linear in the test function: finite sums. -/
theorem ggDefect_finsetSum {ι : Type*} (s : Finset ι) (φ : ι → C(OverlapValue, ℝ)) :
    ggDefect ν n (∑ i ∈ s, φ i) g = ∑ i ∈ s, ggDefect ν n (φ i) g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : (0 : C(OverlapValue, ℝ)) = (0 : ℝ) • (0 : C(OverlapValue, ℝ)) := by simp
    rw [h0, ggDefect_smul, zero_mul]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    have : ggDefect ν n (φ a + ∑ i ∈ s, φ i) g
        = ggDefect ν n (φ a - (-(∑ i ∈ s, φ i))) g := by rw [sub_neg_eq_add]
    rw [this, ggDefect_sub]
    have hneg : (-(∑ i ∈ s, φ i) : C(OverlapValue, ℝ)) = (-1 : ℝ) • ∑ i ∈ s, φ i := by simp
    rw [hneg, ggDefect_smul]
    ring

/-- **The defect is bounded by `2 ‖φ‖ ‖g‖`**: each of the terms of (15.40) is bounded by
`‖φ‖ ‖g‖`, and the weights `1/n`, `(n-1)/n` sum to one. -/
theorem abs_ggDefect_le (hn : 0 < n) (φ : C(OverlapValue, ℝ)) :
    |ggDefect ν n φ g| ≤ 2 * ‖φ‖ * ‖g‖ := by
  have hb : ∀ l : ℕ, |∫ R, φ (R 0 l) * g (blockRestrict n R) ∂ν| ≤ ‖φ‖ * ‖g‖ := by
    intro l
    have := norm_integral_le_of_norm_le_const (μ := ν) (C := ‖φ‖ * ‖g‖)
      (f := fun R : ℕ → ℕ → OverlapValue => φ (R 0 l) * g (blockRestrict n R))
      (Eventually.of_forall fun R => by
        rw [norm_mul]
        exact mul_le_mul (φ.norm_coe_le_norm _) (g.norm_coe_le_norm _) (norm_nonneg _)
          (norm_nonneg _))
    simpa [Real.norm_eq_abs] using this
  have hφ : |∫ R, φ (R 0 n) ∂ν| ≤ ‖φ‖ := by
    have := norm_integral_le_of_norm_le_const (μ := ν) (C := ‖φ‖)
      (f := fun R : ℕ → ℕ → OverlapValue => φ (R 0 n))
      (Eventually.of_forall fun R => φ.norm_coe_le_norm _)
    simpa [Real.norm_eq_abs] using this
  have hg : |∫ R, g (blockRestrict n R) ∂ν| ≤ ‖g‖ := by
    have := norm_integral_le_of_norm_le_const (μ := ν) (C := ‖g‖)
      (f := fun R : ℕ → ℕ → OverlapValue => g (blockRestrict n R))
      (Eventually.of_forall fun R => g.norm_coe_le_norm _)
    simpa [Real.norm_eq_abs] using this
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsum : |∑ l ∈ Finset.Ico 1 n, ∫ R, φ (R 0 l) * g (blockRestrict n R) ∂ν|
      ≤ ((n : ℝ) - 1) * (‖φ‖ * ‖g‖) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun l _ => hb l).trans (le_of_eq ?_)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have : (1 : ℕ) ≤ n := hn
    push_cast [Nat.cast_sub this]
    ring
  unfold ggDefect
  have h1 : |(1 / (n : ℝ)) * ((∫ R, φ (R 0 n) ∂ν) * ∫ R, g (blockRestrict n R) ∂ν)|
      ≤ (1 / (n : ℝ)) * (‖φ‖ * ‖g‖) := by
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (n : ℝ))]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hφ hg (abs_nonneg _) (norm_nonneg _))
      (by positivity)
  have h2 : |(1 / (n : ℝ)) * ∑ l ∈ Finset.Ico 1 n, ∫ R, φ (R 0 l) * g (blockRestrict n R) ∂ν|
      ≤ (1 / (n : ℝ)) * (((n : ℝ) - 1) * (‖φ‖ * ‖g‖)) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (n : ℝ))]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  have hcomb : (1 / (n : ℝ)) * (‖φ‖ * ‖g‖) + (1 / (n : ℝ)) * (((n : ℝ) - 1) * (‖φ‖ * ‖g‖))
      = ‖φ‖ * ‖g‖ := by
    field_simp
    ring
  calc |(∫ R, φ (R 0 n) * g (blockRestrict n R) ∂ν)
        - ((1 / (n : ℝ)) * ((∫ R, φ (R 0 n) ∂ν) * ∫ R, g (blockRestrict n R) ∂ν)
          + (1 / (n : ℝ)) * ∑ l ∈ Finset.Ico 1 n, ∫ R, φ (R 0 l) * g (blockRestrict n R) ∂ν)|
      ≤ |∫ R, φ (R 0 n) * g (blockRestrict n R) ∂ν|
        + (|(1 / (n : ℝ)) * ((∫ R, φ (R 0 n) ∂ν) * ∫ R, g (blockRestrict n R) ∂ν)|
          + |(1 / (n : ℝ)) * ∑ l ∈ Finset.Ico 1 n, ∫ R, φ (R 0 l) * g (blockRestrict n R) ∂ν|) :=
        (abs_sub _ _).trans (add_le_add le_rfl (abs_add_le _ _))
    _ ≤ ‖φ‖ * ‖g‖ + (‖φ‖ * ‖g‖) := by
        have := add_le_add h1 h2
        rw [hcomb] at this
        linarith [hb n]
    _ = 2 * ‖φ‖ * ‖g‖ := by ring

end Linear

/-! ### Talagrand's Definition 15.4.1: the extended identities, uniformly over observables -/

/-- **Talagrand's Definition 15.4.1.** A sequence of array laws satisfies the *extended
Ghirlanda–Guerra identities asymptotically* if, for every number `n` of replicas and every
continuous test function `φ` of one overlap, the defect in (15.40) tends to `0` **uniformly over
the observables `g` of the first `n` replicas**, relative to `‖g‖`. -/
def TendstoGGDefectUniform (μs : ℕ → Measure (ℕ → ℕ → OverlapValue)) : Prop :=
  ∀ n, 0 < n → ∀ φ : C(OverlapValue, ℝ), ∀ η > 0, ∀ᶠ N in atTop,
    ∀ g : C(Fin n → Fin n → OverlapValue, ℝ),
      |ggDefect (μs N) n φ g| ≤ η * ‖g‖

/-- The monomial `x ↦ xᵖ` on `[-1,1]` as a polynomial function agrees with `overlapMonomialCM`. -/
lemma toContinuousMapOn_X_pow_eq (p : ℕ) :
    ((Polynomial.X : Polynomial ℝ) ^ p).toContinuousMapOn (Set.Icc (-1 : ℝ) 1)
      = overlapMonomialCM p := by
  ext x
  simp [Polynomial.toContinuousMapOn, overlapMonomialCM_apply]

/-- **Monomial test functions suffice, uniformly** (Stone–Weierstrass): if the defects at every
monomial `xᵖ` vanish uniformly over the observables, so do the defects at every continuous test
function. -/
theorem tendstoGGDefectUniform_of_monomial (μs : ℕ → Measure (ℕ → ℕ → OverlapValue))
    [∀ N, IsProbabilityMeasure (μs N)]
    (h : ∀ n, 0 < n → ∀ p : ℕ, ∀ η > 0, ∀ᶠ N in atTop,
      ∀ g : C(Fin n → Fin n → OverlapValue, ℝ),
        |ggDefect (μs N) n (overlapMonomialCM p) g| ≤ η * ‖g‖) :
    TendstoGGDefectUniform μs := by
  classical
  intro n hn φ η hη
  -- approximate `φ` by a polynomial within `η/4`
  obtain ⟨P, hPmem, hPdist⟩ :=
    dense_polynomialFunctions.exists_dist_lt φ (by positivity : 0 < η / 4)
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1
    (polynomialFunctions_subset_span_monomials hPmem)
  -- `P = ∑ c p • xᵖ`
  have hP : P = ∑ p ∈ c.support, c p • overlapMonomialCM p := by
    rw [← hc, Finsupp.sum]
    exact Finset.sum_congr rfl fun p _ => by rw [toContinuousMapOn_X_pow_eq]
  set M : ℝ := (∑ p ∈ c.support, |c p|) + 1 with hM
  have hMpos : 0 < M := by positivity
  -- each monomial defect is eventually small
  have hev : ∀ᶠ N in atTop, ∀ p ∈ c.support,
      ∀ g : C(Fin n → Fin n → OverlapValue, ℝ),
        |ggDefect (μs N) n (overlapMonomialCM p) g| ≤ (η / (2 * M)) * ‖g‖ :=
    (eventually_all_finset c.support).2 fun p _ => h n hn p (η / (2 * M)) (by positivity)
  filter_upwards [hev] with N hN g
  have hg0 : 0 ≤ ‖g‖ := norm_nonneg g
  -- the polynomial defect
  have hPdef : |ggDefect (μs N) n P g| ≤ (η / 2) * ‖g‖ := by
    rw [hP, ggDefect_finsetSum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ p ∈ c.support, |ggDefect (μs N) n (c p • overlapMonomialCM p) g|
        = ∑ p ∈ c.support, |c p| * |ggDefect (μs N) n (overlapMonomialCM p) g| := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [ggDefect_smul, abs_mul]
      _ ≤ ∑ p ∈ c.support, |c p| * ((η / (2 * M)) * ‖g‖) :=
          Finset.sum_le_sum fun p hp =>
            mul_le_mul_of_nonneg_left (hN p hp g) (abs_nonneg _)
      _ = (∑ p ∈ c.support, |c p|) * ((η / (2 * M)) * ‖g‖) := by rw [Finset.sum_mul]
      _ ≤ M * ((η / (2 * M)) * ‖g‖) := by
          have : (∑ p ∈ c.support, |c p|) ≤ M := by rw [hM]; linarith
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ = (η / 2) * ‖g‖ := by field_simp
  -- the approximation error
  have happrox : |ggDefect (μs N) n φ g - ggDefect (μs N) n P g| ≤ (η / 2) * ‖g‖ := by
    rw [← ggDefect_sub]
    refine (abs_ggDefect_le (μs N) g hn (φ - P)).trans ?_
    have : ‖φ - P‖ ≤ η / 4 := by rw [← dist_eq_norm]; exact hPdist.le
    nlinarith [norm_nonneg (φ - P)]
  calc |ggDefect (μs N) n φ g|
      ≤ |ggDefect (μs N) n φ g - ggDefect (μs N) n P g| + |ggDefect (μs N) n P g| := by
        have := abs_add_le (ggDefect (μs N) n φ g - ggDefect (μs N) n P g) (ggDefect (μs N) n P g)
        simpa using this
    _ ≤ (η / 2) * ‖g‖ + (η / 2) * ‖g‖ := add_le_add happrox hPdef
    _ = η * ‖g‖ := by ring

end

end SpinGlass
