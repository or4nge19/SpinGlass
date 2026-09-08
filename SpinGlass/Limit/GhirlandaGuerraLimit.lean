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

end

end SpinGlass
