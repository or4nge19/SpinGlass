/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.MixedPSpinLimit
import SpinGlass.Limit.PositivityGG

/-!
# Nonnegativity of the overlap for the mixed `p`-spin limit law (Vol. II, §12.3)

Talagrand's positivity principle (Theorem 12.3.1) applied to the perturbed mixed `p`-spin models of
the Ghirlanda–Guerra capstone: along the sequence, `P(R_{0,1} ≤ -ε') → 0` for every `ε' > 0`, and
the limit law gives no mass to `{R_{0,1} < 0}`. Talagrand: "the perturbation term breaks the
symmetry" — for the unperturbed SK model without external field the overlap is symmetric about `0`.

## Main statements

- `SpinGlass.tendsto_real_negLevel_mixedPSpinArrayLaw`: Theorem 12.3.1 along a sequence of mixed
  `p`-spin array laws satisfying the extended identities asymptotically.
- `SpinGlass.exists_subseq_tendsto_satisfiesGhirlandaGuerra_nonnegOverlap_mixedPSpin`: **the
  capstone with positivity**: the limit law is jointly exchangeable, Gram, satisfies the
  Ghirlanda–Guerra identities, and has nonnegative overlaps almost surely.
-/

open MeasureTheory ProbabilityTheory Filter Topology BigOperators MeasureTheory.GibbsMeasure

namespace SpinGlass

noncomputable section

/-- **Theorem 12.3.1 for mixed `p`-spin array laws.** -/
theorem tendsto_real_negLevel_mixedPSpinArrayLaw (ξ : ℕ → ℝ → ℝ) (h : ℝ)
    (hgg : TendstoGGDefectUniform fun k => mixedPSpinArrayLaw (k + 1) (ξ k) h)
    {ε' : ℝ} (hε' : 0 < ε') :
    Tendsto (fun k => (mixedPSpinArrayLaw (k + 1) (ξ k) h).real
      {R : ℕ → ℕ → OverlapValue | ((R 0 1 : OverlapValue) : ℝ) ≤ -ε'}) atTop (𝓝 0) := by
  have hprob : ∀ k, IsProbabilityMeasure ((gaussField (k + 1) (overlapCovMatrix (k + 1) (ξ k))).map
      (fun H : EnergySpace (k + 1) => H + H_field (k + 1) h)) := fun k =>
    Measure.isProbabilityMeasure_map (measurable_add_const _).aemeasurable
  exact tendsto_real_negLevel_bind (fun k => k + 1)
    (fun k => (gaussField (k + 1) (overlapCovMatrix (k + 1) (ξ k))).map
      (fun H : EnergySpace (k + 1) => H + H_field (k + 1) h)) hgg hε'

/-- **The Ghirlanda–Guerra capstone with Talagrand's positivity principle.** For every mixed
`p`-spin model and admissible scaling, there are couplings such that along a subsequence the
perturbed models' overlap-array laws converge to a jointly exchangeable Gram law that satisfies the
Ghirlanda–Guerra identities **and has nonnegative overlaps almost surely**. -/
theorem exists_subseq_tendsto_satisfiesGhirlandaGuerra_nonnegOverlap_mixedPSpin
    {P : Polynomial ℝ} (hP : ∀ k, 0 ≤ P.coeff k) (h : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (m : ℕ → ℕ) (c δ : ℕ → ℝ) (hc : ∀ N, 0 < N → 0 < c N) (hδ : ∀ N, 0 < N → 0 < δ N)
    (hm : Tendsto m atTop atTop) (hc0 : Tendsto c atTop (𝓝 0)) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hmδ : Tendsto (fun N => ((m N : ℝ) + 1) * δ N) atTop (𝓝 0))
    (hmc : Tendsto (fun N => ((m N : ℝ) + 1) * (c N) ^ 2) atTop (𝓝 0))
    (hrate : Tendsto (fun N => ((m N : ℝ) + 1) / ((c N) ^ 2 * δ N * Real.sqrt N)) atTop (𝓝 0)) :
    ∃ β : ∀ N : ℕ, Fin (m N + 1) → ℝ, (∀ N s, β N s ∈ Set.Icc a b) ∧
      ∃ (μ : ProbabilityMeasure (ℕ → ℕ → OverlapValue)) (φ : ℕ → ℕ), StrictMono φ ∧
        Tendsto (fun k => mixedPSpinArray (φ k + 1)
          (perturbedProfile (fun r => P.eval r) fun s => β (φ k + 1) s * c (φ k + 1)) h)
          atTop (𝓝 μ) ∧
        IsJointlyExchangeable (μ : Measure (ℕ → ℕ → OverlapValue)) ∧
        (μ : Measure (ℕ → ℕ → OverlapValue)) gramArray = 1 ∧
        SatisfiesGhirlandaGuerra (μ : Measure (ℕ → ℕ → OverlapValue)) ∧
        (μ : Measure (ℕ → ℕ → OverlapValue))
          {R : ℕ → ℕ → OverlapValue | ((R 0 1 : OverlapValue) : ℝ) < 0} = 0 := by
  obtain ⟨β, hβ, hunif, μ, φ, hφ, hlim, hex, hgram, hgg⟩ :=
    exists_subseq_tendsto_satisfiesGhirlandaGuerra_mixedPSpin hP h ha hab m c δ hc hδ hm hc0 hδ0
      hmδ hmc hrate
  refine ⟨β, hβ, μ, φ, hφ, hlim, hex, hgram, hgg, ?_⟩
  have hneg : ∀ ε' : ℝ, 0 < ε' → Tendsto (fun k => (mixedPSpinArray (k + 1)
      (perturbedProfile (fun r => P.eval r) fun s => β (k + 1) s * c (k + 1)) h
        : Measure (ℕ → ℕ → OverlapValue)).real
      {R : ℕ → ℕ → OverlapValue | ((R 0 1 : OverlapValue) : ℝ) ≤ -ε'}) atTop (𝓝 0) :=
    fun ε' hε' => tendsto_real_negLevel_mixedPSpinArrayLaw
      (fun k => perturbedProfile (fun r => P.eval r) fun s => β (k + 1) s * c (k + 1)) h hunif hε'
  exact measure_negOverlap_eq_zero_of_tendsto hlim fun ε' hε' =>
    (hneg ε' hε').comp hφ.tendsto_atTop

end

end SpinGlass
