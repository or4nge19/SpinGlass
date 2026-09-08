/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Limit.GhirlandaGuerraLimit
import SpinGlass.MixedPSpinPerturbation

/-!
# The Ghirlanda–Guerra identities in the thermodynamic limit of mixed `p`-spin models

Talagrand, Vol. II, §12.2 → §15.3. The finite-volume extended identities
(`exists_couplings_abs_ghirlandaGuerra_defect_mixedPSpin_monomials_le`) hold up to a defect that is
`O(N^{-1/4} c_N^{-2})` per component; letting the number of components `m_N → ∞` and the
perturbation strength `c_N → 0` slowly, the defects at every monomial vanish, and any weak limit
point of the annealed overlap-array laws of the perturbed models satisfies the identities exactly
(`exists_subseq_tendsto_satisfiesGhirlandaGuerra`).

## Main statements

- `SpinGlass.mixedPSpinArrayLaw N ξ h`: **the annealed overlap-array law of the mixed `p`-spin
  model** with profile `ξ` and external field `h` at volume `N`; it is jointly exchangeable and
  carried by the Gram arrays.
- `SpinGlass.perturbedProfile ξ w`: the profile `ξ(r) + ∑ₛ wₛ² rˢ⁺¹` of the perturbed model.
- `SpinGlass.tendsto_perturbation_rate`: the finite-volume rate vanishes under the scaling
  hypotheses.
- `SpinGlass.exists_subseq_tendsto_satisfiesGhirlandaGuerra_mixedPSpin`: **the capstone** — for
  every mixed `p`-spin model, any admissible scaling `(m_N, c_N, δ_N)` produces couplings
  `β_N ∈ [a,b]^{m_N+1}` such that along a subsequence the perturbed models' overlap-array laws
  converge to a jointly exchangeable Gram law satisfying the Ghirlanda–Guerra identities.
-/

open MeasureTheory ProbabilityTheory Filter Topology BigOperators MeasureTheory.GibbsMeasure

namespace SpinGlass

noncomputable section

/-! ### The annealed overlap-array law of a mixed `p`-spin model -/

/-- **The annealed overlap-array law** of the mixed `p`-spin model with profile `ξ` and external
field `h` at volume `N`: the law of the overlap array of i.i.d. replicas from the Gibbs measure of
the canonical field `gaussField N (overlapCovMatrix N ξ)` shifted by the field, averaged over the
disorder. -/
def mixedPSpinArrayLaw (N : ℕ) (ξ : ℝ → ℝ) (h : ℝ) : Measure (ℕ → ℕ → OverlapValue) :=
  ((gaussField N (overlapCovMatrix N ξ)).map (fun H : EnergySpace N => H + H_field N h)).bind
    (overlapArrayLaw N)

instance isProbabilityMeasure_mixedPSpinArrayLaw (N : ℕ) (ξ : ℝ → ℝ) (h : ℝ) :
    IsProbabilityMeasure (mixedPSpinArrayLaw N ξ h) := by
  unfold mixedPSpinArrayLaw
  have : IsProbabilityMeasure
      ((gaussField N (overlapCovMatrix N ξ)).map (fun H : EnergySpace N => H + H_field N h)) :=
    Measure.isProbabilityMeasure_map (measurable_add_const _).aemeasurable
  exact isProbabilityMeasure_bind (measurable_overlapArrayLaw N).aemeasurable
    (Eventually.of_forall fun _ => inferInstance)

/-- The annealed overlap array of a mixed `p`-spin model is jointly exchangeable. -/
theorem isJointlyExchangeable_mixedPSpinArrayLaw (N : ℕ) (ξ : ℝ → ℝ) (h : ℝ) :
    IsJointlyExchangeable (mixedPSpinArrayLaw N ξ h) :=
  isJointlyExchangeable_bind (measurable_overlapArrayLaw N)
    fun H => isJointlyExchangeable_overlapArrayLaw N H

/-- The annealed overlap array of a mixed `p`-spin model is carried by the Gram arrays. -/
theorem mixedPSpinArrayLaw_gramArray (N : ℕ) (hN : 0 < N) (ξ : ℝ → ℝ) (h : ℝ) :
    mixedPSpinArrayLaw N ξ h gramArray = 1 := by
  have : IsProbabilityMeasure
      ((gaussField N (overlapCovMatrix N ξ)).map (fun H : EnergySpace N => H + H_field N h)) :=
    Measure.isProbabilityMeasure_map (measurable_add_const _).aemeasurable
  unfold mixedPSpinArrayLaw
  rw [Measure.bind_apply isClosed_gramArray.measurableSet
    (measurable_overlapArrayLaw N).aemeasurable]
  simp [overlapArrayLaw_gramArray _ _ hN]

/-- The annealed overlap-array law as a `ProbabilityMeasure`. -/
def mixedPSpinArray (N : ℕ) (ξ : ℝ → ℝ) (h : ℝ) : ProbabilityMeasure (ℕ → ℕ → OverlapValue) :=
  ⟨mixedPSpinArrayLaw N ξ h, inferInstance⟩

@[simp] lemma mixedPSpinArray_toMeasure (N : ℕ) (ξ : ℝ → ℝ) (h : ℝ) :
    (mixedPSpinArray N ξ h : Measure (ℕ → ℕ → OverlapValue)) = mixedPSpinArrayLaw N ξ h := rfl

/-- The profile `ξ(r) + ∑ₛ wₛ² rˢ⁺¹` of the model perturbed by the monomial components with
weights `w`. -/
def perturbedProfile (ξ : ℝ → ℝ) {m : ℕ} (w : Fin (m + 1) → ℝ) (r : ℝ) : ℝ :=
  ξ r + ∑ s : Fin (m + 1), (w s) ^ 2 * r ^ ((s : ℕ) + 1)

/-! ### The rate vanishes -/

/-- Theorem 12.1.1's bound is nonnegative. -/
lemma energyFluctuationBound_nonneg (N : ℕ) {δ a b M₁ M₂ : ℝ} (hδ : 0 < δ) (hab : a ≤ b)
    (hM₂ : 0 ≤ M₂) : 0 ≤ energyFluctuationBound N δ a b M₁ M₂ := by
  unfold energyFluctuationBound
  have h1 : 0 ≤ b - a := sub_nonneg.2 hab
  have h2 : 0 ≤ 2 * δ * (2 * ((|a| + |b| + 2 * δ) * M₂) / (N : ℝ)) := by positivity
  have h3 : 0 ≤ 3 * (b - a) * (Real.sqrt (M₁ + (|a| + |b| + δ) ^ 2 * M₂) / (N : ℝ)) / δ := by
    positivity
  positivity

/-- **The finite-volume rate vanishes under the scaling hypotheses.** With uniform weights
`wₛ = c`, the rate of `exists_couplings_abs_ghirlandaGuerra_defect_mixedPSpin_monomials_le`,
normalised by the kernel scale `c² N`, is
`(m+1) · energyFluctuationBound N δ a b (N K + b²(m+1)c²N) (c²N) / c²`; it tends to `0` as soon as
`c → 0`, `δ → 0`, `(m+1)δ → 0`, `(m+1)c² → 0` and `(m+1)/(c²δ√N) → 0`. -/
theorem tendsto_perturbation_rate {a b K : ℝ} (ha : 0 < a) (hab : a < b) (hK : 0 ≤ K)
    (m : ℕ → ℕ) (c δ : ℕ → ℝ) (hc : ∀ N, 0 < N → 0 < c N) (hδ : ∀ N, 0 < N → 0 < δ N)
    (hc0 : Tendsto c atTop (𝓝 0)) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hmδ : Tendsto (fun N => ((m N : ℝ) + 1) * δ N) atTop (𝓝 0))
    (hmc : Tendsto (fun N => ((m N : ℝ) + 1) * (c N) ^ 2) atTop (𝓝 0))
    (hrate : Tendsto (fun N => ((m N : ℝ) + 1) / ((c N) ^ 2 * δ N * Real.sqrt N)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ((m N : ℝ) + 1) * energyFluctuationBound N (δ N) a b
        ((N : ℝ) * K + b ^ 2 * ∑ _q : Fin (m N + 1), (c N) ^ 2 * (N : ℝ)) ((c N) ^ 2 * (N : ℝ))
        / (c N) ^ 2) atTop (𝓝 0) := by
  have hb : 0 < b := lt_trans ha hab
  have hba : 0 < b - a := sub_pos.2 hab
  set C₁ : ℝ := Real.sqrt (2 * (b - a) * (|a| + |b|)) with hC₁
  set C₂ : ℝ := 4 * (|a| + |b| + 2) with hC₂
  set C₃ : ℝ := 3 * (b - a) * Real.sqrt (K + b ^ 2 + (|a| + |b| + 1) ^ 2) with hC₃
  -- the eventual bounds
  have hc1 : ∀ᶠ N in atTop, c N ≤ 1 := hc0.eventually (eventually_le_nhds one_pos)
  have hδ1 : ∀ᶠ N in atTop, δ N ≤ 1 := hδ0.eventually (eventually_le_nhds one_pos)
  have hmc1 : ∀ᶠ N in atTop, ((m N : ℝ) + 1) * (c N) ^ 2 ≤ 1 :=
    hmc.eventually (eventually_le_nhds one_pos)
  have hN1 : ∀ᶠ N : ℕ in atTop, 1 ≤ N := eventually_ge_atTop 1
  -- the target bound
  have hlim : Tendsto (fun N => (C₁ + C₃) * (((m N : ℝ) + 1) / ((c N) ^ 2 * δ N * Real.sqrt N))
      + C₂ * (((m N : ℝ) + 1) * δ N)) atTop (𝓝 0) := by
    simpa using (hrate.const_mul (C₁ + C₃)).add (hmδ.const_mul C₂)
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [hN1] with N hN
    have hE := energyFluctuationBound_nonneg N (hδ N hN) hab.le
      (M₁ := (N : ℝ) * K + b ^ 2 * ∑ _q : Fin (m N + 1), (c N) ^ 2 * (N : ℝ))
      (by positivity : (0 : ℝ) ≤ (c N) ^ 2 * N)
    exact div_nonneg (mul_nonneg (by positivity) hE) (sq_nonneg _)
  · filter_upwards [hc1, hδ1, hmc1, hN1] with N hcN hδN hmcN hN
    have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
    have hsqN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNR
    have hcN0 := hc N hN
    have hδN0 := hδ N hN
    have hm1 : (0 : ℝ) ≤ (m N : ℝ) + 1 := by positivity
    have hcδ : c N * δ N ≤ 1 := by nlinarith [mul_le_mul hcN hδN hδN0.le zero_le_one]
    -- the sum of constant weights
    have hsum : (∑ _q : Fin (m N + 1), (c N) ^ 2 * (N : ℝ))
        = ((m N : ℝ) + 1) * ((c N) ^ 2 * N) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    -- the three terms of the bound
    set M₂ : ℝ := (c N) ^ 2 * (N : ℝ) with hM₂
    set M₁ : ℝ := (N : ℝ) * K + b ^ 2 * ∑ _q : Fin (m N + 1), (c N) ^ 2 * (N : ℝ) with hM₁
    have hM₁le : M₁ + (|a| + |b| + δ N) ^ 2 * M₂ ≤ (N : ℝ) * (K + b ^ 2 + (|a| + |b| + 1) ^ 2) := by
      rw [hM₁, hM₂, hsum]
      have h1 : ((m N : ℝ) + 1) * ((c N) ^ 2 * N) ≤ N := by
        have := mul_le_mul_of_nonneg_right hmcN hNR.le
        linarith [show ((m N : ℝ) + 1) * (c N) ^ 2 * N = ((m N : ℝ) + 1) * ((c N) ^ 2 * N) by ring]
      have h2 : (|a| + |b| + δ N) ^ 2 * ((c N) ^ 2 * N) ≤ (|a| + |b| + 1) ^ 2 * N := by
        have hab1 : |a| + |b| + δ N ≤ |a| + |b| + 1 := by linarith
        have hc2 : (c N) ^ 2 ≤ 1 := by nlinarith [hcN0.le]
        have := mul_le_mul (pow_le_pow_left₀ (by positivity) hab1 2)
          (mul_le_mul_of_nonneg_right hc2 hNR.le) (by positivity) (by positivity)
        simpa [one_mul] using this
      nlinarith [h1, h2, sq_nonneg b, hNR.le]
    have ht1 : Real.sqrt ((b - a) * ((1 / (N : ℝ)) * (2 * ((|a| + |b|) * M₂) / (N : ℝ))))
        ≤ C₁ * (c N / Real.sqrt N) := by
      have heq : (b - a) * ((1 / (N : ℝ)) * (2 * ((|a| + |b|) * M₂) / (N : ℝ)))
          = (2 * (b - a) * (|a| + |b|)) * ((c N) ^ 2 / N) := by
        rw [hM₂]; field_simp
      rw [heq, Real.sqrt_mul (by positivity), Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hcN0.le,
        hC₁]
    have ht2 : 2 * δ N * (2 * ((|a| + |b| + 2 * δ N) * M₂) / (N : ℝ)) ≤ C₂ * (δ N * (c N) ^ 2) := by
      have heq : 2 * δ N * (2 * ((|a| + |b| + 2 * δ N) * M₂) / (N : ℝ))
          = 4 * (|a| + |b| + 2 * δ N) * (δ N * (c N) ^ 2) := by
        rw [hM₂]; field_simp; ring
      rw [heq, hC₂]
      have : |a| + |b| + 2 * δ N ≤ |a| + |b| + 2 := by linarith
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have ht3 : 3 * (b - a) * (Real.sqrt (M₁ + (|a| + |b| + δ N) ^ 2 * M₂) / (N : ℝ)) / δ N
        ≤ C₃ / (δ N * Real.sqrt N) := by
      have hsq : Real.sqrt (M₁ + (|a| + |b| + δ N) ^ 2 * M₂)
          ≤ Real.sqrt N * Real.sqrt (K + b ^ 2 + (|a| + |b| + 1) ^ 2) := by
        rw [← Real.sqrt_mul hNR.le]
        exact Real.sqrt_le_sqrt hM₁le
      have hRHS : C₃ / (δ N * Real.sqrt N) = C₃ * Real.sqrt N / ((N : ℝ) * δ N) := by
        rw [div_eq_div_iff (by positivity) (by positivity)]
        nth_rewrite 1 [← Real.mul_self_sqrt hNR.le]
        ring
      have hLHS : 3 * (b - a) * (Real.sqrt (M₁ + (|a| + |b| + δ N) ^ 2 * M₂) / (N : ℝ)) / δ N
          = 3 * (b - a) * Real.sqrt (M₁ + (|a| + |b| + δ N) ^ 2 * M₂) / ((N : ℝ) * δ N) := by
        ring
      rw [hLHS, hRHS]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      rw [hC₃]
      have := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 3 * (b - a))
      linarith [this, show 3 * (b - a) * (Real.sqrt N * Real.sqrt (K + b ^ 2 + (|a| + |b| + 1) ^ 2))
        = 3 * (b - a) * Real.sqrt (K + b ^ 2 + (|a| + |b| + 1) ^ 2) * Real.sqrt N by ring]
    -- assemble
    have hEle : energyFluctuationBound N (δ N) a b M₁ M₂
        ≤ C₁ * (c N / Real.sqrt N) + C₂ * (δ N * (c N) ^ 2) + C₃ / (δ N * Real.sqrt N) := by
      unfold energyFluctuationBound
      linarith [ht1, ht2, ht3]
    have hc2pos : 0 < (c N) ^ 2 := by positivity
    have hkey : ((m N : ℝ) + 1) * energyFluctuationBound N (δ N) a b M₁ M₂ / (c N) ^ 2
        ≤ ((m N : ℝ) + 1) * (C₁ * (c N / Real.sqrt N) + C₂ * (δ N * (c N) ^ 2)
            + C₃ / (δ N * Real.sqrt N)) / (c N) ^ 2 := by
      gcongr
    refine hkey.trans ?_
    -- (m+1)(C₁ c/√N + C₂ δ c² + C₃/(δ√N))/c² ≤ (C₁+C₃)(m+1)/(c²δ√N) + C₂ (m+1) δ
    have hC₁0 : 0 ≤ C₁ := Real.sqrt_nonneg _
    have hC₃0 : 0 ≤ C₃ := by rw [hC₃]; positivity
    have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
    have hterm1 : ((m N : ℝ) + 1) * (C₁ * (c N / Real.sqrt N)) / (c N) ^ 2
        ≤ C₁ * (((m N : ℝ) + 1) / ((c N) ^ 2 * δ N * Real.sqrt N)) := by
      rw [div_le_iff₀ hc2pos]
      have : ((m N : ℝ) + 1) * (C₁ * (c N / Real.sqrt N))
          = C₁ * (((m N : ℝ) + 1) / ((c N) ^ 2 * δ N * Real.sqrt N)) * (c N) ^ 2 * (c N * δ N) := by
        field_simp
      rw [this]
      have hpos : 0 ≤ C₁ * (((m N : ℝ) + 1) / ((c N) ^ 2 * δ N * Real.sqrt N)) * (c N) ^ 2 := by
        positivity
      nlinarith [mul_le_mul_of_nonneg_left hcδ hpos]
    have hterm2 : ((m N : ℝ) + 1) * (C₂ * (δ N * (c N) ^ 2)) / (c N) ^ 2
        = C₂ * (((m N : ℝ) + 1) * δ N) := by
      field_simp
    have hterm3 : ((m N : ℝ) + 1) * (C₃ / (δ N * Real.sqrt N)) / (c N) ^ 2
        = C₃ * (((m N : ℝ) + 1) / ((c N) ^ 2 * δ N * Real.sqrt N)) := by
      field_simp
    have hsplit : ((m N : ℝ) + 1) * (C₁ * (c N / Real.sqrt N) + C₂ * (δ N * (c N) ^ 2)
          + C₃ / (δ N * Real.sqrt N)) / (c N) ^ 2
        = ((m N : ℝ) + 1) * (C₁ * (c N / Real.sqrt N)) / (c N) ^ 2
          + ((m N : ℝ) + 1) * (C₂ * (δ N * (c N) ^ 2)) / (c N) ^ 2
          + ((m N : ℝ) + 1) * (C₃ / (δ N * Real.sqrt N)) / (c N) ^ 2 := by
      ring
    rw [hsplit, hterm2, hterm3]
    linarith [hterm1]

/-! ### The capstone: Ghirlanda–Guerra identities for a limit of perturbed mixed `p`-spin models -/

set_option maxHeartbeats 1600000 in
-- The finite-volume bound and the array laws carry many nested integrals.
/-- **The Ghirlanda–Guerra identities hold in the thermodynamic limit of every mixed `p`-spin
model, after a vanishing perturbation** (Talagrand, Vol. II, Theorem 12.2.2 → §15.3).

Let `ξ` be a mixed `p`-spin profile (nonnegative coefficients) and `h` an external field. Fix any
scaling `(m_N, c_N, δ_N)` with `m_N → ∞` components, perturbation strength `c_N → 0`, and
`(m_N+1)δ_N → 0`, `(m_N+1)c_N² → 0`, `(m_N+1)/(c_N² δ_N √N) → 0` (for instance
`c_N = N^{-1/16}`, `δ_N = N^{-1/4}`, `m_N = ⌊N^{1/16}⌋`). Then there are couplings
`β_N ∈ [a,b]^{m_N+1}` such that, along a subsequence, the annealed overlap-array laws of the
perturbed models — the mixed `p`-spin models with profiles `ξ(r) + ∑ₛ (β_{N,s} c_N)² rˢ⁺¹`, a
perturbation of total variance per site `≤ b²(m_N+1)c_N² → 0` — converge in distribution to a law
that is jointly exchangeable, carried by the Gram arrays, and **satisfies the Ghirlanda–Guerra
identities** at every continuous test function. -/
theorem exists_subseq_tendsto_satisfiesGhirlandaGuerra_mixedPSpin {P : Polynomial ℝ}
    (hP : ∀ k, 0 ≤ P.coeff k) (h : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
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
        SatisfiesGhirlandaGuerra (μ : Measure (ℕ → ℕ → OverlapValue)) := by
  classical
  -- couplings at every volume `N ≥ 1` (any couplings in the window at `N = 0`)
  have hex : ∀ N : ℕ, ∃ β : Fin (m N + 1) → ℝ, (∀ s, β s ∈ Set.Icc a b) ∧ (N ≠ 0 →
      ∀ (s : Fin (m N + 1)) {k : ℕ}, 0 < k → ∀ g : C(Fin k → Fin k → OverlapValue, ℝ),
        |ggDefect (mixedPSpinArrayLaw N
            (perturbedProfile (fun r => P.eval r) fun p => β p * c N) h)
            k (overlapMonomialCM ((s : ℕ) + 1)) g|
          ≤ (‖g‖ * ((N : ℝ) *
                ((∑ p : Fin (m N + 1), energyFluctuationBound N (δ N) a b
                    ((N : ℝ) * P.eval 1 + b ^ 2 * ∑ q : Fin (m N + 1), (c N) ^ 2 * (N : ℝ))
                    ((c N) ^ 2 * (N : ℝ))) / (b - a))))
              / ((k : ℝ) * |β s * ((c N) ^ 2 * (N : ℝ))|)) := by
    intro N
    by_cases hN : N = 0
    · exact ⟨fun _ => a, fun _ => ⟨le_rfl, hab.le⟩, fun h0 => (h0 hN).elim⟩
    · obtain ⟨β, hβ, hb⟩ := exists_couplings_abs_ghirlandaGuerra_defect_mixedPSpin_monomials_le
        N hN hP h (w := fun _ => c N) (fun _ => (hc N (Nat.pos_of_ne_zero hN)).ne')
        (hδ N (Nat.pos_of_ne_zero hN)) hab ha
      exact ⟨β, hβ, fun _ s k hk g => hb s hk g⟩
  choose β hβmem hβbound using hex
  refine ⟨β, hβmem, ?_⟩
  -- the sequence of perturbed array laws, indexed so that the volume is `k + 1 ≥ 1`
  set μs : ℕ → ProbabilityMeasure (ℕ → ℕ → OverlapValue) := fun k =>
    mixedPSpinArray (k + 1)
      (perturbedProfile (fun r => P.eval r) fun s => β (k + 1) s * c (k + 1)) h with hμs
  -- the defects vanish
  have hdef : ∀ n, 0 < n → ∀ (p : ℕ) (g : C(Fin n → Fin n → OverlapValue, ℝ)),
      Tendsto (fun k => ggDefect (μs k : Measure (ℕ → ℕ → OverlapValue)) n
        (overlapMonomialCM p) g) atTop (𝓝 0) := by
    intro n hn p g
    rcases p with _ | q
    · refine tendsto_const_nhds.congr fun k => ?_
      exact (ggDefect_monomial_zero _ n hn g).symm
    · have hev : ∀ᶠ k in atTop, q < m (k + 1) + 1 :=
        ((hm.comp (tendsto_add_atTop_nat 1)).eventually_gt_atTop q).mono fun k hk =>
          Nat.lt_succ_of_lt hk
      have hrate' := tendsto_perturbation_rate ha hab
        (Polynomial.eval_one_nonneg_of_nonneg_coeff hP) m c δ hc hδ hc0 hδ0 hmδ hmc hrate
      have hlim' : Tendsto (fun k : ℕ => (‖g‖ / ((b - a) * n * a)) *
          (((m (k + 1) : ℝ) + 1) * energyFluctuationBound (k + 1) (δ (k + 1)) a b
            (((k + 1 : ℕ) : ℝ) * P.eval 1
              + b ^ 2 * ∑ _q : Fin (m (k + 1) + 1), (c (k + 1)) ^ 2 * ((k + 1 : ℕ) : ℝ))
            ((c (k + 1)) ^ 2 * ((k + 1 : ℕ) : ℝ)) / (c (k + 1)) ^ 2)) atTop (𝓝 0) := by
        have := (hrate'.comp (tendsto_add_atTop_nat 1)).const_mul (‖g‖ / ((b - a) * n * a))
        rw [mul_zero] at this
        exact this
      refine squeeze_zero_norm' (hev.mono fun k hk => ?_) hlim'
      set N := k + 1 with hNdef
      have hN0 : N ≠ 0 := Nat.succ_ne_zero k
      have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos k)
      set E := energyFluctuationBound N (δ N) a b
        ((N : ℝ) * P.eval 1 + b ^ 2 * ∑ _q : Fin (m N + 1), (c N) ^ 2 * (N : ℝ))
        ((c N) ^ 2 * (N : ℝ)) with hE
      have hb := hβbound N hN0 ⟨q, hk⟩ hn g
      have hsum : (∑ _p : Fin (m N + 1), E) = ((m N : ℝ) + 1) * E := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
      have hβs : a ≤ β N ⟨q, hk⟩ := (hβmem N ⟨q, hk⟩).1
      have hβpos : 0 < β N ⟨q, hk⟩ := lt_of_lt_of_le ha hβs
      have hE0 : 0 ≤ E := energyFluctuationBound_nonneg N (hδ N (Nat.succ_pos k)) hab.le
        (by positivity)
      have hba : 0 < b - a := sub_pos.2 hab
      have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      have hcN := hc N (Nat.succ_pos k)
      rw [Real.norm_eq_abs]
      refine hb.trans ?_
      rw [hsum, abs_of_pos (by positivity : 0 < β N ⟨q, hk⟩ * ((c N) ^ 2 * (N : ℝ)))]
      have hnum : 0 ≤ ‖g‖ * ((N : ℝ) * (((m N : ℝ) + 1) * E / (b - a))) :=
        mul_nonneg (norm_nonneg _)
          (mul_nonneg hNR.le (div_nonneg (mul_nonneg (by positivity) hE0) hba.le))
      calc (‖g‖ * ((N : ℝ) * (((m N : ℝ) + 1) * E / (b - a))))
            / ((n : ℝ) * (β N ⟨q, hk⟩ * ((c N) ^ 2 * (N : ℝ))))
          ≤ (‖g‖ * ((N : ℝ) * (((m N : ℝ) + 1) * E / (b - a))))
            / ((n : ℝ) * (a * ((c N) ^ 2 * (N : ℝ)))) :=
            div_le_div_of_nonneg_left hnum (by positivity) (by gcongr)
        _ = (‖g‖ / ((b - a) * n * a)) * (((m N : ℝ) + 1) * E / (c N) ^ 2) := by
            field_simp
  obtain ⟨μ, φ, hφ, hlim, hexμ, hgram, hgg⟩ := exists_subseq_tendsto_satisfiesGhirlandaGuerra μs
    (fun k => isJointlyExchangeable_mixedPSpinArrayLaw _ _ _)
    (fun k => mixedPSpinArrayLaw_gramArray _ (Nat.succ_pos k) _ _) hdef
  exact ⟨μ, φ, hφ, hlim, hexμ, hgram, hgg⟩

/-! ### An explicit admissible scaling -/

/-- `(⌊Nᵅ⌋ + 1) N^{-β} → 0` whenever `0 < α < β`. -/
theorem tendsto_floor_rpow_mul_rpow_neg {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    Tendsto (fun N : ℕ => ((⌊(N : ℝ) ^ α⌋₊ : ℝ) + 1) * (N : ℝ) ^ (-β)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(β - α)) + (N : ℝ) ^ (-β)) atTop (𝓝 0) := by
    have h1 := (tendsto_rpow_neg_atTop (sub_pos.2 hαβ)).comp tendsto_natCast_atTop_atTop
    have h2 := (tendsto_rpow_neg_atTop (hα.trans hαβ)).comp tendsto_natCast_atTop_atTop
    simpa using h1.add h2
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards with N
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hx : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
    have hfl : (⌊(N : ℝ) ^ α⌋₊ : ℝ) ≤ (N : ℝ) ^ α := Nat.floor_le (Real.rpow_nonneg hx.le _)
    have hβ0 : 0 ≤ (N : ℝ) ^ (-β) := Real.rpow_nonneg hx.le _
    calc ((⌊(N : ℝ) ^ α⌋₊ : ℝ) + 1) * (N : ℝ) ^ (-β)
        ≤ ((N : ℝ) ^ α + 1) * (N : ℝ) ^ (-β) := by gcongr
      _ = (N : ℝ) ^ (-(β - α)) + (N : ℝ) ^ (-β) := by
          rw [add_mul, one_mul, ← Real.rpow_add hx]
          congr 2
          ring

/-- **The explicit scaling `c_N = N^{-1/16}`, `δ_N = N^{-1/4}`, `m_N = ⌊N^{1/16}⌋` is
admissible** for `exists_subseq_tendsto_satisfiesGhirlandaGuerra_mixedPSpin`. -/
theorem explicitScaling_tendsto :
    Tendsto (fun N : ℕ => ⌊(N : ℝ) ^ ((1 : ℝ) / 16)⌋₊) atTop atTop ∧
    Tendsto (fun N : ℕ => (N : ℝ) ^ (-((1 : ℝ) / 16))) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => (N : ℝ) ^ (-((1 : ℝ) / 4))) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => ((⌊(N : ℝ) ^ ((1 : ℝ) / 16)⌋₊ : ℝ) + 1) * (N : ℝ) ^ (-((1 : ℝ) / 4)))
      atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => ((⌊(N : ℝ) ^ ((1 : ℝ) / 16)⌋₊ : ℝ) + 1)
      * ((N : ℝ) ^ (-((1 : ℝ) / 16))) ^ 2) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => ((⌊(N : ℝ) ^ ((1 : ℝ) / 16)⌋₊ : ℝ) + 1)
      / (((N : ℝ) ^ (-((1 : ℝ) / 16))) ^ 2 * (N : ℝ) ^ (-((1 : ℝ) / 4)) * Real.sqrt N))
      atTop (𝓝 0) := by
  have hsq : ∀ N : ℕ, ((N : ℝ) ^ (-((1 : ℝ) / 16))) ^ 2 = (N : ℝ) ^ (-((1 : ℝ) / 8)) := by
    intro N
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact tendsto_nat_floor_atTop.comp
      ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop)
  · exact (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  · exact (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  · exact tendsto_floor_rpow_mul_rpow_neg (by norm_num) (by norm_num)
  · simp_rw [hsq]
    exact tendsto_floor_rpow_mul_rpow_neg (by norm_num) (by norm_num)
  · have hden : ∀ N : ℕ, ((N : ℝ) ^ (-((1 : ℝ) / 16))) ^ 2 * (N : ℝ) ^ (-((1 : ℝ) / 4))
        * Real.sqrt N = (N : ℝ) ^ ((1 : ℝ) / 8) := by
      intro N
      rw [hsq, Real.sqrt_eq_rpow, ← Real.rpow_add' (Nat.cast_nonneg N) (by norm_num),
        ← Real.rpow_add' (Nat.cast_nonneg N) (by norm_num)]
      norm_num
    simp_rw [hden, div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg _)]
    exact tendsto_floor_rpow_mul_rpow_neg (by norm_num) (by norm_num)

/-- **The Ghirlanda–Guerra identities in the thermodynamic limit of every mixed `p`-spin model,
with the explicit scaling** `c_N = N^{-1/16}`, `δ_N = N^{-1/4}`, `m_N = ⌊N^{1/16}⌋`: there are
couplings `β_N ∈ [a,b]^{m_N+1}` such that along a subsequence the perturbed models — mixed `p`-spin
models with profile `ξ(r) + N^{-1/8} ∑_{s ≤ m_N} β_{N,s}² rˢ⁺¹`, a perturbation of variance per
site `O(N^{-1/16}) → 0` — converge in distribution to a jointly exchangeable Gram law satisfying the
Ghirlanda–Guerra identities. Fully explicit and unconditional. -/
theorem exists_subseq_tendsto_satisfiesGhirlandaGuerra_mixedPSpin_explicit {P : Polynomial ℝ}
    (hP : ∀ k, 0 ≤ P.coeff k) (h : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ β : ∀ N : ℕ, Fin (⌊(N : ℝ) ^ ((1 : ℝ) / 16)⌋₊ + 1) → ℝ, (∀ N s, β N s ∈ Set.Icc a b) ∧
      ∃ (μ : ProbabilityMeasure (ℕ → ℕ → OverlapValue)) (φ : ℕ → ℕ), StrictMono φ ∧
        Tendsto (fun k => mixedPSpinArray (φ k + 1)
          (perturbedProfile (fun r => P.eval r)
            fun s => β (φ k + 1) s * ((φ k + 1 : ℕ) : ℝ) ^ (-((1 : ℝ) / 16))) h)
          atTop (𝓝 μ) ∧
        IsJointlyExchangeable (μ : Measure (ℕ → ℕ → OverlapValue)) ∧
        (μ : Measure (ℕ → ℕ → OverlapValue)) gramArray = 1 ∧
        SatisfiesGhirlandaGuerra (μ : Measure (ℕ → ℕ → OverlapValue)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := explicitScaling_tendsto
  exact exists_subseq_tendsto_satisfiesGhirlandaGuerra_mixedPSpin hP h ha hab
    (fun N => ⌊(N : ℝ) ^ ((1 : ℝ) / 16)⌋₊) (fun N => (N : ℝ) ^ (-((1 : ℝ) / 16)))
    (fun N => (N : ℝ) ^ (-((1 : ℝ) / 4)))
    (fun N hN => Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _)
    (fun N hN => Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _) h1 h2 h3 h4 h5 h6

end

end SpinGlass
