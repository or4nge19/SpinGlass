/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.PointProcess.PoissonDirichlet
import Common.Mathlib.Probability.PointProcess.Mecke

/-!
# The fundamental identities of the Poisson–Dirichlet process (Theorem 13.1.6)

Talagrand, *Mean Field Models for Spin Glasses*, Vol. II, Theorem 13.1.6: for the Poisson–Dirichlet
weights `v_α = u_α / ∑ u_γ` and independent marks `(U_α, V_α, W_α)`,

`𝔼 (∑_α v_α U_α) / (∑_α v_α V_α) = 𝔼 [U V^{m-1}] / 𝔼 V^m`  (13.13)

`𝔼 (∑_α v_α² U_α W_α) / (∑_α v_α V_α)² = (1 - m) 𝔼 [U W V^{m-2}] / 𝔼 V^m`  (13.14)

and in particular `𝔼 ∑_α v_α² = 1 - m` (13.17). Talagrand derives them by differentiating
Theorem 13.1.5 and calls the justification "tedious"; here they are direct consequences of the
**Mecke formula** (`lintegral_lintegral_poissonPointProcess`): the sum over the points becomes an
integral against the intensity `μ_m ⊗ η`, the added point contributes `u V(g)` to the
denominator, `(S + a)^{-1} = ∫₀^∞ e^{-s(S+a)} ds` turns the denominator into the Laplace
transform of `S`, and the `u`- and `s`-integrals are Gamma integrals, with `m c_m = Γ(1 - m)`
(`mul_stableConst_eq_Gamma`).

## Main statements

- `ENNReal.inv_eq_lintegral_negExp`, `ENNReal.inv_mul_inv_eq_lintegral_mul_negExp`: the Laplace
  representations of `x⁻¹` and `x⁻²`, valid for every `x : ℝ≥0∞`.
- `ProbabilityTheory.lintegral_pdSum_mul_inv_pdSum`: **(13.13)** in `ℝ≥0∞`.
- `ProbabilityTheory.lintegral_pdSumSq_mul_inv_pdSum_sq`: **(13.14)** in `ℝ≥0∞`.
- `ProbabilityTheory.lintegral_pdSumSq_mul_inv_pdSum_one_sq`: **(13.17)**, `𝔼 ∑ v_α² = 1 - m`.
-/

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

noncomputable section

/-! ### Laplace representations of `x⁻¹` and `x⁻²` in `ℝ≥0∞` -/

namespace ENNReal

open ProbabilityTheory

/-- `x⁻¹ = ∫₀^∞ e^{-s x} ds` for every `x : ℝ≥0∞` (both sides are `∞` at `x = 0` and `0` at
`x = ∞`). -/
theorem inv_eq_lintegral_negExp (x : ℝ≥0∞) :
    x⁻¹ = ∫⁻ s in Ioi 0, ENNReal.ofReal (negExp (ENNReal.ofReal s * x)) := by
  rcases eq_or_ne x ∞ with rfl | hx
  · rw [ENNReal.inv_top]
    symm
    refine (setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_).trans lintegral_zero
    rw [mem_Ioi] at hs
    rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hs).ne', negExp_top, ENNReal.ofReal_zero]
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [ENNReal.inv_zero]
    symm
    refine (setLIntegral_congr_fun (g := fun _ => (1 : ℝ≥0∞)) measurableSet_Ioi
      fun s _ => ?_).trans ?_
    · rw [mul_zero, negExp_zero, ENNReal.ofReal_one]
    · rw [setLIntegral_const, one_mul, Real.volume_Ioi]
  obtain ⟨y, hy, rfl⟩ : ∃ y : ℝ, 0 < y ∧ x = ENNReal.ofReal y :=
    ⟨x.toReal, ENNReal.toReal_pos hx0 hx, (ENNReal.ofReal_toReal hx).symm⟩
  have hint : IntegrableOn (fun s : ℝ => Real.exp (-(y * s))) (Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => Real.exp (-x)) 0 hy).2
      (by simpa using integrableOn_exp_neg_Ioi 0)
    exact this
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] fun s : ℝ => Real.exp (-(y * s)) :=
    Filter.Eventually.of_forall fun s => (Real.exp_pos _).le
  have hval : ∫ s in Ioi (0 : ℝ), Real.exp (-(y * s)) = y⁻¹ := by
    have := integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x)) 0 hy
    simp only [mul_zero, smul_eq_mul] at this
    rw [this, integral_exp_neg_Ioi_zero, mul_one]
  calc (ENNReal.ofReal y)⁻¹ = ENNReal.ofReal y⁻¹ := (ENNReal.ofReal_inv_of_pos hy).symm
    _ = ENNReal.ofReal (∫ s in Ioi (0 : ℝ), Real.exp (-(y * s))) := by rw [hval]
    _ = ∫⁻ s in Ioi 0, ENNReal.ofReal (Real.exp (-(y * s))) :=
        ofReal_integral_eq_lintegral_ofReal hint hnn
    _ = ∫⁻ s in Ioi 0, ENNReal.ofReal (negExp (ENNReal.ofReal s * ENNReal.ofReal y)) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
        rw [mem_Ioi] at hs
        rw [← ENNReal.ofReal_mul hs.le, negExp_ofReal (by positivity), mul_comm]

/-- `x⁻² = ∫₀^∞ s e^{-s x} ds` for every `x : ℝ≥0∞`. -/
theorem inv_mul_inv_eq_lintegral_mul_negExp (x : ℝ≥0∞) :
    x⁻¹ * x⁻¹
      = ∫⁻ s in Ioi 0, ENNReal.ofReal s * ENNReal.ofReal (negExp (ENNReal.ofReal s * x)) := by
  rcases eq_or_ne x ∞ with rfl | hx
  · rw [ENNReal.inv_top, mul_zero]
    symm
    refine (setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_).trans lintegral_zero
    rw [mem_Ioi] at hs
    rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hs).ne', negExp_top, ENNReal.ofReal_zero, mul_zero]
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [ENNReal.inv_zero, ENNReal.top_mul_top]
    symm
    refine (setLIntegral_congr_fun (g := fun s => ENNReal.ofReal s) measurableSet_Ioi
      fun s _ => ?_).trans ?_
    · rw [mul_zero, negExp_zero, ENNReal.ofReal_one, mul_one]
    · refine eq_top_iff.2 ?_
      calc (∞ : ℝ≥0∞) = ∫⁻ _s in Ioi (1 : ℝ), (1 : ℝ≥0∞) := by
            rw [setLIntegral_const, one_mul, Real.volume_Ioi]
        _ ≤ ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal s := by
            refine setLIntegral_mono ENNReal.measurable_ofReal fun s hs => ?_
            rw [mem_Ioi] at hs
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal hs.le
        _ ≤ ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal s :=
            lintegral_mono_set (Set.Ioi_subset_Ioi zero_le_one)
  obtain ⟨y, hy, rfl⟩ : ∃ y : ℝ, 0 < y ∧ x = ENNReal.ofReal y :=
    ⟨x.toReal, ENNReal.toReal_pos hx0 hx, (ENNReal.ofReal_toReal hx).symm⟩
  have hΓ : Real.Gamma 2 = 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one one_ne_zero, Real.Gamma_one, one_mul]
  have h := lintegral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := y) two_pos hy
  rw [hΓ, mul_one, one_div, Real.rpow_two, sq, ENNReal.ofReal_mul (inv_nonneg.2 hy.le),
    ENNReal.ofReal_inv_of_pos hy] at h
  rw [← h]
  refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  rw [mem_Ioi] at hs
  have hneg : negExp (ENNReal.ofReal s * ENNReal.ofReal y) = Real.exp (-(s * y)) := by
    rw [← ENNReal.ofReal_mul hs.le, negExp_ofReal (by positivity)]
  rw [hneg, ← ENNReal.ofReal_mul hs.le, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
    mul_comm y s]

end ENNReal

namespace ProbabilityTheory

open ENNReal

variable {M : Type*} [MeasurableSpace M] [Nonempty M]

/-! ### Adding a point to the counting measure -/

omit [Nonempty M] in
lemma pdSum_add_dirac {V : M → ℝ≥0∞} (hV : Measurable V) (N : Measure (ℝ × M)) (p : ℝ × M) :
    pdSum V (N + Measure.dirac p) = pdSum V N + ENNReal.ofReal p.1 * V p.2 := by
  rw [pdSum, pdSum, lintegral_add_measure, lintegral_dirac' _ (measurable_ofReal_mul hV)]

/-- **The Mecke formula for the marked Poisson–Dirichlet process**. -/
theorem lintegral_lintegral_pdProcess (m : ℝ) (η : Measure M) [IsFiniteMeasure η]
    {f : (ℝ × M) × Measure (ℝ × M) → ℝ≥0∞} (hf : Measurable f)
    (hF : Measurable fun N : Measure (ℝ × M) => ∫⁻ p, f (p, N) ∂N) :
    ∫⁻ N, ∫⁻ p, f (p, N) ∂N ∂pdProcess m η
      = ∫⁻ N, ∫⁻ p, f (p, N + Measure.dirac p) ∂pdIntensity m η ∂pdProcess m η := by
  rw [← sum_pdSeq m η]
  exact lintegral_lintegral_poissonPointProcessSum (pdSeq m η) hf hF

/-! ### The Laplace transform of `(S + a)⁻¹` and `(S + a)⁻²` -/

/-- `𝔼 (S_V + a)⁻¹ = ∫₀^∞ e^{-s a} e^{-s^m c_m κ} ds`. -/
theorem lintegral_inv_add_pdSum {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {V : M → ℝ≥0∞} (hV : Measurable V)
    (hκ : ∫⁻ g, V g ^ m ∂η ≠ ∞) (a : ℝ≥0∞) :
    ∫⁻ N, (pdSum V N + a)⁻¹ ∂pdProcess m η
      = ∫⁻ s in Ioi 0, ENNReal.ofReal (negExp (ENNReal.ofReal s * a))
          * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m
              * (∫⁻ g, V g ^ m ∂η).toReal))) := by
  have hS := measurable_pdSum (v := V) hV
  simp_rw [ENNReal.inv_eq_lintegral_negExp]
  have hjoint : Measurable fun q : Measure (ℝ × M) × ℝ =>
      ENNReal.ofReal (negExp (ENNReal.ofReal q.2 * (pdSum V q.1 + a))) :=
    ENNReal.measurable_ofReal.comp (measurable_negExp.comp
      ((ENNReal.measurable_ofReal.comp measurable_snd).mul
        ((hS.comp measurable_fst).add measurable_const)))
  rw [lintegral_lintegral_swap (f := fun N s =>
    ENNReal.ofReal (negExp (ENNReal.ofReal s * (pdSum V N + a)))) hjoint.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  rw [mem_Ioi] at hs
  have hpt : ∀ N, ENNReal.ofReal (negExp (ENNReal.ofReal s * (pdSum V N + a)))
      = ENNReal.ofReal (negExp (ENNReal.ofReal s * a))
        * ENNReal.ofReal (negExp (ENNReal.ofReal s * pdSum V N)) := by
    intro N
    rw [mul_add, negExp_add, ENNReal.ofReal_mul (negExp_nonneg _), mul_comm]
  simp_rw [hpt]
  have hint : Integrable (fun N => negExp (ENNReal.ofReal s * pdSum V N)) (pdProcess m η) :=
    Integrable.mono' (integrable_const 1)
      (measurable_negExp.comp (measurable_const.mul hS)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun N => by
        rw [Real.norm_eq_abs, abs_of_nonneg (negExp_nonneg _)]; exact negExp_le_one _)
  have hmeas : Measurable fun N : Measure (ℝ × M) =>
      ENNReal.ofReal (negExp (ENNReal.ofReal s * pdSum V N)) :=
    ENNReal.measurable_ofReal.comp (measurable_negExp.comp (measurable_const.mul hS))
  rw [lintegral_const_mul _ hmeas, ← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun N => negExp_nonneg _),
    integral_negExp_pdSum_eq_exp hm0 hm1 η hV hκ hs.le]

/-- `𝔼 (S_V + a)⁻² = ∫₀^∞ s e^{-s a} e^{-s^m c_m κ} ds`. -/
theorem lintegral_inv_mul_inv_add_pdSum {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {V : M → ℝ≥0∞} (hV : Measurable V)
    (hκ : ∫⁻ g, V g ^ m ∂η ≠ ∞) (a : ℝ≥0∞) :
    ∫⁻ N, (pdSum V N + a)⁻¹ * (pdSum V N + a)⁻¹ ∂pdProcess m η
      = ∫⁻ s in Ioi 0, ENNReal.ofReal s * ENNReal.ofReal (negExp (ENNReal.ofReal s * a))
          * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m
              * (∫⁻ g, V g ^ m ∂η).toReal))) := by
  have hS := measurable_pdSum (v := V) hV
  simp_rw [ENNReal.inv_mul_inv_eq_lintegral_mul_negExp]
  have hjoint : Measurable fun q : Measure (ℝ × M) × ℝ =>
      ENNReal.ofReal q.2 * ENNReal.ofReal (negExp (ENNReal.ofReal q.2 * (pdSum V q.1 + a))) :=
    (ENNReal.measurable_ofReal.comp measurable_snd).mul
      (ENNReal.measurable_ofReal.comp (measurable_negExp.comp
        ((ENNReal.measurable_ofReal.comp measurable_snd).mul
          ((hS.comp measurable_fst).add measurable_const))))
  rw [lintegral_lintegral_swap (f := fun N s =>
    ENNReal.ofReal s * ENNReal.ofReal (negExp (ENNReal.ofReal s * (pdSum V N + a))))
    hjoint.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  rw [mem_Ioi] at hs
  have hpt : ∀ N, ENNReal.ofReal s * ENNReal.ofReal (negExp (ENNReal.ofReal s * (pdSum V N + a)))
      = (ENNReal.ofReal s * ENNReal.ofReal (negExp (ENNReal.ofReal s * a)))
        * ENNReal.ofReal (negExp (ENNReal.ofReal s * pdSum V N)) := by
    intro N
    rw [mul_add, negExp_add, ENNReal.ofReal_mul (negExp_nonneg _)]
    ring
  simp_rw [hpt]
  have hint : Integrable (fun N => negExp (ENNReal.ofReal s * pdSum V N)) (pdProcess m η) :=
    Integrable.mono' (integrable_const 1)
      (measurable_negExp.comp (measurable_const.mul hS)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun N => by
        rw [Real.norm_eq_abs, abs_of_nonneg (negExp_nonneg _)]; exact negExp_le_one _)
  have hmeas : Measurable fun N : Measure (ℝ × M) =>
      ENNReal.ofReal (negExp (ENNReal.ofReal s * pdSum V N)) :=
    ENNReal.measurable_ofReal.comp (measurable_negExp.comp (measurable_const.mul hS))
  rw [lintegral_const_mul _ hmeas, ← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun N => negExp_nonneg _),
    integral_negExp_pdSum_eq_exp hm0 hm1 η hV hκ hs.le]

/-! ### The Gamma integrals in the weight variable -/

omit [Nonempty M] in
/-- `∫₀^∞ u^{-m-1} · u · e^{-s u v} du = (s v)^{m-1} Γ(1 - m)`. -/
lemma lintegral_stableDensity_mul_negExp {m : ℝ} (hm1 : m < 1) {s v : ℝ} (hs : 0 < s)
    (hv : 0 < v) :
    ∫⁻ u in Ioi 0, stableDensity m u
        * (ENNReal.ofReal u * ENNReal.ofReal (negExp (ENNReal.ofReal s
          * (ENNReal.ofReal u * ENNReal.ofReal v))))
      = ENNReal.ofReal ((s * v) ^ (m - 1) * Real.Gamma (1 - m)) := by
  have h := lintegral_rpow_mul_exp_neg_mul_Ioi (a := 1 - m) (r := s * v) (by linarith)
    (mul_pos hs hv)
  have hpow : (1 / (s * v)) ^ (1 - m) = (s * v) ^ (m - 1) := by
    rw [one_div, Real.inv_rpow (mul_pos hs hv).le, ← Real.rpow_neg (mul_pos hs hv).le, neg_sub]
  rw [hpow] at h
  rw [← h]
  refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  rw [mem_Ioi] at hu
  have hneg : negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ENNReal.ofReal v))
      = Real.exp (-(s * (u * v))) := by
    rw [← ENNReal.ofReal_mul hu.le, ← ENNReal.ofReal_mul hs.le, negExp_ofReal (by positivity)]
  rw [hneg, stableDensity, ← ENNReal.ofReal_mul hu.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hu.le _)]
  congr 1
  have : u ^ (1 - m - 1) = u ^ (-m - 1) * u := by
    rw [show (1 : ℝ) - m - 1 = (-m - 1) + 1 by ring, Real.rpow_add hu, Real.rpow_one]
  rw [this]
  ring_nf

omit [Nonempty M] in
/-- `∫₀^∞ u^{-m-1} · u² · e^{-s u v} du = (s v)^{m-2} Γ(2 - m)`. -/
lemma lintegral_stableDensity_mul_sq_negExp {m : ℝ} (hm1 : m < 1) {s v : ℝ} (hs : 0 < s)
    (hv : 0 < v) :
    ∫⁻ u in Ioi 0, stableDensity m u
        * (ENNReal.ofReal u * ENNReal.ofReal u * ENNReal.ofReal (negExp (ENNReal.ofReal s
          * (ENNReal.ofReal u * ENNReal.ofReal v))))
      = ENNReal.ofReal ((s * v) ^ (m - 2) * Real.Gamma (2 - m)) := by
  have h := lintegral_rpow_mul_exp_neg_mul_Ioi (a := 2 - m) (r := s * v) (by linarith)
    (mul_pos hs hv)
  have hpow : (1 / (s * v)) ^ (2 - m) = (s * v) ^ (m - 2) := by
    rw [one_div, Real.inv_rpow (mul_pos hs hv).le, ← Real.rpow_neg (mul_pos hs hv).le, neg_sub]
  rw [hpow] at h
  rw [← h]
  refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  rw [mem_Ioi] at hu
  have hneg : negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ENNReal.ofReal v))
      = Real.exp (-(s * (u * v))) := by
    rw [← ENNReal.ofReal_mul hu.le, ← ENNReal.ofReal_mul hs.le, negExp_ofReal (by positivity)]
  rw [hneg, stableDensity, ← ENNReal.ofReal_mul hu.le, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hu.le _)]
  congr 1
  have : u ^ (2 - m - 1) = u ^ (-m - 1) * u * u := by
    rw [show (2 : ℝ) - m - 1 = (-m - 1) + 1 + 1 by ring, Real.rpow_add hu, Real.rpow_add hu,
      Real.rpow_one]
  rw [this]
  ring_nf

/-! ### Identity (13.13) -/

omit [Nonempty M] in
lemma lintegral_rpow_pos_of_ae_pos {m : ℝ} (hm0 : 0 < m) (η : Measure M) [IsProbabilityMeasure η]
    {V : M → ℝ≥0∞} (hV : Measurable V) (hVpos : ∀ᵐ g ∂η, 0 < V g) :
    0 < ∫⁻ g, V g ^ m ∂η := by
  rw [lintegral_pos_iff_support (hV.pow_const m)]
  have hsub : {g | 0 < V g} ⊆ Function.support fun g => V g ^ m := fun g hg =>
    (ENNReal.rpow_pos_of_nonneg hg hm0.le).ne'
  have h0 : η {g | 0 < V g}ᶜ = 0 := by
    rw [Set.compl_ofPred]
    exact ae_iff.1 hVpos
  have hle := measure_univ_le_add_compl (μ := η) {g | 0 < V g}
  rw [h0, add_zero, measure_univ] at hle
  exact lt_of_lt_of_le (lt_of_lt_of_le one_pos hle) (measure_mono hsub)

/-- The mark-wise computation behind (13.13): for a weight `x ∈ (0, ∞]`,
`∫₀^∞ u^{-m-1} u 𝔼 (S_V + u x)⁻¹ du = x^{m-1} / κ`. -/
lemma lintegral_stableDensity_inv_add_pdSum {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1)
    (η : Measure M) [IsProbabilityMeasure η] {V : M → ℝ≥0∞} (hV : Measurable V)
    (hVpos : ∀ᵐ g ∂η, 0 < V g) (hκ : ∫⁻ g, V g ^ m ∂η ≠ ∞) {x : ℝ≥0∞} (hx0 : x ≠ 0) :
    ∫⁻ u in Ioi 0, stableDensity m u
        * (ENNReal.ofReal u * ∫⁻ N, (pdSum V N + ENNReal.ofReal u * x)⁻¹ ∂pdProcess m η)
      = x ^ (m - 1) * (∫⁻ g, V g ^ m ∂η)⁻¹ := by
  have hc : 0 < stableConst m := stableConst_pos hm0 hm1
  have hκpos : 0 < (∫⁻ g, V g ^ m ∂η).toReal :=
    ENNReal.toReal_pos (lintegral_rpow_pos_of_ae_pos hm0 η hV hVpos).ne' hκ
  have hΓ : Real.Gamma (1 - m) = m * stableConst m := (mul_stableConst_eq_Gamma hm0 hm1).symm
  obtain ⟨κr, hκr0, hκr⟩ : ∃ κr : ℝ, 0 < κr ∧ (∫⁻ g, V g ^ m ∂η).toReal = κr := ⟨_, hκpos, rfl⟩
  have hκinv : (∫⁻ g, V g ^ m ∂η)⁻¹ = ENNReal.ofReal (1 / κr) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos hκr0, ← hκr, ENNReal.ofReal_toReal hκ]
  simp_rw [lintegral_inv_add_pdSum hm0 hm1 η hV hκ, hκr, hκinv]
  rcases eq_or_ne x ∞ with rfl | hx
  · -- an infinite weight contributes nothing
    rw [ENNReal.top_rpow_of_neg (by linarith), zero_mul]
    refine (setLIntegral_congr_fun (g := fun _ => (0 : ℝ≥0∞)) measurableSet_Ioi
      fun u hu => ?_).trans lintegral_zero
    rw [mem_Ioi] at hu
    have : ∫⁻ s in Ioi 0, ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ∞)))
        * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr))) = 0 := by
      refine (setLIntegral_congr_fun (g := fun _ => (0 : ℝ≥0∞)) measurableSet_Ioi
        fun s hs => ?_).trans lintegral_zero
      rw [mem_Ioi] at hs
      rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hu).ne',
        ENNReal.mul_top (ENNReal.ofReal_pos.2 hs).ne', negExp_top, ENNReal.ofReal_zero, zero_mul]
    rw [this, mul_zero, mul_zero]
  obtain ⟨v, hv, rfl⟩ : ∃ v : ℝ, 0 < v ∧ x = ENNReal.ofReal v :=
    ⟨x.toReal, ENNReal.toReal_pos hx0 hx, (ENNReal.ofReal_toReal hx).symm⟩
  -- Tonelli in `(u, s)`
  have hjoint : Measurable fun q : ℝ × ℝ => stableDensity m q.1 * (ENNReal.ofReal q.1
      * (ENNReal.ofReal (negExp (ENNReal.ofReal q.2 * (ENNReal.ofReal q.1 * ENNReal.ofReal v)))
        * ENNReal.ofReal (Real.exp (-(q.2 ^ m * stableConst m * κr))))) := by
    refine ((measurable_stableDensity m).comp measurable_fst).mul
      ((ENNReal.measurable_ofReal.comp measurable_fst).mul
        ((ENNReal.measurable_ofReal.comp (measurable_negExp.comp
          ((ENNReal.measurable_ofReal.comp measurable_snd).mul
            ((ENNReal.measurable_ofReal.comp measurable_fst).mul measurable_const)))).mul
          (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_))))
    exact ((measurable_snd.pow_const m).mul_const _).mul_const _ |>.neg
  have hpull : ∀ u ∈ Ioi (0 : ℝ), stableDensity m u * (ENNReal.ofReal u
      * ∫⁻ s in Ioi 0, ENNReal.ofReal (negExp (ENNReal.ofReal s
          * (ENNReal.ofReal u * ENNReal.ofReal v)))
        * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr))))
      = ∫⁻ s in Ioi 0, stableDensity m u * (ENNReal.ofReal u
        * (ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ENNReal.ofReal v)))
          * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr))))) := by
    intro u _
    have hmeas_u : Measurable fun s : ℝ =>
        ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ENNReal.ofReal v)))
          * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr))) :=
      (ENNReal.measurable_ofReal.comp (measurable_negExp.comp
        (ENNReal.measurable_ofReal.mul_const _))).mul (ENNReal.measurable_ofReal.comp
          (Real.measurable_exp.comp ((((measurable_id.pow_const m).mul_const _).mul_const _).neg)))
    rw [← lintegral_const_mul _ hmeas_u, ← lintegral_const_mul _ (hmeas_u.const_mul _)]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpull,
    lintegral_lintegral_swap (f := fun u s => stableDensity m u * (ENNReal.ofReal u
      * (ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ENNReal.ofReal v)))
        * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr)))))) hjoint.aemeasurable]
  -- the `u`-integral is a Gamma integral
  have hu_int : ∀ s ∈ Ioi (0 : ℝ), ∫⁻ u in Ioi 0, stableDensity m u * (ENNReal.ofReal u
      * (ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ENNReal.ofReal v)))
        * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr)))))
      = ENNReal.ofReal (v ^ (m - 1) * Real.Gamma (1 - m))
        * ENNReal.ofReal (s ^ (m - 1) * Real.exp (-((stableConst m * κr) * s ^ m))) := by
    intro s hs
    rw [mem_Ioi] at hs
    have hmeas : Measurable fun u : ℝ => stableDensity m u * (ENNReal.ofReal u
        * ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ENNReal.ofReal v)))) :=
      (measurable_stableDensity m).mul (ENNReal.measurable_ofReal.mul
        (ENNReal.measurable_ofReal.comp (measurable_negExp.comp (measurable_const.mul
          (ENNReal.measurable_ofReal.mul measurable_const)))))
    have hpt : ∀ u, stableDensity m u * (ENNReal.ofReal u
        * (ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ENNReal.ofReal v)))
          * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr)))))
        = ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr))) * (stableDensity m u
          * (ENNReal.ofReal u * ENNReal.ofReal (negExp (ENNReal.ofReal s
            * (ENNReal.ofReal u * ENNReal.ofReal v))))) := fun u => by ring
    simp_rw [hpt]
    rw [lintegral_const_mul _ hmeas, lintegral_stableDensity_mul_negExp hm1 hs hv,
      Real.mul_rpow hs.le hv.le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hv.le _) (Real.Gamma_nonneg_of_nonneg
        (by linarith)))]
    congr 1
    ring_nf
  have hmeas_s : Measurable fun s : ℝ =>
      ENNReal.ofReal (s ^ (m - 1) * Real.exp (-((stableConst m * κr) * s ^ m))) :=
    ENNReal.measurable_ofReal.comp ((measurable_id.pow_const _).mul
      (Real.measurable_exp.comp (((measurable_id.pow_const m).const_mul _).neg)))
  rw [setLIntegral_congr_fun measurableSet_Ioi hu_int, lintegral_const_mul _ hmeas_s,
    lintegral_rpow_mul_exp_neg_mul_rpow_Ioi hm0 (mul_pos hc hκr0),
    ENNReal.ofReal_rpow_of_pos hv, ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hv.le _)
      (Real.Gamma_nonneg_of_nonneg (by linarith))), ← ENNReal.ofReal_mul (Real.rpow_nonneg hv.le _)]
  congr 1
  rw [hΓ]
  field_simp

/-- **Identity (13.13)** (Talagrand Vol. II, Theorem 13.1.6), in `ℝ≥0∞`:
`𝔼 (∑_α u_α U(g_α)) / (∑_α u_α V(g_α)) = ∫ U V^{m-1} dη / ∫ V^m dη`, for measurable
`U, V : M → ℝ≥0∞` with `V > 0` and `∫ V^m dη < ∞`. -/
theorem lintegral_pdSum_mul_inv_pdSum {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {U V : M → ℝ≥0∞} (hU : Measurable U) (hV : Measurable V)
    (hVpos : ∀ᵐ g ∂η, 0 < V g) (hκ : ∫⁻ g, V g ^ m ∂η ≠ ∞) :
    ∫⁻ N, pdSum U N * (pdSum V N)⁻¹ ∂pdProcess m η
      = (∫⁻ g, U g * V g ^ (m - 1) ∂η) * (∫⁻ g, V g ^ m ∂η)⁻¹ := by
  have hS := measurable_pdSum (v := V) hV
  -- the Mecke formula
  have hf : Measurable fun q : (ℝ × M) × Measure (ℝ × M) =>
      ENNReal.ofReal q.1.1 * U q.1.2 * (pdSum V q.2)⁻¹ :=
    ((ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_fst)).mul
      (hU.comp (measurable_snd.comp measurable_fst))).mul (hS.comp measurable_snd).inv
  have hF : ∀ N : Measure (ℝ × M),
      ∫⁻ p, ENNReal.ofReal p.1 * U p.2 * (pdSum V N)⁻¹ ∂N = pdSum U N * (pdSum V N)⁻¹ :=
    fun N => by rw [lintegral_mul_const _ (measurable_ofReal_mul hU)]; rfl
  have hFm : Measurable fun N : Measure (ℝ × M) =>
      ∫⁻ p, ENNReal.ofReal p.1 * U p.2 * (pdSum V N)⁻¹ ∂N := by
    simp_rw [hF]
    exact (measurable_pdSum hU).mul hS.inv
  have hM : ∫⁻ N, ∫⁻ p, ENNReal.ofReal p.1 * U p.2 * (pdSum V N)⁻¹ ∂N ∂pdProcess m η
      = ∫⁻ N, ∫⁻ p, ENNReal.ofReal p.1 * U p.2 * (pdSum V (N + Measure.dirac p))⁻¹
          ∂pdIntensity m η ∂pdProcess m η :=
    lintegral_lintegral_pdProcess m η hf hFm
  simp_rw [hF] at hM
  rw [hM]
  simp_rw [pdSum_add_dirac hV]
  -- Tonelli in `(N, p)`
  have hjoint : Measurable fun q : Measure (ℝ × M) × (ℝ × M) =>
      ENNReal.ofReal q.2.1 * U q.2.2 * (pdSum V q.1 + ENNReal.ofReal q.2.1 * V q.2.2)⁻¹ :=
    ((ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_snd)).mul
      (hU.comp (measurable_snd.comp measurable_snd))).mul
      ((hS.comp measurable_fst).add ((ENNReal.measurable_ofReal.comp
        (measurable_fst.comp measurable_snd)).mul
          (hV.comp (measurable_snd.comp measurable_snd)))).inv
  have hswap := lintegral_lintegral_swap (μ := pdProcess m η) (ν := pdIntensity m η)
    (f := fun N p => ENNReal.ofReal p.1 * U p.2 * (pdSum V N + ENNReal.ofReal p.1 * V p.2)⁻¹)
    hjoint.aemeasurable
  rw [hswap]
  have hinner : ∀ p : ℝ × M, ∫⁻ N, ENNReal.ofReal p.1 * U p.2
        * (pdSum V N + ENNReal.ofReal p.1 * V p.2)⁻¹ ∂pdProcess m η
      = ENNReal.ofReal p.1 * U p.2
        * ∫⁻ N, (pdSum V N + ENNReal.ofReal p.1 * V p.2)⁻¹ ∂pdProcess m η := fun p =>
    lintegral_const_mul _ (hS.add measurable_const).inv
  simp_rw [hinner]
  have hG : Measurable fun p : ℝ × M => ENNReal.ofReal p.1 * U p.2
      * ∫⁻ N, (pdSum V N + ENNReal.ofReal p.1 * V p.2)⁻¹ ∂pdProcess m η := by
    refine ((ENNReal.measurable_ofReal.comp measurable_fst).mul (hU.comp measurable_snd)).mul ?_
    exact Measurable.lintegral_prod_right' (f := fun q : (ℝ × M) × Measure (ℝ × M) =>
      (pdSum V q.2 + ENNReal.ofReal q.1.1 * V q.1.2)⁻¹)
      ((hS.comp measurable_snd).add ((ENNReal.measurable_ofReal.comp
        (measurable_fst.comp measurable_fst)).mul
          (hV.comp (measurable_snd.comp measurable_fst)))).inv
  rw [lintegral_pdIntensity m η hG]
  have hg : ∀ᵐ g ∂η, ∫⁻ u in Ioi 0, stableDensity m u * (ENNReal.ofReal u * U g
        * ∫⁻ N, (pdSum V N + ENNReal.ofReal u * V g)⁻¹ ∂pdProcess m η)
      = U g * (V g ^ (m - 1) * (∫⁻ g, V g ^ m ∂η)⁻¹) := by
    filter_upwards [hVpos] with g hg
    rw [← lintegral_stableDensity_inv_add_pdSum hm0 hm1 η hV hVpos hκ hg.ne']
    have hmeas : Measurable fun u : ℝ => stableDensity m u * (ENNReal.ofReal u
        * ∫⁻ N, (pdSum V N + ENNReal.ofReal u * V g)⁻¹ ∂pdProcess m η) := by
      refine (measurable_stableDensity m).mul (ENNReal.measurable_ofReal.mul ?_)
      exact Measurable.lintegral_prod_right' (f := fun q : ℝ × Measure (ℝ × M) =>
        (pdSum V q.2 + ENNReal.ofReal q.1 * V g)⁻¹)
        ((hS.comp measurable_snd).add ((ENNReal.measurable_ofReal.comp measurable_fst).mul
          measurable_const)).inv
    rw [← lintegral_const_mul _ hmeas]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    ring
  rw [lintegral_congr_ae hg]
  simp_rw [← mul_assoc]
  exact lintegral_mul_const _ (hU.mul (hV.pow_const _))

/-! ### Identity (13.14) -/

/-- The mark-wise computation behind (13.14): for a weight `x ∈ (0, ∞]`,
`∫₀^∞ u^{-m-1} u² 𝔼 (S_V + u x)⁻² du = (1 - m) x^{m-2} / κ`. -/
lemma lintegral_stableDensity_inv_mul_inv_add_pdSum {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1)
    (η : Measure M) [IsProbabilityMeasure η] {V : M → ℝ≥0∞} (hV : Measurable V)
    (hVpos : ∀ᵐ g ∂η, 0 < V g) (hκ : ∫⁻ g, V g ^ m ∂η ≠ ∞) {x : ℝ≥0∞} (hx0 : x ≠ 0) :
    ∫⁻ u in Ioi 0, stableDensity m u * (ENNReal.ofReal u * ENNReal.ofReal u
        * ∫⁻ N, (pdSum V N + ENNReal.ofReal u * x)⁻¹ * (pdSum V N + ENNReal.ofReal u * x)⁻¹
          ∂pdProcess m η)
      = ENNReal.ofReal (1 - m) * (x ^ (m - 2) * (∫⁻ g, V g ^ m ∂η)⁻¹) := by
  have hc : 0 < stableConst m := stableConst_pos hm0 hm1
  have hκpos : 0 < (∫⁻ g, V g ^ m ∂η).toReal :=
    ENNReal.toReal_pos (lintegral_rpow_pos_of_ae_pos hm0 η hV hVpos).ne' hκ
  have hΓ : Real.Gamma (2 - m) = (1 - m) * (m * stableConst m) := by
    rw [mul_stableConst_eq_Gamma hm0 hm1, show (2 : ℝ) - m = (1 - m) + 1 by ring,
      Real.Gamma_add_one (by linarith)]
  obtain ⟨κr, hκr0, hκr⟩ : ∃ κr : ℝ, 0 < κr ∧ (∫⁻ g, V g ^ m ∂η).toReal = κr := ⟨_, hκpos, rfl⟩
  have hκinv : (∫⁻ g, V g ^ m ∂η)⁻¹ = ENNReal.ofReal (1 / κr) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos hκr0, ← hκr, ENNReal.ofReal_toReal hκ]
  simp_rw [lintegral_inv_mul_inv_add_pdSum hm0 hm1 η hV hκ, hκr, hκinv]
  rcases eq_or_ne x ∞ with rfl | hx
  · rw [ENNReal.top_rpow_of_neg (by linarith), zero_mul, mul_zero]
    refine (setLIntegral_congr_fun (g := fun _ => (0 : ℝ≥0∞)) measurableSet_Ioi
      fun u hu => ?_).trans lintegral_zero
    rw [mem_Ioi] at hu
    have : ∫⁻ s in Ioi 0, ENNReal.ofReal s
        * ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ∞)))
        * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr))) = 0 := by
      refine (setLIntegral_congr_fun (g := fun _ => (0 : ℝ≥0∞)) measurableSet_Ioi
        fun s hs => ?_).trans lintegral_zero
      rw [mem_Ioi] at hs
      rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hu).ne',
        ENNReal.mul_top (ENNReal.ofReal_pos.2 hs).ne', negExp_top, ENNReal.ofReal_zero, mul_zero,
        zero_mul]
    rw [this, mul_zero, mul_zero]
  obtain ⟨v, hv, rfl⟩ : ∃ v : ℝ, 0 < v ∧ x = ENNReal.ofReal v :=
    ⟨x.toReal, ENNReal.toReal_pos hx0 hx, (ENNReal.ofReal_toReal hx).symm⟩
  -- Tonelli in `(u, s)`
  have hjoint : Measurable fun q : ℝ × ℝ => stableDensity m q.1 * (ENNReal.ofReal q.1
      * ENNReal.ofReal q.1 * (ENNReal.ofReal q.2
        * ENNReal.ofReal (negExp (ENNReal.ofReal q.2 * (ENNReal.ofReal q.1 * ENNReal.ofReal v)))
        * ENNReal.ofReal (Real.exp (-(q.2 ^ m * stableConst m * κr))))) := by
    refine ((measurable_stableDensity m).comp measurable_fst).mul
      (((ENNReal.measurable_ofReal.comp measurable_fst).mul
        (ENNReal.measurable_ofReal.comp measurable_fst)).mul
        (((ENNReal.measurable_ofReal.comp measurable_snd).mul
          (ENNReal.measurable_ofReal.comp (measurable_negExp.comp
            ((ENNReal.measurable_ofReal.comp measurable_snd).mul
              ((ENNReal.measurable_ofReal.comp measurable_fst).mul measurable_const))))).mul
          (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_))))
    exact ((measurable_snd.pow_const m).mul_const _).mul_const _ |>.neg
  have hpull : ∀ u ∈ Ioi (0 : ℝ), stableDensity m u * (ENNReal.ofReal u * ENNReal.ofReal u
      * ∫⁻ s in Ioi 0, ENNReal.ofReal s * ENNReal.ofReal (negExp (ENNReal.ofReal s
          * (ENNReal.ofReal u * ENNReal.ofReal v)))
        * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr))))
      = ∫⁻ s in Ioi 0, stableDensity m u * (ENNReal.ofReal u * ENNReal.ofReal u
        * (ENNReal.ofReal s * ENNReal.ofReal (negExp (ENNReal.ofReal s
            * (ENNReal.ofReal u * ENNReal.ofReal v)))
          * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr))))) := by
    intro u _
    have hmeas_u : Measurable fun s : ℝ => ENNReal.ofReal s
        * ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ENNReal.ofReal v)))
          * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr))) :=
      (ENNReal.measurable_ofReal.mul (ENNReal.measurable_ofReal.comp (measurable_negExp.comp
        (ENNReal.measurable_ofReal.mul_const _)))).mul (ENNReal.measurable_ofReal.comp
          (Real.measurable_exp.comp ((((measurable_id.pow_const m).mul_const _).mul_const _).neg)))
    rw [← lintegral_const_mul _ hmeas_u, ← lintegral_const_mul _ (hmeas_u.const_mul _)]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpull,
    lintegral_lintegral_swap (f := fun u s => stableDensity m u * (ENNReal.ofReal u
      * ENNReal.ofReal u * (ENNReal.ofReal s * ENNReal.ofReal (negExp (ENNReal.ofReal s
          * (ENNReal.ofReal u * ENNReal.ofReal v)))
        * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr)))))) hjoint.aemeasurable]
  -- the `u`-integral is a Gamma integral
  have hu_int : ∀ s ∈ Ioi (0 : ℝ), ∫⁻ u in Ioi 0, stableDensity m u * (ENNReal.ofReal u
      * ENNReal.ofReal u * (ENNReal.ofReal s * ENNReal.ofReal (negExp (ENNReal.ofReal s
          * (ENNReal.ofReal u * ENNReal.ofReal v)))
        * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr)))))
      = ENNReal.ofReal (v ^ (m - 2) * Real.Gamma (2 - m))
        * ENNReal.ofReal (s ^ (m - 1) * Real.exp (-((stableConst m * κr) * s ^ m))) := by
    intro s hs
    rw [mem_Ioi] at hs
    have hmeas : Measurable fun u : ℝ => stableDensity m u * (ENNReal.ofReal u
        * ENNReal.ofReal u * ENNReal.ofReal (negExp (ENNReal.ofReal s
          * (ENNReal.ofReal u * ENNReal.ofReal v)))) :=
      (measurable_stableDensity m).mul ((ENNReal.measurable_ofReal.mul
        ENNReal.measurable_ofReal).mul (ENNReal.measurable_ofReal.comp (measurable_negExp.comp
          (measurable_const.mul (ENNReal.measurable_ofReal.mul measurable_const)))))
    have hpt : ∀ u, stableDensity m u * (ENNReal.ofReal u * ENNReal.ofReal u
        * (ENNReal.ofReal s * ENNReal.ofReal (negExp (ENNReal.ofReal s
            * (ENNReal.ofReal u * ENNReal.ofReal v)))
          * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr)))))
        = (ENNReal.ofReal s * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr))))
          * (stableDensity m u * (ENNReal.ofReal u * ENNReal.ofReal u
            * ENNReal.ofReal (negExp (ENNReal.ofReal s
              * (ENNReal.ofReal u * ENNReal.ofReal v))))) := fun u => by ring
    simp_rw [hpt]
    rw [lintegral_const_mul _ hmeas, lintegral_stableDensity_mul_sq_negExp hm1 hs hv,
      Real.mul_rpow hs.le hv.le, ← ENNReal.ofReal_mul hs.le,
      ← ENNReal.ofReal_mul (mul_nonneg hs.le (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hv.le _) (Real.Gamma_nonneg_of_nonneg
        (by linarith)))]
    congr 1
    have : s ^ (m - 1) = s ^ (m - 2) * s := by
      rw [show m - 1 = (m - 2) + 1 by ring, Real.rpow_add hs, Real.rpow_one]
    rw [this]
    ring_nf
  have hmeas_s : Measurable fun s : ℝ =>
      ENNReal.ofReal (s ^ (m - 1) * Real.exp (-((stableConst m * κr) * s ^ m))) :=
    ENNReal.measurable_ofReal.comp ((measurable_id.pow_const _).mul
      (Real.measurable_exp.comp (((measurable_id.pow_const m).const_mul _).neg)))
  rw [setLIntegral_congr_fun measurableSet_Ioi hu_int, lintegral_const_mul _ hmeas_s,
    lintegral_rpow_mul_exp_neg_mul_rpow_Ioi hm0 (mul_pos hc hκr0),
    ENNReal.ofReal_rpow_of_pos hv,
    ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hv.le _)
      (Real.Gamma_nonneg_of_nonneg (by linarith))),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hv.le _),
    ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 1 - m)]
  congr 1
  rw [hΓ]
  field_simp

/-- **Identity (13.14)** (Talagrand Vol. II, Theorem 13.1.6), in `ℝ≥0∞`:
`𝔼 (∑_α u_α² U(g_α) W(g_α)) / (∑_α u_α V(g_α))² = (1 - m) ∫ U W V^{m-2} dη / ∫ V^m dη`. -/
theorem lintegral_pdSumSq_mul_inv_pdSum_sq {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {U W V : M → ℝ≥0∞} (hU : Measurable U) (hW : Measurable W)
    (hV : Measurable V) (hVpos : ∀ᵐ g ∂η, 0 < V g) (hκ : ∫⁻ g, V g ^ m ∂η ≠ ∞) :
    ∫⁻ N, (∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * (U p.2 * W p.2) ∂N)
        * ((pdSum V N)⁻¹ * (pdSum V N)⁻¹) ∂pdProcess m η
      = ENNReal.ofReal (1 - m)
        * ((∫⁻ g, U g * W g * V g ^ (m - 2) ∂η) * (∫⁻ g, V g ^ m ∂η)⁻¹) := by
  have hS := measurable_pdSum (v := V) hV
  have hUW : Measurable fun p : ℝ × M =>
      ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * (U p.2 * W p.2) :=
    ((ENNReal.measurable_ofReal.comp measurable_fst).mul
      (ENNReal.measurable_ofReal.comp measurable_fst)).mul
      ((hU.comp measurable_snd).mul (hW.comp measurable_snd))
  -- the Mecke formula
  have hf : Measurable fun q : (ℝ × M) × Measure (ℝ × M) =>
      ENNReal.ofReal q.1.1 * ENNReal.ofReal q.1.1 * (U q.1.2 * W q.1.2)
        * ((pdSum V q.2)⁻¹ * (pdSum V q.2)⁻¹) :=
    (hUW.comp measurable_fst).mul ((hS.comp measurable_snd).inv.mul (hS.comp measurable_snd).inv)
  have hF : ∀ N : Measure (ℝ × M),
      ∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * (U p.2 * W p.2)
          * ((pdSum V N)⁻¹ * (pdSum V N)⁻¹) ∂N
        = (∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * (U p.2 * W p.2) ∂N)
          * ((pdSum V N)⁻¹ * (pdSum V N)⁻¹) :=
    fun N => lintegral_mul_const _ hUW
  have hFm : Measurable fun N : Measure (ℝ × M) =>
      ∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * (U p.2 * W p.2)
        * ((pdSum V N)⁻¹ * (pdSum V N)⁻¹) ∂N := by
    simp_rw [hF]
    exact (Measure.measurable_lintegral hUW).mul (hS.inv.mul hS.inv)
  have hM : ∫⁻ N, ∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * (U p.2 * W p.2)
        * ((pdSum V N)⁻¹ * (pdSum V N)⁻¹) ∂N ∂pdProcess m η
      = ∫⁻ N, ∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * (U p.2 * W p.2)
          * ((pdSum V (N + Measure.dirac p))⁻¹ * (pdSum V (N + Measure.dirac p))⁻¹)
          ∂pdIntensity m η ∂pdProcess m η :=
    lintegral_lintegral_pdProcess m η hf hFm
  simp_rw [hF] at hM
  rw [hM]
  simp_rw [pdSum_add_dirac hV]
  -- Tonelli in `(N, p)`
  have hjoint : Measurable fun q : Measure (ℝ × M) × (ℝ × M) =>
      ENNReal.ofReal q.2.1 * ENNReal.ofReal q.2.1 * (U q.2.2 * W q.2.2)
        * ((pdSum V q.1 + ENNReal.ofReal q.2.1 * V q.2.2)⁻¹
          * (pdSum V q.1 + ENNReal.ofReal q.2.1 * V q.2.2)⁻¹) := by
    have h1 : Measurable fun q : Measure (ℝ × M) × (ℝ × M) =>
        pdSum V q.1 + ENNReal.ofReal q.2.1 * V q.2.2 :=
      (hS.comp measurable_fst).add ((ENNReal.measurable_ofReal.comp
        (measurable_fst.comp measurable_snd)).mul (hV.comp (measurable_snd.comp measurable_snd)))
    exact (hUW.comp measurable_snd).mul (h1.inv.mul h1.inv)
  have hswap := lintegral_lintegral_swap (μ := pdProcess m η) (ν := pdIntensity m η)
    (f := fun N p => ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * (U p.2 * W p.2)
      * ((pdSum V N + ENNReal.ofReal p.1 * V p.2)⁻¹ * (pdSum V N + ENNReal.ofReal p.1 * V p.2)⁻¹))
    hjoint.aemeasurable
  rw [hswap]
  have hinner : ∀ p : ℝ × M, ∫⁻ N, ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * (U p.2 * W p.2)
        * ((pdSum V N + ENNReal.ofReal p.1 * V p.2)⁻¹
          * (pdSum V N + ENNReal.ofReal p.1 * V p.2)⁻¹) ∂pdProcess m η
      = ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * (U p.2 * W p.2)
        * ∫⁻ N, (pdSum V N + ENNReal.ofReal p.1 * V p.2)⁻¹
          * (pdSum V N + ENNReal.ofReal p.1 * V p.2)⁻¹ ∂pdProcess m η := fun p =>
    lintegral_const_mul _ ((hS.add measurable_const).inv.mul (hS.add measurable_const).inv)
  simp_rw [hinner]
  have hG : Measurable fun p : ℝ × M => ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * (U p.2 * W p.2)
      * ∫⁻ N, (pdSum V N + ENNReal.ofReal p.1 * V p.2)⁻¹
        * (pdSum V N + ENNReal.ofReal p.1 * V p.2)⁻¹ ∂pdProcess m η := by
    refine hUW.mul ?_
    have h1 : Measurable fun q : (ℝ × M) × Measure (ℝ × M) =>
        pdSum V q.2 + ENNReal.ofReal q.1.1 * V q.1.2 :=
      (hS.comp measurable_snd).add ((ENNReal.measurable_ofReal.comp
        (measurable_fst.comp measurable_fst)).mul (hV.comp (measurable_snd.comp measurable_fst)))
    exact Measurable.lintegral_prod_right' (f := fun q : (ℝ × M) × Measure (ℝ × M) =>
      (pdSum V q.2 + ENNReal.ofReal q.1.1 * V q.1.2)⁻¹
        * (pdSum V q.2 + ENNReal.ofReal q.1.1 * V q.1.2)⁻¹) (h1.inv.mul h1.inv)
  rw [lintegral_pdIntensity m η hG]
  have hg : ∀ᵐ g ∂η, ∫⁻ u in Ioi 0, stableDensity m u
        * (ENNReal.ofReal u * ENNReal.ofReal u * (U g * W g)
          * ∫⁻ N, (pdSum V N + ENNReal.ofReal u * V g)⁻¹
            * (pdSum V N + ENNReal.ofReal u * V g)⁻¹ ∂pdProcess m η)
      = U g * W g * (ENNReal.ofReal (1 - m) * (V g ^ (m - 2) * (∫⁻ g, V g ^ m ∂η)⁻¹)) := by
    filter_upwards [hVpos] with g hg
    rw [← lintegral_stableDensity_inv_mul_inv_add_pdSum hm0 hm1 η hV hVpos hκ hg.ne']
    have h1 : Measurable fun q : ℝ × Measure (ℝ × M) =>
        pdSum V q.2 + ENNReal.ofReal q.1 * V g :=
      (hS.comp measurable_snd).add ((ENNReal.measurable_ofReal.comp measurable_fst).mul
        measurable_const)
    have hmeas : Measurable fun u : ℝ => stableDensity m u * (ENNReal.ofReal u * ENNReal.ofReal u
        * ∫⁻ N, (pdSum V N + ENNReal.ofReal u * V g)⁻¹
          * (pdSum V N + ENNReal.ofReal u * V g)⁻¹ ∂pdProcess m η) := by
      refine (measurable_stableDensity m).mul
        ((ENNReal.measurable_ofReal.mul ENNReal.measurable_ofReal).mul ?_)
      exact Measurable.lintegral_prod_right' (f := fun q : ℝ × Measure (ℝ × M) =>
        (pdSum V q.2 + ENNReal.ofReal q.1 * V g)⁻¹ * (pdSum V q.2 + ENNReal.ofReal q.1 * V g)⁻¹)
        (h1.inv.mul h1.inv)
    rw [← lintegral_const_mul _ hmeas]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    ring
  rw [lintegral_congr_ae hg]
  have h1 : Measurable fun g => U g * W g * V g ^ (m - 2) := (hU.mul hW).mul (hV.pow_const _)
  calc ∫⁻ g, U g * W g * (ENNReal.ofReal (1 - m)
          * (V g ^ (m - 2) * (∫⁻ g, V g ^ m ∂η)⁻¹)) ∂η
      = ∫⁻ g, ENNReal.ofReal (1 - m)
          * (U g * W g * V g ^ (m - 2) * (∫⁻ g, V g ^ m ∂η)⁻¹) ∂η :=
        lintegral_congr fun g => by ring
    _ = _ := by rw [lintegral_const_mul _ (h1.mul_const _), lintegral_mul_const _ h1]

/-- **Identity (13.17)** (Talagrand Vol. II): `𝔼 ∑_α v_α² = 1 - m` for the Poisson–Dirichlet
weights `v_α = u_α / ∑_γ u_γ`. -/
theorem lintegral_pdSumSq_mul_inv_pdSum_one_sq {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1)
    (η : Measure M) [IsProbabilityMeasure η] :
    ∫⁻ N, (∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1 ∂N)
        * ((pdSum (fun _ => 1) N)⁻¹ * (pdSum (fun _ => 1) N)⁻¹) ∂pdProcess m η
      = ENNReal.ofReal (1 - m) := by
  have h := lintegral_pdSumSq_mul_inv_pdSum_sq hm0 hm1 η (U := fun _ => 1) (W := fun _ => 1)
    (V := fun _ => 1) measurable_const measurable_const measurable_const
    (Filter.Eventually.of_forall fun _ => one_pos) (by simp)
  simpa using h

/-! ### Real forms -/

/-- **Identity (13.13)** in Talagrand's real form:
`𝔼 (∑_α u_α U(g_α)) / (∑_α u_α V(g_α)) = ∫ U V^{m-1} dη / ∫ V^m dη`. -/
theorem integral_pdSum_div_pdSum {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {U V : M → ℝ≥0∞} (hU : Measurable U) (hV : Measurable V)
    (hVpos : ∀ᵐ g ∂η, 0 < V g) (hκ : ∫⁻ g, V g ^ m ∂η ≠ ∞) (hUκ : ∫⁻ g, U g ^ m ∂η ≠ ∞) :
    ∫ N, (pdSum U N).toReal / (pdSum V N).toReal ∂pdProcess m η
      = (∫⁻ g, U g * V g ^ (m - 1) ∂η).toReal / (∫⁻ g, V g ^ m ∂η).toReal := by
  obtain ⟨δ, hδ, hη⟩ := exists_pos_measure_ge_of_ae_pos η hVpos
  have hae : ∀ᵐ N ∂pdProcess m η, (pdSum U N).toReal / (pdSum V N).toReal
      = (pdSum U N * (pdSum V N)⁻¹).toReal := by
    filter_upwards with N
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv]
  have hfin : ∀ᵐ N ∂pdProcess m η, pdSum U N * (pdSum V N)⁻¹ < ∞ := by
    filter_upwards [ae_pdSum_lt_top hm0 hm1 η hU hUκ, ae_pdSum_pos hm0 η hV hδ hη] with N h1 h2
    exact ENNReal.mul_lt_top h1 (ENNReal.inv_lt_top.2 h2)
  have hmeas : Measurable fun N : Measure (ℝ × M) => pdSum U N * (pdSum V N)⁻¹ :=
    (measurable_pdSum hU).mul (measurable_pdSum hV).inv
  rw [integral_congr_ae hae, integral_toReal hmeas.aemeasurable hfin,
    lintegral_pdSum_mul_inv_pdSum hm0 hm1 η hU hV hVpos hκ, ENNReal.toReal_mul,
    ENNReal.toReal_inv, div_eq_mul_inv]

/-! ### General exponents: `(S + a)^{-b}` -/

omit [Nonempty M] in
/-- `x^{-b} = Γ(b)⁻¹ ∫₀^∞ s^{b-1} e^{-s x} ds` for `b > 0` and every `x ∈ (0, ∞]`. -/
theorem _root_.ENNReal.rpow_neg_eq_lintegral_rpow_mul_negExp {b : ℝ} (hb : 0 < b) {x : ℝ≥0∞}
    (hx0 : x ≠ 0) :
    x ^ (-b) = (ENNReal.ofReal (Real.Gamma b))⁻¹
      * ∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ (b - 1))
          * ENNReal.ofReal (negExp (ENNReal.ofReal s * x)) := by
  rcases eq_or_ne x ∞ with rfl | hx
  · rw [ENNReal.top_rpow_of_neg (by linarith)]
    symm
    rw [(setLIntegral_congr_fun (g := fun _ => (0 : ℝ≥0∞)) measurableSet_Ioi
      fun s hs => ?_).trans lintegral_zero, mul_zero]
    rw [mem_Ioi] at hs
    rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hs).ne', negExp_top, ENNReal.ofReal_zero, mul_zero]
  obtain ⟨y, hy, rfl⟩ : ∃ y : ℝ, 0 < y ∧ x = ENNReal.ofReal y :=
    ⟨x.toReal, ENNReal.toReal_pos hx0 hx, (ENNReal.ofReal_toReal hx).symm⟩
  have hΓ : 0 < Real.Gamma b := Real.Gamma_pos_of_pos hb
  have h := lintegral_rpow_mul_exp_neg_mul_Ioi hb hy
  have hpt : ∀ s ∈ Ioi (0 : ℝ), ENNReal.ofReal (s ^ (b - 1))
      * ENNReal.ofReal (negExp (ENNReal.ofReal s * ENNReal.ofReal y))
      = ENNReal.ofReal (s ^ (b - 1) * Real.exp (-(y * s))) := by
    intro s hs
    rw [mem_Ioi] at hs
    have hneg : negExp (ENNReal.ofReal s * ENNReal.ofReal y) = Real.exp (-(s * y)) := by
      rw [← ENNReal.ofReal_mul hs.le, negExp_ofReal (by positivity)]
    rw [hneg, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _), mul_comm y s]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, h, ← ENNReal.ofReal_inv_of_pos hΓ,
    ← ENNReal.ofReal_mul (inv_nonneg.2 hΓ.le), ENNReal.ofReal_rpow_of_pos hy]
  congr 1
  rw [one_div, Real.inv_rpow hy.le, ← Real.rpow_neg hy.le]
  field_simp

/-- `𝔼 (S_V + a)^{-b} = Γ(b)⁻¹ ∫₀^∞ s^{b-1} e^{-s a} e^{-s^m c_m κ} ds`, for `b > 0`, `a ≠ 0`. -/
theorem lintegral_rpow_neg_add_pdSum {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {V : M → ℝ≥0∞} (hV : Measurable V)
    (hκ : ∫⁻ g, V g ^ m ∂η ≠ ∞) {b : ℝ} (hb : 0 < b) {a : ℝ≥0∞} (ha : a ≠ 0) :
    ∫⁻ N, (pdSum V N + a) ^ (-b) ∂pdProcess m η
      = (ENNReal.ofReal (Real.Gamma b))⁻¹
        * ∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ (b - 1))
          * ENNReal.ofReal (negExp (ENNReal.ofReal s * a))
          * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m
              * (∫⁻ g, V g ^ m ∂η).toReal))) := by
  have hS := measurable_pdSum (v := V) hV
  have hpt : ∀ N, (pdSum V N + a) ^ (-b) = (ENNReal.ofReal (Real.Gamma b))⁻¹
      * ∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ (b - 1))
          * ENNReal.ofReal (negExp (ENNReal.ofReal s * (pdSum V N + a))) := fun N =>
    ENNReal.rpow_neg_eq_lintegral_rpow_mul_negExp hb
      (by intro h; exact ha (add_eq_zero.1 h).2)
  simp_rw [hpt]
  have hjoint : Measurable fun q : Measure (ℝ × M) × ℝ => ENNReal.ofReal (q.2 ^ (b - 1))
      * ENNReal.ofReal (negExp (ENNReal.ofReal q.2 * (pdSum V q.1 + a))) :=
    (ENNReal.measurable_ofReal.comp (measurable_snd.pow_const _)).mul
      (ENNReal.measurable_ofReal.comp (measurable_negExp.comp
        ((ENNReal.measurable_ofReal.comp measurable_snd).mul
          ((hS.comp measurable_fst).add measurable_const))))
  have hmeas : Measurable fun N : Measure (ℝ × M) => ∫⁻ s in Ioi 0,
      ENNReal.ofReal (s ^ (b - 1)) * ENNReal.ofReal (negExp (ENNReal.ofReal s * (pdSum V N + a))) :=
    Measurable.lintegral_prod_right' hjoint
  rw [lintegral_const_mul _ hmeas, lintegral_lintegral_swap (f := fun N s =>
    ENNReal.ofReal (s ^ (b - 1)) * ENNReal.ofReal (negExp (ENNReal.ofReal s * (pdSum V N + a))))
    hjoint.aemeasurable]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  rw [mem_Ioi] at hs
  have hpt' : ∀ N, ENNReal.ofReal (s ^ (b - 1))
        * ENNReal.ofReal (negExp (ENNReal.ofReal s * (pdSum V N + a)))
      = (ENNReal.ofReal (s ^ (b - 1)) * ENNReal.ofReal (negExp (ENNReal.ofReal s * a)))
        * ENNReal.ofReal (negExp (ENNReal.ofReal s * pdSum V N)) := by
    intro N
    rw [mul_add, negExp_add, ENNReal.ofReal_mul (negExp_nonneg _)]
    ring
  simp_rw [hpt']
  have hint : Integrable (fun N => negExp (ENNReal.ofReal s * pdSum V N)) (pdProcess m η) :=
    Integrable.mono' (integrable_const 1)
      (measurable_negExp.comp (measurable_const.mul hS)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun N => by
        rw [Real.norm_eq_abs, abs_of_nonneg (negExp_nonneg _)]; exact negExp_le_one _)
  have hmeas' : Measurable fun N : Measure (ℝ × M) =>
      ENNReal.ofReal (negExp (ENNReal.ofReal s * pdSum V N)) :=
    ENNReal.measurable_ofReal.comp (measurable_negExp.comp (measurable_const.mul hS))
  rw [lintegral_const_mul _ hmeas', ← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun N => negExp_nonneg _),
    integral_negExp_pdSum_eq_exp hm0 hm1 η hV hκ hs.le]

/-- The constant of the identity (13.14) with exponent `a - 2`:
`K₂(a) = Γ(2-m) Γ(1-a/m) (c_m κ)^{a/m-1} / (m Γ(2-a))`. -/
def pdSqConst (m a c κ : ℝ) : ℝ :=
  Real.Gamma (2 - m) * Real.Gamma (1 - a / m) * (c * κ) ^ (a / m - 1) / (m * Real.Gamma (2 - a))

/-- The mark-wise computation behind (13.14) with exponent `a - 2`: for a weight `x ∈ (0, ∞]`,
`∫₀^∞ u^{-m-1} u² 𝔼 (S_V + u x)^{a-2} du = K₂(a) x^{m-2}`. -/
lemma lintegral_stableDensity_rpow_add_pdSum {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1)
    (η : Measure M) [IsProbabilityMeasure η] {V : M → ℝ≥0∞} (hV : Measurable V)
    (hVpos : ∀ᵐ g ∂η, 0 < V g) (hκ : ∫⁻ g, V g ^ m ∂η ≠ ∞) {a : ℝ} (ham : a < m)
    {x : ℝ≥0∞} (hx0 : x ≠ 0) :
    ∫⁻ u in Ioi 0, stableDensity m u * (ENNReal.ofReal u * ENNReal.ofReal u
        * ∫⁻ N, (pdSum V N + ENNReal.ofReal u * x) ^ (a - 2) ∂pdProcess m η)
      = ENNReal.ofReal (pdSqConst m a (stableConst m) (∫⁻ g, V g ^ m ∂η).toReal)
        * x ^ (m - 2) := by
  have hc : 0 < stableConst m := stableConst_pos hm0 hm1
  have hκpos : 0 < (∫⁻ g, V g ^ m ∂η).toReal :=
    ENNReal.toReal_pos (lintegral_rpow_pos_of_ae_pos hm0 η hV hVpos).ne' hκ
  obtain ⟨κr, hκr0, hκr⟩ : ∃ κr : ℝ, 0 < κr ∧ (∫⁻ g, V g ^ m ∂η).toReal = κr := ⟨_, hκpos, rfl⟩
  rw [hκr]
  have hb : 0 < 2 - a := by linarith
  have hΓb : 0 < Real.Gamma (2 - a) := Real.Gamma_pos_of_pos hb
  have hexp : ∀ u : ℝ, 0 < u → ∀ N : Measure (ℝ × M),
      (pdSum V N + ENNReal.ofReal u * x) ^ (a - 2)
        = (pdSum V N + ENNReal.ofReal u * x) ^ (-(2 - a)) := by
    intro u _ N
    rw [neg_sub]
  have hinner : ∀ u ∈ Ioi (0 : ℝ),
      ∫⁻ N, (pdSum V N + ENNReal.ofReal u * x) ^ (a - 2) ∂pdProcess m η
        = (ENNReal.ofReal (Real.Gamma (2 - a)))⁻¹
          * ∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ (2 - a - 1))
            * ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * x)))
            * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr))) := by
    intro u hu
    rw [mem_Ioi] at hu
    simp_rw [hexp u hu]
    rw [lintegral_rpow_neg_add_pdSum hm0 hm1 η hV hκ hb
      (mul_ne_zero (ENNReal.ofReal_pos.2 hu).ne' hx0), hκr]
  rw [setLIntegral_congr_fun measurableSet_Ioi fun u hu => by rw [hinner u hu]]
  rcases eq_or_ne x ∞ with rfl | hx
  · -- an infinite weight contributes nothing
    rw [ENNReal.top_rpow_of_neg (by linarith), mul_zero]
    refine (setLIntegral_congr_fun (g := fun _ => (0 : ℝ≥0∞)) measurableSet_Ioi
      fun u hu => ?_).trans lintegral_zero
    rw [mem_Ioi] at hu
    have : ∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ (2 - a - 1))
        * ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ∞)))
        * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr))) = 0 := by
      refine (setLIntegral_congr_fun (g := fun _ => (0 : ℝ≥0∞)) measurableSet_Ioi
        fun s hs => ?_).trans lintegral_zero
      rw [mem_Ioi] at hs
      rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hu).ne',
        ENNReal.mul_top (ENNReal.ofReal_pos.2 hs).ne', negExp_top, ENNReal.ofReal_zero, mul_zero,
        zero_mul]
    rw [this, mul_zero, mul_zero, mul_zero]
  obtain ⟨v, hv, rfl⟩ : ∃ v : ℝ, 0 < v ∧ x = ENNReal.ofReal v :=
    ⟨x.toReal, ENNReal.toReal_pos hx0 hx, (ENNReal.ofReal_toReal hx).symm⟩
  -- pull the constant out and Tonelli in `(u, s)`
  have hjoint : Measurable fun q : ℝ × ℝ => stableDensity m q.1 * (ENNReal.ofReal q.1
      * ENNReal.ofReal q.1 * (ENNReal.ofReal (q.2 ^ (2 - a - 1))
        * ENNReal.ofReal (negExp (ENNReal.ofReal q.2 * (ENNReal.ofReal q.1 * ENNReal.ofReal v)))
        * ENNReal.ofReal (Real.exp (-(q.2 ^ m * stableConst m * κr))))) := by
    refine ((measurable_stableDensity m).comp measurable_fst).mul
      (((ENNReal.measurable_ofReal.comp measurable_fst).mul
        (ENNReal.measurable_ofReal.comp measurable_fst)).mul
        (((ENNReal.measurable_ofReal.comp (measurable_snd.pow_const _)).mul
          (ENNReal.measurable_ofReal.comp (measurable_negExp.comp
            ((ENNReal.measurable_ofReal.comp measurable_snd).mul
              ((ENNReal.measurable_ofReal.comp measurable_fst).mul measurable_const))))).mul
          (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_))))
    exact ((measurable_snd.pow_const m).mul_const _).mul_const _ |>.neg
  have hpull : ∀ u ∈ Ioi (0 : ℝ), stableDensity m u * (ENNReal.ofReal u * ENNReal.ofReal u
      * ((ENNReal.ofReal (Real.Gamma (2 - a)))⁻¹
        * ∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ (2 - a - 1))
          * ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ENNReal.ofReal v)))
          * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr)))))
      = (ENNReal.ofReal (Real.Gamma (2 - a)))⁻¹
        * ∫⁻ s in Ioi 0, stableDensity m u * (ENNReal.ofReal u * ENNReal.ofReal u
          * (ENNReal.ofReal (s ^ (2 - a - 1))
            * ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ENNReal.ofReal v)))
            * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr))))) := by
    intro u _
    have hmeas_u : Measurable fun s : ℝ => ENNReal.ofReal (s ^ (2 - a - 1))
        * ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ENNReal.ofReal v)))
          * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr))) :=
      ((ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul
        (ENNReal.measurable_ofReal.comp (measurable_negExp.comp
          (ENNReal.measurable_ofReal.mul_const _)))).mul (ENNReal.measurable_ofReal.comp
            (Real.measurable_exp.comp
              ((((measurable_id.pow_const m).mul_const _).mul_const _).neg)))
    have hR : Measurable fun s : ℝ => stableDensity m u * (ENNReal.ofReal u * ENNReal.ofReal u
        * (ENNReal.ofReal (s ^ (2 - a - 1))
          * ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ENNReal.ofReal v)))
          * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr))))) :=
      (hmeas_u.const_mul _).const_mul _
    rw [← lintegral_const_mul _ hR, ← lintegral_const_mul _ hmeas_u,
      ← lintegral_const_mul _ (hmeas_u.const_mul _),
      ← lintegral_const_mul _ ((hmeas_u.const_mul _).const_mul _)]
    refine lintegral_congr fun s => ?_
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hpull, lintegral_const_mul _
    (Measurable.lintegral_prod_right' hjoint),
    lintegral_lintegral_swap (f := fun u s => stableDensity m u * (ENNReal.ofReal u
      * ENNReal.ofReal u * (ENNReal.ofReal (s ^ (2 - a - 1))
        * ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ENNReal.ofReal v)))
        * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr)))))) hjoint.aemeasurable]
  -- the `u`-integral is a Gamma integral
  have hu_int : ∀ s ∈ Ioi (0 : ℝ), ∫⁻ u in Ioi 0, stableDensity m u * (ENNReal.ofReal u
      * ENNReal.ofReal u * (ENNReal.ofReal (s ^ (2 - a - 1))
        * ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ENNReal.ofReal v)))
        * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr)))))
      = ENNReal.ofReal (v ^ (m - 2) * Real.Gamma (2 - m))
        * ENNReal.ofReal (s ^ (m - a - 1) * Real.exp (-((stableConst m * κr) * s ^ m))) := by
    intro s hs
    rw [mem_Ioi] at hs
    have hmeas : Measurable fun u : ℝ => stableDensity m u * (ENNReal.ofReal u
        * ENNReal.ofReal u * ENNReal.ofReal (negExp (ENNReal.ofReal s
          * (ENNReal.ofReal u * ENNReal.ofReal v)))) :=
      (measurable_stableDensity m).mul ((ENNReal.measurable_ofReal.mul
        ENNReal.measurable_ofReal).mul (ENNReal.measurable_ofReal.comp (measurable_negExp.comp
          (measurable_const.mul (ENNReal.measurable_ofReal.mul measurable_const)))))
    have hpt : ∀ u, stableDensity m u * (ENNReal.ofReal u * ENNReal.ofReal u
        * (ENNReal.ofReal (s ^ (2 - a - 1))
          * ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ENNReal.ofReal v)))
          * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr)))))
        = (ENNReal.ofReal (s ^ (2 - a - 1))
            * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr))))
          * (stableDensity m u * (ENNReal.ofReal u * ENNReal.ofReal u
            * ENNReal.ofReal (negExp (ENNReal.ofReal s
              * (ENNReal.ofReal u * ENNReal.ofReal v))))) := fun u => by ring
    simp_rw [hpt]
    rw [lintegral_const_mul _ hmeas, lintegral_stableDensity_mul_sq_negExp hm1 hs hv,
      Real.mul_rpow hs.le hv.le, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _),
      ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hs.le _) (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hv.le _) (Real.Gamma_nonneg_of_nonneg
        (by linarith)))]
    congr 1
    have : s ^ (m - a - 1) = s ^ (2 - a - 1) * s ^ (m - 2) := by
      rw [← Real.rpow_add hs]; ring_nf
    rw [this]
    ring_nf
  have hmeas_s : Measurable fun s : ℝ =>
      ENNReal.ofReal (s ^ (m - a - 1) * Real.exp (-((stableConst m * κr) * s ^ m))) :=
    ENNReal.measurable_ofReal.comp ((measurable_id.pow_const _).mul
      (Real.measurable_exp.comp (((measurable_id.pow_const m).const_mul _).neg)))
  rw [setLIntegral_congr_fun measurableSet_Ioi hu_int, lintegral_const_mul _ hmeas_s,
    lintegral_rpow_mul_exp_neg_mul_rpow_Ioi' hm0 (by linarith : 0 < m - a) (mul_pos hc hκr0),
    ENNReal.ofReal_rpow_of_pos hv, ← ENNReal.ofReal_inv_of_pos hΓb,
    ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hv.le _)
      (Real.Gamma_nonneg_of_nonneg (by linarith))),
    ← ENNReal.ofReal_mul (inv_nonneg.2 hΓb.le)]
  have hK : 0 ≤ pdSqConst m a (stableConst m) κr := by
    unfold pdSqConst
    exact div_nonneg (mul_nonneg (mul_nonneg (Real.Gamma_nonneg_of_nonneg (by linarith))
      (Real.Gamma_nonneg_of_nonneg (by rw [sub_nonneg]; exact (div_le_one hm0).2 ham.le)))
      (Real.rpow_nonneg (by positivity) _)) (mul_nonneg hm0.le hΓb.le)
  rw [← ENNReal.ofReal_mul hK]
  congr 1
  have h1 : (m - a) / m = 1 - a / m := by field_simp
  have h2 : (1 / (stableConst m * κr)) ^ (1 - a / m)
      = (stableConst m * κr) ^ (a / m - 1) := by
    rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), neg_sub]
  rw [pdSqConst, h1, h2]
  ring

/-- **Identity (13.14) with exponent `a - 2`**, `0 ≤ a < m`:
`𝔼 (∑_α u_α² A(g_α)) (∑_α u_α V(g_α))^{a-2} = K₂(a) ∫ A V^{m-2} dη`. -/
theorem lintegral_pdSumSq_mul_rpow_pdSum {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {A V : M → ℝ≥0∞} (hA : Measurable A) (hV : Measurable V)
    (hVpos : ∀ᵐ g ∂η, 0 < V g) (hκ : ∫⁻ g, V g ^ m ∂η ≠ ∞) {a : ℝ} (ham : a < m) :
    ∫⁻ N, (∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * A p.2 ∂N)
        * (pdSum V N) ^ (a - 2) ∂pdProcess m η
      = ENNReal.ofReal (pdSqConst m a (stableConst m) (∫⁻ g, V g ^ m ∂η).toReal)
        * ∫⁻ g, A g * V g ^ (m - 2) ∂η := by
  have hS := measurable_pdSum (v := V) hV
  have hUW : Measurable fun p : ℝ × M => ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * A p.2 :=
    ((ENNReal.measurable_ofReal.comp measurable_fst).mul
      (ENNReal.measurable_ofReal.comp measurable_fst)).mul (hA.comp measurable_snd)
  -- the Mecke formula
  have hf : Measurable fun q : (ℝ × M) × Measure (ℝ × M) =>
      ENNReal.ofReal q.1.1 * ENNReal.ofReal q.1.1 * A q.1.2 * (pdSum V q.2) ^ (a - 2) :=
    (hUW.comp measurable_fst).mul ((hS.comp measurable_snd).pow_const _)
  have hF : ∀ N : Measure (ℝ × M),
      ∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * A p.2 * (pdSum V N) ^ (a - 2) ∂N
        = (∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * A p.2 ∂N) * (pdSum V N) ^ (a - 2) :=
    fun N => lintegral_mul_const _ hUW
  have hFm : Measurable fun N : Measure (ℝ × M) =>
      ∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * A p.2 * (pdSum V N) ^ (a - 2) ∂N := by
    simp_rw [hF]
    exact (Measure.measurable_lintegral hUW).mul (hS.pow_const _)
  have hM : ∫⁻ N, ∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * A p.2
        * (pdSum V N) ^ (a - 2) ∂N ∂pdProcess m η
      = ∫⁻ N, ∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * A p.2
          * (pdSum V (N + Measure.dirac p)) ^ (a - 2) ∂pdIntensity m η ∂pdProcess m η :=
    lintegral_lintegral_pdProcess m η hf hFm
  simp_rw [hF] at hM
  rw [hM]
  simp_rw [pdSum_add_dirac hV]
  -- Tonelli in `(N, p)`
  have hjoint : Measurable fun q : Measure (ℝ × M) × (ℝ × M) =>
      ENNReal.ofReal q.2.1 * ENNReal.ofReal q.2.1 * A q.2.2
        * (pdSum V q.1 + ENNReal.ofReal q.2.1 * V q.2.2) ^ (a - 2) := by
    have h1 : Measurable fun q : Measure (ℝ × M) × (ℝ × M) =>
        pdSum V q.1 + ENNReal.ofReal q.2.1 * V q.2.2 :=
      (hS.comp measurable_fst).add ((ENNReal.measurable_ofReal.comp
        (measurable_fst.comp measurable_snd)).mul (hV.comp (measurable_snd.comp measurable_snd)))
    exact (hUW.comp measurable_snd).mul (h1.pow_const _)
  have hswap := lintegral_lintegral_swap (μ := pdProcess m η) (ν := pdIntensity m η)
    (f := fun N p => ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * A p.2
      * (pdSum V N + ENNReal.ofReal p.1 * V p.2) ^ (a - 2)) hjoint.aemeasurable
  rw [hswap]
  have hinner : ∀ p : ℝ × M, ∫⁻ N, ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * A p.2
        * (pdSum V N + ENNReal.ofReal p.1 * V p.2) ^ (a - 2) ∂pdProcess m η
      = ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * A p.2
        * ∫⁻ N, (pdSum V N + ENNReal.ofReal p.1 * V p.2) ^ (a - 2) ∂pdProcess m η := fun p =>
    lintegral_const_mul _ ((hS.add measurable_const).pow_const _)
  simp_rw [hinner]
  have hG : Measurable fun p : ℝ × M => ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * A p.2
      * ∫⁻ N, (pdSum V N + ENNReal.ofReal p.1 * V p.2) ^ (a - 2) ∂pdProcess m η := by
    refine hUW.mul ?_
    have h1 : Measurable fun q : (ℝ × M) × Measure (ℝ × M) =>
        pdSum V q.2 + ENNReal.ofReal q.1.1 * V q.1.2 :=
      (hS.comp measurable_snd).add ((ENNReal.measurable_ofReal.comp
        (measurable_fst.comp measurable_fst)).mul (hV.comp (measurable_snd.comp measurable_fst)))
    exact Measurable.lintegral_prod_right' (f := fun q : (ℝ × M) × Measure (ℝ × M) =>
      (pdSum V q.2 + ENNReal.ofReal q.1.1 * V q.1.2) ^ (a - 2)) (h1.pow_const _)
  rw [lintegral_pdIntensity m η hG]
  have hg : ∀ᵐ g ∂η, ∫⁻ u in Ioi 0, stableDensity m u
        * (ENNReal.ofReal u * ENNReal.ofReal u * A g
          * ∫⁻ N, (pdSum V N + ENNReal.ofReal u * V g) ^ (a - 2) ∂pdProcess m η)
      = ENNReal.ofReal (pdSqConst m a (stableConst m) (∫⁻ g, V g ^ m ∂η).toReal)
        * (A g * V g ^ (m - 2)) := by
    filter_upwards [hVpos] with g hg
    rw [mul_left_comm, ← lintegral_stableDensity_rpow_add_pdSum hm0 hm1 η hV hVpos hκ ham
      hg.ne']
    have h1 : Measurable fun q : ℝ × Measure (ℝ × M) =>
        pdSum V q.2 + ENNReal.ofReal q.1 * V g :=
      (hS.comp measurable_snd).add ((ENNReal.measurable_ofReal.comp measurable_fst).mul
        measurable_const)
    have hmeas : Measurable fun u : ℝ => stableDensity m u * (ENNReal.ofReal u * ENNReal.ofReal u
        * ∫⁻ N, (pdSum V N + ENNReal.ofReal u * V g) ^ (a - 2) ∂pdProcess m η) := by
      refine (measurable_stableDensity m).mul
        ((ENNReal.measurable_ofReal.mul ENNReal.measurable_ofReal).mul ?_)
      exact Measurable.lintegral_prod_right' (f := fun q : ℝ × Measure (ℝ × M) =>
        (pdSum V q.2 + ENNReal.ofReal q.1 * V g) ^ (a - 2)) (h1.pow_const _)
    rw [← lintegral_const_mul _ hmeas]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    ring
  rw [lintegral_congr_ae hg]
  exact lintegral_const_mul _ (hA.mul (hV.pow_const _))

/-- `𝔼 S_V^a = (c_m κ)^{a/m} Γ(1 - a/m) / Γ(1 - a)` for `0 < a < m`, the moment formula in
Gamma-function form. -/
theorem lintegral_pdSum_rpow_eq_Gamma {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {V : M → ℝ≥0∞} (hV : Measurable V)
    (hκ : ∫⁻ g, V g ^ m ∂η ≠ ∞) {a : ℝ} (ha0 : 0 < a) (ham : a < m) :
    ∫⁻ N, pdSum V N ^ a ∂pdProcess m η
      = ENNReal.ofReal ((stableConst m * (∫⁻ g, V g ^ m ∂η).toReal) ^ (a / m)
          * Real.Gamma (1 - a / m) / Real.Gamma (1 - a)) := by
  have hc : 0 < stableConst m := stableConst_pos hm0 hm1
  have hq : 0 < a / m := div_pos ha0 hm0
  have hq1 : a / m < 1 := (div_lt_one hm0).2 ham
  have hca : 0 < stableConst a := stableConst_pos ha0 (ham.trans hm1)
  have hcq : 0 < stableConst (a / m) := stableConst_pos hq hq1
  have hΓa : Real.Gamma (1 - a) = a * stableConst a :=
    (mul_stableConst_eq_Gamma ha0 (ham.trans hm1)).symm
  have hΓq : Real.Gamma (1 - a / m) = a / m * stableConst (a / m) :=
    (mul_stableConst_eq_Gamma hq hq1).symm
  rw [lintegral_pdSum_rpow hm0 hm1 η hV ha0 ham]
  conv_lhs => rw [← ENNReal.ofReal_toReal hκ]
  rw [← ENNReal.ofReal_mul hc.le, ENNReal.ofReal_rpow_of_nonneg (by positivity) hq.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
  congr 1
  rw [hΓa, hΓq]
  field_simp

/-- The constant of (13.14) with exponent `a - 2`, in terms of the moment `𝔼 S_V^a`:
`K₂(a) κ = (1-m)/(1-a) · 𝔼 S_V^a`, for `0 ≤ a < m`. -/
theorem ofReal_pdSqConst_mul_lintegral {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {V : M → ℝ≥0∞} (hV : Measurable V) (hVpos : ∀ᵐ g ∂η, 0 < V g)
    (hκ : ∫⁻ g, V g ^ m ∂η ≠ ∞) {a : ℝ} (ha0 : 0 ≤ a) (ham : a < m) :
    ENNReal.ofReal (pdSqConst m a (stableConst m) (∫⁻ g, V g ^ m ∂η).toReal)
        * ∫⁻ g, V g ^ m ∂η
      = ENNReal.ofReal ((1 - m) / (1 - a)) * ∫⁻ N, pdSum V N ^ a ∂pdProcess m η := by
  have hc : 0 < stableConst m := stableConst_pos hm0 hm1
  have hκpos : 0 < (∫⁻ g, V g ^ m ∂η).toReal :=
    ENNReal.toReal_pos (lintegral_rpow_pos_of_ae_pos hm0 η hV hVpos).ne' hκ
  have hΓm : Real.Gamma (2 - m) = (1 - m) * (m * stableConst m) := by
    rw [mul_stableConst_eq_Gamma hm0 hm1, show (2 : ℝ) - m = (1 - m) + 1 by ring,
      Real.Gamma_add_one (by linarith)]
  have hΓa : Real.Gamma (2 - a) = (1 - a) * Real.Gamma (1 - a) := by
    rw [show (2 : ℝ) - a = (1 - a) + 1 by ring, Real.Gamma_add_one (by linarith)]
  obtain ⟨κr, hκr0, hκr⟩ : ∃ κr : ℝ, 0 < κr ∧ (∫⁻ g, V g ^ m ∂η).toReal = κr := ⟨_, hκpos, rfl⟩
  have hκe : ∫⁻ g, V g ^ m ∂η = ENNReal.ofReal κr := by rw [← hκr, ENNReal.ofReal_toReal hκ]
  rcases eq_or_lt_of_le ha0 with rfl | ha0'
  · -- `a = 0`
    simp only [ENNReal.rpow_zero, lintegral_const, measure_univ, mul_one, sub_zero, div_one]
    rw [hκr, hκe, ← ENNReal.ofReal_mul (by
      unfold pdSqConst
      exact div_nonneg (mul_nonneg (mul_nonneg (Real.Gamma_nonneg_of_nonneg (by linarith))
        (Real.Gamma_nonneg_of_nonneg (by norm_num))) (Real.rpow_nonneg (by positivity) _))
        (mul_nonneg hm0.le (Real.Gamma_nonneg_of_nonneg (by norm_num))))]
    congr 1
    rw [pdSqConst, hΓm]
    simp only [zero_div, sub_zero, Real.Gamma_one, zero_sub, Real.rpow_neg_one,
      show (2 : ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one one_ne_zero, one_mul]
    field_simp
  · -- `a > 0`
    rw [lintegral_pdSum_rpow_eq_Gamma hm0 hm1 η hV hκ ha0' ham, hκr, hκe,
      ← ENNReal.ofReal_mul (by
        unfold pdSqConst
        exact div_nonneg (mul_nonneg (mul_nonneg (Real.Gamma_nonneg_of_nonneg (by linarith))
          (Real.Gamma_nonneg_of_nonneg (by rw [sub_nonneg]; exact (div_le_one hm0).2 ham.le)))
          (Real.rpow_nonneg (by positivity) _)) (mul_nonneg hm0.le
            (Real.Gamma_nonneg_of_nonneg (by linarith)))),
      ← ENNReal.ofReal_mul (div_nonneg (by linarith) (by linarith))]
    congr 1
    have hΓa' : 0 < Real.Gamma (1 - a) := Real.Gamma_pos_of_pos (by linarith)
    rw [pdSqConst, hΓm, hΓa, div_mul_eq_mul_div,
      Real.rpow_sub_one (by positivity : stableConst m * κr ≠ 0)]
    field_simp

/-! ### Identity (14.27): one insertion, general exponent -/

/-- The constant of the one-insertion identity with exponent `a - 1`:
`K₁(a) = Γ(1-m) Γ(1-a/m) (c_m κ)^{a/m-1} / (m Γ(1-a))`. At `a = 0` it is `1/κ`, which is the
constant of `lintegral_pdSum_mul_inv_pdSum`. -/
def pdOneConst (m a c κ : ℝ) : ℝ :=
  Real.Gamma (1 - m) * Real.Gamma (1 - a / m) * (c * κ) ^ (a / m - 1) / (m * Real.Gamma (1 - a))

omit [Nonempty M] in
lemma pdOneConst_nonneg {m a c κ : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (ham : a < m) (hc : 0 < c)
    (hκ : 0 < κ) : 0 ≤ pdOneConst m a c κ := by
  unfold pdOneConst
  exact div_nonneg (mul_nonneg (mul_nonneg (Real.Gamma_nonneg_of_nonneg (by linarith))
    (Real.Gamma_nonneg_of_nonneg (by rw [sub_nonneg]; exact (div_le_one hm0).2 ham.le)))
    (Real.rpow_nonneg (by positivity) _))
    (mul_nonneg hm0.le (Real.Gamma_nonneg_of_nonneg (by linarith)))

/-- The mark-wise computation behind (14.27) with one insertion and exponent `a - 1`: for a weight
`x ∈ (0, ∞]`, `∫₀^∞ u^{-m-1} u 𝔼 (S_V + u x)^{a-1} du = K₁(a) x^{m-1}`. -/
lemma lintegral_stableDensity_rpow_add_pdSum_one {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1)
    (η : Measure M) [IsProbabilityMeasure η] {V : M → ℝ≥0∞} (hV : Measurable V)
    (hVpos : ∀ᵐ g ∂η, 0 < V g) (hκ : ∫⁻ g, V g ^ m ∂η ≠ ∞) {a : ℝ} (ham : a < m)
    {x : ℝ≥0∞} (hx0 : x ≠ 0) :
    ∫⁻ u in Ioi 0, stableDensity m u * (ENNReal.ofReal u
        * ∫⁻ N, (pdSum V N + ENNReal.ofReal u * x) ^ (a - 1) ∂pdProcess m η)
      = ENNReal.ofReal (pdOneConst m a (stableConst m) (∫⁻ g, V g ^ m ∂η).toReal)
        * x ^ (m - 1) := by
  have hc : 0 < stableConst m := stableConst_pos hm0 hm1
  have hκpos : 0 < (∫⁻ g, V g ^ m ∂η).toReal :=
    ENNReal.toReal_pos (lintegral_rpow_pos_of_ae_pos hm0 η hV hVpos).ne' hκ
  obtain ⟨κr, hκr0, hκr⟩ : ∃ κr : ℝ, 0 < κr ∧ (∫⁻ g, V g ^ m ∂η).toReal = κr := ⟨_, hκpos, rfl⟩
  rw [hκr]
  have hb : 0 < 1 - a := by linarith
  have hΓb : 0 < Real.Gamma (1 - a) := Real.Gamma_pos_of_pos hb
  have hexp : ∀ u : ℝ, 0 < u → ∀ N : Measure (ℝ × M),
      (pdSum V N + ENNReal.ofReal u * x) ^ (a - 1)
        = (pdSum V N + ENNReal.ofReal u * x) ^ (-(1 - a)) := by
    intro u _ N
    rw [neg_sub]
  have hinner : ∀ u ∈ Ioi (0 : ℝ),
      ∫⁻ N, (pdSum V N + ENNReal.ofReal u * x) ^ (a - 1) ∂pdProcess m η
        = (ENNReal.ofReal (Real.Gamma (1 - a)))⁻¹
          * ∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ (1 - a - 1))
            * ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * x)))
            * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr))) := by
    intro u hu
    rw [mem_Ioi] at hu
    simp_rw [hexp u hu]
    rw [lintegral_rpow_neg_add_pdSum hm0 hm1 η hV hκ hb
      (mul_ne_zero (ENNReal.ofReal_pos.2 hu).ne' hx0), hκr]
  rw [setLIntegral_congr_fun measurableSet_Ioi fun u hu => by rw [hinner u hu]]
  rcases eq_or_ne x ∞ with rfl | hx
  · -- an infinite weight contributes nothing
    rw [ENNReal.top_rpow_of_neg (by linarith), mul_zero]
    refine (setLIntegral_congr_fun (g := fun _ => (0 : ℝ≥0∞)) measurableSet_Ioi
      fun u hu => ?_).trans lintegral_zero
    rw [mem_Ioi] at hu
    have : ∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ (1 - a - 1))
        * ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ∞)))
        * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr))) = 0 := by
      refine (setLIntegral_congr_fun (g := fun _ => (0 : ℝ≥0∞)) measurableSet_Ioi
        fun s hs => ?_).trans lintegral_zero
      rw [mem_Ioi] at hs
      rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hu).ne',
        ENNReal.mul_top (ENNReal.ofReal_pos.2 hs).ne', negExp_top, ENNReal.ofReal_zero, mul_zero,
        zero_mul]
    rw [this, mul_zero, mul_zero, mul_zero]
  obtain ⟨v, hv, rfl⟩ : ∃ v : ℝ, 0 < v ∧ x = ENNReal.ofReal v :=
    ⟨x.toReal, ENNReal.toReal_pos hx0 hx, (ENNReal.ofReal_toReal hx).symm⟩
  -- pull the constant out and Tonelli in `(u, s)`
  have hjoint : Measurable fun q : ℝ × ℝ => stableDensity m q.1 * (ENNReal.ofReal q.1
      * (ENNReal.ofReal (q.2 ^ (1 - a - 1))
        * ENNReal.ofReal (negExp (ENNReal.ofReal q.2 * (ENNReal.ofReal q.1 * ENNReal.ofReal v)))
        * ENNReal.ofReal (Real.exp (-(q.2 ^ m * stableConst m * κr))))) := by
    refine ((measurable_stableDensity m).comp measurable_fst).mul
      ((ENNReal.measurable_ofReal.comp measurable_fst).mul
        (((ENNReal.measurable_ofReal.comp (measurable_snd.pow_const _)).mul
          (ENNReal.measurable_ofReal.comp (measurable_negExp.comp
            ((ENNReal.measurable_ofReal.comp measurable_snd).mul
              ((ENNReal.measurable_ofReal.comp measurable_fst).mul measurable_const))))).mul
          (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_))))
    exact ((measurable_snd.pow_const m).mul_const _).mul_const _ |>.neg
  have hpull : ∀ u ∈ Ioi (0 : ℝ), stableDensity m u * (ENNReal.ofReal u
      * ((ENNReal.ofReal (Real.Gamma (1 - a)))⁻¹
        * ∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ (1 - a - 1))
          * ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ENNReal.ofReal v)))
          * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr)))))
      = (ENNReal.ofReal (Real.Gamma (1 - a)))⁻¹
        * ∫⁻ s in Ioi 0, stableDensity m u * (ENNReal.ofReal u
          * (ENNReal.ofReal (s ^ (1 - a - 1))
            * ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ENNReal.ofReal v)))
            * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr))))) := by
    intro u _
    have hmeas_u : Measurable fun s : ℝ => ENNReal.ofReal (s ^ (1 - a - 1))
        * ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ENNReal.ofReal v)))
          * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr))) :=
      ((ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul
        (ENNReal.measurable_ofReal.comp (measurable_negExp.comp
          (ENNReal.measurable_ofReal.mul_const _)))).mul (ENNReal.measurable_ofReal.comp
            (Real.measurable_exp.comp
              ((((measurable_id.pow_const m).mul_const _).mul_const _).neg)))
    have hR : Measurable fun s : ℝ => stableDensity m u * (ENNReal.ofReal u
        * (ENNReal.ofReal (s ^ (1 - a - 1))
          * ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ENNReal.ofReal v)))
          * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr))))) :=
      (hmeas_u.const_mul _).const_mul _
    rw [← lintegral_const_mul _ hR, ← lintegral_const_mul _ hmeas_u,
      ← lintegral_const_mul _ (hmeas_u.const_mul _),
      ← lintegral_const_mul _ ((hmeas_u.const_mul _).const_mul _)]
    refine lintegral_congr fun s => ?_
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hpull, lintegral_const_mul _
    (Measurable.lintegral_prod_right' hjoint),
    lintegral_lintegral_swap (f := fun u s => stableDensity m u * (ENNReal.ofReal u
      * (ENNReal.ofReal (s ^ (1 - a - 1))
        * ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ENNReal.ofReal v)))
        * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr)))))) hjoint.aemeasurable]
  -- the `u`-integral is a Gamma integral
  have hu_int : ∀ s ∈ Ioi (0 : ℝ), ∫⁻ u in Ioi 0, stableDensity m u * (ENNReal.ofReal u
      * (ENNReal.ofReal (s ^ (1 - a - 1))
        * ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ENNReal.ofReal v)))
        * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr)))))
      = ENNReal.ofReal (v ^ (m - 1) * Real.Gamma (1 - m))
        * ENNReal.ofReal (s ^ (m - a - 1) * Real.exp (-((stableConst m * κr) * s ^ m))) := by
    intro s hs
    rw [mem_Ioi] at hs
    have hmeas : Measurable fun u : ℝ => stableDensity m u * (ENNReal.ofReal u
        * ENNReal.ofReal (negExp (ENNReal.ofReal s
          * (ENNReal.ofReal u * ENNReal.ofReal v)))) :=
      (measurable_stableDensity m).mul (ENNReal.measurable_ofReal.mul
        (ENNReal.measurable_ofReal.comp (measurable_negExp.comp
          (measurable_const.mul (ENNReal.measurable_ofReal.mul measurable_const)))))
    have hpt : ∀ u, stableDensity m u * (ENNReal.ofReal u
        * (ENNReal.ofReal (s ^ (1 - a - 1))
          * ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal u * ENNReal.ofReal v)))
          * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr)))))
        = (ENNReal.ofReal (s ^ (1 - a - 1))
            * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr))))
          * (stableDensity m u * (ENNReal.ofReal u
            * ENNReal.ofReal (negExp (ENNReal.ofReal s
              * (ENNReal.ofReal u * ENNReal.ofReal v))))) := fun u => by ring
    simp_rw [hpt]
    rw [lintegral_const_mul _ hmeas, lintegral_stableDensity_mul_negExp hm1 hs hv,
      Real.mul_rpow hs.le hv.le, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _),
      ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hs.le _) (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hv.le _) (Real.Gamma_nonneg_of_nonneg
        (by linarith)))]
    congr 1
    have : s ^ (m - a - 1) = s ^ (1 - a - 1) * s ^ (m - 1) := by
      rw [← Real.rpow_add hs]; ring_nf
    rw [this]
    ring_nf
  have hmeas_s : Measurable fun s : ℝ =>
      ENNReal.ofReal (s ^ (m - a - 1) * Real.exp (-((stableConst m * κr) * s ^ m))) :=
    ENNReal.measurable_ofReal.comp ((measurable_id.pow_const _).mul
      (Real.measurable_exp.comp (((measurable_id.pow_const m).const_mul _).neg)))
  rw [setLIntegral_congr_fun measurableSet_Ioi hu_int, lintegral_const_mul _ hmeas_s,
    lintegral_rpow_mul_exp_neg_mul_rpow_Ioi' hm0 (by linarith : 0 < m - a) (mul_pos hc hκr0),
    ENNReal.ofReal_rpow_of_pos hv, ← ENNReal.ofReal_inv_of_pos hΓb,
    ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hv.le _)
      (Real.Gamma_nonneg_of_nonneg (by linarith))),
    ← ENNReal.ofReal_mul (inv_nonneg.2 hΓb.le)]
  rw [← ENNReal.ofReal_mul (pdOneConst_nonneg hm0 hm1 ham hc hκr0)]
  congr 1
  have h1 : (m - a) / m = 1 - a / m := by field_simp
  have h2 : (1 / (stableConst m * κr)) ^ (1 - a / m)
      = (stableConst m * κr) ^ (a / m - 1) := by
    rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), neg_sub]
  rw [pdOneConst, h1, h2]
  ring

/-- **Identity (14.27) at one level**, `a < m`:
`𝔼 (∑_α u_α A(g_α)) (∑_α u_α V(g_α))^{a-1} = K₁(a) ∫ A V^{m-1} dη`.
At `a = 0` this is `lintegral_pdSum_mul_inv_pdSum`; at `A = V` it is the moment formula
`lintegral_pdSum_rpow_eq_Gamma`. -/
theorem lintegral_pdSum_mul_rpow_pdSum {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {A V : M → ℝ≥0∞} (hA : Measurable A) (hV : Measurable V)
    (hVpos : ∀ᵐ g ∂η, 0 < V g) (hκ : ∫⁻ g, V g ^ m ∂η ≠ ∞) {a : ℝ} (ham : a < m) :
    ∫⁻ N, pdSum A N * (pdSum V N) ^ (a - 1) ∂pdProcess m η
      = ENNReal.ofReal (pdOneConst m a (stableConst m) (∫⁻ g, V g ^ m ∂η).toReal)
        * ∫⁻ g, A g * V g ^ (m - 1) ∂η := by
  have hS := measurable_pdSum (v := V) hV
  have hUW : Measurable fun p : ℝ × M => ENNReal.ofReal p.1 * A p.2 := measurable_ofReal_mul hA
  -- the Mecke formula
  have hf : Measurable fun q : (ℝ × M) × Measure (ℝ × M) =>
      ENNReal.ofReal q.1.1 * A q.1.2 * (pdSum V q.2) ^ (a - 1) :=
    (hUW.comp measurable_fst).mul ((hS.comp measurable_snd).pow_const _)
  have hF : ∀ N : Measure (ℝ × M),
      ∫⁻ p, ENNReal.ofReal p.1 * A p.2 * (pdSum V N) ^ (a - 1) ∂N
        = pdSum A N * (pdSum V N) ^ (a - 1) :=
    fun N => lintegral_mul_const _ hUW
  have hFm : Measurable fun N : Measure (ℝ × M) =>
      ∫⁻ p, ENNReal.ofReal p.1 * A p.2 * (pdSum V N) ^ (a - 1) ∂N := by
    simp_rw [hF]
    exact (measurable_pdSum hA).mul (hS.pow_const _)
  have hM : ∫⁻ N, ∫⁻ p, ENNReal.ofReal p.1 * A p.2 * (pdSum V N) ^ (a - 1) ∂N ∂pdProcess m η
      = ∫⁻ N, ∫⁻ p, ENNReal.ofReal p.1 * A p.2
          * (pdSum V (N + Measure.dirac p)) ^ (a - 1) ∂pdIntensity m η ∂pdProcess m η :=
    lintegral_lintegral_pdProcess m η hf hFm
  simp_rw [hF] at hM
  rw [hM]
  simp_rw [pdSum_add_dirac hV]
  -- Tonelli in `(N, p)`
  have hjoint : Measurable fun q : Measure (ℝ × M) × (ℝ × M) =>
      ENNReal.ofReal q.2.1 * A q.2.2
        * (pdSum V q.1 + ENNReal.ofReal q.2.1 * V q.2.2) ^ (a - 1) := by
    have h1 : Measurable fun q : Measure (ℝ × M) × (ℝ × M) =>
        pdSum V q.1 + ENNReal.ofReal q.2.1 * V q.2.2 :=
      (hS.comp measurable_fst).add ((ENNReal.measurable_ofReal.comp
        (measurable_fst.comp measurable_snd)).mul (hV.comp (measurable_snd.comp measurable_snd)))
    exact (hUW.comp measurable_snd).mul (h1.pow_const _)
  have hswap := lintegral_lintegral_swap (μ := pdProcess m η) (ν := pdIntensity m η)
    (f := fun N p => ENNReal.ofReal p.1 * A p.2
      * (pdSum V N + ENNReal.ofReal p.1 * V p.2) ^ (a - 1)) hjoint.aemeasurable
  rw [hswap]
  have hinner : ∀ p : ℝ × M, ∫⁻ N, ENNReal.ofReal p.1 * A p.2
        * (pdSum V N + ENNReal.ofReal p.1 * V p.2) ^ (a - 1) ∂pdProcess m η
      = ENNReal.ofReal p.1 * A p.2
        * ∫⁻ N, (pdSum V N + ENNReal.ofReal p.1 * V p.2) ^ (a - 1) ∂pdProcess m η := fun p =>
    lintegral_const_mul _ ((hS.add measurable_const).pow_const _)
  simp_rw [hinner]
  have hG : Measurable fun p : ℝ × M => ENNReal.ofReal p.1 * A p.2
      * ∫⁻ N, (pdSum V N + ENNReal.ofReal p.1 * V p.2) ^ (a - 1) ∂pdProcess m η := by
    refine hUW.mul ?_
    have h1 : Measurable fun q : (ℝ × M) × Measure (ℝ × M) =>
        pdSum V q.2 + ENNReal.ofReal q.1.1 * V q.1.2 :=
      (hS.comp measurable_snd).add ((ENNReal.measurable_ofReal.comp
        (measurable_fst.comp measurable_fst)).mul (hV.comp (measurable_snd.comp measurable_fst)))
    exact Measurable.lintegral_prod_right' (f := fun q : (ℝ × M) × Measure (ℝ × M) =>
      (pdSum V q.2 + ENNReal.ofReal q.1.1 * V q.1.2) ^ (a - 1)) (h1.pow_const _)
  rw [lintegral_pdIntensity m η hG]
  have hg : ∀ᵐ g ∂η, ∫⁻ u in Ioi 0, stableDensity m u
        * (ENNReal.ofReal u * A g
          * ∫⁻ N, (pdSum V N + ENNReal.ofReal u * V g) ^ (a - 1) ∂pdProcess m η)
      = ENNReal.ofReal (pdOneConst m a (stableConst m) (∫⁻ g, V g ^ m ∂η).toReal)
        * (A g * V g ^ (m - 1)) := by
    filter_upwards [hVpos] with g hg
    rw [mul_left_comm, ← lintegral_stableDensity_rpow_add_pdSum_one hm0 hm1 η hV hVpos hκ ham
      hg.ne']
    have h1 : Measurable fun q : ℝ × Measure (ℝ × M) =>
        pdSum V q.2 + ENNReal.ofReal q.1 * V g :=
      (hS.comp measurable_snd).add ((ENNReal.measurable_ofReal.comp measurable_fst).mul
        measurable_const)
    have hmeas : Measurable fun u : ℝ => stableDensity m u * (ENNReal.ofReal u
        * ∫⁻ N, (pdSum V N + ENNReal.ofReal u * V g) ^ (a - 1) ∂pdProcess m η) := by
      refine (measurable_stableDensity m).mul (ENNReal.measurable_ofReal.mul ?_)
      exact Measurable.lintegral_prod_right' (f := fun q : ℝ × Measure (ℝ × M) =>
        (pdSum V q.2 + ENNReal.ofReal q.1 * V g) ^ (a - 1)) (h1.pow_const _)
    rw [← lintegral_const_mul _ hmeas]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    ring
  rw [lintegral_congr_ae hg]
  exact lintegral_const_mul _ (hA.mul (hV.pow_const _))

end ProbabilityTheory

end
