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

`𝔼 (∑_{α ≠ γ} v_α v_γ U_α W_γ) / (∑_α v_α V_α)²
  = m (𝔼 [U V^{m-1}] / 𝔼 V^m)(𝔼 [W V^{m-1}] / 𝔼 V^m)`  (13.15)

`𝔼 (∑_α v_α U_α)(∑_α v_α W_α) / (∑_α v_α V_α)² = (13.14) + (13.15)`  (13.16)

and in particular `𝔼 ∑_α v_α² = 1 - m` (13.17). Talagrand derives them by differentiating
Theorem 13.1.5 and calls the justification "tedious"; here they are direct consequences of the
**Mecke formula** (`lintegral_lintegral_poissonPointProcess`): the sum over the points becomes an
integral against the intensity `μ_m ⊗ η`, the added point contributes `u V(g)` to the
denominator, `(S + a)^{-1} = ∫₀^∞ e^{-s(S+a)} ds` turns the denominator into the Laplace
transform of `S`, and the `u`- and `s`-integrals are Gamma integrals, with `m c_m = Γ(1 - m)`
(`mul_stableConst_eq_Gamma`).

The identities (13.15) and (13.16) are second order: they need the **bivariate Mecke equation**
(`lintegral_lintegral_lintegral_pdProcess`), whose two terms are exactly the sum over pairs of
distinct points and the diagonal.  Both are proved here with a *free* exponent `a - 2` in place of
the normalizer's `-2`, since that is the form the higher levels of a Poisson–Dirichlet cascade
need, and the exponent `a = 0` then recovers Talagrand's statements.

## Main statements

- `ENNReal.inv_eq_lintegral_negExp`, `ENNReal.inv_mul_inv_eq_lintegral_mul_negExp`: the Laplace
  representations of `x⁻¹` and `x⁻²`, valid for every `x : ℝ≥0∞`.
- `ProbabilityTheory.lintegral_pdSum_mul_inv_pdSum`: **(13.13)** in `ℝ≥0∞`.
- `ProbabilityTheory.lintegral_pdSumSq_mul_inv_pdSum_sq`: **(13.14)** in `ℝ≥0∞`.
- `ProbabilityTheory.lintegral_superOffDiagSum_mul_inv_pdSum_sq`: **(13.15)** in `ℝ≥0∞`, the sum
  being over ordered pairs of *distinct* points (`superOffDiagSum`, on the sample space, since
  `α ≠ γ` refers to the indices of the points), with no finiteness hypothesis on `U`, `W`: it
  comes from the off-diagonal bivariate Mecke equation, not from a cancellation.
- `ProbabilityTheory.lintegral_pdSum_mul_pdSum_mul_inv_pdSum_sq`: **(13.16)** in `ℝ≥0∞`.
- `ProbabilityTheory.lintegral_pdSumSq_mul_inv_pdSum_one_sq`: **(13.17)**, `𝔼 ∑ v_α² = 1 - m`.

With a free exponent `a < m`, for the cascade:

- `ProbabilityTheory.lintegral_pdSum_mul_rpow_pdSum`: one insertion, **(14.27)**.
- `ProbabilityTheory.lintegral_pdSumSq_mul_rpow_pdSum`: the diagonal, (13.14) at exponent `a - 2`.
- `ProbabilityTheory.lintegral_pdSum_sq_mul_rpow_pdSum`,
  `ProbabilityTheory.lintegral_pdSum_mul_pdSum_mul_rpow_pdSum`: the second-order identity for one
  and for two numerators.
- `ProbabilityTheory.lintegral_pdSumPair_mul_rpow_pdSum`: the second-order identity for a genuine
  function of the *pair* of marks.
- `ProbabilityTheory.lintegral_superOffDiagSumPair_mul_rpow_pdSum`,
  `ProbabilityTheory.lintegral_superOffDiagSum_mul_rpow_pdSum`: the **off-diagonal** one-level
  identity, over pairs of *distinct* points, for a pair function and for a product numerator.
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

/-- **The bivariate Mecke equation for the Poisson–Dirichlet point process**: the double sum over
pairs of points splits into its off-diagonal and diagonal parts. -/
theorem lintegral_lintegral_lintegral_pdProcess (m : ℝ) (η : Measure M) [IsFiniteMeasure η]
    {f : (ℝ × M) × (ℝ × M) × Measure (ℝ × M) → ℝ≥0∞} (hf : Measurable f)
    (hF : Measurable fun N : Measure (ℝ × M) => ∫⁻ p, ∫⁻ q, f (p, q, N) ∂N ∂N)
    (hg : Measurable fun r : (ℝ × M) × Measure (ℝ × M) => ∫⁻ q, f (r.1, q, r.2) ∂r.2)
    (hg' : Measurable fun r : (ℝ × M) × Measure (ℝ × M) =>
      ∫⁻ q, f (r.1, q, r.2 + Measure.dirac r.1) ∂r.2) :
    ∫⁻ N, ∫⁻ p, ∫⁻ q, f (p, q, N) ∂N ∂N ∂pdProcess m η
      = (∫⁻ N, ∫⁻ p, ∫⁻ q, f (p, q, N + Measure.dirac p + Measure.dirac q)
            ∂pdIntensity m η ∂pdIntensity m η ∂pdProcess m η)
        + ∫⁻ N, ∫⁻ p, f (p, p, N + Measure.dirac p) ∂pdIntensity m η ∂pdProcess m η := by
  rw [← sum_pdSeq m η]
  exact lintegral_lintegral_lintegral_poissonPointProcessSum (pdSeq m η) hf hF hg hg'

omit [Nonempty M] in
/-- Almost every point of the stable intensity has a positive weight. -/
lemma ae_stableIntensity_pos (m : ℝ) : ∀ᵐ u ∂stableIntensity m, 0 < u := by
  rw [stableIntensity]
  exact (ae_restrict_mem measurableSet_Ioi).filter_mono
    (withDensity_absolutelyContinuous _ _).ae_le

omit [Nonempty M] in
/-- Almost every point of the Poisson–Dirichlet intensity carries a nonzero weight, when the
marks do. -/
lemma ae_pdIntensity_ne_zero {m : ℝ} (η : Measure M) [SFinite η] {V : M → ℝ≥0∞}
    (hV : Measurable V) (hVpos : ∀ᵐ g ∂η, 0 < V g) :
    ∀ᵐ p ∂pdIntensity m η, ENNReal.ofReal p.1 * V p.2 ≠ 0 := by
  have hmeasS : MeasurableSet {p : ℝ × M | ENNReal.ofReal p.1 * V p.2 ≠ 0} :=
    ((ENNReal.measurable_ofReal.comp measurable_fst).mul (hV.comp measurable_snd))
      (measurableSet_singleton (0 : ℝ≥0∞)).compl
  rw [pdIntensity, Measure.ae_prod_iff_ae_ae hmeasS]
  filter_upwards [ae_stableIntensity_pos m] with u hu
  filter_upwards [hVpos] with g hg
  exact mul_ne_zero (ENNReal.ofReal_pos.2 hu).ne' hg.ne'

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

/-! ### The first-order Palm–Campbell transform -/

omit [Nonempty M] in
/-- **The first-order Palm–Campbell transform of the Poisson–Dirichlet intensity**: for `s > 0`,

`∫ u U(g) e^{-s u V(g)} dΛ_m(u) dη(g) = s^{m-1} Γ(1-m) ∫ U V^{m-1} dη`.

This is the mark-integrated form of `lintegral_stableDensity_mul_negExp`; it is what turns the
off-diagonal term of the bivariate Mecke equation into the square of a first-order quantity. -/
lemma lintegral_pdIntensity_mul_negExp {m : ℝ} (hm1 : m < 1) (η : Measure M) [SFinite η]
    {U V : M → ℝ≥0∞} (hU : Measurable U) (hV : Measurable V) (hVpos : ∀ᵐ g ∂η, 0 < V g)
    {s : ℝ} (hs : 0 < s) :
    ∫⁻ p, ENNReal.ofReal p.1 * U p.2
        * ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal p.1 * V p.2)))
        ∂pdIntensity m η
      = ENNReal.ofReal (s ^ (m - 1) * Real.Gamma (1 - m)) * ∫⁻ g, U g * V g ^ (m - 1) ∂η := by
  have hm1' : m - 1 < 0 := by linarith
  have hmeas : Measurable fun p : ℝ × M => ENNReal.ofReal p.1 * U p.2
      * ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal p.1 * V p.2))) :=
    ((ENNReal.measurable_ofReal.comp measurable_fst).mul (hU.comp measurable_snd)).mul
      (ENNReal.measurable_ofReal.comp (measurable_negExp.comp (measurable_const.mul
        ((ENNReal.measurable_ofReal.comp measurable_fst).mul (hV.comp measurable_snd)))))
  have hUV : Measurable fun g => U g * V g ^ (m - 1) := hU.mul (hV.pow_const _)
  rw [lintegral_pdIntensity m η hmeas, ← lintegral_const_mul _ hUV]
  refine lintegral_congr_ae ?_
  filter_upwards [hVpos] with g hg
  rcases eq_or_ne (V g) ∞ with hinf | hinf
  · -- an infinite mark contributes nothing to either side
    rw [hinf, ENNReal.top_rpow_of_neg hm1', mul_zero, mul_zero]
    refine (setLIntegral_congr_fun (g := fun _ => (0 : ℝ≥0∞)) measurableSet_Ioi
      fun u hu => ?_).trans lintegral_zero
    rw [mem_Ioi] at hu
    rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hu).ne',
      ENNReal.mul_top (ENNReal.ofReal_pos.2 hs).ne', negExp_top, ENNReal.ofReal_zero, mul_zero,
      mul_zero]
  · obtain ⟨v, hv, hveq⟩ : ∃ v : ℝ, 0 < v ∧ V g = ENNReal.ofReal v :=
      ⟨(V g).toReal, ENNReal.toReal_pos hg.ne' hinf, (ENNReal.ofReal_toReal hinf).symm⟩
    have hmeas' : Measurable fun u : ℝ => stableDensity m u * (ENNReal.ofReal u
        * ENNReal.ofReal (negExp (ENNReal.ofReal s
          * (ENNReal.ofReal u * ENNReal.ofReal v)))) :=
      (measurable_stableDensity m).mul (ENNReal.measurable_ofReal.mul
        (ENNReal.measurable_ofReal.comp (measurable_negExp.comp (measurable_const.mul
          (ENNReal.measurable_ofReal.mul measurable_const)))))
    rw [hveq]
    have hpt : ∀ u : ℝ, stableDensity m u * (ENNReal.ofReal u * U g
        * ENNReal.ofReal (negExp (ENNReal.ofReal s
          * (ENNReal.ofReal u * ENNReal.ofReal v))))
        = U g * (stableDensity m u * (ENNReal.ofReal u
          * ENNReal.ofReal (negExp (ENNReal.ofReal s
            * (ENNReal.ofReal u * ENNReal.ofReal v))))) := fun u => by ring
    simp_rw [hpt]
    rw [lintegral_const_mul _ hmeas', lintegral_stableDensity_mul_negExp hm1 hs hv,
      ENNReal.ofReal_rpow_of_pos hv, Real.mul_rpow hs.le hv.le,
      show s ^ (m - 1) * v ^ (m - 1) * Real.Gamma (1 - m)
        = s ^ (m - 1) * Real.Gamma (1 - m) * v ^ (m - 1) by ring,
      ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hs.le _)
        (Real.Gamma_nonneg_of_nonneg (by linarith)))]
    ring

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

/-! ### The off-diagonal term of the bivariate Mecke equation -/

/-- The constant of the off-diagonal term with exponent `a - 2`:
`K₀(a) = Γ(1-m)² Γ(2-a/m) (c_m κ)^{a/m-2} / (m Γ(2-a))`. -/
def pdOffConst (m a c κ : ℝ) : ℝ :=
  Real.Gamma (1 - m) ^ 2 * Real.Gamma (2 - a / m) * (c * κ) ^ (a / m - 2)
    / (m * Real.Gamma (2 - a))

omit [Nonempty M] in
/-- **The `s`-integral of the off-diagonal term**: after the negative-power representation and the
Palm–Campbell transform, the off-diagonal term of the bivariate Mecke equation reduces to a single
Gamma integral, with the constant `pdOffConst`. -/
lemma lintegral_offDiag_gamma {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) {κr : ℝ} (hκr : 0 < κr)
    {a : ℝ} (ham : a < m) (J : ℝ≥0∞) :
    (ENNReal.ofReal (Real.Gamma (2 - a)))⁻¹
        * ∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ (1 - a))
            * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr)))
            * (ENNReal.ofReal (s ^ (m - 1) * Real.Gamma (1 - m)) ^ 2 * J)
      = ENNReal.ofReal (pdOffConst m a (stableConst m) κr) * J := by
  have hc : 0 < stableConst m := stableConst_pos hm0 hm1
  have ha1 : a < 1 := lt_trans ham hm1
  have hΓb : 0 < Real.Gamma (2 - a) := Real.Gamma_pos_of_pos (by linarith)
  have hΓm : 0 ≤ Real.Gamma (1 - m) := Real.Gamma_nonneg_of_nonneg (by linarith)
  have hb : (0 : ℝ) < 2 * m - a := by linarith
  -- the integrand is a constant times a single Gamma integrand
  have hpt : ∀ s ∈ Ioi (0 : ℝ), ENNReal.ofReal (s ^ (1 - a))
        * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr)))
        * (ENNReal.ofReal (s ^ (m - 1) * Real.Gamma (1 - m)) ^ 2 * J)
      = (ENNReal.ofReal (Real.Gamma (1 - m) ^ 2) * J)
        * ENNReal.ofReal (s ^ (2 * m - a - 1)
            * Real.exp (-(stableConst m * κr * s ^ m))) := by
    intro s hs
    rw [mem_Ioi] at hs
    have hsq : (s ^ (m - 1)) ^ (2 : ℕ) = s ^ (2 * m - 2) := by
      rw [← Real.rpow_natCast (s ^ (m - 1)) 2, ← Real.rpow_mul hs.le]
      norm_num
      ring_nf
    have hadd : s ^ (1 - a) * s ^ (2 * m - 2) = s ^ (2 * m - a - 1) := by
      rw [← Real.rpow_add hs]
      ring_nf
    have hE : (-(s ^ m * stableConst m * κr)) = -(stableConst m * κr * s ^ m) := by ring
    -- the real-number identity behind the pointwise rewrite
    have hreal : s ^ (1 - a) * Real.exp (-(s ^ m * stableConst m * κr))
          * (s ^ (m - 1) * Real.Gamma (1 - m)) ^ 2
        = Real.Gamma (1 - m) ^ 2 * (s ^ (2 * m - a - 1)
            * Real.exp (-(stableConst m * κr * s ^ m))) := by
      rw [mul_pow, hsq, hE, ← hadd]
      ring
    -- pull the square inside `ENNReal.ofReal` and separate `J`
    have key : ENNReal.ofReal (s ^ (1 - a))
          * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr)))
          * (ENNReal.ofReal (s ^ (m - 1) * Real.Gamma (1 - m)) ^ 2 * J)
        = (ENNReal.ofReal (s ^ (1 - a))
            * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr)))
            * ENNReal.ofReal ((s ^ (m - 1) * Real.Gamma (1 - m)) ^ 2)) * J := by
      rw [← ENNReal.ofReal_pow (by positivity)]
      ring
    -- merge the three real scalars, rewrite, and split off the constant
    have hcomb : ENNReal.ofReal (s ^ (1 - a))
          * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * κr)))
          * ENNReal.ofReal ((s ^ (m - 1) * Real.Gamma (1 - m)) ^ 2)
        = ENNReal.ofReal (Real.Gamma (1 - m) ^ 2)
          * ENNReal.ofReal (s ^ (2 * m - a - 1)
              * Real.exp (-(stableConst m * κr * s ^ m))) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le (1 - a)),
        ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ s ^ (1 - a)
          * Real.exp (-(s ^ m * stableConst m * κr)) by positivity),
        hreal, ENNReal.ofReal_mul (show (0 : ℝ) ≤ Real.Gamma (1 - m) ^ 2 by positivity)]
    rw [key, hcomb]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt]
  have hmeas : Measurable fun s : ℝ => ENNReal.ofReal (s ^ (2 * m - a - 1)
      * Real.exp (-(stableConst m * κr * s ^ m))) :=
    ENNReal.measurable_ofReal.comp ((measurable_id.pow_const _).mul
      (Real.measurable_exp.comp (((measurable_id.pow_const m).const_mul _).neg)))
  rw [lintegral_const_mul _ hmeas,
    show (2 : ℝ) * m - a - 1 = (2 * m - a) - 1 by ring,
    lintegral_rpow_mul_exp_neg_mul_rpow_Ioi' hm0 hb (mul_pos hc hκr)]
  -- the constant
  have hprod : (ENNReal.ofReal (Real.Gamma (2 - a)))⁻¹ * ENNReal.ofReal (Real.Gamma (1 - m) ^ 2)
        * ENNReal.ofReal (1 / m * ((1 / (stableConst m * κr)) ^ ((2 * m - a) / m)
          * Real.Gamma ((2 * m - a) / m)))
      = ENNReal.ofReal (pdOffConst m a (stableConst m) κr) := by
    have hgnn : (0 : ℝ) ≤ 1 / m * ((1 / (stableConst m * κr)) ^ ((2 * m - a) / m)
        * Real.Gamma ((2 * m - a) / m)) :=
      mul_nonneg (by positivity) (mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.Gamma_nonneg_of_nonneg (by rw [le_div_iff₀ hm0]; linarith)))
    rw [← ENNReal.ofReal_inv_of_pos hΓb,
      ← ENNReal.ofReal_mul (inv_nonneg.2 hΓb.le),
      ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 hΓb.le) (by positivity))]
    congr 1
    have h1 : (2 * m - a) / m = 2 - a / m := by field_simp
    have h2 : (1 / (stableConst m * κr)) ^ (2 - a / m)
        = (stableConst m * κr) ^ (a / m - 2) := by
      rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), neg_sub]
    rw [h1, h2, pdOffConst]
    field_simp
  calc (ENNReal.ofReal (Real.Gamma (2 - a)))⁻¹
        * (ENNReal.ofReal (Real.Gamma (1 - m) ^ 2) * J
          * ENNReal.ofReal (1 / m * ((1 / (stableConst m * κr)) ^ ((2 * m - a) / m)
            * Real.Gamma ((2 * m - a) / m))))
      = ((ENNReal.ofReal (Real.Gamma (2 - a)))⁻¹ * ENNReal.ofReal (Real.Gamma (1 - m) ^ 2)
          * ENNReal.ofReal (1 / m * ((1 / (stableConst m * κr)) ^ ((2 * m - a) / m)
            * Real.Gamma ((2 * m - a) / m)))) * J := by ring
    _ = ENNReal.ofReal (pdOffConst m a (stableConst m) κr) * J := by rw [hprod]

omit [Nonempty M] in
/-- Pulling a constant out of `pdSum`. -/
lemma lintegral_const_mul_pdSum {A : M → ℝ≥0∞} (hA : Measurable A) (N : Measure (ℝ × M))
    (r : ℝ≥0∞) : ∫⁻ p, r * (ENNReal.ofReal p.1 * A p.2) ∂N = r * pdSum A N :=
  lintegral_const_mul _ (measurable_ofReal_mul hA)

/-- **The off-diagonal term of the bivariate Mecke equation**, `a < m`, for a general function of
the *pair* of inserted marks: the two independent insertions each contribute a first-order
Palm–Campbell factor, and the term is

`K₀(a) ∫∫ A(g, g') V(g)^{m-1} V(g')^{m-1} dη dη`.

This is the mechanism behind the product term of Talagrand's second-order identities: the two
points of the off-diagonal are independent, so a general function of the pair is integrated
against the *product* of two copies of the first-order Palm measure. -/
theorem lintegral_offDiag_pdProcess {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {A : M × M → ℝ≥0∞} {V : M → ℝ≥0∞} (hA : Measurable A)
    (hV : Measurable V) (hVpos : ∀ᵐ g ∂η, 0 < V g) (hκ : ∫⁻ g, V g ^ m ∂η ≠ ∞)
    {a : ℝ} (ham : a < m) :
    ∫⁻ N, ∫⁻ p, ∫⁻ q, ENNReal.ofReal p.1 * ENNReal.ofReal q.1 * A (p.2, q.2)
        * (pdSum V N + ENNReal.ofReal p.1 * V p.2 + ENNReal.ofReal q.1 * V q.2) ^ (a - 2)
        ∂pdIntensity m η ∂pdIntensity m η ∂pdProcess m η
      = ENNReal.ofReal (pdOffConst m a (stableConst m) (∫⁻ g, V g ^ m ∂η).toReal)
        * ∫⁻ g, ∫⁻ g', A (g, g') * V g ^ (m - 1) * V g' ^ (m - 1) ∂η ∂η := by
  have hc : 0 < stableConst m := stableConst_pos hm0 hm1
  have hκpos : 0 < (∫⁻ g, V g ^ m ∂η).toReal :=
    ENNReal.toReal_pos (lintegral_rpow_pos_of_ae_pos hm0 η hV hVpos).ne' hκ
  have hb : (0 : ℝ) < 2 - a := by linarith
  have hS := measurable_pdSum (v := V) hV
  have hx : Measurable fun p : ℝ × M => ENNReal.ofReal p.1 * V p.2 := measurable_ofReal_mul hV
  -- the inner mark integral `B g = ∫ A(g, ·) V^{m-1} dη`
  have hBm : Measurable fun g : M => ∫⁻ g', A (g, g') * V g' ^ (m - 1) ∂η :=
    Measurable.lintegral_prod_right' (ν := η) (f := fun r : M × M => A r * V r.2 ^ (m - 1))
      (hA.mul ((hV.comp measurable_snd).pow_const _))
  have hGs : Measurable fun s : ℝ => ENNReal.ofReal (s ^ (1 - a))
      * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * (∫⁻ g, V g ^ m ∂η).toReal))) :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (((measurable_id.pow_const m).mul_const _).mul_const _).neg))
  have hnp : ∀ p : ℝ × M, Measurable fun s : ℝ =>
      ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal p.1 * V p.2))) := fun p =>
    ENNReal.measurable_ofReal.comp (measurable_negExp.comp
      (ENNReal.measurable_ofReal.mul_const _))
  have hAq : Measurable fun r : (ℝ × M) × (ℝ × M) => ENNReal.ofReal r.1.1 * ENNReal.ofReal r.2.1
      * A (r.1.2, r.2.2) :=
    ((ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_fst)).mul
      (ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_snd))).mul
      (hA.comp ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)))
  -- Step 1: move the `N`-integral innermost
  have hΦ : Measurable fun r : (Measure (ℝ × M) × (ℝ × M)) × (ℝ × M) =>
      ENNReal.ofReal r.1.2.1 * ENNReal.ofReal r.2.1 * A (r.1.2.2, r.2.2)
        * (pdSum V r.1.1 + ENNReal.ofReal r.1.2.1 * V r.1.2.2
            + ENNReal.ofReal r.2.1 * V r.2.2) ^ (a - 2) :=
    (hAq.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).mul
      ((((hS.comp (measurable_fst.comp measurable_fst)).add
        (hx.comp (measurable_snd.comp measurable_fst))).add (hx.comp measurable_snd)).pow_const _)
  rw [lintegral_lintegral_swap (μ := pdProcess m η) (ν := pdIntensity m η)
    (f := fun (N : Measure (ℝ × M)) (p : ℝ × M) => ∫⁻ q, ENNReal.ofReal p.1 * ENNReal.ofReal q.1
      * A (p.2, q.2)
      * (pdSum V N + ENNReal.ofReal p.1 * V p.2 + ENNReal.ofReal q.1 * V q.2) ^ (a - 2)
      ∂pdIntensity m η)
    (Measurable.lintegral_prod_right' (ν := pdIntensity m η) hΦ).aemeasurable]
  have hswap2 : ∀ p : ℝ × M,
      ∫⁻ N, ∫⁻ q, ENNReal.ofReal p.1 * ENNReal.ofReal q.1 * A (p.2, q.2)
          * (pdSum V N + ENNReal.ofReal p.1 * V p.2 + ENNReal.ofReal q.1 * V q.2) ^ (a - 2)
          ∂pdIntensity m η ∂pdProcess m η
        = ∫⁻ q, ∫⁻ N, ENNReal.ofReal p.1 * ENNReal.ofReal q.1 * A (p.2, q.2)
            * (pdSum V N + ENNReal.ofReal p.1 * V p.2 + ENNReal.ofReal q.1 * V q.2) ^ (a - 2)
            ∂pdProcess m η ∂pdIntensity m η := fun p =>
    lintegral_lintegral_swap (μ := pdProcess m η) (ν := pdIntensity m η)
      (f := fun (N : Measure (ℝ × M)) (q : ℝ × M) => ENNReal.ofReal p.1 * ENNReal.ofReal q.1
        * A (p.2, q.2)
        * (pdSum V N + ENNReal.ofReal p.1 * V p.2 + ENNReal.ofReal q.1 * V q.2) ^ (a - 2))
      (((hAq.comp ((measurable_const : Measurable fun _ : Measure (ℝ × M) × (ℝ × M) => p).prodMk
        measurable_snd)).mul
        ((((hS.comp measurable_fst).add measurable_const).add
          (hx.comp measurable_snd)).pow_const _))).aemeasurable
  simp_rw [hswap2]
  -- Step 2: the Laplace representation and the Palm–Campbell transform in the `q`-variable
  have hkey : ∀ᵐ p ∂pdIntensity m η,
      ∫⁻ q, ∫⁻ N, ENNReal.ofReal p.1 * ENNReal.ofReal q.1 * A (p.2, q.2)
          * (pdSum V N + ENNReal.ofReal p.1 * V p.2 + ENNReal.ofReal q.1 * V q.2) ^ (a - 2)
          ∂pdProcess m η ∂pdIntensity m η
        = (ENNReal.ofReal (Real.Gamma (2 - a)))⁻¹
          * ∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ (1 - a))
              * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m
                  * (∫⁻ g, V g ^ m ∂η).toReal)))
              * (ENNReal.ofReal p.1 * ENNReal.ofReal (negExp (ENNReal.ofReal s
                  * (ENNReal.ofReal p.1 * V p.2))))
              * (ENNReal.ofReal (s ^ (m - 1) * Real.Gamma (1 - m))
                  * ∫⁻ g', A (p.2, g') * V g' ^ (m - 1) ∂η) := by
    filter_upwards [ae_pdIntensity_ne_zero η hV hVpos] with p hp
    have hinner : ∀ q : ℝ × M,
        ∫⁻ N, ENNReal.ofReal p.1 * ENNReal.ofReal q.1 * A (p.2, q.2)
            * (pdSum V N + ENNReal.ofReal p.1 * V p.2 + ENNReal.ofReal q.1 * V q.2) ^ (a - 2)
            ∂pdProcess m η
          = (ENNReal.ofReal (Real.Gamma (2 - a)))⁻¹
            * ∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ (1 - a))
                * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m
                    * (∫⁻ g, V g ^ m ∂η).toReal)))
                * (ENNReal.ofReal p.1 * ENNReal.ofReal (negExp (ENNReal.ofReal s
                    * (ENNReal.ofReal p.1 * V p.2))))
                * (ENNReal.ofReal q.1 * A (p.2, q.2) * ENNReal.ofReal (negExp (ENNReal.ofReal s
                    * (ENNReal.ofReal q.1 * V q.2)))) := by
      intro q
      have hmeasN : Measurable fun N : Measure (ℝ × M) =>
          (pdSum V N + ENNReal.ofReal p.1 * V p.2
            + ENNReal.ofReal q.1 * V q.2) ^ (a - 2) := by
        exact ((hS.add measurable_const).add measurable_const).pow_const _
      rw [lintegral_const_mul _ hmeasN]
      have hass : ∀ N : Measure (ℝ × M),
          (pdSum V N + ENNReal.ofReal p.1 * V p.2 + ENNReal.ofReal q.1 * V q.2) ^ (a - 2)
            = (pdSum V N + (ENNReal.ofReal p.1 * V p.2
                + ENNReal.ofReal q.1 * V q.2)) ^ (-(2 - a)) := fun N => by
        rw [add_assoc, neg_sub]
      simp_rw [hass]
      rw [lintegral_rpow_neg_add_pdSum hm0 hm1 η hV hκ hb (fun h => hp (add_eq_zero.1 h).1)]
      have hmeas_s : Measurable fun s : ℝ => ENNReal.ofReal (s ^ (2 - a - 1))
          * ENNReal.ofReal (negExp (ENNReal.ofReal s
              * (ENNReal.ofReal p.1 * V p.2 + ENNReal.ofReal q.1 * V q.2)))
          * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m
              * (∫⁻ g, V g ^ m ∂η).toReal))) :=
        ((ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul
          (ENNReal.measurable_ofReal.comp (measurable_negExp.comp
            (ENNReal.measurable_ofReal.mul_const _)))).mul
          (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
            (((measurable_id.pow_const m).mul_const _).mul_const _).neg))
      rw [mul_left_comm]
      congr 1
      rw [← lintegral_const_mul _ hmeas_s]
      refine setLIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
      rw [show (2 : ℝ) - a - 1 = 1 - a by ring, mul_add, negExp_add,
        ENNReal.ofReal_mul (negExp_nonneg _)]
      ring
    simp_rw [hinner]
    have hjointqs : Measurable fun r : (ℝ × M) × ℝ =>
        ENNReal.ofReal (r.2 ^ (1 - a))
          * ENNReal.ofReal (Real.exp (-(r.2 ^ m * stableConst m
              * (∫⁻ g, V g ^ m ∂η).toReal)))
          * (ENNReal.ofReal p.1 * ENNReal.ofReal (negExp (ENNReal.ofReal r.2
              * (ENNReal.ofReal p.1 * V p.2))))
          * (ENNReal.ofReal r.1.1 * A (p.2, r.1.2) * ENNReal.ofReal (negExp (ENNReal.ofReal r.2
              * (ENNReal.ofReal r.1.1 * V r.1.2)))) :=
      ((hGs.comp measurable_snd).mul
        (measurable_const.mul ((hnp p).comp measurable_snd))).mul
        (((ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_fst)).mul
          (hA.comp (measurable_const.prodMk (measurable_snd.comp measurable_fst)))).mul
          (ENNReal.measurable_ofReal.comp (measurable_negExp.comp
            ((ENNReal.measurable_ofReal.comp measurable_snd).mul (hx.comp measurable_fst)))))
    have hmeas_q : Measurable fun q : ℝ × M =>
        ∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ (1 - a))
          * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * (∫⁻ g, V g ^ m ∂η).toReal)))
          * (ENNReal.ofReal p.1 * ENNReal.ofReal (negExp (ENNReal.ofReal s
              * (ENNReal.ofReal p.1 * V p.2))))
          * (ENNReal.ofReal q.1 * A (p.2, q.2) * ENNReal.ofReal (negExp (ENNReal.ofReal s
              * (ENNReal.ofReal q.1 * V q.2)))) :=
      Measurable.lintegral_prod_right' (ν := volume.restrict (Ioi 0)) hjointqs
    rw [lintegral_const_mul _ hmeas_q]
    congr 1
    rw [lintegral_lintegral_swap (μ := pdIntensity m η) (ν := volume.restrict (Ioi 0))
      (f := fun (q : ℝ × M) (s : ℝ) => ENNReal.ofReal (s ^ (1 - a))
        * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * (∫⁻ g, V g ^ m ∂η).toReal)))
        * (ENNReal.ofReal p.1 * ENNReal.ofReal (negExp (ENNReal.ofReal s
            * (ENNReal.ofReal p.1 * V p.2))))
        * (ENNReal.ofReal q.1 * A (p.2, q.2) * ENNReal.ofReal (negExp (ENNReal.ofReal s
            * (ENNReal.ofReal q.1 * V q.2))))) hjointqs.aemeasurable]
    refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    rw [mem_Ioi] at hs
    have hWm : Measurable fun q : ℝ × M => ENNReal.ofReal q.1 * A (p.2, q.2)
        * ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal q.1 * V q.2))) :=
      ((ENNReal.measurable_ofReal.comp measurable_fst).mul
        (hA.comp (measurable_const.prodMk measurable_snd))).mul
        (ENNReal.measurable_ofReal.comp (measurable_negExp.comp
          (measurable_const.mul hx)))
    rw [lintegral_const_mul _ hWm, lintegral_pdIntensity_mul_negExp hm1 η
      (U := fun g' => A (p.2, g')) (hA.comp (measurable_const.prodMk measurable_id)) hV hVpos hs]
  rw [lintegral_congr_ae hkey]
  -- Step 3: the Palm–Campbell transform in the `p`-variable
  have hjointps : Measurable fun r : (ℝ × M) × ℝ =>
      ENNReal.ofReal (r.2 ^ (1 - a))
        * ENNReal.ofReal (Real.exp (-(r.2 ^ m * stableConst m * (∫⁻ g, V g ^ m ∂η).toReal)))
        * (ENNReal.ofReal r.1.1 * ENNReal.ofReal (negExp (ENNReal.ofReal r.2
            * (ENNReal.ofReal r.1.1 * V r.1.2))))
        * (ENNReal.ofReal (r.2 ^ (m - 1) * Real.Gamma (1 - m))
            * ∫⁻ g', A (r.1.2, g') * V g' ^ (m - 1) ∂η) :=
    ((hGs.comp measurable_snd).mul
      ((ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_fst)).mul
        (ENNReal.measurable_ofReal.comp (measurable_negExp.comp
          ((ENNReal.measurable_ofReal.comp measurable_snd).mul (hx.comp measurable_fst)))))).mul
      ((ENNReal.measurable_ofReal.comp
        ((measurable_snd.pow_const _).mul_const _)).mul
        (hBm.comp (measurable_snd.comp measurable_fst)))
  have hmeas_p : Measurable fun p : ℝ × M =>
      ∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ (1 - a))
        * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * (∫⁻ g, V g ^ m ∂η).toReal)))
        * (ENNReal.ofReal p.1 * ENNReal.ofReal (negExp (ENNReal.ofReal s
            * (ENNReal.ofReal p.1 * V p.2))))
        * (ENNReal.ofReal (s ^ (m - 1) * Real.Gamma (1 - m))
            * ∫⁻ g', A (p.2, g') * V g' ^ (m - 1) ∂η) :=
    Measurable.lintegral_prod_right' (ν := volume.restrict (Ioi 0)) hjointps
  rw [lintegral_const_mul _ hmeas_p,
    lintegral_lintegral_swap (μ := pdIntensity m η) (ν := volume.restrict (Ioi 0))
      (f := fun (p : ℝ × M) (s : ℝ) => ENNReal.ofReal (s ^ (1 - a))
        * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * (∫⁻ g, V g ^ m ∂η).toReal)))
        * (ENNReal.ofReal p.1 * ENNReal.ofReal (negExp (ENNReal.ofReal s
            * (ENNReal.ofReal p.1 * V p.2))))
        * (ENNReal.ofReal (s ^ (m - 1) * Real.Gamma (1 - m))
            * ∫⁻ g', A (p.2, g') * V g' ^ (m - 1) ∂η)) hjointps.aemeasurable]
  have hs_inner : ∀ s ∈ Ioi (0 : ℝ),
      ∫⁻ p, ENNReal.ofReal (s ^ (1 - a))
          * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * (∫⁻ g, V g ^ m ∂η).toReal)))
          * (ENNReal.ofReal p.1 * ENNReal.ofReal (negExp (ENNReal.ofReal s
              * (ENNReal.ofReal p.1 * V p.2))))
          * (ENNReal.ofReal (s ^ (m - 1) * Real.Gamma (1 - m))
              * ∫⁻ g', A (p.2, g') * V g' ^ (m - 1) ∂η) ∂pdIntensity m η
        = ENNReal.ofReal (s ^ (1 - a))
          * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * (∫⁻ g, V g ^ m ∂η).toReal)))
          * (ENNReal.ofReal (s ^ (m - 1) * Real.Gamma (1 - m)) ^ 2
              * ∫⁻ g, ∫⁻ g', A (g, g') * V g ^ (m - 1) * V g' ^ (m - 1) ∂η ∂η) := by
    intro s hs
    rw [mem_Ioi] at hs
    have hre : ∀ p : ℝ × M, ENNReal.ofReal (s ^ (1 - a))
        * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m * (∫⁻ g, V g ^ m ∂η).toReal)))
        * (ENNReal.ofReal p.1 * ENNReal.ofReal (negExp (ENNReal.ofReal s
            * (ENNReal.ofReal p.1 * V p.2))))
        * (ENNReal.ofReal (s ^ (m - 1) * Real.Gamma (1 - m))
            * ∫⁻ g', A (p.2, g') * V g' ^ (m - 1) ∂η)
        = ENNReal.ofReal (s ^ (1 - a))
            * ENNReal.ofReal (Real.exp (-(s ^ m * stableConst m
                * (∫⁻ g, V g ^ m ∂η).toReal)))
            * ENNReal.ofReal (s ^ (m - 1) * Real.Gamma (1 - m))
          * (ENNReal.ofReal p.1 * (∫⁻ g', A (p.2, g') * V g' ^ (m - 1) ∂η)
              * ENNReal.ofReal (negExp (ENNReal.ofReal s
                  * (ENNReal.ofReal p.1 * V p.2)))) := fun p => by ring
    simp_rw [hre]
    have hWm : Measurable fun p : ℝ × M => ENNReal.ofReal p.1
        * (∫⁻ g', A (p.2, g') * V g' ^ (m - 1) ∂η)
        * ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal p.1 * V p.2))) :=
      ((ENNReal.measurable_ofReal.comp measurable_fst).mul (hBm.comp measurable_snd)).mul
        (ENNReal.measurable_ofReal.comp (measurable_negExp.comp (measurable_const.mul hx)))
    rw [lintegral_const_mul _ hWm, lintegral_pdIntensity_mul_negExp hm1 η
      (U := fun g => ∫⁻ g', A (g, g') * V g' ^ (m - 1) ∂η) hBm hV hVpos hs]
    have hJ : ∫⁻ g, (∫⁻ g', A (g, g') * V g' ^ (m - 1) ∂η) * V g ^ (m - 1) ∂η
        = ∫⁻ g, ∫⁻ g', A (g, g') * V g ^ (m - 1) * V g' ^ (m - 1) ∂η ∂η := by
      refine lintegral_congr fun g => ?_
      have hmeas : Measurable fun g' : M => A (g, g') * V g' ^ (m - 1) :=
        (hA.comp (measurable_const.prodMk measurable_id)).mul (hV.pow_const _)
      rw [← lintegral_mul_const _ hmeas]
      exact lintegral_congr fun g' => by ring
    rw [hJ]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hs_inner,
    lintegral_offDiag_gamma hm0 hm1 hκpos ham
      (∫⁻ g, ∫⁻ g', A (g, g') * V g ^ (m - 1) * V g' ^ (m - 1) ∂η ∂η)]

/-- **The second-order one-level identity**, `a < m`: the square of a linear statistic against a
negative power of the normalizer splits into an off-diagonal and a diagonal contribution,

`𝔼 (∑_α u_α A(g_α))² (∑_α u_α V(g_α))^{a-2} = K₀(a) (∫ A V^{m-1} dη)² + K₂(a) ∫ A² V^{m-2} dη`.

The off-diagonal half is the case `A(g, g') = A(g) A(g')` of `lintegral_offDiag_pdProcess`, the
diagonal half is `lintegral_pdSumSq_mul_rpow_pdSum`, and the bivariate Mecke equation separates
them. At `a = 0` the first term is `(∫ A V^{m-1} dη / κ)²` and the second is
`(1-m) ∫ A² V^{m-2} dη / κ`, which is Talagrand's (13.14) together with (13.13); the general
exponent is what is needed at the higher levels of the cascade. -/
theorem lintegral_pdSum_sq_mul_rpow_pdSum {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {A V : M → ℝ≥0∞} (hA : Measurable A) (hV : Measurable V)
    (hVpos : ∀ᵐ g ∂η, 0 < V g) (hκ : ∫⁻ g, V g ^ m ∂η ≠ ∞) {a : ℝ} (ham : a < m) :
    ∫⁻ N, pdSum A N ^ 2 * pdSum V N ^ (a - 2) ∂pdProcess m η
      = ENNReal.ofReal (pdOffConst m a (stableConst m) (∫⁻ g, V g ^ m ∂η).toReal)
          * (∫⁻ g, A g * V g ^ (m - 1) ∂η) ^ 2
        + ENNReal.ofReal (pdSqConst m a (stableConst m) (∫⁻ g, V g ^ m ∂η).toReal)
          * ∫⁻ g, A g ^ 2 * V g ^ (m - 2) ∂η := by
  have hS := measurable_pdSum (v := V) hV
  have hSA := measurable_pdSum (v := A) hA
  have hw : Measurable fun p : ℝ × M => ENNReal.ofReal p.1 * A p.2 := measurable_ofReal_mul hA
  have hx : Measurable fun p : ℝ × M => ENNReal.ofReal p.1 * V p.2 := measurable_ofReal_mul hV
  have hsq : Measurable fun p : ℝ × M =>
      ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * A p.2 ^ 2 :=
    ((ENNReal.measurable_ofReal.comp measurable_fst).mul
      (ENNReal.measurable_ofReal.comp measurable_fst)).mul
      ((hA.comp measurable_snd).pow_const _)
  -- the double sum over pairs of points
  have hdouble : ∀ (N : Measure (ℝ × M)) (C : ℝ≥0∞),
      ∫⁻ p, ∫⁻ q, ENNReal.ofReal p.1 * A p.2 * (ENNReal.ofReal q.1 * A q.2) * C ∂N ∂N
        = pdSum A N ^ 2 * C := by
    intro N C
    have hq : ∀ p : ℝ × M,
        ∫⁻ q, ENNReal.ofReal p.1 * A p.2 * (ENNReal.ofReal q.1 * A q.2) * C ∂N
          = C * pdSum A N * (ENNReal.ofReal p.1 * A p.2) := by
      intro p
      calc ∫⁻ q, ENNReal.ofReal p.1 * A p.2 * (ENNReal.ofReal q.1 * A q.2) * C ∂N
          = ∫⁻ q, ENNReal.ofReal p.1 * A p.2 * C * (ENNReal.ofReal q.1 * A q.2) ∂N :=
            lintegral_congr fun q => by ring
        _ = ENNReal.ofReal p.1 * A p.2 * C * pdSum A N := lintegral_const_mul_pdSum hA N _
        _ = C * pdSum A N * (ENNReal.ofReal p.1 * A p.2) := by ring
    simp_rw [hq]
    rw [lintegral_const_mul_pdSum hA N]
    ring
  -- the bivariate Mecke equation
  have hf : Measurable fun r : (ℝ × M) × (ℝ × M) × Measure (ℝ × M) =>
      ENNReal.ofReal r.1.1 * A r.1.2 * (ENNReal.ofReal r.2.1.1 * A r.2.1.2)
        * pdSum V r.2.2 ^ (a - 2) :=
    ((hw.comp measurable_fst).mul (hw.comp (measurable_fst.comp measurable_snd))).mul
      ((hS.comp (measurable_snd.comp measurable_snd)).pow_const _)
  have hF : Measurable fun N : Measure (ℝ × M) => ∫⁻ p, ∫⁻ q, ENNReal.ofReal p.1 * A p.2
      * (ENNReal.ofReal q.1 * A q.2) * pdSum V N ^ (a - 2) ∂N ∂N := by
    simp_rw [hdouble]
    exact (hSA.pow_const _).mul (hS.pow_const _)
  have hgeq : ∀ (r : (ℝ × M) × Measure (ℝ × M)) (C : ℝ≥0∞),
      ∫⁻ q, ENNReal.ofReal r.1.1 * A r.1.2 * (ENNReal.ofReal q.1 * A q.2) * C ∂r.2
        = ENNReal.ofReal r.1.1 * A r.1.2 * C * pdSum A r.2 := by
    intro r C
    calc ∫⁻ q, ENNReal.ofReal r.1.1 * A r.1.2 * (ENNReal.ofReal q.1 * A q.2) * C ∂r.2
        = ∫⁻ q, ENNReal.ofReal r.1.1 * A r.1.2 * C * (ENNReal.ofReal q.1 * A q.2) ∂r.2 :=
          lintegral_congr fun q => by ring
      _ = _ := lintegral_const_mul_pdSum hA r.2 _
  have hg : Measurable fun r : (ℝ × M) × Measure (ℝ × M) =>
      ∫⁻ q, ENNReal.ofReal r.1.1 * A r.1.2 * (ENNReal.ofReal q.1 * A q.2)
        * pdSum V r.2 ^ (a - 2) ∂r.2 := by
    simp_rw [hgeq]
    exact ((hw.comp measurable_fst).mul ((hS.comp measurable_snd).pow_const _)).mul
      (hSA.comp measurable_snd)
  have hg' : Measurable fun r : (ℝ × M) × Measure (ℝ × M) =>
      ∫⁻ q, ENNReal.ofReal r.1.1 * A r.1.2 * (ENNReal.ofReal q.1 * A q.2)
        * pdSum V (r.2 + Measure.dirac r.1) ^ (a - 2) ∂r.2 := by
    simp_rw [hgeq, pdSum_add_dirac hV]
    exact ((hw.comp measurable_fst).mul
      (((hS.comp measurable_snd).add (hx.comp measurable_fst)).pow_const _)).mul
      (hSA.comp measurable_snd)
  have hbi : ∫⁻ N, ∫⁻ p, ∫⁻ q, ENNReal.ofReal p.1 * A p.2 * (ENNReal.ofReal q.1 * A q.2)
        * pdSum V N ^ (a - 2) ∂N ∂N ∂pdProcess m η
      = (∫⁻ N, ∫⁻ p, ∫⁻ q, ENNReal.ofReal p.1 * A p.2 * (ENNReal.ofReal q.1 * A q.2)
            * pdSum V (N + Measure.dirac p + Measure.dirac q) ^ (a - 2)
            ∂pdIntensity m η ∂pdIntensity m η ∂pdProcess m η)
        + ∫⁻ N, ∫⁻ p, ENNReal.ofReal p.1 * A p.2 * (ENNReal.ofReal p.1 * A p.2)
            * pdSum V (N + Measure.dirac p) ^ (a - 2) ∂pdIntensity m η ∂pdProcess m η :=
    lintegral_lintegral_lintegral_pdProcess m η
      (f := fun r : (ℝ × M) × (ℝ × M) × Measure (ℝ × M) =>
        ENNReal.ofReal r.1.1 * A r.1.2 * (ENNReal.ofReal r.2.1.1 * A r.2.1.2)
          * pdSum V r.2.2 ^ (a - 2)) hf hF hg hg'
  have hlhs : ∫⁻ N, pdSum A N ^ 2 * pdSum V N ^ (a - 2) ∂pdProcess m η
      = ∫⁻ N, ∫⁻ p, ∫⁻ q, ENNReal.ofReal p.1 * A p.2 * (ENNReal.ofReal q.1 * A q.2)
          * pdSum V N ^ (a - 2) ∂N ∂N ∂pdProcess m η :=
    lintegral_congr fun N => (hdouble N _).symm
  rw [hlhs, hbi]
  congr 1
  · -- the off-diagonal term, from the pair identity at `A ⊗ A`
    simp_rw [pdSum_add_dirac hV]
    have hApair : Measurable fun r : M × M => A r.1 * A r.2 :=
      (hA.comp measurable_fst).mul (hA.comp measurable_snd)
    have hAV : Measurable fun g => A g * V g ^ (m - 1) := hA.mul (hV.pow_const _)
    have hconv : ∫⁻ N, ∫⁻ p, ∫⁻ q, ENNReal.ofReal p.1 * A p.2 * (ENNReal.ofReal q.1 * A q.2)
          * (pdSum V N + ENNReal.ofReal p.1 * V p.2 + ENNReal.ofReal q.1 * V q.2) ^ (a - 2)
          ∂pdIntensity m η ∂pdIntensity m η ∂pdProcess m η
        = ∫⁻ N, ∫⁻ p, ∫⁻ q, ENNReal.ofReal p.1 * ENNReal.ofReal q.1 * (A p.2 * A q.2)
            * (pdSum V N + ENNReal.ofReal p.1 * V p.2 + ENNReal.ofReal q.1 * V q.2) ^ (a - 2)
            ∂pdIntensity m η ∂pdIntensity m η ∂pdProcess m η :=
      lintegral_congr fun N => lintegral_congr fun p => lintegral_congr fun q => by ring
    rw [hconv, lintegral_offDiag_pdProcess hm0 hm1 η hApair hV hVpos hκ ham]
    congr 1
    have hin : ∀ g : M, ∫⁻ g', A g * A g' * V g ^ (m - 1) * V g' ^ (m - 1) ∂η
        = (A g * V g ^ (m - 1)) * ∫⁻ g', A g' * V g' ^ (m - 1) ∂η := by
      intro g
      rw [← lintegral_const_mul _ hAV]
      exact lintegral_congr fun g' => by ring
    simp_rw [hin]
    rw [lintegral_mul_const _ hAV, pow_two]
  · -- the diagonal term, back through the one-point Mecke formula
    have hdiag : ∀ (N : Measure (ℝ × M)) (p : ℝ × M),
        ENNReal.ofReal p.1 * A p.2 * (ENNReal.ofReal p.1 * A p.2)
            * pdSum V (N + Measure.dirac p) ^ (a - 2)
          = ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * A p.2 ^ 2
            * pdSum V (N + Measure.dirac p) ^ (a - 2) := fun N p => by ring
    simp_rw [hdiag]
    have hf2 : Measurable fun r : (ℝ × M) × Measure (ℝ × M) =>
        ENNReal.ofReal r.1.1 * ENNReal.ofReal r.1.1 * A r.1.2 ^ 2
          * pdSum V r.2 ^ (a - 2) :=
      (hsq.comp measurable_fst).mul ((hS.comp measurable_snd).pow_const _)
    have hF2 : Measurable fun N : Measure (ℝ × M) => ∫⁻ p, ENNReal.ofReal p.1
        * ENNReal.ofReal p.1 * A p.2 ^ 2 * pdSum V N ^ (a - 2) ∂N := by
      have hc : ∀ N : Measure (ℝ × M), ∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1
          * A p.2 ^ 2 * pdSum V N ^ (a - 2) ∂N
          = (∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * A p.2 ^ 2 ∂N)
            * pdSum V N ^ (a - 2) := fun N => lintegral_mul_const _ hsq
      simp_rw [hc]
      exact (Measure.measurable_lintegral hsq).mul (hS.pow_const _)
    rw [← lintegral_lintegral_pdProcess m η
      (f := fun r : (ℝ × M) × Measure (ℝ × M) => ENNReal.ofReal r.1.1 * ENNReal.ofReal r.1.1
        * A r.1.2 ^ 2 * pdSum V r.2 ^ (a - 2)) hf2 hF2]
    have hc : ∀ N : Measure (ℝ × M), ∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1
        * A p.2 ^ 2 * pdSum V N ^ (a - 2) ∂N
        = (∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * A p.2 ^ 2 ∂N)
          * pdSum V N ^ (a - 2) := fun N => lintegral_mul_const _ hsq
    simp_rw [hc]
    exact lintegral_pdSumSq_mul_rpow_pdSum hm0 hm1 η (hA.pow_const 2) hV hVpos hκ ham

/-- The reflexive `HasLaw`, used to read the transported statements as statements about
`pdProcess` itself. -/
lemma hasLaw_self {N : Type*} [MeasurableSpace N] (μ : Measure N) :
    HasLaw (id : N → N) μ μ := ⟨aemeasurable_id, Measure.map_id⟩

/-- **The `a`-th moment of the Poisson–Dirichlet sum**, `a < m`, in the form
`𝔼 S_V^a = K₁(a) ∫ V^m dη`: the case `A = V` of `lintegral_pdSum_mul_rpow_pdSum`, after
`S_V^a = S_V · S_V^{a-1}` and `V^m = V · V^{m-1}` almost everywhere. -/
theorem lintegral_pdSum_rpow_eq_pdOneConst {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {V : M → ℝ≥0∞} (hV : Measurable V) (hVpos : ∀ᵐ g ∂η, 0 < V g)
    (hκ : ∫⁻ g, V g ^ m ∂η ≠ ∞) {a : ℝ} (ham : a < m) :
    ∫⁻ N, pdSum V N ^ a ∂pdProcess m η
      = ENNReal.ofReal (pdOneConst m a (stableConst m) (∫⁻ g, V g ^ m ∂η).toReal)
        * ∫⁻ g, V g ^ m ∂η := by
  have hidlaw := hasLaw_self (pdProcess m η)
  have haepos : ∀ᵐ N ∂pdProcess m η, 0 < pdSum V N := hidlaw.ae_pdSum_pos hm0 hV hVpos
  have haetop : ∀ᵐ N ∂pdProcess m η, pdSum V N < ∞ := hidlaw.ae_pdSum_lt_top hm0 hm1 hV hκ
  have haeVfin : ∀ᵐ p ∂η, V p < ∞ := by
    filter_upwards [ae_lt_top (hV.pow_const m) hκ] with p hp
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon, ENNReal.top_rpow_of_pos hm0] at hp
    exact hp.ne rfl
  have hpt : ∀ᵐ N ∂pdProcess m η, pdSum V N ^ a = pdSum V N * pdSum V N ^ (a - 1) := by
    filter_upwards [haepos, haetop] with N h0 htop
    conv_lhs => rw [show a = 1 + (a - 1) by ring]
    rw [ENNReal.rpow_add _ _ h0.ne' htop.ne, ENNReal.rpow_one]
  rw [lintegral_congr_ae hpt, lintegral_pdSum_mul_rpow_pdSum hm0 hm1 η hV hV hVpos hκ ham]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [hVpos, haeVfin] with p h0 htop
  conv_rhs => rw [show m = 1 + (m - 1) by ring]
  rw [ENNReal.rpow_add _ _ h0.ne' htop.ne, ENNReal.rpow_one]


/-! ### The two-point identities (13.15) and (13.16) -/

omit [Nonempty M] in
/-- `K₀(0) = m / κ²`. -/
lemma pdOffConst_zero {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) {κ : ℝ} (hκ : 0 < κ) :
    pdOffConst m 0 (stableConst m) κ = m / κ ^ 2 := by
  have hc : 0 < stableConst m := stableConst_pos hm0 hm1
  have hΓm : Real.Gamma (1 - m) = m * stableConst m := (mul_stableConst_eq_Gamma hm0 hm1).symm
  have hpow : (stableConst m * κ) ^ ((0 : ℝ) / m - 2) = (stableConst m * κ) ^ (-2 : ℝ) := by
    norm_num
  rw [pdOffConst, hΓm, hpow, Real.rpow_neg (by positivity),
    show ((stableConst m * κ) ^ (2 : ℝ)) = (stableConst m * κ) ^ (2 : ℕ) by
      rw [← Real.rpow_natCast (stableConst m * κ) 2]; norm_num]
  norm_num
  field_simp

omit [Nonempty M] in
/-- `K₂(0) = (1 - m) / κ`. -/
lemma pdSqConst_zero {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) {κ : ℝ} (hκ : 0 < κ) :
    pdSqConst m 0 (stableConst m) κ = (1 - m) / κ := by
  have hc : 0 < stableConst m := stableConst_pos hm0 hm1
  have hΓm : Real.Gamma (2 - m) = (1 - m) * (m * stableConst m) := by
    rw [mul_stableConst_eq_Gamma hm0 hm1, show (2 : ℝ) - m = (1 - m) + 1 by ring,
      Real.Gamma_add_one (by linarith)]
  rw [pdSqConst, hΓm]
  norm_num
  rw [Real.rpow_neg_one]
  field_simp

/-- **The polarized second-order one-level identity**, `a < m`: for two numerators,

`𝔼 (∑_α u_α A(g_α)) (∑_γ u_γ B(g_γ)) (∑_α u_α V(g_α))^{a-2}
  = K₀(a) (∫ A V^{m-1})(∫ B V^{m-1}) + K₂(a) ∫ A B V^{m-2}`.

At `A = B` it is `lintegral_pdSum_sq_mul_rpow_pdSum`; at `a = 0` it is Talagrand's (13.16). -/
theorem lintegral_pdSum_mul_pdSum_mul_rpow_pdSum {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1)
    (η : Measure M) [IsProbabilityMeasure η] {A B V : M → ℝ≥0∞} (hA : Measurable A)
    (hB : Measurable B) (hV : Measurable V) (hVpos : ∀ᵐ g ∂η, 0 < V g)
    (hκ : ∫⁻ g, V g ^ m ∂η ≠ ∞) {a : ℝ} (ham : a < m) :
    ∫⁻ N, pdSum A N * pdSum B N * pdSum V N ^ (a - 2) ∂pdProcess m η
      = ENNReal.ofReal (pdOffConst m a (stableConst m) (∫⁻ g, V g ^ m ∂η).toReal)
          * ((∫⁻ g, A g * V g ^ (m - 1) ∂η) * ∫⁻ g, B g * V g ^ (m - 1) ∂η)
        + ENNReal.ofReal (pdSqConst m a (stableConst m) (∫⁻ g, V g ^ m ∂η).toReal)
          * ∫⁻ g, A g * B g * V g ^ (m - 2) ∂η := by
  have hS := measurable_pdSum (v := V) hV
  have hSA := measurable_pdSum (v := A) hA
  have hSB := measurable_pdSum (v := B) hB
  have hwA : Measurable fun p : ℝ × M => ENNReal.ofReal p.1 * A p.2 := measurable_ofReal_mul hA
  have hwB : Measurable fun p : ℝ × M => ENNReal.ofReal p.1 * B p.2 := measurable_ofReal_mul hB
  have hx : Measurable fun p : ℝ × M => ENNReal.ofReal p.1 * V p.2 := measurable_ofReal_mul hV
  have hsq : Measurable fun p : ℝ × M =>
      ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * (A p.2 * B p.2) :=
    ((ENNReal.measurable_ofReal.comp measurable_fst).mul
      (ENNReal.measurable_ofReal.comp measurable_fst)).mul
      ((hA.comp measurable_snd).mul (hB.comp measurable_snd))
  have hdouble : ∀ (N : Measure (ℝ × M)) (C : ℝ≥0∞),
      ∫⁻ p, ∫⁻ q, ENNReal.ofReal p.1 * A p.2 * (ENNReal.ofReal q.1 * B q.2) * C ∂N ∂N
        = pdSum A N * pdSum B N * C := by
    intro N C
    have hq : ∀ p : ℝ × M,
        ∫⁻ q, ENNReal.ofReal p.1 * A p.2 * (ENNReal.ofReal q.1 * B q.2) * C ∂N
          = C * pdSum B N * (ENNReal.ofReal p.1 * A p.2) := by
      intro p
      calc ∫⁻ q, ENNReal.ofReal p.1 * A p.2 * (ENNReal.ofReal q.1 * B q.2) * C ∂N
          = ∫⁻ q, ENNReal.ofReal p.1 * A p.2 * C * (ENNReal.ofReal q.1 * B q.2) ∂N :=
            lintegral_congr fun q => by ring
        _ = ENNReal.ofReal p.1 * A p.2 * C * pdSum B N := lintegral_const_mul_pdSum hB N _
        _ = C * pdSum B N * (ENNReal.ofReal p.1 * A p.2) := by ring
    simp_rw [hq]
    rw [lintegral_const_mul_pdSum hA N]
    ring
  have hf : Measurable fun r : (ℝ × M) × (ℝ × M) × Measure (ℝ × M) =>
      ENNReal.ofReal r.1.1 * A r.1.2 * (ENNReal.ofReal r.2.1.1 * B r.2.1.2)
        * pdSum V r.2.2 ^ (a - 2) :=
    ((hwA.comp measurable_fst).mul (hwB.comp (measurable_fst.comp measurable_snd))).mul
      ((hS.comp (measurable_snd.comp measurable_snd)).pow_const _)
  have hF : Measurable fun N : Measure (ℝ × M) => ∫⁻ p, ∫⁻ q, ENNReal.ofReal p.1 * A p.2
      * (ENNReal.ofReal q.1 * B q.2) * pdSum V N ^ (a - 2) ∂N ∂N := by
    simp_rw [hdouble]
    exact (hSA.mul hSB).mul (hS.pow_const _)
  have hgeq : ∀ (r : (ℝ × M) × Measure (ℝ × M)) (C : ℝ≥0∞),
      ∫⁻ q, ENNReal.ofReal r.1.1 * A r.1.2 * (ENNReal.ofReal q.1 * B q.2) * C ∂r.2
        = ENNReal.ofReal r.1.1 * A r.1.2 * C * pdSum B r.2 := by
    intro r C
    calc ∫⁻ q, ENNReal.ofReal r.1.1 * A r.1.2 * (ENNReal.ofReal q.1 * B q.2) * C ∂r.2
        = ∫⁻ q, ENNReal.ofReal r.1.1 * A r.1.2 * C * (ENNReal.ofReal q.1 * B q.2) ∂r.2 :=
          lintegral_congr fun q => by ring
      _ = _ := lintegral_const_mul_pdSum hB r.2 _
  have hg : Measurable fun r : (ℝ × M) × Measure (ℝ × M) =>
      ∫⁻ q, ENNReal.ofReal r.1.1 * A r.1.2 * (ENNReal.ofReal q.1 * B q.2)
        * pdSum V r.2 ^ (a - 2) ∂r.2 := by
    simp_rw [hgeq]
    exact ((hwA.comp measurable_fst).mul ((hS.comp measurable_snd).pow_const _)).mul
      (hSB.comp measurable_snd)
  have hg' : Measurable fun r : (ℝ × M) × Measure (ℝ × M) =>
      ∫⁻ q, ENNReal.ofReal r.1.1 * A r.1.2 * (ENNReal.ofReal q.1 * B q.2)
        * pdSum V (r.2 + Measure.dirac r.1) ^ (a - 2) ∂r.2 := by
    simp_rw [hgeq, pdSum_add_dirac hV]
    exact ((hwA.comp measurable_fst).mul
      (((hS.comp measurable_snd).add (hx.comp measurable_fst)).pow_const _)).mul
      (hSB.comp measurable_snd)
  have hbi : ∫⁻ N, ∫⁻ p, ∫⁻ q, ENNReal.ofReal p.1 * A p.2 * (ENNReal.ofReal q.1 * B q.2)
        * pdSum V N ^ (a - 2) ∂N ∂N ∂pdProcess m η
      = (∫⁻ N, ∫⁻ p, ∫⁻ q, ENNReal.ofReal p.1 * A p.2 * (ENNReal.ofReal q.1 * B q.2)
            * pdSum V (N + Measure.dirac p + Measure.dirac q) ^ (a - 2)
            ∂pdIntensity m η ∂pdIntensity m η ∂pdProcess m η)
        + ∫⁻ N, ∫⁻ p, ENNReal.ofReal p.1 * A p.2 * (ENNReal.ofReal p.1 * B p.2)
            * pdSum V (N + Measure.dirac p) ^ (a - 2) ∂pdIntensity m η ∂pdProcess m η :=
    lintegral_lintegral_lintegral_pdProcess m η
      (f := fun r : (ℝ × M) × (ℝ × M) × Measure (ℝ × M) =>
        ENNReal.ofReal r.1.1 * A r.1.2 * (ENNReal.ofReal r.2.1.1 * B r.2.1.2)
          * pdSum V r.2.2 ^ (a - 2)) hf hF hg hg'
  have hlhs : ∫⁻ N, pdSum A N * pdSum B N * pdSum V N ^ (a - 2) ∂pdProcess m η
      = ∫⁻ N, ∫⁻ p, ∫⁻ q, ENNReal.ofReal p.1 * A p.2 * (ENNReal.ofReal q.1 * B q.2)
          * pdSum V N ^ (a - 2) ∂N ∂N ∂pdProcess m η :=
    lintegral_congr fun N => (hdouble N _).symm
  rw [hlhs, hbi]
  congr 1
  · -- the off-diagonal term
    simp_rw [pdSum_add_dirac hV]
    have hApair : Measurable fun r : M × M => A r.1 * B r.2 :=
      (hA.comp measurable_fst).mul (hB.comp measurable_snd)
    have hAV : Measurable fun g => A g * V g ^ (m - 1) := hA.mul (hV.pow_const _)
    have hBV : Measurable fun g => B g * V g ^ (m - 1) := hB.mul (hV.pow_const _)
    have hconv : ∫⁻ N, ∫⁻ p, ∫⁻ q, ENNReal.ofReal p.1 * A p.2 * (ENNReal.ofReal q.1 * B q.2)
          * (pdSum V N + ENNReal.ofReal p.1 * V p.2 + ENNReal.ofReal q.1 * V q.2) ^ (a - 2)
          ∂pdIntensity m η ∂pdIntensity m η ∂pdProcess m η
        = ∫⁻ N, ∫⁻ p, ∫⁻ q, ENNReal.ofReal p.1 * ENNReal.ofReal q.1 * (A p.2 * B q.2)
            * (pdSum V N + ENNReal.ofReal p.1 * V p.2 + ENNReal.ofReal q.1 * V q.2) ^ (a - 2)
            ∂pdIntensity m η ∂pdIntensity m η ∂pdProcess m η :=
      lintegral_congr fun N => lintegral_congr fun p => lintegral_congr fun q => by ring
    rw [hconv, lintegral_offDiag_pdProcess hm0 hm1 η hApair hV hVpos hκ ham]
    congr 1
    have hin : ∀ g : M, ∫⁻ g', A g * B g' * V g ^ (m - 1) * V g' ^ (m - 1) ∂η
        = (A g * V g ^ (m - 1)) * ∫⁻ g', B g' * V g' ^ (m - 1) ∂η := by
      intro g
      rw [← lintegral_const_mul _ hBV]
      exact lintegral_congr fun g' => by ring
    simp_rw [hin]
    exact lintegral_mul_const _ hAV
  · -- the diagonal term
    have hdiag : ∀ (N : Measure (ℝ × M)) (p : ℝ × M),
        ENNReal.ofReal p.1 * A p.2 * (ENNReal.ofReal p.1 * B p.2)
            * pdSum V (N + Measure.dirac p) ^ (a - 2)
          = ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * (A p.2 * B p.2)
            * pdSum V (N + Measure.dirac p) ^ (a - 2) := fun N p => by ring
    simp_rw [hdiag]
    have hf2 : Measurable fun r : (ℝ × M) × Measure (ℝ × M) =>
        ENNReal.ofReal r.1.1 * ENNReal.ofReal r.1.1 * (A r.1.2 * B r.1.2)
          * pdSum V r.2 ^ (a - 2) :=
      (hsq.comp measurable_fst).mul ((hS.comp measurable_snd).pow_const _)
    have hc : ∀ N : Measure (ℝ × M), ∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1
        * (A p.2 * B p.2) * pdSum V N ^ (a - 2) ∂N
        = (∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * (A p.2 * B p.2) ∂N)
          * pdSum V N ^ (a - 2) := fun N => lintegral_mul_const _ hsq
    have hF2 : Measurable fun N : Measure (ℝ × M) => ∫⁻ p, ENNReal.ofReal p.1
        * ENNReal.ofReal p.1 * (A p.2 * B p.2) * pdSum V N ^ (a - 2) ∂N := by
      simp_rw [hc]
      exact (Measure.measurable_lintegral hsq).mul (hS.pow_const _)
    rw [← lintegral_lintegral_pdProcess m η
      (f := fun r : (ℝ × M) × Measure (ℝ × M) => ENNReal.ofReal r.1.1 * ENNReal.ofReal r.1.1
        * (A r.1.2 * B r.1.2) * pdSum V r.2 ^ (a - 2)) hf2 hF2]
    simp_rw [hc]
    exact lintegral_pdSumSq_mul_rpow_pdSum hm0 hm1 η (hA.mul hB) hV hVpos hκ ham

omit [Nonempty M] in
/-- The double sum over *ordered pairs* of points factors: `∑_{α,γ} u_α U_α u_γ W_γ
= (∑_α u_α U_α)(∑_γ u_γ W_γ)`. -/
lemma lintegral_lintegral_ofReal_mul_eq_pdSum_mul {U W : M → ℝ≥0∞} (hU : Measurable U)
    (hW : Measurable W) (N : Measure (ℝ × M)) :
    ∫⁻ p, ∫⁻ q, ENNReal.ofReal p.1 * U p.2 * (ENNReal.ofReal q.1 * W q.2) ∂N ∂N
      = pdSum U N * pdSum W N := by
  have hq : ∀ p : ℝ × M, ∫⁻ q, ENNReal.ofReal p.1 * U p.2 * (ENNReal.ofReal q.1 * W q.2) ∂N
      = ENNReal.ofReal p.1 * U p.2 * pdSum W N := fun p => lintegral_const_mul_pdSum hW N _
  simp_rw [hq]
  exact lintegral_mul_const _ (measurable_ofReal_mul hU)

/-- **Identity (13.16)** (Talagrand Vol. II, Theorem 13.1.6), in `ℝ≥0∞`:

`𝔼 (∑_α v_α U_α)(∑_α v_α W_α)
  = (1-m) ∫ U W V^{m-2} dη / ∫ V^m dη
    + m (∫ U V^{m-1} dη / ∫ V^m dη)(∫ W V^{m-1} dη / ∫ V^m dη)`.

It is the case `a = 0` of `lintegral_pdSum_mul_pdSum_mul_rpow_pdSum`: the diagonal half is (13.14)
and the off-diagonal half is (13.15). -/
theorem lintegral_pdSum_mul_pdSum_mul_inv_pdSum_sq {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1)
    (η : Measure M) [IsProbabilityMeasure η] {U W V : M → ℝ≥0∞} (hU : Measurable U)
    (hW : Measurable W) (hV : Measurable V) (hVpos : ∀ᵐ g ∂η, 0 < V g)
    (hκ : ∫⁻ g, V g ^ m ∂η ≠ ∞) :
    ∫⁻ N, pdSum U N * pdSum W N * ((pdSum V N)⁻¹ * (pdSum V N)⁻¹) ∂pdProcess m η
      = ENNReal.ofReal (1 - m) * ((∫⁻ g, U g * W g * V g ^ (m - 2) ∂η) * (∫⁻ g, V g ^ m ∂η)⁻¹)
        + ENNReal.ofReal m
          * ((∫⁻ g, U g * V g ^ (m - 1) ∂η) * (∫⁻ g, V g ^ m ∂η)⁻¹
              * ((∫⁻ g, W g * V g ^ (m - 1) ∂η) * (∫⁻ g, V g ^ m ∂η)⁻¹)) := by
  have hκpos : 0 < (∫⁻ g, V g ^ m ∂η).toReal :=
    ENNReal.toReal_pos (lintegral_rpow_pos_of_ae_pos hm0 η hV hVpos).ne' hκ
  have hkr : ENNReal.ofReal (∫⁻ g, V g ^ m ∂η).toReal = ∫⁻ g, V g ^ m ∂η :=
    ENNReal.ofReal_toReal hκ
  have hneg : ∀ x : ℝ≥0∞, x ^ (-(2 : ℝ)) = x⁻¹ * x⁻¹ := by
    intro x
    rw [ENNReal.rpow_neg, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
      ENNReal.inv_pow, pow_two]
  have hkey := lintegral_pdSum_mul_pdSum_mul_rpow_pdSum hm0 hm1 η hU hW hV hVpos hκ (a := 0) hm0
  simp only [zero_sub] at hkey
  simp_rw [hneg] at hkey
  have h0 : ENNReal.ofReal (pdOffConst m 0 (stableConst m) (∫⁻ g, V g ^ m ∂η).toReal)
      = ENNReal.ofReal m * ((∫⁻ g, V g ^ m ∂η)⁻¹ * (∫⁻ g, V g ^ m ∂η)⁻¹) := by
    rw [pdOffConst_zero hm0 hm1 hκpos, ENNReal.ofReal_div_of_pos (by positivity),
      ENNReal.ofReal_pow hκpos.le, hkr, div_eq_mul_inv, ENNReal.inv_pow, pow_two]
  have h2 : ENNReal.ofReal (pdSqConst m 0 (stableConst m) (∫⁻ g, V g ^ m ∂η).toReal)
      = ENNReal.ofReal (1 - m) * (∫⁻ g, V g ^ m ∂η)⁻¹ := by
    rw [pdSqConst_zero hm0 hm1 hκpos, ENNReal.ofReal_div_of_pos hκpos, hkr, div_eq_mul_inv]
  rw [hkey, h0, h2]
  ring

/-! ### Two insertions with a general function of the pair -/

/-- **The bivariate Mecke equation for the Poisson–Dirichlet process, at the level of the
sample**: no measurability hypothesis beyond `Measurable f`, because the inner integrals are
taken against the counting measure of the sample. -/
theorem lintegral_lintegral_lintegral_pdSampleLaw (m : ℝ) (η : Measure M) [IsFiniteMeasure η]
    {f : (ℝ × M) × (ℝ × M) × Measure (ℝ × M) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, ∫⁻ p, ∫⁻ q, f (p, q, superCounting ω) ∂superCounting ω ∂superCounting ω
        ∂pdSampleLaw m η
      = (∫⁻ ω, ∫⁻ p, ∫⁻ q, f (p, q, superCounting ω + Measure.dirac p + Measure.dirac q)
            ∂pdIntensity m η ∂pdIntensity m η ∂pdSampleLaw m η)
        + ∫⁻ ω, ∫⁻ p, f (p, p, superCounting ω + Measure.dirac p) ∂pdIntensity m η
            ∂pdSampleLaw m η := by
  rw [← sum_pdSeq m η, pdSampleLaw]
  exact lintegral_lintegral_lintegral_superCounting (pdSeq m η) hf

set_option maxHeartbeats 1000000 in
-- the nested measurability terms for the three-fold integrals against `pdIntensity` are large
/-- **The second-order one-level identity for a pair function**, `a < m`: the double sum over
*ordered pairs* of points against a negative power of the normalizer splits into an off-diagonal
and a diagonal contribution,

`𝔼 (∑_{α,γ} u_α u_γ A(g_α, g_γ)) (∑_α u_α V(g_α))^{a-2}
  = K₀(a) ∫∫ A(g,g') V(g)^{m-1} V(g')^{m-1} + K₂(a) ∫ A(g,g) V(g)^{m-2}`.

The numerator is a genuine function of the pair of marks, not a product, so the statement is at
the level of the *sample*: that is the form in which the measurability hypotheses of the bivariate
Mecke equation are available, and it is the form the coupled construction of Talagrand's Theorem
14.3.5 needs. -/
theorem lintegral_pdSumPair_mul_rpow_pdSum {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {A : M × M → ℝ≥0∞} {V : M → ℝ≥0∞} (hA : Measurable A)
    (hV : Measurable V) (hVpos : ∀ᵐ g ∂η, 0 < V g) (hκ : ∫⁻ g, V g ^ m ∂η ≠ ∞)
    {a : ℝ} (ham : a < m) :
    ∫⁻ ω, (∫⁻ p, ∫⁻ q, ENNReal.ofReal p.1 * ENNReal.ofReal q.1 * A (p.2, q.2)
          ∂superCounting ω ∂superCounting ω) * pdSum V (superCounting ω) ^ (a - 2)
        ∂pdSampleLaw m η
      = ENNReal.ofReal (pdOffConst m a (stableConst m) (∫⁻ g, V g ^ m ∂η).toReal)
          * ∫⁻ g, ∫⁻ g', A (g, g') * V g ^ (m - 1) * V g' ^ (m - 1) ∂η ∂η
        + ENNReal.ofReal (pdSqConst m a (stableConst m) (∫⁻ g, V g ^ m ∂η).toReal)
          * ∫⁻ g, A (g, g) * V g ^ (m - 2) ∂η := by
  have hS := measurable_pdSum (v := V) hV
  have hx : Measurable fun p : ℝ × M => ENNReal.ofReal p.1 * V p.2 := measurable_ofReal_mul hV
  have hAd : Measurable fun g : M => A (g, g) := hA.comp (measurable_id.prodMk measurable_id)
  have hAq : Measurable fun r : (ℝ × M) × (ℝ × M) => ENNReal.ofReal r.1.1 * ENNReal.ofReal r.2.1
      * A (r.1.2, r.2.2) :=
    ((ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_fst)).mul
      (ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_snd))).mul
      (hA.comp ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)))
  have hsq : Measurable fun p : ℝ × M =>
      ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * A (p.2, p.2) :=
    ((ENNReal.measurable_ofReal.comp measurable_fst).mul
      (ENNReal.measurable_ofReal.comp measurable_fst)).mul (hAd.comp measurable_snd)
  -- pulling the normalizer inside the double sum over the points of the sample
  have hinnerm : ∀ ω : SuperSample (ℝ × M), Measurable fun p : ℝ × M =>
      ∫⁻ q, ENNReal.ofReal p.1 * ENNReal.ofReal q.1 * A (p.2, q.2) ∂superCounting ω := by
    intro ω
    have h1 : Measurable fun r : (ℝ × M) × SuperSample (ℝ × M) =>
        ∫⁻ q, ENNReal.ofReal r.1.1 * ENNReal.ofReal q.1 * A (r.1.2, q.2)
          ∂superCounting r.2 :=
      measurable_lintegral_superCounting_prod hAq
    have h2 := h1.comp (measurable_id.prodMk (measurable_const : Measurable fun _ : ℝ × M => ω))
    simp only [Function.comp_def] at h2
    exact h2
  have hdouble : ∀ (ω : SuperSample (ℝ × M)) (C : ℝ≥0∞),
      ∫⁻ p, ∫⁻ q, ENNReal.ofReal p.1 * ENNReal.ofReal q.1 * A (p.2, q.2) * C
          ∂superCounting ω ∂superCounting ω
        = (∫⁻ p, ∫⁻ q, ENNReal.ofReal p.1 * ENNReal.ofReal q.1 * A (p.2, q.2)
            ∂superCounting ω ∂superCounting ω) * C := by
    intro ω C
    rw [← lintegral_mul_const _ (hinnerm ω)]
    refine lintegral_congr fun p => ?_
    exact lintegral_mul_const _
      (hAq.comp ((measurable_const : Measurable fun _ : ℝ × M => p).prodMk measurable_id))
  have hf : Measurable fun r : (ℝ × M) × (ℝ × M) × Measure (ℝ × M) =>
      ENNReal.ofReal r.1.1 * ENNReal.ofReal r.2.1.1 * A (r.1.2, r.2.1.2)
        * pdSum V r.2.2 ^ (a - 2) :=
    (hAq.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      ((hS.comp (measurable_snd.comp measurable_snd)).pow_const _)
  have hlhs : ∫⁻ ω, (∫⁻ p, ∫⁻ q, ENNReal.ofReal p.1 * ENNReal.ofReal q.1 * A (p.2, q.2)
          ∂superCounting ω ∂superCounting ω) * pdSum V (superCounting ω) ^ (a - 2)
        ∂pdSampleLaw m η
      = ∫⁻ ω, ∫⁻ p, ∫⁻ q, ENNReal.ofReal p.1 * ENNReal.ofReal q.1 * A (p.2, q.2)
          * pdSum V (superCounting ω) ^ (a - 2) ∂superCounting ω ∂superCounting ω
          ∂pdSampleLaw m η :=
    lintegral_congr fun ω => (hdouble ω _).symm
  rw [hlhs, lintegral_lintegral_lintegral_pdSampleLaw m η
    (f := fun r : (ℝ × M) × (ℝ × M) × Measure (ℝ × M) =>
      ENNReal.ofReal r.1.1 * ENNReal.ofReal r.2.1.1 * A (r.1.2, r.2.1.2)
        * pdSum V r.2.2 ^ (a - 2)) hf]
  have hlaw := hasLaw_superCounting_pdProcess m η
  congr 1
  · -- the off-diagonal term
    have hΦ : Measurable fun N : Measure (ℝ × M) =>
        ∫⁻ p, ∫⁻ q, ENNReal.ofReal p.1 * ENNReal.ofReal q.1 * A (p.2, q.2)
          * pdSum V (N + Measure.dirac p + Measure.dirac q) ^ (a - 2)
          ∂pdIntensity m η ∂pdIntensity m η := by
      simp_rw [pdSum_add_dirac hV]
      have h2 : Measurable fun r : (Measure (ℝ × M) × (ℝ × M)) × (ℝ × M) =>
          ENNReal.ofReal r.1.2.1 * ENNReal.ofReal r.2.1 * A (r.1.2.2, r.2.2)
            * (pdSum V r.1.1 + ENNReal.ofReal r.1.2.1 * V r.1.2.2
              + ENNReal.ofReal r.2.1 * V r.2.2) ^ (a - 2) :=
        (hAq.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).mul
          ((((hS.comp (measurable_fst.comp measurable_fst)).add
            (hx.comp (measurable_snd.comp measurable_fst))).add
            (hx.comp measurable_snd)).pow_const _)
      have h3 : Measurable fun r : Measure (ℝ × M) × (ℝ × M) =>
          ∫⁻ q, ENNReal.ofReal r.2.1 * ENNReal.ofReal q.1 * A (r.2.2, q.2)
            * (pdSum V r.1 + ENNReal.ofReal r.2.1 * V r.2.2
              + ENNReal.ofReal q.1 * V q.2) ^ (a - 2) ∂pdIntensity m η :=
        Measurable.lintegral_prod_right' (ν := pdIntensity m η) h2
      exact Measurable.lintegral_prod_right' (ν := pdIntensity m η) h3
    rw [hlaw.lintegral_comp hΦ.aemeasurable]
    simp_rw [pdSum_add_dirac hV]
    exact lintegral_offDiag_pdProcess hm0 hm1 η hA hV hVpos hκ ham
  · -- the diagonal term
    have hΨ : Measurable fun N : Measure (ℝ × M) =>
        ∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * A (p.2, p.2)
          * pdSum V (N + Measure.dirac p) ^ (a - 2) ∂pdIntensity m η := by
      have h2 : Measurable fun r : Measure (ℝ × M) × (ℝ × M) =>
          ENNReal.ofReal r.2.1 * ENNReal.ofReal r.2.1 * A (r.2.2, r.2.2)
            * pdSum V (r.1 + Measure.dirac r.2) ^ (a - 2) := by
        simp_rw [pdSum_add_dirac hV]
        exact (hsq.comp measurable_snd).mul
          (((hS.comp measurable_fst).add (hx.comp measurable_snd)).pow_const _)
      exact Measurable.lintegral_prod_right' (ν := pdIntensity m η) h2
    rw [hlaw.lintegral_comp hΨ.aemeasurable]
    have hf2 : Measurable fun r : (ℝ × M) × Measure (ℝ × M) =>
        ENNReal.ofReal r.1.1 * ENNReal.ofReal r.1.1 * A (r.1.2, r.1.2)
          * pdSum V r.2 ^ (a - 2) :=
      (hsq.comp measurable_fst).mul ((hS.comp measurable_snd).pow_const _)
    have hcst : ∀ N : Measure (ℝ × M), ∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1
        * A (p.2, p.2) * pdSum V N ^ (a - 2) ∂N
        = (∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * A (p.2, p.2) ∂N)
          * pdSum V N ^ (a - 2) := fun N => lintegral_mul_const _ hsq
    have hF2 : Measurable fun N : Measure (ℝ × M) => ∫⁻ p, ENNReal.ofReal p.1
        * ENNReal.ofReal p.1 * A (p.2, p.2) * pdSum V N ^ (a - 2) ∂N := by
      simp_rw [hcst]
      exact (Measure.measurable_lintegral hsq).mul (hS.pow_const _)
    rw [← lintegral_lintegral_pdProcess m η
      (f := fun r : (ℝ × M) × Measure (ℝ × M) => ENNReal.ofReal r.1.1 * ENNReal.ofReal r.1.1
        * A (r.1.2, r.1.2) * pdSum V r.2 ^ (a - 2)) hf2 hF2]
    simp_rw [hcst]
    exact lintegral_pdSumSq_mul_rpow_pdSum hm0 hm1 η hAd hV hVpos hκ ham

/-- The constant of the off-diagonal term in terms of the moment `𝔼 S_V^a`:
`K₀(a) κ² = (m - a)/(1 - a) · 𝔼 S_V^a`, for `0 ≤ a < m`. Together with
`ofReal_pdSqConst_mul_lintegral` this exhibits `lintegral_pdSum_sq_mul_rpow_pdSum` as a convex
combination with weights `(m-a)/(1-a)` and `(1-m)/(1-a)`, which is the one-level case of
Talagrand's (14.32). -/
theorem ofReal_pdOffConst_mul_lintegral {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {V : M → ℝ≥0∞} (hV : Measurable V) (hVpos : ∀ᵐ g ∂η, 0 < V g)
    (hκ : ∫⁻ g, V g ^ m ∂η ≠ ∞) {a : ℝ} (ha0 : 0 ≤ a) (ham : a < m) :
    ENNReal.ofReal (pdOffConst m a (stableConst m) (∫⁻ g, V g ^ m ∂η).toReal)
        * (∫⁻ g, V g ^ m ∂η) ^ 2
      = ENNReal.ofReal ((m - a) / (1 - a)) * ∫⁻ N, pdSum V N ^ a ∂pdProcess m η := by
  have hc : 0 < stableConst m := stableConst_pos hm0 hm1
  have ha1 : a < 1 := ham.trans hm1
  have hq1 : a / m ≤ 1 := (div_le_one hm0).2 ham.le
  have hκpos : 0 < (∫⁻ g, V g ^ m ∂η).toReal :=
    ENNReal.toReal_pos (lintegral_rpow_pos_of_ae_pos hm0 η hV hVpos).ne' hκ
  obtain ⟨κr, hκr0, hκr⟩ : ∃ κr : ℝ, 0 < κr ∧ (∫⁻ g, V g ^ m ∂η).toReal = κr := ⟨_, hκpos, rfl⟩
  have hκe : ∫⁻ g, V g ^ m ∂η = ENNReal.ofReal κr := by rw [← hκr, ENNReal.ofReal_toReal hκ]
  have hΓa' : 0 < Real.Gamma (1 - a) := Real.Gamma_pos_of_pos (by linarith)
  have hnn : 0 ≤ pdOffConst m a (stableConst m) κr := by
    unfold pdOffConst
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (Real.Gamma_nonneg_of_nonneg (by linarith)))
      (Real.rpow_nonneg (by positivity) _))
      (mul_nonneg hm0.le (Real.Gamma_nonneg_of_nonneg (by linarith)))
  have hmom : ∫⁻ N, pdSum V N ^ a ∂pdProcess m η
      = ENNReal.ofReal ((stableConst m * κr) ^ (a / m) * Real.Gamma (1 - a / m)
          / Real.Gamma (1 - a)) := by
    rcases eq_or_lt_of_le ha0 with rfl | ha0'
    · simp only [ENNReal.rpow_zero, lintegral_const, measure_univ, mul_one, zero_div,
        sub_zero, Real.rpow_zero, Real.Gamma_one, div_one, ENNReal.ofReal_one]
    · rw [lintegral_pdSum_rpow_eq_Gamma hm0 hm1 η hV hκ ha0' ham, hκr]
  rw [hmom, hκr, hκe, ← ENNReal.ofReal_pow hκr0.le, ← ENNReal.ofReal_mul hnn,
    ← ENNReal.ofReal_mul (div_nonneg (by linarith) (by linarith))]
  congr 1
  have hΓm : Real.Gamma (1 - m) = m * stableConst m := (mul_stableConst_eq_Gamma hm0 hm1).symm
  have hΓa : Real.Gamma (2 - a) = (1 - a) * Real.Gamma (1 - a) := by
    rw [show (2 : ℝ) - a = (1 - a) + 1 by ring, Real.Gamma_add_one (by linarith)]
  have hΓq : Real.Gamma (2 - a / m) = (1 - a / m) * Real.Gamma (1 - a / m) := by
    rw [show (2 : ℝ) - a / m = (1 - a / m) + 1 by ring, Real.Gamma_add_one (by
      have : 0 ≤ a / m := div_nonneg ha0 hm0.le
      rcases eq_or_lt_of_le hq1 with h | h
      · exact absurd ((div_eq_one_iff_eq hm0.ne').1 h) (by linarith)
      · linarith)]
  have hsq : (stableConst m * κr) ^ (2 : ℝ) = (stableConst m * κr) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (stableConst m * κr) 2]
    norm_num
  have hpow : (stableConst m * κr) ^ (a / m - 2)
      = (stableConst m * κr) ^ (a / m) / (stableConst m * κr) ^ (2 : ℕ) := by
    rw [Real.rpow_sub (by positivity), hsq]
  rw [pdOffConst, hΓm, hΓa, hΓq, hpow]
  field_simp


/-! ### The off-diagonal one-level identity: pairs of distinct points -/

/-- **The off-diagonal bivariate Mecke equation for the Poisson–Dirichlet process**, at the level
of the sample. -/
theorem lintegral_superOffDiagSum_pdSampleLaw (m : ℝ) (η : Measure M) [IsFiniteMeasure η]
    {f : (ℝ × M) × (ℝ × M) × Measure (ℝ × M) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, superOffDiagSum ω (fun p q => f (p, q, superCounting ω)) ∂pdSampleLaw m η
      = ∫⁻ ω, ∫⁻ p, ∫⁻ q, f (p, q, superCounting ω + Measure.dirac p + Measure.dirac q)
          ∂pdIntensity m η ∂pdIntensity m η ∂pdSampleLaw m η := by
  rw [← sum_pdSeq m η, pdSampleLaw]
  exact lintegral_superOffDiagSum_superCounting (pdSeq m η) hf

/-- **The off-diagonal one-level identity for a pair function**, `a < m`: the sum over ordered
pairs of **distinct** points against a negative power of the normalizer is the off-diagonal
term alone,

`𝔼 (∑_{α ≠ γ} u_α u_γ A(g_α, g_γ)) (∑_α u_α V(g_α))^{a-2}
  = K₀(a) ∫∫ A(g,g') V(g)^{m-1} V(g')^{m-1} dη dη`.

It is the off-diagonal Mecke equation followed by `lintegral_offDiag_pdProcess`, so it holds with
**no** finiteness hypothesis on `A` — the diagonal is never formed, hence never cancelled. -/
theorem lintegral_superOffDiagSumPair_mul_rpow_pdSum {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1)
    (η : Measure M) [IsProbabilityMeasure η] {A : M × M → ℝ≥0∞} {V : M → ℝ≥0∞}
    (hA : Measurable A) (hV : Measurable V) (hVpos : ∀ᵐ g ∂η, 0 < V g)
    (hκ : ∫⁻ g, V g ^ m ∂η ≠ ∞) {a : ℝ} (ham : a < m) :
    ∫⁻ ω, superOffDiagSum ω (fun p q : ℝ × M =>
          ENNReal.ofReal p.1 * ENNReal.ofReal q.1 * A (p.2, q.2))
        * pdSum V (superCounting ω) ^ (a - 2) ∂pdSampleLaw m η
      = ENNReal.ofReal (pdOffConst m a (stableConst m) (∫⁻ g, V g ^ m ∂η).toReal)
          * ∫⁻ g, ∫⁻ g', A (g, g') * V g ^ (m - 1) * V g' ^ (m - 1) ∂η ∂η := by
  have hS := measurable_pdSum (v := V) hV
  have hx : Measurable fun p : ℝ × M => ENNReal.ofReal p.1 * V p.2 := measurable_ofReal_mul hV
  have hAq : Measurable fun r : (ℝ × M) × (ℝ × M) => ENNReal.ofReal r.1.1 * ENNReal.ofReal r.2.1
      * A (r.1.2, r.2.2) :=
    ((ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_fst)).mul
      (ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_snd))).mul
      (hA.comp ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)))
  have hf : Measurable fun r : (ℝ × M) × (ℝ × M) × Measure (ℝ × M) =>
      ENNReal.ofReal r.1.1 * ENNReal.ofReal r.2.1.1 * A (r.1.2, r.2.1.2)
        * pdSum V r.2.2 ^ (a - 2) :=
    (hAq.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      ((hS.comp (measurable_snd.comp measurable_snd)).pow_const _)
  -- the normalizer goes inside the sum over pairs
  have hlhs : ∫⁻ ω, superOffDiagSum ω (fun p q : ℝ × M =>
          ENNReal.ofReal p.1 * ENNReal.ofReal q.1 * A (p.2, q.2))
        * pdSum V (superCounting ω) ^ (a - 2) ∂pdSampleLaw m η
      = ∫⁻ ω, superOffDiagSum ω (fun p q : ℝ × M =>
          ENNReal.ofReal p.1 * ENNReal.ofReal q.1 * A (p.2, q.2)
            * pdSum V (superCounting ω) ^ (a - 2)) ∂pdSampleLaw m η :=
    lintegral_congr fun ω => (superOffDiagSum_mul_const ω _ _).symm
  rw [hlhs, lintegral_superOffDiagSum_pdSampleLaw m η
    (f := fun r : (ℝ × M) × (ℝ × M) × Measure (ℝ × M) =>
      ENNReal.ofReal r.1.1 * ENNReal.ofReal r.2.1.1 * A (r.1.2, r.2.1.2)
        * pdSum V r.2.2 ^ (a - 2)) hf]
  have hlaw := hasLaw_superCounting_pdProcess m η
  have hΦ : Measurable fun N : Measure (ℝ × M) =>
      ∫⁻ p, ∫⁻ q, ENNReal.ofReal p.1 * ENNReal.ofReal q.1 * A (p.2, q.2)
        * pdSum V (N + Measure.dirac p + Measure.dirac q) ^ (a - 2)
        ∂pdIntensity m η ∂pdIntensity m η := by
    simp_rw [pdSum_add_dirac hV]
    have h2 : Measurable fun r : (Measure (ℝ × M) × (ℝ × M)) × (ℝ × M) =>
        ENNReal.ofReal r.1.2.1 * ENNReal.ofReal r.2.1 * A (r.1.2.2, r.2.2)
          * (pdSum V r.1.1 + ENNReal.ofReal r.1.2.1 * V r.1.2.2
            + ENNReal.ofReal r.2.1 * V r.2.2) ^ (a - 2) :=
      (hAq.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).mul
        ((((hS.comp (measurable_fst.comp measurable_fst)).add
          (hx.comp (measurable_snd.comp measurable_fst))).add
          (hx.comp measurable_snd)).pow_const _)
    have h3 : Measurable fun r : Measure (ℝ × M) × (ℝ × M) =>
        ∫⁻ q, ENNReal.ofReal r.2.1 * ENNReal.ofReal q.1 * A (r.2.2, q.2)
          * (pdSum V r.1 + ENNReal.ofReal r.2.1 * V r.2.2
            + ENNReal.ofReal q.1 * V q.2) ^ (a - 2) ∂pdIntensity m η :=
      Measurable.lintegral_prod_right' (ν := pdIntensity m η) h2
    exact Measurable.lintegral_prod_right' (ν := pdIntensity m η) h3
  rw [hlaw.lintegral_comp hΦ.aemeasurable]
  simp_rw [pdSum_add_dirac hV]
  exact lintegral_offDiag_pdProcess hm0 hm1 η hA hV hVpos hκ ham

/-- **The off-diagonal one-level identity for a product numerator**, `a < m`:

`𝔼 (∑_{α ≠ γ} u_α u_γ A(g_α) B(g_γ)) (∑_α u_α V(g_α))^{a-2}
  = K₀(a) (∫ A V^{m-1} dη)(∫ B V^{m-1} dη)`.

At `a = 0` this is Talagrand's (13.15). -/
theorem lintegral_superOffDiagSum_mul_rpow_pdSum {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1)
    (η : Measure M) [IsProbabilityMeasure η] {A B V : M → ℝ≥0∞} (hA : Measurable A)
    (hB : Measurable B) (hV : Measurable V) (hVpos : ∀ᵐ g ∂η, 0 < V g)
    (hκ : ∫⁻ g, V g ^ m ∂η ≠ ∞) {a : ℝ} (ham : a < m) :
    ∫⁻ ω, superOffDiagSum ω (fun p q : ℝ × M =>
          ENNReal.ofReal p.1 * A p.2 * (ENNReal.ofReal q.1 * B q.2))
        * pdSum V (superCounting ω) ^ (a - 2) ∂pdSampleLaw m η
      = ENNReal.ofReal (pdOffConst m a (stableConst m) (∫⁻ g, V g ^ m ∂η).toReal)
          * ((∫⁻ g, A g * V g ^ (m - 1) ∂η) * ∫⁻ g, B g * V g ^ (m - 1) ∂η) := by
  have hApair : Measurable fun r : M × M => A r.1 * B r.2 :=
    (hA.comp measurable_fst).mul (hB.comp measurable_snd)
  have hAV : Measurable fun g => A g * V g ^ (m - 1) := hA.mul (hV.pow_const _)
  have hBV : Measurable fun g => B g * V g ^ (m - 1) := hB.mul (hV.pow_const _)
  have hF : ∀ ω : SuperSample (ℝ × M), superOffDiagSum ω (fun p q : ℝ × M =>
        ENNReal.ofReal p.1 * A p.2 * (ENNReal.ofReal q.1 * B q.2))
      = superOffDiagSum ω (fun p q : ℝ × M =>
          ENNReal.ofReal p.1 * ENNReal.ofReal q.1 * (fun r : M × M => A r.1 * B r.2) (p.2, q.2)) :=
    fun ω => superOffDiagSum_congr ω fun p q => by simp only; ring
  simp_rw [hF]
  rw [lintegral_superOffDiagSumPair_mul_rpow_pdSum hm0 hm1 η hApair hV hVpos hκ ham]
  congr 1
  have hin : ∀ g : M, ∫⁻ g', (fun r : M × M => A r.1 * B r.2) (g, g') * V g ^ (m - 1)
      * V g' ^ (m - 1) ∂η
      = (A g * V g ^ (m - 1)) * ∫⁻ g', B g' * V g' ^ (m - 1) ∂η := by
    intro g
    rw [← lintegral_const_mul _ hBV]
    exact lintegral_congr fun g' => by simp only; ring
  simp_rw [hin]
  exact lintegral_mul_const _ hAV

/-! ### Identity (13.15): the sum over pairs of distinct points -/

/-- **Identity (13.15)** (Talagrand Vol. II, Theorem 13.1.6), in `ℝ≥0∞`:

`𝔼 (∑_{α ≠ γ} v_α v_γ U_α W_γ)
  = m (∫ U V^{m-1} dη / ∫ V^m dη)(∫ W V^{m-1} dη / ∫ V^m dη)`,

the sum being over ordered pairs of **distinct** points.  Because `α ≠ γ` refers to the *indices*
of the points, the statement lives on the sample space, through `superOffDiagSum`.

It is the case `a = 0` of the off-diagonal one-level identity
`lintegral_superOffDiagSum_mul_rpow_pdSum`, i.e. of the **off-diagonal bivariate Mecke equation**
(`lintegral_superOffDiagSum_superCounting`): the diagonal is never formed, so — unlike
Talagrand's derivation, which subtracts (13.14) from (13.16) and needs `𝔼U² + 𝔼W² < ∞` for the
cancellation — no finiteness of any moment of `U`, `W` is required. -/
theorem lintegral_superOffDiagSum_mul_inv_pdSum_sq {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1)
    (η : Measure M) [IsProbabilityMeasure η] {U W V : M → ℝ≥0∞} (hU : Measurable U)
    (hW : Measurable W) (hV : Measurable V) (hVpos : ∀ᵐ g ∂η, 0 < V g)
    (hκ : ∫⁻ g, V g ^ m ∂η ≠ ∞) :
    ∫⁻ ω, superOffDiagSum ω (fun p q : ℝ × M =>
            ENNReal.ofReal p.1 * U p.2 * (ENNReal.ofReal q.1 * W q.2))
          * ((pdSum V (superCounting ω))⁻¹ * (pdSum V (superCounting ω))⁻¹) ∂pdSampleLaw m η
      = ENNReal.ofReal m
        * ((∫⁻ g, U g * V g ^ (m - 1) ∂η) * (∫⁻ g, V g ^ m ∂η)⁻¹
            * ((∫⁻ g, W g * V g ^ (m - 1) ∂η) * (∫⁻ g, V g ^ m ∂η)⁻¹)) := by
  have hκpos : 0 < (∫⁻ g, V g ^ m ∂η).toReal :=
    ENNReal.toReal_pos (lintegral_rpow_pos_of_ae_pos hm0 η hV hVpos).ne' hκ
  have hkr : ENNReal.ofReal (∫⁻ g, V g ^ m ∂η).toReal = ∫⁻ g, V g ^ m ∂η :=
    ENNReal.ofReal_toReal hκ
  have hneg : ∀ x : ℝ≥0∞, x ^ (-(2 : ℝ)) = x⁻¹ * x⁻¹ := by
    intro x
    rw [ENNReal.rpow_neg, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
      ENNReal.inv_pow, pow_two]
  have hkey := lintegral_superOffDiagSum_mul_rpow_pdSum hm0 hm1 η hU hW hV hVpos hκ
    (a := 0) hm0
  simp only [zero_sub] at hkey
  simp_rw [hneg] at hkey
  have h0 : ENNReal.ofReal (pdOffConst m 0 (stableConst m) (∫⁻ g, V g ^ m ∂η).toReal)
      = ENNReal.ofReal m * ((∫⁻ g, V g ^ m ∂η)⁻¹ * (∫⁻ g, V g ^ m ∂η)⁻¹) := by
    rw [pdOffConst_zero hm0 hm1 hκpos, ENNReal.ofReal_div_of_pos (by positivity),
      ENNReal.ofReal_pow hκpos.le, hkr, div_eq_mul_inv, ENNReal.inv_pow, pow_two]
  rw [hkey, h0]
  ring

/-- **The off-diagonal mass of the Poisson–Dirichlet weights**: `𝔼 ∑_{α ≠ γ} v_α v_γ = m`.  This
is the case `U = V = W = 1` of (13.15), and the exact complement of `𝔼 ∑_α v_α² = 1 - m` (13.17):
the two together say that the total mass `(∑_α v_α)² = 1` splits as `(1 - m) + m`. -/
theorem lintegral_superOffDiagSum_one_mul_inv_pdSum_one_sq {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1)
    (η : Measure M) [IsProbabilityMeasure η] :
    ∫⁻ ω, superOffDiagSum ω (fun p q : ℝ × M => ENNReal.ofReal p.1 * ENNReal.ofReal q.1)
        * ((pdSum (fun _ => 1) (superCounting ω))⁻¹
            * (pdSum (fun _ => 1) (superCounting ω))⁻¹) ∂pdSampleLaw m η
      = ENNReal.ofReal m := by
  have h := lintegral_superOffDiagSum_mul_inv_pdSum_sq hm0 hm1 η (U := fun _ => 1)
    (W := fun _ => 1) (V := fun _ => 1) measurable_const measurable_const measurable_const
    (Filter.Eventually.of_forall fun _ => one_pos) (by simp)
  simpa using h

end ProbabilityTheory

end
