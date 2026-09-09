/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.PointProcess.PoissonSuperposition
import Common.Mathlib.Probability.PointProcess.StableIntensity
import Common.Mathlib.Analysis.SpecialFunctions.FrullaniExp

/-!
# The Poisson–Dirichlet point process and Talagrand's fundamental identities

Talagrand, *Mean Field Models for Spin Glasses*, Vol. II, §13.1. The marked Poisson point
process `(u_α, g_α)` with intensity `μ_m ⊗ η`, where `μ_m` has density `u^{-m-1}` on `(0, ∞)` and
`η` is the law of the marks, is the probability measure `pdProcess m η` on the space of measures
on `ℝ × M`. For measurable weights `v : M → ℝ≥0∞` on the marks, the random sum
`S_v = ∑_α u_α v(g_α)` is the function `pdSum v` of the counting measure, and has Laplace
transform

`𝔼 e^{-s S_v} = exp (-s^m c_m ∫ v^m dη)`

(Lemma 13.1.1 and Corollary 13.1.2 in Laplace form). From it: `S_v` is a.s. finite and positive,
its tails are `P(S_v > t) ≤ C t^{-m}` and `P(S_v < t) ≤ e^{-C t^{-m}}`, `𝔼|log S_v| < ∞`,
the **moments of order `m' < m`** are explicit,

`𝔼 S_v^{m'} = (c_m ∫ v^m dη)^{m'/m} · c_{m'/m} / (m c_{m'})`,

which contains (13.8) and (13.9), and **Talagrand's identity (13.10)** holds:

`𝔼 log ∑_α u_α v(g_α) = 𝔼 log ∑_α u_α + (1/m) log ∫ v^m dη`.

Every statement is proved for the law `pdProcess m η` and then transported to any random measure
`N` with `HasLaw N (pdProcess m η) P` — the form in which the multi-level cascades use them.

## Main statements

- `ProbabilityTheory.pdIntensity`, `ProbabilityTheory.pdProcess`, `ProbabilityTheory.pdSum`.
- `ProbabilityTheory.integral_negExp_pdSum`: **the Laplace transform**.
- `ProbabilityTheory.lintegral_pdSum_rpow`: **the moments** `𝔼 S_v^{m'}`, `0 < m' < m`;
  `ProbabilityTheory.lintegral_pdSum_rpow_eq_mul` is (13.9) and
  `ProbabilityTheory.lintegral_pdSum_rpow_lt_top` is (13.8).
- `ProbabilityTheory.ae_pdSum_lt_top`, `ProbabilityTheory.ae_pdSum_pos`.
- `ProbabilityTheory.measureReal_lt_pdSum_le`, `ProbabilityTheory.measureReal_pdSum_lt_le`: tails.
- `ProbabilityTheory.integrable_log_pdSum`: `𝔼|log S_v| < ∞`.
- `ProbabilityTheory.integral_log_pdSum_eq`: **Talagrand's identity (13.10)**.
- `ProbabilityTheory.integral_log_pdSum_div_eq`: **Theorem 13.1.5**.
- `ProbabilityTheory.HasLaw.integral_log_pdSum_eq` and friends: the `HasLaw` forms.
- `ProbabilityTheory.measureReal_eq_top_of_laplace`,
  `ProbabilityTheory.measureReal_lt_le_of_laplace`,
  `ProbabilityTheory.integrable_log_toReal_of_tails`: the general facts about a nonnegative
  random variable with Laplace transform `exp (-A s^m)`, or with polynomial upper and
  stretched-exponential lower tails.
-/

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace ProbabilityTheory

open ENNReal

noncomputable section

/-! ### Consequences of a Laplace transform `exp (-A s^m)` -/

section Laplace

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {S : Ω → ℝ≥0∞}

/-- A nonnegative random variable whose Laplace transform is `exp (-A s^m)` for all `s > 0`, with
`m > 0`, is almost surely finite: let `s → 0⁺`. -/
theorem measureReal_eq_top_of_laplace (hS : Measurable S) {m A : ℝ} (hm0 : 0 < m) (hA : 0 ≤ A)
    (hL : ∀ s : ℝ, 0 < s → ∫ ω, negExp (ENNReal.ofReal s * S ω) ∂P = Real.exp (-(s ^ m * A))) :
    P.real {ω | S ω = ∞} = 0 := by
  have hAm : MeasurableSet {ω | S ω = ∞} := measurableSet_eq_fun hS measurable_const
  have key : ∀ s : ℝ, 0 < s → Real.exp (-(s ^ m * A)) ≤ 1 - P.real {ω | S ω = ∞} := by
    intro s hs
    rw [← hL s hs]
    have hpt : ∀ ω, negExp (ENNReal.ofReal s * S ω) ≤ {ω | S ω = ∞}ᶜ.indicator 1 ω := by
      intro ω
      by_cases hω : S ω = ∞
      · rw [hω, ENNReal.mul_top (ENNReal.ofReal_pos.2 hs).ne', negExp_top]
        have : ω ∉ {ω | S ω = ∞}ᶜ := by simp [hω]
        rw [Set.indicator_of_notMem this]
      · have : ω ∈ {ω | S ω = ∞}ᶜ := by simpa using hω
        rw [Set.indicator_of_mem this, Pi.one_apply]
        exact negExp_le_one _
    have hint1 : Integrable (fun ω => negExp (ENNReal.ofReal s * S ω)) P :=
      Integrable.mono' (integrable_const 1)
        (measurable_negExp.comp (measurable_const.mul hS)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (negExp_nonneg _)]; exact negExp_le_one _)
    have hint2 : Integrable ({ω | S ω = ∞}ᶜ.indicator (1 : Ω → ℝ)) P :=
      (integrable_const 1).indicator hAm.compl
    calc ∫ ω, negExp (ENNReal.ofReal s * S ω) ∂P
        ≤ ∫ ω, {ω | S ω = ∞}ᶜ.indicator 1 ω ∂P := integral_mono hint1 hint2 hpt
      _ = P.real {ω | S ω = ∞}ᶜ := integral_indicator_one hAm.compl
      _ = 1 - P.real {ω | S ω = ∞} := by rw [measureReal_compl hAm, probReal_univ]
  have hbound : ∀ ε : ℝ, 0 < ε → P.real {ω | S ω = ∞} ≤ ε := by
    intro ε hε
    have hpos : 0 < A + 1 := by linarith
    have hs : 0 < (ε / (A + 1)) ^ (1 / m) := Real.rpow_pos_of_pos (div_pos hε hpos) _
    have hsm : ((ε / (A + 1)) ^ (1 / m)) ^ m = ε / (A + 1) := by
      rw [← Real.rpow_mul (div_pos hε hpos).le, one_div_mul_cancel hm0.ne', Real.rpow_one]
    have h1 := key _ hs
    rw [hsm] at h1
    have h2 : 1 - ε / (A + 1) * A ≤ Real.exp (-(ε / (A + 1) * A)) := by
      linarith [Real.add_one_le_exp (-(ε / (A + 1) * A))]
    have h3 : ε / (A + 1) * A ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
      nlinarith
    linarith
  have hle : P.real {ω | S ω = ∞} ≤ 0 :=
    le_of_forall_pos_le_add fun ε hε => by simpa using hbound ε hε
  exact le_antisymm hle measureReal_nonneg

theorem ae_lt_top_of_laplace (hS : Measurable S) {m A : ℝ} (hm0 : 0 < m) (hA : 0 ≤ A)
    (hL : ∀ s : ℝ, 0 < s → ∫ ω, negExp (ENNReal.ofReal s * S ω) ∂P = Real.exp (-(s ^ m * A))) :
    ∀ᵐ ω ∂P, S ω < ∞ := by
  have h := measureReal_eq_top_of_laplace hS hm0 hA hL
  rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at h
  have h' : P {ω | S ω = ∞} = 0 := h.resolve_right (measure_ne_top _ _)
  rw [ae_iff]
  convert h' using 2
  ext ω
  simp [lt_top_iff_ne_top]

/-- **The upper tail from the Laplace transform**: if `𝔼 e^{-S/t} = exp (-A t^{-m})`, then
`P (S > t) ≤ (1 - e^{-1})⁻¹ A t^{-m}`. -/
theorem measureReal_lt_le_of_laplace (hS : Measurable S) {m A t : ℝ} (ht : 0 < t)
    (hL : ∫ ω, negExp (ENNReal.ofReal (1 / t) * S ω) ∂P = Real.exp (-((1 / t) ^ m * A))) :
    P.real {ω | ENNReal.ofReal t < S ω} ≤ (1 - Real.exp (-1))⁻¹ * (t ^ (-m) * A) := by
  have hset : MeasurableSet {ω | ENNReal.ofReal t < S ω} := measurableSet_lt measurable_const hS
  have he : 0 < 1 - Real.exp (-1) := by
    linarith [Real.exp_lt_one_iff.2 (by norm_num : (-1 : ℝ) < 0)]
  have hpt : ∀ ω, (1 - Real.exp (-1)) * {ω | ENNReal.ofReal t < S ω}.indicator 1 ω
      ≤ 1 - negExp (ENNReal.ofReal (1 / t) * S ω) := by
    intro ω
    by_cases hω : ENNReal.ofReal t < S ω
    · rw [Set.indicator_of_mem (show ω ∈ {ω | ENNReal.ofReal t < S ω} from hω), Pi.one_apply,
        mul_one]
      have h1 : (1 : ℝ≥0∞) < ENNReal.ofReal (1 / t) * S ω := by
        have h0 : ENNReal.ofReal (1 / t) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
        have := ENNReal.mul_lt_mul_left h0 ENNReal.ofReal_ne_top hω
        rw [← ENNReal.ofReal_mul ht.le, mul_one_div_cancel ht.ne', ENNReal.ofReal_one,
          mul_comm] at this
        exact this
      have h2 : negExp (ENNReal.ofReal (1 / t) * S ω) ≤ Real.exp (-1) := by
        have := negExp_antitone h1.le
        rwa [negExp_of_ne_top ENNReal.one_ne_top, ENNReal.toReal_one] at this
      linarith
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | ENNReal.ofReal t < S ω} from hω), mul_zero]
      linarith [negExp_le_one (ENNReal.ofReal (1 / t) * S ω)]
  have hint' : Integrable (fun ω => negExp (ENNReal.ofReal (1 / t) * S ω)) P :=
    Integrable.mono' (integrable_const 1)
      (measurable_negExp.comp (measurable_const.mul hS)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (negExp_nonneg _)]; exact negExp_le_one _)
  have hint2 : Integrable (fun ω => (1 - Real.exp (-1))
      * {ω | ENNReal.ofReal t < S ω}.indicator 1 ω) P :=
    ((integrable_const 1).indicator hset).const_mul _
  have hint : Integrable (fun ω => 1 - negExp (ENNReal.ofReal (1 / t) * S ω)) P :=
    (integrable_const 1).sub hint'
  have hle := integral_mono hint2 hint hpt
  rw [integral_const_mul, integral_indicator_one hset, integral_sub (integrable_const 1) hint',
    integral_const, probReal_univ, one_smul, hL] at hle
  have h3 : (1 / t) ^ m = t ^ (-m) := by
    rw [one_div, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
  rw [h3] at hle
  have h2 : 1 - Real.exp (-(t ^ (-m) * A)) ≤ t ^ (-m) * A := by
    linarith [Real.add_one_le_exp (-(t ^ (-m) * A))]
  rw [← div_eq_inv_mul, le_div_iff₀ he]
  linarith

omit [IsProbabilityMeasure P] in
lemma measurable_log_toReal (hS : Measurable S) :
    Measurable fun ω => Real.log (S ω).toReal :=
  Real.measurable_log.comp (ENNReal.measurable_toReal.comp hS)

omit [MeasurableSpace Ω] in
/-- `r < log S` forces `e^r < S`, for `r > 0`. -/
lemma subset_lt_of_lt_log {r : ℝ} (hr0 : 0 < r) :
    {ω | r < max (Real.log (S ω).toReal) 0} ⊆ {ω | ENNReal.ofReal (Real.exp r) < S ω} := by
  intro ω hω
  rw [Set.mem_ofPred_eq] at hω ⊢
  have hr : r < Real.log (S ω).toReal := by
    rcases lt_max_iff.1 hω with h | h
    · exact h
    · exact absurd h (not_lt.2 hr0.le)
  have hx : 0 < (S ω).toReal := by
    by_contra hcon
    push Not at hcon
    have hzero : (S ω).toReal = 0 := le_antisymm hcon ENNReal.toReal_nonneg
    rw [hzero, Real.log_zero] at hr
    exact absurd hr (not_lt.2 hr0.le)
  have hne : S ω ≠ ∞ := by
    intro h
    rw [h, ENNReal.toReal_top] at hx
    exact lt_irrefl _ hx
  rw [Real.lt_log_iff_exp_lt hx] at hr
  calc ENNReal.ofReal (Real.exp r) < ENNReal.ofReal (S ω).toReal :=
        (ENNReal.ofReal_lt_ofReal_iff hx).2 hr
    _ = S ω := ENNReal.ofReal_toReal hne

omit [MeasurableSpace Ω] in
/-- `r < -log S` forces `S < e^{-r}`, for `r > 0`. -/
lemma subset_lt_of_lt_neg_log {r : ℝ} (hr0 : 0 < r) :
    {ω | r < max (-Real.log (S ω).toReal) 0} ⊆ {ω | S ω < ENNReal.ofReal (Real.exp (-r))} := by
  intro ω hω
  rw [Set.mem_ofPred_eq] at hω ⊢
  have hr : Real.log (S ω).toReal < -r := by
    rcases lt_max_iff.1 hω with h | h
    · linarith
    · exact absurd h (not_lt.2 hr0.le)
  have hx : 0 < (S ω).toReal := by
    by_contra hcon
    push Not at hcon
    have hzero : (S ω).toReal = 0 := le_antisymm hcon ENNReal.toReal_nonneg
    rw [hzero, Real.log_zero] at hr
    linarith
  have hne : S ω ≠ ∞ := by
    intro h
    rw [h, ENNReal.toReal_top] at hx
    exact lt_irrefl _ hx
  rw [Real.log_lt_iff_lt_exp hx] at hr
  calc S ω = ENNReal.ofReal (S ω).toReal := (ENNReal.ofReal_toReal hne).symm
    _ < ENNReal.ofReal (Real.exp (-r)) := (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).2 hr

/-- **`𝔼 |log S| < ∞` from the tails**: a polynomial upper tail `P (S > t) ≤ C t^{-m}` and a
stretched-exponential lower tail `P (S < t) ≤ e^{-D t^{-m}}` make `log S` integrable. -/
theorem integrable_log_toReal_of_tails (hS : Measurable S) {m C D : ℝ} (hm0 : 0 < m)
    (hD : 0 < D)
    (hup : ∀ t : ℝ, 0 < t → P.real {ω | ENNReal.ofReal t < S ω} ≤ C * t ^ (-m))
    (hlow : ∀ t : ℝ, 0 < t → P.real {ω | S ω < ENNReal.ofReal t} ≤ Real.exp (-(D * t ^ (-m)))) :
    Integrable (fun ω => Real.log (S ω).toReal) P := by
  have hmeas := measurable_log_toReal hS
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  simp_rw [Real.enorm_eq_ofReal_abs]
  have habs : ∀ ω, ENNReal.ofReal |Real.log (S ω).toReal|
      = ENNReal.ofReal (max (Real.log (S ω).toReal) 0)
        + ENNReal.ofReal (max (-Real.log (S ω).toReal) 0) := by
    intro ω
    rw [← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
    congr 1
    rcases le_or_gt 0 (Real.log (S ω).toReal) with h | h
    · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [abs_of_neg h, max_eq_right h.le, max_eq_left (by linarith)]; ring
  simp_rw [habs]
  have hm1' : Measurable fun ω => max (Real.log (S ω).toReal) 0 := hmeas.max measurable_const
  have hm2' : Measurable fun ω => max (-Real.log (S ω).toReal) 0 :=
    hmeas.neg.max measurable_const
  rw [lintegral_add_left hm1'.ennreal_ofReal]
  have hgm : ∀ a b : ℝ, Measurable fun r : ℝ => ENNReal.ofReal (a * Real.exp (-(b * r))) :=
    fun a b => ENNReal.measurable_ofReal.comp
      (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id).neg))
  have hexpint : ∀ b : ℝ, 0 < b → IntegrableOn (fun r : ℝ => Real.exp (-(b * r))) (Ioi 0) :=
    fun b hb => (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => Real.exp (-x)) 0 hb).2
      (by simpa using integrableOn_exp_neg_Ioi 0)
  have hC0 : 0 ≤ C := by
    have h := hup 1 one_pos
    rw [Real.one_rpow, mul_one] at h
    exact le_trans measureReal_nonneg h
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · -- the upper tail
    rw [lintegral_eq_lintegral_meas_lt P (f := fun ω => max (Real.log (S ω).toReal) 0)
      (Filter.Eventually.of_forall fun ω => le_max_right _ _) hm1'.aemeasurable]
    have hbd : ∀ r ∈ Ioi (0 : ℝ), P {ω | r < max (Real.log (S ω).toReal) 0}
          ≤ ENNReal.ofReal (C * Real.exp (-(m * r))) := by
      intro r hr
      rw [mem_Ioi] at hr
      calc P {ω | r < max (Real.log (S ω).toReal) 0}
          ≤ P {ω | ENNReal.ofReal (Real.exp r) < S ω} := measure_mono (subset_lt_of_lt_log hr)
        _ = ENNReal.ofReal (P.real {ω | ENNReal.ofReal (Real.exp r) < S ω}) :=
            (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
        _ ≤ ENNReal.ofReal (C * Real.exp (-(m * r))) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have h := hup _ (Real.exp_pos r)
            have hpow : (Real.exp r) ^ (-m) = Real.exp (-(m * r)) := by
              rw [Real.rpow_def_of_pos (Real.exp_pos r), Real.log_exp]
              congr 1; ring
            rwa [hpow] at h
    have hfin : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (C * Real.exp (-(m * r))) < ∞ := by
      have hint := (hexpint m hm0).const_mul C
      have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun r => C * Real.exp (-(m * r)) :=
        Filter.Eventually.of_forall fun r => mul_nonneg hC0 (Real.exp_pos _).le
      exact (hasFiniteIntegral_iff_ofReal hnn).1 hint.hasFiniteIntegral
    exact lt_of_le_of_lt (setLIntegral_mono (hgm _ _) hbd) hfin
  · -- the lower tail
    rw [lintegral_eq_lintegral_meas_lt P (f := fun ω => max (-Real.log (S ω).toReal) 0)
      (Filter.Eventually.of_forall fun ω => le_max_right _ _) hm2'.aemeasurable]
    have hbd : ∀ r ∈ Ioi (0 : ℝ), P {ω | r < max (-Real.log (S ω).toReal) 0}
          ≤ ENNReal.ofReal (Real.exp (-D) * Real.exp (-((D * m) * r))) := by
      intro r hr
      rw [mem_Ioi] at hr
      calc P {ω | r < max (-Real.log (S ω).toReal) 0}
          ≤ P {ω | S ω < ENNReal.ofReal (Real.exp (-r))} :=
            measure_mono (subset_lt_of_lt_neg_log hr)
        _ = ENNReal.ofReal (P.real {ω | S ω < ENNReal.ofReal (Real.exp (-r))}) :=
            (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
        _ ≤ ENNReal.ofReal (Real.exp (-D) * Real.exp (-((D * m) * r))) := by
            refine ENNReal.ofReal_le_ofReal ?_
            refine (hlow _ (Real.exp_pos (-r))).trans ?_
            have hpow : (Real.exp (-r)) ^ (-m) = Real.exp (m * r) := by
              rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
              congr 1; ring
            rw [hpow, ← Real.exp_add]
            refine Real.exp_le_exp.2 ?_
            have hexp : 1 + m * r ≤ Real.exp (m * r) := by
              linarith [Real.add_one_le_exp (m * r)]
            nlinarith [mul_le_mul_of_nonneg_left hexp hD.le]
    have hfin : ∫⁻ r in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-D) * Real.exp (-((D * m) * r))) < ∞ := by
      have hint := (hexpint _ (mul_pos hD hm0)).const_mul (Real.exp (-D))
      have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun r =>
          Real.exp (-D) * Real.exp (-((D * m) * r)) :=
        Filter.Eventually.of_forall fun r => by positivity
      exact (hasFiniteIntegral_iff_ofReal hnn).1 hint.hasFiniteIntegral
    exact lt_of_le_of_lt (setLIntegral_mono (hgm _ _) hbd) hfin

end Laplace

variable {M : Type*} [MeasurableSpace M] [Nonempty M]

/-! ### The marked intensity, the law, and the weighted sums -/

/-- The marked intensity `μ_m ⊗ η`. -/
def pdIntensity (m : ℝ) (η : Measure M) : Measure (ℝ × M) := (stableIntensity m).prod η

omit [Nonempty M] in
instance (m : ℝ) (η : Measure M) [SFinite η] : SFinite (pdIntensity m η) := by
  unfold pdIntensity; infer_instance

/-- **The marked Poisson–Dirichlet point process**: the Poisson point process with intensity
`μ_m ⊗ η`, a probability measure on the measures on `ℝ × M`. Talagrand Vol. II, §13.1. -/
def pdProcess (m : ℝ) (η : Measure M) [SFinite η] : Measure (Measure (ℝ × M)) :=
  poissonPointProcess (pdIntensity m η)

instance (m : ℝ) (η : Measure M) [SFinite η] : IsProbabilityMeasure (pdProcess m η) := by
  unfold pdProcess; infer_instance

/-- **The weighted sum** `S_v = ∑_α u_α v(g_α)`, as an `ℝ≥0∞`-valued function of the counting
measure, for `ℝ≥0∞`-valued weights on the marks. -/
def pdSum (v : M → ℝ≥0∞) (N : Measure (ℝ × M)) : ℝ≥0∞ :=
  ∫⁻ p : ℝ × M, ENNReal.ofReal p.1 * v p.2 ∂N

omit [Nonempty M] in
lemma measurable_ofReal_mul {v : M → ℝ≥0∞} (hv : Measurable v) :
    Measurable fun p : ℝ × M => ENNReal.ofReal p.1 * v p.2 :=
  (ENNReal.measurable_ofReal.comp measurable_fst).mul (hv.comp measurable_snd)

omit [Nonempty M] in
lemma measurable_pdSum {v : M → ℝ≥0∞} (hv : Measurable v) : Measurable (pdSum v) :=
  Measure.measurable_lintegral (measurable_ofReal_mul hv)

omit [Nonempty M] in
/-- Integration against `μ_m ⊗ η`. -/
lemma lintegral_pdIntensity (m : ℝ) (η : Measure M) [SFinite η] {F : ℝ × M → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ p, F p ∂pdIntensity m η
      = ∫⁻ g, (∫⁻ u in Ioi 0, stableDensity m u * F (u, g)) ∂η := by
  rw [pdIntensity, lintegral_prod _ hF.aemeasurable,
    lintegral_stableIntensity m hF.lintegral_prod_right']
  have hpt : ∀ u, stableDensity m u * ∫⁻ g, F (u, g) ∂η
      = ∫⁻ g, stableDensity m u * F (u, g) ∂η := fun u =>
    (lintegral_const_mul _ (hF.comp (measurable_const.prodMk measurable_id))).symm
  simp_rw [hpt]
  exact lintegral_lintegral_swap (f := fun u g => stableDensity m u * F (u, g))
    (((measurable_stableDensity m).comp measurable_fst).mul hF).aemeasurable

/-! ### The Laplace transform -/

/-- **The Laplace transform of the weighted sum**, Talagrand Vol. II, Lemma 13.1.1 and
Corollary 13.1.2: `𝔼 e^{-s S_v} = exp (-s^m c_m ∫ v^m dη)`, in `ℝ≥0∞` (both sides vanish when
`∫ v^m dη = ∞` and `s > 0`). -/
theorem integral_negExp_pdSum {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {v : M → ℝ≥0∞} (hv : Measurable v) {s : ℝ} (hs : 0 ≤ s) :
    ∫ N, negExp (ENNReal.ofReal s * pdSum v N) ∂pdProcess m η
      = negExp (ENNReal.ofReal (s ^ m * stableConst m) * ∫⁻ g, v g ^ m ∂η) := by
  classical
  have hc : 0 < stableConst m := stableConst_pos hm0 hm1
  rcases eq_or_lt_of_le hs with rfl | hs
  · simp [Real.zero_rpow hm0.ne', integral_const]
  have hφm : Measurable fun p : ℝ × M => ENNReal.ofReal s * (ENNReal.ofReal p.1 * v p.2) :=
    measurable_const.mul (measurable_ofReal_mul hv)
  have h1 : ∀ N : Measure (ℝ × M), ENNReal.ofReal s * pdSum v N
      = ∫⁻ p, ENNReal.ofReal s * (ENNReal.ofReal p.1 * v p.2) ∂N := fun N => by
    rw [pdSum, ← lintegral_const_mul _ (measurable_ofReal_mul hv)]
  simp_rw [h1]
  rw [pdProcess, integral_negExp_lintegral_poissonPointProcess _ hφm]
  congr 1
  have hFm : Measurable fun p : ℝ × M =>
      1 - ENNReal.ofReal (negExp (ENNReal.ofReal s * (ENNReal.ofReal p.1 * v p.2))) :=
    measurable_const.sub (ENNReal.measurable_ofReal.comp (measurable_negExp.comp hφm))
  rw [lintegral_pdIntensity m η hFm]
  have hinner : ∀ g, ∫⁻ u in Ioi 0, stableDensity m u * (1 - ENNReal.ofReal (negExp
        (ENNReal.ofReal s * (ENNReal.ofReal u * v g))))
      = ENNReal.ofReal (s ^ m * stableConst m) * v g ^ m := by
    intro g
    rcases eq_or_ne (v g) ∞ with hg | hg
    · rw [hg, ENNReal.top_rpow_of_pos hm0,
        ENNReal.mul_top (ENNReal.ofReal_pos.2 (mul_pos (Real.rpow_pos_of_pos hs m) hc)).ne']
      refine (setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_).trans
        (lintegral_stableDensity_Ioi_zero hm0)
      rw [mem_Ioi] at hu
      rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hu).ne', ENNReal.mul_top
        (ENNReal.ofReal_pos.2 hs).ne', negExp_top, ENNReal.ofReal_zero, tsub_zero, mul_one]
    · obtain ⟨x, hx0, hvg⟩ : ∃ x : ℝ, 0 ≤ x ∧ v g = ENNReal.ofReal x :=
        ⟨(v g).toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hg).symm⟩
      rw [hvg]
      have hrhs : ENNReal.ofReal (s ^ m * stableConst m) * ENNReal.ofReal x ^ m
          = ENNReal.ofReal ((s * x) ^ m * stableConst m) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hx0 hm0.le,
          ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hs.le m) hc.le),
          Real.mul_rpow hs.le hx0]
        congr 1
        ring
      rw [hrhs, ← lintegral_stableDensity_one_sub_exp hm0 hm1 (mul_nonneg hs.le hx0)]
      refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
      rw [mem_Ioi] at hu
      congr 1
      rw [← ENNReal.ofReal_mul hu.le, ← ENNReal.ofReal_mul hs.le,
        negExp_ofReal (by positivity), ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_sub _ (Real.exp_nonneg _)]
      congr 3
      ring
  simp only [hinner]
  rw [lintegral_const_mul _ (hv.pow_const m)]

/-- The Laplace transform in real form, when `∫ v^m dη < ∞`. -/
theorem integral_negExp_pdSum_eq_exp {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {v : M → ℝ≥0∞} (hv : Measurable v)
    (hκ : ∫⁻ g, v g ^ m ∂η ≠ ∞) {s : ℝ} (hs : 0 ≤ s) :
    ∫ N, negExp (ENNReal.ofReal s * pdSum v N) ∂pdProcess m η
      = Real.exp (-(s ^ m * stableConst m * (∫⁻ g, v g ^ m ∂η).toReal)) := by
  have hc : 0 ≤ stableConst m := (stableConst_pos hm0 hm1).le
  rw [integral_negExp_pdSum hm0 hm1 η hv hs]
  conv_lhs => rw [← ENNReal.ofReal_toReal hκ]
  rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hs m) hc),
    negExp_ofReal (mul_nonneg (mul_nonneg (Real.rpow_nonneg hs m) hc) ENNReal.toReal_nonneg)]

omit [Nonempty M] in
@[simp] lemma lintegral_one_rpow (η : Measure M) [IsProbabilityMeasure η] (m : ℝ) :
    ∫⁻ _g : M, (1 : ℝ≥0∞) ^ m ∂η = 1 := by simp

/-- The Laplace transform of the unweighted sum `S_1`. -/
theorem integral_negExp_pdSum_one {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {s : ℝ} (hs : 0 ≤ s) :
    ∫ N, negExp (ENNReal.ofReal s * pdSum (fun _ => (1 : ℝ≥0∞)) N) ∂pdProcess m η
      = Real.exp (-(s ^ m * stableConst m)) := by
  rw [integral_negExp_pdSum_eq_exp hm0 hm1 η measurable_const (by simp) hs]
  simp

/-! ### Almost sure finiteness and the upper tail -/

/-- **`S_v < ∞` almost surely** when `∫ v^m dη < ∞`. -/
theorem measureReal_pdSum_eq_top {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {v : M → ℝ≥0∞} (hv : Measurable v)
    (hκ : ∫⁻ g, v g ^ m ∂η ≠ ∞) :
    (pdProcess m η).real {N | pdSum v N = ∞} = 0 :=
  measureReal_eq_top_of_laplace (measurable_pdSum hv) hm0
    (mul_nonneg (stableConst_pos hm0 hm1).le ENNReal.toReal_nonneg) fun s hs => by
      rw [integral_negExp_pdSum_eq_exp hm0 hm1 η hv hκ hs.le, mul_assoc]

theorem ae_pdSum_lt_top {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {v : M → ℝ≥0∞} (hv : Measurable v)
    (hκ : ∫⁻ g, v g ^ m ∂η ≠ ∞) :
    ∀ᵐ N ∂pdProcess m η, pdSum v N < ∞ :=
  ae_lt_top_of_laplace (measurable_pdSum hv) hm0
    (mul_nonneg (stableConst_pos hm0 hm1).le ENNReal.toReal_nonneg) fun s hs => by
      rw [integral_negExp_pdSum_eq_exp hm0 hm1 η hv hκ hs.le, mul_assoc]

/-- **The upper tail** `P (S_v > t) ≤ (1 - e^{-1})⁻¹ t^{-m} c_m ∫ v^m dη`. -/
theorem measureReal_lt_pdSum_le {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {v : M → ℝ≥0∞} (hv : Measurable v)
    (hκ : ∫⁻ g, v g ^ m ∂η ≠ ∞) {t : ℝ} (ht : 0 < t) :
    (pdProcess m η).real {N | ENNReal.ofReal t < pdSum v N}
      ≤ (1 - Real.exp (-1))⁻¹
        * (t ^ (-m) * (stableConst m * (∫⁻ g, v g ^ m ∂η).toReal)) :=
  measureReal_lt_le_of_laplace (measurable_pdSum hv) ht (by
    rw [integral_negExp_pdSum_eq_exp hm0 hm1 η hv hκ (by positivity), mul_assoc])

/-! ### The lower tail -/

omit [Nonempty M] in
/-- A counting measure is integer-valued: a nonzero count is at least `1`. -/
lemma one_le_superCounting_of_ne_zero {ω : SuperSample (ℝ × M)} {B : Set (ℝ × M)}
    (hB : MeasurableSet B) (h : superCounting ω B ≠ 0) : 1 ≤ superCounting ω B := by
  rw [superCounting, Measure.sum_apply _ hB] at h ⊢
  obtain ⟨n, hn⟩ : ∃ n, countingMeasure (ω n) B ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h (ENNReal.tsum_eq_zero.2 hcon)
  refine le_trans ?_ (ENNReal.le_tsum n)
  rw [countingMeasure_apply _ hB] at hn ⊢
  obtain ⟨i, hi, hi'⟩ : ∃ i ∈ Finset.range (ω n).2,
      B.indicator (1 : ℝ × M → ℝ≥0∞) ((ω n).1 i) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hn (Finset.sum_eq_zero hcon)
  have hval : B.indicator (1 : ℝ × M → ℝ≥0∞) ((ω n).1 i) = 1 := by
    by_cases hmem : (ω n).1 i ∈ B
    · simp [hmem]
    · simp [hmem] at hi'
  calc (1 : ℝ≥0∞) = B.indicator 1 ((ω n).1 i) := hval.symm
    _ ≤ ∑ j ∈ Finset.range (ω n).2, B.indicator 1 ((ω n).1 j) :=
        Finset.single_le_sum (f := fun j => B.indicator (1 : ℝ × M → ℝ≥0∞) ((ω n).1 j))
          (fun _ _ => zero_le) hi

omit [Nonempty M] in
/-- If some point has `u v(g) ≥ t`, then `S_v ≥ t`. -/
lemma ofReal_le_pdSum_of_superCounting_ne_zero {v : M → ℝ≥0∞} (hv : Measurable v) {δ t : ℝ}
    (hδ : 0 < δ) (ht : 0 ≤ t) {ω : SuperSample (ℝ × M)}
    (h : superCounting ω (Ioi (t / δ) ×ˢ {g | ENNReal.ofReal δ ≤ v g}) ≠ 0) :
    ENNReal.ofReal t ≤ pdSum v (superCounting ω) := by
  have hB : MeasurableSet (Ioi (t / δ) ×ˢ {g | ENNReal.ofReal δ ≤ v g}) :=
    measurableSet_Ioi.prod (measurableSet_le measurable_const hv)
  have h1 := one_le_superCounting_of_ne_zero hB h
  calc ENNReal.ofReal t = ENNReal.ofReal t * 1 := (mul_one _).symm
    _ ≤ ENNReal.ofReal t * superCounting ω (Ioi (t / δ) ×ˢ {g | ENNReal.ofReal δ ≤ v g}) :=
        mul_le_mul' le_rfl h1
    _ = ∫⁻ _p in Ioi (t / δ) ×ˢ {g | ENNReal.ofReal δ ≤ v g}, ENNReal.ofReal t
          ∂superCounting ω := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ p in Ioi (t / δ) ×ˢ {g | ENNReal.ofReal δ ≤ v g},
          ENNReal.ofReal p.1 * v p.2 ∂superCounting ω := by
        refine setLIntegral_mono (measurable_ofReal_mul hv) fun p hp => ?_
        rw [Set.mem_prod, mem_Ioi, Set.mem_ofPred_eq] at hp
        have hp1 : t / δ < p.1 := hp.1
        calc ENNReal.ofReal t = ENNReal.ofReal (t / δ) * ENNReal.ofReal δ := by
              rw [← ENNReal.ofReal_mul (div_nonneg ht hδ.le), div_mul_cancel₀ _ hδ.ne']
          _ ≤ ENNReal.ofReal p.1 * v p.2 :=
              mul_le_mul' (ENNReal.ofReal_le_ofReal hp1.le) hp.2
    _ ≤ pdSum v (superCounting ω) := lintegral_mono' Measure.restrict_le_self le_rfl

/-- **The lower tail** `P (S_v < t) ≤ exp (-(t/δ)^{-m} η{v ≥ δ} / m)`: if `S_v < t` then no point
lies in `(t/δ, ∞) × {v ≥ δ}`, an event of probability `exp (-Λ)`. -/
theorem measureReal_pdSum_lt_le {m : ℝ} (hm0 : 0 < m) (η : Measure M)
    [IsProbabilityMeasure η] {v : M → ℝ≥0∞} (hv : Measurable v) {δ : ℝ} (hδ : 0 < δ) {t : ℝ}
    (ht : 0 < t) :
    (pdProcess m η).real {N | pdSum v N < ENNReal.ofReal t}
      ≤ Real.exp (-((t / δ) ^ (-m) / m * (η {g | ENNReal.ofReal δ ≤ v g}).toReal)) := by
  have hB : MeasurableSet (Ioi (t / δ) ×ˢ {g | ENNReal.ofReal δ ≤ v g}) :=
    measurableSet_Ioi.prod (measurableSet_le measurable_const hv)
  have hlaw := hasLaw_superCounting_poissonPointProcess (pdIntensity m η)
  have hset : MeasurableSet {N : Measure (ℝ × M) | pdSum v N < ENNReal.ofReal t} :=
    measurableSet_lt (measurable_pdSum hv) measurable_const
  rw [pdProcess, ← hlaw.measureReal_eq (p := fun N => pdSum v N < ENNReal.ofReal t) hset]
  have hsub : {ω : SuperSample (ℝ × M) | pdSum v (superCounting ω) < ENNReal.ofReal t}
      ⊆ {ω | superCounting ω (Ioi (t / δ) ×ˢ {g | ENNReal.ofReal δ ≤ v g}) = 0} := by
    intro ω hω
    by_contra hne
    exact absurd (ofReal_le_pdSum_of_superCounting_ne_zero hv hδ ht.le hne) (not_le.2 hω)
  have hvoid := measureReal_superCounting_eq_zero (sfiniteSeq (pdIntensity m η)) hB
  rw [sum_sfiniteSeq] at hvoid
  have hmass : pdIntensity m η (Ioi (t / δ) ×ˢ {g | ENNReal.ofReal δ ≤ v g})
      = ENNReal.ofReal ((t / δ) ^ (-m) / m) * η {g | ENNReal.ofReal δ ≤ v g} := by
    rw [pdIntensity, Measure.prod_prod, stableIntensity_Ioi hm0 (div_pos ht hδ)]
  calc (superSampleLaw (sfiniteSeq (pdIntensity m η))).real
        {ω | pdSum v (superCounting ω) < ENNReal.ofReal t}
      ≤ (superSampleLaw (sfiniteSeq (pdIntensity m η))).real
        {ω | superCounting ω (Ioi (t / δ) ×ˢ {g | ENNReal.ofReal δ ≤ v g}) = 0} :=
        measureReal_mono hsub
    _ = negExp (pdIntensity m η (Ioi (t / δ) ×ˢ {g | ENNReal.ofReal δ ≤ v g})) := hvoid
    _ = Real.exp (-((t / δ) ^ (-m) / m * (η {g | ENNReal.ofReal δ ≤ v g}).toReal)) := by
        rw [hmass, ← ENNReal.ofReal_toReal (measure_ne_top η _),
          ← ENNReal.ofReal_mul (by positivity), negExp_ofReal (by positivity),
          ENNReal.toReal_ofReal ENNReal.toReal_nonneg]

/-! ### Almost sure positivity -/

/-- **`S_v > 0` almost surely**: the lower tail bound at `t → 0`. -/
theorem ae_pdSum_pos {m : ℝ} (hm0 : 0 < m) (η : Measure M) [IsProbabilityMeasure η]
    {v : M → ℝ≥0∞} (hv : Measurable v) {δ : ℝ} (hδ : 0 < δ)
    (hη : 0 < η {g | ENNReal.ofReal δ ≤ v g}) :
    ∀ᵐ N ∂pdProcess m η, 0 < pdSum v N := by
  have hS := measurable_pdSum (v := v) hv
  have hηr : 0 < (η {g | ENNReal.ofReal δ ≤ v g}).toReal :=
    ENNReal.toReal_pos hη.ne' (measure_ne_top _ _)
  have hbound : ∀ ε : ℝ, 0 < ε → (pdProcess m η).real {N | pdSum v N = 0} ≤ ε := by
    intro ε hε
    rcases le_or_gt 1 ε with h1 | h1
    · exact le_trans (measureReal_le_one) h1
    set X : ℝ := m * (-Real.log ε) / (η {g | ENNReal.ofReal δ ≤ v g}).toReal + 1 with hX
    have hX1 : 1 ≤ X := by
      have : 0 ≤ m * (-Real.log ε) / (η {g | ENNReal.ofReal δ ≤ v g}).toReal := by
        have : 0 < -Real.log ε := by linarith [Real.log_neg hε h1]
        positivity
      linarith
    have hXpos : 0 < X := by linarith
    set t : ℝ := δ * X ^ (-(1 / m)) with ht
    have htpos : 0 < t := mul_pos hδ (Real.rpow_pos_of_pos hXpos _)
    have hpow : (t / δ) ^ (-m) = X := by
      rw [ht, mul_div_cancel_left₀ _ hδ.ne', ← Real.rpow_mul hXpos.le]
      have : -(1 / m) * -m = 1 := by field_simp
      rw [this, Real.rpow_one]
    have h := measureReal_pdSum_lt_le hm0 η hv hδ htpos
    rw [hpow] at h
    have hsub : {N : Measure (ℝ × M) | pdSum v N = 0} ⊆ {N | pdSum v N < ENNReal.ofReal t} := by
      intro N hN
      rw [Set.mem_ofPred_eq] at hN ⊢
      rw [hN]
      exact ENNReal.ofReal_pos.2 htpos
    refine (measureReal_mono hsub).trans (h.trans ?_)
    have hexp : X / m * (η {g | ENNReal.ofReal δ ≤ v g}).toReal
        = -Real.log ε + (η {g | ENNReal.ofReal δ ≤ v g}).toReal / m := by
      rw [hX]; field_simp
    rw [hexp, neg_add, Real.exp_add, neg_neg, Real.exp_log hε]
    have : Real.exp (-((η {g | ENNReal.ofReal δ ≤ v g}).toReal / m)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by rw [neg_nonpos]; positivity)
    nlinarith [hε.le]
  have hle : (pdProcess m η).real {N | pdSum v N = 0} ≤ 0 :=
    le_of_forall_pos_le_add fun ε hε => by simpa using hbound ε hε
  have hzero : (pdProcess m η) {N | pdSum v N = 0} = 0 := by
    have h := le_antisymm hle measureReal_nonneg
    rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at h
    exact h.resolve_right (measure_ne_top _ _)
  rw [ae_iff]
  convert hzero using 2
  ext N
  simp [pos_iff_ne_zero]

omit [Nonempty M] in
/-- Weights that are a.e. positive are `≥ δ` on a set of positive measure, for some `δ > 0`. -/
lemma exists_pos_measure_ge_of_ae_pos (η : Measure M) [IsProbabilityMeasure η] {v : M → ℝ≥0∞}
    (hvpos : ∀ᵐ g ∂η, 0 < v g) : ∃ δ > (0 : ℝ), 0 < η {g | ENNReal.ofReal δ ≤ v g} := by
  by_contra hcon
  push Not at hcon
  have hnull : ∀ n : ℕ, η {g | ENNReal.ofReal (1 / ((n : ℝ) + 1)) ≤ v g} = 0 := fun n =>
    le_antisymm (hcon _ (by positivity)) zero_le
  have hunion : {g | 0 < v g} ⊆ ⋃ n : ℕ, {g | ENNReal.ofReal (1 / ((n : ℝ) + 1)) ≤ v g} := by
    intro g hg
    rw [Set.mem_ofPred_eq] at hg
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hg.ne'
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    rw [Set.mem_ofPred_eq]
    refine le_trans ?_ hn.le
    rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_add (by positivity)
      zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    exact ENNReal.inv_le_inv.2 le_self_add
  have h0 : η {g | 0 < v g} = 0 :=
    measure_mono_null hunion (measure_iUnion_null hnull)
  have h1 : η {g | 0 < v g}ᶜ = 0 := by
    rw [Set.compl_ofPred]
    exact ae_iff.1 hvpos
  have hle := measure_univ_le_add_compl (μ := η) {g | 0 < v g}
  rw [h0, h1, measure_univ] at hle
  simp at hle

/-! ### The moments of order `m' < m` -/

omit [Nonempty M] in
/-- `x^{m'} c_{m'} = ∫₀^∞ (1 - e^{-ux}) u^{-m'-1} du` for every `x : ℝ≥0∞`, including `x = ∞`. -/
lemma rpow_mul_ofReal_stableConst_eq_lintegral {m' : ℝ} (hm'0 : 0 < m') (hm'1 : m' < 1)
    (x : ℝ≥0∞) :
    x ^ m' * ENNReal.ofReal (stableConst m')
      = ∫⁻ u in Ioi 0,
          stableDensity m' u * (1 - ENNReal.ofReal (negExp (ENNReal.ofReal u * x))) := by
  have hc : 0 < stableConst m' := stableConst_pos hm'0 hm'1
  rcases eq_or_ne x ∞ with hx | hx
  · rw [hx, ENNReal.top_rpow_of_pos hm'0, ENNReal.top_mul (ENNReal.ofReal_pos.2 hc).ne']
    symm
    refine (setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_).trans
      (lintegral_stableDensity_Ioi_zero hm'0)
    rw [mem_Ioi] at hu
    rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hu).ne', negExp_top, ENNReal.ofReal_zero,
      tsub_zero, mul_one]
  · obtain ⟨y, hx0, hxr⟩ : ∃ y : ℝ, 0 ≤ y ∧ x = ENNReal.ofReal y :=
      ⟨x.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hx).symm⟩
    rw [hxr, ENNReal.ofReal_rpow_of_nonneg hx0 hm'0.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hx0 _),
      ← lintegral_stableDensity_one_sub_exp hm'0 hm'1 hx0]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    rw [mem_Ioi] at hu
    congr 1
    rw [← ENNReal.ofReal_mul hu.le, negExp_ofReal (by positivity), ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ (Real.exp_nonneg _)]
    congr 3
    ring

/-- **The moments of the weighted sum**, `0 < m' < m`:
`𝔼 S_v^{m'} = (c_m ∫ v^m dη)^{m'/m} · c_{m'/m} / (m c_{m'})`, in `ℝ≥0∞` (both sides are `∞`
when `∫ v^m dη = ∞`). This contains Talagrand's (13.8) and (13.9). -/
theorem lintegral_pdSum_rpow {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {v : M → ℝ≥0∞} (hv : Measurable v) {m' : ℝ} (hm'0 : 0 < m')
    (hm'm : m' < m) :
    ∫⁻ N, pdSum v N ^ m' ∂pdProcess m η
      = (ENNReal.ofReal (stableConst m) * ∫⁻ g, v g ^ m ∂η) ^ (m' / m)
          * ENNReal.ofReal (stableConst (m' / m) / (m * stableConst m')) := by
  have hm'1 : m' < 1 := hm'm.trans hm1
  have hc : 0 < stableConst m := stableConst_pos hm0 hm1
  have hc' : 0 < stableConst m' := stableConst_pos hm'0 hm'1
  have hq : 0 < m' / m := div_pos hm'0 hm0
  have hq1 : m' / m < 1 := (div_lt_one hm0).2 hm'm
  have hc'' : 0 < stableConst (m' / m) := stableConst_pos hq hq1
  have hS := measurable_pdSum (v := v) hv
  -- multiply both sides by `c_{m'}`
  suffices h : (∫⁻ N, pdSum v N ^ m' ∂pdProcess m η) * ENNReal.ofReal (stableConst m')
      = (ENNReal.ofReal (stableConst m) * ∫⁻ g, v g ^ m ∂η) ^ (m' / m)
          * ENNReal.ofReal (stableConst (m' / m) / (m * stableConst m'))
          * ENNReal.ofReal (stableConst m') by
    exact (ENNReal.mul_left_inj (ENNReal.ofReal_pos.2 hc').ne' ENNReal.ofReal_ne_top).1 h
  rw [← lintegral_mul_const _ (hS.pow_const m')]
  simp_rw [rpow_mul_ofReal_stableConst_eq_lintegral hm'0 hm'1]
  -- Tonelli
  have hjoint : Measurable fun q : Measure (ℝ × M) × ℝ => stableDensity m' q.2
      * (1 - ENNReal.ofReal (negExp (ENNReal.ofReal q.2 * pdSum v q.1))) :=
    ((measurable_stableDensity m').comp measurable_snd).mul (measurable_const.sub
      (ENNReal.measurable_ofReal.comp (measurable_negExp.comp
        ((ENNReal.measurable_ofReal.comp measurable_snd).mul (hS.comp measurable_fst)))))
  rw [lintegral_lintegral_swap (f := fun N u => stableDensity m' u
    * (1 - ENNReal.ofReal (negExp (ENNReal.ofReal u * pdSum v N)))) hjoint.aemeasurable]
  -- the inner integral is the Laplace transform
  have hinner : ∀ u ∈ Ioi (0 : ℝ),
      ∫⁻ N, stableDensity m' u * (1 - ENNReal.ofReal (negExp (ENNReal.ofReal u * pdSum v N)))
          ∂pdProcess m η
        = stableDensity m' u * (1 - ENNReal.ofReal (negExp
            (ENNReal.ofReal (u ^ m * stableConst m) * ∫⁻ g, v g ^ m ∂η))) := by
    intro u hu
    rw [mem_Ioi] at hu
    have hg : Measurable fun N : Measure (ℝ × M) =>
        1 - ENNReal.ofReal (negExp (ENNReal.ofReal u * pdSum v N)) :=
      measurable_const.sub (ENNReal.measurable_ofReal.comp
        (measurable_negExp.comp (measurable_const.mul hS)))
    rw [lintegral_const_mul _ hg]
    congr 1
    have hint : Integrable (fun N => negExp (ENNReal.ofReal u * pdSum v N)) (pdProcess m η) :=
      Integrable.mono' (integrable_const 1)
        (measurable_negExp.comp (measurable_const.mul hS)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun N => by
          rw [Real.norm_eq_abs, abs_of_nonneg (negExp_nonneg _)]; exact negExp_le_one _)
    have hg' : Measurable fun N : Measure (ℝ × M) =>
        ENNReal.ofReal (negExp (ENNReal.ofReal u * pdSum v N)) :=
      ENNReal.measurable_ofReal.comp (measurable_negExp.comp (measurable_const.mul hS))
    have hfin : ∫⁻ N, ENNReal.ofReal (negExp (ENNReal.ofReal u * pdSum v N)) ∂pdProcess m η
        ≠ ∞ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun N => negExp_nonneg _)]
      exact ENNReal.ofReal_ne_top
    rw [lintegral_sub hg' hfin (Filter.Eventually.of_forall fun N => ofReal_negExp_le_one _),
      lintegral_const, measure_univ, mul_one,
      ← ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun N => negExp_nonneg _),
      integral_negExp_pdSum hm0 hm1 η hv hu.le]
  rw [setLIntegral_congr_fun measurableSet_Ioi hinner]
  -- the outer integral: the moment integral
  rcases eq_or_ne (∫⁻ g, v g ^ m ∂η) ∞ with hκ | hκ
  · rw [hκ, ENNReal.mul_top (ENNReal.ofReal_pos.2 hc).ne', ENNReal.top_rpow_of_pos hq,
      ENNReal.top_mul (ENNReal.ofReal_pos.2 (by positivity)).ne',
      ENNReal.top_mul (ENNReal.ofReal_pos.2 hc').ne']
    refine (setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_).trans
      (lintegral_stableDensity_Ioi_zero hm'0)
    rw [mem_Ioi] at hu
    rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 (mul_pos (Real.rpow_pos_of_pos hu m) hc)).ne',
      negExp_top, ENNReal.ofReal_zero, tsub_zero, mul_one]
  · obtain ⟨κr, hκ0, hκr⟩ : ∃ κr : ℝ, 0 ≤ κr ∧ ∫⁻ g, v g ^ m ∂η = ENNReal.ofReal κr :=
      ⟨(∫⁻ g, v g ^ m ∂η).toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hκ).symm⟩
    rw [hκr]
    have hpt : ∀ u ∈ Ioi (0 : ℝ), stableDensity m' u * (1 - ENNReal.ofReal (negExp
          (ENNReal.ofReal (u ^ m * stableConst m) * ENNReal.ofReal κr)))
        = stableDensity m' u * ENNReal.ofReal (1 - Real.exp
            (-((stableConst m * κr) * u ^ m))) := by
      intro u hu
      rw [mem_Ioi] at hu
      congr 1
      rw [← ENNReal.ofReal_mul (by positivity), negExp_ofReal (by positivity),
        ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.exp_nonneg _)]
      congr 3
      ring
    rw [setLIntegral_congr_fun measurableSet_Ioi hpt,
      lintegral_stableDensity_one_sub_exp_rpow hm0 hm'0 hm'm (by positivity),
      ← ENNReal.ofReal_mul hc.le, ENNReal.ofReal_rpow_of_nonneg (by positivity) hq.le,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp

/-- **(13.8)**: `𝔼 S_v^{m'} < ∞` for `0 < m' < m` when `∫ v^m dη < ∞`. -/
theorem lintegral_pdSum_rpow_lt_top {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {v : M → ℝ≥0∞} (hv : Measurable v)
    (hκ : ∫⁻ g, v g ^ m ∂η ≠ ∞) {m' : ℝ} (hm'0 : 0 < m') (hm'm : m' < m) :
    ∫⁻ N, pdSum v N ^ m' ∂pdProcess m η < ∞ := by
  rw [lintegral_pdSum_rpow hm0 hm1 η hv hm'0 hm'm]
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (div_pos hm'0 hm0).le
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hκ)) ENNReal.ofReal_lt_top

/-- **(13.9)**: `𝔼 S_v^{m'} = (∫ v^m dη)^{m'/m} 𝔼 S_1^{m'}` for `0 < m' < m`. -/
theorem lintegral_pdSum_rpow_eq_mul {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {v : M → ℝ≥0∞} (hv : Measurable v) {m' : ℝ} (hm'0 : 0 < m')
    (hm'm : m' < m) :
    ∫⁻ N, pdSum v N ^ m' ∂pdProcess m η
      = (∫⁻ g, v g ^ m ∂η) ^ (m' / m)
          * ∫⁻ N, pdSum (fun _ => (1 : ℝ≥0∞)) N ^ m' ∂pdProcess m η := by
  rw [lintegral_pdSum_rpow hm0 hm1 η hv hm'0 hm'm,
    lintegral_pdSum_rpow hm0 hm1 η measurable_const hm'0 hm'm, lintegral_one_rpow, mul_one,
    ENNReal.mul_rpow_of_nonneg _ _ (div_pos hm'0 hm0).le]
  ring

/-! ### Integrability of `log S` -/

omit [Nonempty M] in
lemma measurable_log_toReal_pdSum {v : M → ℝ≥0∞} (hv : Measurable v) :
    Measurable fun N : Measure (ℝ × M) => Real.log (pdSum v N).toReal :=
  measurable_log_toReal (measurable_pdSum hv)

/-- **`𝔼 |log S_v| < ∞`**: the two tails are integrable. Talagrand Vol. II, the comment after
Proposition 13.1.3. -/
theorem integrable_log_pdSum {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {v : M → ℝ≥0∞} (hv : Measurable v)
    (hκ : ∫⁻ g, v g ^ m ∂η ≠ ∞) {δ : ℝ} (hδ : 0 < δ)
    (hη : 0 < η {g | ENNReal.ofReal δ ≤ v g}) :
    Integrable (fun N => Real.log (pdSum v N).toReal) (pdProcess m η) := by
  have hηr : 0 < (η {g | ENNReal.ofReal δ ≤ v g}).toReal :=
    ENNReal.toReal_pos hη.ne' (measure_ne_top _ _)
  refine integrable_log_toReal_of_tails (measurable_pdSum hv) hm0
    (C := (1 - Real.exp (-1))⁻¹ * (stableConst m * (∫⁻ g, v g ^ m ∂η).toReal))
    (D := δ ^ m * (η {g | ENNReal.ofReal δ ≤ v g}).toReal / m) (by positivity)
    (fun t ht => ?_) (fun t ht => ?_)
  · refine (measureReal_lt_pdSum_le hm0 hm1 η hv hκ ht).trans (le_of_eq ?_)
    ring
  · refine (measureReal_pdSum_lt_le hm0 η hv hδ ht).trans (le_of_eq ?_)
    congr 2
    rw [Real.div_rpow ht.le hδ.le, Real.rpow_neg hδ.le, div_inv_eq_mul]
    ring

/-! ### Talagrand's identity (13.10) -/

omit [Nonempty M] in
/-- `∫ v^m dη > 0` when `v ≥ δ > 0` on a set of positive measure. -/
lemma lintegral_rpow_pos_of_measure_pos {m : ℝ} (hm0 : 0 < m) (η : Measure M)
    {v : M → ℝ≥0∞} (hv : Measurable v) {δ : ℝ} (hδ : 0 < δ)
    (hη : 0 < η {g | ENNReal.ofReal δ ≤ v g}) :
    0 < ∫⁻ g, v g ^ m ∂η := by
  rw [lintegral_pos_iff_support (hv.pow_const m)]
  refine lt_of_lt_of_le hη (measure_mono fun g hg => ?_)
  rw [Set.mem_ofPred_eq] at hg
  rw [Function.mem_support]
  intro h0
  rcases ENNReal.rpow_eq_zero_iff.1 h0 with ⟨h, _⟩ | ⟨_, h⟩
  · rw [h] at hg
    exact absurd hg (not_le.2 (ENNReal.ofReal_pos.2 hδ))
  · exact absurd h (not_lt.2 hm0.le)

/-- The substitution `t = s^m` in `∫_0^∞ s⁻¹ (e^{-c s^m} - e^{-cκ s^m}) ds`. -/
lemma integral_inv_mul_exp_rpow_sub {m c κ : ℝ} (hm0 : 0 < m) (hc : 0 < c) (hκ : 0 < κ) :
    ∫ s in Ioi (0 : ℝ), s⁻¹ * (Real.exp (-(s ^ m * c)) - Real.exp (-(s ^ m * c * κ)))
      = (1 / m) * Real.log κ := by
  have hfr := Real.frullani_exp hc (mul_pos hc hκ)
  rw [mul_div_cancel_left₀ _ hc.ne'] at hfr
  have hsub := integral_comp_rpow_Ioi
    (fun t : ℝ => t⁻¹ * (Real.exp (-(c * t)) - Real.exp (-(c * κ * t)))) hm0.ne'
  rw [hfr] at hsub
  have hpt : ∀ s ∈ Ioi (0 : ℝ), (|m| * s ^ (m - 1)) •
      ((fun t : ℝ => t⁻¹ * (Real.exp (-(c * t)) - Real.exp (-(c * κ * t)))) (s ^ m))
      = m * (s⁻¹ * (Real.exp (-(s ^ m * c)) - Real.exp (-(s ^ m * c * κ)))) := by
    intro s hs
    rw [mem_Ioi] at hs
    have hsm : 0 < s ^ m := Real.rpow_pos_of_pos hs m
    simp only [smul_eq_mul, abs_of_pos hm0, Real.rpow_sub_one hs.ne']
    rw [mul_comm c (s ^ m), mul_comm (c * κ) (s ^ m), ← mul_assoc (s ^ m) c κ]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul] at hsub
  calc ∫ s in Ioi (0 : ℝ), s⁻¹ * (Real.exp (-(s ^ m * c)) - Real.exp (-(s ^ m * c * κ)))
      = (1 / m) * (m * ∫ s in Ioi (0 : ℝ),
          s⁻¹ * (Real.exp (-(s ^ m * c)) - Real.exp (-(s ^ m * c * κ)))) := by
        rw [← mul_assoc, one_div, inv_mul_cancel₀ hm0.ne', one_mul]
    _ = (1 / m) * Real.log κ := by rw [hsub]

/-- **Talagrand's identity (13.10)** for the law: for weights with `∫ v^m dη < ∞` and
`v ≥ δ > 0` on a set of positive measure,

`𝔼 log ∑_α u_α v(g_α) = 𝔼 log ∑_α u_α + (1/m) log ∫ v^m dη`.

Talagrand, *Mean Field Models for Spin Glasses*, Vol. II, Proposition 13.1.3, (13.10). -/
theorem integral_log_pdSum_eq_of_measure_pos {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1)
    (η : Measure M) [IsProbabilityMeasure η] {v : M → ℝ≥0∞} (hv : Measurable v)
    (hκ : ∫⁻ g, v g ^ m ∂η ≠ ∞) {δ : ℝ} (hδ : 0 < δ)
    (hη : 0 < η {g | ENNReal.ofReal δ ≤ v g}) :
    ∫ N, Real.log (pdSum v N).toReal ∂pdProcess m η
      = (∫ N, Real.log (pdSum (fun _ => (1 : ℝ≥0∞)) N).toReal ∂pdProcess m η)
        + (1 / m) * Real.log (∫⁻ g, v g ^ m ∂η).toReal := by
  have hc : 0 < stableConst m := stableConst_pos hm0 hm1
  have hκpos : 0 < (∫⁻ g, v g ^ m ∂η).toReal :=
    ENNReal.toReal_pos (lintegral_rpow_pos_of_measure_pos hm0 η hv hδ hη).ne' hκ
  have h1m : ∫⁻ _g : M, (1 : ℝ≥0∞) ^ m ∂η ≠ ∞ := by simp
  have hη1 : 0 < η {g : M | ENNReal.ofReal 1 ≤ (fun _ => (1 : ℝ≥0∞)) g} := by simp
  obtain ⟨hv_eq, hv_int⟩ := integral_log_toReal_eq_integral_Ioi (pdProcess m η)
    (measurable_pdSum hv) (ae_pdSum_pos hm0 η hv hδ hη) (ae_pdSum_lt_top hm0 hm1 η hv hκ)
    (integrable_log_pdSum hm0 hm1 η hv hκ hδ hη)
  obtain ⟨h1_eq, h1_int⟩ := integral_log_toReal_eq_integral_Ioi (pdProcess m η)
    (measurable_pdSum measurable_const)
    (ae_pdSum_pos hm0 η measurable_const one_pos hη1)
    (ae_pdSum_lt_top hm0 hm1 η measurable_const h1m)
    (integrable_log_pdSum hm0 hm1 η measurable_const h1m one_pos hη1)
  rw [hv_eq, h1_eq, ← sub_eq_iff_eq_add', ← integral_sub hv_int h1_int]
  have hpt : ∀ s ∈ Ioi (0 : ℝ),
      s⁻¹ * (Real.exp (-s) - laplaceTransform (pdProcess m η) (pdSum v) s)
        - s⁻¹ * (Real.exp (-s) - laplaceTransform (pdProcess m η) (pdSum fun _ => (1 : ℝ≥0∞)) s)
      = s⁻¹ * (Real.exp (-(s ^ m * stableConst m))
          - Real.exp (-(s ^ m * stableConst m * (∫⁻ g, v g ^ m ∂η).toReal))) := by
    intro s hs
    rw [mem_Ioi] at hs
    have e1 : laplaceTransform (pdProcess m η) (pdSum v) s
        = Real.exp (-(s ^ m * stableConst m * (∫⁻ g, v g ^ m ∂η).toReal)) :=
      integral_negExp_pdSum_eq_exp hm0 hm1 η hv hκ hs.le
    have e2 : laplaceTransform (pdProcess m η) (pdSum fun _ => (1 : ℝ≥0∞)) s
        = Real.exp (-(s ^ m * stableConst m)) := integral_negExp_pdSum_one hm0 hm1 η hs.le
    rw [e1, e2]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  exact integral_inv_mul_exp_rpow_sub hm0 hc hκpos

/-- **Talagrand's identity (13.10)**, with a.e. positive weights. -/
theorem integral_log_pdSum_eq {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {v : M → ℝ≥0∞} (hv : Measurable v)
    (hκ : ∫⁻ g, v g ^ m ∂η ≠ ∞) (hvpos : ∀ᵐ g ∂η, 0 < v g) :
    ∫ N, Real.log (pdSum v N).toReal ∂pdProcess m η
      = (∫ N, Real.log (pdSum (fun _ => (1 : ℝ≥0∞)) N).toReal ∂pdProcess m η)
        + (1 / m) * Real.log (∫⁻ g, v g ^ m ∂η).toReal := by
  obtain ⟨δ, hδ, hη⟩ := exists_pos_measure_ge_of_ae_pos η hvpos
  exact integral_log_pdSum_eq_of_measure_pos hm0 hm1 η hv hκ hδ hη

/-- **Theorem 13.1.5**: for the Poisson–Dirichlet weights `v_α = u_α / ∑_γ u_γ`,
`𝔼 log ∑_α v_α V_α = (1/m) log 𝔼 V^m`. -/
theorem integral_log_pdSum_div_eq {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (η : Measure M)
    [IsProbabilityMeasure η] {v : M → ℝ≥0∞} (hv : Measurable v)
    (hκ : ∫⁻ g, v g ^ m ∂η ≠ ∞) (hvpos : ∀ᵐ g ∂η, 0 < v g) :
    ∫ N, Real.log ((pdSum v N).toReal / (pdSum (fun _ => (1 : ℝ≥0∞)) N).toReal) ∂pdProcess m η
      = (1 / m) * Real.log (∫⁻ g, v g ^ m ∂η).toReal := by
  obtain ⟨δ, hδ, hη⟩ := exists_pos_measure_ge_of_ae_pos η hvpos
  have h1m : ∫⁻ _g : M, (1 : ℝ≥0∞) ^ m ∂η ≠ ∞ := by simp
  have hη1 : 0 < η {g : M | ENNReal.ofReal 1 ≤ (fun _ => (1 : ℝ≥0∞)) g} := by simp
  have hintv := integrable_log_pdSum hm0 hm1 η hv hκ hδ hη
  have hint1 := integrable_log_pdSum hm0 hm1 η measurable_const h1m one_pos hη1
  have hae : ∀ᵐ N ∂pdProcess m η,
      Real.log ((pdSum v N).toReal / (pdSum (fun _ => (1 : ℝ≥0∞)) N).toReal)
        = Real.log (pdSum v N).toReal - Real.log (pdSum (fun _ => (1 : ℝ≥0∞)) N).toReal := by
    filter_upwards [ae_pdSum_pos hm0 η hv hδ hη, ae_pdSum_lt_top hm0 hm1 η hv hκ,
      ae_pdSum_pos hm0 η measurable_const one_pos hη1,
      ae_pdSum_lt_top hm0 hm1 η measurable_const h1m] with N h1 h2 h3 h4
    rw [Real.log_div (ENNReal.toReal_pos h1.ne' h2.ne).ne' (ENNReal.toReal_pos h3.ne' h4.ne).ne']
  rw [integral_congr_ae hae, integral_sub hintv hint1,
    integral_log_pdSum_eq_of_measure_pos hm0 hm1 η hv hκ hδ hη]
  ring

/-! ### Transport to any random measure with the Poisson–Dirichlet law -/

section HasLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → Measure (ℝ × M)}

/-- The Laplace transform, for any random measure with the Poisson–Dirichlet law. -/
theorem HasLaw.integral_negExp_pdSum {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) {η : Measure M}
    [IsProbabilityMeasure η] (hN : HasLaw N (pdProcess m η) P) {v : M → ℝ≥0∞}
    (hv : Measurable v) {s : ℝ} (hs : 0 ≤ s) :
    ∫ ω, negExp (ENNReal.ofReal s * pdSum v (N ω)) ∂P
      = negExp (ENNReal.ofReal (s ^ m * stableConst m) * ∫⁻ g, v g ^ m ∂η) := by
  have hmeas : Measurable fun N : Measure (ℝ × M) => negExp (ENNReal.ofReal s * pdSum v N) :=
    measurable_negExp.comp (measurable_const.mul (measurable_pdSum hv))
  have h := _root_.ProbabilityTheory.integral_negExp_pdSum hm0 hm1 η hv hs
  rw [← hN.integral_comp hmeas.aestronglyMeasurable] at h
  exact h

theorem HasLaw.integral_negExp_pdSum_eq_exp {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) {η : Measure M}
    [IsProbabilityMeasure η] (hN : HasLaw N (pdProcess m η) P) {v : M → ℝ≥0∞}
    (hv : Measurable v) (hκ : ∫⁻ g, v g ^ m ∂η ≠ ∞) {s : ℝ} (hs : 0 ≤ s) :
    ∫ ω, negExp (ENNReal.ofReal s * pdSum v (N ω)) ∂P
      = Real.exp (-(s ^ m * stableConst m * (∫⁻ g, v g ^ m ∂η).toReal)) := by
  have hmeas : Measurable fun N : Measure (ℝ × M) => negExp (ENNReal.ofReal s * pdSum v N) :=
    measurable_negExp.comp (measurable_const.mul (measurable_pdSum hv))
  have h := _root_.ProbabilityTheory.integral_negExp_pdSum_eq_exp hm0 hm1 η hv hκ hs
  rw [← hN.integral_comp hmeas.aestronglyMeasurable] at h
  exact h

/-- The moments, for any random measure with the Poisson–Dirichlet law. -/
theorem HasLaw.lintegral_pdSum_rpow {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) {η : Measure M}
    [IsProbabilityMeasure η] (hN : HasLaw N (pdProcess m η) P) {v : M → ℝ≥0∞}
    (hv : Measurable v) {m' : ℝ} (hm'0 : 0 < m') (hm'm : m' < m) :
    ∫⁻ ω, pdSum v (N ω) ^ m' ∂P
      = (ENNReal.ofReal (stableConst m) * ∫⁻ g, v g ^ m ∂η) ^ (m' / m)
          * ENNReal.ofReal (stableConst (m' / m) / (m * stableConst m')) := by
  rw [← _root_.ProbabilityTheory.lintegral_pdSum_rpow hm0 hm1 η hv hm'0 hm'm]
  exact hN.lintegral_comp ((measurable_pdSum hv).pow_const m').aemeasurable

theorem HasLaw.ae_pdSum_lt_top {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) {η : Measure M}
    [IsProbabilityMeasure η] (hN : HasLaw N (pdProcess m η) P) {v : M → ℝ≥0∞}
    (hv : Measurable v) (hκ : ∫⁻ g, v g ^ m ∂η ≠ ∞) :
    ∀ᵐ ω ∂P, pdSum v (N ω) < ∞ :=
  (hN.ae_iff (p := fun N => pdSum v N < ∞)
    (measurableSet_setOfPred.1 (measurableSet_lt (measurable_pdSum hv) measurable_const))).2
    (_root_.ProbabilityTheory.ae_pdSum_lt_top hm0 hm1 η hv hκ)

theorem HasLaw.ae_pdSum_pos {m : ℝ} (hm0 : 0 < m) {η : Measure M} [IsProbabilityMeasure η]
    (hN : HasLaw N (pdProcess m η) P) {v : M → ℝ≥0∞} (hv : Measurable v)
    (hvpos : ∀ᵐ g ∂η, 0 < v g) :
    ∀ᵐ ω ∂P, 0 < pdSum v (N ω) := by
  obtain ⟨δ, hδ, hη⟩ := exists_pos_measure_ge_of_ae_pos η hvpos
  exact (hN.ae_iff (p := fun N => 0 < pdSum v N)
    (measurableSet_setOfPred.1 (measurableSet_lt measurable_const (measurable_pdSum hv)))).2
    (_root_.ProbabilityTheory.ae_pdSum_pos hm0 η hv hδ hη)

theorem HasLaw.integrable_log_pdSum {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) {η : Measure M}
    [IsProbabilityMeasure η] (hN : HasLaw N (pdProcess m η) P) {v : M → ℝ≥0∞}
    (hv : Measurable v) (hκ : ∫⁻ g, v g ^ m ∂η ≠ ∞) (hvpos : ∀ᵐ g ∂η, 0 < v g) :
    Integrable (fun ω => Real.log (pdSum v (N ω)).toReal) P := by
  obtain ⟨δ, hδ, hη⟩ := exists_pos_measure_ge_of_ae_pos η hvpos
  have h := _root_.ProbabilityTheory.integrable_log_pdSum hm0 hm1 η hv hκ hδ hη
  rw [← hN.map_eq] at h
  exact (integrable_map_measure (measurable_log_toReal_pdSum hv).aestronglyMeasurable
    hN.aemeasurable).1 h

/-- **Talagrand's identity (13.10)**, for any random measure with the Poisson–Dirichlet law. -/
theorem HasLaw.integral_log_pdSum_eq {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) {η : Measure M}
    [IsProbabilityMeasure η] (hN : HasLaw N (pdProcess m η) P) {v : M → ℝ≥0∞}
    (hv : Measurable v) (hκ : ∫⁻ g, v g ^ m ∂η ≠ ∞) (hvpos : ∀ᵐ g ∂η, 0 < v g) :
    ∫ ω, Real.log (pdSum v (N ω)).toReal ∂P
      = (∫ ω, Real.log (pdSum (fun _ => (1 : ℝ≥0∞)) (N ω)).toReal ∂P)
        + (1 / m) * Real.log (∫⁻ g, v g ^ m ∂η).toReal := by
  have h := _root_.ProbabilityTheory.integral_log_pdSum_eq hm0 hm1 η hv hκ hvpos
  rw [← hN.integral_comp (measurable_log_toReal_pdSum hv).aestronglyMeasurable,
    ← hN.integral_comp (measurable_log_toReal_pdSum measurable_const).aestronglyMeasurable] at h
  exact h

/-- **Theorem 13.1.5**, for any random measure with the Poisson–Dirichlet law. -/
theorem HasLaw.integral_log_pdSum_div_eq {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) {η : Measure M}
    [IsProbabilityMeasure η] (hN : HasLaw N (pdProcess m η) P) {v : M → ℝ≥0∞}
    (hv : Measurable v) (hκ : ∫⁻ g, v g ^ m ∂η ≠ ∞) (hvpos : ∀ᵐ g ∂η, 0 < v g) :
    ∫ ω, Real.log ((pdSum v (N ω)).toReal / (pdSum (fun _ => (1 : ℝ≥0∞)) (N ω)).toReal) ∂P
      = (1 / m) * Real.log (∫⁻ g, v g ^ m ∂η).toReal := by
  have hmeas : Measurable fun N : Measure (ℝ × M) =>
      Real.log ((pdSum v N).toReal / (pdSum (fun _ => (1 : ℝ≥0∞)) N).toReal) :=
    Real.measurable_log.comp ((ENNReal.measurable_toReal.comp (measurable_pdSum hv)).div
      (ENNReal.measurable_toReal.comp (measurable_pdSum measurable_const)))
  have h := _root_.ProbabilityTheory.integral_log_pdSum_div_eq hm0 hm1 η hv hκ hvpos
  rw [← hN.integral_comp hmeas.aestronglyMeasurable] at h
  exact h

end HasLaw

end

end ProbabilityTheory
