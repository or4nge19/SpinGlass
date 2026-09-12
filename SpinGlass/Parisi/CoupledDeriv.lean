/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.CoupledSite
import Common.Mathlib.Probability.PointProcess.CascadeDeriv

/-!
# The `λ`-dependence of `Y₀` (Talagrand Vol. II, §14.6, after Proposition 14.6.3)

The one-site function `Y_{κ+1}(λ) = log (ch A ch B ch λ + sh A sh B sh λ)` of (14.168) has
derivative `pairSiteY'`, bounded by `1` in absolute value (`abs_pairSiteY'_le_one`: with
`T = th λ`, `T₁ = th A`, `T₂ = th B`, `|T + T₁T₂| ≤ 1 + T T₁ T₂`, Talagrand's inequality in the
proof of Lemma 14.6.5). By the derivative of the Parisi recursion in a parameter
(`hasDerivAt_parisiRec`), `Y₁(λ, y₀)` is differentiable in `λ` with derivative the tilted average
of `∂_λ Y_{κ+1}` — Talagrand's (14.185), `Y'_p = 𝔼_p(W_p Y'_{p+1})`, iterated
(`hasDerivAt_parisiRec_pairSiteF`) — and so is `Y₀(λ) = 𝔼 Y₁(λ, y₀)`
(`hasDerivAt_pairSiteY₀`), with `|Y₀'(λ)| ≤ 1` (`abs_pairSiteY₀'_le_one`).
-/

open MeasureTheory ProbabilityTheory Finset Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

/-! ### The derivative of `Y_{κ+1}` in `λ` -/

/-- `∂_λ Y_{κ+1} = (ch A ch B sh λ + sh A sh B ch λ) / (ch A ch B ch λ + sh A sh B sh λ)`. -/
def pairSiteY' (lam A B : ℝ) : ℝ :=
  (Real.cosh A * Real.cosh B * Real.sinh lam + Real.sinh A * Real.sinh B * Real.cosh lam)
    / (Real.cosh A * Real.cosh B * Real.cosh lam + Real.sinh A * Real.sinh B * Real.sinh lam)

lemma hasDerivAt_pairSiteY (A B lam : ℝ) :
    HasDerivAt (fun l => pairSiteY l A B) (pairSiteY' lam A B) lam := by
  unfold pairSiteY pairSiteY'
  have h1 : HasDerivAt (fun l => Real.cosh A * Real.cosh B * Real.cosh l
      + Real.sinh A * Real.sinh B * Real.sinh l)
      (Real.cosh A * Real.cosh B * Real.sinh lam + Real.sinh A * Real.sinh B * Real.cosh lam)
      lam :=
    ((Real.hasDerivAt_cosh lam).const_mul _).add ((Real.hasDerivAt_sinh lam).const_mul _)
  exact h1.log (cosh_mul_cosh_mul_cosh_add_sinh_mul_sinh_mul_sinh_pos A B lam).ne'

/-- **Talagrand's inequality** (proof of Lemma 14.6.5):
`|ch A ch B sh λ + sh A sh B ch λ| ≤ ch A ch B ch λ + sh A sh B sh λ`, i.e. `|∂_λ Y_{κ+1}| ≤ 1`. -/
lemma abs_pairSiteY'_le_one (lam A B : ℝ) : |pairSiteY' lam A B| ≤ 1 := by
  unfold pairSiteY'
  have hc := cosh_mul_cosh_mul_cosh_add_sinh_mul_sinh_mul_sinh_pos A B lam
  rw [abs_div, abs_of_pos hc, div_le_one hc, abs_le]
  have h1 : Real.cosh A * Real.cosh B * Real.cosh lam + Real.sinh A * Real.sinh B * Real.sinh lam
      + (Real.cosh A * Real.cosh B * Real.sinh lam + Real.sinh A * Real.sinh B * Real.cosh lam)
      = Real.exp lam * Real.cosh (A + B) := by
    rw [Real.cosh_add, ← Real.cosh_add_sinh]
    ring
  have h2 : Real.cosh A * Real.cosh B * Real.cosh lam + Real.sinh A * Real.sinh B * Real.sinh lam
      - (Real.cosh A * Real.cosh B * Real.sinh lam + Real.sinh A * Real.sinh B * Real.cosh lam)
      = Real.exp (-lam) * Real.cosh (A - B) := by
    rw [Real.cosh_sub, ← Real.cosh_sub_sinh]
    ring
  have h3 : 0 ≤ Real.exp lam * Real.cosh (A + B) :=
    mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le
  have h4 : 0 ≤ Real.exp (-lam) * Real.cosh (A - B) :=
    mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le
  constructor <;> linarith

lemma continuous_pairSiteY' : Continuous fun q : ℝ × ℝ × ℝ => pairSiteY' q.1 q.2.1 q.2.2 := by
  unfold pairSiteY'
  refine Continuous.div ?_ ?_ fun q =>
    (cosh_mul_cosh_mul_cosh_add_sinh_mul_sinh_mul_sinh_pos _ _ _).ne'
  · fun_prop
  · fun_prop

/-! ### The one-site branch functions of the marks -/

variable {κ : ℕ} {J : Type*} [Fintype J]

/-- `∂_λ Y_{κ+1}(λ, y₀, y)` for the one-site function of the marks. -/
def pairSiteF' (lam : ℝ) (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ)
    (y₀ : J → ℝ) (y : Fin κ → J → ℝ) : ℝ :=
  pairSiteY' lam (h 0 + pairSiteMark K₀ K y₀ y 0) (h 1 + pairSiteMark K₀ K y₀ y 1)

lemma hasDerivAt_pairSiteF (lam : ℝ) (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin κ → Fin 2 → J → ℝ) (y₀ : J → ℝ) (y : Fin κ → J → ℝ) :
    HasDerivAt (fun l => pairSiteF l h K₀ K y₀ y) (pairSiteF' lam h K₀ K y₀ y) lam :=
  hasDerivAt_pairSiteY _ _ lam

lemma abs_pairSiteF'_le_one (lam : ℝ) (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin κ → Fin 2 → J → ℝ) (y₀ : J → ℝ) (y : Fin κ → J → ℝ) :
    |pairSiteF' lam h K₀ K y₀ y| ≤ 1 :=
  abs_pairSiteY'_le_one _ _ _

lemma continuous_pairSiteMark (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ) (l : Fin 2) :
    Continuous fun q : (J → ℝ) × (Fin κ → J → ℝ) => pairSiteMark K₀ K q.1 q.2 l := by
  unfold pairSiteMark
  fun_prop

/-- Joint continuity of `Y_{κ+1}` in `(λ, y₀, y)`. -/
lemma continuous_pairSiteF_prod (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin κ → Fin 2 → J → ℝ) :
    Continuous fun q : ℝ × ((J → ℝ) × (Fin κ → J → ℝ)) => pairSiteF q.1 h K₀ K q.2.1 q.2.2 := by
  unfold pairSiteF pairSiteY
  refine Continuous.log ?_ fun q =>
    (cosh_mul_cosh_mul_cosh_add_sinh_mul_sinh_mul_sinh_pos _ _ _).ne'
  have h0 := (continuous_pairSiteMark K₀ K 0).comp (continuous_snd :
    Continuous fun q : ℝ × ((J → ℝ) × (Fin κ → J → ℝ)) => q.2)
  have h1 := (continuous_pairSiteMark K₀ K 1).comp (continuous_snd :
    Continuous fun q : ℝ × ((J → ℝ) × (Fin κ → J → ℝ)) => q.2)
  have hA : Continuous fun q : ℝ × ((J → ℝ) × (Fin κ → J → ℝ)) =>
      h 0 + pairSiteMark K₀ K q.2.1 q.2.2 0 := continuous_const.add h0
  have hB : Continuous fun q : ℝ × ((J → ℝ) × (Fin κ → J → ℝ)) =>
      h 1 + pairSiteMark K₀ K q.2.1 q.2.2 1 := continuous_const.add h1
  exact (((Real.continuous_cosh.comp hA).mul (Real.continuous_cosh.comp hB)).mul
    (Real.continuous_cosh.comp continuous_fst)).add
    (((Real.continuous_sinh.comp hA).mul (Real.continuous_sinh.comp hB)).mul
      (Real.continuous_sinh.comp continuous_fst))

/-- Joint continuity of `∂_λ Y_{κ+1}` in `(λ, y₀, y)`. -/
lemma continuous_pairSiteF'_prod (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin κ → Fin 2 → J → ℝ) :
    Continuous fun q : ℝ × ((J → ℝ) × (Fin κ → J → ℝ)) =>
      pairSiteF' q.1 h K₀ K q.2.1 q.2.2 := by
  have h0 := (continuous_pairSiteMark K₀ K 0).comp (continuous_snd :
    Continuous fun q : ℝ × ((J → ℝ) × (Fin κ → J → ℝ)) => q.2)
  have h1 := (continuous_pairSiteMark K₀ K 1).comp (continuous_snd :
    Continuous fun q : ℝ × ((J → ℝ) × (Fin κ → J → ℝ)) => q.2)
  have hf : Continuous fun q : ℝ × ((J → ℝ) × (Fin κ → J → ℝ)) =>
      (q.1, (h 0 + pairSiteMark K₀ K q.2.1 q.2.2 0, h 1 + pairSiteMark K₀ K q.2.1 q.2.2 1)) :=
    continuous_fst.prodMk ((continuous_const.add h0).prodMk (continuous_const.add h1))
  have hc := continuous_pairSiteY'.comp hf
  exact hc

/-- **Talagrand's (14.4) for the one-site branch function**: `∫ e^{Y_{κ+1}} d(marks) < ∞`, by the
Gaussian integrals of the four exponentials of (14.142). -/
theorem lintegral_ofReal_exp_pairSiteF_ne_top (vs : Fin κ → ℝ≥0) (lam : ℝ) (h : Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ) (y₀ : J → ℝ) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))
      ∂Measure.pi (siteGaussianMarks J κ vs) ≠ ∞ := by
  classical
  -- the four exponentials of (14.142)
  set a : (Fin 2 → Bool) → ℝ := fun ε =>
    isingSpin (ε 0) * (h 0 + ∑ j, K₀ 0 j * y₀ j) + isingSpin (ε 1) * (h 1 + ∑ j, K₀ 1 j * y₀ j)
      + isingSpin (ε 0) * isingSpin (ε 1) * lam with ha
  set B : (Fin 2 → Bool) → Fin κ → J → ℝ := fun ε p j =>
    isingSpin (ε 0) * K p 0 j + isingSpin (ε 1) * K p 1 j with hB
  have hexp : ∀ (ε : Fin 2 → Bool) (y : Fin κ → J → ℝ),
      isingSpin (ε 0) * (h 0 + pairSiteMark K₀ K y₀ y 0)
        + isingSpin (ε 1) * (h 1 + pairSiteMark K₀ K y₀ y 1)
        + isingSpin (ε 0) * isingSpin (ε 1) * lam
      = a ε + ∑ p, ∑ j, B ε p j * y p j := by
    intro ε y
    rw [ha, hB]
    simp only [pairSiteMark]
    have h1 : ∑ p, ∑ j, (isingSpin (ε 0) * K p 0 j + isingSpin (ε 1) * K p 1 j) * y p j
        = isingSpin (ε 0) * (∑ p, ∑ j, K p 0 j * y p j)
          + isingSpin (ε 1) * (∑ p, ∑ j, K p 1 j * y p j) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h1]
    ring
  have hpt : ∀ y : Fin κ → J → ℝ, ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))
      = ∑ ε : Fin 2 → Bool, ENNReal.ofReal (1 / 4)
          * ENNReal.ofReal (Real.exp (a ε + ∑ p, ∑ j, B ε p j * y p j)) := by
    intro y
    have hs := sum_exp_pairSpin (h 0 + pairSiteMark K₀ K y₀ y 0) (h 1 + pairSiteMark K₀ K y₀ y 1)
      lam
    simp_rw [hexp] at hs
    rw [pairSiteF, exp_pairSiteY, show Real.cosh (h 0 + pairSiteMark K₀ K y₀ y 0)
        * Real.cosh (h 1 + pairSiteMark K₀ K y₀ y 1) * Real.cosh lam
        + Real.sinh (h 0 + pairSiteMark K₀ K y₀ y 0) * Real.sinh (h 1 + pairSiteMark K₀ K y₀ y 1)
          * Real.sinh lam
        = ∑ ε : Fin 2 → Bool, (1 / 4) * Real.exp (a ε + ∑ p, ∑ j, B ε p j * y p j) by
      rw [← Finset.mul_sum, hs]; ring,
      ENNReal.ofReal_sum_of_nonneg fun ε _ => by positivity]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [ENNReal.ofReal_mul (by norm_num)]
  have hm : ∀ ε : Fin 2 → Bool, Measurable fun y : Fin κ → J → ℝ =>
      ENNReal.ofReal (1 / 4) * ENNReal.ofReal (Real.exp (a ε + ∑ p, ∑ j, B ε p j * y p j)) :=
    fun ε => (measurable_ofReal_exp_add_sum_mul J κ (a ε) (B ε)).const_mul _
  rw [lintegral_congr hpt, lintegral_finsetSum _ fun ε _ => hm ε]
  refine ENNReal.sum_ne_top.2 fun ε _ => ?_
  rw [lintegral_const_mul _ (measurable_ofReal_exp_add_sum_mul J κ (a ε) (B ε)),
    lintegral_ofReal_exp_add_siteGaussianMarks J κ vs (a ε) (B ε)]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)

/-- Measurability of the one-site recursion in the root marks. -/
lemma measurable_parisiRec_pairSiteF (ns : Fin κ → ℝ) (vs : Fin κ → ℝ≥0) (lam : ℝ)
    (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ) :
    Measurable fun y₀ : J → ℝ =>
      parisiRec κ ns (siteGaussianMarks J κ vs) (pairSiteF lam h K₀ K y₀) := by
  have hc := (continuous_pairSiteF_prod h K₀ K).comp (continuous_const.prodMk continuous_id :
    Continuous fun q : (J → ℝ) × (Fin κ → J → ℝ) => (lam, q))
  have hG : Measurable (Function.uncurry fun (y₀ : J → ℝ) (y : Fin κ → J → ℝ) =>
      ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))) := by
    have h := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hc.measurable)
    exact h
  have hR : Measurable fun y₀ : J → ℝ => cascadeRec κ ns (siteGaussianMarks J κ vs)
      (fun y => ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))) :=
    measurable_cascadeRec_prod κ ns (siteGaussianMarks J κ vs) hG
  exact hR.ennreal_toReal.log

/-! ### The derivative of `Y₁` and of `Y₀` in `λ` -/

/-- **Talagrand's (14.185), iterated**: `Y₁(λ, y₀)` is differentiable in `λ`, with derivative the
tilted average `𝔼(W₁ ⋯ W_κ ∂_λ Y_{κ+1})`. -/
theorem hasDerivAt_parisiRec_pairSiteF (ns : Fin κ → ℝ) (hpos : ∀ i, 0 < ns i)
    (hle : ∀ i, ns i ≤ 1) (vs : Fin κ → ℝ≥0) (lam : ℝ) (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin κ → Fin 2 → J → ℝ) (y₀ : J → ℝ) :
    HasDerivAt (fun l => parisiRec κ ns (siteGaussianMarks J κ vs) (pairSiteF l h K₀ K y₀))
      (∫ y, pairSiteF' lam h K₀ K y₀ y ∂cascadeTiltMeasure κ ns (siteGaussianMarks J κ vs)
        (fun y => ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y)))) lam := by
  have hF : Measurable (Function.uncurry fun (l : ℝ) (y : Fin κ → J → ℝ) =>
      pairSiteF l h K₀ K y₀ y) := by
    have hc := (continuous_pairSiteF_prod h K₀ K).comp
      (continuous_fst.prodMk (continuous_const.prodMk continuous_snd) :
        Continuous fun q : ℝ × (Fin κ → J → ℝ) => (q.1, (y₀, q.2)))
    exact hc.measurable
  have hF' : Measurable (Function.uncurry fun (l : ℝ) (y : Fin κ → J → ℝ) =>
      pairSiteF' l h K₀ K y₀ y) := by
    have hc := (continuous_pairSiteF'_prod h K₀ K).comp
      (continuous_fst.prodMk (continuous_const.prodMk continuous_snd) :
        Continuous fun q : ℝ × (Fin κ → J → ℝ) => (q.1, (y₀, q.2)))
    exact hc.measurable
  exact hasDerivAt_parisiRec κ ns (siteGaussianMarks J κ vs)
    (fun l => hF.comp (measurable_const.prodMk measurable_id))
    (fun l => hF'.comp (measurable_const.prodMk measurable_id))
    (fun l y => hasDerivAt_pairSiteF l h K₀ K y₀ y) (C := 1)
    (fun l y => abs_pairSiteF'_le_one l h K₀ K y₀ y) hpos hle
    (lintegral_ofReal_exp_pairSiteF_ne_top vs lam h K₀ K y₀)

/-- The tilted measure of the one-site branch function is a probability measure. -/
lemma isProbabilityMeasure_cascadeTiltMeasure_pairSiteF (ns : Fin κ → ℝ) (hpos : ∀ i, 0 < ns i)
    (hle : ∀ i, ns i ≤ 1) (vs : Fin κ → ℝ≥0) (lam : ℝ) (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin κ → Fin 2 → J → ℝ) (y₀ : J → ℝ) :
    IsProbabilityMeasure (cascadeTiltMeasure κ ns (siteGaussianMarks J κ vs)
      (fun y => ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y)))) :=
  isProbabilityMeasure_cascadeTiltMeasure κ ns _
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_pairSiteF' lam h K₀ K y₀)))
    (fun _ => ENNReal.ofReal_pos.2 (Real.exp_pos _)) hpos hle
    (lintegral_ofReal_exp_pairSiteF_ne_top vs lam h K₀ K y₀)

/-- `|∂_λ Y₁(λ, y₀)| ≤ 1`. -/
lemma abs_integral_pairSiteF'_le_one (ns : Fin κ → ℝ) (hpos : ∀ i, 0 < ns i) (hle : ∀ i, ns i ≤ 1)
    (vs : Fin κ → ℝ≥0) (lam : ℝ) (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin κ → Fin 2 → J → ℝ) (y₀ : J → ℝ) :
    |∫ y, pairSiteF' lam h K₀ K y₀ y ∂cascadeTiltMeasure κ ns (siteGaussianMarks J κ vs)
      (fun y => ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y)))| ≤ 1 := by
  have := isProbabilityMeasure_cascadeTiltMeasure_pairSiteF ns hpos hle vs lam h K₀ K y₀
  have hb := norm_integral_le_of_norm_le_const
    (μ := cascadeTiltMeasure κ ns (siteGaussianMarks J κ vs)
      (fun y => ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))))
    (f := fun y => pairSiteF' lam h K₀ K y₀ y) (C := 1)
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact abs_pairSiteF'_le_one _ _ _ _ _ _)
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at hb

universe u

variable {J' : Type u} [Fintype J']

/-- `Y₁(λ, ·)` is integrable in the root marks (the one-site case of
`integrable_parisiRec_pairCoshF_rootMarksLaw`). -/
theorem integrable_parisiRec_pairSiteF (ns : Fin κ → ℝ) (hpos : ∀ i, 0 < ns i)
    (hle : ∀ i, ns i ≤ 1) (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (lam : ℝ)
    (h : Fin 2 → ℝ) (K₀ : Fin 2 → J' → ℝ) (K : Fin κ → Fin 2 → J' → ℝ) :
    Integrable (fun y₀ : J' → ℝ =>
        parisiRec κ ns (siteGaussianMarks J' κ vs) (pairSiteF lam h K₀ K y₀))
      (Measure.pi fun _ : J' => gaussianReal 0 v₀) := by
  have hI := integrable_parisiRec_pairCoshF_rootMarksLaw 1 ns hpos hle lam (fun s => h s.2)
    K₀ K v₀ vs
  have hpt : ∀ z₀ : Fin 1 × J' → ℝ, parisiRec κ ns (siteGaussianMarks (Fin 1 × J') κ vs)
      (pairCoshF 1 κ lam (fun s => h s.2) K₀ K z₀)
      = parisiRec κ ns (siteGaussianMarks J' κ vs) (pairSiteF lam h K₀ K (fun j => z₀ (0, j))) := by
    intro z₀
    rw [parisiRec_pairCoshF 1 ns hpos hle vs lam (fun s => h s.2) K₀ K z₀,
      Fin.sum_univ_one]
  have hg : Function.Injective fun j : J' => ((0 : Fin 1), j) :=
    fun j j' hjj' => (Prod.mk.inj hjj').2
  have hmp : MeasurePreserving (fun z₀ : Fin 1 × J' → ℝ => fun j => z₀ (0, j))
      (rootMarksLaw 1 v₀) (Measure.pi fun _ : J' => gaussianReal 0 v₀) :=
    measurePreserving_comp_pi_of_injective (gaussianReal 0 v₀) hg
  rw [← hmp.integrable_comp (measurable_parisiRec_pairSiteF ns vs lam h K₀ K).aestronglyMeasurable]
  exact hI.congr (Filter.Eventually.of_forall fun z₀ => hpt z₀)

/-- **The derivative of Talagrand's `Y₀(λ)`**: `Y₀'(λ) = 𝔼_{y₀} 𝔼(W₁ ⋯ W_κ ∂_λ Y_{κ+1})`. -/
def pairSiteY₀' (ns : Fin κ → ℝ) (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (lam : ℝ) (h : Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ) : ℝ :=
  ∫ y₀, (∫ y, pairSiteF' lam h K₀ K y₀ y ∂cascadeTiltMeasure κ ns (siteGaussianMarks J κ vs)
      (fun y => ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))))
    ∂Measure.pi fun _ : J => gaussianReal 0 v₀

/-- **`Y₀` is differentiable in `λ`**, with derivative `Y₀'(λ) = 𝔼_{y₀} 𝔼(W₁ ⋯ W_κ ∂_λ Y_{κ+1})`. -/
theorem hasDerivAt_pairSiteY₀ (ns : Fin κ → ℝ) (hpos : ∀ i, 0 < ns i)
    (hle : ∀ i, ns i ≤ 1) (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (lam : ℝ) (h : Fin 2 → ℝ)
    (K₀ : Fin 2 → J' → ℝ) (K : Fin κ → Fin 2 → J' → ℝ) :
    HasDerivAt (fun l => pairSiteY₀ ns v₀ vs l h K₀ K) (pairSiteY₀' ns v₀ vs lam h K₀ K) lam := by
  -- measurability of the derivative in the root marks, through the density
  have hF'meas : AEStronglyMeasurable (fun y₀ : J' → ℝ =>
      ∫ y, pairSiteF' lam h K₀ K y₀ y ∂cascadeTiltMeasure κ ns (siteGaussianMarks J' κ vs)
        (fun y => ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))))
      (Measure.pi fun _ : J' => gaussianReal 0 v₀) := by
    have hG : Measurable (Function.uncurry fun (y₀ : J' → ℝ) (y : Fin κ → J' → ℝ) =>
        ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))) := by
      have hc := (continuous_pairSiteF_prod h K₀ K).comp (continuous_const.prodMk continuous_id :
        Continuous fun q : (J' → ℝ) × (Fin κ → J' → ℝ) => (lam, q))
      have h := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hc.measurable)
      exact h
    have hF'm : Measurable fun q : (J' → ℝ) × (Fin κ → J' → ℝ) =>
        pairSiteF' lam h K₀ K q.1 q.2 := by
      have hc := (continuous_pairSiteF'_prod h K₀ K).comp (continuous_const.prodMk continuous_id :
        Continuous fun q : (J' → ℝ) × (Fin κ → J' → ℝ) => (lam, q))
      exact hc.measurable
    have hjoint : Measurable fun q : (J' → ℝ) × (Fin κ → J' → ℝ) =>
        (cascadeTiltDensity κ ns (siteGaussianMarks J' κ vs)
          (fun y => ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K q.1 y))) q.2).toReal
          * pairSiteF' lam h K₀ K q.1 q.2 :=
      (measurable_cascadeTiltDensity_prod κ ns (siteGaussianMarks J' κ vs)
        hG).ennreal_toReal.mul hF'm
    have hsm' := hjoint.stronglyMeasurable.integral_prod_right'
      (ν := Measure.pi (siteGaussianMarks J' κ vs))
    refine hsm'.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun y₀ => ?_)
    have hGy : Measurable fun y : Fin κ → J' → ℝ =>
        ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y)) := by
      have := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_pairSiteF' lam h K₀ K y₀))
      exact this
    show (∫ y, (cascadeTiltDensity κ ns (siteGaussianMarks J' κ vs)
        (fun y => ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))) y).toReal
          * pairSiteF' lam h K₀ K y₀ y ∂Measure.pi (siteGaussianMarks J' κ vs))
      = ∫ y, pairSiteF' lam h K₀ K y₀ y ∂cascadeTiltMeasure κ ns (siteGaussianMarks J' κ vs)
          (fun y => ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y)))
    rw [integral_cascadeTiltMeasure κ ns (siteGaussianMarks J' κ vs)
      (G := fun y => ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))) hGy
      (fun _ => ENNReal.ofReal_pos.2 (Real.exp_pos _)) hpos hle
      (lintegral_ofReal_exp_pairSiteF_ne_top vs lam h K₀ K y₀)]
    simp only [smul_eq_mul]
  unfold pairSiteY₀ pairSiteY₀'
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := Measure.pi fun _ : J' => gaussianReal 0 v₀) (s := Set.univ)
    (F := fun l y₀ => parisiRec κ ns (siteGaussianMarks J' κ vs) (pairSiteF l h K₀ K y₀))
    (F' := fun l y₀ => ∫ y, pairSiteF' l h K₀ K y₀ y
      ∂cascadeTiltMeasure κ ns (siteGaussianMarks J' κ vs)
        (fun y => ENNReal.ofReal (Real.exp (pairSiteF l h K₀ K y₀ y))))
    (bound := fun _ => 1) Filter.univ_mem
    (Filter.Eventually.of_forall fun l =>
      (measurable_parisiRec_pairSiteF ns vs l h K₀ K).aestronglyMeasurable)
    (integrable_parisiRec_pairSiteF ns hpos hle v₀ vs lam h K₀ K) hF'meas
    (Filter.Eventually.of_forall fun y₀ l _ => by
      rw [Real.norm_eq_abs]; exact abs_integral_pairSiteF'_le_one ns hpos hle vs l h K₀ K y₀)
    (integrable_const _)
    (Filter.Eventually.of_forall fun y₀ l _ =>
      hasDerivAt_parisiRec_pairSiteF ns hpos hle vs l h K₀ K y₀)).2

/-- `|Y₀'(λ)| ≤ 1`. -/
theorem abs_pairSiteY₀'_le_one (ns : Fin κ → ℝ) (hpos : ∀ i, 0 < ns i) (hle : ∀ i, ns i ≤ 1)
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (lam : ℝ) (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin κ → Fin 2 → J → ℝ) :
    |pairSiteY₀' ns v₀ vs lam h K₀ K| ≤ 1 := by
  unfold pairSiteY₀'
  have hb := norm_integral_le_of_norm_le_const (μ := Measure.pi fun _ : J => gaussianReal 0 v₀)
    (C := 1) (Filter.Eventually.of_forall fun y₀ => by
      rw [Real.norm_eq_abs]; exact abs_integral_pairSiteF'_le_one ns hpos hle vs lam h K₀ K y₀)
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at hb

end

end SpinGlass
