/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.CoupledDeriv
import SpinGlass.Parisi.CascadeLogIntegrable
import Common.Mathlib.Probability.PointProcess.CascadeLinear
import Common.Mathlib.Probability.PointProcess.CascadeExponent
import Common.Mathlib.Analysis.Convex.Limit
import Common.Mathlib.Analysis.Convex.TangentLine

/-!
# Lemma 14.6.5: `0 ≤ Y₀''(λ) ≤ 1`

Talagrand's `Y₀(λ)` (Vol. II, (14.145); `pairSiteY₀`) is, by Theorem 14.2.1, the expectation over
the cascade of `log ∑_α v_α exp Y_{κ+1}(λ, ζ_α)`, and
`exp Y_{κ+1}(λ) = (e^λ ch(ζ¹ + ζ²) + e^{−λ} ch(ζ¹ − ζ²))/2`, so by linearity of the cascade sum
`S(λ) = ∑_α v_α exp Y_{κ+1}(λ, ζ_α) = (e^λ P + e^{−λ} M)/2` with `P, M ≥ 0` independent of `λ`
(`cascadeSum_pairSiteG`). Hence `S'' = S`, `|S'| ≤ S` and `(log S)'' = 1 − ((log S)')² ∈ [0, 1]`
(`logExpMix`). Differentiating twice under the expectation with these constant bounds gives
`Y₀'' = 1 − 𝔼 (S'/S)²` (`hasDerivAt_pairSiteY₀'`, `pairSiteY₀''_nonneg`, `pairSiteY₀''_le_one`) for
strictly increasing exponents, so `Y₀` is convex and `Y₀ − λ²/2` concave; both pass to nondecreasing
exponents `0 < n₁ ≤ ⋯ ≤ n_κ ≤ 1` by continuity in the exponents (`convexOn_pairSiteY₀`,
`concaveOn_pairSiteY₀_sub_sq`), whence the two-sided Taylor bound
`Y₀(0) + λ Y₀'(0) ≤ Y₀(λ) ≤ Y₀(0) + λ Y₀'(0) + λ²/2` (`taylor_le_pairSiteY₀`,
`pairSiteY₀_le_taylor`) used in the main estimate of §14.8. Talagrand's statement of Lemma 14.6.5
reads `0 ≤ Y₀'(λ) ≤ 1`; its proof is about `Y₀''`.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

noncomputable section

universe u

variable {κ : ℕ} {J : Type u} [Fintype J]

/-! ### The four exponentials, jointly in the root marks -/

/-- The affine coefficient in the root marks of the four exponentials of (14.142). -/
def pairSiteA (lam : ℝ) (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (ε : Fin 2 → Bool) (y₀ : J → ℝ) :
    ℝ :=
  isingSpin (ε 0) * (h 0 + ∑ j, K₀ 0 j * y₀ j) + isingSpin (ε 1) * (h 1 + ∑ j, K₀ 1 j * y₀ j)
    + isingSpin (ε 0) * isingSpin (ε 1) * lam

/-- The linear coefficients in the marks along the branch of the four exponentials. -/
def pairSiteB (K : Fin κ → Fin 2 → J → ℝ) (ε : Fin 2 → Bool) (p : Fin κ) (j : J) : ℝ :=
  isingSpin (ε 0) * K p 0 j + isingSpin (ε 1) * K p 1 j

lemma pairSiteA_eq (lam : ℝ) (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (ε : Fin 2 → Bool)
    (y₀ : J → ℝ) :
    pairSiteA lam h K₀ ε y₀
      = (isingSpin (ε 0) * h 0 + isingSpin (ε 1) * h 1 + isingSpin (ε 0) * isingSpin (ε 1) * lam)
        + ∑ j, (isingSpin (ε 0) * K₀ 0 j + isingSpin (ε 1) * K₀ 1 j) * y₀ j := by
  unfold pairSiteA
  have h1 : ∑ j, (isingSpin (ε 0) * K₀ 0 j + isingSpin (ε 1) * K₀ 1 j) * y₀ j
      = isingSpin (ε 0) * (∑ j, K₀ 0 j * y₀ j) + isingSpin (ε 1) * (∑ j, K₀ 1 j * y₀ j) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h1]
  ring

/-- `exp Y_{κ+1}` as the four exponentials of (14.142), each the exponential of an affine
function of the marks. -/
lemma ofReal_exp_pairSiteF_eq_sum (lam : ℝ) (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin κ → Fin 2 → J → ℝ) (y₀ : J → ℝ) (y : Fin κ → J → ℝ) :
    ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))
      = ∑ ε : Fin 2 → Bool, ENNReal.ofReal (1 / 4) * ENNReal.ofReal (Real.exp
          (pairSiteA lam h K₀ ε y₀ + ∑ p, ∑ j, pairSiteB K ε p j * y p j)) := by
  have hexp : ∀ ε : Fin 2 → Bool,
      isingSpin (ε 0) * (h 0 + pairSiteMark K₀ K y₀ y 0)
        + isingSpin (ε 1) * (h 1 + pairSiteMark K₀ K y₀ y 1)
        + isingSpin (ε 0) * isingSpin (ε 1) * lam
      = pairSiteA lam h K₀ ε y₀ + ∑ p, ∑ j, pairSiteB K ε p j * y p j := by
    intro ε
    unfold pairSiteA pairSiteB pairSiteMark
    have h1 : ∑ p, ∑ j, (isingSpin (ε 0) * K p 0 j + isingSpin (ε 1) * K p 1 j) * y p j
        = isingSpin (ε 0) * (∑ p, ∑ j, K p 0 j * y p j)
          + isingSpin (ε 1) * (∑ p, ∑ j, K p 1 j * y p j) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h1]
    ring
  have hs := sum_exp_pairSpin (h 0 + pairSiteMark K₀ K y₀ y 0) (h 1 + pairSiteMark K₀ K y₀ y 1)
    lam
  simp_rw [hexp] at hs
  rw [pairSiteF, exp_pairSiteY, show Real.cosh (h 0 + pairSiteMark K₀ K y₀ y 0)
      * Real.cosh (h 1 + pairSiteMark K₀ K y₀ y 1) * Real.cosh lam
      + Real.sinh (h 0 + pairSiteMark K₀ K y₀ y 0) * Real.sinh (h 1 + pairSiteMark K₀ K y₀ y 1)
        * Real.sinh lam
      = ∑ ε : Fin 2 → Bool, (1 / 4) * Real.exp (pairSiteA lam h K₀ ε y₀
          + ∑ p, ∑ j, pairSiteB K ε p j * y p j) by
    rw [← Finset.mul_sum, hs]; ring,
    ENNReal.ofReal_sum_of_nonneg fun ε _ => by positivity]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [ENNReal.ofReal_mul (by norm_num)]

/-- **Talagrand's (14.4) for the one-site branch function, jointly in the root marks**:
`𝔼_{y₀} 𝔼_y exp Y_{κ+1}(y₀, y) < ∞`. -/
theorem lintegral_lintegral_ofReal_exp_pairSiteF_ne_top (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (lam : ℝ)
    (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ) :
    ∫⁻ y₀, ∫⁻ y, ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))
      ∂Measure.pi (siteGaussianMarks J κ vs) ∂Measure.pi (fun _ : J => gaussianReal 0 v₀)
      ≠ ∞ := by
  classical
  have hAm : ∀ ε : Fin 2 → Bool, Measurable fun y₀ : J → ℝ =>
      ENNReal.ofReal (Real.exp (pairSiteA lam h K₀ ε y₀)) := by
    intro ε
    have : Measurable fun y₀ : J → ℝ => pairSiteA lam h K₀ ε y₀ := by
      simp_rw [pairSiteA_eq]
      exact measurable_const.add (Finset.measurable_sum _ fun j _ =>
        measurable_const.mul (measurable_pi_apply j))
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp this)
  -- the inner Gaussian integral over the marks along the branch
  have hin : ∀ y₀, ∫⁻ y, ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))
      ∂Measure.pi (siteGaussianMarks J κ vs)
      = ∑ ε : Fin 2 → Bool, ENNReal.ofReal (1 / 4)
          * (ENNReal.ofReal (Real.exp (pairSiteA lam h K₀ ε y₀))
            * ENNReal.ofReal (Real.exp (∑ p, ∑ j, (vs p : ℝ) * pairSiteB K ε p j ^ 2 / 2))) := by
    intro y₀
    rw [lintegral_congr (ofReal_exp_pairSiteF_eq_sum lam h K₀ K y₀),
      lintegral_finsetSum _ fun ε _ => (measurable_ofReal_exp_add_sum_mul J κ
        (pairSiteA lam h K₀ ε y₀) (pairSiteB K ε)).const_mul _]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [lintegral_const_mul _ (measurable_ofReal_exp_add_sum_mul J κ (pairSiteA lam h K₀ ε y₀)
      (pairSiteB K ε)), lintegral_ofReal_exp_add_siteGaussianMarks J κ vs
      (pairSiteA lam h K₀ ε y₀) (pairSiteB K ε)]
  simp_rw [hin]
  rw [lintegral_finsetSum _ fun ε _ => ((hAm ε).mul_const _).const_mul _]
  refine ENNReal.sum_ne_top.2 fun ε _ => ?_
  rw [lintegral_const_mul _ ((hAm ε).mul_const _), lintegral_mul_const _ (hAm ε)]
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top)
  -- the outer Gaussian integral of the exponential of an affine function of the root marks
  have h1 : ∀ y₀ : J → ℝ, ENNReal.ofReal (Real.exp (pairSiteA lam h K₀ ε y₀))
      = ENNReal.ofReal (Real.exp (isingSpin (ε 0) * h 0 + isingSpin (ε 1) * h 1
          + isingSpin (ε 0) * isingSpin (ε 1) * lam))
        * ENNReal.ofReal (Real.exp (∑ j, (isingSpin (ε 0) * K₀ 0 j + isingSpin (ε 1) * K₀ 1 j)
          * y₀ j)) := by
    intro y₀
    rw [pairSiteA_eq, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp_rw [h1]
  have hm2 : Measurable fun y₀ : J → ℝ => ENNReal.ofReal (Real.exp
      (∑ j, (isingSpin (ε 0) * K₀ 0 j + isingSpin (ε 1) * K₀ 1 j) * y₀ j)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (Finset.measurable_sum _ fun j _ => measurable_const.mul (measurable_pi_apply j)))
  rw [lintegral_const_mul _ hm2, lintegral_ofReal_exp_sum_mul_pi_gaussianReal (fun _ : J => v₀)
      (fun j => isingSpin (ε 0) * K₀ 0 j + isingSpin (ε 1) * K₀ 1 j)]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- `𝔼_{y₀} 𝔼_y |Y_{κ+1}| < ∞`, from `0 ≤ Y_{κ+1} ≤ exp Y_{κ+1}`. -/
theorem lintegral_lintegral_enorm_log_ofReal_exp_pairSiteF_ne_top (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0)
    (lam : ℝ) (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ) :
    ∫⁻ y₀, ∫⁻ y, ‖Real.log (ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))).toReal‖ₑ
      ∂Measure.pi (siteGaussianMarks J κ vs) ∂Measure.pi (fun _ : J => gaussianReal 0 v₀)
      ≠ ∞ := by
  refine ne_top_of_le_ne_top (lintegral_lintegral_ofReal_exp_pairSiteF_ne_top v₀ vs lam h K₀ K)
    (lintegral_mono fun y₀ => lintegral_mono fun y => ?_)
  have h0 : 0 ≤ pairSiteF lam h K₀ K y₀ y := pairSiteY_nonneg lam _ _
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp, Real.enorm_eq_ofReal_abs,
    abs_of_nonneg h0]
  exact ENNReal.ofReal_le_ofReal
    (by linarith [Real.add_one_le_exp (pairSiteF lam h K₀ K y₀ y)])

theorem lintegral_lintegral_enorm_pairSiteF_ne_top (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (lam : ℝ)
    (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ) :
    ∫⁻ y₀, ∫⁻ y, ‖pairSiteF lam h K₀ K y₀ y‖ₑ
      ∂Measure.pi (siteGaussianMarks J κ vs) ∂Measure.pi (fun _ : J => gaussianReal 0 v₀)
      ≠ ∞ := by
  have h1 : ∀ x : ℝ, (ENNReal.ofReal (Real.exp x)).toReal = Real.exp x := fun x =>
    ENNReal.toReal_ofReal (Real.exp_pos x).le
  have := lintegral_lintegral_enorm_log_ofReal_exp_pairSiteF_ne_top v₀ vs lam h K₀ K
  simp_rw [h1, Real.log_exp] at this
  exact this

/-! ### `Y₀` as an expectation over the cascade -/

/-- The one-site branch functions `exp Y_{κ+1}(λ, y₀, ·)`. -/
def pairSiteG (lam : ℝ) (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ)
    (y₀ : J → ℝ) (y : Fin κ → J → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (pairSiteF lam h K₀ K y₀ y))

lemma measurable_pairSiteG (lam : ℝ) (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin κ → Fin 2 → J → ℝ) : Measurable (Function.uncurry (pairSiteG lam h K₀ K)) := by
  have hc := (continuous_pairSiteF_prod h K₀ K).comp (continuous_const.prodMk continuous_id :
    Continuous fun q : (J → ℝ) × (Fin κ → J → ℝ) => (lam, q))
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hc.measurable)

lemma measurable_pairSiteMark_right (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ)
    (y₀ : J → ℝ) (l : Fin 2) : Measurable fun y : Fin κ → J → ℝ => pairSiteMark K₀ K y₀ y l := by
  unfold pairSiteMark
  exact measurable_const.add (Finset.measurable_sum _ fun p _ => Finset.measurable_sum _ fun j _ =>
    measurable_const.mul ((measurable_pi_apply j).comp (measurable_pi_apply p)))

lemma measurable_pairSiteG_right (lam : ℝ) (h : Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ)
    (K : Fin κ → Fin 2 → J → ℝ) (y₀ : J → ℝ) : Measurable (pairSiteG lam h K₀ K y₀) := by
  unfold pairSiteG pairSiteF pairSiteY
  have hA : Measurable fun y : Fin κ → J → ℝ => h 0 + pairSiteMark K₀ K y₀ y 0 :=
    measurable_const.add (measurable_pairSiteMark_right K₀ K y₀ 0)
  have hB : Measurable fun y : Fin κ → J → ℝ => h 1 + pairSiteMark K₀ K y₀ y 1 :=
    measurable_const.add (measurable_pairSiteMark_right K₀ K y₀ 1)
  refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Real.measurable_log.comp ?_))
  exact (((Real.continuous_cosh.measurable.comp hA).mul
    (Real.continuous_cosh.measurable.comp hB)).mul_const _).add
    (((Real.continuous_sinh.measurable.comp hA).mul
      (Real.continuous_sinh.measurable.comp hB)).mul_const _)

variable (ns : Fin κ → ℝ) (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (lam : ℝ) (h : Fin 2 → ℝ)
  (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ)

/-- The joint law of the root marks, the cascade weights and the marks along the branches. -/
abbrev pairSiteLaw : Measure ((J → ℝ) × (CascadeWeights κ × CascadeMarks (J → ℝ) κ)) :=
  (Measure.pi fun _ : J => gaussianReal 0 v₀).prod
    ((cascadeWeightsLaw κ ns).prod (cascadeMarksLaw κ (siteGaussianMarks J κ vs)))

/-- The integrand of Theorem 14.2.1 for the one-site problem:
`log (∑_α v_α exp Y_{κ+1}(λ, ζ_α) / ∑_α v_α)`. -/
def pairSiteLogSum (q : (J → ℝ) × (CascadeWeights κ × CascadeMarks (J → ℝ) κ)) : ℝ :=
  Real.log ((cascadeSum κ (pairSiteG lam h K₀ K q.1) (cascadeZip κ (q.2.1, q.2.2))).toReal
    / (cascadeSum κ (fun _ => 1) (cascadeZip κ (q.2.1, q.2.2))).toReal)

lemma measurable_pairSiteLogSum : Measurable (pairSiteLogSum lam h K₀ K) := by
  have h1 := (measurable_log_cascadeSum_div_prod κ (pairSiteG lam h K₀ K)
    (measurable_pairSiteG lam h K₀ K)).comp
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)) :
      Measurable fun q : (J → ℝ) × (CascadeWeights κ × CascadeMarks (J → ℝ) κ) =>
        (q.2.1, (q.1, q.2.2)))
  exact h1

lemma integrable_pairSiteLogSum (hsm : StrictMono ns) (hpos : ∀ i, 0 < ns i)
    (hlt : ∀ i, ns i < 1) : Integrable (pairSiteLogSum lam h K₀ K) (pairSiteLaw ns v₀ vs) :=
  integrable_log_cascadeSum_div_prod' κ (Measure.pi fun _ : J => gaussianReal 0 v₀) ns
    (siteGaussianMarks J κ vs) (pairSiteG lam h K₀ K) hsm hpos hlt (measurable_pairSiteG lam h K₀ K)
    (fun _ _ => ENNReal.ofReal_pos.2 (Real.exp_pos _)) (fun _ _ => ENNReal.ofReal_ne_top)
    (lintegral_lintegral_ofReal_exp_pairSiteF_ne_top v₀ vs lam h K₀ K)
    (lintegral_lintegral_enorm_log_ofReal_exp_pairSiteF_ne_top v₀ vs lam h K₀ K)

/-- **`Y₀(λ)` through Theorem 14.2.1**: the expectation over the root marks and the cascade of
`log (∑_α v_α exp Y_{κ+1}(λ, ζ_α) / ∑_α v_α)`. -/
theorem pairSiteY₀_eq_integral (hsm : StrictMono ns) (hpos : ∀ i, 0 < ns i)
    (hlt : ∀ i, ns i < 1) :
    pairSiteY₀ ns v₀ vs lam h K₀ K = ∫ q, pairSiteLogSum lam h K₀ K q ∂pairSiteLaw ns v₀ vs := by
  have hGm := measurable_pairSiteG lam h K₀ K
  have hGpos : ∀ (y₀ : J → ℝ) y, 0 < pairSiteG lam h K₀ K y₀ y :=
    fun _ _ => ENNReal.ofReal_pos.2 (Real.exp_pos _)
  have hfin : ∀ y₀, cascadeRec κ ns (siteGaussianMarks J κ vs) (pairSiteG lam h K₀ K y₀) ≠ ∞ :=
    fun y₀ => ne_top_of_le_ne_top (lintegral_ofReal_exp_pairSiteF_ne_top vs lam h K₀ K y₀)
      (cascadeRec_le_lintegral_pi κ ns _ (measurable_pairSiteG_right lam h K₀ K y₀) hpos
        (fun i => (hlt i).le))
  have hI := integrable_pairSiteLogSum ns v₀ vs lam h K₀ K hsm hpos hlt
  unfold pairSiteLaw pairSiteLogSum at hI ⊢
  rw [integral_prod _ hI]
  unfold pairSiteY₀
  refine integral_congr_ae (Filter.Eventually.of_forall fun y₀ => ?_)
  change parisiRec κ ns (siteGaussianMarks J κ vs) (pairSiteF lam h K₀ K y₀)
    = ∫ r : CascadeWeights κ × CascadeMarks (J → ℝ) κ,
        Real.log ((cascadeSum κ (pairSiteG lam h K₀ K y₀) (cascadeZip κ (r.1, r.2))).toReal
          / (cascadeSum κ (fun _ => 1) (cascadeZip κ (r.1, r.2))).toReal)
        ∂(cascadeWeightsLaw κ ns).prod (cascadeMarksLaw κ (siteGaussianMarks J κ vs))
  rw [integral_log_cascadeSum_div_eq_of κ ns (siteGaussianMarks J κ vs) (pairSiteG lam h K₀ K)
    hsm hpos hlt hGm hGpos hfin y₀]
  rfl

/-! ### The `λ`-structure of the cascade sum -/

/-- `ch(ζ¹ + ζ²)` at the marks along a branch, in `ℝ≥0∞`. -/
def pairSiteCoshP (y₀ : J → ℝ) (y : Fin κ → J → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.cosh ((h 0 + pairSiteMark K₀ K y₀ y 0) + (h 1 + pairSiteMark K₀ K y₀ y 1)))

/-- `ch(ζ¹ − ζ²)` at the marks along a branch, in `ℝ≥0∞`. -/
def pairSiteCoshM (y₀ : J → ℝ) (y : Fin κ → J → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.cosh ((h 0 + pairSiteMark K₀ K y₀ y 0) - (h 1 + pairSiteMark K₀ K y₀ y 1)))

lemma measurable_pairSiteCoshP : Measurable (Function.uncurry (pairSiteCoshP h K₀ K)) := by
  have hc : Continuous fun q : (J → ℝ) × (Fin κ → J → ℝ) =>
      Real.cosh ((h 0 + pairSiteMark K₀ K q.1 q.2 0) + (h 1 + pairSiteMark K₀ K q.1 q.2 1)) :=
    Real.continuous_cosh.comp ((continuous_const.add (continuous_pairSiteMark K₀ K 0)).add
      (continuous_const.add (continuous_pairSiteMark K₀ K 1)))
  exact ENNReal.measurable_ofReal.comp hc.measurable

lemma measurable_pairSiteCoshM : Measurable (Function.uncurry (pairSiteCoshM h K₀ K)) := by
  have hc : Continuous fun q : (J → ℝ) × (Fin κ → J → ℝ) =>
      Real.cosh ((h 0 + pairSiteMark K₀ K q.1 q.2 0) - (h 1 + pairSiteMark K₀ K q.1 q.2 1)) :=
    Real.continuous_cosh.comp ((continuous_const.add (continuous_pairSiteMark K₀ K 0)).sub
      (continuous_const.add (continuous_pairSiteMark K₀ K 1)))
  exact ENNReal.measurable_ofReal.comp hc.measurable

lemma measurable_pairSiteCoshP_right (y₀ : J → ℝ) : Measurable (pairSiteCoshP h K₀ K y₀) := by
  unfold pairSiteCoshP
  refine ENNReal.measurable_ofReal.comp (Real.continuous_cosh.measurable.comp ?_)
  exact (measurable_const.add (measurable_pairSiteMark_right K₀ K y₀ 0)).add
    (measurable_const.add (measurable_pairSiteMark_right K₀ K y₀ 1))

lemma measurable_pairSiteCoshM_right (y₀ : J → ℝ) : Measurable (pairSiteCoshM h K₀ K y₀) := by
  unfold pairSiteCoshM
  refine ENNReal.measurable_ofReal.comp (Real.continuous_cosh.measurable.comp ?_)
  exact (measurable_const.add (measurable_pairSiteMark_right K₀ K y₀ 0)).sub
    (measurable_const.add (measurable_pairSiteMark_right K₀ K y₀ 1))

/-- `exp Y_{κ+1}(λ) = (e^λ ch(ζ¹ + ζ²) + e^{−λ} ch(ζ¹ − ζ²))/2`. -/
lemma pairSiteG_eq (y₀ : J → ℝ) :
    pairSiteG lam h K₀ K y₀ = fun y => ENNReal.ofReal (Real.exp lam / 2) * pairSiteCoshP h K₀ K y₀ y
      + ENNReal.ofReal (Real.exp (-lam) / 2) * pairSiteCoshM h K₀ K y₀ y := by
  funext y
  unfold pairSiteG pairSiteCoshP pairSiteCoshM pairSiteF
  set A := h 0 + pairSiteMark K₀ K y₀ y 0
  set B := h 1 + pairSiteMark K₀ K y₀ y 1
  rw [exp_pairSiteY, pairSiteY_arg_eq,
    show (Real.cosh (A + B) * Real.exp lam + Real.cosh (A - B) * Real.exp (-lam)) / 2
      = Real.exp lam / 2 * Real.cosh (A + B) + Real.exp (-lam) / 2 * Real.cosh (A - B) by ring,
    ENNReal.ofReal_add (mul_nonneg (by positivity) (Real.cosh_pos _).le)
      (mul_nonneg (by positivity) (Real.cosh_pos _).le),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]

/-- `P(y₀) = ∑_α v_α ch(ζ¹_α + ζ²_α)`. -/
def pairSiteP (y₀ : J → ℝ) (ω : CascadeSpace (J → ℝ) κ) : ℝ≥0∞ :=
  cascadeSum κ (pairSiteCoshP h K₀ K y₀) ω

/-- `M(y₀) = ∑_α v_α ch(ζ¹_α − ζ²_α)`. -/
def pairSiteM (y₀ : J → ℝ) (ω : CascadeSpace (J → ℝ) κ) : ℝ≥0∞ :=
  cascadeSum κ (pairSiteCoshM h K₀ K y₀) ω

/-- **The `λ`-structure of the cascade sum**:
`∑_α v_α exp Y_{κ+1}(λ, ζ_α) = (e^λ P + e^{−λ} M)/2`. -/
theorem cascadeSum_pairSiteG (y₀ : J → ℝ) (ω : CascadeSpace (J → ℝ) κ) :
    cascadeSum κ (pairSiteG lam h K₀ K y₀) ω
      = ENNReal.ofReal (Real.exp lam / 2) * pairSiteP h K₀ K y₀ ω
        + ENNReal.ofReal (Real.exp (-lam) / 2) * pairSiteM h K₀ K y₀ ω := by
  have hP : Measurable (pairSiteCoshP h K₀ K y₀) := measurable_pairSiteCoshP_right h K₀ K y₀
  have hM : Measurable (pairSiteCoshM h K₀ K y₀) := measurable_pairSiteCoshM_right h K₀ K y₀
  have hG : Measurable fun y => ENNReal.ofReal (Real.exp lam / 2) * pairSiteCoshP h K₀ K y₀ y :=
    hP.const_mul _
  have hH : Measurable fun y => ENNReal.ofReal (Real.exp (-lam) / 2) * pairSiteCoshM h K₀ K y₀ y :=
    hM.const_mul _
  unfold pairSiteP pairSiteM
  rw [pairSiteG_eq, cascadeSum_add κ hG hH, cascadeSum_const_mul κ _ hP,
    cascadeSum_const_mul κ _ hM]

lemma weightSum_le_pairSiteP (y₀ : J → ℝ) (w : CascadeWeights κ) (z : CascadeMarks (J → ℝ) κ) :
    weightSum κ w ≤ pairSiteP h K₀ K y₀ (cascadeZip κ (w, z)) := by
  rw [← cascadeSum_one_cascadeZip κ w z]
  exact cascadeSum_mono κ (fun y => ENNReal.one_le_ofReal.2 (Real.one_le_cosh _)) _

/-- `ch(ζ¹ + ζ²) ≤ 2 exp Y_{κ+1}(0)`. -/
lemma cosh_add_le_two_mul_exp_pairSiteY_zero (A B : ℝ) :
    Real.cosh (A + B) ≤ 2 * Real.exp (pairSiteY 0 A B) := by
  rw [exp_pairSiteY, pairSiteY_arg_eq]
  simp only [neg_zero, Real.exp_zero, mul_one]
  linarith [Real.cosh_pos (A - B)]

/-- `ch(ζ¹ − ζ²) ≤ 2 exp Y_{κ+1}(0)`. -/
lemma cosh_sub_le_two_mul_exp_pairSiteY_zero (A B : ℝ) :
    Real.cosh (A - B) ≤ 2 * Real.exp (pairSiteY 0 A B) := by
  rw [exp_pairSiteY, pairSiteY_arg_eq]
  simp only [neg_zero, Real.exp_zero, mul_one]
  linarith [Real.cosh_pos (A + B)]

lemma lintegral_pairSiteCoshP_ne_top (y₀ : J → ℝ) :
    ∫⁻ y, pairSiteCoshP h K₀ K y₀ y ∂Measure.pi (siteGaussianMarks J κ vs) ≠ ∞ := by
  have hm : Measurable fun y : Fin κ → J → ℝ =>
      ENNReal.ofReal (Real.exp (pairSiteF 0 h K₀ K y₀ y)) := measurable_pairSiteG_right 0 h K₀ K y₀
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := 2))
    (lintegral_ofReal_exp_pairSiteF_ne_top vs 0 h K₀ K y₀)) ?_
  rw [← lintegral_const_mul _ hm]
  refine lintegral_mono fun y => ?_
  unfold pairSiteCoshP
  rw [← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (cosh_add_le_two_mul_exp_pairSiteY_zero _ _)

lemma lintegral_pairSiteCoshM_ne_top (y₀ : J → ℝ) :
    ∫⁻ y, pairSiteCoshM h K₀ K y₀ y ∂Measure.pi (siteGaussianMarks J κ vs) ≠ ∞ := by
  have hm : Measurable fun y : Fin κ → J → ℝ =>
      ENNReal.ofReal (Real.exp (pairSiteF 0 h K₀ K y₀ y)) := measurable_pairSiteG_right 0 h K₀ K y₀
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := 2))
    (lintegral_ofReal_exp_pairSiteF_ne_top vs 0 h K₀ K y₀)) ?_
  rw [← lintegral_const_mul _ hm]
  refine lintegral_mono fun y => ?_
  unfold pairSiteCoshM
  rw [← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (cosh_sub_le_two_mul_exp_pairSiteY_zero _ _)

/-- **Almost-sure regularity**: `P, M < ∞` and `0 < ∑_α v_α < ∞`, jointly in the root marks, the
weights and the marks. -/
theorem ae_pairSite_regular (hsm : StrictMono ns) (hpos : ∀ i, 0 < ns i) (hlt : ∀ i, ns i < 1) :
    ∀ᵐ q ∂pairSiteLaw ns v₀ vs,
      pairSiteP h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2)) ≠ ∞
        ∧ pairSiteM h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2)) ≠ ∞
        ∧ weightSum κ q.2.1 ≠ 0 ∧ weightSum κ q.2.1 ≠ ∞ := by
  have hP := ae_cascadeSum_cascadeZip_lt_top κ (Measure.pi fun _ : J => gaussianReal 0 v₀) ns
    (siteGaussianMarks J κ vs) (pairSiteCoshP h K₀ K) hsm hpos hlt (measurable_pairSiteCoshP h K₀ K)
    (lintegral_pairSiteCoshP_ne_top vs h K₀ K)
  have hM := ae_cascadeSum_cascadeZip_lt_top κ (Measure.pi fun _ : J => gaussianReal 0 v₀) ns
    (siteGaussianMarks J κ vs) (pairSiteCoshM h K₀ K) hsm hpos hlt (measurable_pairSiteCoshM h K₀ K)
    (lintegral_pairSiteCoshM_ne_top vs h K₀ K)
  have hW := ae_weightSum_prod κ (Measure.pi fun _ : J => gaussianReal 0 v₀) ns
    (siteGaussianMarks J κ vs) hsm hpos hlt
  filter_upwards [hP, hM, hW] with q h1 h2 h3
  exact ⟨h1.ne, h2.ne, h3.1, h3.2⟩

/-! ### Elementary calculus of `log ((e^λ p + e^{-λ} m)/2)` -/

/-- `log ((e^λ p + e^{−λ} m)/2)`. -/
def logExpMix (p m lam : ℝ) : ℝ := Real.log ((Real.exp lam * p + Real.exp (-lam) * m) / 2)

/-- Its derivative `(e^λ p − e^{−λ} m)/(e^λ p + e^{−λ} m)`. -/
def logExpMix' (p m lam : ℝ) : ℝ :=
  (Real.exp lam * p - Real.exp (-lam) * m) / (Real.exp lam * p + Real.exp (-lam) * m)

lemma logExpMix_den_pos {p m : ℝ} (hp : 0 ≤ p) (hm : 0 ≤ m) (hpm : 0 < p + m) (lam : ℝ) :
    0 < Real.exp lam * p + Real.exp (-lam) * m := by
  have h1 : 0 ≤ Real.exp lam * p := by positivity
  have h2 : 0 ≤ Real.exp (-lam) * m := by positivity
  rcases lt_or_ge 0 p with hp' | hp'
  · linarith [mul_pos (Real.exp_pos lam) hp']
  · have hm' : 0 < m := by linarith
    linarith [mul_pos (Real.exp_pos (-lam)) hm']

lemma hasDerivAt_exp_neg (lam : ℝ) :
    HasDerivAt (fun l => Real.exp (-l)) (-Real.exp (-lam)) lam :=
  (hasDerivAt_neg (x := lam)).exp.congr_deriv (by ring)

lemma hasDerivAt_logExpMix {p m : ℝ} (hp : 0 ≤ p) (hm : 0 ≤ m) (hpm : 0 < p + m) (lam : ℝ) :
    HasDerivAt (logExpMix p m) (logExpMix' p m lam) lam := by
  unfold logExpMix logExpMix'
  have hD : HasDerivAt (fun l => (Real.exp l * p + Real.exp (-l) * m) / 2)
      ((Real.exp lam * p - Real.exp (-lam) * m) / 2) lam := by
    have h1 : HasDerivAt (fun l => Real.exp l * p + Real.exp (-l) * m)
        (Real.exp lam * p + -Real.exp (-lam) * m) lam :=
      ((Real.hasDerivAt_exp lam).mul_const p).add ((hasDerivAt_exp_neg lam).mul_const m)
    exact (h1.div_const 2).congr_deriv (by ring)
  have hpos := logExpMix_den_pos hp hm hpm lam
  refine (hD.log (by positivity)).congr_deriv ?_
  rw [div_div_div_cancel_right₀ (two_ne_zero : (2 : ℝ) ≠ 0)]

lemma hasDerivAt_logExpMix' {p m : ℝ} (hp : 0 ≤ p) (hm : 0 ≤ m) (hpm : 0 < p + m) (lam : ℝ) :
    HasDerivAt (logExpMix' p m) (1 - logExpMix' p m lam ^ 2) lam := by
  unfold logExpMix'
  have hN : HasDerivAt (fun l => Real.exp l * p - Real.exp (-l) * m)
      (Real.exp lam * p - -Real.exp (-lam) * m) lam :=
    ((Real.hasDerivAt_exp lam).mul_const p).sub ((hasDerivAt_exp_neg lam).mul_const m)
  have hD : HasDerivAt (fun l => Real.exp l * p + Real.exp (-l) * m)
      (Real.exp lam * p + -Real.exp (-lam) * m) lam :=
    ((Real.hasDerivAt_exp lam).mul_const p).add ((hasDerivAt_exp_neg lam).mul_const m)
  have hpos := logExpMix_den_pos hp hm hpm lam
  refine (hN.div hD hpos.ne').congr_deriv ?_
  field_simp
  ring

lemma abs_logExpMix'_le_one {p m : ℝ} (hp : 0 ≤ p) (hm : 0 ≤ m) (lam : ℝ) :
    |logExpMix' p m lam| ≤ 1 := by
  unfold logExpMix'
  have h1 : 0 ≤ Real.exp lam * p := by positivity
  have h2 : 0 ≤ Real.exp (-lam) * m := by positivity
  rcases eq_or_lt_of_le (add_nonneg h1 h2) with h0 | h0
  · rw [← h0, div_zero, abs_zero]
    exact zero_le_one
  · rw [abs_div, abs_of_pos h0, div_le_one h0, abs_le]
    constructor <;> linarith

lemma sq_logExpMix'_le_one {p m : ℝ} (hp : 0 ≤ p) (hm : 0 ≤ m) (lam : ℝ) :
    logExpMix' p m lam ^ 2 ≤ 1 := by
  have h := abs_le.1 (abs_logExpMix'_le_one hp hm lam)
  nlinarith [h.1, h.2]

/-! ### The derivatives of `Y₀` through the cascade -/

lemma measurable_pairSiteP_toReal :
    Measurable fun q : (J → ℝ) × (CascadeWeights κ × CascadeMarks (J → ℝ) κ) =>
      (pairSiteP h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal :=
  ((measurable_cascadeSum_prod κ (G := pairSiteCoshP h K₀ K) (measurable_pairSiteCoshP h K₀ K)).comp
    (measurable_fst.prodMk ((measurable_cascadeZip κ).comp measurable_snd))).ennreal_toReal

lemma measurable_pairSiteM_toReal :
    Measurable fun q : (J → ℝ) × (CascadeWeights κ × CascadeMarks (J → ℝ) κ) =>
      (pairSiteM h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal :=
  ((measurable_cascadeSum_prod κ (G := pairSiteCoshM h K₀ K) (measurable_pairSiteCoshM h K₀ K)).comp
    (measurable_fst.prodMk ((measurable_cascadeZip κ).comp measurable_snd))).ennreal_toReal

lemma measurable_logExpMix'_pairSite :
    Measurable fun q : (J → ℝ) × (CascadeWeights κ × CascadeMarks (J → ℝ) κ) =>
      logExpMix' (pairSiteP h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal
        (pairSiteM h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal lam := by
  unfold logExpMix'
  exact ((measurable_const.mul (measurable_pairSiteP_toReal h K₀ K)).sub
    (measurable_const.mul (measurable_pairSiteM_toReal h K₀ K))).div
    ((measurable_const.mul (measurable_pairSiteP_toReal h K₀ K)).add
      (measurable_const.mul (measurable_pairSiteM_toReal h K₀ K)))

/-- On the regular set, `log (S(λ)/∑ v_α) = log ((e^λ p + e^{−λ} m)/2) − log ∑ v_α`. -/
lemma pairSiteLogSum_eq {q : (J → ℝ) × (CascadeWeights κ × CascadeMarks (J → ℝ) κ)}
    (hq : pairSiteP h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2)) ≠ ∞
      ∧ pairSiteM h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2)) ≠ ∞
      ∧ weightSum κ q.2.1 ≠ 0 ∧ weightSum κ q.2.1 ≠ ∞) :
    pairSiteLogSum lam h K₀ K q
      = logExpMix (pairSiteP h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal
          (pairSiteM h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal lam
        - Real.log (weightSum κ q.2.1).toReal := by
  obtain ⟨hP, hM, hZ0, hZ⟩ := hq
  have hPpos : 0 < (pairSiteP h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 hZ0)
      (weightSum_le_pairSiteP h K₀ K q.1 q.2.1 q.2.2))) hP
  have hMnn : 0 ≤ (pairSiteM h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal :=
    ENNReal.toReal_nonneg
  unfold pairSiteLogSum logExpMix
  rw [cascadeSum_pairSiteG, cascadeSum_one_cascadeZip,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)]
  have hnum : 0 < Real.exp lam / 2 * (pairSiteP h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal
      + Real.exp (-lam) / 2 * (pairSiteM h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal :=
    add_pos_of_pos_of_nonneg (mul_pos (by positivity) hPpos) (mul_nonneg (by positivity) hMnn)
  rw [Real.log_div hnum.ne' (ENNReal.toReal_pos hZ0 hZ).ne']
  congr 2
  ring

lemma hasDerivAt_pairSiteLogSum {q : (J → ℝ) × (CascadeWeights κ × CascadeMarks (J → ℝ) κ)}
    (hq : pairSiteP h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2)) ≠ ∞
      ∧ pairSiteM h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2)) ≠ ∞
      ∧ weightSum κ q.2.1 ≠ 0 ∧ weightSum κ q.2.1 ≠ ∞) (l : ℝ) :
    HasDerivAt (fun l => pairSiteLogSum l h K₀ K q)
      (logExpMix' (pairSiteP h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal
        (pairSiteM h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal l) l := by
  have hPpos : 0 < (pairSiteP h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 hq.2.2.1)
      (weightSum_le_pairSiteP h K₀ K q.1 q.2.1 q.2.2))) hq.1
  have hfun : (fun l => pairSiteLogSum l h K₀ K q)
      = fun l => logExpMix (pairSiteP h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal
          (pairSiteM h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal l
        - Real.log (weightSum κ q.2.1).toReal :=
    funext fun l => pairSiteLogSum_eq l h K₀ K hq
  rw [hfun]
  have hMnn : 0 ≤ (pairSiteM h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal :=
    ENNReal.toReal_nonneg
  exact (hasDerivAt_logExpMix hPpos.le hMnn (by linarith) l).sub_const _

/-- **`Y₀'(λ)` through the cascade**: `Y₀' = 𝔼 (S'/S)`. -/
theorem hasDerivAt_pairSiteY₀_cascade (hsm : StrictMono ns) (hpos : ∀ i, 0 < ns i)
    (hlt : ∀ i, ns i < 1) :
    HasDerivAt (fun l => pairSiteY₀ ns v₀ vs l h K₀ K)
      (∫ q, logExpMix' (pairSiteP h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal
        (pairSiteM h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal lam ∂pairSiteLaw ns v₀ vs)
      lam := by
  have hrep : (fun l => pairSiteY₀ ns v₀ vs l h K₀ K)
      = fun l => ∫ q, pairSiteLogSum l h K₀ K q ∂pairSiteLaw ns v₀ vs :=
    funext fun l => pairSiteY₀_eq_integral ns v₀ vs l h K₀ K hsm hpos hlt
  rw [hrep]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := pairSiteLaw ns v₀ vs)
    (F := fun l q => pairSiteLogSum l h K₀ K q)
    (F' := fun l q => logExpMix' (pairSiteP h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal
      (pairSiteM h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal l)
    (bound := fun _ => 1) (s := univ) univ_mem
    (Filter.Eventually.of_forall fun l => (measurable_pairSiteLogSum l h K₀ K).aestronglyMeasurable)
    (integrable_pairSiteLogSum ns v₀ vs lam h K₀ K hsm hpos hlt)
    (measurable_logExpMix'_pairSite lam h K₀ K).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q l _ => ?_) (integrable_const 1) ?_).2
  · rw [Real.norm_eq_abs]
    exact abs_logExpMix'_le_one ENNReal.toReal_nonneg ENNReal.toReal_nonneg l
  · filter_upwards [ae_pairSite_regular ns v₀ vs h K₀ K hsm hpos hlt] with q hq
    exact fun l _ => hasDerivAt_pairSiteLogSum h K₀ K hq l

/-- The tilted-average form of `Y₀'` (`pairSiteY₀'`) agrees with the cascade form. -/
theorem pairSiteY₀'_eq_cascade (hsm : StrictMono ns) (hpos : ∀ i, 0 < ns i)
    (hlt : ∀ i, ns i < 1) :
    pairSiteY₀' ns v₀ vs lam h K₀ K
      = ∫ q, logExpMix' (pairSiteP h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal
          (pairSiteM h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal lam ∂pairSiteLaw ns v₀ vs :=
  (hasDerivAt_pairSiteY₀ ns hpos (fun i => (hlt i).le) v₀ vs lam h K₀ K).unique
    (hasDerivAt_pairSiteY₀_cascade ns v₀ vs lam h K₀ K hsm hpos hlt)

/-- **`Y₀''(λ) = 1 − 𝔼 (S'/S)²`** (Talagrand's proof of Lemma 14.6.5). -/
def pairSiteY₀'' : ℝ :=
  ∫ q, (1 - logExpMix' (pairSiteP h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal
    (pairSiteM h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal lam ^ 2) ∂pairSiteLaw ns v₀ vs

lemma integrable_logExpMix'_pairSite :
    Integrable (fun q => logExpMix' (pairSiteP h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal
      (pairSiteM h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal lam) (pairSiteLaw ns v₀ vs) :=
  (integrable_const (1 : ℝ)).mono' (measurable_logExpMix'_pairSite lam h K₀ K).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs]
      exact abs_logExpMix'_le_one ENNReal.toReal_nonneg ENNReal.toReal_nonneg lam)

/-- **`Y₀'` is differentiable, with derivative `Y₀''`.** -/
theorem hasDerivAt_pairSiteY₀' (hsm : StrictMono ns) (hpos : ∀ i, 0 < ns i)
    (hlt : ∀ i, ns i < 1) :
    HasDerivAt (fun l => pairSiteY₀' ns v₀ vs l h K₀ K) (pairSiteY₀'' ns v₀ vs lam h K₀ K) lam := by
  have hrep : (fun l => pairSiteY₀' ns v₀ vs l h K₀ K)
      = fun l => ∫ q, logExpMix' (pairSiteP h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal
          (pairSiteM h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal l ∂pairSiteLaw ns v₀ vs :=
    funext fun l => pairSiteY₀'_eq_cascade ns v₀ vs l h K₀ K hsm hpos hlt
  rw [hrep]
  unfold pairSiteY₀''
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := pairSiteLaw ns v₀ vs)
    (F := fun l q => logExpMix' (pairSiteP h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal
      (pairSiteM h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal l)
    (F' := fun l q => 1 - logExpMix' (pairSiteP h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal
      (pairSiteM h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal l ^ 2)
    (bound := fun _ => 1) (s := univ) univ_mem
    (Filter.Eventually.of_forall fun l =>
      (measurable_logExpMix'_pairSite l h K₀ K).aestronglyMeasurable)
    (integrable_logExpMix'_pairSite ns v₀ vs lam h K₀ K)
    (measurable_const.sub ((measurable_logExpMix'_pairSite lam h K₀ K).pow_const 2)
      |>.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun q l _ => ?_) (integrable_const 1) ?_).2
  · rw [Real.norm_eq_abs, abs_le]
    have h1 := sq_logExpMix'_le_one (ENNReal.toReal_nonneg
      (a := pairSiteP h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2)))) (ENNReal.toReal_nonneg
      (a := pairSiteM h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2)))) l
    have h2 := sq_nonneg (logExpMix' (pairSiteP h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal
      (pairSiteM h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal l)
    constructor <;> linarith
  · filter_upwards [ae_pairSite_regular ns v₀ vs h K₀ K hsm hpos hlt] with q hq
    intro l _
    have hPpos : 0 < (pairSiteP h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal :=
      ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 hq.2.2.1)
        (weightSum_le_pairSiteP h K₀ K q.1 q.2.1 q.2.2))) hq.1
    have hMnn : 0 ≤ (pairSiteM h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal :=
      ENNReal.toReal_nonneg
    exact hasDerivAt_logExpMix' hPpos.le hMnn (by linarith) l

/-- **Lemma 14.6.5, lower half**: `0 ≤ Y₀''`. -/
theorem pairSiteY₀''_nonneg : 0 ≤ pairSiteY₀'' ns v₀ vs lam h K₀ K :=
  integral_nonneg fun q => by
    have := sq_logExpMix'_le_one (ENNReal.toReal_nonneg
      (a := pairSiteP h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2)))) (ENNReal.toReal_nonneg
      (a := pairSiteM h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2)))) lam
    change (0 : ℝ) ≤ 1 - _
    linarith

/-- **Lemma 14.6.5, upper half**: `Y₀'' ≤ 1`. -/
theorem pairSiteY₀''_le_one : pairSiteY₀'' ns v₀ vs lam h K₀ K ≤ 1 := by
  unfold pairSiteY₀''
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun q => ?_) (integrable_const 1)
    (Filter.Eventually.of_forall fun q => ?_)).trans ?_
  · have := sq_logExpMix'_le_one (ENNReal.toReal_nonneg
      (a := pairSiteP h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2)))) (ENNReal.toReal_nonneg
      (a := pairSiteM h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2)))) lam
    change (0 : ℝ) ≤ 1 - _
    linarith
  · change (1 : ℝ) - _ ≤ 1
    linarith [sq_nonneg (logExpMix' (pairSiteP h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal
      (pairSiteM h K₀ K q.1 (cascadeZip κ (q.2.1, q.2.2))).toReal lam)]
  · simp

/-! ### Convexity, for all admissible exponents -/

/-- `Y₀` is convex in `λ` (strictly increasing exponents). -/
theorem convexOn_pairSiteY₀_of_strictMono (hsm : StrictMono ns) (hpos : ∀ i, 0 < ns i)
    (hlt : ∀ i, ns i < 1) :
    ConvexOn ℝ univ fun l => pairSiteY₀ ns v₀ vs l h K₀ K := by
  have hd1 : ∀ l, HasDerivAt (fun l => pairSiteY₀ ns v₀ vs l h K₀ K)
      (pairSiteY₀' ns v₀ vs l h K₀ K) l :=
    fun l => hasDerivAt_pairSiteY₀ ns hpos (fun i => (hlt i).le) v₀ vs l h K₀ K
  have hderiv : deriv (fun l => pairSiteY₀ ns v₀ vs l h K₀ K)
      = fun l => pairSiteY₀' ns v₀ vs l h K₀ K := funext fun l => (hd1 l).deriv
  have hd2 : ∀ l, HasDerivAt (fun l => pairSiteY₀' ns v₀ vs l h K₀ K)
      (pairSiteY₀'' ns v₀ vs l h K₀ K) l :=
    fun l => hasDerivAt_pairSiteY₀' ns v₀ vs l h K₀ K hsm hpos hlt
  refine convexOn_univ_of_deriv2_nonneg (fun l => (hd1 l).differentiableAt) ?_ ?_
  · rw [hderiv]
    exact fun l => (hd2 l).differentiableAt
  · intro x
    change 0 ≤ deriv (deriv fun l => pairSiteY₀ ns v₀ vs l h K₀ K) x
    rw [hderiv, (hd2 x).deriv]
    exact pairSiteY₀''_nonneg ns v₀ vs x h K₀ K

/-- `Y₀(λ) − λ²/2` is concave in `λ` (strictly increasing exponents). -/
theorem concaveOn_pairSiteY₀_sub_sq_of_strictMono (hsm : StrictMono ns) (hpos : ∀ i, 0 < ns i)
    (hlt : ∀ i, ns i < 1) :
    ConcaveOn ℝ univ fun l => pairSiteY₀ ns v₀ vs l h K₀ K - l * l / 2 := by
  have hsq : ∀ l : ℝ, HasDerivAt (fun l : ℝ => l * l / 2) l l := fun l =>
    (((hasDerivAt_id l).mul (hasDerivAt_id l)).div_const 2).congr_deriv (by
      simp only [id_eq, one_mul, mul_one]
      ring)
  have hd1 : ∀ l, HasDerivAt (fun l => pairSiteY₀ ns v₀ vs l h K₀ K - l * l / 2)
      (pairSiteY₀' ns v₀ vs l h K₀ K - l) l :=
    fun l => (hasDerivAt_pairSiteY₀ ns hpos (fun i => (hlt i).le) v₀ vs l h K₀ K).sub (hsq l)
  have hderiv : deriv (fun l => pairSiteY₀ ns v₀ vs l h K₀ K - l * l / 2)
      = fun l => pairSiteY₀' ns v₀ vs l h K₀ K - l := funext fun l => (hd1 l).deriv
  have hd2 : ∀ l, HasDerivAt (fun l => pairSiteY₀' ns v₀ vs l h K₀ K - l)
      (pairSiteY₀'' ns v₀ vs l h K₀ K - 1) l :=
    fun l => (hasDerivAt_pairSiteY₀' ns v₀ vs l h K₀ K hsm hpos hlt).sub (hasDerivAt_id l)
  refine concaveOn_univ_of_deriv2_nonpos (fun l => (hd1 l).differentiableAt) ?_ ?_
  · rw [hderiv]
    exact fun l => (hd2 l).differentiableAt
  · intro x
    change deriv (deriv fun l => pairSiteY₀ ns v₀ vs l h K₀ K - l * l / 2) x ≤ 0
    rw [hderiv, (hd2 x).deriv]
    linarith [pairSiteY₀''_le_one ns v₀ vs x h K₀ K]

/-- `Y₀` is continuous in the exponents on `(0, 1]^κ`. -/
theorem continuousOn_pairSiteY₀ :
    ContinuousOn (fun ns : Fin κ → ℝ => pairSiteY₀ ns v₀ vs lam h K₀ K)
      (Set.pi Set.univ fun _ => Set.Ioc (0 : ℝ) 1) := by
  have hFm : Measurable (Function.uncurry fun (y₀ : J → ℝ) (y : Fin κ → J → ℝ) =>
      pairSiteF lam h K₀ K y₀ y) := by
    have hc := (continuous_pairSiteF_prod h K₀ K).comp (continuous_const.prodMk continuous_id :
      Continuous fun q : (J → ℝ) × (Fin κ → J → ℝ) => (lam, q))
    exact hc.measurable
  exact continuousOn_integral_parisiRec κ (Measure.pi fun _ : J => gaussianReal 0 v₀)
    (siteGaussianMarks J κ vs) hFm
    (lintegral_lintegral_ofReal_exp_pairSiteF_ne_top v₀ vs lam h K₀ K)
    (lintegral_lintegral_enorm_pairSiteF_ne_top v₀ vs lam h K₀ K)

/-- **`Y₀` is convex in `λ`** for every nondecreasing `0 < n₁ ≤ ⋯ ≤ n_κ ≤ 1`. -/
theorem convexOn_pairSiteY₀ (hmono : Monotone ns) (hpos : ∀ i, 0 < ns i) (hle : ∀ i, ns i ≤ 1) :
    ConvexOn ℝ univ fun l => pairSiteY₀ ns v₀ vs l h K₀ K := by
  have hmem : ns ∈ (Set.pi Set.univ fun _ : Fin κ => Set.Ioc (0 : ℝ) 1) := by
    simp only [Set.mem_univ_pi, Set.mem_Ioc]
    exact fun i => ⟨hpos i, hle i⟩
  refine convexOn_of_tendsto (l := atTop) convex_univ
    (f := fun j l => pairSiteY₀ (strictApprox κ ns j) v₀ vs l h K₀ K)
    (fun j => convexOn_pairSiteY₀_of_strictMono (strictApprox κ ns j) v₀ vs h K₀ K
      (strictApprox_strictMono hmono hpos j) (strictApprox_pos hpos j) (strictApprox_lt_one hle j))
    fun l _ => ?_
  exact ((continuousOn_pairSiteY₀ v₀ vs l h K₀ K) ns hmem).tendsto.comp
    (tendsto_strictApprox_nhdsWithin hpos hle)

/-- **`Y₀(λ) − λ²/2` is concave in `λ`** for every nondecreasing `0 < n₁ ≤ ⋯ ≤ n_κ ≤ 1`. -/
theorem concaveOn_pairSiteY₀_sub_sq (hmono : Monotone ns) (hpos : ∀ i, 0 < ns i)
    (hle : ∀ i, ns i ≤ 1) :
    ConcaveOn ℝ univ fun l => pairSiteY₀ ns v₀ vs l h K₀ K - l * l / 2 := by
  have hmem : ns ∈ (Set.pi Set.univ fun _ : Fin κ => Set.Ioc (0 : ℝ) 1) := by
    simp only [Set.mem_univ_pi, Set.mem_Ioc]
    exact fun i => ⟨hpos i, hle i⟩
  refine concaveOn_of_tendsto (l := atTop) convex_univ
    (f := fun j l => pairSiteY₀ (strictApprox κ ns j) v₀ vs l h K₀ K - l * l / 2)
    (fun j => concaveOn_pairSiteY₀_sub_sq_of_strictMono (strictApprox κ ns j) v₀ vs h K₀ K
      (strictApprox_strictMono hmono hpos j) (strictApprox_pos hpos j) (strictApprox_lt_one hle j))
    fun l _ => ?_
  exact (((continuousOn_pairSiteY₀ v₀ vs l h K₀ K) ns hmem).tendsto.comp
    (tendsto_strictApprox_nhdsWithin hpos hle)).sub_const _

/-- **The tangent-line lower bound** `Y₀(0) + λ Y₀'(0) ≤ Y₀(λ)`. -/
theorem taylor_le_pairSiteY₀ (hmono : Monotone ns) (hpos : ∀ i, 0 < ns i) (hle : ∀ i, ns i ≤ 1) :
    pairSiteY₀ ns v₀ vs 0 h K₀ K + pairSiteY₀' ns v₀ vs 0 h K₀ K * lam
      ≤ pairSiteY₀ ns v₀ vs lam h K₀ K := by
  have hconv := convexOn_pairSiteY₀ ns v₀ vs h K₀ K hmono hpos hle
  have hdiff : Differentiable ℝ fun l => pairSiteY₀ ns v₀ vs l h K₀ K := fun l =>
    (hasDerivAt_pairSiteY₀ ns hpos hle v₀ vs l h K₀ K).differentiableAt
  have := hconv.add_deriv_mul_sub_le_univ hdiff 0 lam
  rwa [(hasDerivAt_pairSiteY₀ ns hpos hle v₀ vs 0 h K₀ K).deriv, sub_zero] at this

/-- **Lemma 14.6.5 as used in §14.8**: `Y₀(λ) ≤ Y₀(0) + λ Y₀'(0) + λ²/2`. -/
theorem pairSiteY₀_le_taylor (hmono : Monotone ns) (hpos : ∀ i, 0 < ns i) (hle : ∀ i, ns i ≤ 1) :
    pairSiteY₀ ns v₀ vs lam h K₀ K
      ≤ pairSiteY₀ ns v₀ vs 0 h K₀ K + pairSiteY₀' ns v₀ vs 0 h K₀ K * lam + lam ^ 2 / 2 := by
  have hconc := concaveOn_pairSiteY₀_sub_sq ns v₀ vs h K₀ K hmono hpos hle
  have hsq : ∀ l : ℝ, HasDerivAt (fun l : ℝ => l * l / 2) l l := fun l =>
    (((hasDerivAt_id l).mul (hasDerivAt_id l)).div_const 2).congr_deriv (by
      simp only [id_eq, one_mul, mul_one]
      ring)
  have hd : ∀ l, HasDerivAt (fun l => pairSiteY₀ ns v₀ vs l h K₀ K - l * l / 2)
      (pairSiteY₀' ns v₀ vs l h K₀ K - l) l :=
    fun l => (hasDerivAt_pairSiteY₀ ns hpos hle v₀ vs l h K₀ K).sub (hsq l)
  have := hconc.le_add_deriv_mul_sub (fun y _ => (hd y).differentiableAt) (mem_univ 0)
    (mem_univ lam)
  rw [(hd 0).deriv] at this
  simp only [mul_zero, zero_div, sub_zero] at this
  rw [pow_two]
  linarith

end

end SpinGlass
