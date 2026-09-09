/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.GuerraFixedWeights

/-!
# Guerra's broken replica-symmetry bound (Talagrand Vol. II, Theorem 14.4.3)

Integrating the fixed-weights interpolation `guerra_fixed_weights` over the law of the
Poisson–Dirichlet cascade weights:

* the first term is `φ(0)`: by Theorem 14.2.1 (`integral_log_cascadeSum_exp_div_eq`, applied
  conditionally on the root marks `z₀`), the site factorization (14.82) (`parisiRec_sum`) and the
  absorption of the last level `m_{k+1} = 1` (14.84) (`parisiRecGauss_logCosh`),
  `φ(0) = log 2 + X₀ − (ξ'(1) − ξ'(q_{k+1}))/2` (`integral_logRatio_eq`, Talagrand's (14.85));
* the bound is computed by Proposition 14.3.3 (`lintegral_cascadeSq_mul_inv_sq`), applied
  conditionally on `(t, H_N, z₀)`: `𝔼⟨1_{(α,γ) ≥ r}⟩_t = 1 − m_r` (`integral_pairAvg`,
  Talagrand's (14.76)), so that `∫₀¹ 𝔼 b_w(t) dt = (1/2)(ξ(1) − ξ'(q_{k+1})) +
  (1/2) ∑_{r ≤ k} θ(q_{r+1})(m_{r+1} − m_r)` (`integral_intervalIntegral_guerraBound`).

Abel summation then gives **Guerra's bound** `p_N ≤ 𝒫_k(m, q)` for the Parisi functional
`parisiFunctional` (`mixedPSpinFreeEnergy_le_parisiFunctional`), for every `N`, every convex
`ξ` with `ξ'(0) = 0`, every `0 = q₀ ≤ q₁ ≤ ⋯ ≤ q_{k+1} ≤ q_{k+2} = 1` (along which `ξ'` is
monotone) and every `0 < m₁ < ⋯ < m_k < 1`.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k : ℕ)

/-! ### The recursion for `log cosh` with Gaussian marks -/

/-- `F₁` for `F_{k+1}(y₁, …, y_k) = log cosh (a + ∑ₚ yₚ)`, `yₚ ∼ N(0, vₚ)`. -/
def logCoshRec (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (a : ℝ) : ℝ :=
  parisiRec k ms (fun p => gaussianReal 0 (vs p)) (fun y => Real.log (Real.cosh (a + ∑ p, y p)))

omit N in
lemma lintegral_ofReal_cosh_add_sum_pi_gaussianReal (vs : Fin k → ℝ≥0) (a : ℝ) :
    ∫⁻ y, ENNReal.ofReal (Real.cosh (a + ∑ p, y p)) ∂Measure.pi (fun p => gaussianReal 0 (vs p))
      = ENNReal.ofReal (Real.cosh a * Real.exp (∑ p, (vs p : ℝ) / 2)) := by
  have h1 : ∀ y : Fin k → ℝ, ENNReal.ofReal (Real.cosh (a + ∑ p, y p))
      = ENNReal.ofReal (Real.exp a / 2) * ENNReal.ofReal (Real.exp (∑ p, 1 * y p))
        + ENNReal.ofReal (Real.exp (-a) / 2) * ENNReal.ofReal (Real.exp (∑ p, (-1) * y p)) := by
    intro y
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    simp_rw [one_mul, neg_one_mul, Finset.sum_neg_distrib]
    rw [Real.cosh_eq, Real.exp_add, neg_add, Real.exp_add]
    ring
  simp_rw [h1]
  have hm : ∀ c : ℝ, Measurable fun y : Fin k → ℝ => ENNReal.ofReal (Real.exp (∑ p, c * y p)) :=
    fun c => ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (Finset.measurable_sum _ fun p _ => measurable_const.mul (measurable_pi_apply p)))
  rw [lintegral_add_left ((hm 1).const_mul _), lintegral_const_mul _ (hm 1),
    lintegral_const_mul _ (hm (-1)), lintegral_ofReal_exp_sum_mul_pi_gaussianReal,
    lintegral_ofReal_exp_sum_mul_pi_gaussianReal]
  simp only [one_pow, mul_one, neg_one_sq]
  rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.cosh_eq]
  ring

omit N in
lemma measurable_ofReal_exp_log_cosh_add_sum (a : ℝ) :
    Measurable fun y : Fin k → ℝ =>
      ENNReal.ofReal (Real.exp (Real.log (Real.cosh (a + ∑ p, y p)))) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Real.measurable_log.comp
    (Real.continuous_cosh.measurable.comp (measurable_const.add
      (Finset.measurable_sum _ fun p _ => measurable_pi_apply p)))))

omit N in
lemma measurable_logCoshRec (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) :
    Measurable (logCoshRec k ms vs) := by
  unfold logCoshRec parisiRec
  refine Real.measurable_log.comp (ENNReal.measurable_toReal.comp ?_)
  have hc : Continuous fun q : ℝ × (Fin k → ℝ) =>
      ENNReal.ofReal (Real.exp (Real.log (Real.cosh (q.1 + ∑ p, q.2 p)))) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
      ((Real.continuous_cosh.comp (continuous_fst.add (continuous_finsetSum _ fun p _ =>
        (continuous_apply p).comp continuous_snd))).log fun q => (Real.cosh_pos _).ne'))
  have hu : Measurable (Function.uncurry fun (a : ℝ) (y : Fin k → ℝ) =>
      ENNReal.ofReal (Real.exp (Real.log (Real.cosh (a + ∑ p, y p))))) := by
    have := hc.measurable
    unfold Function.uncurry
    exact this
  have := measurable_cascadeRec_prod k ms (fun p => gaussianReal 0 (vs p)) hu
  exact this

omit N in
lemma logCoshRec_nonneg (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (hpos : ∀ i, 0 < ms i) (a : ℝ) :
    0 ≤ logCoshRec k ms vs a :=
  parisiRec_nonneg k ms _ (fun _ => log_cosh_nonneg _) hpos

omit N in
lemma cascadeRec_cosh_ne_top (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (hpos : ∀ i, 0 < ms i)
    (hle : ∀ i, ms i ≤ 1) (a : ℝ) :
    cascadeRec k ms (fun p => gaussianReal 0 (vs p))
      (fun y => ENNReal.ofReal (Real.exp (Real.log (Real.cosh (a + ∑ p, y p))))) ≠ ∞ := by
  refine ne_top_of_le_ne_top ?_
    (cascadeRec_le_lintegral_pi k ms _ (measurable_ofReal_exp_log_cosh_add_sum k a) hpos hle)
  simp_rw [Real.exp_log (Real.cosh_pos _)]
  rw [lintegral_ofReal_cosh_add_sum_pi_gaussianReal]
  exact ENNReal.ofReal_ne_top

omit N in
/-- Jensen's bound `F₁ ≤ log 𝔼 exp F_{k+1} = log cosh a + ∑ₚ vₚ/2 ≤ |a| + ∑ₚ vₚ/2`. -/
lemma logCoshRec_le (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (hpos : ∀ i, 0 < ms i)
    (hle : ∀ i, ms i ≤ 1) (a : ℝ) :
    logCoshRec k ms vs a ≤ |a| + ∑ p, (vs p : ℝ) / 2 := by
  unfold logCoshRec parisiRec
  have hG := measurable_ofReal_exp_log_cosh_add_sum k a
  have hJ := cascadeRec_le_lintegral_pi k ms (fun p => gaussianReal 0 (vs p)) hG hpos hle
  have hI : ∫⁻ y, ENNReal.ofReal (Real.exp (Real.log (Real.cosh (a + ∑ p, y p))))
      ∂Measure.pi (fun p => gaussianReal 0 (vs p))
      = ENNReal.ofReal (Real.cosh a * Real.exp (∑ p, (vs p : ℝ) / 2)) := by
    simp_rw [Real.exp_log (Real.cosh_pos _)]
    exact lintegral_ofReal_cosh_add_sum_pi_gaussianReal k vs a
  rw [hI] at hJ
  have hpos' := cascadeRec_pos k ms (fun p => gaussianReal 0 (vs p)) hG
    (fun _ => ENNReal.ofReal_pos.2 (Real.exp_pos _)) hpos
  calc Real.log (cascadeRec k ms (fun p => gaussianReal 0 (vs p))
        (fun y => ENNReal.ofReal (Real.exp (Real.log (Real.cosh (a + ∑ p, y p)))))).toReal
      ≤ Real.log (ENNReal.ofReal (Real.cosh a * Real.exp (∑ p, (vs p : ℝ) / 2))).toReal :=
        Real.log_le_log (ENNReal.toReal_pos hpos'.ne'
          (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hJ)) (ENNReal.toReal_mono ENNReal.ofReal_ne_top hJ)
    _ = Real.log (Real.cosh a) + ∑ p, (vs p : ℝ) / 2 := by
        rw [ENNReal.toReal_ofReal (by positivity),
          Real.log_mul (Real.cosh_pos _).ne' (Real.exp_pos _).ne', Real.log_exp]
    _ ≤ |a| + ∑ p, (vs p : ℝ) / 2 := add_le_add_right (log_cosh_le_abs a) _

omit N in
lemma integrable_logCoshRec_add (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (hpos : ∀ i, 0 < ms i)
    (hle : ∀ i, ms i ≤ 1) (h : ℝ) (v₀ : ℝ≥0) :
    Integrable (fun a => logCoshRec k ms vs (h + a)) (gaussianReal 0 v₀) := by
  have hg : Integrable (fun a : ℝ => |h + a| + ∑ p, (vs p : ℝ) / 2) (gaussianReal 0 v₀) :=
    (((integrable_const h).add (integrable_id_gaussianReal 0 v₀)).abs).add (integrable_const _)
  refine Integrable.mono' hg
    ((measurable_logCoshRec k ms vs).comp (measurable_const.add measurable_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (logCoshRec_nonneg k ms vs hpos _)]
  exact logCoshRec_le k ms vs hpos hle _

omit N in
/-- The absorption of the level `m_{k+1} = 1` (Talagrand's (14.84)) in terms of `logCoshRec`. -/
lemma logCoshRec_eq_parisiRecGauss (ξ : ℝ → ℝ) (h : ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) (a : ℝ) :
    logCoshRec k ms (fun p => parisiVar ξ qs (p.val + 1)) (h + a)
      = parisiRecGauss ξ ms qs (fun x => Real.log (Real.cosh (h + x))) a
        - (parisiVar ξ qs (k + 1) : ℝ) / 2 := by
  rw [parisiRecGauss_logCosh ξ h ms qs hpos hle a]
  unfold logCoshRec
  have : (fun p : Fin k => parisiMarks ξ qs p.castSucc)
      = fun p => gaussianReal 0 (parisiVar ξ qs (p.val + 1)) := by
    funext p
    rfl
  rw [this]
  ring

/-- The `z₀`-average of the site sum: `N` times the Gaussian average of `F₁`. -/
lemma integral_sum_logCoshRec (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (hpos : ∀ i, 0 < ms i)
    (hle : ∀ i, ms i ≤ 1) (h : ℝ) (v₀ : ℝ≥0) :
    ∫ z₀, ∑ i, logCoshRec k ms vs (h + z₀ i) ∂Measure.pi (fun _ : Fin N => gaussianReal 0 v₀)
      = N * ∫ a, logCoshRec k ms vs (h + a) ∂gaussianReal 0 v₀ := by
  have hmp : ∀ i : Fin N, MeasurePreserving (Function.eval i)
      (Measure.pi (fun _ : Fin N => gaussianReal 0 v₀)) (gaussianReal 0 v₀) := fun i =>
    measurePreserving_eval (μ := fun _ : Fin N => gaussianReal 0 v₀) i
  have hint := integrable_logCoshRec_add k ms vs hpos hle h v₀
  have hmeas : Measurable fun a : ℝ => logCoshRec k ms vs (h + a) :=
    (measurable_logCoshRec k ms vs).comp (measurable_const.add measurable_id)
  have hi : ∀ i : Fin N, ∫ z₀, logCoshRec k ms vs (h + z₀ i)
      ∂Measure.pi (fun _ : Fin N => gaussianReal 0 v₀)
      = ∫ a, logCoshRec k ms vs (h + a) ∂gaussianReal 0 v₀ := by
    intro i
    have := integral_map (hmp i).measurable.aemeasurable
      (f := fun a => logCoshRec k ms vs (h + a)) hmeas.aestronglyMeasurable
    rw [(hmp i).map_eq] at this
    exact this.symm
  rw [integral_finset_sum _ fun i _ => ((hmp i).integrable_comp hmeas.aestronglyMeasurable).2 hint]
  simp_rw [hi]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The site factorization (14.82) with the constant `log 2`**:
`F₁ = N log 2 + ∑ᵢ F₁(z_{i,0})` for `F_{k+1} = ∑ᵢ log (2 cosh (h + z_{i,0} + ∑ₚ x_{i,p}))`. -/
theorem parisiRec_coshF (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (hpos : ∀ i, 0 < ms i)
    (hle : ∀ i, ms i ≤ 1) (h : ℝ) (z₀ : Fin N → ℝ) :
    parisiRec k ms (gaussianMarks N k vs) (coshF N k h z₀)
      = N * Real.log 2 + ∑ i, logCoshRec k ms vs (h + z₀ i) := by
  have hFs : ∀ i : Fin N, Measurable fun y : Fin k → ℝ =>
      Real.log (2 * Real.cosh (h + z₀ i + ∑ p, y p)) := fun i =>
    Real.measurable_log.comp (measurable_const.mul (Real.continuous_cosh.measurable.comp
      (measurable_const.add (Finset.measurable_sum _ fun p _ => measurable_pi_apply p))))
  have hfin : ∀ i : Fin N, cascadeRec k ms (fun p => gaussianReal 0 (vs p))
      (fun y => ENNReal.ofReal (Real.exp (Real.log (2 * Real.cosh (h + z₀ i + ∑ p, y p))))) ≠ ∞ := by
    intro i
    refine ne_top_of_le_ne_top ?_ (cascadeRec_le_lintegral_pi k ms _
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hFs i))) hpos hle)
    have hm : Measurable fun y : Fin k → ℝ => ENNReal.ofReal (Real.cosh (h + z₀ i + ∑ p, y p)) :=
      ENNReal.measurable_ofReal.comp (Real.continuous_cosh.measurable.comp
        (measurable_const.add (Finset.measurable_sum _ fun p _ => measurable_pi_apply p)))
    simp_rw [Real.exp_log (by positivity : (0 : ℝ) < 2 * Real.cosh _),
      ENNReal.ofReal_mul (zero_le_two : (0 : ℝ) ≤ 2)]
    rw [lintegral_const_mul _ hm, lintegral_ofReal_cosh_add_sum_pi_gaussianReal]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have h1 := parisiRec_sum k ms (fun p _ => gaussianReal 0 (vs p))
    (Fs := fun i y => Real.log (2 * Real.cosh (h + z₀ i + ∑ p, y p))) hFs hpos hfin
  beta_reduce at h1
  have h2 : ∀ i : Fin N, parisiRec k ms (fun p => gaussianReal 0 (vs p))
      (fun y => Real.log (2 * Real.cosh (h + z₀ i + ∑ p, y p)))
      = Real.log 2 + logCoshRec k ms vs (h + z₀ i) := by
    intro i
    unfold logCoshRec
    rw [← parisiRec_const_add k ms _ (Real.measurable_log.comp (Real.continuous_cosh.measurable.comp
      (measurable_const.add (Finset.measurable_sum _ fun p _ => measurable_pi_apply p)))) hpos
      (cascadeRec_cosh_ne_top k ms vs hpos hle _)]
    congr 1
    funext y
    rw [Real.log_mul two_ne_zero (Real.cosh_pos _).ne']
  unfold coshF
  refine h1.trans ?_
  rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### The first term: `φ(0)` -/

/-- `∑_α u*_α ≤ ∑_α u*_α exp F(z_α)` since `exp F ≥ 1`. -/
lemma weightSum_le_cascadeSum_coshG (h : ℝ) (z₀ : Fin N → ℝ) (w : CascadeWeights k)
    (z : CascadeMarks (Fin N → ℝ) k) :
    weightSum k w ≤ cascadeSum k (coshG N k h z₀) (cascadeZip k (w, z)) := by
  rw [cascadeSum_cascadeZip k (measurable_coshG' N k h z₀), weightSum]
  refine ENNReal.tsum_le_tsum fun α => ?_
  calc branchWeight k w α = branchWeight k w α * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul' le_rfl (one_le_coshG N k h z₀ _)

/-- Joint measurability of the cascade sum of `exp F_{k+1}` in the weights and the marks. -/
lemma measurable_cascadeSum_coshG_prod (h : ℝ) :
    Measurable fun q : CascadeWeights k × MarksSpace N k =>
      cascadeSum k (coshG N k h q.2.1) (cascadeZip k (q.1, q.2.2)) := by
  have h1 := measurable_cascadeSum_prod k (measurable_uncurry_coshG N k h)
  have hm : Measurable fun q : CascadeWeights k × MarksSpace N k =>
      (q.2.1, cascadeZip k (q.1, q.2.2)) :=
    (measurable_fst.comp measurable_snd).prodMk
      ((measurable_cascadeZip k).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have := h1.comp hm
  simp only [Function.comp_def] at this
  exact this

/-- The integrand `log (∑_α v_α exp F(z_α))` of `φ(0)`, jointly in the weights and the marks. -/
def logRatio (h : ℝ) (q : CascadeWeights k × MarksSpace N k) : ℝ :=
  Real.log ((cascadeSum k (coshG N k h q.2.1) (cascadeZip k (q.1, q.2.2))).toReal
    / (cascadeSum k (fun _ => 1) (cascadeZip k (q.1, q.2.2))).toReal)

lemma measurable_logRatio (h : ℝ) : Measurable (logRatio N k h) := by
  unfold logRatio
  refine Real.measurable_log.comp (Measurable.div (ENNReal.measurable_toReal.comp
    (measurable_cascadeSum_coshG_prod N k h)) (ENNReal.measurable_toReal.comp ?_))
  have : Measurable fun q : CascadeWeights k × MarksSpace N k => weightSum k q.1 :=
    (measurable_weightSum k).comp measurable_fst
  simp_rw [cascadeSum_one_cascadeZip]
  exact this

/-- **Integrability of `log ∑_α v_α exp F(z_α)`** over the weights and the marks: it lies between
`0` and `∑_α v_α exp F(z_α)`, whose expectation is `𝔼 exp F_{k+1} < ∞`. -/
theorem integrable_logRatio (ms : Fin k → ℝ) (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i)
    (hlt : ∀ i, ms i < 1) (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) (h : ℝ) :
    Integrable (logRatio N k h) ((cascadeWeightsLaw k ms).prod (marksLaw N k v₀ vs)) := by
  set Pw := cascadeWeightsLaw k ms with hPw
  set Pm := marksLaw N k v₀ vs with hPm
  have hmS := measurable_cascadeSum_coshG_prod N k h
  have hmW : Measurable fun q : CascadeWeights k × MarksSpace N k => weightSum k q.1 :=
    (measurable_weightSum k).comp measurable_fst
  -- the weights are a.s. of positive finite total mass
  have haeW : ∀ᵐ q ∂Pw.prod Pm, weightSum k q.1 ≠ 0 ∧ weightSum k q.1 ≠ ∞ := by
    have hmeasW : MeasurableSet {q : CascadeWeights k × MarksSpace N k |
        weightSum k q.1 ≠ 0 ∧ weightSum k q.1 ≠ ∞} :=
      (hmW (measurableSet_singleton 0)).compl.inter (hmW (measurableSet_singleton ∞)).compl
    rw [Measure.ae_prod_iff_ae_ae hmeasW]
    filter_upwards [ae_weightSum_ne_zero_ne_top k ms hsm hpos hlt] with w hw
    exact Filter.Eventually.of_forall fun _ => hw
  -- the cascade sum is a.s. finite
  have haeS : ∀ᵐ q ∂Pw.prod Pm,
      cascadeSum k (coshG N k h q.2.1) (cascadeZip k (q.1, q.2.2)) < ∞ := by
    rw [Measure.ae_prod_iff_ae_ae (measurableSet_lt hmS measurable_const)]
    filter_upwards [ae_weightSum_ne_zero_ne_top k ms hsm hpos hlt] with w hw
    refine ae_lt_top (measurable_cascadeSum_coshG N k h w) ?_
    rw [hPm, lintegral_cascadeSum_coshG]
    exact ENNReal.mul_ne_top hw.2 (coshConst_ne_top N k v₀ vs h)
  -- the dominating function `∑_α v_α exp F(z_α)` has finite integral `𝔼 exp F_{k+1}`
  have hfin : ∫⁻ q, cascadeSum k (coshG N k h q.2.1) (cascadeZip k (q.1, q.2.2)) / weightSum k q.1
      ∂Pw.prod Pm ≠ ∞ := by
    rw [lintegral_prod _ (hmS.div hmW).aemeasurable]
    have hinner : ∀ᵐ w ∂Pw, ∫⁻ z, cascadeSum k (coshG N k h z.1) (cascadeZip k (w, z.2))
        / weightSum k w ∂Pm = coshConst N k v₀ vs h := by
      filter_upwards [ae_weightSum_ne_zero_ne_top k ms hsm hpos hlt] with w hw
      simp_rw [div_eq_mul_inv]
      rw [lintegral_mul_const _ (measurable_cascadeSum_coshG N k h w), hPm,
        lintegral_cascadeSum_coshG, mul_right_comm, ENNReal.mul_inv_cancel hw.1 hw.2, one_mul]
    rw [lintegral_congr_ae hinner, lintegral_const, measure_univ, mul_one]
    exact coshConst_ne_top N k v₀ vs h
  refine Integrable.mono' (integrable_toReal_of_lintegral_ne_top (hmS.div hmW).aemeasurable hfin)
    (measurable_logRatio N k h).aestronglyMeasurable ?_
  filter_upwards [haeW, haeS] with q hq hqS
  unfold logRatio
  rw [Real.norm_eq_abs, cascadeSum_one_cascadeZip, ENNReal.toReal_div]
  have hWpos : 0 < (weightSum k q.1).toReal := ENNReal.toReal_pos hq.1 hq.2
  have h1 : 1 ≤ (cascadeSum k (coshG N k h q.2.1) (cascadeZip k (q.1, q.2.2))).toReal
      / (weightSum k q.1).toReal := by
    rw [le_div_iff₀ hWpos, one_mul]
    exact ENNReal.toReal_mono hqS.ne (weightSum_le_cascadeSum_coshG N k h q.2.1 q.1 q.2.2)
  rw [abs_of_nonneg (Real.log_nonneg h1)]
  linarith [Real.log_le_sub_one_of_pos (zero_lt_one.trans_le h1)]

/-- **`φ(0)` (Talagrand's (14.85))**: `𝔼 log ∑_α v_α ∏ᵢ 2cosh(h + z_{i,0} + ∑ₚ z_{i,p,α})
= N (log 2 + X₀ − (ξ'(1) − ξ'(q_{k+1}))/2)`. -/
theorem integral_logRatio_eq (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (hsm : StrictMono ms)
    (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1) (qs : Fin (k + 1) → ℝ) (h : ℝ) :
    ∫ q, logRatio N k h q ∂(cascadeWeightsLaw k ms).prod
        (marksLaw N k (parisiVar ξ qs 0) fun p => parisiVar ξ qs (p.val + 1))
      = N * (Real.log 2 + parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h + x)))
          - (parisiVar ξ qs (k + 1) : ℝ) / 2) := by
  set v₀ : ℝ≥0 := parisiVar ξ qs 0 with hv₀
  set vs : Fin k → ℝ≥0 := fun p => parisiVar ξ qs (p.val + 1) with hvs
  set Pw := cascadeWeightsLaw k ms with hPw
  set P₀ : Measure (Fin N → ℝ) := Measure.pi (fun _ : Fin N => gaussianReal 0 v₀) with hP₀
  set Pmk := cascadeMarksLaw k (gaussianMarks N k vs) with hPmk
  have hle : ∀ i, ms i ≤ 1 := fun i => (hlt i).le
  have hF := integrable_logRatio N k ms hsm hpos hlt v₀ vs h
  have hFmeas := measurable_logRatio N k h
  -- swap the weights and the root marks
  have hφ : Measurable fun p : (Fin N → ℝ) × CascadeWeights k × CascadeMarks (Fin N → ℝ) k =>
      ((p.2.1, (p.1, p.2.2)) : CascadeWeights k × MarksSpace N k) :=
    (measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hswap : Pw.prod (marksLaw N k v₀ vs)
      = (P₀.prod (Pw.prod Pmk)).map
          (fun p : (Fin N → ℝ) × CascadeWeights k × CascadeMarks (Fin N → ℝ) k =>
            ((p.2.1, (p.1, p.2.2)) : CascadeWeights k × MarksSpace N k)) := by
    unfold marksLaw
    exact Measure.prod_swap_left₃ Pw P₀ Pmk
  have hF' : Integrable (fun p : (Fin N → ℝ) × CascadeWeights k × CascadeMarks (Fin N → ℝ) k =>
      logRatio N k h (p.2.1, (p.1, p.2.2))) (P₀.prod (Pw.prod Pmk)) := by
    have := (integrable_map_measure hFmeas.aestronglyMeasurable hφ.aemeasurable).1
      (hswap ▸ hF)
    exact this
  rw [hswap, integral_map hφ.aemeasurable hFmeas.aestronglyMeasurable, integral_prod _ hF']
  -- Theorem 14.2.1 conditionally on the root marks
  have hinner : ∀ z₀ : Fin N → ℝ, ∫ q', logRatio N k h (q'.1, (z₀, q'.2)) ∂Pw.prod Pmk
      = parisiRec k ms (gaussianMarks N k vs) (coshF N k h z₀) := by
    intro z₀
    have hmeasF : Measurable fun ω : CascadeSpace (Fin N → ℝ) k =>
        Real.log ((cascadeSum k (fun zs => ENNReal.ofReal (Real.exp (coshF N k h z₀ zs))) ω).toReal
          / (cascadeSum k (fun _ => 1) ω).toReal) :=
      Real.measurable_log.comp ((ENNReal.measurable_toReal.comp
        (measurable_cascadeSum k (measurable_coshG' N k h z₀))).div
          (ENNReal.measurable_toReal.comp (measurable_cascadeSum k measurable_const)))
    rw [← integral_log_cascadeSum_exp_div_eq k ms (gaussianMarks N k vs) (measurable_coshF' N k h z₀)
      hsm hpos hlt (cascadeRec_coshG_ne_top N k ms vs hpos hle h z₀), cascadeLaw_eq_map_cascadeZip,
      integral_map (measurable_cascadeZip k).aemeasurable hmeasF.aestronglyMeasurable]
    rfl
  simp_rw [hinner, parisiRec_coshF N k ms vs hpos hle h]
  have hint : Integrable (fun z₀ : Fin N → ℝ => ∑ i, logCoshRec k ms vs (h + z₀ i)) P₀ := by
    refine integrable_finset_sum _ fun i _ => ?_
    have hmp : MeasurePreserving (Function.eval i) P₀ (gaussianReal 0 v₀) :=
      measurePreserving_eval (μ := fun _ : Fin N => gaussianReal 0 v₀) i
    exact (hmp.integrable_comp ((measurable_logCoshRec k ms vs).comp
      (measurable_const.add measurable_id)).aestronglyMeasurable).2
        (integrable_logCoshRec_add k ms vs hpos hle h v₀)
  rw [integral_add (integrable_const _) hint, integral_const, probReal_univ, one_smul,
    integral_sum_logCoshRec N k ms vs hpos hle h v₀]
  -- the absorption (14.84)
  have hX : ∫ a, logCoshRec k ms vs (h + a) ∂gaussianReal 0 v₀
      = parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h + x))) - (parisiVar ξ qs (k + 1) : ℝ) / 2 := by
    have hfun : (fun a => logCoshRec k ms vs (h + a))
        = fun a => parisiRecGauss ξ ms qs (fun x => Real.log (Real.cosh (h + x))) a
          - (parisiVar ξ qs (k + 1) : ℝ) / 2 := by
      funext a
      exact logCoshRec_eq_parisiRecGauss k ξ h ms qs hpos hle a
    have hintG : Integrable (fun a => parisiRecGauss ξ ms qs (fun x => Real.log (Real.cosh (h + x))) a)
        (gaussianReal 0 v₀) := by
      have : (fun a => parisiRecGauss ξ ms qs (fun x => Real.log (Real.cosh (h + x))) a)
          = fun a => logCoshRec k ms vs (h + a) + (parisiVar ξ qs (k + 1) : ℝ) / 2 := by
        funext a
        rw [logCoshRec_eq_parisiRecGauss k ξ h ms qs hpos hle a]
        ring
      rw [this]
      exact (integrable_logCoshRec_add k ms vs hpos hle h v₀).add (integrable_const _)
    rw [hfun, integral_sub hintG (integrable_const _), integral_const, probReal_univ, one_smul]
    rfl
  rw [hX]
  ring

/-! ### The bound: Proposition 14.3.3 conditionally on `(t, H_N, z₀)` -/

/-- `𝔼_{H,z} ⟨1_{(α,γ) ≥ r}⟩_t` at fixed weights `w`. -/
def pairAvg (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : ℝ) (r : ℕ) (w : CascadeWeights k) (t : ℝ) : ℝ :=
  ∫ ω, gibbsPair N k r (hamG N k t h ω.1 ω.2.1) w ω.2.2
    ∂(gaussField N (overlapCovMatrix N ξ)).prod
      (marksLaw N k (parisiVar ξ qs 0) fun p => parisiVar ξ qs (p.val + 1))

/-- Joint measurability of the pair fraction in `(w, t)` and the disorder and marks. -/
lemma measurable_gibbsPair_hamG_wt (r : ℕ) (h : ℝ) :
    Measurable fun q : (CascadeWeights k × ℝ) × (EnergySpace N × MarksSpace N k) =>
      gibbsPair N k r (hamG N k q.1.2 h q.2.1 q.2.2.1) q.1.1 q.2.2.2 := by
  have hm : Measurable fun q : (CascadeWeights k × ℝ) × (EnergySpace N × MarksSpace N k) =>
      ((q.1.2, q.2.1, q.2.2.1), (q.1.1, q.2.2.2)) :=
    ((measurable_snd.comp measurable_fst).prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))).prodMk
      ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have := (measurable_gibbsPair_hamG N k r h).comp hm
  simp only [Function.comp_def] at this
  exact this

/-- Joint measurability of the pair fraction in the weights and the disorder and marks. -/
lemma measurable_gibbsPair_hamG_w (r : ℕ) (t h : ℝ) :
    Measurable fun q : CascadeWeights k × (EnergySpace N × MarksSpace N k) =>
      gibbsPair N k r (hamG N k t h q.2.1 q.2.2.1) q.1 q.2.2.2 := by
  have hm : Measurable fun q : CascadeWeights k × (EnergySpace N × MarksSpace N k) =>
      ((t, q.2.1, q.2.2.1), (q.1, q.2.2.2)) :=
    (measurable_const.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))).prodMk
      (measurable_fst.prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have := (measurable_gibbsPair_hamG N k r h).comp hm
  simp only [Function.comp_def] at this
  exact this

/-- The pair fraction in the disorder and the marks, at fixed `(t, H, z₀)` and the weights. -/
lemma measurable_gibbsPair_hamG_wz (r : ℕ) (t h : ℝ) (H : EnergySpace N) (z₀ : Fin N → ℝ) :
    Measurable fun q' : CascadeWeights k × CascadeMarks (Fin N → ℝ) k =>
      gibbsPair N k r (hamG N k t h H z₀) q'.1 q'.2 := by
  have := (measurable_gibbsPair_hamG N k r h).comp
    (measurable_const.prodMk measurable_id :
      Measurable fun q' : CascadeWeights k × CascadeMarks (Fin N → ℝ) k => ((t, H, z₀), q'))
  simp only [Function.comp_def] at this
  exact this

/-- **Proposition 14.3.3, integrated (Talagrand's (14.76))**: `𝔼⟨1_{(α,γ) ≥ r}⟩_t = 1 − m_r`. -/
theorem integral_pairAvg (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : ℝ) (ms : Fin k → ℝ)
    (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1) (r : ℕ) (t : ℝ) :
    ∫ w, pairAvg N k ξ qs h r w t ∂cascadeWeightsLaw k ms = 1 - mExt ms r := by
  set v₀ : ℝ≥0 := parisiVar ξ qs 0 with hv₀
  set vs : Fin k → ℝ≥0 := fun p => parisiVar ξ qs (p.val + 1) with hvs
  set Pw := cascadeWeightsLaw k ms with hPw
  set Pz := gaussField N (overlapCovMatrix N ξ) with hPz
  set P₀ : Measure (Fin N → ℝ) := Measure.pi (fun _ : Fin N => gaussianReal 0 v₀) with hP₀
  set Pmk := cascadeMarksLaw k (gaussianMarks N k vs) with hPmk
  have hle : ∀ i, ms i ≤ 1 := fun i => (hlt i).le
  have hmeas := measurable_gibbsPair_hamG_w N k r t h
  have hg : Integrable (fun q : CascadeWeights k × (EnergySpace N × MarksSpace N k) =>
      gibbsPair N k r (hamG N k t h q.2.1 q.2.2.1) q.1 q.2.2.2) (Pw.prod (Pz.prod (marksLaw N k v₀ vs))) :=
    Integrable.of_bound hmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gibbsPair_nonneg N k r _ _ _)]
      exact gibbsPair_le_one N k r (measurable_hamG' N k t h _ _) _ _)
  unfold pairAvg
  rw [← integral_prod _ hg]
  -- swap `w` with `(H, z₀)`
  have hφ : Measurable fun p : (EnergySpace N × (Fin N → ℝ)) × (CascadeWeights k × CascadeMarks (Fin N → ℝ) k) =>
      ((p.2.1, (p.1.1, (p.1.2, p.2.2))) : CascadeWeights k × (EnergySpace N × MarksSpace N k)) :=
    (measurable_fst.comp measurable_snd).prodMk ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)))
  have hswap : Pw.prod (Pz.prod (marksLaw N k v₀ vs))
      = ((Pz.prod P₀).prod (Pw.prod Pmk)).map
          (fun p : (EnergySpace N × (Fin N → ℝ)) × (CascadeWeights k × CascadeMarks (Fin N → ℝ) k) =>
            ((p.2.1, (p.1.1, (p.1.2, p.2.2))) : CascadeWeights k × (EnergySpace N × MarksSpace N k))) := by
    unfold marksLaw
    exact Measure.prod_swap_left₄ Pw Pz P₀ Pmk
  have hg' : Integrable (fun p : (EnergySpace N × (Fin N → ℝ)) × (CascadeWeights k × CascadeMarks (Fin N → ℝ) k) =>
      gibbsPair N k r (hamG N k t h p.1.1 p.1.2) p.2.1 p.2.2) ((Pz.prod P₀).prod (Pw.prod Pmk)) := by
    have := (integrable_map_measure hmeas.aestronglyMeasurable hφ.aemeasurable).1 (hswap ▸ hg)
    exact this
  rw [hswap, integral_map hφ.aemeasurable hmeas.aestronglyMeasurable, integral_prod _ hg']
  -- Proposition 14.3.3 at fixed `(H, z₀)`
  have hinner : ∀ a : EnergySpace N × (Fin N → ℝ),
      ∫ q', gibbsPair N k r (hamG N k t h a.1 a.2) q'.1 q'.2 ∂Pw.prod Pmk = 1 - mExt ms r := by
    intro a
    have hG := measurable_hamG' N k t h a.1 a.2
    have hmeasF : Measurable fun ω : CascadeSpace (Fin N → ℝ) k =>
        (cascadeSq k r (hamG N k t h a.1 a.2) ω * (cascadeSum k (hamG N k t h a.1 a.2) ω)⁻¹ ^ 2).toReal :=
      ENNReal.measurable_toReal.comp ((measurable_cascadeSq k r hG).mul
        ((measurable_cascadeSum k hG).inv.pow_const 2))
    have e1 : (∫ q', gibbsPair N k r (hamG N k t h a.1 a.2) q'.1 q'.2 ∂Pw.prod Pmk)
        = ∫ ω, (cascadeSq k r (hamG N k t h a.1 a.2) ω
            * (cascadeSum k (hamG N k t h a.1 a.2) ω)⁻¹ ^ 2).toReal
          ∂cascadeLaw k ms (gaussianMarks N k vs) := by
      rw [cascadeLaw_eq_map_cascadeZip, integral_map (measurable_cascadeZip k).aemeasurable
        hmeasF.aestronglyMeasurable]
      rfl
    rw [e1, integral_toReal hmeasF.aemeasurable.fst]
    sorry
  simp_rw [hinner]
  rw [integral_const, probReal_univ, one_smul]

end

end SpinGlass
