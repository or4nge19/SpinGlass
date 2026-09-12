/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.GuerraFixedWeights
import Common.Mathlib.Analysis.Convex.TangentLine
import Common.Mathlib.Probability.PointProcess.CascadeExponent

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
monotone) and every `0 < m₁ < ⋯ < m_k < 1`; by continuity of `𝒫_k` in the exponents
(`continuousOn_parisiFunctional`, from `ProbabilityTheory.continuousOn_parisiRec`) it extends to
nondecreasing `0 < m₁ ≤ ⋯ ≤ m_k ≤ 1` (`mixedPSpinFreeEnergy_le_parisiFunctional_of_monotone`).
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
    _ ≤ |a| + ∑ p, (vs p : ℝ) / 2 := add_le_add (log_cosh_le_abs a) le_rfl

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

omit N in
/-- `X₀` as the `z₀`-average of the recursion over the levels `1, …, k` plus the absorbed level
(14.84). -/
lemma parisiX₀_logCosh_eq (ξ : ℝ → ℝ) (h : ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) :
    parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h + x)))
      = (∫ a, logCoshRec k ms (fun p => parisiVar ξ qs (p.val + 1)) (h + a)
          ∂gaussianReal 0 (parisiVar ξ qs 0)) + (parisiVar ξ qs (k + 1) : ℝ) / 2 := by
  have hpt : ∀ a, parisiRecGauss ξ ms qs (fun x => Real.log (Real.cosh (h + x))) a
      = logCoshRec k ms (fun p => parisiVar ξ qs (p.val + 1)) (h + a)
        + (parisiVar ξ qs (k + 1) : ℝ) / 2 := by
    intro a
    rw [logCoshRec_eq_parisiRecGauss k ξ h ms qs hpos hle a]
    ring
  unfold parisiX₀
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_add (integrable_logCoshRec_add k ms _ hpos hle h _) (integrable_const _),
    integral_const, probReal_univ, one_smul]

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
    have hmap : ∫ a, logCoshRec k ms vs (h + a)
          ∂(Measure.pi (fun _ : Fin N => gaussianReal 0 v₀)).map (Function.eval i)
        = ∫ z₀, logCoshRec k ms vs (h + z₀ i)
          ∂Measure.pi (fun _ : Fin N => gaussianReal 0 v₀) :=
      integral_map (hmp i).measurable.aemeasurable hmeas.aestronglyMeasurable
    rw [(hmp i).map_eq] at hmap
    exact hmap.symm
  have hint_i : ∀ i : Fin N, Integrable (fun z₀ : Fin N → ℝ => logCoshRec k ms vs (h + z₀ i))
      (Measure.pi (fun _ : Fin N => gaussianReal 0 v₀)) := fun i =>
    ((hmp i).integrable_comp hmeas.aestronglyMeasurable).2 hint
  rw [integral_finsetSum _ fun i _ => hint_i i]
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
    have hmi : Measurable fun y : Fin k → ℝ => Real.log (Real.cosh (h + z₀ i + ∑ p, y p)) :=
      Real.measurable_log.comp (Real.continuous_cosh.measurable.comp
        (measurable_const.add (Finset.measurable_sum _ fun p _ => measurable_pi_apply p)))
    have h3 := parisiRec_const_add k ms (fun p => gaussianReal 0 (vs p))
      (F := fun y : Fin k → ℝ => Real.log (Real.cosh (h + z₀ i + ∑ p, y p))) hmi hpos
      (cascadeRec_cosh_ne_top k ms vs hpos hle (h + z₀ i)) (Real.log 2)
    have hfun : (fun y : Fin k → ℝ => Real.log (2 * Real.cosh (h + z₀ i + ∑ p, y p)))
        = fun y => Real.log 2 + Real.log (Real.cosh (h + z₀ i + ∑ p, y p)) := by
      funext y
      rw [Real.log_mul two_ne_zero (Real.cosh_pos _).ne']
    rw [hfun, h3]
    rfl
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
  have hdiv : Measurable fun q : CascadeWeights k × MarksSpace N k =>
      cascadeSum k (coshG N k h q.2.1) (cascadeZip k (q.1, q.2.2)) / weightSum k q.1 :=
    hmS.div hmW
  have hfin : ∫⁻ q, cascadeSum k (coshG N k h q.2.1) (cascadeZip k (q.1, q.2.2)) / weightSum k q.1
      ∂Pw.prod Pm ≠ ∞ := by
    rw [lintegral_prod _ hdiv.aemeasurable]
    have hinner : ∀ᵐ w ∂Pw, ∫⁻ z, cascadeSum k (coshG N k h z.1) (cascadeZip k (w, z.2))
        / weightSum k w ∂Pm = coshConst N k v₀ vs h := by
      filter_upwards [ae_weightSum_ne_zero_ne_top k ms hsm hpos hlt] with w hw
      simp_rw [div_eq_mul_inv]
      rw [lintegral_mul_const _ (measurable_cascadeSum_coshG N k h w), hPm,
        lintegral_cascadeSum_coshG, mul_right_comm, ENNReal.mul_inv_cancel hw.1 hw.2, one_mul]
    rw [lintegral_congr_ae hinner, lintegral_const, measure_univ, mul_one]
    exact coshConst_ne_top N k v₀ vs h
  refine Integrable.mono' (integrable_toReal_of_lintegral_ne_top hdiv.aemeasurable hfin)
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
    refine integrable_finsetSum _ fun i _ => ?_
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
  ∫ ω, gibbsPair k r (hamG N k t h ω.1 ω.2.1) w ω.2.2
    ∂(gaussField N (overlapCovMatrix N ξ)).prod
      (marksLaw N k (parisiVar ξ qs 0) fun p => parisiVar ξ qs (p.val + 1))

/-- Joint measurability of the pair fraction in `(w, t)` and the disorder and marks. -/
lemma measurable_gibbsPair_hamG_wt (r : ℕ) (h : ℝ) :
    Measurable fun q : (CascadeWeights k × ℝ) × (EnergySpace N × MarksSpace N k) =>
      gibbsPair k r (hamG N k q.1.2 h q.2.1 q.2.2.1) q.1.1 q.2.2.2 := by
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
      gibbsPair k r (hamG N k t h q.2.1 q.2.2.1) q.1 q.2.2.2 := by
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
      gibbsPair k r (hamG N k t h H z₀) q'.1 q'.2 := by
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
      gibbsPair k r (hamG N k t h q.2.1 q.2.2.1) q.1 q.2.2.2) (Pw.prod (Pz.prod (marksLaw N k v₀ vs))) :=
    Integrable.of_bound hmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gibbsPair_nonneg k r _ _ _)]
      exact gibbsPair_le_one k r (measurable_hamG' N k t h _ _) _ _)
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
  have hg' : Integrable (fun p : (EnergySpace N × (Fin N → ℝ))
        × (CascadeWeights k × CascadeMarks (Fin N → ℝ) k) =>
      gibbsPair k r (hamG N k t h p.1.1 p.1.2) p.2.1 p.2.2) ((Pz.prod P₀).prod (Pw.prod Pmk)) := by
    have := (integrable_map_measure hmeas.aestronglyMeasurable hφ.aemeasurable).1 (hswap ▸ hg)
    exact this
  rw [hswap, integral_map hφ.aemeasurable hmeas.aestronglyMeasurable, integral_prod _ hg']
  -- Proposition 14.3.3 at fixed `(H, z₀)`
  have hinner : ∀ a : EnergySpace N × (Fin N → ℝ),
      ∫ q', gibbsPair k r (hamG N k t h a.1 a.2) q'.1 q'.2 ∂Pw.prod Pmk = 1 - mExt ms r := fun a =>
    integral_gibbsPair_eq k ms (gaussianMarks N k vs) (measurable_hamG' N k t h a.1 a.2)
      (fun zs => hamG_pos N k t h a.1 a.2 zs) hsm hpos hlt
      (cascadeRec_hamG_ne_top N k ms vs hpos hle t h a.1 a.2) r
  simp_rw [hinner]
  rw [integral_const, probReal_univ, one_smul]

/-! ### The bound integrated over the weights -/

/-- Joint measurability of `𝔼⟨1_{(α,γ) ≥ r}⟩_t` in the weights and the time. -/
lemma measurable_pairAvg (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : ℝ) (r : ℕ) :
    Measurable fun q : CascadeWeights k × ℝ => pairAvg N k ξ qs h r q.1 q.2 := by
  unfold pairAvg
  exact ((measurable_gibbsPair_hamG_wt N k r h).stronglyMeasurable.integral_prod_right').measurable

lemma abs_pairAvg_le_one (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : ℝ) (r : ℕ)
    (w : CascadeWeights k) (t : ℝ) : |pairAvg N k ξ qs h r w t| ≤ 1 := by
  unfold pairAvg
  have := norm_integral_le_of_norm_le_const (C := 1)
    (μ := (gaussField N (overlapCovMatrix N ξ)).prod
      (marksLaw N k (parisiVar ξ qs 0) fun p => parisiVar ξ qs (p.val + 1)))
    (f := fun ω : EnergySpace N × MarksSpace N k =>
      gibbsPair k r (hamG N k t h ω.1 ω.2.1) w ω.2.2)
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gibbsPair_nonneg k r _ _ _)]
      exact gibbsPair_le_one k r (measurable_hamG' N k t h ω.1 ω.2.1) _ _)
  rwa [Real.norm_eq_abs, probReal_univ, mul_one] at this

lemma pairAvg_nonneg (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : ℝ) (r : ℕ)
    (w : CascadeWeights k) (t : ℝ) : 0 ≤ pairAvg N k ξ qs h r w t :=
  integral_nonneg fun _ => gibbsPair_nonneg k r _ _ _

/-- The pair fraction is integrable in the disorder and the marks. -/
lemma integrable_gibbsPair (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : ℝ) (r : ℕ)
    (w : CascadeWeights k) (t : ℝ) :
    Integrable (fun ω : EnergySpace N × MarksSpace N k =>
        gibbsPair k r (hamG N k t h ω.1 ω.2.1) w ω.2.2)
      ((gaussField N (overlapCovMatrix N ξ)).prod
        (marksLaw N k (parisiVar ξ qs 0) fun p => parisiVar ξ qs (p.val + 1))) :=
  Integrable.of_bound (measurable_gibbsPair_hamG' N k r t h w).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gibbsPair_nonneg k r _ _ _)]
      exact gibbsPair_le_one k r (measurable_hamG' N k t h ω.1 ω.2.1) _ _)

lemma pairAvg_le_one (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : ℝ) (r : ℕ)
    (w : CascadeWeights k) (t : ℝ) : pairAvg N k ξ qs h r w t ≤ 1 := by
  have := integral_mono (integrable_gibbsPair N k ξ qs h r w t) (integrable_const (1 : ℝ))
    fun ω => gibbsPair_le_one k r (measurable_hamG' N k t h ω.1 ω.2.1) _ _
  rwa [integral_const, probReal_univ, one_smul] at this

/-- **The bound of the interpolation in terms of the pair averages** (Talagrand's (14.75)). -/
lemma guerraBound_eq (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : ℝ) (w : CascadeWeights k) (t : ℝ) :
    guerraBound N k ξ qs h w t
      = (1 / 2) * (ξ 1 - deriv ξ (qs (Fin.last k)))
        + (1 / 2) * ∑ r ∈ Finset.range (k + 1), parisiTheta ξ (qExt qs (r + 1))
            * (pairAvg N k ξ qs h r w t - pairAvg N k ξ qs h (r + 1) w t) := by
  have hint : ∀ r : ℕ, Integrable (fun ω : EnergySpace N × MarksSpace N k =>
      gibbsPair k r (hamG N k t h ω.1 ω.2.1) w ω.2.2)
      ((gaussField N (overlapCovMatrix N ξ)).prod
        (marksLaw N k (parisiVar ξ qs 0) fun p => parisiVar ξ qs (p.val + 1))) := fun r =>
    integrable_gibbsPair N k ξ qs h r w t
  have hsum : Integrable (fun ω : EnergySpace N × MarksSpace N k =>
      ∑ r ∈ Finset.range (k + 1), parisiTheta ξ (qExt qs (r + 1))
        * (gibbsPair k r (hamG N k t h ω.1 ω.2.1) w ω.2.2
          - gibbsPair k (r + 1) (hamG N k t h ω.1 ω.2.1) w ω.2.2))
      ((gaussField N (overlapCovMatrix N ξ)).prod
        (marksLaw N k (parisiVar ξ qs 0) fun p => parisiVar ξ qs (p.val + 1))) :=
    integrable_finsetSum _ fun r _ => ((hint r).sub (hint (r + 1))).const_mul _
  have hterm : ∀ r : ℕ, Integrable (fun ω : EnergySpace N × MarksSpace N k =>
      parisiTheta ξ (qExt qs (r + 1))
        * (gibbsPair k r (hamG N k t h ω.1 ω.2.1) w ω.2.2
          - gibbsPair k (r + 1) (hamG N k t h ω.1 ω.2.1) w ω.2.2))
      ((gaussField N (overlapCovMatrix N ξ)).prod
        (marksLaw N k (parisiVar ξ qs 0) fun p => parisiVar ξ qs (p.val + 1))) := fun r =>
    ((hint r).sub (hint (r + 1))).const_mul _
  unfold guerraBound levelBound pairAvg
  rw [integral_add (integrable_const _) (hsum.const_mul _), integral_const, probReal_univ,
    one_smul, integral_const_mul, integral_finsetSum _ fun r _ => hterm r]
  congr 2
  exact Finset.sum_congr rfl fun r _ => by
    rw [integral_const_mul, integral_sub (hint r) (hint (r + 1))]

/-- **The bound of the interpolation, averaged over the cascade weights** (Talagrand's (14.79)):
`(1/2)(ξ(1) − ξ'(q_{k+1})) + (1/2) ∑_{r ≤ k} θ(q_{r+1}) (m_{r+1} − m_r)`, independently of `t`. -/
theorem integral_guerraBound (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : ℝ) (ms : Fin k → ℝ)
    (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1) (t : ℝ) :
    ∫ w, guerraBound N k ξ qs h w t ∂cascadeWeightsLaw k ms
      = (1 / 2) * (ξ 1 - deriv ξ (qs (Fin.last k)))
        + (1 / 2) * ∑ r ∈ Finset.range (k + 1), parisiTheta ξ (qExt qs (r + 1))
            * (mExt ms (r + 1) - mExt ms r) := by
  have hintP : ∀ r : ℕ, Integrable (fun w => pairAvg N k ξ qs h r w t) (cascadeWeightsLaw k ms) :=
    fun r => Integrable.of_bound
      (((measurable_pairAvg N k ξ qs h r).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable) 1
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs]; exact abs_pairAvg_le_one N k ξ qs h r w t)
  have hterm : ∀ r : ℕ, Integrable (fun w : CascadeWeights k =>
      parisiTheta ξ (qExt qs (r + 1))
        * (pairAvg N k ξ qs h r w t - pairAvg N k ξ qs h (r + 1) w t))
      (cascadeWeightsLaw k ms) := fun r => ((hintP r).sub (hintP (r + 1))).const_mul _
  have hsum : Integrable (fun w : CascadeWeights k =>
      ∑ r ∈ Finset.range (k + 1), parisiTheta ξ (qExt qs (r + 1))
        * (pairAvg N k ξ qs h r w t - pairAvg N k ξ qs h (r + 1) w t))
      (cascadeWeightsLaw k ms) := integrable_finsetSum _ fun r _ => hterm r
  simp_rw [guerraBound_eq N k ξ qs h _ t]
  rw [integral_add (integrable_const _) (hsum.const_mul _),
    integral_const, probReal_univ, one_smul, integral_const_mul,
    integral_finsetSum _ fun r _ => hterm r]
  congr 2
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [integral_const_mul, integral_sub (hintP r) (hintP (r + 1)),
    integral_pairAvg N k ξ qs h ms hsm hpos hlt r t,
    integral_pairAvg N k ξ qs h ms hsm hpos hlt (r + 1) t]
  ring

/-- The bound is jointly measurable in the weights and the time. -/
lemma measurable_guerraBound (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : ℝ) :
    Measurable fun q : CascadeWeights k × ℝ => guerraBound N k ξ qs h q.1 q.2 := by
  simp_rw [guerraBound_eq N k ξ qs h]
  exact measurable_const.add (measurable_const.mul (Finset.measurable_sum _ fun r _ =>
    measurable_const.mul ((measurable_pairAvg N k ξ qs h r).sub
      (measurable_pairAvg N k ξ qs h (r + 1)))))

lemma abs_guerraBound_le (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : ℝ) (w : CascadeWeights k)
    (t : ℝ) : |guerraBound N k ξ qs h w t|
      ≤ (1 / 2) * |ξ 1 - deriv ξ (qs (Fin.last k))|
        + (1 / 2) * ∑ r ∈ Finset.range (k + 1), |parisiTheta ξ (qExt qs (r + 1))| := by
  rw [guerraBound_eq N k ξ qs h w t]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  · rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun r _ => ?_)) (by norm_num)
    rw [abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    rw [abs_sub_le_iff]
    exact ⟨by linarith [pairAvg_nonneg N k ξ qs h (r + 1) w t, pairAvg_le_one N k ξ qs h r w t],
      by linarith [pairAvg_nonneg N k ξ qs h r w t, pairAvg_le_one N k ξ qs h (r + 1) w t]⟩

/-- **The time-integrated bound, averaged over the cascade weights.** -/
theorem integral_intervalIntegral_guerraBound (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : ℝ)
    (ms : Fin k → ℝ) (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1) :
    ∫ w, (∫ t in (0 : ℝ)..1, guerraBound N k ξ qs h w t) ∂cascadeWeightsLaw k ms
      = (1 / 2) * (ξ 1 - deriv ξ (qs (Fin.last k)))
        + (1 / 2) * ∑ r ∈ Finset.range (k + 1), parisiTheta ξ (qExt qs (r + 1))
            * (mExt ms (r + 1) - mExt ms r) := by
  have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hswap : Integrable (Function.uncurry fun (w : CascadeWeights k) (t : ℝ) =>
      guerraBound N k ξ qs h w t)
      ((cascadeWeightsLaw k ms).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
    Integrable.of_bound (measurable_guerraBound N k ξ qs h).aestronglyMeasurable
      ((1 / 2) * |ξ 1 - deriv ξ (qs (Fin.last k))|
        + (1 / 2) * ∑ r ∈ Finset.range (k + 1), |parisiTheta ξ (qExt qs (r + 1))|)
      (Filter.Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs]; exact abs_guerraBound_le N k ξ qs h q.1 q.2)
  simp_rw [intervalIntegral.integral_of_le (zero_le_one' ℝ)]
  rw [integral_integral_swap hswap]
  simp_rw [integral_guerraBound N k ξ qs h ms hsm hpos hlt]
  rw [setIntegral_const, Measure.real, Real.volume_Ioc]
  norm_num

/-! ### Abel summation and Guerra's bound -/

/-- **Guerra's broken replica-symmetry bound** (Talagrand Vol. II, Theorem 14.4.3, (14.90)):
for a convex `ξ` with `ξ'(0) = 0`, a nondecreasing `0 = q₀ ≤ q₁ ≤ ⋯ ≤ q_{k+1} ≤ q_{k+2} = 1`
along which `ξ'` is nondecreasing, and `0 < m₁ < ⋯ < m_k < 1`,

`p_N ≤ 𝒫_k(m, q) = log 2 + X₀ − (1/2) ∑_{1 ≤ p ≤ k+1} m_p (θ(q_{p+1}) − θ(q_p))`. -/
theorem mixedPSpinFreeEnergy_le_parisiFunctional (hN : 0 < N) (ξ : ℝ → ℝ)
    (hS : (overlapCovMatrix N ξ).PosSemidef) (qs : Fin (k + 1) → ℝ) (ms : Fin k → ℝ)
    (h0 : deriv ξ 0 = 0)
    (hmono : ∀ r, r ≤ k + 1 → deriv ξ (qExt qs r) ≤ deriv ξ (qExt qs (r + 1)))
    (hq01 : ∀ r, qExt qs r ∈ Set.Icc (0 : ℝ) 1)
    (htan : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ q ∈ Set.Icc (0 : ℝ) 1, ξ q + (x - q) * deriv ξ q ≤ ξ x)
    (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1) (h : ℝ) :
    mixedPSpinFreeEnergy N ξ h ≤ parisiFunctional ξ h ms qs := by
  set v₀ : ℝ≥0 := parisiVar ξ qs 0 with hv₀
  set vs : Fin k → ℝ≥0 := fun p => parisiVar ξ qs (p.val + 1) with hvs
  set Pw := cascadeWeightsLaw k ms with hPw
  set Pm := marksLaw N k v₀ vs with hPm
  set Φ : CascadeWeights k → ℝ := fun w =>
    (1 / (N : ℝ)) * ∫ z, logRatio N k h (w, z) ∂Pm with hΦ
  set Ψ : CascadeWeights k → ℝ := fun w => ∫ t in (0 : ℝ)..1, guerraBound N k ξ qs h w t with hΨ
  -- integrability of the two terms
  have hF := integrable_logRatio N k ms hsm hpos hlt v₀ vs h
  have hintΦ : Integrable Φ Pw := (hF.integral_prod_left).const_mul _
  have hintΨ : Integrable Ψ Pw := by
    have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
    have hswap : Integrable (Function.uncurry fun (w : CascadeWeights k) (t : ℝ) =>
        guerraBound N k ξ qs h w t) (Pw.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
      Integrable.of_bound (measurable_guerraBound N k ξ qs h).aestronglyMeasurable
        ((1 / 2) * |ξ 1 - deriv ξ (qs (Fin.last k))|
          + (1 / 2) * ∑ r ∈ Finset.range (k + 1), |parisiTheta ξ (qExt qs (r + 1))|)
        (Filter.Eventually.of_forall fun q => by
          rw [Real.norm_eq_abs]; exact abs_guerraBound_le N k ξ qs h q.1 q.2)
    have hIP := hswap.integral_prod_left
    refine hIP.congr (Filter.Eventually.of_forall fun w => ?_)
    change (∫ y in Set.Ioc (0 : ℝ) 1, guerraBound N k ξ qs h w y)
      = ∫ t in (0 : ℝ)..1, guerraBound N k ξ qs h w t
    exact (intervalIntegral.integral_of_le (zero_le_one' ℝ)).symm
  -- the fixed-weights bound, almost surely in the weights
  have hae : ∀ᵐ w ∂Pw, mixedPSpinFreeEnergy N ξ h ≤ Φ w + Ψ w := by
    filter_upwards [ae_weightSum_ne_zero_ne_top k ms hsm hpos hlt] with w hw
    exact guerra_fixed_weights N k hN ξ hS qs h0 hmono hq01 htan h w hw.1 hw.2
  have hle : mixedPSpinFreeEnergy N ξ h ≤ (∫ w, Φ w ∂Pw) + ∫ w, Ψ w ∂Pw := by
    have h1 := integral_mono_ae (integrable_const (mixedPSpinFreeEnergy N ξ h))
      (hintΦ.add hintΨ) hae
    rw [integral_const, probReal_univ, one_smul] at h1
    calc mixedPSpinFreeEnergy N ξ h ≤ ∫ w, (Φ + Ψ) w ∂Pw := h1
      _ = (∫ w, Φ w ∂Pw) + ∫ w, Ψ w ∂Pw := integral_add hintΦ hintΨ
  -- the first term: `φ(0)`
  have hΦint : (∫ w, Φ w ∂Pw)
      = Real.log 2 + parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h + x)))
        - (parisiVar ξ qs (k + 1) : ℝ) / 2 := by
    rw [hΦ, integral_const_mul, integral_prod _ hF |>.symm,
      integral_logRatio_eq N k ξ ms hsm hpos hlt qs h, ← mul_assoc, one_div,
      inv_mul_cancel₀ (by exact_mod_cast hN.ne' : (N : ℝ) ≠ 0), one_mul]
  -- the second term: the averaged bound
  have hΨint : (∫ w, Ψ w ∂Pw)
      = (1 / 2) * (ξ 1 - deriv ξ (qs (Fin.last k)))
        + (1 / 2) * ∑ r ∈ Finset.range (k + 1), parisiTheta ξ (qExt qs (r + 1))
            * (mExt ms (r + 1) - mExt ms r) :=
    integral_intervalIntegral_guerraBound N k ξ qs h ms hsm hpos hlt
  rw [hΦint, hΨint] at hle
  refine hle.trans (le_of_eq ?_)
  -- Talagrand's second form (14.403) of the functional
  have hqlast : qExt qs (k + 1) = qs (Fin.last k) := qExt_succ_of_lt qs (Nat.lt_succ_self k)
  have hqtop : qExt qs (k + 1 + 1) = 1 := qExt_of_le qs (by omega)
  have hv : (parisiVar ξ qs (k + 1) : ℝ) = deriv ξ 1 - deriv ξ (qs (Fin.last k)) := by
    have hnn : (0 : ℝ) ≤ deriv ξ (qExt qs (k + 1 + 1)) - deriv ξ (qExt qs (k + 1)) := by
      have := hmono (k + 1) (le_refl (k + 1))
      linarith
    rw [parisiVar, Real.coe_toNNReal _ hnn, hqtop, hqlast]
  rw [parisiFunctional_eq_theta_sum ξ h ms qs, hv, parisiTheta]
  ring

/-- **Guerra's broken replica-symmetry bound under Talagrand's own hypotheses**
(Vol. II, Theorem 14.4.3): for a convex differentiable `ξ` with `ξ'(0) = 0`, a nondecreasing
`q₁ ≤ ⋯ ≤ q_{k+1}` in `[0, 1]` and `0 < m₁ < ⋯ < m_k < 1`, `p_N ≤ 𝒫_k(m, q)`. -/
theorem mixedPSpinFreeEnergy_le_parisiFunctional_of_convexOn (hN : 0 < N) (ξ : ℝ → ℝ)
    (hS : (overlapCovMatrix N ξ).PosSemidef) (hconv : ConvexOn ℝ Set.univ ξ)
    (hdiff : Differentiable ℝ ξ) (h0 : deriv ξ 0 = 0) (qs : Fin (k + 1) → ℝ)
    (hqmono : Monotone qs) (hq0 : 0 ≤ qs 0) (hq1 : qs (Fin.last k) ≤ 1) (ms : Fin k → ℝ)
    (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1) (h : ℝ) :
    mixedPSpinFreeEnergy N ξ h ≤ parisiFunctional ξ h ms qs := by
  have hderiv : Monotone (deriv ξ) :=
    monotoneOn_univ.1 (hconv.monotoneOn_deriv fun x _ => hdiff x)
  refine mixedPSpinFreeEnergy_le_parisiFunctional N k hN ξ hS qs ms h0
    (fun r hr => hderiv (qExt_le_succ hqmono hq0 hq1 hr))
    (fun r => qExt_mem_Icc hqmono hq0 hq1 r) (fun x _ q _ => ?_) hsm hpos hlt h
  rw [mul_comm (x - q) (deriv ξ q)]
  exact hconv.add_deriv_mul_sub_le_univ hdiff q x

/-- **Guerra's bound for the Sherrington–Kirkpatrick model at every level `k`**: for
`0 ≤ q₁ ≤ ⋯ ≤ q_{k+1} ≤ 1` and `0 < m₁ < ⋯ < m_k < 1`,
`p_N(β, h) ≤ 𝒫_k(m, q)` for the profile `ξ(x) = β²x²/2`. At `k = 0` this is the
replica-symmetric bound of Vol. I, Theorem 1.3.7. -/
theorem skFreeEnergy_le_parisiFunctional (hN : 0 < N) (β h : ℝ) (qs : Fin (k + 1) → ℝ)
    (hqmono : Monotone qs) (hq0 : 0 ≤ qs 0) (hq1 : qs (Fin.last k) ≤ 1) (ms : Fin k → ℝ)
    (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1) :
    skFreeEnergy N β h ≤ parisiFunctional (skCovXi β) h ms qs := by
  change mixedPSpinFreeEnergy N (skCovXi β) h ≤ _
  exact mixedPSpinFreeEnergy_le_parisiFunctional_of_convexOn N k hN (skCovXi β)
    (posSemidef_skCovMatrix N β) (convexOn_univ_skCovXi β) (differentiable_skCovXi β)
    (deriv_skCovXi_zero β) qs hqmono hq0 hq1 ms hsm hpos hlt h

/-- **The replica-symmetric bound at finite `N` is the case `k = 0`** of Guerra's bound: for
`0 ≤ q ≤ 1`, `p_N(β, h) ≤ 𝔼 log (2 cosh (β √q z + h)) + β²(1-q)²/4`. This is Vol. I,
Theorem 1.3.7 (there stated in the limit). -/
theorem skFreeEnergy_le_rs_bound (hN : 0 < N) (β h q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    skFreeEnergy N β h
      ≤ (∫ z : ℝ, Real.log (2 * Real.cosh (β * Real.sqrt q * z + h)) ∂gaussianReal 0 1)
        + β ^ 2 / 4 * (1 - q) ^ 2 := by
  have hmono1 : Monotone (![q] : Fin (0 + 1) → ℝ) := by
    intro a b _
    fin_cases a
    fin_cases b
    simp
  have hsm0 : StrictMono (![] : Fin 0 → ℝ) := fun a _ _ => a.elim0
  have hmain := skFreeEnergy_le_parisiFunctional N 0 hN β h ![q] hmono1
    (by simpa using hq0) (by simpa using hq1) ![] hsm0 (fun i => i.elim0) (fun i => i.elim0)
  rwa [parisiFunctional_skCovXi_zero β h q hq0 hq1] at hmain

/-! ### Nondecreasing exponents `0 < m₁ ≤ ⋯ ≤ m_k ≤ 1` -/

omit N in
/-- `ms ↦ 𝔼_a F₁(h + a)` is continuous in the exponents on `(0, 1]^k`: dominated convergence with
the uniform bound `0 ≤ F₁ ≤ |h + a| + ∑ v_p/2` and `continuousOn_parisiRec`. -/
theorem continuousOn_integral_logCoshRec_add (vs : Fin k → ℝ≥0) (h : ℝ) (v₀ : ℝ≥0) :
    ContinuousOn (fun ms : Fin k → ℝ => ∫ a, logCoshRec k ms vs (h + a) ∂gaussianReal 0 v₀)
      (Set.pi Set.univ fun _ => Set.Ioc (0 : ℝ) 1) := by
  intro ms₀ hmem
  have hg : Integrable (fun a : ℝ => |h + a| + ∑ p, (vs p : ℝ) / 2) (gaussianReal 0 v₀) :=
    (((integrable_const h).add (integrable_id_gaussianReal 0 v₀)).abs).add (integrable_const _)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun a => |h + a| + ∑ p, (vs p : ℝ) / 2)
    (Filter.Eventually.of_forall fun ms => ((measurable_logCoshRec k ms vs).comp
      (measurable_const.add measurable_id)).aestronglyMeasurable)
    (eventually_nhdsWithin_of_forall fun ms hms => Filter.Eventually.of_forall fun a => ?_) hg
    (Filter.Eventually.of_forall fun a => ?_)
  · simp only [Set.mem_univ_pi, Set.mem_Ioc] at hms
    rw [Real.norm_eq_abs, abs_of_nonneg (logCoshRec_nonneg k ms vs (fun i => (hms i).1) _)]
    exact logCoshRec_le k ms vs (fun i => (hms i).1) (fun i => (hms i).2) _
  · have hF : Measurable fun y : Fin k → ℝ => Real.log (Real.cosh (h + a + ∑ p, y p)) :=
      Real.measurable_log.comp (Real.continuous_cosh.measurable.comp
        (measurable_const.add (Finset.measurable_sum Finset.univ fun p _ => measurable_pi_apply p)))
    have hfin : ∫⁻ y, ENNReal.ofReal (Real.exp (Real.log (Real.cosh (h + a + ∑ p, y p))))
        ∂Measure.pi (fun p => gaussianReal 0 (vs p)) ≠ ∞ := by
      simp_rw [Real.exp_log (Real.cosh_pos _)]
      rw [lintegral_ofReal_cosh_add_sum_pi_gaussianReal k vs (h + a)]
      exact ENNReal.ofReal_ne_top
    exact (continuousOn_parisiRec k (fun p => gaussianReal 0 (vs p)) hF hfin ms₀ hmem).tendsto

omit N in
lemma continuous_mExt (r : ℕ) : Continuous fun ms : Fin k → ℝ => mExt ms r := by
  by_cases h1 : r = 0
  · simp only [mExt, ite_eq_left h1]
    exact continuous_const
  · by_cases h2 : r - 1 < k
    · simp only [mExt, ite_eq_right h1, dite_eq_left h2]
      exact continuous_apply _
    · simp only [mExt, ite_eq_right h1, dite_eq_right h2]
      exact continuous_const

omit N in
/-- **The Parisi functional is continuous in the exponents on `(0, 1]^k`.** -/
theorem continuousOn_parisiFunctional (ξ : ℝ → ℝ) (h : ℝ) (qs : Fin (k + 1) → ℝ) :
    ContinuousOn (fun ms : Fin k → ℝ => parisiFunctional ξ h ms qs)
      (Set.pi Set.univ fun _ => Set.Ioc (0 : ℝ) 1) := by
  have h1 := continuousOn_integral_logCoshRec_add k (fun p => parisiVar ξ qs (p.val + 1)) h
    (parisiVar ξ qs 0)
  have h2 : Continuous fun ms : Fin k → ℝ => ∑ p ∈ Finset.range (k + 1),
      mExt ms (p + 1) * (parisiTheta ξ (qExt qs (p + 2)) - parisiTheta ξ (qExt qs (p + 1))) :=
    continuous_finsetSum _ fun p _ => (continuous_mExt k (p + 1)).mul continuous_const
  refine (((continuousOn_const (c := Real.log 2)).add
    (h1.add (continuousOn_const (c := (parisiVar ξ qs (k + 1) : ℝ) / 2)))).sub
    ((continuousOn_const (c := (1 / 2 : ℝ))).mul h2.continuousOn)).congr fun ms hms => ?_
  simp only [Set.mem_univ_pi, Set.mem_Ioc] at hms
  unfold parisiFunctional
  rw [parisiX₀_logCosh_eq k ξ h ms qs (fun i => (hms i).1) (fun i => (hms i).2)]
  rfl

/-- **Guerra's bound for nondecreasing exponents `0 < m₁ ≤ ⋯ ≤ m_k ≤ 1`**: both sides are
continuous in the exponents and the strictly increasing tuples are dense (Talagrand's remark
after (14.145)). -/
theorem mixedPSpinFreeEnergy_le_parisiFunctional_of_monotone (hN : 0 < N) (ξ : ℝ → ℝ)
    (hS : (overlapCovMatrix N ξ).PosSemidef) (qs : Fin (k + 1) → ℝ) (ms : Fin k → ℝ)
    (h0 : deriv ξ 0 = 0)
    (hmono : ∀ r, r ≤ k + 1 → deriv ξ (qExt qs r) ≤ deriv ξ (qExt qs (r + 1)))
    (hq01 : ∀ r, qExt qs r ∈ Set.Icc (0 : ℝ) 1)
    (htan : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ q ∈ Set.Icc (0 : ℝ) 1, ξ q + (x - q) * deriv ξ q ≤ ξ x)
    (hmsm : Monotone ms) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) (h : ℝ) :
    mixedPSpinFreeEnergy N ξ h ≤ parisiFunctional ξ h ms qs :=
  le_of_forall_strictMono_le (f := fun _ => mixedPSpinFreeEnergy N ξ h) continuousOn_const
    (continuousOn_parisiFunctional k ξ h qs)
    (fun ms hsm hpos hlt => mixedPSpinFreeEnergy_le_parisiFunctional N k hN ξ hS qs ms h0 hmono
      hq01 htan hsm hpos hlt h) hmsm hpos hle

/-- **Guerra's bound under Talagrand's own hypotheses, for nondecreasing exponents
`0 < m₁ ≤ ⋯ ≤ m_k ≤ 1`.** -/
theorem mixedPSpinFreeEnergy_le_parisiFunctional_of_convexOn_of_monotone (hN : 0 < N)
    (ξ : ℝ → ℝ) (hS : (overlapCovMatrix N ξ).PosSemidef) (hconv : ConvexOn ℝ Set.univ ξ)
    (hdiff : Differentiable ℝ ξ) (h0 : deriv ξ 0 = 0) (qs : Fin (k + 1) → ℝ)
    (hqmono : Monotone qs) (hq0 : 0 ≤ qs 0) (hq1 : qs (Fin.last k) ≤ 1) (ms : Fin k → ℝ)
    (hmsm : Monotone ms) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) (h : ℝ) :
    mixedPSpinFreeEnergy N ξ h ≤ parisiFunctional ξ h ms qs :=
  le_of_forall_strictMono_le (f := fun _ => mixedPSpinFreeEnergy N ξ h) continuousOn_const
    (continuousOn_parisiFunctional k ξ h qs)
    (fun ms hsm hpos hlt => mixedPSpinFreeEnergy_le_parisiFunctional_of_convexOn N k hN ξ hS
      hconv hdiff h0 qs hqmono hq0 hq1 ms hsm hpos hlt h) hmsm hpos hle

/-- **Guerra's bound for the SK model, for nondecreasing exponents `0 < m₁ ≤ ⋯ ≤ m_k ≤ 1`.** -/
theorem skFreeEnergy_le_parisiFunctional_of_monotone (hN : 0 < N) (β h : ℝ)
    (qs : Fin (k + 1) → ℝ) (hqmono : Monotone qs) (hq0 : 0 ≤ qs 0) (hq1 : qs (Fin.last k) ≤ 1)
    (ms : Fin k → ℝ) (hmsm : Monotone ms) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) :
    skFreeEnergy N β h ≤ parisiFunctional (skCovXi β) h ms qs := by
  change mixedPSpinFreeEnergy N (skCovXi β) h ≤ _
  exact mixedPSpinFreeEnergy_le_parisiFunctional_of_convexOn_of_monotone N k hN (skCovXi β)
    (posSemidef_skCovMatrix N β) (convexOn_univ_skCovXi β) (differentiable_skCovXi β)
    (deriv_skCovXi_zero β) qs hqmono hq0 hq1 ms hmsm hpos hle h

end

end SpinGlass
