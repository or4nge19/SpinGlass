/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.CoupledProp
import SpinGlass.Parisi.GuerraParisi

/-!
# Proposition 14.6.3 at `λ = 0`: the bound is `2 𝒫_k(m, q)`

Talagrand's check after (14.152): for the coupling at the level `τ` (`η = 1`, `u = q_τ`), the
field `h` and the exponents `n_p = m_p/2` for `p < τ`, `n_p = m_p` for `p ≥ τ`, the right-hand
side of (14.147) at `λ = 0` is exactly twice the Parisi functional. The three ingredients:

* **`Y₀(0) = 2 X₀`** (`pairSiteY₀_coupling_zero`, from `cascadeRec_coupling`, Lemma 14.3.6 (a)
  in raw coordinates): at `λ = 0` the one-site function is `log ch A + log ch B`, the two copies
  read the same marks below `τ` and independent ones from `τ` on, and the halved exponents turn
  the square into the factor `2`;
* the level sum (14.152) with the halved exponents is `∑_{p ≤ k} m_p (θ(q_{p+1}) − θ(q_p))`
  (`couplingLevelSum_halveBelow`);
* the diagonal defect at `ρ_{k+1} = q_{k+1}` is `ξ(1) − ξ(q_{k+1}) − (1 − q_{k+1}) ξ'(q_{k+1})`
  (`pairDiagDefect_couplingRhoSgn`); with the variance `ξ'(1) − ξ'(q_{k+1})` of the level
  `m_{k+1} = 1` absorbed in `X₀` (14.84) it is the last term of the functional
  (`coupling_rhs_zero_eq`).

Hence **Proposition 14.6.3 at `λ = 0`** bounds the constrained free energy (14.149) by
`2 𝒫_k(m, q)` (`constrainedFreeEnergy_le_two_parisiFunctional`), as it should.
-/

open MeasureTheory ProbabilityTheory Finset Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable {κ : ℕ}

/-! ### `Y₀(0) = 2 X₀` -/

/-- (14.144) at `λ = 0`: `Y_{κ+1} = log ch A + log ch B`. -/
lemma pairSiteY_zero (A B : ℝ) :
    pairSiteY 0 A B = Real.log (Real.cosh A) + Real.log (Real.cosh B) := by
  unfold pairSiteY
  rw [Real.cosh_zero, Real.sinh_zero, mul_one, mul_zero, add_zero,
    Real.log_mul (Real.cosh_pos _).ne' (Real.cosh_pos _).ne']

/-- The field of copy `1` for the coupling with `η = 1`: `y₀ 0 + ∑_p y_p 0`. -/
lemma pairSiteMark_couplingFactorSgn_one_zero {τ : ℕ} (hτ : 1 ≤ τ) (y₀ : Fin 2 → ℝ)
    (y : Fin κ → Fin 2 → ℝ) :
    pairSiteMark (couplingFactorSgn 1 τ 0) (fun p => couplingFactorSgn 1 τ (p.val + 1)) y₀ y 0
      = y₀ 0 + ∑ p : Fin κ, (couplingMap (τ - 1) p (y p 0, y p 1)).1 := by
  unfold pairSiteMark
  have h0 : ∑ j, couplingFactorSgn 1 τ 0 0 j * y₀ j = y₀ 0 := by
    simp [couplingFactorSgn, (by omega : 0 < τ)]
  rw [h0]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : p.val + 1 < τ
  · have hp' : (p : ℕ) < τ - 1 := by omega
    unfold couplingMap
    rw [ite_eq_left hp']
    simp [couplingFactorSgn, hp]
  · have hp' : ¬ (p : ℕ) < τ - 1 := by omega
    unfold couplingMap
    rw [ite_eq_right hp']
    simp [couplingFactorSgn, hp]

/-- The field of copy `2` for the coupling with `η = 1`: the coupled coordinates. -/
lemma pairSiteMark_couplingFactorSgn_one_one {τ : ℕ} (hτ : 1 ≤ τ) (y₀ : Fin 2 → ℝ)
    (y : Fin κ → Fin 2 → ℝ) :
    pairSiteMark (couplingFactorSgn 1 τ 0) (fun p => couplingFactorSgn 1 τ (p.val + 1)) y₀ y 1
      = y₀ 0 + ∑ p : Fin κ, (couplingMap (τ - 1) p (y p 0, y p 1)).2 := by
  unfold pairSiteMark
  have h0 : ∑ j, couplingFactorSgn 1 τ 0 1 j * y₀ j = y₀ 0 := by
    simp [couplingFactorSgn, (by omega : 0 < τ)]
  rw [h0]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : p.val + 1 < τ
  · have hp' : (p : ℕ) < τ - 1 := by omega
    unfold couplingMap
    rw [ite_eq_left hp']
    simp [couplingFactorSgn, hp]
  · have hp' : ¬ (p : ℕ) < τ - 1 := by omega
    unfold couplingMap
    rw [ite_eq_right hp']
    simp [couplingFactorSgn, hp]

/-- **`Y₀(0) = 2 X₀`** (Talagrand's remark after (14.152); Proposition 14.6.4 (a)): for the
coupling at the level `τ ≥ 1` with `η = 1`, the field `h` on both copies and the exponents
`n_p = m_p/2` below `τ`, `n_p = m_p` from `τ` on, `Y₀(0) = 2 𝔼_{z₀} X₁(h + z₀)`, `X₁` the
recursion of `log ch` over the levels with the exponents `m`. -/
theorem pairSiteY₀_coupling_zero (ms : Fin κ → ℝ) (hpos : ∀ i, 0 < ms i) (v₀ : ℝ≥0)
    (vs : Fin κ → ℝ≥0) (h : ℝ) {τ : ℕ} (hτ : 1 ≤ τ) :
    pairSiteY₀ (J := Fin 2) (halveBelow (τ - 1) ms) v₀ vs 0 (fun _ => h)
        (couplingFactorSgn 1 τ 0) (fun p => couplingFactorSgn 1 τ (p.val + 1))
      = 2 * ∫ a, logCoshRec κ ms vs (h + a) ∂gaussianReal 0 v₀ := by
  have hpt : ∀ y₀ : Fin 2 → ℝ, parisiRec κ (halveBelow (τ - 1) ms) (siteGaussianMarks (Fin 2) κ vs)
        (pairSiteF 0 (fun _ => h) (couplingFactorSgn 1 τ 0)
          (fun p => couplingFactorSgn 1 τ (p.val + 1)) y₀)
      = 2 * logCoshRec κ ms vs (h + y₀ 0) := by
    intro y₀
    set G : (Fin κ → ℝ) → ℝ≥0∞ := fun zs =>
      ENNReal.ofReal (Real.exp (Real.log (Real.cosh (h + y₀ 0 + ∑ p, zs p)))) with hG
    have hGm : Measurable G :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Real.measurable_log.comp
        (Real.continuous_cosh.measurable.comp (measurable_const.add
          (Finset.measurable_sum _ fun p _ => measurable_pi_apply p)))))
    set Ĝ : (Fin κ → ℝ × ℝ) → ℝ≥0∞ := fun zs =>
      G (fun i => (couplingMap (τ - 1) i (zs i)).1) * G (fun i => (couplingMap (τ - 1) i (zs i)).2)
      with hĜ
    have hĜm : Measurable Ĝ :=
      (hGm.comp (measurable_pi_lambda _ fun i => measurable_fst.comp
        ((measurable_couplingMap (τ - 1) i).comp (measurable_pi_apply i)))).mul
      (hGm.comp (measurable_pi_lambda _ fun i => measurable_snd.comp
        ((measurable_couplingMap (τ - 1) i).comp (measurable_pi_apply i))))
    -- the one-site branch function is `Ĝ` on the marks read as pairs
    have hF : (fun y : Fin κ → Fin 2 → ℝ => ENNReal.ofReal (Real.exp (pairSiteF 0 (fun _ => h)
          (couplingFactorSgn 1 τ 0) (fun p => couplingFactorSgn 1 τ (p.val + 1)) y₀ y)))
        = fun y => Ĝ (fun i => MeasurableEquiv.finTwoArrow (y i)) := by
      funext y
      rw [hĜ]
      simp only [hG]
      rw [pairSiteF, pairSiteY_zero, pairSiteMark_couplingFactorSgn_one_zero hτ,
        pairSiteMark_couplingFactorSgn_one_one hτ, Real.exp_add,
        ENNReal.ofReal_mul (Real.exp_pos _).le]
      simp only [← add_assoc]
      rfl
    have hmap : (fun p => (siteGaussianMarks (Fin 2) κ vs p).map MeasurableEquiv.finTwoArrow)
        = fun p => (gaussianReal 0 (vs p)).prod (gaussianReal 0 (vs p)) :=
      funext fun p => (measurePreserving_finTwoArrow (gaussianReal 0 (vs p))).map_eq
    have h1 : parisiRec κ (halveBelow (τ - 1) ms) (siteGaussianMarks (Fin 2) κ vs)
          (pairSiteF 0 (fun _ => h) (couplingFactorSgn 1 τ 0)
            (fun p => couplingFactorSgn 1 τ (p.val + 1)) y₀)
        = Real.log (cascadeRec κ (halveBelow (τ - 1) ms)
            (fun p => (siteGaussianMarks (Fin 2) κ vs p).map MeasurableEquiv.finTwoArrow)
            Ĝ).toReal := by
      unfold parisiRec
      rw [hF, cascadeRec_map κ _ _ (fun _ => MeasurableEquiv.finTwoArrow)
        (fun _ => MeasurableEquiv.finTwoArrow.measurable) hĜm]
    rw [h1, hmap, hĜ, cascadeRec_coupling κ (τ - 1) ms (fun p => gaussianReal 0 (vs p)) hGm hpos,
      ENNReal.toReal_pow, Real.log_pow]
    push_cast
    rfl
  unfold pairSiteY₀
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
  congr 1
  have hm : Measurable fun a : ℝ => logCoshRec κ ms vs (h + a) :=
    (measurable_logCoshRec κ ms vs).comp (measurable_const.add measurable_id)
  have hme : (Measure.pi fun _ : Fin 2 => gaussianReal 0 v₀).map (fun f => f 0)
      = gaussianReal 0 v₀ := (measurePreserving_eval _ 0).map_eq
  conv_rhs => rw [← hme]
  rw [integral_map (measurable_pi_apply 0).aemeasurable hm.aestronglyMeasurable]

/-! ### The level sum and the diagonal defect for the halved exponents -/

/-- (14.152) with the halved exponents: `∑_{p ≤ κ} m_p (θ(ρ_{p+1}) − θ(ρ_p))`. -/
lemma couplingLevelSum_halveBelow (ξ : ℝ → ℝ) (ρ : ℕ → ℝ) {τ : ℕ} (hτ : 1 ≤ τ)
    (ms : Fin κ → ℝ) :
    couplingLevelSum ξ ρ τ (halveBelow (τ - 1) ms)
      = ∑ p : Fin κ, ms p * (parisiTheta ξ (ρ (p.val + 2)) - parisiTheta ξ (ρ (p.val + 1))) := by
  unfold couplingLevelSum halveBelow
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : p.val + 1 < τ
  · rw [ite_eq_left hp, ite_eq_left (by omega : p.val < τ - 1)]
    ring
  · rw [ite_eq_right hp, ite_eq_right (by omega : ¬ p.val < τ - 1)]
    ring

/-- The diagonal defect of the coupling at the top value `ρ_{κ+1}`, for `u = η ρ_τ`:
`ξ(1) − ξ(ρ_{κ+1}) − (1 − ρ_{κ+1}) ξ'(ρ_{κ+1})`. -/
lemma pairDiagDefect_couplingRhoSgn (ξ : ℝ → ℝ) (ρ : ℕ → ℝ) (η : ℝ) {τ : ℕ} (hτ : τ ≤ κ + 1) :
    pairDiagDefect ξ (η * ρ τ) (fun l l' => couplingRhoSgn ρ η τ l l' (κ + 1))
      = ξ 1 - ξ (ρ (κ + 1)) - (1 - ρ (κ + 1)) * deriv ξ (ρ (κ + 1)) := by
  unfold pairDiagDefect couplingRhoSgn
  simp only [Fin.sum_univ_two, Fin.isValue, ↓reduceIte, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one,
    one_ne_zero, min_eq_right hτ]
  ring

/-! ### The right-hand side at `λ = 0` is `2 𝒫_k(m, q)` -/

lemma couplingVar_qExt (ξ : ℝ → ℝ) {k : ℕ} (qs : Fin (k + 1) → ℝ) (p : ℕ) :
    couplingVar ξ (qExt qs) p = parisiVar ξ qs p := rfl

/-- **The right-hand side of Proposition 14.6.3 at `λ = 0` is `2 𝒫_k(m, q)`**: with `κ = k`,
`ρ = q`, `η = 1`, `u = q_τ`, `1 ≤ τ ≤ k + 1`, the field `h` and the exponents `n_p = m_p/2` below
`τ`, `m_p` from `τ` on. -/
theorem coupling_rhs_zero_eq (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) {τ : ℕ} (hτ : 1 ≤ τ)
    (hτk : τ ≤ k + 1) (hmonoTop : deriv ξ (qExt qs (k + 1)) ≤ deriv ξ (qExt qs (k + 2))) :
    2 * Real.log 2
        + pairSiteY₀ (J := Fin 2) (halveBelow (τ - 1) ms) (couplingVar ξ (qExt qs) 0)
          (fun p => couplingVar ξ (qExt qs) (p.val + 1)) 0 (fun _ => h) (couplingFactorSgn 1 τ 0)
          (fun p => couplingFactorSgn 1 τ (p.val + 1))
        - 0 * (1 * qExt qs τ) - couplingLevelSum ξ (qExt qs) τ (halveBelow (τ - 1) ms)
        + pairDiagDefect ξ (1 * qExt qs τ) (fun l l' => couplingRhoSgn (qExt qs) 1 τ l l' (k + 1))
      = 2 * parisiFunctional ξ h ms qs := by
  rw [pairSiteY₀_coupling_zero ms hpos _ _ h hτ, couplingLevelSum_halveBelow ξ _ hτ ms,
    pairDiagDefect_couplingRhoSgn ξ (qExt qs) 1 hτk]
  simp only [couplingVar_qExt]
  unfold parisiFunctional
  rw [parisiX₀_logCosh_eq k ξ h ms qs hpos hle, Finset.sum_range_succ, Finset.sum_range,
    mExt_eq_one_of_le ms (le_refl (k + 1)), qExt_of_le qs (by omega : k + 2 ≤ k + 1 + 1)]
  have hv : (parisiVar ξ qs (k + 1) : ℝ) = deriv ξ 1 - deriv ξ (qExt qs (k + 1)) := by
    rw [parisiVar, Real.coe_toNNReal _ (sub_nonneg.2 hmonoTop),
      qExt_of_le qs (by omega : k + 2 ≤ k + 1 + 1)]
  have hs : ∑ i : Fin k, mExt ms (i.val + 1)
      * (parisiTheta ξ (qExt qs (i.val + 1 + 1)) - parisiTheta ξ (qExt qs (i.val + 1)))
      = ∑ p : Fin k,
          ms p * (parisiTheta ξ (qExt qs (p.val + 2)) - parisiTheta ξ (qExt qs (p.val + 1))) :=
    Finset.sum_congr rfl fun i _ => by rw [mExt_val_succ]
  rw [hs, hv]
  unfold parisiTheta
  ring

/-- `F₁` for `log ch` is even in the field: the marks are symmetric. -/
lemma logCoshRec_neg (ms : Fin κ → ℝ) (vs : Fin κ → ℝ≥0) (a : ℝ) :
    logCoshRec κ ms vs (-a) = logCoshRec κ ms vs a := by
  unfold logCoshRec parisiRec
  have hφ : (fun p : Fin κ => (gaussianReal 0 (vs p)).map (fun x : ℝ => -x))
      = fun p => gaussianReal 0 (vs p) := funext fun p => by rw [gaussianReal_map_neg, neg_zero]
  have hG : Measurable fun y : Fin κ → ℝ =>
      ENNReal.ofReal (Real.exp (Real.log (Real.cosh (a + ∑ p, y p)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Real.measurable_log.comp
      (Real.continuous_cosh.measurable.comp (measurable_const.add
        (Finset.measurable_sum _ fun p _ => measurable_pi_apply p)))))
  have hfun : (fun y : Fin κ → ℝ =>
        ENNReal.ofReal (Real.exp (Real.log (Real.cosh (-a + ∑ p, y p)))))
      = fun zs => ENNReal.ofReal (Real.exp (Real.log (Real.cosh (a + ∑ p, -zs p)))) := by
    funext y
    rw [show a + ∑ p, -y p = -(-a + ∑ p, y p) by rw [Finset.sum_neg_distrib]; ring, Real.cosh_neg]
  conv_rhs => rw [← hφ]
  rw [cascadeRec_map κ ms _ (fun _ => fun x : ℝ => -x) (fun _ => measurable_neg) hG, hfun]

lemma integral_logCoshRec_neg_add (ms : Fin κ → ℝ) (vs : Fin κ → ℝ≥0) (h : ℝ) (v₀ : ℝ≥0) :
    ∫ a, logCoshRec κ ms vs (-h + a) ∂gaussianReal 0 v₀
      = ∫ a, logCoshRec κ ms vs (h + a) ∂gaussianReal 0 v₀ := by
  have hm : Measurable fun a : ℝ => logCoshRec κ ms vs (-h + a) :=
    (measurable_logCoshRec κ ms vs).comp (measurable_const.add measurable_id)
  have hmap : (gaussianReal 0 v₀).map (fun x : ℝ => -x) = gaussianReal 0 v₀ := by
    rw [gaussianReal_map_neg, neg_zero]
  conv_lhs => rw [← hmap]
  rw [integral_map measurable_neg.aemeasurable hm.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  change logCoshRec κ ms vs (-h + -a) = logCoshRec κ ms vs (h + a)
  rw [← neg_add, logCoshRec_neg]

/-- The Parisi functional is even in the external field. -/
lemma parisiFunctional_neg (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) :
    parisiFunctional ξ (-h) ms qs = parisiFunctional ξ h ms qs := by
  unfold parisiFunctional
  rw [parisiX₀_logCosh_eq k ξ (-h) ms qs hpos hle, parisiX₀_logCosh_eq k ξ h ms qs hpos hle,
    integral_logCoshRec_neg_add]

/-! ### Proposition 14.6.3 at `λ = 0` -/

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]

/-- **Proposition 14.6.3 at `λ = 0`, for `u = q_τ ≥ 0`** (Talagrand's check after (14.152)): the
constrained free energy `(1/N) 𝔼 log ∑_{R_{1,2}=q_τ} e^{−H_N(σ¹) − H_N(σ²) + h ∑ᵢ (σ¹ᵢ + σ²ᵢ)}`
is at most `2 𝒫_k(m, q)`, for a convex `ξ` with `ξ'(0) = 0` (no evenness is needed for `u ≥ 0`),
`0 = q₀ ≤ q₁ ≤ ⋯ ≤ q_{k+2} = 1` along which `ξ'` is nondecreasing, `1 ≤ τ ≤ k + 1` and
`0 < m₁ ≤ ⋯ ≤ m_k ≤ 1`. -/
theorem constrainedFreeEnergy_le_two_parisiFunctional (N : ℕ) (hN : 0 < N) (ξ : ℝ → ℝ)
    (hconv : ConvexOn ℝ univ ξ) (hdiff : Differentiable ℝ ξ)
    (h0 : deriv ξ 0 = 0) {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (hmono : ∀ r, r ≤ k + 1 → deriv ξ (qExt qs r) ≤ deriv ξ (qExt qs (r + 1)))
    {τ : ℕ} (hτ : 1 ≤ τ) (hτk : τ ≤ k + 1)
    (hu : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = qExt qs τ)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ)) (h : ℝ)
    (ms : Fin k → ℝ) (hmsm : Monotone ms) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) :
    (1 / (N : ℝ)) * ∫ ω, Real.log (constrainedPairZ N (qExt qs τ) (G₀.U ω) (fun _ => -h)) ∂Pm
      ≤ 2 * parisiFunctional ξ h ms qs := by
  have htan : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ q ∈ (univ : Set ℝ), ξ q + (x - q) * deriv ξ q ≤ ξ x :=
    fun x _ q _ => by
      have := hconv.add_deriv_mul_sub_le_univ hdiff q x
      linarith [mul_comm (x - q) (deriv ξ q)]
  have hb := coupled_bound_coupling_zero N hN ξ htan h0 (qExt qs) (qExt_zero qs)
    (fun r hr => hmono r (by omega)) (η := 1) (by norm_num) (fun x => by rw [one_mul, one_mul])
    (fun x => by rw [one_mul]) (fun _ => mem_univ _) (fun _ => mem_univ _) τ (qExt qs τ) hu G₀
    (fun _ => -h) 0
    (halveBelow (τ - 1) ms) (halveBelow_monotone hmsm hpos _) (halveBelow_pos hpos _)
    (halveBelow_le_one hle _)
  have hq : (1 : ℝ) * qExt qs τ = qExt qs τ := one_mul _
  rw [← hq] at hb
  rw [coupling_rhs_zero_eq ξ (-h) ms qs hpos hle hτ hτk (hmono (k + 1) (le_refl _)),
    parisiFunctional_neg ξ h ms qs hpos hle] at hb
  rw [hq] at hb
  exact hb

end

end SpinGlass
