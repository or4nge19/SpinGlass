/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.PairLevels

/-!
# Guerra's interpolation for the whole cascade, at fixed weights

Letting `M → ∞` in the interpolation for the truncated tree (`guerra_truncated`): for every
sample `w` of the cascade weights with total weight `W = ∑_α u*_α ∈ (0, ∞)`,

`p_N ≤ (1/N) 𝔼_z log (∑_α u*_α exp F(z_α) / ∑_α u*_α) + ∫₀¹ b_w(t) dt`,

where `exp F(z_α) = ∏ᵢ 2 cosh (h + z_{i,0} + ∑ₚ z_{i,p,α})` and `b_w` is the bound `guerraBound`
for the whole cascade (`guerra_fixed_weights`). The truncated sums `∑_{α ∈ A_M}` increase to the
cascade sums, so the `log` of the truncated partition function is bounded by the `log` of the
full one (both integrable: they lie between the single term `u*_{α₀} ≥ c > 0` and the integrable
cascade sum), the truncated total weights converge to `W`, and the truncated bounds converge by
dominated convergence (`tendsto_integral_guerraTruncBound`).
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k : ℕ)

/-! ### Gaussian integrals of `exp F_{k+1}` -/

lemma lintegral_ofReal_exp_add_gaussianMarks (vs : Fin k → ℝ≥0) (a : ℝ) (B : Fin k → Fin N → ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (a + ∑ p, ∑ i, B p i * x p i)) ∂Measure.pi (gaussianMarks N k vs)
      = ENNReal.ofReal (Real.exp a)
        * ENNReal.ofReal (Real.exp (∑ p, ∑ i, (vs p : ℝ) * B p i ^ 2 / 2)) := by
  have hm : Measurable fun x : Fin k → Fin N → ℝ =>
      ENNReal.ofReal (Real.exp (∑ p, ∑ i, B p i * x p i)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Finset.measurable_sum _ fun p _ =>
      Finset.measurable_sum _ fun i _ => measurable_const.mul
        ((measurable_pi_apply i).comp (measurable_pi_apply p))))
  simp_rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [lintegral_const_mul _ hm]
  unfold gaussianMarks
  rw [lintegral_ofReal_exp_sum_mul_pi_pi_gaussianReal]

lemma lintegral_ofReal_exp_add_pi_gaussianReal (v₀ : ℝ≥0) (a : ℝ) (c : Fin N → ℝ) :
    ∫⁻ z₀, ENNReal.ofReal (Real.exp (a + ∑ i, c i * z₀ i))
        ∂Measure.pi (fun _ : Fin N => gaussianReal 0 v₀)
      = ENNReal.ofReal (Real.exp a) * ENNReal.ofReal (Real.exp (∑ i, (v₀ : ℝ) * c i ^ 2 / 2)) := by
  have hm : Measurable fun z₀ : Fin N → ℝ => ENNReal.ofReal (Real.exp (∑ i, c i * z₀ i)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Finset.measurable_sum _ fun i _ =>
      measurable_const.mul (measurable_pi_apply i)))
  simp_rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [lintegral_const_mul _ hm]
  exact congrArg _ (lintegral_ofReal_exp_sum_mul_pi_gaussianReal (fun _ : Fin N => v₀) c)

/-- `𝔼 exp F_{k+1} = 𝔼_{z₀} ∫ ∏ᵢ 2 cosh (h + z_{i,0} + ∑ₚ x_{i,p}) dμ^{⊗k}`. -/
def coshConst (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) (h : ℝ) : ℝ≥0∞ :=
  ∫⁻ z₀, ∫⁻ x, coshG N k h z₀ x ∂Measure.pi (gaussianMarks N k vs)
    ∂Measure.pi (fun _ : Fin N => gaussianReal 0 v₀)

/-- Talagrand's hypothesis (14.4) for `F_{k+1}`: `𝔼 exp F_{k+1} < ∞`. -/
lemma coshConst_ne_top (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) (h : ℝ) : coshConst N k v₀ vs h ≠ ∞ := by
  unfold coshConst
  have hin : ∀ z₀ : Fin N → ℝ, ∫⁻ x, coshG N k h z₀ x ∂Measure.pi (gaussianMarks N k vs)
      = ∑ σ : Config N, ENNReal.ofReal (Real.exp (∑ i, (h + z₀ i) * isingSpin (σ i)))
        * ENNReal.ofReal (Real.exp (∑ p, ∑ i, (vs p : ℝ) * isingSpin (σ i) ^ 2 / 2)) := by
    intro z₀
    simp_rw [coshG_eq_sum]
    have hm : ∀ σ : Config N, Measurable fun x : Fin k → Fin N → ℝ =>
        ENNReal.ofReal (Real.exp ((∑ i, (h + z₀ i) * isingSpin (σ i))
          + ∑ p, ∑ i, isingSpin (σ i) * x p i)) := fun σ =>
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.add
        (Finset.measurable_sum _ fun p _ => Finset.measurable_sum _ fun i _ => measurable_const.mul
          ((measurable_pi_apply i).comp (measurable_pi_apply p)))))
    rw [lintegral_finsetSum _ fun σ _ => hm σ]
    exact Finset.sum_congr rfl fun σ _ => lintegral_ofReal_exp_add_gaussianMarks N k vs _ _
  simp_rw [hin]
  have hm' : ∀ σ : Config N, Measurable fun z₀ : Fin N → ℝ =>
      ENNReal.ofReal (Real.exp (∑ i, (h + z₀ i) * isingSpin (σ i)))
        * ENNReal.ofReal (Real.exp (∑ p, ∑ i, (vs p : ℝ) * isingSpin (σ i) ^ 2 / 2)) := fun σ =>
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Finset.measurable_sum _ fun i _ =>
      (measurable_const.add (measurable_pi_apply i)).mul measurable_const))).mul measurable_const
  rw [lintegral_finsetSum _ fun σ _ => hm' σ]
  refine ENNReal.sum_ne_top.2 fun σ _ => ?_
  have hmz : Measurable fun z₀ : Fin N → ℝ =>
      ENNReal.ofReal (Real.exp (∑ i, (h + z₀ i) * isingSpin (σ i))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (Finset.measurable_sum _ fun i _ => (measurable_const.add (measurable_pi_apply i)).mul
        measurable_const))
  rw [lintegral_mul_const _ hmz]
  have hsplit : ∀ z₀ : Fin N → ℝ, ∑ i, (h + z₀ i) * isingSpin (σ i)
      = (∑ i, h * isingSpin (σ i)) + ∑ i, isingSpin (σ i) * z₀ i := by
    intro z₀
    simp_rw [add_mul, Finset.sum_add_distrib, mul_comm (z₀ _)]
  simp_rw [hsplit]
  rw [lintegral_ofReal_exp_add_pi_gaussianReal]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    ENNReal.ofReal_ne_top

lemma measurable_uncurry_coshG (h : ℝ) :
    Measurable (Function.uncurry fun z₀ : Fin N → ℝ => coshG N k h z₀) := by
  have := measurable_coshG N k h
  unfold Function.uncurry
  exact this

/-- Measurability of the cascade sum of `exp F_{k+1}` in the marks. -/
lemma measurable_cascadeSum_coshG (h : ℝ) (w : CascadeWeights k) :
    Measurable fun z : MarksSpace N k => cascadeSum k (coshG N k h z.1) (cascadeZip k (w, z.2)) := by
  have h1 := measurable_cascadeSum_prod k (measurable_uncurry_coshG N k h)
  have hm : Measurable fun z : MarksSpace N k => (z.1, cascadeZip k (w, z.2)) :=
    measurable_fst.prodMk ((measurable_cascadeZip k).comp (measurable_const.prodMk measurable_snd))
  have := h1.comp hm
  simp only [Function.comp_def] at this
  exact this

/-- **The marks average of the cascade sum of `exp F_{k+1}` at fixed weights**: `W · 𝔼 exp F_{k+1}`. -/
lemma lintegral_cascadeSum_coshG (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) (h : ℝ) (w : CascadeWeights k) :
    ∫⁻ z, cascadeSum k (coshG N k h z.1) (cascadeZip k (w, z.2)) ∂marksLaw N k v₀ vs
      = weightSum k w * coshConst N k v₀ vs h := by
  unfold marksLaw coshConst
  rw [lintegral_prod _ (measurable_cascadeSum_coshG N k h w).aemeasurable]
  have hin : ∀ z₀ : Fin N → ℝ, ∫⁻ z₂, cascadeSum k (coshG N k h z₀) (cascadeZip k (w, z₂))
      ∂cascadeMarksLaw k (gaussianMarks N k vs)
      = weightSum k w * ∫⁻ x, coshG N k h z₀ x ∂Measure.pi (gaussianMarks N k vs) := fun z₀ =>
    lintegral_cascadeSum_cascadeZip k (gaussianMarks N k vs) w (measurable_coshG' N k h z₀)
  simp_rw [hin]
  have hmz : Measurable fun z₀ : Fin N → ℝ =>
      ∫⁻ x, coshG N k h z₀ x ∂Measure.pi (gaussianMarks N k vs) := by
    have := (measurable_uncurry_coshG N k h).lintegral_prod_right'
      (ν := Measure.pi (gaussianMarks N k vs))
    simpa only [Function.uncurry_apply_pair] using this
  rw [lintegral_const_mul _ hmz]

/-! ### The truncated cascade sums -/

/-- `S^M = ∑_{α ∈ A_M} u*_α G(z_α)`: the cascade sum restricted to the truncated tree. -/
def truncSum (M : ℕ) (w : CascadeWeights k) (G : (Fin k → Fin N → ℝ) → ℝ≥0∞)
    (z : CascadeMarks (Fin N → ℝ) k) : ℝ≥0∞ :=
  ∑ α : TruncBranch k M, branchWeight k w (truncBranchCoe k M α)
    * G (branchMarks k z (truncBranchCoe k M α))

lemma truncSum_le_cascadeSum (M : ℕ) (w : CascadeWeights k) {G : (Fin k → Fin N → ℝ) → ℝ≥0∞}
    (hG : Measurable G) (z : CascadeMarks (Fin N → ℝ) k) :
    truncSum N k M w G z ≤ cascadeSum k G (cascadeZip k (w, z)) := by
  rw [cascadeSum_cascadeZip k hG, truncSum,
    sum_truncBranch_eq k M fun α => branchWeight k w α * G (branchMarks k z α)]
  exact ENNReal.sum_le_tsum _

lemma le_truncSum_of_mem (M : ℕ) (w : CascadeWeights k) (G : (Fin k → Fin N → ℝ) → ℝ≥0∞)
    (z : CascadeMarks (Fin N → ℝ) k) {α₀ : Fin k → ℕ × ℕ} (hmem : α₀ ∈ truncFinset k M) :
    branchWeight k w α₀ * G (branchMarks k z α₀) ≤ truncSum N k M w G z := by
  rw [truncSum, sum_truncBranch_eq k M fun α => branchWeight k w α * G (branchMarks k z α)]
  exact Finset.single_le_sum (f := fun α => branchWeight k w α * G (branchMarks k z α))
    (fun _ _ => bot_le) hmem

lemma le_cascadeSum_cascadeZip (w : CascadeWeights k) {G : (Fin k → Fin N → ℝ) → ℝ≥0∞}
    (hG : Measurable G) (z : CascadeMarks (Fin N → ℝ) k) (α₀ : Fin k → ℕ × ℕ) :
    branchWeight k w α₀ * G (branchMarks k z α₀) ≤ cascadeSum k G (cascadeZip k (w, z)) := by
  rw [cascadeSum_cascadeZip k hG]
  exact ENNReal.le_tsum α₀

lemma one_le_coshG (h : ℝ) (z₀ : Fin N → ℝ) (x : Fin k → Fin N → ℝ) : 1 ≤ coshG N k h z₀ x := by
  rw [coshG_eq]
  refine ENNReal.one_le_ofReal.2 ?_
  calc (1 : ℝ) = ∏ _i : Fin N, (1 : ℝ) := by simp
    _ ≤ ∏ i, (2 * Real.cosh (h + z₀ i + ∑ p, x p i)) :=
      Finset.prod_le_prod (fun _ _ => zero_le_one) fun i _ =>
        one_le_two.trans (le_mul_of_one_le_right two_pos.le (Real.one_le_cosh _))

/-- The truncated partition function of the Ising site factorization is the truncated cascade sum
of `exp F_{k+1}`. -/
lemma sum_truncWt_mul_prod_eq (M : ℕ) (w : CascadeWeights k) (hw : ∀ α, branchWeight k w α ≠ ∞)
    (h : ℝ) (z : MarksSpace N k) :
    ∑ α, truncWt k M w α * ∏ i, (2 * Real.cosh (h + treeMark N k M z α i))
      = (truncSum N k M w (coshG N k h z.1) z.2).toReal := by
  unfold truncSum
  rw [ENNReal.toReal_sum fun α _ => ENNReal.mul_ne_top (hw _) (by rw [coshG]; exact ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [ENNReal.toReal_mul, ← ofReal_prod_two_cosh_treeMark, ENNReal.toReal_ofReal
    (Finset.prod_nonneg fun i _ => by positivity)]
  rfl

omit N in
/-- A branch of positive weight lies in all sufficiently large truncated trees. -/
lemma exists_mem_truncFinset (w : CascadeWeights k) (hW0 : weightSum k w ≠ 0) :
    ∃ α₀ : Fin k → ℕ × ℕ, branchWeight k w α₀ ≠ 0 ∧ ∃ M₀, ∀ M, M₀ ≤ M → α₀ ∈ truncFinset k M := by
  obtain ⟨α₀, hα₀⟩ : ∃ α₀, branchWeight k w α₀ ≠ 0 := by
    by_contra hcon
    exact hW0 (ENNReal.tsum_eq_zero.2 fun α => by simpa using fun h => hcon ⟨α, h⟩)
  obtain ⟨M₀, hM₀⟩ := exists_subset_truncFinset k {α₀}
  exact ⟨α₀, hα₀, M₀, fun M hM => truncFinset_mono k hM (hM₀ (Finset.mem_singleton_self _))⟩

omit N in
lemma truncWt_ne_zero_of_mem {M : ℕ} (w : CascadeWeights k) (hW : weightSum k w ≠ ∞)
    {α₀ : Fin k → ℕ × ℕ} (hα₀ : branchWeight k w α₀ ≠ 0) (hmem : α₀ ∈ truncFinset k M) :
    ∃ β : TruncBranch k M, truncWt k M w β ≠ 0 := by
  obtain ⟨β, _, hβ⟩ := Finset.mem_map.1 hmem
  refine ⟨β, ?_⟩
  unfold truncWt
  rw [show truncBranchCoe k M β = α₀ from hβ]
  exact ENNReal.toReal_ne_zero.2 ⟨hα₀, ne_top_of_le_ne_top hW (branchWeight_le_weightSum k w α₀)⟩

omit N k in
/-- `|log x| ≤ x + |log c|` for `0 < c ≤ x`. -/
lemma abs_log_le_add_abs_log {c x : ℝ} (hc : 0 < c) (hcx : c ≤ x) : |Real.log x| ≤ x + |Real.log c| := by
  refine abs_le.2 ⟨?_, ?_⟩
  · linarith [Real.log_le_log hc hcx, neg_abs_le (Real.log c)]
  · linarith [Real.log_le_sub_one_of_pos (hc.trans_le hcx), abs_nonneg (Real.log c)]

/-! ### The interpolation at fixed weights -/

/-- **Guerra's interpolation for the whole cascade, at fixed weights of positive finite total
mass** (Talagrand Vol. II, Lemma 14.4.1 with (14.79)–(14.80), integrated over `t`, for the
cascade weights `u*_α` and the marks `z`):
`p_N ≤ (1/N) 𝔼_z log (∑_α u*_α ∏ᵢ 2cosh(h + z_{i,0} + ∑ₚ z_{i,p,α}) / ∑_α u*_α) + ∫₀¹ b_w(t) dt`. -/
theorem guerra_fixed_weights (hN : 0 < N) (ξ : ℝ → ℝ) (hS : (overlapCovMatrix N ξ).PosSemidef)
    (qs : Fin (k + 1) → ℝ) (h0 : deriv ξ 0 = 0)
    (hmono : ∀ r, r ≤ k + 1 → deriv ξ (qExt qs r) ≤ deriv ξ (qExt qs (r + 1)))
    (hq01 : ∀ r, qExt qs r ∈ Set.Icc (0 : ℝ) 1)
    (htan : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ q ∈ Set.Icc (0 : ℝ) 1, ξ q + (x - q) * deriv ξ q ≤ ξ x)
    (h : ℝ) (w : CascadeWeights k) (hW0 : weightSum k w ≠ 0) (hW : weightSum k w ≠ ∞) :
    mixedPSpinFreeEnergy N ξ h
      ≤ (1 / (N : ℝ)) * (∫ z, Real.log ((cascadeSum k (coshG N k h z.1) (cascadeZip k (w, z.2))).toReal
            / (cascadeSum k (fun _ => 1) (cascadeZip k (w, z.2))).toReal)
          ∂marksLaw N k (parisiVar ξ qs 0) fun p => parisiVar ξ qs (p.val + 1))
        + ∫ t in (0 : ℝ)..1, guerraBound N k ξ qs h w t := by
  set v₀ : ℝ≥0 := parisiVar ξ qs 0 with hv₀
  set vs : Fin k → ℝ≥0 := fun p => parisiVar ξ qs (p.val + 1) with hvs
  set Pm : Measure (MarksSpace N k) := marksLaw N k v₀ vs with hPm
  set S : MarksSpace N k → ℝ :=
    fun z => (cascadeSum k (coshG N k h z.1) (cascadeZip k (w, z.2))).toReal with hSdef
  set SM : ℕ → MarksSpace N k → ℝ :=
    fun M z => (truncSum N k M w (coshG N k h z.1) z.2).toReal with hSMdef
  set W : ℝ := (weightSum k w).toReal with hWdef
  have hWpos : 0 < W := ENNReal.toReal_pos hW0 hW
  have hw : ∀ α, branchWeight k w α ≠ ∞ :=
    fun α => ne_top_of_le_ne_top hW (branchWeight_le_weightSum k w α)
  -- the branch `α₀` of positive weight, present in all large truncated trees
  obtain ⟨α₀, hα₀, M₀, hM₀⟩ := exists_mem_truncFinset k w hW0
  set c : ℝ := (branchWeight k w α₀).toReal with hcdef
  have hc : 0 < c := ENNReal.toReal_pos hα₀ (hw α₀)
  -- measurability and a.e. finiteness of the cascade sum
  have hmeasS := measurable_cascadeSum_coshG N k h w
  have hfin : ∫⁻ z, cascadeSum k (coshG N k h z.1) (cascadeZip k (w, z.2)) ∂Pm ≠ ∞ := by
    rw [hPm, lintegral_cascadeSum_coshG]
    exact ENNReal.mul_ne_top hW (coshConst_ne_top N k v₀ vs h)
  have hSfin : ∀ᵐ z ∂Pm, cascadeSum k (coshG N k h z.1) (cascadeZip k (w, z.2)) < ∞ :=
    ae_lt_top hmeasS hfin
  have hintS : Integrable S Pm := integrable_toReal_of_lintegral_ne_top hmeasS.aemeasurable hfin
  -- lower bounds by the single branch `α₀`
  have hcS : ∀ z : MarksSpace N k, cascadeSum k (coshG N k h z.1) (cascadeZip k (w, z.2)) < ∞ →
      c ≤ S z := by
    intro z hz
    refine ENNReal.toReal_mono hz.ne ?_
    calc branchWeight k w α₀ = branchWeight k w α₀ * 1 := (mul_one _).symm
      _ ≤ branchWeight k w α₀ * coshG N k h z.1 (branchMarks k z.2 α₀) :=
        mul_le_mul' le_rfl (one_le_coshG N k h z.1 _)
      _ ≤ _ := le_cascadeSum_cascadeZip N k w (measurable_coshG' N k h z.1) z.2 α₀
  have hcSM : ∀ M, M₀ ≤ M → ∀ z : MarksSpace N k,
      cascadeSum k (coshG N k h z.1) (cascadeZip k (w, z.2)) < ∞ → c ≤ SM M z := by
    intro M hM z hz
    refine ENNReal.toReal_mono (ne_top_of_le_ne_top hz.ne
      (truncSum_le_cascadeSum N k M w (measurable_coshG' N k h z.1) z.2)) ?_
    calc branchWeight k w α₀ = branchWeight k w α₀ * 1 := (mul_one _).symm
      _ ≤ branchWeight k w α₀ * coshG N k h z.1 (branchMarks k z.2 α₀) :=
        mul_le_mul' le_rfl (one_le_coshG N k h z.1 _)
      _ ≤ _ := le_truncSum_of_mem N k M w _ z.2 (hM₀ M hM)
  have hSMS : ∀ M (z : MarksSpace N k),
      cascadeSum k (coshG N k h z.1) (cascadeZip k (w, z.2)) < ∞ → SM M z ≤ S z := fun M z hz =>
    ENNReal.toReal_mono hz.ne (truncSum_le_cascadeSum N k M w (measurable_coshG' N k h z.1) z.2)
  -- integrability of the logarithms
  have hmeasSM : ∀ M, Measurable (SM M) := by
    intro M
    refine ENNReal.measurable_toReal.comp (Finset.measurable_sum _ fun α _ => measurable_const.mul ?_)
    have := (measurable_coshG N k h).comp (measurable_fst.prodMk
      ((measurable_branchMarks k (truncBranchCoe k M α)).comp measurable_snd) :
        Measurable fun z : MarksSpace N k => (z.1, branchMarks k z.2 (truncBranchCoe k M α)))
    simp only [Function.comp_def] at this
    exact this
  have hintlogS : Integrable (fun z => Real.log (S z)) Pm := by
    refine Integrable.mono' (hintS.add (integrable_const |Real.log c|))
      (Real.measurable_log.comp (ENNReal.measurable_toReal.comp hmeasS)).aestronglyMeasurable ?_
    filter_upwards [hSfin] with z hz
    rw [Real.norm_eq_abs]
    exact abs_log_le_add_abs_log hc (hcS z hz)
  have hintlogSM : ∀ M, M₀ ≤ M → Integrable (fun z => Real.log (SM M z)) Pm := by
    intro M hM
    refine Integrable.mono' (hintS.add (integrable_const |Real.log c|))
      (Real.measurable_log.comp (hmeasSM M)).aestronglyMeasurable ?_
    filter_upwards [hSfin] with z hz
    rw [Real.norm_eq_abs]
    refine (abs_log_le_add_abs_log hc (hcSM M hM z hz)).trans ?_
    show SM M z + |Real.log c| ≤ S z + |Real.log c|
    exact add_le_add (hSMS M z hz) le_rfl
  -- monotonicity of the first term
  have hmono_int : ∀ M, M₀ ≤ M →
      (∫ z, (1 / (N : ℝ)) * Real.log (SM M z) ∂Pm) ≤ ∫ z, (1 / (N : ℝ)) * Real.log (S z) ∂Pm := by
    intro M hM
    refine integral_mono_ae ((hintlogSM M hM).const_mul _) (hintlogS.const_mul _) ?_
    filter_upwards [hSfin] with z hz
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (hc.trans_le (hcSM M hM z hz)) (hSMS M z hz))
      (by positivity)
  -- the truncated bound (★) for `M ≥ M₀`
  have hstar : ∀ M, M₀ ≤ M → mixedPSpinFreeEnergy N ξ h
      ≤ (∫ z, (1 / (N : ℝ)) * Real.log (S z) ∂Pm)
        - (1 / (N : ℝ)) * Real.log (∑ α, truncWt k M w α)
        + ∫ t in (0 : ℝ)..1, guerraTruncBound N k M ξ qs h w t := by
    intro M hM
    have hne := truncWt_ne_zero_of_mem k w hW hα₀ (hM₀ M hM)
    have h1 := guerra_truncated (N := N) (k := k) (M := M) hN ξ hS qs h0 hmono hq01 htan h w hne
    have h2 : (∫ z, (1 / (N : ℝ)) * Real.log (∑ α, truncWt k M w α
        * ∏ i, (2 * Real.cosh (h + treeMark N k M z α i))) ∂Pm)
        = ∫ z, (1 / (N : ℝ)) * Real.log (SM M z) ∂Pm := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      beta_reduce
      rw [sum_truncWt_mul_prod_eq N k M w hw h z]
    rw [h2] at h1
    linarith [hmono_int M hM]
  -- the limits of the remaining terms
  have hlimW : Tendsto (fun M => (1 / (N : ℝ)) * Real.log (∑ α, truncWt k M w α)) atTop
      (𝓝 ((1 / (N : ℝ)) * Real.log W)) :=
    ((tendsto_toReal_sum_truncBranch k (branchWeight k w) hW).log hWpos.ne').const_mul _
  have hlimB := tendsto_integral_guerraTruncBound N k ξ qs h w hW0 hW
  have hlim : Tendsto (fun M => (∫ z, (1 / (N : ℝ)) * Real.log (S z) ∂Pm)
      - (1 / (N : ℝ)) * Real.log (∑ α, truncWt k M w α)
      + ∫ t in (0 : ℝ)..1, guerraTruncBound N k M ξ qs h w t) atTop
      (𝓝 ((∫ z, (1 / (N : ℝ)) * Real.log (S z) ∂Pm) - (1 / (N : ℝ)) * Real.log W
        + ∫ t in (0 : ℝ)..1, guerraBound N k ξ qs h w t)) :=
    (tendsto_const_nhds.sub hlimW).add hlimB
  have hle : mixedPSpinFreeEnergy N ξ h ≤ (∫ z, (1 / (N : ℝ)) * Real.log (S z) ∂Pm)
      - (1 / (N : ℝ)) * Real.log W + ∫ t in (0 : ℝ)..1, guerraBound N k ξ qs h w t :=
    ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨M₀, hstar⟩)
  -- identification of the first two terms
  have hlogdiv : (∫ z, Real.log ((cascadeSum k (coshG N k h z.1) (cascadeZip k (w, z.2))).toReal
        / (cascadeSum k (fun _ => 1) (cascadeZip k (w, z.2))).toReal) ∂Pm)
      = (∫ z, Real.log (S z) ∂Pm) - Real.log W := by
    have hae : ∀ᵐ z ∂Pm, Real.log ((cascadeSum k (coshG N k h z.1) (cascadeZip k (w, z.2))).toReal
        / (cascadeSum k (fun _ => 1) (cascadeZip k (w, z.2))).toReal)
        = Real.log (S z) - Real.log W := by
      filter_upwards [hSfin] with z hz
      rw [cascadeSum_one_cascadeZip, Real.log_div (hc.trans_le (hcS z hz)).ne' hWpos.ne']
    rw [integral_congr_ae hae, integral_sub hintlogS (integrable_const _), integral_const,
      probReal_univ, one_smul]
  rw [hlogdiv, mul_sub, ← integral_const_mul]
  exact hle

end

end SpinGlass
