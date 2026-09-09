/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Limit.PositivityPrinciple

/-!
# Talagrand's positivity principle: the identities half (Vol. II, §12.3)

Proposition 12.3.4 and Theorem 12.3.1. Given `0 < ε ≤ 1/2` and `n` replicas besides replica `0`,
let `b_j = -2ε + jε/n` (`j = 0, …, n`) and let `ψ_l` be the continuous ramp equal to `1` on
`(-∞, b_{l-1}]` and `0` on `[b_l, ∞)`. The observables

`G_j(R) = ∏_{l=1}^{j} ψ_l(R_{0,l})`

of the first `j+1` replicas satisfy `G_n ≤ 1_{D_{n+1}}`, and the Ghirlanda–Guerra identity applied
to `ψ_{j+1}(R_{0,j+1})` and `G_j` gives the recursion `I_{j+1} ≥ ((j + a)/(j+1)) I_j − δ_j`, where
`I_j = ∫ G_j` and `a` is the mass of `{R_{0,1} ≤ -2ε}`. Iterating,
`a ∏_{j<n} (j+a)/(j+1) − ∑ δ_j ≤ I_n ≤ μ(D_{n+1}) ≤ (4 log(n+1) + 1)/(ε(n+1))`, and since the
product is `≳ n^{a-1}` this forces `a → 0` as the defects vanish.

This file contains the test functions and observables and their pointwise properties.
-/

open MeasureTheory ProbabilityTheory Filter Topology BigOperators MeasureTheory.GibbsMeasure

namespace SpinGlass

noncomputable section

/-! ### The ramp test functions -/

/-- The continuous ramp on `[-1,1]`: `1` on `(-∞, lo]`, `0` on `[hi, ∞)`, linear in between. -/
def rampCM (lo hi : ℝ) : C(OverlapValue, ℝ) :=
  ⟨fun x => max 0 (min 1 ((hi - (x : ℝ)) / (hi - lo))), by fun_prop⟩

@[simp] lemma rampCM_apply (lo hi : ℝ) (x : OverlapValue) :
    rampCM lo hi x = max 0 (min 1 ((hi - (x : ℝ)) / (hi - lo))) := rfl

lemma rampCM_nonneg (lo hi : ℝ) (x : OverlapValue) : 0 ≤ rampCM lo hi x := le_max_left _ _

lemma rampCM_le_one (lo hi : ℝ) (x : OverlapValue) : rampCM lo hi x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma rampCM_eq_one {lo hi : ℝ} (hlt : lo < hi) {x : OverlapValue} (hx : (x : ℝ) ≤ lo) :
    rampCM lo hi x = 1 := by
  have h1 : 1 ≤ (hi - (x : ℝ)) / (hi - lo) := by
    rw [le_div_iff₀ (sub_pos.2 hlt)]
    linarith
  rw [rampCM_apply, min_eq_left h1, max_eq_right zero_le_one]

lemma rampCM_eq_zero {lo hi : ℝ} (hlt : lo < hi) {x : OverlapValue} (hx : hi ≤ (x : ℝ)) :
    rampCM lo hi x = 0 := by
  have h0 : (hi - (x : ℝ)) / (hi - lo) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_pos.2 hlt).le
  rw [rampCM_apply, max_eq_left (min_le_of_right_le h0)]

/-- Where the ramp is positive, the argument is below the upper threshold. -/
lemma lt_of_rampCM_pos {lo hi : ℝ} (hlt : lo < hi) {x : OverlapValue} (hx : 0 < rampCM lo hi x) :
    (x : ℝ) < hi := by
  by_contra h
  rw [rampCM_eq_zero hlt (not_lt.1 h)] at hx
  exact lt_irrefl _ hx

/-- The ramp dominates the indicator of `(-∞, lo]`. -/
lemma indicator_le_rampCM {lo hi : ℝ} (hlt : lo < hi) (x : OverlapValue) :
    (if (x : ℝ) ≤ lo then (1 : ℝ) else 0) ≤ rampCM lo hi x := by
  split_ifs with h
  · exact (rampCM_eq_one hlt h).ge
  · exact rampCM_nonneg _ _ _

lemma norm_rampCM_le (lo hi : ℝ) : ‖rampCM lo hi‖ ≤ 1 :=
  ContinuousMap.norm_le _ zero_le_one |>.2 fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (rampCM_nonneg _ _ _)]
    exact rampCM_le_one _ _ _

/-! ### The thresholds and the observables -/

section Observables

variable (ε : ℝ) (n : ℕ)

/-- The thresholds `b_j = -2ε + jε/n`, `j = 0, …, n`: from `-2ε` to `-ε`. -/
def negThreshold (j : ℕ) : ℝ := -2 * ε + (j : ℝ) * ε / n

lemma negThreshold_zero : negThreshold ε n 0 = -2 * ε := by simp [negThreshold]

lemma negThreshold_self (hn : 0 < n) : negThreshold ε n n = -ε := by
  unfold negThreshold
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

lemma negThreshold_lt_succ (hε : 0 < ε) (hn : 0 < n) (j : ℕ) :
    negThreshold ε n j < negThreshold ε n (j + 1) := by
  unfold negThreshold
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  push_cast
  have : (j : ℝ) * ε / n < ((j : ℝ) + 1) * ε / n := by
    rw [div_lt_div_iff_of_pos_right hnR]
    nlinarith
  linarith

lemma negThreshold_mono (hε : 0 < ε) (hn : 0 < n) : Monotone (negThreshold ε n) :=
  monotone_nat_of_le_succ fun j => (negThreshold_lt_succ ε n hε hn j).le

lemma negThreshold_le_neg (hε : 0 < ε) (hn : 0 < n) {j : ℕ} (hj : j ≤ n) :
    negThreshold ε n j ≤ -ε := by
  rw [← negThreshold_self ε n hn]
  exact negThreshold_mono ε n hε hn hj

/-- The `l`-th ramp: `1` below `b_{l-1}`, `0` above `b_l`. -/
def negRamp (l : ℕ) : C(OverlapValue, ℝ) :=
  rampCM (negThreshold ε n (l - 1)) (negThreshold ε n l)

/-- **The observables `G_j`**: the product of the ramps of the overlaps of replica `0` with replicas
`1, …, j`, as a continuous function of the block of the first `j+1` replicas. -/
def negObs (j : ℕ) : C(Fin (j + 1) → Fin (j + 1) → OverlapValue, ℝ) :=
  ⟨fun x => ∏ l : Fin j, negRamp ε n ((l : ℕ) + 1) (x 0 l.succ),
    continuous_finsetProd _ fun _ _ =>
      (negRamp ε n _).continuous.comp ((continuous_apply _).comp (continuous_apply _))⟩

@[simp] lemma negObs_apply (j : ℕ) (x : Fin (j + 1) → Fin (j + 1) → OverlapValue) :
    negObs ε n j x = ∏ l : Fin j, negRamp ε n ((l : ℕ) + 1) (x 0 l.succ) := rfl

lemma negObs_nonneg (j : ℕ) (x : Fin (j + 1) → Fin (j + 1) → OverlapValue) :
    0 ≤ negObs ε n j x := by
  rw [negObs_apply]
  exact Finset.prod_nonneg fun l _ => rampCM_nonneg _ _ _

lemma negObs_le_one (j : ℕ) (x : Fin (j + 1) → Fin (j + 1) → OverlapValue) :
    negObs ε n j x ≤ 1 := by
  rw [negObs_apply]
  exact Finset.prod_le_one (fun l _ => rampCM_nonneg _ _ _) fun l _ => rampCM_le_one _ _ _

lemma norm_negObs_le (j : ℕ) : ‖negObs ε n j‖ ≤ 1 :=
  ContinuousMap.norm_le _ zero_le_one |>.2 fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (negObs_nonneg ε n j x)]
    exact negObs_le_one ε n j x

/-- `G_{j+1}(R) = ψ_{j+1}(R_{0,j+1}) · G_j(R)`. -/
lemma negObs_succ_blockRestrict (j : ℕ) (R : ℕ → ℕ → OverlapValue) :
    negObs ε n (j + 1) (blockRestrict (j + 2) R)
      = negRamp ε n (j + 1) (R 0 (j + 1)) * negObs ε n j (blockRestrict (j + 1) R) := by
  simp only [negObs_apply, blockRestrict_apply]
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.succ_castSucc, Fin.val_succ, Fin.val_zero, Fin.val_last]
  ring

/-- A positive product of nonnegative factors has positive factors. -/
lemma negRamp_pos_of_negObs_pos (j : ℕ) (R : ℕ → ℕ → OverlapValue)
    (hpos : 0 < negObs ε n j (blockRestrict (j + 1) R)) (l : Fin j) :
    0 < negRamp ε n ((l : ℕ) + 1) (R 0 ((l : ℕ) + 1)) := by
  by_contra h
  have h0 : negRamp ε n ((l : ℕ) + 1) (R 0 ((l : ℕ) + 1)) = 0 :=
    le_antisymm (not_lt.1 h) (rampCM_nonneg _ _ _)
  refine hpos.ne' ?_
  rw [negObs_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ l)
    (by simpa [blockRestrict_apply, Fin.val_succ] using h0)

/-- Where `G_j > 0`, the overlap `R_{0,l}` (`1 ≤ l ≤ j`) lies strictly below `b_l`. -/
lemma lt_negThreshold_of_negObs_pos (hε : 0 < ε) (hn : 0 < n) {j l : ℕ} (hl1 : 1 ≤ l) (hlj : l ≤ j)
    (R : ℕ → ℕ → OverlapValue) (hpos : 0 < negObs ε n j (blockRestrict (j + 1) R)) :
    ((R 0 l : OverlapValue) : ℝ) < negThreshold ε n l := by
  have hfac := negRamp_pos_of_negObs_pos ε n j R hpos ⟨l - 1, by omega⟩
  simp only [Nat.sub_add_cancel hl1] at hfac
  have hlt' := negThreshold_lt_succ ε n hε hn (l - 1)
  rw [Nat.sub_add_cancel hl1] at hlt'
  unfold negRamp at hfac
  exact lt_of_rampCM_pos hlt' hfac

/-- **Absorption**: for `1 ≤ l ≤ j`, `ψ_{j+1}(R_{0,l}) · G_j(R) = G_j(R)`, because `G_j > 0` forces
`R_{0,l} < b_l ≤ b_j`, where `ψ_{j+1} = 1`. -/
lemma negRamp_mul_negObs (hε : 0 < ε) (hn : 0 < n) {j l : ℕ} (hl1 : 1 ≤ l) (hlj : l ≤ j)
    (R : ℕ → ℕ → OverlapValue) :
    negRamp ε n (j + 1) (R 0 l) * negObs ε n j (blockRestrict (j + 1) R)
      = negObs ε n j (blockRestrict (j + 1) R) := by
  rcases (negObs_nonneg ε n j (blockRestrict (j + 1) R)).lt_or_eq with hpos | hzero
  · have hle : ((R 0 l : OverlapValue) : ℝ) ≤ negThreshold ε n j :=
      (lt_negThreshold_of_negObs_pos ε n hε hn hl1 hlj R hpos).le.trans
        (negThreshold_mono ε n hε hn hlj)
    simp only [negRamp, Nat.add_sub_cancel]
    rw [rampCM_eq_one (negThreshold_lt_succ ε n hε hn j) hle, one_mul]
  · rw [← hzero, mul_zero]

/-- **`G_n ≤ 1_{D_{n+1}}`**: where `G_n > 0`, every `R_{0,l}` (`1 ≤ l ≤ n`) is `< b_l ≤ -ε`. -/
lemma negObs_le_indicator_negSet (hε : 0 < ε) (hn : 0 < n) (R : ℕ → ℕ → OverlapValue) :
    negObs ε n n (blockRestrict (n + 1) R) ≤ (negSet ε (n + 1)).indicator 1 R := by
  rcases (negObs_nonneg ε n n (blockRestrict (n + 1) R)).lt_or_eq with hpos | hzero
  · have hmem : R ∈ negSet ε (n + 1) := by
      intro l hl
      rw [Finset.mem_Ico] at hl
      exact (lt_negThreshold_of_negObs_pos ε n hε hn hl.1 (by omega) R hpos).le.trans
        (negThreshold_le_neg ε n hε hn (by omega))
    rw [Set.indicator_of_mem hmem, Pi.one_apply]
    exact negObs_le_one ε n n _
  · rw [← hzero]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) R

end Observables

/-! ### The recursion (Proposition 12.3.4) -/

section Recursion

variable (μ : Measure (ℕ → ℕ → OverlapValue)) [IsProbabilityMeasure μ] (ε : ℝ) (n : ℕ)

/-- `I_j = ∫ G_j`. -/
def negObsInt (j : ℕ) : ℝ := ∫ R, negObs ε n j (blockRestrict (j + 1) R) ∂μ

/-- `a = μ{R_{0,1} ≤ -2ε}`. -/
def negMassLaw : ℝ := μ.real {R : ℕ → ℕ → OverlapValue | ((R 0 1 : OverlapValue) : ℝ) ≤ -2 * ε}

lemma measurableSet_negLevel (t : ℝ) :
    MeasurableSet {R : ℕ → ℕ → OverlapValue | ((R 0 1 : OverlapValue) : ℝ) ≤ t} :=
  (isClosed_le (continuous_entry 0 1) continuous_const).measurableSet

omit [IsProbabilityMeasure μ] in
lemma negObsInt_nonneg (j : ℕ) : 0 ≤ negObsInt μ ε n j :=
  integral_nonneg fun _ => negObs_nonneg ε n j _

/-- `I_j ≤ 1`. -/
lemma negObsInt_le_one (j : ℕ) : negObsInt μ ε n j ≤ 1 := by
  unfold negObsInt
  calc (∫ R, negObs ε n j (blockRestrict (j + 1) R) ∂μ) ≤ ∫ _R, (1 : ℝ) ∂μ :=
        integral_mono (integrable_continuousMap ((negObs ε n j).comp (blockRestrict (j + 1))))
          (integrable_const 1) fun R => negObs_le_one ε n j _
    _ = 1 := by simp

/-- **`I_1 ≥ a`**: the first ramp dominates the indicator of `{R_{0,1} ≤ -2ε}`. -/
lemma negMassLaw_le_negObsInt_one (hε : 0 < ε) (hn : 0 < n) :
    negMassLaw μ ε ≤ negObsInt μ ε n 1 := by
  unfold negMassLaw negObsInt
  rw [← integral_indicator_one (measurableSet_negLevel (-2 * ε))]
  refine integral_mono ((integrable_const (1 : ℝ)).indicator (measurableSet_negLevel _))
    (integrable_continuousMap ((negObs ε n 1).comp (blockRestrict 2))) fun R => ?_
  simp only [negObs_apply, Fin.prod_univ_one, blockRestrict_apply, Fin.val_succ, Fin.val_zero,
    Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply, negRamp, Nat.sub_self]
  have hlt := negThreshold_lt_succ ε n hε hn 0
  split_ifs with hx
  · exact (rampCM_eq_one hlt (by rw [negThreshold_zero]; linarith)).ge
  · exact rampCM_nonneg _ _ _

omit [IsProbabilityMeasure μ] in
/-- Exchangeability: `∫ φ(R_{0,j+1}) = ∫ φ(R_{0,1})`. -/
lemma integral_comp_entry_eq_of_exchangeable (hex : IsJointlyExchangeable μ)
    (φ : C(OverlapValue, ℝ)) (j : ℕ) :
    (∫ R, φ (R 0 (j + 1)) ∂μ) = ∫ R, φ (R 0 1) ∂μ := by
  have hm1 : Measurable fun R : ℕ → ℕ → OverlapValue => R 0 (j + 1) :=
    (measurable_pi_apply (j + 1)).comp (measurable_pi_apply 0)
  have hm2 : Measurable fun R : ℕ → ℕ → OverlapValue => R 0 1 :=
    (measurable_pi_apply 1).comp (measurable_pi_apply 0)
  have h1 : (∫ R, φ (R 0 (j + 1)) ∂μ) = ∫ x, φ x ∂(μ.map fun R => R 0 (j + 1)) := by
    rw [integral_map hm1.aemeasurable φ.continuous.aestronglyMeasurable]
  have h2 : (∫ R, φ (R 0 1) ∂μ) = ∫ x, φ x ∂(μ.map fun R => R 0 1) := by
    rw [integral_map hm2.aemeasurable φ.continuous.aestronglyMeasurable]
  rw [h1, h2, map_entry_eq_oneOverlapLaw hex (Nat.zero_ne_add_one j),
    map_entry_eq_oneOverlapLaw hex zero_ne_one]

/-- `∫ ψ_{j+1}(R_{0,1}) ≥ a`: the `(j+1)`-th ramp is `1` on `(-∞, b_j] ⊇ (-∞, -2ε]`. -/
lemma negMassLaw_le_integral_negRamp (hε : 0 < ε) (hn : 0 < n) (j : ℕ) :
    negMassLaw μ ε ≤ ∫ R, negRamp ε n (j + 1) (R 0 1) ∂μ := by
  unfold negMassLaw
  rw [← integral_indicator_one (measurableSet_negLevel (-2 * ε))]
  refine integral_mono ((integrable_const (1 : ℝ)).indicator (measurableSet_negLevel _))
    (integrable_continuousMap ((negRamp ε n (j + 1)).comp (evalCM 0 1))) fun R => ?_
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
  have hlt := negThreshold_lt_succ ε n hε hn j
  have hb0 : -2 * ε ≤ negThreshold ε n j := by
    rw [← negThreshold_zero ε n]
    exact negThreshold_mono ε n hε hn (Nat.zero_le j)
  unfold negRamp
  simp only [Nat.add_sub_cancel]
  split_ifs with h
  · exact (rampCM_eq_one hlt (h.trans hb0)).ge
  · exact rampCM_nonneg _ _ _

/-- **The recursion (Talagrand, Vol. II, (12.51)–(12.52))**: for `j + 1 ≤ n`,
`I_{j+1} ≥ ((j + a)/(j+1)) I_j − |defect|`. -/
theorem negObsInt_succ_ge (hex : IsJointlyExchangeable μ) (hε : 0 < ε) (hn : 0 < n) (j : ℕ) :
    ((j : ℝ) + negMassLaw μ ε) / ((j : ℝ) + 1) * negObsInt μ ε n j
        - |ggDefect μ (j + 1) (negRamp ε n (j + 1)) (negObs ε n j)|
      ≤ negObsInt μ ε n (j + 1) := by
  classical
  set a := negMassLaw μ ε with ha
  set I := negObsInt μ ε n j with hI
  set D := ggDefect μ (j + 1) (negRamp ε n (j + 1)) (negObs ε n j) with hD
  have hI0 : 0 ≤ I := negObsInt_nonneg μ ε n j
  -- the three ingredients
  have hmain : (∫ R, negRamp ε n (j + 1) (R 0 (j + 1)) * negObs ε n j (blockRestrict (j + 1) R) ∂μ)
      = negObsInt μ ε n (j + 1) := by
    unfold negObsInt
    refine integral_congr_ae (Eventually.of_forall fun R => ?_)
    change _ = negObs ε n (j + 1) (blockRestrict (j + 2) R)
    exact (negObs_succ_blockRestrict ε n j R).symm
  have habsorb : ∀ l ∈ Finset.Ico 1 (j + 1),
      (∫ R, negRamp ε n (j + 1) (R 0 l) * negObs ε n j (blockRestrict (j + 1) R) ∂μ) = I := by
    intro l hl
    rw [Finset.mem_Ico] at hl
    rw [hI]
    unfold negObsInt
    refine integral_congr_ae (Eventually.of_forall fun R => ?_)
    exact negRamp_mul_negObs ε n hε hn hl.1 (by omega) R
  have hfirst : a ≤ ∫ R, negRamp ε n (j + 1) (R 0 (j + 1)) ∂μ := by
    rw [integral_comp_entry_eq_of_exchangeable μ hex]
    exact negMassLaw_le_integral_negRamp μ ε n hε hn j
  -- unfold the defect
  have hDdef : D = negObsInt μ ε n (j + 1)
      - ((1 / ((j : ℝ) + 1)) * ((∫ R, negRamp ε n (j + 1) (R 0 (j + 1)) ∂μ) * I)
        + (1 / ((j : ℝ) + 1)) * ∑ l ∈ Finset.Ico 1 (j + 1), I) := by
    rw [hD]
    unfold ggDefect
    rw [hmain, Finset.sum_congr rfl habsorb]
    push_cast
    rfl
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hDdef
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hcast : ((j + 1 - 1 : ℕ) : ℝ) = j := by simp
  rw [hcast] at hDdef
  -- conclude
  have hD_le : -|D| ≤ D := neg_abs_le D
  have hterm : (1 / ((j : ℝ) + 1)) * (a * I) ≤
      (1 / ((j : ℝ) + 1)) * ((∫ R, negRamp ε n (j + 1) (R 0 (j + 1)) ∂μ) * I) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hfirst hI0) (by positivity)
  have hsplit : ((j : ℝ) + a) / ((j : ℝ) + 1) * I
      = (1 / ((j : ℝ) + 1)) * (a * I) + (1 / ((j : ℝ) + 1)) * ((j : ℝ) * I) := by
    field_simp
    ring
  rw [hsplit]
  linarith [hDdef, hD_le, hterm]

/-- The product `P_k(a) = ∏_{j=1}^{k-1} (j + a)/(j + 1)`. -/
def negProd (a : ℝ) (k : ℕ) : ℝ := ∏ j ∈ Finset.Ico 1 k, ((j : ℝ) + a) / ((j : ℝ) + 1)

lemma negProd_one (a : ℝ) : negProd a 1 = 1 := by simp [negProd]

lemma negProd_succ (a : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    negProd a (k + 1) = negProd a k * (((k : ℝ) + a) / ((k : ℝ) + 1)) := by
  unfold negProd
  rw [Finset.prod_Ico_succ_top hk]

lemma negProd_nonneg {a : ℝ} (ha : 0 ≤ a) (k : ℕ) : 0 ≤ negProd a k :=
  Finset.prod_nonneg fun j _ => div_nonneg (by positivity) (by positivity)

/-- **The iterated recursion**: for `1 ≤ k ≤ n`,
`a P_k(a) − ∑_{j=1}^{k-1} |defect_j| ≤ I_k`. -/
theorem negMassLaw_mul_negProd_sub_le (hex : IsJointlyExchangeable μ) (hε : 0 < ε) (hn : 0 < n)
    {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    negMassLaw μ ε * negProd (negMassLaw μ ε) k
        - ∑ j ∈ Finset.Ico 1 k, |ggDefect μ (j + 1) (negRamp ε n (j + 1)) (negObs ε n j)|
      ≤ negObsInt μ ε n k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simp only [zero_add, negProd_one, mul_one, Finset.Ico_self, Finset.sum_empty, sub_zero]
      exact negMassLaw_le_negObsInt_one μ ε n hε hn
    · have ih' := ih hkpos (by omega)
      have hrec := negObsInt_succ_ge μ ε n hex hε hn k
      have ha0 : 0 ≤ negMassLaw μ ε := measureReal_nonneg
      have hfrac1 : ((k : ℝ) + negMassLaw μ ε) / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have : negMassLaw μ ε ≤ 1 := by
          unfold negMassLaw
          exact measureReal_le_one
        linarith
      have hfrac0 : 0 ≤ ((k : ℝ) + negMassLaw μ ε) / ((k : ℝ) + 1) := by positivity
      have hS0 : 0 ≤ ∑ j ∈ Finset.Ico 1 k,
          |ggDefect μ (j + 1) (negRamp ε n (j + 1)) (negObs ε n j)| :=
        Finset.sum_nonneg fun j _ => abs_nonneg _
      rw [negProd_succ _ hkpos, Finset.sum_Ico_succ_top hkpos]
      have h1 : ((k : ℝ) + negMassLaw μ ε) / ((k : ℝ) + 1)
          * (negMassLaw μ ε * negProd (negMassLaw μ ε) k
            - ∑ j ∈ Finset.Ico 1 k, |ggDefect μ (j + 1) (negRamp ε n (j + 1)) (negObs ε n j)|)
          ≤ ((k : ℝ) + negMassLaw μ ε) / ((k : ℝ) + 1) * negObsInt μ ε n k :=
        mul_le_mul_of_nonneg_left ih' hfrac0
      have h2 : ((k : ℝ) + negMassLaw μ ε) / ((k : ℝ) + 1)
          * ∑ j ∈ Finset.Ico 1 k, |ggDefect μ (j + 1) (negRamp ε n (j + 1)) (negObs ε n j)|
          ≤ ∑ j ∈ Finset.Ico 1 k, |ggDefect μ (j + 1) (negRamp ε n (j + 1)) (negObs ε n j)| := by
        nlinarith [hfrac1, hfrac0, hS0]
      nlinarith [h1, h2, hrec]

/-- **`I_n ≤ μ(D_{n+1})`.** -/
theorem negObsInt_le_real_negSet (hε : 0 < ε) (hn : 0 < n) :
    negObsInt μ ε n n ≤ μ.real (negSet ε (n + 1)) := by
  unfold negObsInt
  rw [← integral_indicator_one (measurableSet_negSet ε (n + 1))]
  exact integral_mono (integrable_continuousMap ((negObs ε n n).comp (blockRestrict (n + 1))))
    ((integrable_const (1 : ℝ)).indicator (measurableSet_negSet ε (n + 1)))
    fun R => negObs_le_indicator_negSet ε n hε hn R

end Recursion

/-! ### Elementary estimates: the product `P_k(a)` is at least `e⁻² k^{a-1}` -/

section Analytic

/-- `1 - x ≥ exp(-x - 2x²)` on `[0, 1/2]`. -/
lemma exp_neg_sub_le_one_sub {x : ℝ} (hx1 : x ≤ 1 / 2) :
    Real.exp (-x - 2 * x ^ 2) ≤ 1 - x := by
  have h1x : 0 < 1 - x := by linarith
  have hlog : Real.log (1 / (1 - x)) ≤ 1 / (1 - x) - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [one_div, Real.log_inv] at hlog
  have hfrac : (1 - x)⁻¹ - 1 ≤ x + 2 * x ^ 2 := by
    rw [inv_eq_one_div, div_sub_one h1x.ne', div_le_iff₀ h1x]
    nlinarith
  have hlog' : -x - 2 * x ^ 2 ≤ Real.log (1 - x) := by linarith [hlog, hfrac]
  calc Real.exp (-x - 2 * x ^ 2) ≤ Real.exp (Real.log (1 - x)) := Real.exp_le_exp.2 hlog'
    _ = 1 - x := Real.exp_log h1x

/-- `log(k+1) - log k ≥ 1/(k+1)` for `k ≥ 1`. -/
lemma inv_succ_le_log_succ_sub_log {k : ℕ} (hk : 1 ≤ k) :
    1 / ((k : ℝ) + 1) ≤ Real.log ((k : ℝ) + 1) - Real.log k := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have h := Real.log_le_sub_one_of_pos (x := (k : ℝ) / ((k : ℝ) + 1)) (by positivity)
  rw [Real.log_div hkR.ne' (by positivity)] at h
  have : (k : ℝ) / ((k : ℝ) + 1) - 1 = -(1 / ((k : ℝ) + 1)) := by
    field_simp
    ring
  linarith

/-- `∑_{j=1}^{k-1} 1/(j+1) ≤ log k`. -/
lemma sum_Ico_inv_succ_le_log (k : ℕ) (hk : 1 ≤ k) :
    ∑ j ∈ Finset.Ico 1 k, 1 / ((j : ℝ) + 1) ≤ Real.log k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0; simp
    · rw [Finset.sum_Ico_succ_top hpos]
      have := inv_succ_le_log_succ_sub_log hpos
      have ih' := ih hpos
      push_cast
      linarith

/-- `∑_{j=1}^{k-1} (1/(j+1))² ≤ 1 - 1/k ≤ 1`. -/
lemma sum_Ico_inv_succ_sq_le (k : ℕ) (hk : 1 ≤ k) :
    ∑ j ∈ Finset.Ico 1 k, (1 / ((j : ℝ) + 1)) ^ 2 ≤ 1 - 1 / (k : ℝ) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0; simp
    · rw [Finset.sum_Ico_succ_top hpos]
      have ih' := ih hpos
      have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hpos
      have hstep : (1 / ((k : ℝ) + 1)) ^ 2 ≤ 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) := by
        rw [div_pow, one_pow, div_sub_div _ _ hkR.ne' (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      push_cast
      linarith

/-- **The product lower bound**: for `0 ≤ a ≤ 1` and `k ≥ 1`, `P_k(a) ≥ e⁻² k^{a-1}`. -/
theorem negProd_ge (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (k : ℕ) (hk : 1 ≤ k) :
    Real.exp (-2) * (k : ℝ) ^ (a - 1) ≤ negProd a k := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  -- each factor
  have hfac : ∀ j ∈ Finset.Ico 1 k,
      Real.exp (-((1 - a) / ((j : ℝ) + 1)) - 2 * ((1 - a) / ((j : ℝ) + 1)) ^ 2)
        ≤ ((j : ℝ) + a) / ((j : ℝ) + 1) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj.1
    have hx0 : 0 ≤ (1 - a) / ((j : ℝ) + 1) := div_nonneg (by linarith) (by positivity)
    have hx1 : (1 - a) / ((j : ℝ) + 1) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have := exp_neg_sub_le_one_sub hx1
    have heq : 1 - (1 - a) / ((j : ℝ) + 1) = ((j : ℝ) + a) / ((j : ℝ) + 1) := by
      field_simp
      ring
    rw [heq] at this
    exact this
  have hprod : ∏ j ∈ Finset.Ico 1 k,
      Real.exp (-((1 - a) / ((j : ℝ) + 1)) - 2 * ((1 - a) / ((j : ℝ) + 1)) ^ 2) ≤ negProd a k :=
    Finset.prod_le_prod (fun j _ => (Real.exp_pos _).le) hfac
  rw [← Real.exp_sum] at hprod
  refine le_trans ?_ hprod
  -- the exponent
  have hsum1 := sum_Ico_inv_succ_le_log k hk
  have hsum2 := sum_Ico_inv_succ_sq_le k hk
  have hexp : -2 + Real.log k * (a - 1)
      ≤ ∑ j ∈ Finset.Ico 1 k, (-((1 - a) / ((j : ℝ) + 1)) - 2 * ((1 - a) / ((j : ℝ) + 1)) ^ 2) := by
    have h1 : ∑ j ∈ Finset.Ico 1 k, -((1 - a) / ((j : ℝ) + 1))
        = -((1 - a) * ∑ j ∈ Finset.Ico 1 k, 1 / ((j : ℝ) + 1)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have h2 : ∑ j ∈ Finset.Ico 1 k, 2 * ((1 - a) / ((j : ℝ) + 1)) ^ 2
        = 2 * (1 - a) ^ 2 * ∑ j ∈ Finset.Ico 1 k, (1 / ((j : ℝ) + 1)) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_sub_distrib, h1, h2]
    have h1a : 0 ≤ 1 - a := by linarith
    have hsq : (1 - a) ^ 2 ≤ 1 := by nlinarith
    have hlogk : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
    have hS0 : 0 ≤ ∑ j ∈ Finset.Ico 1 k, (1 / ((j : ℝ) + 1)) ^ 2 :=
      Finset.sum_nonneg fun j _ => by positivity
    have hk1 : 1 - 1 / (k : ℝ) ≤ 1 := by
      have : 0 ≤ 1 / (k : ℝ) := by positivity
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hsum1 h1a, mul_le_mul_of_nonneg_left (hsum2.trans hk1)
      (by positivity : 0 ≤ 2 * (1 - a) ^ 2), mul_le_mul_of_nonneg_right hsq hS0]
  calc Real.exp (-2) * (k : ℝ) ^ (a - 1) = Real.exp (-2 + Real.log k * (a - 1)) := by
        rw [Real.exp_add, Real.rpow_def_of_pos hkR]
    _ ≤ _ := Real.exp_le_exp.2 hexp

/-- **Existence of a good number of replicas**: for `0 < d ≤ 1` there is `k ≥ 2` with
`e² ((4 log(k+1) + 1)/ε + 1) < d k^d`. -/
theorem exists_good_k {ε d : ℝ} (hε : 0 < ε) (hd : 0 < d) (hd1 : d ≤ 1) :
    ∃ k : ℕ, 2 ≤ k ∧
      Real.exp 2 * ((4 * Real.log ((k : ℝ) + 1) + 1) / ε + 1) < d * (k : ℝ) ^ d := by
  -- `log(k+1)/k^d → 0` and `1/k^d → 0`
  have hlog : Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1) ^ d) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_atTop hd).tendsto_div_nhds_zero).comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hinv : Tendsto (fun k : ℕ => (k : ℝ) ^ (-d)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hd).comp tendsto_natCast_atTop_atTop
  -- `(k+1)^d ≤ 2 k^d` for `k ≥ 1`
  have hpow : ∀ k : ℕ, 1 ≤ k → ((k : ℝ) + 1) ^ d ≤ 2 * (k : ℝ) ^ d := by
    intro k hk
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    calc ((k : ℝ) + 1) ^ d ≤ (2 * (k : ℝ)) ^ d :=
          Real.rpow_le_rpow (by positivity) (by linarith) hd.le
      _ = 2 ^ d * (k : ℝ) ^ d := Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ 2 * (k : ℝ) ^ d := by
          have : (2 : ℝ) ^ d ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hd1
          rw [Real.rpow_one] at this
          exact mul_le_mul_of_nonneg_right this (by positivity)
  -- the combined quantity tends to `0`
  have hmain : Tendsto (fun k : ℕ =>
      Real.exp 2 * ((2 * (4 * (Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1) ^ d)) + (k : ℝ) ^ (-d)) / ε
        + (k : ℝ) ^ (-d))) atTop (𝓝 0) := by
    have := (((hlog.const_mul 4).const_mul 2).add hinv).div_const ε |>.add hinv
      |>.const_mul (Real.exp 2)
    simpa using this
  have hev := hmain.eventually (gt_mem_nhds hd)
  obtain ⟨k, hk⟩ := (hev.and (eventually_ge_atTop 2)).exists
  refine ⟨k, hk.2, ?_⟩
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk.2
  have hkR : (0 : ℝ) < k := by linarith
  have hkd : 0 < (k : ℝ) ^ d := Real.rpow_pos_of_pos hkR d
  have hneg : (k : ℝ) ^ (-d) = 1 / (k : ℝ) ^ d := by rw [Real.rpow_neg hkR.le, one_div]
  -- divide the target by `k^d`
  rw [← div_lt_iff₀ hkd]
  refine lt_of_le_of_lt ?_ hk.1
  rw [hneg]
  have hp := hpow k (by omega)
  have hl0 : 0 ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hq : Real.log ((k : ℝ) + 1) / (k : ℝ) ^ d
      ≤ 2 * (Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1) ^ d) := by
    rw [mul_div_assoc', div_le_div_iff₀ hkd (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hp hl0]
  have hexp2 : 0 < Real.exp 2 := Real.exp_pos 2
  have h4 : (4 * Real.log ((k : ℝ) + 1) + 1) / (k : ℝ) ^ d
      ≤ 2 * (4 * (Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1) ^ d)) + 1 / (k : ℝ) ^ d := by
    have : (4 * Real.log ((k : ℝ) + 1) + 1) / (k : ℝ) ^ d
        = 4 * (Real.log ((k : ℝ) + 1) / (k : ℝ) ^ d) + 1 / (k : ℝ) ^ d := by ring
    rw [this]
    linarith [hq]
  have key : (4 * Real.log ((k : ℝ) + 1) + 1) / ε / (k : ℝ) ^ d
      ≤ (2 * (4 * (Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1) ^ d)) + 1 / (k : ℝ) ^ d) / ε := by
    rw [div_right_comm]
    exact div_le_div_of_nonneg_right h4 hε.le
  calc Real.exp 2 * ((4 * Real.log ((k : ℝ) + 1) + 1) / ε + 1) / (k : ℝ) ^ d
      = Real.exp 2 * ((4 * Real.log ((k : ℝ) + 1) + 1) / ε / (k : ℝ) ^ d + 1 / (k : ℝ) ^ d) := by
        field_simp
    _ ≤ Real.exp 2 * ((2 * (4 * (Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1) ^ d)) + 1 / (k : ℝ) ^ d) / ε
          + 1 / (k : ℝ) ^ d) :=
        mul_le_mul_of_nonneg_left (add_le_add key le_rfl) hexp2.le

end Analytic

/-! ### Theorem 12.3.1 -/

section Theorem

/-- **Talagrand's positivity principle, Vol. II, Theorem 12.3.1.** For a sequence of jointly
exchangeable array laws satisfying the extended Ghirlanda–Guerra identities asymptotically,
uniformly over observables (`TendstoGGDefectUniform`), and the deterministic bound of Proposition
12.3.2 (automatic for the annealed overlap-array laws of Gibbs measures), the mass of
`{R_{0,1} ≤ -2ε}` tends to `0`. -/
theorem tendsto_negMassLaw (μs : ℕ → Measure (ℕ → ℕ → OverlapValue))
    [∀ N, IsProbabilityMeasure (μs N)] (hex : ∀ N, IsJointlyExchangeable (μs N))
    (hgg : TendstoGGDefectUniform μs) {ε : ℝ} (hε : 0 < ε)
    (hD : ∀ N (m : ℕ), 2 ≤ m → (μs N).real (negSet ε (m + 1))
      ≤ (4 * Real.log ((m : ℝ) + 1) + 1) / (ε * ((m : ℝ) + 1))) :
    Tendsto (fun N => negMassLaw (μs N) ε) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun d hd => Eventually.of_forall fun N =>
    lt_of_lt_of_le hd measureReal_nonneg, fun d hd => ?_⟩
  rcases le_or_gt d 1 with hd1 | hd1
  · obtain ⟨k, hk2, hkgood⟩ := exists_good_k hε hd hd1
    have hk1 : 1 ≤ k := by omega
    have hkpos : 0 < k := hk1
    have hK1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hKpos : (0 : ℝ) < k := by linarith
    set E : ℝ := Real.exp 2 with hE
    have hEpos : 0 < E := Real.exp_pos 2
    have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_exp (by norm_num)
    set η : ℝ := 1 / (E * k * k) with hη
    have hηpos : 0 < η := by positivity
    have hev : ∀ᶠ N in atTop, ∀ j ∈ Finset.Ico 1 k,
        ∀ g : C(Fin (j + 1) → Fin (j + 1) → OverlapValue, ℝ),
          |ggDefect (μs N) (j + 1) (negRamp ε k (j + 1)) g| ≤ η * ‖g‖ :=
      (eventually_all_finset _).2 fun j _ =>
        hgg (j + 1) (Nat.succ_pos j) (negRamp ε k (j + 1)) η hηpos
    filter_upwards [hev] with N hN
    set a := negMassLaw (μs N) ε with ha
    have ha0 : 0 ≤ a := measureReal_nonneg
    have ha1 : a ≤ 1 := measureReal_le_one
    by_contra hcon
    have hda : d ≤ a := not_lt.1 hcon
    -- the accumulated defects
    have hsum : ∑ j ∈ Finset.Ico 1 k,
        |ggDefect (μs N) (j + 1) (negRamp ε k (j + 1)) (negObs ε k j)| ≤ 1 / (E * k) := by
      calc ∑ j ∈ Finset.Ico 1 k, |ggDefect (μs N) (j + 1) (negRamp ε k (j + 1)) (negObs ε k j)|
          ≤ ∑ _j ∈ Finset.Ico 1 k, η :=
            Finset.sum_le_sum fun j hj => (hN j hj (negObs ε k j)).trans
              (by nlinarith [norm_negObs_le ε k j, hηpos, norm_nonneg (negObs ε k j)])
        _ = ((k - 1 : ℕ) : ℝ) * η := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        _ ≤ (k : ℝ) * η := by
            gcongr
            exact_mod_cast Nat.sub_le k 1
        _ = 1 / (E * k) := by rw [hη]; field_simp
    have hiter := negMassLaw_mul_negProd_sub_le (μs N) ε k (hex N) hε hkpos hk1 le_rfl
    have hI := negObsInt_le_real_negSet (μs N) ε k hε hkpos
    have hDk := hD N k hk2
    have hprod := negProd_ge a ha0 ha1 k hk1
    set B : ℝ := (4 * Real.log ((k : ℝ) + 1) + 1) / (ε * ((k : ℝ) + 1)) with hB
    have h1 : a * negProd a k ≤ B + 1 / (E * k) := by linarith
    -- lower bound on `a P_k(a)` and monotonicity in `a`
    have hpow : (k : ℝ) ^ (a - 1) = (k : ℝ) ^ a / k := Real.rpow_sub_one hKpos.ne' a
    have hexp : Real.exp (-2) = E⁻¹ := by rw [hE, Real.exp_neg]
    rw [hexp, hpow] at hprod
    have hmono : d * (k : ℝ) ^ d ≤ a * (k : ℝ) ^ a :=
      mul_le_mul hda (Real.rpow_le_rpow_of_exponent_le hK1 hda) (by positivity) ha0
    have h2 : a * (E⁻¹ * ((k : ℝ) ^ a / k)) ≤ B + 1 / (E * k) :=
      (mul_le_mul_of_nonneg_left hprod ha0).trans h1
    have h3 : a * (k : ℝ) ^ a ≤ (E * k) * B + 1 := by
      have heq : a * (k : ℝ) ^ a = (a * (E⁻¹ * ((k : ℝ) ^ a / k))) * (E * k) := by
        field_simp
      have heq2 : (B + 1 / (E * k)) * (E * k) = (E * k) * B + 1 := by
        field_simp
      rw [heq, ← heq2]
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    have hKB : (k : ℝ) * B ≤ (4 * Real.log ((k : ℝ) + 1) + 1) / ε := by
      rw [hB, mul_div_assoc', div_le_div_iff₀ (by positivity) hε]
      have hl0 : 0 ≤ 4 * Real.log ((k : ℝ) + 1) + 1 := by
        have := Real.log_nonneg (show (1 : ℝ) ≤ (k : ℝ) + 1 by linarith)
        linarith
      nlinarith [hl0, hε, hKpos]
    have h4 : d * (k : ℝ) ^ d ≤ E * ((4 * Real.log ((k : ℝ) + 1) + 1) / ε + 1) := by
      have : (E * k) * B = E * ((k : ℝ) * B) := by ring
      nlinarith [hmono, h3, hKB, hE1, hEpos]
    exact absurd (lt_of_le_of_lt h4 hkgood) (lt_irrefl _)
  · exact Eventually.of_forall fun N => lt_of_le_of_lt measureReal_le_one hd1

end Theorem

/-! ### Consequences: Gibbs array laws, and the limit law -/

section Consequences

/-- **Theorem 12.3.1 for the annealed overlap-array laws of Gibbs measures.** For any sequence of
volumes `N_k` and Hamiltonian laws `ν_k` whose array laws satisfy the extended Ghirlanda–Guerra
identities asymptotically, `P(R_{0,1} ≤ -ε') → 0` for every `ε' > 0`. -/
theorem tendsto_real_negLevel_bind (Ns : ℕ → ℕ) (ν : ∀ k, Measure (EnergySpace (Ns k)))
    [∀ k, IsProbabilityMeasure (ν k)]
    (hgg : TendstoGGDefectUniform fun k => (ν k).bind (overlapArrayLaw (Ns k)))
    {ε' : ℝ} (hε' : 0 < ε') :
    Tendsto (fun k => ((ν k).bind (overlapArrayLaw (Ns k))).real
      {R : ℕ → ℕ → OverlapValue | ((R 0 1 : OverlapValue) : ℝ) ≤ -ε'}) atTop (𝓝 0) := by
  set ε : ℝ := min (ε' / 2) (1 / 2) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have h2ε : 2 * ε ≤ ε' := by
    have := min_le_left (ε' / 2) (1 / 2)
    linarith
  have hprob : ∀ k, IsProbabilityMeasure ((ν k).bind (overlapArrayLaw (Ns k))) := fun k =>
    isProbabilityMeasure_bind (measurable_overlapArrayLaw (Ns k)).aemeasurable
      (Eventually.of_forall fun _ => inferInstance)
  have hex : ∀ k, IsJointlyExchangeable ((ν k).bind (overlapArrayLaw (Ns k))) := fun k =>
    isJointlyExchangeable_bind (measurable_overlapArrayLaw (Ns k))
      fun H => isJointlyExchangeable_overlapArrayLaw (Ns k) H
  have hD : ∀ k (m : ℕ), 2 ≤ m → ((ν k).bind (overlapArrayLaw (Ns k))).real (negSet ε (m + 1))
      ≤ (4 * Real.log ((m : ℝ) + 1) + 1) / (ε * ((m : ℝ) + 1)) := fun k m hm =>
    bind_overlapArrayLaw_real_negSet_le (ν k) hε hε1 hm
  have hlim := tendsto_negMassLaw (fun k => (ν k).bind (overlapArrayLaw (Ns k))) hex hgg hε hD
  refine squeeze_zero (fun k => measureReal_nonneg) (fun k => ?_) hlim
  unfold negMassLaw
  exact measureReal_mono fun R hR => by
    simp only [Set.mem_ofPred_eq] at hR ⊢
    linarith

/-- **Nonnegativity of the overlap in the limit.** If the array laws converge in distribution and
`P(R_{0,1} ≤ -ε') → 0` for every `ε' > 0`, then the limit law gives no mass to `{R_{0,1} < 0}`
(Portmanteau, open sets). -/
theorem measure_negOverlap_eq_zero_of_tendsto {μs : ℕ → ProbabilityMeasure (ℕ → ℕ → OverlapValue)}
    {μ : ProbabilityMeasure (ℕ → ℕ → OverlapValue)} (hlim : Tendsto μs atTop (𝓝 μ))
    (hneg : ∀ ε' : ℝ, 0 < ε' → Tendsto (fun k => (μs k : Measure (ℕ → ℕ → OverlapValue)).real
      {R : ℕ → ℕ → OverlapValue | ((R 0 1 : OverlapValue) : ℝ) ≤ -ε'}) atTop (𝓝 0)) :
    (μ : Measure (ℕ → ℕ → OverlapValue))
      {R : ℕ → ℕ → OverlapValue | ((R 0 1 : OverlapValue) : ℝ) < 0} = 0 := by
  have hopen : ∀ ε' : ℝ, IsOpen {R : ℕ → ℕ → OverlapValue | ((R 0 1 : OverlapValue) : ℝ) < -ε'} :=
    fun ε' => isOpen_lt (continuous_entry 0 1) continuous_const
  have hzero : ∀ ε' : ℝ, 0 < ε' →
      (μ : Measure (ℕ → ℕ → OverlapValue))
        {R : ℕ → ℕ → OverlapValue | ((R 0 1 : OverlapValue) : ℝ) < -ε'} = 0 := by
    intro ε' hε'
    have h1 := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim (hopen ε')
    have h2 : Tendsto (fun k => (μs k : Measure (ℕ → ℕ → OverlapValue))
        {R : ℕ → ℕ → OverlapValue | ((R 0 1 : OverlapValue) : ℝ) ≤ -ε'}) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (hneg ε' hε')
      rw [ENNReal.ofReal_zero] at this
      refine this.congr fun k => ?_
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    have h3 : Filter.liminf (fun k => (μs k : Measure (ℕ → ℕ → OverlapValue))
          {R : ℕ → ℕ → OverlapValue | ((R 0 1 : OverlapValue) : ℝ) < -ε'}) atTop
        ≤ Filter.liminf (fun k => (μs k : Measure (ℕ → ℕ → OverlapValue))
          {R : ℕ → ℕ → OverlapValue | ((R 0 1 : OverlapValue) : ℝ) ≤ -ε'}) atTop :=
      liminf_le_liminf (Eventually.of_forall fun k => measure_mono
        fun R (hR : ((R 0 1 : OverlapValue) : ℝ) < -ε') =>
          show ((R 0 1 : OverlapValue) : ℝ) ≤ -ε' from le_of_lt hR)
    rw [h2.liminf_eq] at h3
    exact le_antisymm (h1.trans h3) zero_le
  have hunion : {R : ℕ → ℕ → OverlapValue | ((R 0 1 : OverlapValue) : ℝ) < 0}
      = ⋃ n : ℕ, {R : ℕ → ℕ → OverlapValue |
          ((R 0 1 : OverlapValue) : ℝ) < -(1 / ((n : ℝ) + 1))} := by
    ext R
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.2 h)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  rw [hunion]
  exact measure_iUnion_null fun n => hzero _ (by positivity)

end Consequences

end

end SpinGlass
