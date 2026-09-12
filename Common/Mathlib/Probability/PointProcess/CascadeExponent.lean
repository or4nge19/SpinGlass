/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Analysis.SpecialFunctions.Pow.ENNRealContinuity
import Common.Mathlib.Probability.PointProcess.Cascade

/-!
# The cascade recursion as a function of the exponents

Talagrand's recursion `F_p = (1/m_p) log 𝔼_p exp (m_p F_{p+1})` (Vol. II, (14.5)), in the `ℝ≥0∞`
form `cascadeRec k ms μs G`, is **nondecreasing in each exponent** `m_p` (Lyapunov's inequality
level by level, `cascadeRec_mono_exponent`) and **continuous on `(0, 1]^k`** under Talagrand's
hypothesis (14.4) `∫ G d(μ₁ ⊗ ⋯ ⊗ μ_k) < ∞` (`continuousOn_cascadeRec`: dominated convergence
level by level, the dominating function `1 + ∫ G(z, ·)` coming from the Jensen bound
`cascadeRec_le_lintegral_pi`, and the joint continuity `ENNReal.continuousAt_rpow`).
`parisiRec_mono_exponent` and `continuousOn_parisiRec` are the real forms. This is the
continuity Talagrand invokes after (14.145) to extend his bounds from `0 < n₁ < ⋯ < n_κ < 1`
to `0 < n₁ ≤ ⋯ ≤ n_κ ≤ 1`.
-/

open MeasureTheory Set Filter Function Topology
open scoped ENNReal

namespace ProbabilityTheory

open ENNReal

universe u

noncomputable section

variable {T : Type u} [MeasurableSpace T]

/-! ### Monotonicity in the exponents -/

/-- **The recursion is nondecreasing in each exponent**: `ms ≤ ms'` pointwise, `ms` positive,
gives `cascadeRec k ms μs G ≤ cascadeRec k ms' μs G` (Lyapunov's inequality level by level). -/
theorem cascadeRec_mono_exponent (k : ℕ) :
    ∀ (ms ms' : Fin k → ℝ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
      {G : (Fin k → T) → ℝ≥0∞}, Measurable G → (∀ i, 0 < ms i) → ms ≤ ms' →
      cascadeRec k ms μs G ≤ cascadeRec k ms' μs G := by
  induction k with
  | zero =>
    intro ms ms' μs _ G _ _ _
    rw [cascadeRec_zero, cascadeRec_zero]
  | succ k ih =>
    intro ms ms' μs _ G hG hpos hle
    have hm : 0 < ms 0 := hpos 0
    have hR' : Measurable fun z => cascadeRec k (Fin.tail ms') (Fin.tail μs)
        (fun zs => G (Fin.cons z zs)) := measurable_cascadeRec_cons k _ _ hG
    rw [cascadeRec_succ, cascadeRec_succ]
    calc (∫⁻ z, cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
            ∂μs 0) ^ (1 / ms 0)
        ≤ (∫⁻ z, cascadeRec k (Fin.tail ms') (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
            ∂μs 0) ^ (1 / ms 0) := by
          refine ENNReal.rpow_le_rpow (lintegral_mono fun z => ENNReal.rpow_le_rpow ?_ hm.le)
            (by positivity)
          exact ih (Fin.tail ms) (Fin.tail ms') (Fin.tail μs)
            (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
            (fun i => hpos i.succ) (fun i => hle i.succ)
      _ ≤ (∫⁻ z, cascadeRec k (Fin.tail ms') (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms' 0
            ∂μs 0) ^ (1 / ms' 0) :=
          lintegral_rpow_rpow_inv_le_of_le (μs 0) hR'.aemeasurable hm (hle 0)

/-! ### Continuity in the exponents -/

/-- **The recursion is continuous in the exponents on `(0, 1]^k`** under Talagrand's hypothesis
(14.4), `∫ G d(μ₁ ⊗ ⋯ ⊗ μ_k) < ∞`. -/
theorem continuousOn_cascadeRec (k : ℕ) :
    ∀ (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)] {G : (Fin k → T) → ℝ≥0∞},
      Measurable G → ∫⁻ zs, G zs ∂Measure.pi μs ≠ ∞ →
      ContinuousOn (fun ms => cascadeRec k ms μs G) (pi univ fun _ => Ioc (0 : ℝ) 1) := by
  induction k with
  | zero =>
    intro μs _ G _ _
    exact continuousOn_const
  | succ k ih =>
    intro μs _ G hG hfin ms₀ hms₀
    simp only [mem_univ_pi, mem_Ioc] at hms₀
    have hGz : ∀ z, Measurable fun zs => G (Fin.cons z zs) := fun z =>
      hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id))
    have hRm : ∀ ms : Fin (k + 1) → ℝ, Measurable fun z => cascadeRec k (Fin.tail ms)
        (Fin.tail μs) (fun zs => G (Fin.cons z zs)) :=
      fun ms => measurable_cascadeRec_cons k _ _ hG
    have hĜm : Measurable fun z => ∫⁻ zs, G (Fin.cons z zs) ∂Measure.pi (Fin.tail μs) :=
      Measurable.lintegral_prod_right' (hG.comp measurable_fin_cons)
    have hĜfin : ∫⁻ z, ∫⁻ zs, G (Fin.cons z zs) ∂Measure.pi (Fin.tail μs) ∂μs 0 ≠ ∞ := by
      rwa [lintegral_pi_fin_succ μs hG] at hfin
    -- domination, uniform in the exponents: `R^m ≤ (∫ G(z, ·))^m ≤ 1 + ∫ G(z, ·)`
    have hdom : ∀ ms ∈ (pi univ fun _ : Fin (k + 1) => Ioc (0 : ℝ) 1), ∀ z,
        cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
          ≤ 1 + ∫⁻ zs, G (Fin.cons z zs) ∂Measure.pi (Fin.tail μs) := by
      intro ms hms z
      simp only [mem_univ_pi, mem_Ioc] at hms
      have h1 := cascadeRec_le_lintegral_pi k (Fin.tail ms) (Fin.tail μs) (hGz z)
        (fun i => (hms i.succ).1) (fun i => (hms i.succ).2)
      refine (ENNReal.rpow_le_rpow h1 (hms 0).1.le).trans ?_
      rcases le_total (∫⁻ zs, G (Fin.cons z zs) ∂Measure.pi (Fin.tail μs)) 1 with h | h
      · exact ((ENNReal.rpow_le_rpow h (hms 0).1.le).trans_eq (ENNReal.one_rpow _)).trans
          le_self_add
      · calc (∫⁻ zs, G (Fin.cons z zs) ∂Measure.pi (Fin.tail μs)) ^ ms 0
            ≤ (∫⁻ zs, G (Fin.cons z zs) ∂Measure.pi (Fin.tail μs)) ^ (1 : ℝ) :=
              ENNReal.rpow_le_rpow_of_exponent_le h (hms 0).2
          _ ≤ 1 + ∫⁻ zs, G (Fin.cons z zs) ∂Measure.pi (Fin.tail μs) := by
              rw [ENNReal.rpow_one]
              exact le_add_self
    -- the tail exponents move within `(0, 1]^k`
    have htail : Tendsto (fun ms : Fin (k + 1) → ℝ => Fin.tail ms)
        (𝓝[pi univ fun _ => Ioc (0 : ℝ) 1] ms₀)
        (𝓝[pi univ fun _ : Fin k => Ioc (0 : ℝ) 1] (Fin.tail ms₀)) := by
      refine (continuous_pi fun i => continuous_apply i.succ).continuousWithinAt.tendsto_nhdsWithin
        fun ms hms => ?_
      simp only [mem_univ_pi, mem_Ioc] at hms ⊢
      exact fun i => hms i.succ
    have h0 : Tendsto (fun ms : Fin (k + 1) → ℝ => ms 0)
        (𝓝[pi univ fun _ => Ioc (0 : ℝ) 1] ms₀) (𝓝 (ms₀ 0)) :=
      tendsto_nhdsWithin_of_tendsto_nhds ((continuous_apply 0).tendsto ms₀)
    -- pointwise convergence at a.e. `z` (where `∫ G(z, ·) < ∞`), from the induction hypothesis
    have hlim : ∀ᵐ z ∂μs 0, Tendsto (fun ms : Fin (k + 1) → ℝ =>
        cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0)
        (𝓝[pi univ fun _ => Ioc (0 : ℝ) 1] ms₀)
        (𝓝 (cascadeRec k (Fin.tail ms₀) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms₀ 0)) := by
      filter_upwards [ae_lt_top hĜm hĜfin] with z hz
      have hc := ih (Fin.tail μs) (hGz z) hz.ne (Fin.tail ms₀)
        (by simp only [mem_univ_pi, mem_Ioc]; exact fun i => hms₀ i.succ)
      exact (hc.tendsto.comp htail).ennrpow h0 (Or.inr (hms₀ 0).1.ne')
    have hI : Tendsto (fun ms : Fin (k + 1) → ℝ => ∫⁻ z, cascadeRec k (Fin.tail ms) (Fin.tail μs)
        (fun zs => G (Fin.cons z zs)) ^ ms 0 ∂μs 0)
        (𝓝[pi univ fun _ => Ioc (0 : ℝ) 1] ms₀)
        (𝓝 (∫⁻ z, cascadeRec k (Fin.tail ms₀) (Fin.tail μs)
          (fun zs => G (Fin.cons z zs)) ^ ms₀ 0 ∂μs 0)) := by
      refine tendsto_lintegral_filter_of_dominated_convergence
        (fun z => 1 + ∫⁻ zs, G (Fin.cons z zs) ∂Measure.pi (Fin.tail μs))
        (Eventually.of_forall fun ms => (hRm ms).pow_const _)
        (eventually_nhdsWithin_of_forall fun ms hms => Eventually.of_forall (hdom ms hms)) ?_ hlim
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hĜfin⟩
    have hinv : Tendsto (fun ms : Fin (k + 1) → ℝ => 1 / ms 0)
        (𝓝[pi univ fun _ => Ioc (0 : ℝ) 1] ms₀) (𝓝 (1 / ms₀ 0)) :=
      tendsto_const_nhds.div h0 (hms₀ 0).1.ne'
    exact hI.ennrpow hinv (Or.inr (one_div_pos.2 (hms₀ 0).1).ne')

/-! ### Talagrand's form -/

/-- **Talagrand's `F₁` is nondecreasing in each exponent.** -/
theorem parisiRec_mono_exponent (k : ℕ) (ms ms' : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {F : (Fin k → T) → ℝ} (hF : Measurable F)
    (hpos : ∀ i, 0 < ms i) (hle : ms ≤ ms')
    (hfin : cascadeRec k ms' μs (fun zs => ENNReal.ofReal (Real.exp (F zs))) ≠ ∞) :
    parisiRec k ms μs F ≤ parisiRec k ms' μs F := by
  have hG : Measurable fun zs : Fin k → T => ENNReal.ofReal (Real.exp (F zs)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hF)
  have hmono := cascadeRec_mono_exponent k ms ms' μs hG hpos hle
  have hpos' : 0 < cascadeRec k ms μs (fun zs => ENNReal.ofReal (Real.exp (F zs))) :=
    cascadeRec_pos k ms μs hG (fun zs => ENNReal.ofReal_pos.2 (Real.exp_pos _)) hpos
  exact Real.log_le_log (ENNReal.toReal_pos hpos'.ne' (ne_top_of_le_ne_top hfin hmono))
    (ENNReal.toReal_mono hfin hmono)

/-- **Talagrand's `F₁` is continuous in the exponents on `(0, 1]^k`** under (14.4). -/
theorem continuousOn_parisiRec (k : ℕ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {F : (Fin k → T) → ℝ} (hF : Measurable F)
    (hfin : ∫⁻ zs, ENNReal.ofReal (Real.exp (F zs)) ∂Measure.pi μs ≠ ∞) :
    ContinuousOn (fun ms => parisiRec k ms μs F) (pi univ fun _ => Ioc (0 : ℝ) 1) := by
  have hG : Measurable fun zs : Fin k → T => ENNReal.ofReal (Real.exp (F zs)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hF)
  have hne : ∀ ms ∈ (pi univ fun _ : Fin k => Ioc (0 : ℝ) 1),
      cascadeRec k ms μs (fun zs => ENNReal.ofReal (Real.exp (F zs))) ≠ ∞ := by
    intro ms hms
    simp only [mem_univ_pi, mem_Ioc] at hms
    exact ne_top_of_le_ne_top hfin
      (cascadeRec_le_lintegral_pi k ms μs hG (fun i => (hms i).1) (fun i => (hms i).2))
  have hpos : ∀ ms ∈ (pi univ fun _ : Fin k => Ioc (0 : ℝ) 1),
      0 < cascadeRec k ms μs (fun zs => ENNReal.ofReal (Real.exp (F zs))) := by
    intro ms hms
    simp only [mem_univ_pi, mem_Ioc] at hms
    exact cascadeRec_pos k ms μs hG (fun zs => ENNReal.ofReal_pos.2 (Real.exp_pos _))
      (fun i => (hms i).1)
  have h1 : ContinuousOn (fun ms => (cascadeRec k ms μs
      (fun zs => ENNReal.ofReal (Real.exp (F zs)))).toReal) (pi univ fun _ => Ioc (0 : ℝ) 1) :=
    ENNReal.continuousOn_toReal.comp (continuousOn_cascadeRec k μs hG hfin)
      fun ms hms => hne ms hms
  exact Real.continuousOn_log.comp h1 fun ms hms =>
    (ENNReal.toReal_pos (hpos ms hms).ne' (hne ms hms)).ne'

/-! ### Talagrand's density argument -/

/-- Strictly increasing approximants `m_p (1 − (k − p)/(k (j + 2)))` of a nondecreasing tuple
`m ∈ (0, 1]^k`: they lie in `(0, 1)^k`, are nondecreasing in `j` and converge to `m`. -/
def strictApprox (k : ℕ) (ms : Fin k → ℝ) (j : ℕ) : Fin k → ℝ :=
  fun p => ms p * (1 - ((k : ℝ) - p) / ((k : ℝ) * (j + 2)))

section strictApprox

variable {k : ℕ} {ms : Fin k → ℝ}

/-- The correction `(k − p)/(k (j + 2))` lies in `(0, 1/2]`. -/
lemma strictApprox_aux (p : Fin k) (j : ℕ) :
    0 < ((k : ℝ) - p) / ((k : ℝ) * (j + 2)) ∧ ((k : ℝ) - p) / ((k : ℝ) * (j + 2)) ≤ 1 / 2 := by
  have hk : (0 : ℝ) < k := by exact_mod_cast p.pos
  have hp : (p : ℝ) < k := by exact_mod_cast p.isLt
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  constructor
  · exact div_pos (by linarith) (mul_pos hk (by positivity))
  · rw [div_le_iff₀ (mul_pos hk (by positivity))]
    nlinarith [mul_nonneg hk.le hj]

lemma strictApprox_pos (hpos : ∀ p, 0 < ms p) (j : ℕ) (p : Fin k) :
    0 < strictApprox k ms j p := by
  have h := strictApprox_aux p j
  exact mul_pos (hpos p) (by linarith [h.2])

lemma strictApprox_le (hpos : ∀ p, 0 < ms p) (j : ℕ) : strictApprox k ms j ≤ ms := fun p => by
  have h := strictApprox_aux p j
  exact mul_le_of_le_one_right (hpos p).le (by linarith [h.1])

lemma strictApprox_lt_one (hle : ∀ p, ms p ≤ 1) (j : ℕ) (p : Fin k) :
    strictApprox k ms j p < 1 := by
  have h := strictApprox_aux p j
  calc strictApprox k ms j p ≤ 1 * (1 - ((k : ℝ) - p) / ((k : ℝ) * (j + 2))) :=
        mul_le_mul_of_nonneg_right (hle p) (by linarith [h.2])
    _ < 1 := by linarith [h.1]

lemma strictApprox_strictMono (hmono : Monotone ms) (hpos : ∀ p, 0 < ms p) (j : ℕ) :
    StrictMono (strictApprox k ms j) := by
  intro p q hpq
  have hq := strictApprox_aux q j
  have hk : (0 : ℝ) < k := by exact_mod_cast p.pos
  have hpq' : ((p : ℕ) : ℝ) < q := by exact_mod_cast (Fin.lt_def.1 hpq)
  have hx : ((k : ℝ) - q) / ((k : ℝ) * (j + 2)) < ((k : ℝ) - p) / ((k : ℝ) * (j + 2)) :=
    div_lt_div_of_pos_right (by linarith) (mul_pos hk (by positivity))
  calc strictApprox k ms j p = ms p * (1 - ((k : ℝ) - p) / ((k : ℝ) * (j + 2))) := rfl
    _ < ms p * (1 - ((k : ℝ) - q) / ((k : ℝ) * (j + 2))) :=
        mul_lt_mul_of_pos_left (by linarith) (hpos p)
    _ ≤ ms q * (1 - ((k : ℝ) - q) / ((k : ℝ) * (j + 2))) :=
        mul_le_mul_of_nonneg_right (hmono hpq.le) (by linarith [hq.2])

lemma monotone_strictApprox (hpos : ∀ p, 0 < ms p) : Monotone (strictApprox k ms) := by
  intro i j hij p
  have hk : (0 : ℝ) < k := by exact_mod_cast p.pos
  have hp : (p : ℝ) < k := by exact_mod_cast p.isLt
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hx : ((k : ℝ) - p) / ((k : ℝ) * (j + 2)) ≤ ((k : ℝ) - p) / ((k : ℝ) * (i + 2)) :=
    div_le_div_of_nonneg_left (by linarith) (mul_pos hk (by positivity))
      (mul_le_mul_of_nonneg_left (by linarith) hk.le)
  exact mul_le_mul_of_nonneg_left (by linarith) (hpos p).le

lemma tendsto_strictApprox (k : ℕ) (ms : Fin k → ℝ) :
    Tendsto (strictApprox k ms) atTop (𝓝 ms) := by
  rw [tendsto_pi_nhds]
  intro p
  have h1 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 2)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
    refine h.congr fun j => ?_
    simp only [Function.comp, Nat.cast_add, Nat.cast_one]
    ring
  have h2 : Tendsto (fun j : ℕ => ms p * (1 - ((k : ℝ) - p) / k * (1 / ((j : ℝ) + 2)))) atTop
      (𝓝 (ms p * (1 - ((k : ℝ) - p) / k * 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub (tendsto_const_nhds.mul h1))
  rw [mul_zero, sub_zero, mul_one] at h2
  refine h2.congr fun j => ?_
  simp only [strictApprox]
  rw [div_mul_div_comm, mul_one]

lemma tendsto_strictApprox_nhdsWithin (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1) :
    Tendsto (strictApprox k ms) atTop (𝓝[pi univ fun _ => Ioc (0 : ℝ) 1] ms) := by
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_strictApprox k ms, Eventually.of_forall fun j => ?_⟩
  simp only [mem_univ_pi, mem_Ioc]
  exact fun p => ⟨strictApprox_pos hpos j p, (strictApprox_lt_one hle j p).le⟩

end strictApprox

/-- **Talagrand's density argument** (Vol. II, after (14.145)): an inequality `f ≤ g` between
functions of the exponents that are continuous on `(0, 1]^k` and holds at every strictly
increasing tuple in `(0, 1)^k` holds at every nondecreasing tuple in `(0, 1]^k`. -/
theorem le_of_forall_strictMono_le {k : ℕ} {f g : (Fin k → ℝ) → ℝ}
    (hf : ContinuousOn f (pi univ fun _ => Ioc (0 : ℝ) 1))
    (hg : ContinuousOn g (pi univ fun _ => Ioc (0 : ℝ) 1))
    (h : ∀ ms : Fin k → ℝ, StrictMono ms → (∀ i, 0 < ms i) → (∀ i, ms i < 1) → f ms ≤ g ms)
    {ms : Fin k → ℝ} (hmono : Monotone ms) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) :
    f ms ≤ g ms := by
  have hmem : ms ∈ (pi univ fun _ : Fin k => Ioc (0 : ℝ) 1) := by
    simp only [mem_univ_pi, mem_Ioc]
    exact fun i => ⟨hpos i, hle i⟩
  have hT := tendsto_strictApprox_nhdsWithin hpos hle
  exact le_of_tendsto_of_tendsto' ((hf ms hmem).tendsto.comp hT) ((hg ms hmem).tendsto.comp hT)
    fun j => h _ (strictApprox_strictMono hmono hpos j) (strictApprox_pos hpos j)
      (strictApprox_lt_one hle j)

end

end ProbabilityTheory
