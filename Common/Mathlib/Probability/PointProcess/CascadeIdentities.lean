/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.PointProcess.Cascade
import Common.Mathlib.Probability.PointProcess.PoissonDirichletIdentities

/-!
# The fundamental identities of the Poisson–Dirichlet cascades (Proposition 14.3.3)

Talagrand, *Mean Field Models for Spin Glasses*, Vol. II, §14.3. For a `k`-level cascade with
parameters `0 = m₀ < m₁ < ⋯ < m_k < m_{k+1} = 1`, two branches `α, γ ∈ ℕ^{*k}` first differ at
the level `(α, γ) ∈ {1, …, k+1}` (with the convention that `(α, α) = k + 1`), and
**Proposition 14.3.3** (14.38) states that, for the cascade Gibbs average with any weights
`exp F(α)`,

`𝔼 ⟨1_{(α,γ) = r}⟩ = m_r - m_{r-1}`.

Since `1_{α|(r-1) = γ|(r-1)} - 1_{α|r = γ|r} = 1_{(α,γ) = r}`, this is equivalent to
`𝔼 ⟨1_{α|r = γ|r}⟩ = 1 - m_r` for `0 ≤ r ≤ k + 1`, where `⟨1_{α|r = γ|r}⟩ = Q_r / S²` and

`Q_r = ∑_{|β| = r} (∑_{α ⊇ β} u*_α G(α))²`

is the sum over the prefixes of length `r` of the squared partial sums (`cascadeSq`). The `Q_r`
are built by the same recursion as the cascade sums, and the identity follows by induction on the
number of levels from the identity (13.14) with a general exponent
(`lintegral_pdSumSq_mul_rpow_pdSum`) and the moments of Proposition 14.2.2, through the mixed
moments

`𝔼 Q_r S^{a-2} = (1 - m_r)/(1 - a) · 𝔼 S^a`  (`0 < a < m₁`),

with no differentiation in Talagrand's parameter `t`.

## Main statements

- `ProbabilityTheory.cascadeSq`, `ProbabilityTheory.mExt`.
- `ProbabilityTheory.lintegral_cascadeSq_mul_rpow`: the mixed moments.
- `ProbabilityTheory.lintegral_cascadeSq_mul_inv_sq`: `𝔼 Q_r / S² = 1 - m_r`.
- `ProbabilityTheory.lintegral_cascadePairIndicator`: **Proposition 14.3.3**,
  `𝔼 ⟨1_{(α,γ) = r}⟩ = m_r - m_{r-1}`.
-/

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace ProbabilityTheory

open ENNReal

universe u

noncomputable section

variable {T : Type u} [MeasurableSpace T]

/-! ### The prefix sums of squares -/

/-- `Q_r = ∑_{|β| = r} (∑_{α ⊇ β} u*_α G(α))²`: the sum over the prefixes of length `r` of the
squared partial sums of the cascade; `Q_0 = S²` and `Q_r = 0` for `r > k`. -/
def cascadeSq : (k : ℕ) → ℕ → ((Fin k → T) → ℝ≥0∞) → CascadeSpace T k → ℝ≥0∞
  | k, 0, G, ω => cascadeSum k G ω * cascadeSum k G ω
  | 0, _ + 1, _, _ => 0
  | k + 1, r + 1, G, ω =>
    ∫⁻ p : ℝ × (T × CascadeSpace T k), ENNReal.ofReal p.1 * ENNReal.ofReal p.1
      * cascadeSq k r (fun zs => G (Fin.cons p.2.1 zs)) p.2.2 ∂superCounting ω

lemma cascadeSq_zero (k : ℕ) (G : (Fin k → T) → ℝ≥0∞) (ω : CascadeSpace T k) :
    cascadeSq k 0 G ω = cascadeSum k G ω * cascadeSum k G ω := by
  cases k <;> rfl

lemma cascadeSq_zero_succ (r : ℕ) (G : (Fin 0 → T) → ℝ≥0∞) (ω : CascadeSpace T 0) :
    cascadeSq 0 (r + 1) G ω = 0 := rfl

lemma cascadeSq_succ (k r : ℕ) (G : (Fin (k + 1) → T) → ℝ≥0∞) (ω : CascadeSpace T (k + 1)) :
    cascadeSq (k + 1) (r + 1) G ω
      = ∫⁻ p : ℝ × (T × CascadeSpace T k), ENNReal.ofReal p.1 * ENNReal.ofReal p.1
          * cascadeSq k r (fun zs => G (Fin.cons p.2.1 zs)) p.2.2 ∂superCounting ω := rfl

/-- Joint measurability of `Q_r` in a parameter and the sample. -/
lemma measurable_cascadeSq_prod (k : ℕ) :
    ∀ (r : ℕ) {α : Type u} [MeasurableSpace α] {G : α → (Fin k → T) → ℝ≥0∞},
      Measurable (uncurry G) →
        Measurable fun q : α × CascadeSpace T k => cascadeSq k r (G q.1) q.2 := by
  induction k with
  | zero =>
    intro r α _ G hG
    cases r with
    | zero =>
      simp only [cascadeSq_zero]
      exact (measurable_cascadeSum_prod 0 hG).mul (measurable_cascadeSum_prod 0 hG)
    | succ r =>
      simp only [cascadeSq_zero_succ]
      exact measurable_const
  | succ k ih =>
    intro r α _ G hG
    cases r with
    | zero =>
      simp only [cascadeSq_zero]
      exact (measurable_cascadeSum_prod _ hG).mul (measurable_cascadeSum_prod _ hG)
    | succ r =>
      simp only [cascadeSq_succ]
      have hG' : Measurable fun q : (α × T) × (Fin k → T) => G q.1.1 (Fin.cons q.1.2 q.2) :=
        hG.comp ((measurable_fst.comp measurable_fst).prodMk
          (measurable_fin_cons.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
      have h1 := ih r (α := α × T) (G := fun q zs => G q.1 (Fin.cons q.2 zs)) hG'
      have hf : Measurable fun q : α × (ℝ × (T × CascadeSpace T k)) =>
          ENNReal.ofReal q.2.1 * ENNReal.ofReal q.2.1
            * cascadeSq k r (fun zs => G q.1 (Fin.cons q.2.2.1 zs)) q.2.2.2 := by
        refine ((ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_snd)).mul
          (ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_snd))).mul ?_
        exact h1.comp ((measurable_fst.prodMk (measurable_fst.comp
          (measurable_snd.comp measurable_snd))).prodMk (measurable_snd.comp
            (measurable_snd.comp measurable_snd)))
      exact measurable_lintegral_superCounting_prod hf

/-! ### The extended sequence of parameters -/

/-- The extended sequence `m₀ = 0, m₁, …, m_k, m_{k+1} = 1, 1, …` of Talagrand's convention
(14.69): `mExt ms r` is `m_r`. -/
def mExt {k : ℕ} (ms : Fin k → ℝ) (r : ℕ) : ℝ :=
  if r = 0 then 0 else if h : r - 1 < k then ms ⟨r - 1, h⟩ else 1

/-- The extended sequence with the level-`0` value replaced by an exponent `a`. -/
def mExt' {k : ℕ} (ms : Fin k → ℝ) (a : ℝ) (r : ℕ) : ℝ := if r = 0 then a else mExt ms r

@[simp] lemma mExt_zero {k : ℕ} (ms : Fin k → ℝ) : mExt ms 0 = 0 := by simp [mExt]

@[simp] lemma mExt'_zero {k : ℕ} (ms : Fin k → ℝ) (a : ℝ) : mExt' ms a 0 = a := by simp [mExt']

lemma mExt'_succ_eq {k : ℕ} (ms : Fin k → ℝ) (a : ℝ) (r : ℕ) :
    mExt' ms a (r + 1) = mExt ms (r + 1) := by simp [mExt']

lemma mExt'_zero_exp {k : ℕ} (ms : Fin k → ℝ) (r : ℕ) : mExt' ms 0 r = mExt ms r := by
  rcases r with _ | r <;> simp [mExt', mExt]

lemma mExt_one {k : ℕ} (ms : Fin (k + 1) → ℝ) : mExt ms 1 = ms 0 := by
  simp [mExt]

lemma mExt_succ_tail {k : ℕ} (ms : Fin (k + 1) → ℝ) (r : ℕ) :
    mExt ms (r + 2) = mExt (Fin.tail ms) (r + 1) := by
  change mExt ms (r + 1 + 1) = mExt (Fin.tail ms) (r + 1)
  unfold mExt
  simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.add_lt_add_iff_right]
  split_ifs <;> rfl

lemma mExt'_succ {k : ℕ} (ms : Fin (k + 1) → ℝ) (a : ℝ) (r : ℕ) :
    mExt' ms a (r + 1) = mExt' (Fin.tail ms) (ms 0) r := by
  rcases r with _ | r
  · simp [mExt', mExt_one]
  · rw [mExt'_succ_eq, mExt'_succ_eq, mExt_succ_tail]

lemma mExt_of_zero_lt {ms : Fin 0 → ℝ} {r : ℕ} (hr : r ≠ 0) : mExt ms r = 1 := by
  simp [mExt, hr]

lemma mExt_le_one {k : ℕ} {ms : Fin k → ℝ} (hlt : ∀ i, ms i ≤ 1) (r : ℕ) : mExt ms r ≤ 1 := by
  unfold mExt
  split_ifs
  · exact zero_le_one
  · exact hlt _
  · exact le_rfl

lemma mExt_nonneg {k : ℕ} {ms : Fin k → ℝ} (hpos : ∀ i, 0 ≤ ms i) (r : ℕ) : 0 ≤ mExt ms r := by
  unfold mExt
  split_ifs
  · exact le_rfl
  · exact hpos _
  · exact zero_le_one

lemma mExt'_le_one {k : ℕ} {ms : Fin k → ℝ} (hlt : ∀ i, ms i ≤ 1) {a : ℝ} (ha : a ≤ 1) (r : ℕ) :
    mExt' ms a r ≤ 1 := by
  rcases r with _ | r
  · simpa using ha
  · rw [mExt'_succ_eq]; exact mExt_le_one hlt _

/-! ### The mixed moments -/

variable [Nonempty T]

/-- **The mixed moments of the prefix sums of squares**: for `0 ≤ a < m₁`,
`𝔼 Q_r S^{a-2} = (1 - m_r)/(1 - a) · 𝔼 S^a`, where `m_0` is replaced by `a`. -/
theorem lintegral_cascadeSq_mul_rpow (k : ℕ) :
    ∀ (ms : Fin k → ℝ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
      {G : (Fin k → T) → ℝ≥0∞}, Measurable G → (∀ zs, 0 < G zs) → StrictMono ms →
      (∀ i, ms i < 1) → ∀ {a : ℝ}, 0 ≤ a → a < 1 → (∀ i, a < ms i) →
      cascadeRec k ms μs G ≠ ∞ → ∀ r : ℕ,
      ∫⁻ ω, cascadeSq k r G ω * cascadeSum k G ω ^ (a - 2) ∂cascadeLaw k ms μs
        = ENNReal.ofReal ((1 - mExt' ms a r) / (1 - a))
          * ∫⁻ ω, cascadeSum k G ω ^ a ∂cascadeLaw k ms μs := by
  induction k with
  | zero =>
    intro ms μs _ G hG hGpos _ _ a ha0 ha1 _ hfin r
    have hg0 : 0 < G Fin.elim0 := hGpos _
    have hgfin : G Fin.elim0 ≠ ∞ := by simpa using hfin
    rcases r with _ | r
    · simp only [cascadeSq_zero, cascadeSum_zero, mExt'_zero, div_self (by linarith :
        (1 : ℝ) - a ≠ 0), ENNReal.ofReal_one, one_mul]
      refine lintegral_congr fun _ => ?_
      rw [← sq, ← ENNReal.rpow_two, ← ENNReal.rpow_add _ _ hg0.ne' hgfin]
      norm_num
    · simp only [cascadeSq_zero_succ, zero_mul, lintegral_zero, mExt'_succ_eq,
        mExt_of_zero_lt (Nat.succ_ne_zero r), sub_self, zero_div, ENNReal.ofReal_zero]
  | succ k ih =>
    intro ms μs _ G hG hGpos hsm hlt a ha0 ha1 ham hfin r
    have hm : 0 < ms 0 := lt_of_le_of_lt ha0 (ham 0)
    have hm1 : ms 0 < 1 := hlt 0
    have ham0 : a < ms 0 := ham 0
    have hsm' : StrictMono (Fin.cons (ms 0) (Fin.tail ms) : Fin (k + 1) → ℝ) := by
      rw [Fin.cons_self_tail]; exact hsm
    -- the weights on the marks
    set v : T × CascadeSpace T k → ℝ≥0∞ :=
      fun p => cascadeSum k (fun zs => G (Fin.cons p.1 zs)) p.2 with hv_def
    have hv : Measurable v :=
      measurable_cascadeSum_prod k (α := T) (G := fun z zs => G (Fin.cons z zs))
        (hG.comp measurable_fin_cons)
    have hlaw := hasLaw_superCounting_cascadeLaw k ms μs
    have hsum : ∀ ω, cascadeSum (k + 1) G ω = pdSum v (superCounting ω) := fun ω => rfl
    have hR : Measurable fun z => cascadeRec k (Fin.tail ms) (Fin.tail μs)
        (fun zs => G (Fin.cons z zs)) := measurable_cascadeRec_cons k _ _ hG
    -- the `m₁`-th moment of the weights
    have hκ : ∫⁻ p, v p ^ ms 0 ∂(μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs))
        = cascadeConst k (ms 0) (Fin.tail ms) * cascadeRec (k + 1) ms μs G ^ ms 0 := by
      rw [lintegral_prod _ (hv.pow_const _).aemeasurable]
      have hpt : ∀ z, ∫⁻ ω', v (z, ω') ^ ms 0 ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
          = cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
            * cascadeConst k (ms 0) (Fin.tail ms) := fun z =>
        lintegral_cascadeSum_rpow k (Fin.tail ms) (Fin.tail μs)
          (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
          hm hsm' (fun i => hlt i.succ)
      simp_rw [hpt]
      rw [lintegral_mul_const _ (hR.pow_const _), cascadeRec_succ, ← ENNReal.rpow_mul,
        one_div_mul_cancel hm.ne', ENNReal.rpow_one, mul_comm]
    obtain ⟨hC, hC'⟩ := cascadeConst_pos_ne_top k hm hsm' (fun i => hlt i.succ)
    have hκfin : ∫⁻ p, v p ^ ms 0 ∂(μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs))
        ≠ ∞ := by
      rw [hκ]
      exact ENNReal.mul_ne_top hC' (ENNReal.rpow_ne_top_of_nonneg hm.le hfin)
    have hvpos : ∀ᵐ p ∂(μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs)), 0 < v p := by
      rw [Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const hv)]
      exact Filter.Eventually.of_forall fun z => ae_cascadeSum_pos k (Fin.tail ms) (Fin.tail μs)
        (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (fun zs => hGpos _) (fun i => pos_of_strictMono_cons hm hsm' i)
    rcases r with _ | r
    · -- `Q₀ = S²`
      simp only [cascadeSq_zero, hsum, mExt'_zero,
        div_self (by linarith : (1 : ℝ) - a ≠ 0), ENNReal.ofReal_one, one_mul]
      refine lintegral_congr_ae ?_
      filter_upwards [hlaw.ae_pdSum_pos hm hv hvpos, hlaw.ae_pdSum_lt_top hm hm1 hv hκfin]
        with ω h1 h2
      rw [← sq, ← ENNReal.rpow_two, ← ENNReal.rpow_add _ _ h1.ne' h2.ne]
      norm_num
    · -- `Q_{r+1} = ∑_j u_j² Q_r^{(j)}`
      set A : T × CascadeSpace T k → ℝ≥0∞ :=
        fun p => cascadeSq k r (fun zs => G (Fin.cons p.1 zs)) p.2 with hA_def
      have hA : Measurable A :=
        measurable_cascadeSq_prod k r (α := T) (G := fun z zs => G (Fin.cons z zs))
          (hG.comp measurable_fin_cons)
      have hQ : ∀ ω, cascadeSq (k + 1) (r + 1) G ω
          = ∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * A p.2 ∂superCounting ω :=
        fun ω => rfl
      simp_rw [hQ, hsum]
      have hUW : Measurable fun p : ℝ × (T × CascadeSpace T k) =>
          ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * A p.2 :=
        ((ENNReal.measurable_ofReal.comp measurable_fst).mul
          (ENNReal.measurable_ofReal.comp measurable_fst)).mul (hA.comp measurable_snd)
      have hmeas : Measurable fun N : Measure (ℝ × (T × CascadeSpace T k)) =>
          (∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1 * A p.2 ∂N) * pdSum v N ^ (a - 2) :=
        (Measure.measurable_lintegral hUW).mul ((measurable_pdSum hv).pow_const _)
      rw [hlaw.lintegral_comp hmeas.aemeasurable,
        hlaw.lintegral_comp ((measurable_pdSum hv).pow_const a).aemeasurable,
        lintegral_pdSumSq_mul_rpow_pdSum hm hm1 _ hA hv hvpos hκfin ham0]
      -- the induction hypothesis on the sub-cascades
      have hRfin : ∀ᵐ z ∂μs 0, cascadeRec k (Fin.tail ms) (Fin.tail μs)
          (fun zs => G (Fin.cons z zs)) ≠ ∞ := by
        have hint : ∫⁻ z, cascadeRec k (Fin.tail ms) (Fin.tail μs)
            (fun zs => G (Fin.cons z zs)) ^ ms 0 ∂μs 0 ≠ ∞ := by
          intro h
          rw [cascadeRec_succ, h, ENNReal.top_rpow_of_pos (by positivity)] at hfin
          exact hfin rfl
        filter_upwards [ae_lt_top (hR.pow_const _) hint] with z hz
        intro h
        rw [h, ENNReal.top_rpow_of_pos hm] at hz
        exact lt_irrefl _ hz
      have hinner : ∫⁻ g, A g * v g ^ (ms 0 - 2)
            ∂(μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs))
          = ENNReal.ofReal ((1 - mExt' (Fin.tail ms) (ms 0) r) / (1 - ms 0))
            * ∫⁻ g, v g ^ ms 0 ∂(μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs)) := by
        have hAv : Measurable fun g : T × CascadeSpace T k => A g * v g ^ (ms 0 - 2) :=
          hA.mul (hv.pow_const _)
        have hvm : Measurable fun g : T × CascadeSpace T k => v g ^ ms 0 := hv.pow_const _
        rw [lintegral_prod _ hAv.aemeasurable, lintegral_prod _ hvm.aemeasurable]
        have hmeas' : Measurable fun z : T => ∫⁻ ω', v (z, ω') ^ ms 0
            ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs) :=
          Measurable.lintegral_prod_right' (f := fun q : T × CascadeSpace T k => v q ^ ms 0)
            (hv.pow_const _)
        rw [← lintegral_const_mul _ hmeas']
        refine lintegral_congr_ae ?_
        filter_upwards [hRfin] with z hz
        exact ih (Fin.tail ms) (Fin.tail μs)
          (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
          (fun zs => hGpos _) (strictMono_of_strictMono_cons hsm') (fun i => hlt i.succ)
          hm.le hm1 (fun i => hsm (Fin.succ_pos i)) hz r
      have hle := mExt'_le_one (ms := Fin.tail ms) (fun i => (hlt i.succ).le) hm1.le r
      have hnn : 0 ≤ (1 - mExt' (Fin.tail ms) (ms 0) r) / (1 - ms 0) :=
        div_nonneg (by linarith) (by linarith)
      have h1m : (1 : ℝ) - ms 0 ≠ 0 := by linarith
      have h1a : (1 : ℝ) - a ≠ 0 := by linarith
      rw [hinner, ← mul_assoc, mul_comm (ENNReal.ofReal _) (ENNReal.ofReal _), mul_assoc,
        ofReal_pdSqConst_mul_lintegral hm hm1 _ hv hvpos hκfin ha0 ham0, ← mul_assoc,
        ← ENNReal.ofReal_mul hnn, mExt'_succ]
      congr 2
      rw [div_mul_div_comm, mul_comm (1 - ms 0) (1 - a), ← div_mul_div_comm, div_self h1m,
        mul_one]

/-- **`𝔼 ⟨1_{α|r = γ|r}⟩ = 1 - m_r`** for the cascade Gibbs average, `0 ≤ r ≤ k + 1`
(`m₀ = 0`, `m_{k+1} = 1`). -/
theorem lintegral_cascadeSq_mul_inv_sq (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G : (Fin k → T) → ℝ≥0∞} (hG : Measurable G)
    (hGpos : ∀ zs, 0 < G zs) (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (hfin : cascadeRec k ms μs G ≠ ∞) (r : ℕ) :
    ∫⁻ ω, cascadeSq k r G ω * (cascadeSum k G ω)⁻¹ ^ 2 ∂cascadeLaw k ms μs
      = ENNReal.ofReal (1 - mExt ms r) := by
  have h := lintegral_cascadeSq_mul_rpow k ms μs hG hGpos hsm hlt (a := 0) le_rfl one_pos hpos
    hfin r
  simp only [ENNReal.rpow_zero, lintegral_const, measure_univ, mul_one, sub_zero, div_one,
    mExt'_zero_exp] at h
  rw [← h]
  refine lintegral_congr fun ω => ?_
  rw [zero_sub, ENNReal.rpow_neg, ENNReal.rpow_two, ENNReal.inv_pow]

/-- **Proposition 14.3.3** (Talagrand Vol. II, (14.38)): for the cascade Gibbs average and
`1 ≤ r ≤ k + 1`, `𝔼 ⟨1_{(α,γ) = r}⟩ = m_r - m_{r-1}`, where the pair indicator is
`1_{(α,γ) = r} = 1_{α|(r-1) = γ|(r-1)} - 1_{α|r = γ|r}` and `⟨1_{α|r = γ|r}⟩ = Q_r / S²`. -/
theorem lintegral_cascadePairIndicator (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G : (Fin k → T) → ℝ≥0∞} (hG : Measurable G)
    (hGpos : ∀ zs, 0 < G zs) (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (hfin : cascadeRec k ms μs G ≠ ∞) (r : ℕ) :
    (∫⁻ ω, cascadeSq k r G ω * (cascadeSum k G ω)⁻¹ ^ 2 ∂cascadeLaw k ms μs)
        - ∫⁻ ω, cascadeSq k (r + 1) G ω * (cascadeSum k G ω)⁻¹ ^ 2 ∂cascadeLaw k ms μs
      = ENNReal.ofReal (mExt ms (r + 1) - mExt ms r) := by
  rw [lintegral_cascadeSq_mul_inv_sq k ms μs hG hGpos hsm hpos hlt hfin,
    lintegral_cascadeSq_mul_inv_sq k ms μs hG hGpos hsm hpos hlt hfin,
    ← ENNReal.ofReal_sub _ (by linarith [mExt_le_one (fun i => (hlt i).le) (r + 1)])]
  congr 1
  ring

end

end ProbabilityTheory
