/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.PointProcess.PoissonDirichlet

/-!
# Poisson–Dirichlet cascades

Talagrand, *Mean Field Models for Spin Glasses*, Vol. II, §14.2. A `k`-level cascade with
parameters `0 < m₁ < ⋯ < m_k < 1` and marks `z_p ∼ μ_p` is built by recursion on the number of
levels: a `(k+1)`-level cascade is a Poisson–Dirichlet point process of parameter `m₁` whose points
carry, as marks, a mark `z₁ ∼ μ₁` **and an independent `k`-level cascade**. This is exactly
Talagrand's tree `(u_α, z_{p,α})_{α ∈ ℕ^{*k}}`: the weight `u*_α = u_{α|1} ⋯ u_{α|k}` of a
branch is the product of the weights along the branch, and the "secret about Poisson–Dirichlet
cascades is to be unimpressed by the definition, and to work by induction over `k`".

For a measurable `G : T^k → ℝ≥0∞` the **cascade sum** `∑_α u*_α G(z_{1,α}, …, z_{k,α})` is the
function `cascadeSum k G` of the sample, defined by the same recursion, and Talagrand's recursion
(14.5) `F_p = (1/m_p) log 𝔼_p exp (m_p F_{p+1})` is, in `ℝ≥0∞` and for `G = exp F`,

`cascadeRec (k+1) ms μs G = (∫ z, cascadeRec k (tail ms) (tail μs) (G (z, ·))^{m₁} dμ₁)^{1/m₁}`.

## Main statements

- `ProbabilityTheory.CascadeSpace`, `ProbabilityTheory.cascadeLaw`,
  `ProbabilityTheory.cascadeSum`, `ProbabilityTheory.cascadeRec`.
- `ProbabilityTheory.lintegral_cascadeSum_rpow`: **Proposition 14.2.2** — for
  `0 < m₀ < m₁ < ⋯ < m_k < 1`, `𝔼 (∑_α u*_α G(α))^{m₀} = cascadeRec^{m₀} · C(m₀, m₁, …, m_k)`,
  with an explicit constant, unconditionally in `ℝ≥0∞`.
- `ProbabilityTheory.integral_log_cascadeSum_div_eq`: **Theorem 14.2.1** —
  `𝔼 log ∑_α v_α G(α) = log cascadeRec`, where `v_α = u*_α / ∑_γ u*_γ`, with the single
  hypothesis `cascadeRec < ∞`; `ProbabilityTheory.integral_log_cascadeSum_exp_div_eq` is
  Talagrand's form `𝔼 log ∑_α v_α exp F(α) = F₁`.
- `ProbabilityTheory.cascadeRec_le_lintegral_pi`: Jensen, `cascadeRec ≤ ∫ G d(μ₁ ⊗ ⋯ ⊗ μ_k)`,
  so Talagrand's hypothesis `𝔼 exp F < ∞` suffices.
-/

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace ProbabilityTheory

open ENNReal

universe u

noncomputable section

/-- `(z, zs) ↦ Fin.cons z zs` is measurable. -/
lemma measurable_fin_cons {n : ℕ} {β : Type*} [MeasurableSpace β] :
    Measurable fun p : β × (Fin n → β) => (Fin.cons p.1 p.2 : Fin (n + 1) → β) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact measurable_fst
  · simp only [Fin.cons_succ]
    exact measurable_snd.eval

/-! ### The sample space of a cascade -/

/-- The sample space of a `k`-level cascade with marks in `T`: a `(k+1)`-level cascade is a
Poisson sample on `ℝ × (T × (k-level cascade))`. -/
abbrev CascadeSpace (T : Type u) : ℕ → Type u
  | 0 => PUnit
  | k + 1 => SuperSample (ℝ × (T × CascadeSpace T k))

variable {T : Type u} [MeasurableSpace T]

instance instMeasurableSpaceCascadeSpace : ∀ k, MeasurableSpace (CascadeSpace T k)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | k + 1 =>
    letI := instMeasurableSpaceCascadeSpace k
    inferInstanceAs (MeasurableSpace (SuperSample (ℝ × (T × CascadeSpace T k))))

instance instNonemptyCascadeSpace [Nonempty T] : ∀ k, Nonempty (CascadeSpace T k)
  | 0 => ⟨PUnit.unit⟩
  | k + 1 =>
    letI := instNonemptyCascadeSpace k
    inferInstanceAs (Nonempty (SuperSample (ℝ × (T × CascadeSpace T k))))

instance {k : ℕ} {μs : Fin (k + 1) → Measure T} [∀ i, IsProbabilityMeasure (μs i)] (i : Fin k) :
    IsProbabilityMeasure (Fin.tail μs i) :=
  inferInstanceAs (IsProbabilityMeasure (μs i.succ))

/-! ### The cascade sums -/

/-- **The cascade sum** `∑_α u*_α G(z_{1,α}, …, z_{k,α})` as a function of the sample: at level
`k+1`, the Poisson–Dirichlet weighted sum of the level-`k` cascade sums of the marks. -/
def cascadeSum : (k : ℕ) → ((Fin k → T) → ℝ≥0∞) → CascadeSpace T k → ℝ≥0∞
  | 0, G, _ => G Fin.elim0
  | k + 1, G, ω =>
    pdSum (fun p : T × CascadeSpace T k => cascadeSum k (fun zs => G (Fin.cons p.1 zs)) p.2)
      (superCounting ω)

@[simp] lemma cascadeSum_zero (G : (Fin 0 → T) → ℝ≥0∞) (ω : CascadeSpace T 0) :
    cascadeSum 0 G ω = G Fin.elim0 := rfl

lemma cascadeSum_succ (k : ℕ) (G : (Fin (k + 1) → T) → ℝ≥0∞) (ω : CascadeSpace T (k + 1)) :
    cascadeSum (k + 1) G ω
      = pdSum (fun p : T × CascadeSpace T k => cascadeSum k (fun zs => G (Fin.cons p.1 zs)) p.2)
        (superCounting ω) := rfl

/-- Joint measurability of the cascade sum in a parameter and the sample. -/
lemma measurable_cascadeSum_prod (k : ℕ) :
    ∀ {α : Type u} [MeasurableSpace α] {G : α → (Fin k → T) → ℝ≥0∞},
      Measurable (uncurry G) →
        Measurable fun q : α × CascadeSpace T k => cascadeSum k (G q.1) q.2 := by
  induction k with
  | zero =>
    intro α _ G hG
    simp only [cascadeSum_zero]
    exact hG.comp (measurable_fst.prodMk measurable_const)
  | succ k ih =>
    intro α _ G hG
    simp only [cascadeSum_succ, pdSum]
    have hG' : Measurable fun r : (α × T) × (Fin k → T) => G r.1.1 (Fin.cons r.1.2 r.2) :=
      hG.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fin_cons.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
    have h1 := ih (α := α × T) (G := fun q zs => G q.1 (Fin.cons q.2 zs)) hG'
    have hf : Measurable fun r : α × (ℝ × (T × CascadeSpace T k)) =>
        ENNReal.ofReal r.2.1 * cascadeSum k (fun zs => G r.1 (Fin.cons r.2.2.1 zs)) r.2.2.2 := by
      refine (ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_snd)).mul ?_
      exact h1.comp ((measurable_fst.prodMk (measurable_fst.comp
        (measurable_snd.comp measurable_snd))).prodMk (measurable_snd.comp
          (measurable_snd.comp measurable_snd)))
    exact measurable_lintegral_superCounting_prod hf

lemma measurable_cascadeSum (k : ℕ) {G : (Fin k → T) → ℝ≥0∞} (hG : Measurable G) :
    Measurable (cascadeSum k G) := by
  have h := measurable_cascadeSum_prod k (α := PUnit) (G := fun _ => G)
    (hG.comp measurable_snd)
  exact h.comp (measurable_const.prodMk measurable_id :
    Measurable fun ω : CascadeSpace T k => (PUnit.unit, ω))

/-! ### The recursion (14.5) -/

/-- **Talagrand's recursion (14.5)** in `ℝ≥0∞`: `cascadeRec k ms μs G` is `exp F₁` for
`G = exp F`, where `F_p = (1/m_p) log 𝔼_p exp (m_p F_{p+1})`. -/
def cascadeRec : (k : ℕ) → (Fin k → ℝ) → (Fin k → Measure T) → ((Fin k → T) → ℝ≥0∞) → ℝ≥0∞
  | 0, _, _, G => G Fin.elim0
  | k + 1, ms, μs, G =>
    (∫⁻ z, cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
      ∂μs 0) ^ (1 / ms 0)

@[simp] lemma cascadeRec_zero (ms : Fin 0 → ℝ) (μs : Fin 0 → Measure T)
    (G : (Fin 0 → T) → ℝ≥0∞) : cascadeRec 0 ms μs G = G Fin.elim0 := rfl

lemma cascadeRec_succ (k : ℕ) (ms : Fin (k + 1) → ℝ) (μs : Fin (k + 1) → Measure T)
    (G : (Fin (k + 1) → T) → ℝ≥0∞) :
    cascadeRec (k + 1) ms μs G
      = (∫⁻ z, cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
          ∂μs 0) ^ (1 / ms 0) := rfl

lemma measurable_cascadeRec_prod (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] :
    ∀ {α : Type u} [MeasurableSpace α] {G : α → (Fin k → T) → ℝ≥0∞},
      Measurable (uncurry G) → Measurable fun a => cascadeRec k ms μs (G a) := by
  induction k with
  | zero =>
    intro α _ G hG
    simp only [cascadeRec_zero]
    exact hG.comp (measurable_id.prodMk measurable_const)
  | succ k ih =>
    intro α _ G hG
    simp only [cascadeRec_succ]
    have hG' : Measurable fun r : (α × T) × (Fin k → T) => G r.1.1 (Fin.cons r.1.2 r.2) :=
      hG.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fin_cons.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
    have h1 := ih (Fin.tail ms) (Fin.tail μs) (α := α × T)
      (G := fun q zs => G q.1 (Fin.cons q.2 zs)) hG'
    exact (Measurable.lintegral_prod_right' (h1.pow_const (ms 0))).pow_const _

lemma measurable_cascadeRec_cons (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G : (Fin (k + 1) → T) → ℝ≥0∞} (hG : Measurable G) :
    Measurable fun z => cascadeRec k ms μs (fun zs => G (Fin.cons z zs)) :=
  measurable_cascadeRec_prod k ms μs (α := T) (G := fun z zs => G (Fin.cons z zs))
    (hG.comp measurable_fin_cons)

lemma cascadeRec_pos (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G : (Fin k → T) → ℝ≥0∞} (hG : Measurable G)
    (hGpos : ∀ zs, 0 < G zs) (hpos : ∀ i, 0 < ms i) : 0 < cascadeRec k ms μs G := by
  induction k with
  | zero => simpa using hGpos Fin.elim0
  | succ k ih =>
    rw [cascadeRec_succ]
    refine ENNReal.rpow_pos_of_nonneg ?_ (by have := hpos 0; positivity)
    rw [lintegral_pos_iff_support ((measurable_cascadeRec_cons k _ _ hG).pow_const _)]
    have : Function.support (fun z => cascadeRec k (Fin.tail ms) (Fin.tail μs)
        (fun zs => G (Fin.cons z zs)) ^ ms 0) = univ := by
      ext z
      simp only [Function.mem_support, mem_univ, iff_true]
      exact (ENNReal.rpow_pos_of_nonneg (ih (Fin.tail ms) (Fin.tail μs)
        (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (fun zs => hGpos _) (fun i => hpos i.succ)) (hpos 0).le).ne'
    rw [this, measure_univ]
    exact one_pos

lemma cascadeRec_one (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] (hpos : ∀ i, 0 < ms i) :
    cascadeRec k ms μs (fun _ => 1) = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [cascadeRec_succ]
    simp only [ih (Fin.tail ms) (Fin.tail μs) (fun i => hpos i.succ), ENNReal.one_rpow,
      lintegral_const, measure_univ, mul_one]

/-! ### The constant of Proposition 14.2.2 -/

/-- The constant `∏_p (𝔼 (∑_j u_j^{(p)})^{m_{p-1}})^{m₀/m_{p-1}}` of Proposition 14.2.2, with the
moments of the one-level sums made explicit by `lintegral_pdSum_rpow`. -/
def cascadeConst : (k : ℕ) → ℝ → (Fin k → ℝ) → ℝ≥0∞
  | 0, _, _ => 1
  | k + 1, m₀, ms =>
    ENNReal.ofReal (stableConst (ms 0) ^ (m₀ / ms 0) * stableConst (m₀ / ms 0)
        / (ms 0 * stableConst m₀))
      * cascadeConst k (ms 0) (Fin.tail ms) ^ (m₀ / ms 0)

@[simp] lemma cascadeConst_zero (m₀ : ℝ) (ms : Fin 0 → ℝ) : cascadeConst 0 m₀ ms = 1 := rfl

lemma cascadeConst_succ (k : ℕ) (m₀ : ℝ) (ms : Fin (k + 1) → ℝ) :
    cascadeConst (k + 1) m₀ ms
      = ENNReal.ofReal (stableConst (ms 0) ^ (m₀ / ms 0) * stableConst (m₀ / ms 0)
          / (ms 0 * stableConst m₀))
        * cascadeConst k (ms 0) (Fin.tail ms) ^ (m₀ / ms 0) := rfl

/-- `StrictMono (Fin.cons m₀ ms)` restricts to `StrictMono ms`. -/
lemma strictMono_of_strictMono_cons {k : ℕ} {m₀ : ℝ} {ms : Fin k → ℝ}
    (h : StrictMono (Fin.cons m₀ ms : Fin (k + 1) → ℝ)) : StrictMono ms := by
  intro i j hij
  have := h (Fin.succ_lt_succ_iff.2 hij)
  simpa using this

lemma lt_zero_of_strictMono_cons {k : ℕ} {m₀ : ℝ} {ms : Fin (k + 1) → ℝ}
    (h : StrictMono (Fin.cons m₀ ms : Fin (k + 2) → ℝ)) : m₀ < ms 0 := by
  have := h (show (0 : Fin (k + 2)) < 1 from Fin.zero_lt_one)
  simpa using this

lemma pos_of_strictMono_cons {k : ℕ} {m₀ : ℝ} (hm₀ : 0 < m₀) {ms : Fin k → ℝ}
    (h : StrictMono (Fin.cons m₀ ms : Fin (k + 1) → ℝ)) (i : Fin k) : 0 < ms i := by
  have := h (show (0 : Fin (k + 1)) < i.succ from Fin.succ_pos i)
  simp only [Fin.cons_zero, Fin.cons_succ] at this
  linarith

lemma cascadeConst_pos_ne_top (k : ℕ) {m₀ : ℝ} (hm₀ : 0 < m₀) {ms : Fin k → ℝ}
    (hsm : StrictMono (Fin.cons m₀ ms : Fin (k + 1) → ℝ)) (hlt : ∀ i, ms i < 1) :
    0 < cascadeConst k m₀ ms ∧ cascadeConst k m₀ ms ≠ ∞ := by
  induction k generalizing m₀ with
  | zero => simp
  | succ k ih =>
    have hm : 0 < ms 0 := pos_of_strictMono_cons hm₀ hsm 0
    have hm₀m : m₀ < ms 0 := lt_zero_of_strictMono_cons hsm
    have hm1 : ms 0 < 1 := hlt 0
    have hq : 0 < m₀ / ms 0 := div_pos hm₀ hm
    have hq1 : m₀ / ms 0 < 1 := (div_lt_one hm).2 hm₀m
    have hc : 0 < stableConst (ms 0) := stableConst_pos hm hm1
    have hc' : 0 < stableConst (m₀ / ms 0) := stableConst_pos hq hq1
    have hc₀ : 0 < stableConst m₀ := stableConst_pos hm₀ (hm₀m.trans hm1)
    have hsm' : StrictMono (Fin.cons (ms 0) (Fin.tail ms) : Fin (k + 1) → ℝ) := by
      rw [Fin.cons_self_tail]
      exact strictMono_of_strictMono_cons hsm
    obtain ⟨h1, h2⟩ := ih hm hsm' (fun i => hlt i.succ)
    rw [cascadeConst_succ]
    refine ⟨ENNReal.mul_pos (ENNReal.ofReal_pos.2 (by positivity)).ne'
      (ENNReal.rpow_pos_of_nonneg h1 hq.le).ne', ?_⟩
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg hq.le h2)

variable [Nonempty T]

/-! ### The law of a cascade -/

/-- The law of a `k`-level cascade, bundled with its probability-measure proof for the
recursion. -/
def cascadeLawAux : (k : ℕ) → (Fin k → ℝ) → (Fin k → {μ : Measure T // IsProbabilityMeasure μ}) →
    {P : Measure (CascadeSpace T k) // IsProbabilityMeasure P}
  | 0, _, _ => ⟨Measure.dirac PUnit.unit, inferInstance⟩
  | k + 1, ms, μs =>
    haveI := (μs 0).2
    haveI := (cascadeLawAux k (Fin.tail ms) (Fin.tail μs)).2
    ⟨pdSampleLaw (ms 0) (((μs 0).1).prod
        (cascadeLawAux k (Fin.tail ms) (Fin.tail μs)).1), inferInstance⟩

/-- **The law of a `k`-level Poisson–Dirichlet cascade** with parameters `ms` and mark laws
`μs`: a `(k+1)`-level cascade is the Poisson–Dirichlet point process of parameter `ms 0` whose
marks are a mark `z ∼ μs 0` together with an independent `k`-level cascade.
Talagrand Vol. II, §14.2, (14.1). -/
def cascadeLaw (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] : Measure (CascadeSpace T k) :=
  (cascadeLawAux k ms fun i => ⟨μs i, inferInstance⟩).1

instance (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)] :
    IsProbabilityMeasure (cascadeLaw k ms μs) :=
  (cascadeLawAux k ms fun i => ⟨μs i, inferInstance⟩).2

lemma cascadeLaw_zero (ms : Fin 0 → ℝ) (μs : Fin 0 → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] :
    cascadeLaw 0 ms μs = Measure.dirac PUnit.unit := rfl

lemma cascadeLaw_succ (k : ℕ) (ms : Fin (k + 1) → ℝ) (μs : Fin (k + 1) → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] :
    cascadeLaw (k + 1) ms μs
      = pdSampleLaw (ms 0) ((μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs))) := rfl

/-- The counting measure of a `(k+1)`-level cascade is a Poisson–Dirichlet point process whose
marks are `(z, k-level cascade)`. -/
lemma hasLaw_superCounting_cascadeLaw (k : ℕ) (ms : Fin (k + 1) → ℝ)
    (μs : Fin (k + 1) → Measure T) [∀ i, IsProbabilityMeasure (μs i)] :
    HasLaw (fun ω : CascadeSpace T (k + 1) => superCounting ω)
      (pdProcess (ms 0) ((μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs))))
      (cascadeLaw (k + 1) ms μs) :=
  hasLaw_superCounting_pdProcess _ _

/-! ### Proposition 14.2.2: the moments of a cascade sum -/

/-- **Proposition 14.2.2** (Talagrand Vol. II, (14.9)): for `0 < m₀ < m₁ < ⋯ < m_k < 1`,
`𝔼 (∑_α u*_α G(α))^{m₀} = cascadeRec^{m₀} · C(m₀, m₁, …, m_k)`, unconditionally in `ℝ≥0∞`. -/
theorem lintegral_cascadeSum_rpow (k : ℕ) :
    ∀ (ms : Fin k → ℝ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
      {G : (Fin k → T) → ℝ≥0∞}, Measurable G → ∀ {m₀ : ℝ}, 0 < m₀ →
      StrictMono (Fin.cons m₀ ms : Fin (k + 1) → ℝ) → (∀ i, ms i < 1) →
      ∫⁻ ω, cascadeSum k G ω ^ m₀ ∂cascadeLaw k ms μs
        = cascadeRec k ms μs G ^ m₀ * cascadeConst k m₀ ms := by
  induction k with
  | zero =>
    intro ms μs _ G _ m₀ _ _ _
    simp only [cascadeSum_zero, cascadeRec_zero, cascadeConst_zero, mul_one]
    rw [cascadeLaw_zero, lintegral_const, measure_univ, mul_one]
  | succ k ih =>
    intro ms μs _ G hG m₀ hm₀ hsm hlt
    have hm : 0 < ms 0 := pos_of_strictMono_cons hm₀ hsm 0
    have hm₀m : m₀ < ms 0 := lt_zero_of_strictMono_cons hsm
    have hm1 : ms 0 < 1 := hlt 0
    have hq : 0 < m₀ / ms 0 := div_pos hm₀ hm
    have hc : 0 < stableConst (ms 0) := stableConst_pos hm hm1
    have hsm' : StrictMono (Fin.cons (ms 0) (Fin.tail ms) : Fin (k + 1) → ℝ) := by
      rw [Fin.cons_self_tail]
      exact strictMono_of_strictMono_cons hsm
    -- the weight on the marks is the level-`k` cascade sum
    set v : T × CascadeSpace T k → ℝ≥0∞ :=
      fun p => cascadeSum k (fun zs => G (Fin.cons p.1 zs)) p.2 with hv_def
    have hv : Measurable v :=
      measurable_cascadeSum_prod k (α := T) (G := fun z zs => G (Fin.cons z zs))
        (hG.comp measurable_fin_cons)
    have hlaw := hasLaw_superCounting_cascadeLaw k ms μs
    have hsum : ∀ ω, cascadeSum (k + 1) G ω = pdSum v (superCounting ω) := fun ω => rfl
    simp_rw [hsum]
    rw [hlaw.lintegral_pdSum_rpow hm hm1 hv hm₀ hm₀m]
    -- the `m₁`-th moment of the weights, by the induction hypothesis
    have hR : Measurable fun z => cascadeRec k (Fin.tail ms) (Fin.tail μs)
        (fun zs => G (Fin.cons z zs)) := measurable_cascadeRec_cons k _ _ hG
    have hκ : ∫⁻ p, v p ^ ms 0 ∂(μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs))
        = cascadeConst k (ms 0) (Fin.tail ms) * cascadeRec (k + 1) ms μs G ^ ms 0 := by
      rw [lintegral_prod _ (hv.pow_const _).aemeasurable]
      have hpt : ∀ z, ∫⁻ ω', v (z, ω') ^ ms 0 ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
          = cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
            * cascadeConst k (ms 0) (Fin.tail ms) := fun z =>
        ih (Fin.tail ms) (Fin.tail μs)
          (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
          hm hsm' (fun i => hlt i.succ)
      simp_rw [hpt]
      rw [lintegral_mul_const _ (hR.pow_const _), cascadeRec_succ, ← ENNReal.rpow_mul,
        one_div_mul_cancel hm.ne', ENNReal.rpow_one, mul_comm]
    rw [hκ, cascadeConst_succ, ENNReal.mul_rpow_of_nonneg _ _ hq.le,
      ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← ENNReal.rpow_mul, mul_div_cancel₀ _ hm.ne',
      ENNReal.ofReal_rpow_of_nonneg hc.le hq.le,
      mul_div_assoc (stableConst (ms 0) ^ (m₀ / ms 0)), ENNReal.ofReal_mul (by positivity)]
    ring

/-- The cascade sum is almost surely positive when `G > 0`. -/
theorem ae_cascadeSum_pos (k : ℕ) :
    ∀ (ms : Fin k → ℝ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
      {G : (Fin k → T) → ℝ≥0∞}, Measurable G → (∀ zs, 0 < G zs) → (∀ i, 0 < ms i) →
      ∀ᵐ ω ∂cascadeLaw k ms μs, 0 < cascadeSum k G ω := by
  induction k with
  | zero =>
    intro ms μs _ G _ hGpos _
    exact Filter.Eventually.of_forall fun ω => by simpa using hGpos _
  | succ k ih =>
    intro ms μs _ G hG hGpos hpos
    set v : T × CascadeSpace T k → ℝ≥0∞ :=
      fun p => cascadeSum k (fun zs => G (Fin.cons p.1 zs)) p.2 with hv_def
    have hv : Measurable v :=
      measurable_cascadeSum_prod k (α := T) (G := fun z zs => G (Fin.cons z zs))
        (hG.comp measurable_fin_cons)
    have hlaw := hasLaw_superCounting_cascadeLaw k ms μs
    have hsum : ∀ ω, cascadeSum (k + 1) G ω = pdSum v (superCounting ω) := fun ω => rfl
    simp_rw [hsum]
    refine hlaw.ae_pdSum_pos (hpos 0) hv ?_
    rw [Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const hv)]
    exact Filter.Eventually.of_forall fun z => ih (Fin.tail ms) (Fin.tail μs)
      (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
      (fun zs => hGpos _) (fun i => hpos i.succ)

/-! ### Theorem 14.2.1 -/

/-- **Theorem 14.2.1** (Talagrand Vol. II, (14.8)): for `0 < m₁ < ⋯ < m_k < 1`, `G > 0`
measurable with `cascadeRec k ms μs G < ∞`,

`𝔼 log ∑_α v_α G(α) = log cascadeRec k ms μs G`,

where `v_α = u*_α / ∑_γ u*_γ` are the cascade weights. -/
theorem integral_log_cascadeSum_div_eq (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G : (Fin k → T) → ℝ≥0∞} (hG : Measurable G)
    (hGpos : ∀ zs, 0 < G zs) (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (hfin : cascadeRec k ms μs G ≠ ∞) :
    ∫ ω, Real.log ((cascadeSum k G ω).toReal / (cascadeSum k (fun _ => 1) ω).toReal)
        ∂cascadeLaw k ms μs
      = Real.log (cascadeRec k ms μs G).toReal := by
  cases k with
  | zero =>
    simp only [cascadeSum_zero, cascadeRec_zero]
    rw [cascadeLaw_zero, integral_const]
    simp
  | succ k =>
    have hm : 0 < ms 0 := hpos 0
    have hm1 : ms 0 < 1 := hlt 0
    have hsm' : StrictMono (Fin.cons (ms 0) (Fin.tail ms) : Fin (k + 1) → ℝ) := by
      rw [Fin.cons_self_tail]; exact hsm
    set v : T × CascadeSpace T k → ℝ≥0∞ :=
      fun p => cascadeSum k (fun zs => G (Fin.cons p.1 zs)) p.2 with hv_def
    set v₁ : T × CascadeSpace T k → ℝ≥0∞ :=
      fun p => cascadeSum k (fun _ => 1) p.2 with hv₁_def
    have hv : Measurable v :=
      measurable_cascadeSum_prod k (α := T) (G := fun z zs => G (Fin.cons z zs))
        (hG.comp measurable_fin_cons)
    have hv₁ : Measurable v₁ := (measurable_cascadeSum k measurable_const).comp measurable_snd
    have hlaw := hasLaw_superCounting_cascadeLaw k ms μs
    have hsum : ∀ ω, cascadeSum (k + 1) G ω = pdSum v (superCounting ω) := fun ω => rfl
    have hsum₁ : ∀ ω, cascadeSum (k + 1) (fun _ => 1) ω = pdSum v₁ (superCounting ω) :=
      fun ω => rfl
    simp_rw [hsum, hsum₁]
    -- the moments of the weights
    obtain ⟨hC, hC'⟩ := cascadeConst_pos_ne_top k hm hsm' (fun i => hlt i.succ)
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
      rw [lintegral_mul_const _ ((measurable_cascadeRec_cons k _ _ hG).pow_const _),
        cascadeRec_succ, ← ENNReal.rpow_mul, one_div_mul_cancel hm.ne', ENNReal.rpow_one,
        mul_comm]
    have hκ₁ : ∫⁻ p, v₁ p ^ ms 0 ∂(μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs))
        = cascadeConst k (ms 0) (Fin.tail ms) := by
      rw [lintegral_prod _ (hv₁.pow_const _).aemeasurable]
      have hpt : ∀ z, ∫⁻ ω', v₁ (z, ω') ^ ms 0 ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
          = cascadeConst k (ms 0) (Fin.tail ms) := fun z => by
        have := lintegral_cascadeSum_rpow k (Fin.tail ms) (Fin.tail μs)
          (G := fun _ => (1 : ℝ≥0∞)) measurable_const hm hsm' (fun i => hlt i.succ)
        rw [cascadeRec_one k (Fin.tail ms) (Fin.tail μs) (fun i => hpos i.succ),
          ENNReal.one_rpow, one_mul] at this
        exact this
      simp_rw [hpt]
      rw [lintegral_const, measure_univ, mul_one]
    have hκfin : ∫⁻ p, v p ^ ms 0 ∂(μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs))
        ≠ ∞ := by
      rw [hκ]
      exact ENNReal.mul_ne_top hC' (ENNReal.rpow_ne_top_of_nonneg hm.le hfin)
    have hκ₁fin : ∫⁻ p, v₁ p ^ ms 0 ∂(μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs))
        ≠ ∞ := by rw [hκ₁]; exact hC'
    -- a.e. positivity of the weights
    have hvpos : ∀ᵐ p ∂(μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs)), 0 < v p := by
      rw [Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const hv)]
      exact Filter.Eventually.of_forall fun z => ae_cascadeSum_pos k (Fin.tail ms) (Fin.tail μs)
        (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (fun zs => hGpos _) (fun i => hpos i.succ)
    have hv₁pos : ∀ᵐ p ∂(μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs)), 0 < v₁ p := by
      rw [Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const hv₁)]
      exact Filter.Eventually.of_forall fun z => ae_cascadeSum_pos k (Fin.tail ms) (Fin.tail μs)
        measurable_const (fun _ => one_pos) (fun i => hpos i.succ)
    -- (13.10) for both weights
    have hae : ∀ᵐ ω ∂cascadeLaw (k + 1) ms μs,
        Real.log ((pdSum v (superCounting ω)).toReal / (pdSum v₁ (superCounting ω)).toReal)
          = Real.log (pdSum v (superCounting ω)).toReal
            - Real.log (pdSum v₁ (superCounting ω)).toReal := by
      filter_upwards [hlaw.ae_pdSum_pos hm hv hvpos, hlaw.ae_pdSum_lt_top hm hm1 hv hκfin,
        hlaw.ae_pdSum_pos hm hv₁ hv₁pos, hlaw.ae_pdSum_lt_top hm hm1 hv₁ hκ₁fin]
        with ω h1 h2 h3 h4
      rw [Real.log_div (ENNReal.toReal_pos h1.ne' h2.ne).ne'
        (ENNReal.toReal_pos h3.ne' h4.ne).ne']
    rw [integral_congr_ae hae, integral_sub (hlaw.integrable_log_pdSum hm hm1 hv hκfin hvpos)
      (hlaw.integrable_log_pdSum hm hm1 hv₁ hκ₁fin hv₁pos),
      hlaw.integral_log_pdSum_eq hm hm1 hv hκfin hvpos,
      hlaw.integral_log_pdSum_eq hm hm1 hv₁ hκ₁fin hv₁pos, hκ, hκ₁]
    have hRpos : 0 < cascadeRec (k + 1) ms μs G := cascadeRec_pos _ _ _ hG hGpos hpos
    have hRr : 0 < (cascadeRec (k + 1) ms μs G).toReal := ENNReal.toReal_pos hRpos.ne' hfin
    have hCr : 0 < (cascadeConst k (ms 0) (Fin.tail ms)).toReal := ENNReal.toReal_pos hC.ne' hC'
    rw [ENNReal.toReal_mul, Real.log_mul hCr.ne' (by
        rw [← ENNReal.toReal_rpow]; exact (Real.rpow_pos_of_pos hRr _).ne'),
      ← ENNReal.toReal_rpow, Real.log_rpow hRr]
    field_simp
    ring

/-! ### Talagrand's form -/

/-- **Talagrand's recursion (14.5)**: `parisiRec k ms μs F` is `F₁`, where
`F_{k+1} = F(z₁, …, z_k)` and `F_p = (1/m_p) log 𝔼_p exp (m_p F_{p+1})`. -/
def parisiRec (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T) (F : (Fin k → T) → ℝ) : ℝ :=
  Real.log (cascadeRec k ms μs fun zs => ENNReal.ofReal (Real.exp (F zs))).toReal

omit [Nonempty T] in
@[simp] lemma parisiRec_zero (ms : Fin 0 → ℝ) (μs : Fin 0 → Measure T) (F : (Fin 0 → T) → ℝ) :
    parisiRec 0 ms μs F = F Fin.elim0 := by
  simp [parisiRec, ENNReal.toReal_ofReal (Real.exp_pos _).le]

omit [Nonempty T] in
/-- **The recursion (14.5)**: `F_p = (1/m_p) log 𝔼_p exp (m_p F_{p+1})`, when the right-hand side
is finite. -/
lemma parisiRec_succ (k : ℕ) (ms : Fin (k + 1) → ℝ) (μs : Fin (k + 1) → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {F : (Fin (k + 1) → T) → ℝ} (hF : Measurable F)
    (hpos : ∀ i, 0 < ms i)
    (hfin : cascadeRec (k + 1) ms μs (fun zs => ENNReal.ofReal (Real.exp (F zs))) ≠ ∞) :
    parisiRec (k + 1) ms μs F
      = (1 / ms 0) * Real.log (∫ z, Real.exp (ms 0
          * parisiRec k (Fin.tail ms) (Fin.tail μs) (fun zs => F (Fin.cons z zs))) ∂μs 0) := by
  have hm : 0 < ms 0 := hpos 0
  have hG : Measurable fun zs : Fin (k + 1) → T => ENNReal.ofReal (Real.exp (F zs)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hF)
  have hR : Measurable fun z => cascadeRec k (Fin.tail ms) (Fin.tail μs)
      (fun zs => ENNReal.ofReal (Real.exp (F (Fin.cons z zs)))) :=
    measurable_cascadeRec_cons k _ _ hG
  have hRpos : ∀ z, 0 < cascadeRec k (Fin.tail ms) (Fin.tail μs)
      (fun zs => ENNReal.ofReal (Real.exp (F (Fin.cons z zs)))) := fun z =>
    cascadeRec_pos k _ _
      (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
      (fun zs => ENNReal.ofReal_pos.2 (Real.exp_pos _)) (fun i => hpos i.succ)
  have hL : parisiRec (k + 1) ms μs F
      = Real.log (cascadeRec (k + 1) ms μs fun zs => ENNReal.ofReal (Real.exp (F zs))).toReal :=
    rfl
  rw [cascadeRec_succ] at hfin
  have hint : ∫⁻ z, cascadeRec k (Fin.tail ms) (Fin.tail μs)
      (fun zs => ENNReal.ofReal (Real.exp (F (Fin.cons z zs)))) ^ ms 0 ∂μs 0 ≠ ∞ := by
    intro h
    rw [h, ENNReal.top_rpow_of_pos (by positivity)] at hfin
    exact hfin rfl
  have hLpos : 0 < ∫⁻ z, cascadeRec k (Fin.tail ms) (Fin.tail μs)
      (fun zs => ENNReal.ofReal (Real.exp (F (Fin.cons z zs)))) ^ ms 0 ∂μs 0 := by
    rw [lintegral_pos_iff_support (hR.pow_const _)]
    have : Function.support (fun z => cascadeRec k (Fin.tail ms) (Fin.tail μs)
        (fun zs => ENNReal.ofReal (Real.exp (F (Fin.cons z zs)))) ^ ms 0) = univ := by
      ext z
      simp only [Function.mem_support, mem_univ, iff_true]
      exact (ENNReal.rpow_pos_of_nonneg (hRpos z) hm.le).ne'
    rw [this, measure_univ]
    exact one_pos
  have hRfin : ∀ᵐ z ∂μs 0, cascadeRec k (Fin.tail ms) (Fin.tail μs)
      (fun zs => ENNReal.ofReal (Real.exp (F (Fin.cons z zs)))) ^ ms 0 < ∞ :=
    ae_lt_top (hR.pow_const _) hint
  have hexp : ∀ᵐ z ∂μs 0, Real.exp (ms 0 * parisiRec k (Fin.tail ms) (Fin.tail μs)
      (fun zs => F (Fin.cons z zs)))
        = (cascadeRec k (Fin.tail ms) (Fin.tail μs)
            (fun zs => ENNReal.ofReal (Real.exp (F (Fin.cons z zs)))) ^ ms 0).toReal := by
    filter_upwards [hRfin] with z hz
    have hz' : cascadeRec k (Fin.tail ms) (Fin.tail μs)
        (fun zs => ENNReal.ofReal (Real.exp (F (Fin.cons z zs)))) ≠ ∞ := by
      intro h
      rw [h, ENNReal.top_rpow_of_pos hm] at hz
      exact lt_irrefl _ hz
    have hzr : 0 < (cascadeRec k (Fin.tail ms) (Fin.tail μs)
        (fun zs => ENNReal.ofReal (Real.exp (F (Fin.cons z zs))))).toReal :=
      ENNReal.toReal_pos (hRpos z).ne' hz'
    rw [parisiRec, ← ENNReal.toReal_rpow, Real.rpow_def_of_pos hzr, mul_comm]
  rw [hL, cascadeRec_succ, ← ENNReal.toReal_rpow,
    Real.log_rpow (ENNReal.toReal_pos hLpos.ne' hint), integral_congr_ae hexp,
    integral_toReal (hR.pow_const _).aemeasurable hRfin]

/-- **Theorem 14.2.1 in Talagrand's form**: `𝔼 log ∑_α v_α exp F(α) = F₁`. -/
theorem integral_log_cascadeSum_exp_div_eq (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {F : (Fin k → T) → ℝ} (hF : Measurable F)
    (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (hfin : cascadeRec k ms μs (fun zs => ENNReal.ofReal (Real.exp (F zs))) ≠ ∞) :
    ∫ ω, Real.log ((cascadeSum k (fun zs => ENNReal.ofReal (Real.exp (F zs))) ω).toReal
        / (cascadeSum k (fun _ => 1) ω).toReal) ∂cascadeLaw k ms μs
      = parisiRec k ms μs F :=
  integral_log_cascadeSum_div_eq k ms μs
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hF))
    (fun _ => ENNReal.ofReal_pos.2 (Real.exp_pos _)) hsm hpos hlt hfin

/-! ### Pushing the mark laws forward -/

omit [Nonempty T] in
/-- **The cascade recursion under a change of marks**: pushing every mark law forward along a
measurable map is the same as composing the terminal function with the maps. -/
theorem cascadeRec_map {T' : Type*} [MeasurableSpace T'] (k : ℕ) :
    ∀ (ms : Fin k → ℝ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
      (φ : Fin k → T → T'), (∀ i, Measurable (φ i)) → ∀ {G : (Fin k → T') → ℝ≥0∞},
      Measurable G →
      cascadeRec k ms (fun i => (μs i).map (φ i)) G
        = cascadeRec k ms μs (fun zs => G (fun i => φ i (zs i))) := by
  induction k with
  | zero =>
    intro ms μs _ φ _ G _
    simp only [cascadeRec_zero]
    exact congrArg G (Subsingleton.elim _ _)
  | succ k ih =>
    intro ms μs hμs φ hφ G hG
    have hinst : ∀ i, IsProbabilityMeasure ((μs i).map (φ i)) := fun i =>
      Measure.isProbabilityMeasure_map (hφ i).aemeasurable
    have htail_inst : ∀ i : Fin k, IsProbabilityMeasure ((Fin.tail μs i).map (Fin.tail φ i)) :=
      fun i => hinst i.succ
    simp only [cascadeRec_succ]
    have htail : Fin.tail (fun i => (μs i).map (φ i))
        = fun i => (Fin.tail μs i).map (Fin.tail φ i) := rfl
    rw [htail]
    have hmeas : Measurable fun z : T' => cascadeRec k (Fin.tail ms)
        (fun i => (Fin.tail μs i).map (Fin.tail φ i)) (fun zs => G (Fin.cons z zs)) ^ ms 0 :=
      (measurable_cascadeRec_prod k (Fin.tail ms) _ (α := T')
        (G := fun z zs => G (Fin.cons z zs)) (hG.comp measurable_fin_cons)).pow_const _
    rw [lintegral_map hmeas (hφ 0)]
    congr 1
    refine lintegral_congr fun z => ?_
    congr 1
    have hGz : Measurable fun zs : Fin k → T' => G (Fin.cons (φ 0 z) zs) := by
      have h2 := hG.comp (measurable_fin_cons.comp
        ((measurable_const : Measurable fun _ : Fin k → T' => φ 0 z).prodMk measurable_id))
      simp only [Function.comp_def] at h2
      exact h2
    rw [ih (Fin.tail ms) (Fin.tail μs) (Fin.tail φ) (fun i => hφ i.succ)
      (G := fun zs => G (Fin.cons (φ 0 z) zs)) hGz]
    congr 1
    funext zs
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [Fin.tail]

omit [Nonempty T] in
/-- The Parisi recursion under a change of marks. -/
theorem parisiRec_map {T' : Type*} [MeasurableSpace T'] (k : ℕ) (ms : Fin k → ℝ)
    (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)] (φ : Fin k → T → T')
    (hφ : ∀ i, Measurable (φ i)) {F : (Fin k → T') → ℝ} (hF : Measurable F) :
    parisiRec k ms (fun i => (μs i).map (φ i)) F
      = parisiRec k ms μs (fun zs => F (fun i => φ i (zs i))) := by
  unfold parisiRec
  have hG : Measurable fun zs : Fin k → T' => ENNReal.ofReal (Real.exp (F zs)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hF)
  rw [cascadeRec_map k ms μs φ hφ (G := fun zs => ENNReal.ofReal (Real.exp (F zs))) hG]

/-! ### Jensen: Talagrand's hypothesis `𝔼 exp F < ∞` suffices -/

omit [Nonempty T] in
/-- Jensen's inequality for `x ↦ x^m`, `0 < m ≤ 1`, on a probability space, in `ℝ≥0∞`. -/
theorem lintegral_rpow_le_rpow_lintegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : Ω → ℝ≥0∞} (hf : AEMeasurable f μ) {m : ℝ} (hm0 : 0 < m)
    (hm1 : m ≤ 1) :
    ∫⁻ ω, f ω ^ m ∂μ ≤ (∫⁻ ω, f ω ∂μ) ^ m := by
  rcases eq_or_lt_of_le hm1 with rfl | hm1
  · simp
  have hpq : (m⁻¹).HolderConjugate (1 - m)⁻¹ :=
    (Real.HolderConjugate.one_sub_inv_inv hm0 hm1).symm
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq (f := fun ω => f ω ^ m)
    (g := fun _ => (1 : ℝ≥0∞)) (hf.pow_const m) aemeasurable_const
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ, one_div,
    inv_inv] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  refine lintegral_congr fun ω => ?_
  rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hm0.ne', ENNReal.rpow_one]

omit [Nonempty T] in
/-- **Lyapunov's inequality**: the power means `(∫ f^p)^{1/p}` are nondecreasing in `p > 0` on a
probability space, in `ℝ≥0∞`. -/
theorem lintegral_rpow_rpow_inv_le_of_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : Ω → ℝ≥0∞} (hf : AEMeasurable f μ) {p q : ℝ} (hp : 0 < p)
    (hpq : p ≤ q) :
    (∫⁻ ω, f ω ^ p ∂μ) ^ (1 / p) ≤ (∫⁻ ω, f ω ^ q ∂μ) ^ (1 / q) := by
  have hq : 0 < q := hp.trans_le hpq
  have h1 : ∫⁻ ω, f ω ^ p ∂μ ≤ (∫⁻ ω, f ω ^ q ∂μ) ^ (p / q) := by
    have := lintegral_rpow_le_rpow_lintegral μ (hf.pow_const q) (m := p / q) (by positivity)
      ((div_le_one hq).2 hpq)
    refine le_of_eq_of_le (lintegral_congr fun ω => ?_) this
    rw [← ENNReal.rpow_mul]
    congr 1
    field_simp
  calc (∫⁻ ω, f ω ^ p ∂μ) ^ (1 / p) ≤ ((∫⁻ ω, f ω ^ q ∂μ) ^ (p / q)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow h1 (by positivity)
    _ = (∫⁻ ω, f ω ^ q ∂μ) ^ (1 / q) := by
        rw [← ENNReal.rpow_mul]
        congr 1
        field_simp

omit [Nonempty T] in
/-- The product measure on `Fin (n+1) → T` splits off its first coordinate. -/
lemma lintegral_pi_fin_succ {n : ℕ} (μs : Fin (n + 1) → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {G : (Fin (n + 1) → T) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ zs, G zs ∂Measure.pi μs
      = ∫⁻ z, (∫⁻ zs, G (Fin.cons z zs) ∂Measure.pi (Fin.tail μs)) ∂μs 0 := by
  have hmp := (measurePreserving_piFinSuccAbove μs 0).symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => T) 0)
  have hGe : Measurable fun q : T × (Fin n → T) =>
      G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => T) 0).symm q) :=
    hG.comp hmp.measurable
  rw [← hmp.lintegral_comp hG, lintegral_prod _ hGe.aemeasurable]
  simp only [Fin.succAbove_zero]
  refine lintegral_congr fun z => lintegral_congr fun zs => ?_
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero]
  rfl

omit [Nonempty T] in
/-- **Jensen for the recursion**: `cascadeRec k ms μs G ≤ ∫ G d(μ₁ ⊗ ⋯ ⊗ μ_k)` when all
`0 < m_p ≤ 1`. In particular Talagrand's hypothesis (14.4), `𝔼 exp F < ∞`, gives
`cascadeRec < ∞`. -/
theorem cascadeRec_le_lintegral_pi (k : ℕ) :
    ∀ (ms : Fin k → ℝ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
      {G : (Fin k → T) → ℝ≥0∞}, Measurable G → (∀ i, 0 < ms i) → (∀ i, ms i ≤ 1) →
      cascadeRec k ms μs G ≤ ∫⁻ zs, G zs ∂Measure.pi μs := by
  induction k with
  | zero =>
    intro ms μs _ G hG _ _
    rw [cascadeRec_zero, Measure.pi_of_empty, lintegral_dirac' _ hG]
    exact le_of_eq (congrArg G (Subsingleton.elim _ _))
  | succ k ih =>
    intro ms μs _ G hG hpos hle
    have hm : 0 < ms 0 := hpos 0
    rw [cascadeRec_succ, lintegral_pi_fin_succ μs hG]
    have hR : Measurable fun z => cascadeRec k (Fin.tail ms) (Fin.tail μs)
        (fun zs => G (Fin.cons z zs)) := measurable_cascadeRec_cons k _ _ hG
    calc (∫⁻ z, cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
            ∂μs 0) ^ (1 / ms 0)
        ≤ ((∫⁻ z, cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
            ∂μs 0) ^ ms 0) ^ (1 / ms 0) :=
          ENNReal.rpow_le_rpow (lintegral_rpow_le_rpow_lintegral _ hR.aemeasurable hm (hle 0))
            (by positivity)
      _ = ∫⁻ z, cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ∂μs 0 := by
          rw [← ENNReal.rpow_mul, mul_one_div_cancel hm.ne', ENNReal.rpow_one]
      _ ≤ ∫⁻ z, (∫⁻ zs, G (Fin.cons z zs) ∂Measure.pi (Fin.tail μs)) ∂μs 0 :=
          lintegral_mono fun z => ih (Fin.tail ms) (Fin.tail μs)
            (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
            (fun i => hpos i.succ) (fun i => hle i.succ)

/-- **Theorem 14.2.1 under Talagrand's hypothesis (14.4)**: if `𝔼 exp F(z₁, …, z_k) < ∞`, then
`𝔼 log ∑_α v_α exp F(α) = F₁`. -/
theorem integral_log_cascadeSum_exp_div_eq_of_lintegral_ne_top (k : ℕ) (ms : Fin k → ℝ)
    (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)] {F : (Fin k → T) → ℝ}
    (hF : Measurable F) (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (hfin : ∫⁻ zs, ENNReal.ofReal (Real.exp (F zs)) ∂Measure.pi μs ≠ ∞) :
    ∫ ω, Real.log ((cascadeSum k (fun zs => ENNReal.ofReal (Real.exp (F zs))) ω).toReal
        / (cascadeSum k (fun _ => 1) ω).toReal) ∂cascadeLaw k ms μs
      = parisiRec k ms μs F :=
  integral_log_cascadeSum_exp_div_eq k ms μs hF hsm hpos hlt
    (ne_top_of_le_ne_top hfin (cascadeRec_le_lintegral_pi k ms μs
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hF)) hpos fun i => (hlt i).le))

end

end ProbabilityTheory
