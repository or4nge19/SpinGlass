/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.CoupledFixedWeights

/-!
# The bound (14.147) for coupled copies (Talagrand Vol. II, §14.6)

Integrating the fixed-weights inequality `coupled_fixed_weights` over the law of the cascade
weights and evaluating both endpoints by Theorem 14.2.1 conditionally on the disorder and the root
marks (`integral_log_cascadeSum_div_prod_eq`) gives Talagrand's **(14.147)** for the
two-dimensional scheme (14.130)–(14.136) with `0 < n₁ < ⋯ < n_κ < 1` (`coupled_bound`,
`coupled_bound'`):

`(1/N) 𝔼 G₁ ≤ 2 log 2 + Y₀(λ) − λu
    − (1/2) ∑_{ℓ,ℓ'} ∑_{1 ≤ p ≤ κ} n_p (θ(ρ^{ℓ,ℓ'}_{p+1}) − θ(ρ^{ℓ,ℓ'}_p)) + D(ρ_{κ+1})`.

Here `G₁` is the recursion (14.160) in the marks of `H⁰` of the constrained sum
`∑_{R_{1,2}=u} e^{-H_N(σ¹)-H_N(σ²)-H⁰}`, `Y₀(λ)` is the recursion (14.144)–(14.145) of
`∑ᵢ log (ch Aᵢ ch Bᵢ ch λ + sh Aᵢ sh Bᵢ sh λ)` in the marks `y`, averaged over the root marks, and
`D = pairDiagDefect` is the tangent-line defect of `ξ` at the top values `ρ_{κ+1}`, which vanishes
under Talagrand's (14.132) `ρ^{ℓ,ℓ}_{κ+1} = 1`, `ρ^{1,2}_{κ+1} = u` (`coupled_bound_of_top`).
Two remarks:

* Talagrand's (14.137) omits the diagonal term `α = γ` of the Gibbs average; the bound proved
  here is the correct one, and is stronger than his (14.147) by `(θ(1) + θ(u))(1 − n_κ) ≥ 0`.
* The top values `ρ_{κ+1}` are left free. A last level with `n_{κ+1} = 1` and marks independent
  between the copies (the situation of Proposition 14.6.3) is then absorbed *exactly* into `D`
  and `Y₀`, with no continuity argument in the `n_p`.
-/

open MeasureTheory ProbabilityTheory Finset Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

/-! ### The level sum and the diagonal defect -/

/-- Talagrand's level sum `∑_{ℓ,ℓ'} ∑_{1 ≤ p ≤ κ} n_p (θ(ρ^{ℓ,ℓ'}_{p+1}) − θ(ρ^{ℓ,ℓ'}_p))` of
(14.147), for `n_p = ns ⟨p - 1⟩`. -/
def coupledLevelSum {κ : ℕ} (ξ : ℝ → ℝ) (ρ : Fin 2 → Fin 2 → ℕ → ℝ) (ns : Fin κ → ℝ) : ℝ :=
  ∑ l : Fin 2, ∑ l' : Fin 2, ∑ p : Fin κ,
    ns p * (parisiTheta ξ (ρ l l' (p.val + 2)) - parisiTheta ξ (ρ l l' (p.val + 1)))

/-- **The tangent-line defect at the diagonal**: for the self-overlaps `R = (1, u; u, 1)` and the
top values `d^{ℓ,ℓ'}` of the parameters,
`D = (1/2) ∑_{ℓ,ℓ'} (ξ(R^{ℓ,ℓ'}) − ξ(d^{ℓ,ℓ'}) − (R^{ℓ,ℓ'} − d^{ℓ,ℓ'}) ξ'(d^{ℓ,ℓ'}))`; it is
nonnegative for a convex `ξ` and vanishes under (14.132). -/
def pairDiagDefect (ξ : ℝ → ℝ) (u : ℝ) (d : Fin 2 → Fin 2 → ℝ) : ℝ :=
  (1 / 2) * ∑ l : Fin 2, ∑ l' : Fin 2, (ξ (if l = l' then 1 else u) - ξ (d l l')
    - ((if l = l' then 1 else u) - d l l') * deriv ξ (d l l'))

lemma pairDiagDefect_eq (ξ : ℝ → ℝ) (u : ℝ) (d : Fin 2 → Fin 2 → ℝ) :
    pairDiagDefect ξ u d
      = (1 / 2) * pairDiagConst ξ u d
        + (1 / 2) * ∑ l : Fin 2, ∑ l' : Fin 2, parisiTheta ξ (d l l') := by
  unfold pairDiagDefect pairDiagConst parisiTheta
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l' _ => ?_
  ring

/-- Under Talagrand's (14.132) the diagonal defect vanishes. -/
lemma pairDiagDefect_diag (ξ : ℝ → ℝ) (u : ℝ) :
    pairDiagDefect ξ u (fun l l' => if l = l' then 1 else u) = 0 := by
  rw [pairDiagDefect_eq, pairDiagConst_diag]
  simp only [Fin.sum_univ_two]
  norm_num
  try ring

/-- The defect is nonnegative when `ξ` lies above its tangent lines at the top values. -/
lemma pairDiagDefect_nonneg (ξ : ℝ → ℝ) {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1)
    {S : Set ℝ} {d : Fin 2 → Fin 2 → ℝ} (hd : ∀ l l', d l l' ∈ S)
    (htan : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ q ∈ S, ξ q + (x - q) * deriv ξ q ≤ ξ x) :
    0 ≤ pairDiagDefect ξ u d := by
  unfold pairDiagDefect
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun l' _ => ?_)
  have hR : (if l = l' then (1 : ℝ) else u) ∈ Icc (-1 : ℝ) 1 := by
    split_ifs
    · exact ⟨by norm_num, le_refl 1⟩
    · exact hu
  have := htan _ hR _ (hd l l')
  linarith

/-- Summation by parts for the level sum: with `m₀ = 0` and `m_{κ+1} = 1`,
`∑_{r ≤ κ} A_r (m_{r+1} − m_r) = A_κ − ∑_{p < κ} m_{p+1} (A_{p+1} − A_p)`. -/
lemma sum_range_mul_mExt_sub {κ : ℕ} (ns : Fin κ → ℝ) (A : ℕ → ℝ) :
    ∑ r ∈ Finset.range (κ + 1), A r * (mExt ns (r + 1) - mExt ns r)
      = A κ - ∑ p ∈ Finset.range κ, mExt ns (p + 1) * (A (p + 1) - A p) := by
  have h := Finset.sum_range_mul_sub_add_sub_mul (fun j => mExt ns j) A (κ + 1)
  rw [mExt_eq_one_of_le ns (le_refl (κ + 1)), mExt_zero, one_mul, zero_mul, sub_zero,
    Finset.sum_add_distrib, Finset.sum_range_succ (fun i => mExt ns (i + 1) * (A (i + 1) - A i)),
    mExt_eq_one_of_le ns (le_refl (κ + 1)), one_mul] at h
  have h2 : ∑ r ∈ Finset.range (κ + 1), A r * (mExt ns (r + 1) - mExt ns r)
      = ∑ i ∈ Finset.range (κ + 1), (mExt ns (i + 1) - mExt ns i) * A i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h2]
  linarith

/-- The level sum as the summation-by-parts term of the level bound. -/
lemma coupledLevelSum_eq {κ : ℕ} (ξ : ℝ → ℝ) (ρ : Fin 2 → Fin 2 → ℕ → ℝ) (ns : Fin κ → ℝ) :
    ∑ p ∈ Finset.range κ, mExt ns (p + 1)
        * ((∑ l : Fin 2, ∑ l' : Fin 2, parisiTheta ξ (ρ l l' (p + 1 + 1)))
          - ∑ l : Fin 2, ∑ l' : Fin 2, parisiTheta ξ (ρ l l' (p + 1)))
      = coupledLevelSum ξ ρ ns := by
  unfold coupledLevelSum
  rw [Finset.sum_range]
  have h1 : ∀ p : Fin κ, mExt ns (p.val + 1)
        * ((∑ l : Fin 2, ∑ l' : Fin 2, parisiTheta ξ (ρ l l' (p.val + 1 + 1)))
          - ∑ l : Fin 2, ∑ l' : Fin 2, parisiTheta ξ (ρ l l' (p.val + 1)))
      = ∑ l : Fin 2, ∑ l' : Fin 2,
          ns p * (parisiTheta ξ (ρ l l' (p.val + 2)) - parisiTheta ξ (ρ l l' (p.val + 1))) := by
    intro p
    rw [mExt_val_succ, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun p _ => h1 p]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun l _ => Finset.sum_comm)

/-! ### The bound, integrated over the cascade -/

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
variable (N : ℕ) {κ : ℕ} {J : Type u} [Fintype J] [DecidableEq J]

omit [DecidableEq J] in
/-- `Y₁(z₀) = parisiRec(Y_{κ+1}(z₀, ·))` is integrable in the root marks: it is
`log cascadeRec(F₂) − N log 4` for the endpoint branch functions `F₂`, whose logarithm is
integrable by `integrable_log_cascadeRec`. -/
theorem integrable_parisiRec_pairCoshF (ns : Fin κ → ℝ) (hsm : StrictMono ns)
    (hpos : ∀ i, 0 < ns i) (hlt : ∀ i, ns i < 1) (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ) (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) :
    Integrable (fun θ : Ω × (Fin N × J → ℝ) => parisiRec κ ns
      (siteGaussianMarks (Fin N × J) κ vs) (pairCoshF N κ lam a K₀ K θ.2))
      (Pm.prod (rootMarksLaw N v₀)) := by
  have hle1 : ∀ i, ns i ≤ 1 := fun i => (hlt i).le
  set G₂ : Ω × (Fin N × J → ℝ) → (Fin κ → Fin N × J → ℝ) → ℝ≥0∞ :=
    fun θ x => pairHamG N κ (fun _ => 1) 0 lam a K₀ K θ.2 x with hG₂
  -- pointwise: `log cascadeRec(F₂) = N log 4 + Y₁`
  have hpt : ∀ θ : Ω × (Fin N × J → ℝ),
      Real.log (cascadeRec κ ns (siteGaussianMarks (Fin N × J) κ vs) (G₂ θ)).toReal
        = (N : ℝ) * Real.log 4 + parisiRec κ ns (siteGaussianMarks (Fin N × J) κ vs)
            (pairCoshF N κ lam a K₀ K θ.2) := by
    intro θ
    have he : G₂ θ = fun x => ENNReal.ofReal (Real.exp
        ((N : ℝ) * Real.log 4 + pairCoshF N κ lam a K₀ K θ.2 x)) := funext fun x => by
      rw [hG₂]
      simp only
      rw [pairHamG, pairBranchZX_one_zero_eq_exp]
    rw [he, ← parisiRec_const_add κ ns _ (measurable_pairCoshF' N κ lam a K₀ K θ.2) hpos
      (cascadeRec_ofReal_exp_pairCoshF_ne_top N κ ns vs hpos hle1 lam a K₀ K θ.2)
      ((N : ℝ) * Real.log 4)]
    rfl
  have hHf0 : Measurable fun _ : Ω => (0 : EnergySpace N) := measurable_const
  have hGm₂ : Measurable (Function.uncurry G₂) :=
    measurable_pairHamG_branchParam N κ (fun _ => 1) hHf0 lam a K₀ K
  have hGpos₂ : ∀ θ x, 0 < G₂ θ x :=
    fun θ x => pairHamG_pos N κ (fun _ => zero_le_one) ⟨fun _ _ => true, one_pos⟩ _ _ _ _ _ _ _
  have hGfin₂ : ∀ θ x, G₂ θ x ≠ ∞ := fun θ x => ENNReal.ofReal_ne_top
  have hint₂ : ∫⁻ θ, ∫⁻ x, G₂ θ x
      ∂Measure.pi (siteGaussianMarks (Fin N × J) κ vs) ∂Pm.prod (rootMarksLaw N v₀) ≠ ∞ :=
    lintegral_lintegral_pairHamG_ne_top N (fun _ => zero_le_one) (fun _ => (0 : EnergySpace N))
      hHf0 (fun σ => by simp) lam a K₀ K v₀ vs
  have hlog₂ : ∫⁻ θ, ∫⁻ x, ‖Real.log (G₂ θ x).toReal‖ₑ
      ∂Measure.pi (siteGaussianMarks (Fin N × J) κ vs) ∂Pm.prod (rootMarksLaw N v₀) ≠ ∞ :=
    lintegral_lintegral_enorm_log_pairHamG_ne_top N (fun _ => zero_le_one) (fun _ => le_refl 1)
      (σ₀ := fun _ _ => true) rfl hHf0 (fun τ => by simp) lam a K₀ K v₀ vs
  have hfin₂ : ∀ θ, cascadeRec κ ns (siteGaussianMarks (Fin N × J) κ vs) (G₂ θ) ≠ ∞ := fun θ =>
    cascadeRec_pairHamG_ne_top N κ ns vs hpos hle1 (fun _ => zero_le_one) _ _ _ _ _ _
  have hI := integrable_log_cascadeRec κ (Pm.prod (rootMarksLaw N v₀)) ns
    (siteGaussianMarks (Fin N × J) κ vs) G₂ hsm hpos hlt hGm₂ hGpos₂ hGfin₂ hint₂ hlog₂ hfin₂
  refine (hI.sub (integrable_const ((N : ℝ) * Real.log 4))).congr
    (Filter.Eventually.of_forall fun θ => ?_)
  change Real.log (cascadeRec κ ns (siteGaussianMarks (Fin N × J) κ vs) (G₂ θ)).toReal
      - (N : ℝ) * Real.log 4 = _
  rw [hpt θ]
  ring

omit [DecidableEq J] in
/-- **The endpoint `Y₀` (14.143)–(14.145)**: the expectation of the logarithm of the recursion of
the unconstrained branch functions is `N log 4 + 𝔼_{y₀} Y₁(y₀)`, `Y₁` the recursion of
`Y_{κ+1} = ∑ᵢ log (ch Aᵢ ch Bᵢ ch λ + sh Aᵢ sh Bᵢ sh λ)` over the marks along a branch. -/
theorem integral_log_cascadeRec_coupledEndG (ns : Fin κ → ℝ) (hsm : StrictMono ns)
    (hpos : ∀ i, 0 < ns i) (hlt : ∀ i, ns i < 1) (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (L₀ L₀' : Fin 2 → J → ℝ) (L L' : Fin κ → Fin 2 → J → ℝ) (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) :
    ∫ θ, Real.log (cascadeRec κ ns (siteGaussianMarks (Fin N × J) κ vs)
        (coupledEndG N lam a L₀ L₀' L L' θ)).toReal ∂Pm.prod (rootMarksLaw N v₀)
      = (N : ℝ) * Real.log 4 + ∫ z₀, parisiRec κ ns (siteGaussianMarks (Fin N × J) κ vs)
          (pairCoshF N κ lam a (L₀ + L₀') (fun p => L p + L' p) z₀) ∂rootMarksLaw N v₀ := by
  have hle1 : ∀ i, ns i ≤ 1 := fun i => (hlt i).le
  -- pointwise: `parisiRec_const_add`
  have hpt : ∀ θ : Ω × (Fin N × J → ℝ),
      Real.log (cascadeRec κ ns (siteGaussianMarks (Fin N × J) κ vs)
          (coupledEndG N lam a L₀ L₀' L L' θ)).toReal
        = (N : ℝ) * Real.log 4 + parisiRec κ ns (siteGaussianMarks (Fin N × J) κ vs)
            (pairCoshF N κ lam a (L₀ + L₀') (fun p => L p + L' p) θ.2) := by
    intro θ
    have he : coupledEndG N lam a L₀ L₀' L L' θ = fun x => ENNReal.ofReal (Real.exp
        ((N : ℝ) * Real.log 4 + pairCoshF N κ lam a (L₀ + L₀') (fun p => L p + L' p) θ.2 x)) :=
      funext fun x => coupledEndG_eq N lam a L₀ L₀' L L' θ x
    rw [he, ← parisiRec_const_add κ ns _
      (measurable_pairCoshF' N κ lam a (L₀ + L₀') (fun p => L p + L' p) θ.2) hpos
      (cascadeRec_ofReal_exp_pairCoshF_ne_top N κ ns vs hpos hle1 lam a (L₀ + L₀')
        (fun p => L p + L' p) θ.2) ((N : ℝ) * Real.log 4)]
    rfl
  have hY := integrable_parisiRec_pairCoshF N ns hsm hpos hlt lam a (L₀ + L₀')
    (fun p => L p + L' p) v₀ vs (Pm := Pm)
  -- measurability of `Y₁` in the root marks
  have hYm : Measurable fun z₀ : Fin N × J → ℝ => parisiRec κ ns
      (siteGaussianMarks (Fin N × J) κ vs)
      (pairCoshF N κ lam a (L₀ + L₀') (fun p => L p + L' p) z₀) := by
    have hc := (continuous_pairCoshF N κ (J := J) lam a).comp
      ((continuous_const.prodMk (continuous_fst.prodMk continuous_snd)) :
        Continuous fun p : (Fin N × J → ℝ) × (Fin κ → Fin N × J → ℝ) =>
          (((0 : EnergySpace N), L₀ + L₀', fun p => L p + L' p), (p.1, p.2)))
    have hG : Measurable (Function.uncurry fun (z₀ : Fin N × J → ℝ)
        (x : Fin κ → Fin N × J → ℝ) => ENNReal.ofReal (Real.exp
          (pairCoshF N κ lam a (L₀ + L₀') (fun p => L p + L' p) z₀ x))) := by
      have h := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hc.measurable)
      exact h
    have hR : Measurable fun z₀ : Fin N × J → ℝ => cascadeRec κ ns
        (siteGaussianMarks (Fin N × J) κ vs) (fun x => ENNReal.ofReal (Real.exp
          (pairCoshF N κ lam a (L₀ + L₀') (fun p => L p + L' p) z₀ x))) :=
      measurable_cascadeRec_prod κ ns (siteGaussianMarks (Fin N × J) κ vs) hG
    exact hR.ennreal_toReal.log
  have hmap : (Pm.prod (rootMarksLaw (J := J) N v₀)).map Prod.snd = rootMarksLaw (J := J) N v₀ := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have h2 : ∫ z₀, parisiRec κ ns (siteGaussianMarks (Fin N × J) κ vs)
        (pairCoshF N κ lam a (L₀ + L₀') (fun p => L p + L' p) z₀) ∂rootMarksLaw N v₀
      = ∫ θ, parisiRec κ ns (siteGaussianMarks (Fin N × J) κ vs)
        (pairCoshF N κ lam a (L₀ + L₀') (fun p => L p + L' p) θ.2)
        ∂Pm.prod (rootMarksLaw N v₀) := by
    conv_lhs => rw [← hmap]
    exact integral_map measurable_snd.aemeasurable hYm.aestronglyMeasurable
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add (integrable_const _) hY,
    integral_const, probReal_univ, one_smul, h2]

/-- **Talagrand's (14.147), integrated over the cascade** (Vol. II, §14.6): for the
two-dimensional scheme with parameters `ρ^{ℓ,ℓ'}_p`, `0 ≤ p ≤ κ + 1`, factors `L, L'` on
disjoint columns, an external field `a`, `0 < n₁ < ⋯ < n_κ < 1` and any `λ`,

`(1/N) 𝔼 log F₁ ≤ −λu + (1/N) 𝔼 log F₂ + (1/2) c₀ + (1/2) ∑_{r ≤ κ} θ_r (n_{r+1} − n_r)`,

where `F₁ = cascadeRec(∑_{R_{1,2}=u} e^{−H_N(σ¹)−H_N(σ²)−H⁰})`, `F₂ = cascadeRec(∏ᵢ 4(ch ch ch λ +
sh sh sh λ))` are the recursions (14.145) over the marks along a branch, averaged over the disorder
and the root marks, `c₀ = pairDiagConst ξ u (ρ_{κ+1})` and `θ_r = ∑_{ℓ,ℓ'} θ(ρ^{ℓ,ℓ'}_{r+1})`. -/
theorem coupled_bound (hN : 0 < N) (ξ : ℝ → ℝ) (ρ : Fin 2 → Fin 2 → ℕ → ℝ) (u : ℝ)
    (hρ0 : ∀ l l', ρ l l' 0 = 0) {S : Set ℝ} (hρS : ∀ l l' r, ρ l l' r ∈ S)
    (htan : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ q ∈ S, ξ q + (x - q) * deriv ξ q ≤ ξ x) (h0 : deriv ξ 0 = 0)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) {J₁ : Finset J} {L₀ L₀' : Fin 2 → J → ℝ}
    {L L' : Fin κ → Fin 2 → J → ℝ}
    (hC0 : ∀ l l', (v₀ : ℝ) * gram L₀ l l' = deriv ξ (ρ l l' 1) - deriv ξ (ρ l l' 0))
    (hC : ∀ (p : Fin κ) l l', (vs p : ℝ) * gram (L p) l l'
      = deriv ξ (ρ l l' (p.val + 2)) - deriv ξ (ρ l l' (p.val + 1)))
    (hL0 : ∀ l j, j ∉ J₁ → L₀ l j = 0) (hL : ∀ p l j, j ∉ J₁ → L p l j = 0)
    (hL0' : ∀ l j, j ∈ J₁ → L₀' l j = 0) (hL' : ∀ p l j, j ∈ J₁ → L' p l j = 0)
    (a : Fin N × Fin 2 → ℝ) (lam : ℝ) (ns : Fin κ → ℝ) (hsm : StrictMono ns)
    (hpos : ∀ i, 0 < ns i) (hlt : ∀ i, ns i < 1)
    (hu : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    (1 / (N : ℝ)) * ∫ θ, Real.log (cascadeRec κ ns (siteGaussianMarks (Fin N × J) κ vs)
        (coupledG N u a L₀ L₀' L L' ξ G₀ 1 θ)).toReal ∂Pm.prod (rootMarksLaw N v₀)
      ≤ -(lam * u) + (1 / (N : ℝ)) * ∫ θ, Real.log (cascadeRec κ ns
            (siteGaussianMarks (Fin N × J) κ vs)
            (coupledEndG N lam a L₀ L₀' L L' θ)).toReal ∂Pm.prod (rootMarksLaw N v₀)
        + ((1 / 2) * pairDiagConst ξ u (fun l l' => ρ l l' (κ + 1))
          + (1 / 2) * ∑ r ∈ Finset.range (κ + 1),
            (∑ l : Fin 2, ∑ l' : Fin 2, parisiTheta ξ (ρ l l' (r + 1)))
              * (mExt ns (r + 1) - mExt ns r)) := by
  classical
  obtain ⟨σ₀, hσ₀⟩ := hu
  have hcσ₀ : constraintR N u σ₀ = 1 := by
    unfold constraintR
    rw [ite_eq_left hσ₀]
  have hle1 : ∀ i, ns i ≤ 1 := fun i => (hlt i).le
  set c₀ := pairDiagConst ξ u fun l l' => ρ l l' (κ + 1) with hc₀
  set θf : ℕ → ℝ := fun r => ∑ l : Fin 2, ∑ l' : Fin 2, parisiTheta ξ (ρ l l' (r + 1)) with hθf
  set Pw := cascadeWeightsLaw κ ns with hPw
  -- the branch functions at `t = 1`
  have hHf1 : Measurable fun ω => Real.sqrt 1 • G₀.U ω := by
    have h := G₀.measU.const_smul (Real.sqrt 1)
    exact h
  have hGm₁ : Measurable (Function.uncurry (coupledG N u a L₀ L₀' L L' ξ G₀ 1)) :=
    measurable_pairHamG_branchParam N κ (constraintR N u) hHf1 0 a
      (Real.sqrt (1 - 1) • L₀ + L₀') (fun p => Real.sqrt (1 - 1) • L p + L' p)
  have hGpos₁ : ∀ θ x, 0 < coupledG N u a L₀ L₀' L L' ξ G₀ 1 θ x :=
    fun θ x => coupledG_pos N u ⟨σ₀, hσ₀⟩ a L₀ L₀' L L' ξ G₀ 1 θ x
  have hGfin₁ : ∀ θ x, coupledG N u a L₀ L₀' L L' ξ G₀ 1 θ x ≠ ∞ :=
    fun θ x => ENNReal.ofReal_ne_top
  have hint₁ : ∫⁻ θ, ∫⁻ x, coupledG N u a L₀ L₀' L L' ξ G₀ 1 θ x
      ∂Measure.pi (siteGaussianMarks (Fin N × J) κ vs) ∂Pm.prod (rootMarksLaw N v₀) ≠ ∞ :=
    lintegral_lintegral_pairHamG_ne_top N (constraintR_nonneg N u) (fun ω => Real.sqrt 1 • G₀.U ω)
      hHf1 (fun σ => G₀.lintegral_ofReal_exp_neg_smul_add_ne_top (Real.sqrt 1) (σ 0) (σ 1)) 0 a
      (Real.sqrt (1 - 1) • L₀ + L₀') (fun p => Real.sqrt (1 - 1) • L p + L' p) v₀ vs
  have hlog₁ : ∫⁻ θ, ∫⁻ x, ‖Real.log (coupledG N u a L₀ L₀' L L' ξ G₀ 1 θ x).toReal‖ₑ
      ∂Measure.pi (siteGaussianMarks (Fin N × J) κ vs) ∂Pm.prod (rootMarksLaw N v₀) ≠ ∞ :=
    lintegral_lintegral_enorm_log_pairHamG_ne_top N (constraintR_nonneg N u)
      (constraintR_le_one N u) hcσ₀ hHf1
      (fun τ => integrable_smul_apply_disorder N ξ G₀ (Real.sqrt 1) τ) 0 a
      (Real.sqrt (1 - 1) • L₀ + L₀') (fun p => Real.sqrt (1 - 1) • L p + L' p) v₀ vs
  have hfin₁ : ∀ θ, cascadeRec κ ns (siteGaussianMarks (Fin N × J) κ vs)
      (coupledG N u a L₀ L₀' L L' ξ G₀ 1 θ) ≠ ∞ :=
    fun θ => cascadeRec_coupledG_ne_top N ns vs hpos hle1 u a L₀ L₀' L L' ξ G₀ 1 θ
  -- the branch functions at the endpoint
  have hHf0 : Measurable fun _ : Ω => (0 : EnergySpace N) := measurable_const
  have hGm₂ : Measurable (Function.uncurry (coupledEndG N lam a L₀ L₀' L L')) :=
    measurable_pairHamG_branchParam N κ (fun _ => 1) hHf0 lam a (L₀ + L₀') (fun p => L p + L' p)
  have hGpos₂ : ∀ (θ : Ω × (Fin N × J → ℝ)) x, 0 < coupledEndG N lam a L₀ L₀' L L' θ x :=
    fun θ x => pairHamG_pos N κ (fun _ => zero_le_one) ⟨σ₀, one_pos⟩ _ _ _ _ _ _ _
  have hGfin₂ : ∀ (θ : Ω × (Fin N × J → ℝ)) x, coupledEndG N lam a L₀ L₀' L L' θ x ≠ ∞ :=
    fun θ x => ENNReal.ofReal_ne_top
  have hint₂ : ∫⁻ θ, ∫⁻ x, coupledEndG N lam a L₀ L₀' L L' θ x
      ∂Measure.pi (siteGaussianMarks (Fin N × J) κ vs) ∂Pm.prod (rootMarksLaw N v₀) ≠ ∞ :=
    lintegral_lintegral_pairHamG_ne_top N (fun _ => zero_le_one) (fun _ => (0 : EnergySpace N))
      hHf0 (fun σ => by simp) lam a (L₀ + L₀') (fun p => L p + L' p) v₀ vs
  have hlog₂ : ∫⁻ θ, ∫⁻ x, ‖Real.log (coupledEndG N lam a L₀ L₀' L L' θ x).toReal‖ₑ
      ∂Measure.pi (siteGaussianMarks (Fin N × J) κ vs) ∂Pm.prod (rootMarksLaw N v₀) ≠ ∞ :=
    lintegral_lintegral_enorm_log_pairHamG_ne_top N (fun _ => zero_le_one) (fun _ => le_refl 1)
      (σ₀ := σ₀) rfl hHf0 (fun τ => by simp) lam a (L₀ + L₀') (fun p => L p + L' p) v₀ vs
  have hfin₂ : ∀ θ : Ω × (Fin N × J → ℝ), cascadeRec κ ns (siteGaussianMarks (Fin N × J) κ vs)
      (coupledEndG N lam a L₀ L₀' L L' θ) ≠ ∞ := fun θ =>
    cascadeRec_pairHamG_ne_top N κ ns vs hpos hle1 (fun _ => zero_le_one) _ _ _ _ _ _
  -- the three terms as functions of the weights
  set f₁ : CascadeWeights κ × ((Ω × (Fin N × J → ℝ)) × CascadeMarks (Fin N × J → ℝ) κ) → ℝ :=
    fun q => Real.log ((cascadeSum κ (coupledG N u a L₀ L₀' L L' ξ G₀ 1 q.2.1)
      (cascadeZip κ (q.1, q.2.2))).toReal
        / (cascadeSum κ (fun _ => 1) (cascadeZip κ (q.1, q.2.2))).toReal) with hf₁def
  set f₂ : CascadeWeights κ × ((Ω × (Fin N × J → ℝ)) × CascadeMarks (Fin N × J → ℝ) κ) → ℝ :=
    fun q => Real.log ((cascadeSum κ (coupledEndG N lam a L₀ L₀' L L' q.2.1)
      (cascadeZip κ (q.1, q.2.2))).toReal
        / (cascadeSum κ (fun _ => 1) (cascadeZip κ (q.1, q.2.2))).toReal) with hf₂def
  have hf₁ : Integrable f₁ (Pw.prod (coupledLaw N Pm v₀ vs)) :=
    integrable_log_cascadeSum_div_prod κ (Pm.prod (rootMarksLaw N v₀)) ns
      (siteGaussianMarks (Fin N × J) κ vs) (coupledG N u a L₀ L₀' L L' ξ G₀ 1) hsm hpos hlt hGm₁
      hGpos₁ hGfin₁ hint₁ hlog₁
  have hf₂ : Integrable f₂ (Pw.prod (coupledLaw N Pm v₀ vs)) :=
    integrable_log_cascadeSum_div_prod κ (Pm.prod (rootMarksLaw N v₀)) ns
      (siteGaussianMarks (Fin N × J) κ vs) (coupledEndG N lam a L₀ L₀' L L') hsm hpos hlt hGm₂
      hGpos₂ hGfin₂ hint₂ hlog₂
  set Φ₁ : CascadeWeights κ → ℝ := fun w =>
    (1 / (N : ℝ)) * ∫ q, f₁ (w, q) ∂coupledLaw N Pm v₀ vs with hΦ₁
  set Φ₂ : CascadeWeights κ → ℝ := fun w =>
    (1 / (N : ℝ)) * ∫ q, f₂ (w, q) ∂coupledLaw N Pm v₀ vs with hΦ₂
  set Ψ : CascadeWeights κ → ℝ := fun w => ∫ t in (0 : ℝ)..1,
    levelBoundLaw κ (Pm.prod (rootMarksLaw N v₀)) (siteGaussianMarks (Fin N × J) κ vs)
      (coupledG N u a L₀ L₀' L L' ξ G₀) c₀ θf w t with hΨ
  have hintΦ₁ : Integrable Φ₁ Pw := hf₁.integral_prod_left.const_mul _
  have hintΦ₂ : Integrable Φ₂ Pw := hf₂.integral_prod_left.const_mul _
  have hintΨ : Integrable Ψ Pw := by
    have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
    have hswap : Integrable (Function.uncurry fun (w : CascadeWeights κ) (t : ℝ) =>
        levelBoundLaw κ (Pm.prod (rootMarksLaw N v₀)) (siteGaussianMarks (Fin N × J) κ vs)
          (coupledG N u a L₀ L₀' L L' ξ G₀) c₀ θf w t)
        (Pw.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
      Integrable.of_bound (measurable_levelBoundLaw κ _ _ _
        (measurable_coupledG N u a L₀ L₀' L L' ξ G₀) c₀ θf).aestronglyMeasurable
        ((1 / 2) * |c₀| + (1 / 2) * ∑ r ∈ Finset.range (κ + 1), |θf r|)
        (Filter.Eventually.of_forall fun q => by
          rw [Real.norm_eq_abs]
          exact abs_levelBoundLaw_le κ _ _ _ (measurable_coupledG N u a L₀ L₀' L L' ξ G₀) c₀ θf
            q.1 q.2)
    have hIP := hswap.integral_prod_left
    refine hIP.congr (Filter.Eventually.of_forall fun w => ?_)
    change (∫ y in Set.Ioc (0 : ℝ) 1, levelBoundLaw κ (Pm.prod (rootMarksLaw N v₀))
        (siteGaussianMarks (Fin N × J) κ vs) (coupledG N u a L₀ L₀' L L' ξ G₀) c₀ θf w y)
      = ∫ t in (0 : ℝ)..1, levelBoundLaw κ (Pm.prod (rootMarksLaw N v₀))
        (siteGaussianMarks (Fin N × J) κ vs) (coupledG N u a L₀ L₀' L L' ξ G₀) c₀ θf w t
    exact (intervalIntegral.integral_of_le (zero_le_one' ℝ)).symm
  -- the fixed-weights bound, almost surely in the weights
  have hae : ∀ᵐ w ∂Pw, Φ₁ w ≤ -(lam * u) + Φ₂ w + Ψ w := by
    filter_upwards [ae_weightSum_ne_zero_ne_top κ ns hsm hpos hlt] with w hw
    exact coupled_fixed_weights N hN ξ ρ u hρ0 hρS htan h0 G₀ v₀ vs hC0 hC hL0 hL hL0' hL' a lam
      w hw.1 hw.2 ⟨σ₀, hσ₀⟩
  have hle : ∫ w, Φ₁ w ∂Pw ≤ -(lam * u) + (∫ w, Φ₂ w ∂Pw) + ∫ w, Ψ w ∂Pw := by
    have h1 := integral_mono_ae hintΦ₁ (((integrable_const (-(lam * u))).add hintΦ₂).add hintΨ)
      hae
    calc ∫ w, Φ₁ w ∂Pw ≤ ∫ w, ((fun _ : CascadeWeights κ => -(lam * u)) + Φ₂ + Ψ) w ∂Pw := h1
      _ = (∫ w, ((fun _ : CascadeWeights κ => -(lam * u)) + Φ₂) w ∂Pw) + ∫ w, Ψ w ∂Pw :=
          integral_add ((integrable_const _).add hintΦ₂) hintΨ
      _ = ((∫ _w, -(lam * u) ∂Pw) + ∫ w, Φ₂ w ∂Pw) + ∫ w, Ψ w ∂Pw := by
          rw [show (∫ w, ((fun _ : CascadeWeights κ => -(lam * u)) + Φ₂) w ∂Pw)
              = (∫ _w, -(lam * u) ∂Pw) + ∫ w, Φ₂ w ∂Pw from
            integral_add (integrable_const _) hintΦ₂]
      _ = -(lam * u) + (∫ w, Φ₂ w ∂Pw) + ∫ w, Ψ w ∂Pw := by
          rw [integral_const, probReal_univ, one_smul]
  -- the endpoints, by Theorem 14.2.1 conditionally on the disorder and the root marks
  have hΦ₁int : ∫ w, Φ₁ w ∂Pw = (1 / (N : ℝ)) * ∫ θ, Real.log (cascadeRec κ ns
      (siteGaussianMarks (Fin N × J) κ vs)
      (coupledG N u a L₀ L₀' L L' ξ G₀ 1 θ)).toReal ∂Pm.prod (rootMarksLaw N v₀) := by
    have h := integral_log_cascadeSum_div_prod_eq κ (Pm.prod (rootMarksLaw N v₀)) ns
      (siteGaussianMarks (Fin N × J) κ vs) (coupledG N u a L₀ L₀' L L' ξ G₀ 1) hsm hpos hlt hGm₁
      hGpos₁ hGfin₁ hint₁ hlog₁ hfin₁
    have h2 : ∫ w, Φ₁ w ∂Pw = (1 / (N : ℝ)) * ∫ z, f₁ z ∂Pw.prod (coupledLaw N Pm v₀ vs) := by
      rw [integral_prod f₁ hf₁]
      exact integral_const_mul _ _
    exact h2.trans (congrArg (fun r => (1 / (N : ℝ)) * r) h)
  have hΦ₂int : ∫ w, Φ₂ w ∂Pw = (1 / (N : ℝ)) * ∫ θ, Real.log (cascadeRec κ ns
      (siteGaussianMarks (Fin N × J) κ vs)
      (coupledEndG N lam a L₀ L₀' L L' θ)).toReal ∂Pm.prod (rootMarksLaw N v₀) := by
    have h := integral_log_cascadeSum_div_prod_eq κ (Pm.prod (rootMarksLaw N v₀)) ns
      (siteGaussianMarks (Fin N × J) κ vs) (coupledEndG N lam a L₀ L₀' L L') hsm hpos hlt hGm₂
      hGpos₂ hGfin₂ hint₂ hlog₂ hfin₂
    have h2 : ∫ w, Φ₂ w ∂Pw = (1 / (N : ℝ)) * ∫ z, f₂ z ∂Pw.prod (coupledLaw N Pm v₀ vs) := by
      rw [integral_prod f₂ hf₂]
      exact integral_const_mul _ _
    exact h2.trans (congrArg (fun r => (1 / (N : ℝ)) * r) h)
  -- the bound, by Proposition 14.3.3
  have hΨint : ∫ w, Ψ w ∂Pw = (1 / 2) * c₀ + (1 / 2) * ∑ r ∈ Finset.range (κ + 1),
      θf r * (mExt ns (r + 1) - mExt ns r) :=
    integral_intervalIntegral_levelBoundLaw κ (Pm.prod (rootMarksLaw N v₀))
      (siteGaussianMarks (Fin N × J) κ vs) (coupledG N u a L₀ L₀' L L' ξ G₀)
      (measurable_coupledG N u a L₀ L₀' L L' ξ G₀)
      (fun t θ x => coupledG_pos N u ⟨σ₀, hσ₀⟩ a L₀ L₀' L L' ξ G₀ t θ x) ns hsm hpos hlt
      (fun t θ => cascadeRec_coupledG_ne_top N ns vs hpos hle1 u a L₀ L₀' L L' ξ G₀ t θ) c₀ θf
  rw [hΦ₁int, hΦ₂int, hΨint] at hle
  exact hle

/-- **Talagrand's (14.147)** in his form: for the two-dimensional scheme with
`0 < n₁ < ⋯ < n_κ < 1` and any `λ`,

`(1/N) 𝔼 G₁ ≤ 2 log 2 + Y₀(λ) − λu
    − (1/2) ∑_{ℓ,ℓ'} ∑_{1 ≤ p ≤ κ} n_p (θ(ρ^{ℓ,ℓ'}_{p+1}) − θ(ρ^{ℓ,ℓ'}_p)) + D(ρ_{κ+1})`,

with `Y₀(λ) = (1/N) 𝔼_{y₀} Y₁(y₀)`, `Y₁` the recursion (14.145) of
`Y_{κ+1} = ∑ᵢ log (ch Aᵢ ch Bᵢ ch λ + sh Aᵢ sh Bᵢ sh λ)`, and the diagonal defect `D`, which
vanishes under (14.132). -/
theorem coupled_bound' (hN : 0 < N) (ξ : ℝ → ℝ) (ρ : Fin 2 → Fin 2 → ℕ → ℝ) (u : ℝ)
    (hρ0 : ∀ l l', ρ l l' 0 = 0) {S : Set ℝ} (hρS : ∀ l l' r, ρ l l' r ∈ S)
    (htan : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ q ∈ S, ξ q + (x - q) * deriv ξ q ≤ ξ x) (h0 : deriv ξ 0 = 0)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) {J₁ : Finset J} {L₀ L₀' : Fin 2 → J → ℝ}
    {L L' : Fin κ → Fin 2 → J → ℝ}
    (hC0 : ∀ l l', (v₀ : ℝ) * gram L₀ l l' = deriv ξ (ρ l l' 1) - deriv ξ (ρ l l' 0))
    (hC : ∀ (p : Fin κ) l l', (vs p : ℝ) * gram (L p) l l'
      = deriv ξ (ρ l l' (p.val + 2)) - deriv ξ (ρ l l' (p.val + 1)))
    (hL0 : ∀ l j, j ∉ J₁ → L₀ l j = 0) (hL : ∀ p l j, j ∉ J₁ → L p l j = 0)
    (hL0' : ∀ l j, j ∈ J₁ → L₀' l j = 0) (hL' : ∀ p l j, j ∈ J₁ → L' p l j = 0)
    (a : Fin N × Fin 2 → ℝ) (lam : ℝ) (ns : Fin κ → ℝ) (hsm : StrictMono ns)
    (hpos : ∀ i, 0 < ns i) (hlt : ∀ i, ns i < 1)
    (hu : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    (1 / (N : ℝ)) * ∫ θ, Real.log (cascadeRec κ ns (siteGaussianMarks (Fin N × J) κ vs)
        (coupledG N u a L₀ L₀' L L' ξ G₀ 1 θ)).toReal ∂Pm.prod (rootMarksLaw N v₀)
      ≤ 2 * Real.log 2 + (1 / (N : ℝ)) * (∫ z₀, parisiRec κ ns (siteGaussianMarks (Fin N × J) κ vs)
            (pairCoshF N κ lam a (L₀ + L₀') (fun p => L p + L' p) z₀) ∂rootMarksLaw N v₀)
          - lam * u - (1 / 2) * coupledLevelSum ξ ρ ns
          + pairDiagDefect ξ u (fun l l' => ρ l l' (κ + 1)) := by
  refine (coupled_bound N hN ξ ρ u hρ0 hρS htan h0 G₀ v₀ vs hC0 hC hL0 hL hL0' hL' a lam ns hsm
    hpos hlt hu).trans (le_of_eq ?_)
  rw [integral_log_cascadeRec_coupledEndG N ns hsm hpos hlt lam a L₀ L₀' L L' v₀ vs,
    sum_range_mul_mExt_sub, coupledLevelSum_eq, pairDiagDefect_eq]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [hlog4]
  field_simp
  ring

/-- **(14.147) under Talagrand's (14.132)** `ρ^{ℓ,ℓ}_{κ+1} = 1`, `ρ^{1,2}_{κ+1} = u`: the diagonal
defect vanishes. -/
theorem coupled_bound_of_top (hN : 0 < N) (ξ : ℝ → ℝ) (ρ : Fin 2 → Fin 2 → ℕ → ℝ) (u : ℝ)
    (hρ0 : ∀ l l', ρ l l' 0 = 0) (hρtop : ∀ l l', ρ l l' (κ + 1) = if l = l' then 1 else u)
    {S : Set ℝ} (hρS : ∀ l l' r, ρ l l' r ∈ S)
    (htan : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ q ∈ S, ξ q + (x - q) * deriv ξ q ≤ ξ x) (h0 : deriv ξ 0 = 0)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) {J₁ : Finset J} {L₀ L₀' : Fin 2 → J → ℝ}
    {L L' : Fin κ → Fin 2 → J → ℝ}
    (hC0 : ∀ l l', (v₀ : ℝ) * gram L₀ l l' = deriv ξ (ρ l l' 1) - deriv ξ (ρ l l' 0))
    (hC : ∀ (p : Fin κ) l l', (vs p : ℝ) * gram (L p) l l'
      = deriv ξ (ρ l l' (p.val + 2)) - deriv ξ (ρ l l' (p.val + 1)))
    (hL0 : ∀ l j, j ∉ J₁ → L₀ l j = 0) (hL : ∀ p l j, j ∉ J₁ → L p l j = 0)
    (hL0' : ∀ l j, j ∈ J₁ → L₀' l j = 0) (hL' : ∀ p l j, j ∈ J₁ → L' p l j = 0)
    (a : Fin N × Fin 2 → ℝ) (lam : ℝ) (ns : Fin κ → ℝ) (hsm : StrictMono ns)
    (hpos : ∀ i, 0 < ns i) (hlt : ∀ i, ns i < 1)
    (hu : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    (1 / (N : ℝ)) * ∫ θ, Real.log (cascadeRec κ ns (siteGaussianMarks (Fin N × J) κ vs)
        (coupledG N u a L₀ L₀' L L' ξ G₀ 1 θ)).toReal ∂Pm.prod (rootMarksLaw N v₀)
      ≤ 2 * Real.log 2 + (1 / (N : ℝ)) * (∫ z₀, parisiRec κ ns (siteGaussianMarks (Fin N × J) κ vs)
            (pairCoshF N κ lam a (L₀ + L₀') (fun p => L p + L' p) z₀) ∂rootMarksLaw N v₀)
          - lam * u - (1 / 2) * coupledLevelSum ξ ρ ns := by
  have h := coupled_bound' N hN ξ ρ u hρ0 hρS htan h0 G₀ v₀ vs hC0 hC hL0 hL hL0' hL' a lam ns
    hsm hpos hlt hu
  have hd : (fun l l' => ρ l l' (κ + 1)) = fun l l' => if l = l' then (1 : ℝ) else u :=
    funext fun l => funext fun l' => hρtop l l'
  rw [hd, pairDiagDefect_diag, add_zero] at h
  exact h

end

end SpinGlass
