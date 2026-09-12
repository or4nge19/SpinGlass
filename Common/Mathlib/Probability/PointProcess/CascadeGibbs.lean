/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.PointProcess.CascadeTilt
import Common.Mathlib.Probability.PointProcess.CascadeIdentities

/-!
# The cascade Gibbs average is the tilted average

Talagrand's identity (14.26)–(14.27) of Vol. II: for a cascade with weights `u*_α` and marks
`z_α`, and a positive function `G` of the marks (`G = exp F`),

`𝔼 ⟨A/G⟩ = 𝔼 (W₁ ⋯ W_k (A/G))`,   where `⟨A/G⟩ = (∑_α u*_α A(z_α)) / (∑_α u*_α G(z_α))`

(`lintegral_cascadeSum_div_cascadeSum`): the Gibbs average of a function of the marks, for the
weights `u*_α G(z_α)`, is the average against the tilted law of `CascadeTilt`. The case `G`
constant is `lintegral_cascadeSum_div_cascadeSum_one_prod` together with `cascadeTilt_const`.

The proof is by the *one-insertion moment* of a cascade,

`𝔼 (∑_α u*_α A(z_α)) (∑_α u*_α G(z_α))^{a-1} = 𝔼(W₁ ⋯ W_k (A/G)) · 𝔼 (∑_α u*_α G(z_α))^a`

(`lintegral_cascadeSum_mul_rpow`), the companion with a numerator of Proposition 14.2.2
(`lintegral_cascadeSum_rpow`, the case `A = G`), proved by induction on the number of levels from
the one-level identity `lintegral_pdSum_mul_rpow_pdSum`. Talagrand instead differentiates (14.8)
in the direction of `A`; this route stays inside the `ℝ≥0∞` calculus.
-/

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace ProbabilityTheory

open ENNReal

universe u

variable {T : Type u} [MeasurableSpace T] [Nonempty T]

/-- The reflexive `HasLaw`, used to read the one-level identities as statements about
`pdProcess` itself. -/
private lemma hasLaw_id {M : Type*} [MeasurableSpace M] (μ : Measure M) :
    HasLaw (id : M → M) μ μ := ⟨aemeasurable_id, Measure.map_id⟩

/-- **The one-insertion moment of a cascade**: for `0 < a < m₁`,
`𝔼 (∑_α u*_α A(z_α))(∑_α u*_α G(z_α))^{a-1} = 𝔼(W₁ ⋯ W_k (A/G)) · 𝔼(∑_α u*_α G(z_α))^a`.
At `A = G` it is Proposition 14.2.2 (`lintegral_cascadeSum_rpow`). -/
theorem lintegral_cascadeSum_mul_rpow (k : ℕ) :
    ∀ (ms : Fin k → ℝ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
      {A G : (Fin k → T) → ℝ≥0∞}, Measurable A → Measurable G →
      (∀ zs, 0 < G zs) → ∫⁻ zs, G zs ∂Measure.pi μs ≠ ∞ →
      ∀ {a : ℝ}, 0 < a → StrictMono (Fin.cons a ms : Fin (k + 1) → ℝ) → (∀ i, ms i < 1) →
      ∫⁻ ω, cascadeSum k A ω * cascadeSum k G ω ^ (a - 1) ∂cascadeLaw k ms μs
        = cascadeTilt k ms μs G (fun zs => A zs / G zs)
          * ∫⁻ ω, cascadeSum k G ω ^ a ∂cascadeLaw k ms μs := by
  induction k with
  | zero =>
    intro ms μs _ A G hA hG hGpos hfin a _ _ _
    have hG0 : G Fin.elim0 ≠ 0 := (hGpos _).ne'
    have hGtop : G Fin.elim0 ≠ ∞ := by
      rw [Measure.pi_of_empty, lintegral_dirac' _ hG] at hfin
      exact fun h => hfin (by rw [← h]; exact congrArg G (Subsingleton.elim _ _))
    have hf1 : Measurable fun ω : CascadeSpace T 0 =>
        cascadeSum 0 A ω * cascadeSum 0 G ω ^ (a - 1) :=
      (measurable_cascadeSum 0 hA).mul ((measurable_cascadeSum 0 hG).pow_const _)
    have hf2 : Measurable fun ω : CascadeSpace T 0 => cascadeSum 0 G ω ^ a :=
      (measurable_cascadeSum 0 hG).pow_const _
    rw [cascadeLaw_zero, lintegral_dirac' _ hf1, lintegral_dirac' _ hf2]
    simp only [cascadeSum_zero, cascadeTilt_zero]
    rw [ENNReal.rpow_sub _ _ hG0 hGtop, ENNReal.rpow_one, div_eq_mul_inv, div_eq_mul_inv,
      mul_right_comm, mul_assoc]
  | succ k ih =>
    intro ms μs _ A G hA hG hGpos hfin a ha0 hsm hlt
    have hm : 0 < ms 0 := pos_of_strictMono_cons ha0 hsm 0
    have ham : a < ms 0 := lt_zero_of_strictMono_cons hsm
    have hm1 : ms 0 < 1 := hlt 0
    have hsm' : StrictMono (Fin.cons (ms 0) (Fin.tail ms) : Fin (k + 1) → ℝ) := by
      rw [Fin.cons_self_tail]
      exact strictMono_of_strictMono_cons hsm
    have hposTail : ∀ i, 0 < Fin.tail ms i := fun i => pos_of_strictMono_cons hm hsm' i
    have hposAll : ∀ i, 0 < ms i := fun i => pos_of_strictMono_cons ha0 hsm i
    have hfinTail : ∀ᵐ z ∂μs 0,
        ∫⁻ zs, G (Fin.cons z zs) ∂Measure.pi (Fin.tail μs) ≠ ∞ :=
      ae_lintegral_pi_cons_ne_top k μs hG hfin
    -- the marked weights
    set η := (μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs)) with hη
    set vA : T × CascadeSpace T k → ℝ≥0∞ :=
      fun p => cascadeSum k (fun zs => A (Fin.cons p.1 zs)) p.2 with hvA_def
    set vG : T × CascadeSpace T k → ℝ≥0∞ :=
      fun p => cascadeSum k (fun zs => G (Fin.cons p.1 zs)) p.2 with hvG_def
    have hvA : Measurable vA :=
      measurable_cascadeSum_prod k (α := T) (G := fun z zs => A (Fin.cons z zs))
        (hA.comp measurable_fin_cons)
    have hvG : Measurable vG :=
      measurable_cascadeSum_prod k (α := T) (G := fun z zs => G (Fin.cons z zs))
        (hG.comp measurable_fin_cons)
    have hlaw := hasLaw_superCounting_cascadeLaw k ms μs
    have hsumA : ∀ ω, cascadeSum (k + 1) A ω = pdSum vA (superCounting ω) := fun ω => rfl
    have hsumG : ∀ ω, cascadeSum (k + 1) G ω = pdSum vG (superCounting ω) := fun ω => rfl
    -- the mark law is positive and has a finite `m₀`-moment
    have hVpos : ∀ᵐ p ∂η, 0 < vG p := by
      rw [hη, Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const hvG)]
      refine Filter.Eventually.of_forall fun z => ?_
      exact ae_cascadeSum_pos k (Fin.tail ms) (Fin.tail μs)
        (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (fun zs => hGpos _) hposTail
    have hR : Measurable fun z => cascadeRec k (Fin.tail ms) (Fin.tail μs)
        (fun zs => G (Fin.cons z zs)) := measurable_cascadeRec_cons k _ _ hG
    -- the level-`k` moment of the marked weights
    have hQ : ∀ z, ∫⁻ ω', vG (z, ω') ^ ms 0 ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
        = cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
          * cascadeConst k (ms 0) (Fin.tail ms) := fun z =>
      lintegral_cascadeSum_rpow k (Fin.tail ms) (Fin.tail μs)
        (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        hm hsm' (fun i => hlt i.succ)
    have hQ' : ∀ z, ∫⁻ ω, cascadeSum k (fun zs => G (Fin.cons z zs)) ω ^ ms 0
        ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
        = cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
          * cascadeConst k (ms 0) (Fin.tail ms) := hQ
    obtain ⟨hCk0, hCktop⟩ := cascadeConst_pos_ne_top k hm hsm' (fun i => hlt i.succ)
    set R := cascadeRec (k + 1) ms μs G with hRdef
    have hR0 : R ≠ 0 := (cascadeRec_pos (k + 1) ms μs hG hGpos hposAll).ne'
    have hRtop : R ≠ ∞ :=
      cascadeRec_ne_top (k + 1) ms μs hG hposAll (fun i => (hlt i).le) hfin
    have hRm0 : R ^ ms 0 ≠ 0 := by
      simpa using (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 hR0) hm.le).ne'
    have hRmtop : R ^ ms 0 ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hm.le hRtop
    have hκ : ∫⁻ p, vG p ^ ms 0 ∂η = cascadeConst k (ms 0) (Fin.tail ms) * R ^ ms 0 := by
      rw [hη, lintegral_prod _ (hvG.pow_const _).aemeasurable]
      simp_rw [hQ]
      rw [lintegral_mul_const _ (hR.pow_const _), hRdef, cascadeRec_succ, ← ENNReal.rpow_mul,
        one_div_mul_cancel hm.ne', ENNReal.rpow_one, mul_comm]
    have hκtop : ∫⁻ p, vG p ^ ms 0 ∂η ≠ ∞ := by
      rw [hκ]
      exact ENNReal.mul_ne_top hCktop hRmtop
    -- transport both sides to the Poisson–Dirichlet process
    have htransA : ∫⁻ ω, cascadeSum (k + 1) A ω * cascadeSum (k + 1) G ω ^ (a - 1)
          ∂cascadeLaw (k + 1) ms μs
        = ∫⁻ N, pdSum vA N * pdSum vG N ^ (a - 1) ∂pdProcess (ms 0) η := by
      simp_rw [hsumA, hsumG]
      exact hlaw.lintegral_comp
        ((measurable_pdSum hvA).mul ((measurable_pdSum hvG).pow_const _)).aemeasurable
    have htransG : ∫⁻ ω, cascadeSum (k + 1) G ω ^ a ∂cascadeLaw (k + 1) ms μs
        = ∫⁻ N, pdSum vG N ^ a ∂pdProcess (ms 0) η := by
      simp_rw [hsumG]
      exact hlaw.lintegral_comp ((measurable_pdSum hvG).pow_const _).aemeasurable
    rw [htransA, htransG]
    -- the moment of `G` alone, from the same one-level identity
    have hidlaw := hasLaw_id (pdProcess (ms 0) η)
    have haepos : ∀ᵐ N ∂pdProcess (ms 0) η, 0 < pdSum vG N :=
      hidlaw.ae_pdSum_pos hm hvG hVpos
    have haetop : ∀ᵐ N ∂pdProcess (ms 0) η, pdSum vG N < ∞ :=
      hidlaw.ae_pdSum_lt_top hm hm1 hvG hκtop
    have haeVfin : ∀ᵐ p ∂η, vG p < ∞ := by
      filter_upwards [ae_lt_top (hvG.pow_const (ms 0)) hκtop] with p hp
      by_contra hcon
      rw [not_lt, top_le_iff] at hcon
      rw [hcon, ENNReal.top_rpow_of_pos hm] at hp
      exact hp.ne rfl
    have hmomG : ∫⁻ N, pdSum vG N ^ a ∂pdProcess (ms 0) η
        = ENNReal.ofReal (pdOneConst (ms 0) a (stableConst (ms 0))
            (∫⁻ p, vG p ^ ms 0 ∂η).toReal) * ∫⁻ p, vG p ^ ms 0 ∂η := by
      have hpt : ∀ᵐ N ∂pdProcess (ms 0) η,
          pdSum vG N ^ a = pdSum vG N * pdSum vG N ^ (a - 1) := by
        filter_upwards [haepos, haetop] with N h0 htop
        conv_lhs => rw [show a = 1 + (a - 1) by ring]
        rw [ENNReal.rpow_add _ _ h0.ne' htop.ne, ENNReal.rpow_one]
      rw [lintegral_congr_ae hpt,
        lintegral_pdSum_mul_rpow_pdSum hm hm1 η hvG hvG hVpos hκtop ham]
      congr 1
      refine lintegral_congr_ae ?_
      filter_upwards [hVpos, haeVfin] with p h0 htop
      conv_rhs => rw [show ms 0 = 1 + (ms 0 - 1) by ring]
      rw [ENNReal.rpow_add _ _ h0.ne' htop.ne, ENNReal.rpow_one]
    rw [lintegral_pdSum_mul_rpow_pdSum hm hm1 η hvA hvG hVpos hκtop ham, hmomG]
    -- the numerator, by the induction hypothesis
    have hin : ∀ᵐ z ∂μs 0, ∫⁻ ω', vA (z, ω') * vG (z, ω') ^ (ms 0 - 1)
          ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
        = cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
            (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs))
          * (cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
            * cascadeConst k (ms 0) (Fin.tail ms)) := by
      filter_upwards [hfinTail] with z hz
      have h := ih (Fin.tail ms) (Fin.tail μs) (A := fun zs => A (Fin.cons z zs))
        (G := fun zs => G (Fin.cons z zs))
        (hA.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (fun zs => hGpos _) hz hm hsm' (fun i => hlt i.succ)
      rw [hQ' z] at h
      exact h
    have hTm : Measurable fun z => cascadeTilt k (Fin.tail ms) (Fin.tail μs)
        (fun zs => G (Fin.cons z zs)) (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs)) :=
      measurable_cascadeTilt_prod k (Fin.tail ms) (Fin.tail μs)
        (Gs := fun z zs => G (Fin.cons z zs))
        (As := fun z zs => A (Fin.cons z zs) / G (Fin.cons z zs))
        (hG.comp measurable_fin_cons)
        ((hA.comp measurable_fin_cons).div (hG.comp measurable_fin_cons))
    have hI : Measurable fun z => cascadeRec k (Fin.tail ms) (Fin.tail μs)
        (fun zs => G (Fin.cons z zs)) ^ ms 0
      * cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
          (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs)) := (hR.pow_const _).mul hTm
    have hnum : ∫⁻ p, vA p * vG p ^ (ms 0 - 1) ∂η
        = cascadeTilt (k + 1) ms μs G (fun zs => A zs / G zs) * ∫⁻ p, vG p ^ ms 0 ∂η := by
      rw [hη, lintegral_prod (fun p : T × CascadeSpace T k => vA p * vG p ^ (ms 0 - 1))
        (hvA.mul (hvG.pow_const _)).aemeasurable]
      rw [lintegral_congr_ae hin, cascadeTilt_succ, hκ]
      have hW : ∀ z : T, cascadeW k ms μs G z
            * cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
                (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs))
          = (R ^ ms 0)⁻¹ * (cascadeRec k (Fin.tail ms) (Fin.tail μs)
              (fun zs => G (Fin.cons z zs)) ^ ms 0
            * cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
                (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs))) := by
        intro z
        rw [cascadeW, ENNReal.div_rpow_of_nonneg _ _ hm.le, div_eq_mul_inv]
        ring
      simp_rw [hW]
      rw [lintegral_const_mul _ hI]
      have hL : ∫⁻ z, cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
              (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs))
            * (cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
              * cascadeConst k (ms 0) (Fin.tail ms)) ∂μs 0
          = (∫⁻ z, cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
              * cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
                  (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs)) ∂μs 0)
            * cascadeConst k (ms 0) (Fin.tail ms) := by
        rw [← lintegral_mul_const _ hI]
        exact lintegral_congr fun z => by ring
      rw [hL]
      have halg : ∀ I : ℝ≥0∞,
          ((R ^ ms 0)⁻¹ * I) * (cascadeConst k (ms 0) (Fin.tail ms) * R ^ ms 0)
            = (I * cascadeConst k (ms 0) (Fin.tail ms)) * ((R ^ ms 0)⁻¹ * R ^ ms 0) := by
        intro I
        ring
      rw [halg, ENNReal.inv_mul_cancel hRm0 hRmtop, mul_one]
    rw [hnum]
    ring

/-- **The `(m₀ - 1)`-moment of the marked weights of a cascade**: over the product of the first
mark law and the law of the remaining levels,

`∫ vA vG^{m₀-1} dη = 𝔼(W₁ ⋯ W_k (A/G)) · ∫ vG^{m₀} dη`,

where `vA(z, ω) = ∑_α u*_α A(z, z_α)` and `vG(z, ω) = ∑_α u*_α G(z, z_α)`. This is the step of
the induction in `lintegral_cascadeSum_mul_rpow` that converts the numerator produced by the
one-level identity into the tilted average, isolated for reuse in the second-order identities. -/
theorem lintegral_prod_cascadeSum_mul_rpow (k : ℕ) (ms : Fin (k + 1) → ℝ)
    (μs : Fin (k + 1) → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
    {A G : (Fin (k + 1) → T) → ℝ≥0∞} (hA : Measurable A) (hG : Measurable G)
    (hGpos : ∀ zs, 0 < G zs) (hfin : ∫⁻ zs, G zs ∂Measure.pi μs ≠ ∞)
    (hsm : StrictMono ms) (hlt : ∀ i, ms i < 1) (hpos : ∀ i, 0 < ms i) :
    ∫⁻ p : T × CascadeSpace T k, cascadeSum k (fun zs => A (Fin.cons p.1 zs)) p.2
        * cascadeSum k (fun zs => G (Fin.cons p.1 zs)) p.2 ^ (ms 0 - 1)
        ∂(μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs))
      = cascadeTilt (k + 1) ms μs G (fun zs => A zs / G zs)
        * ∫⁻ p : T × CascadeSpace T k, cascadeSum k (fun zs => G (Fin.cons p.1 zs)) p.2 ^ ms 0
          ∂(μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs)) := by
  have hm : 0 < ms 0 := hpos 0
  have hm1 : ms 0 < 1 := hlt 0
  have hsm' : StrictMono (Fin.cons (ms 0) (Fin.tail ms) : Fin (k + 1) → ℝ) := by
    rw [Fin.cons_self_tail]
    exact hsm
  have hfinTail : ∀ᵐ z ∂μs 0,
      ∫⁻ zs, G (Fin.cons z zs) ∂Measure.pi (Fin.tail μs) ≠ ∞ :=
    ae_lintegral_pi_cons_ne_top k μs hG hfin
  have hvA : Measurable fun p : T × CascadeSpace T k =>
      cascadeSum k (fun zs => A (Fin.cons p.1 zs)) p.2 :=
    measurable_cascadeSum_prod k (α := T) (G := fun z zs => A (Fin.cons z zs))
      (hA.comp measurable_fin_cons)
  have hvG : Measurable fun p : T × CascadeSpace T k =>
      cascadeSum k (fun zs => G (Fin.cons p.1 zs)) p.2 :=
    measurable_cascadeSum_prod k (α := T) (G := fun z zs => G (Fin.cons z zs))
      (hG.comp measurable_fin_cons)
  have hR : Measurable fun z => cascadeRec k (Fin.tail ms) (Fin.tail μs)
      (fun zs => G (Fin.cons z zs)) := measurable_cascadeRec_cons k _ _ hG
  have hQ : ∀ z, ∫⁻ ω', cascadeSum k (fun zs => G (Fin.cons z zs)) ω' ^ ms 0
      ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
      = cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
        * cascadeConst k (ms 0) (Fin.tail ms) := fun z =>
    lintegral_cascadeSum_rpow k (Fin.tail ms) (Fin.tail μs)
      (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
      hm hsm' (fun i => hlt i.succ)
  set R := cascadeRec (k + 1) ms μs G with hRdef
  have hR0 : R ≠ 0 := (cascadeRec_pos (k + 1) ms μs hG hGpos hpos).ne'
  have hRtop : R ≠ ∞ := cascadeRec_ne_top (k + 1) ms μs hG hpos (fun i => (hlt i).le) hfin
  have hRm0 : R ^ ms 0 ≠ 0 := by
    simpa using (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 hR0) hm.le).ne'
  have hRmtop : R ^ ms 0 ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hm.le hRtop
  have hκ : ∫⁻ p : T × CascadeSpace T k, cascadeSum k (fun zs => G (Fin.cons p.1 zs)) p.2 ^ ms 0
        ∂(μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs))
      = cascadeConst k (ms 0) (Fin.tail ms) * R ^ ms 0 := by
    rw [lintegral_prod (fun p : T × CascadeSpace T k =>
      cascadeSum k (fun zs => G (Fin.cons p.1 zs)) p.2 ^ ms 0) (hvG.pow_const _).aemeasurable]
    simp_rw [hQ]
    rw [lintegral_mul_const _ (hR.pow_const _), hRdef, cascadeRec_succ, ← ENNReal.rpow_mul,
      one_div_mul_cancel hm.ne', ENNReal.rpow_one, mul_comm]
  have hin : ∀ᵐ z ∂μs 0, ∫⁻ ω', cascadeSum k (fun zs => A (Fin.cons z zs)) ω'
        * cascadeSum k (fun zs => G (Fin.cons z zs)) ω' ^ (ms 0 - 1)
        ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
      = cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
          (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs))
        * (cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
          * cascadeConst k (ms 0) (Fin.tail ms)) := by
    filter_upwards [hfinTail] with z hz
    have h := lintegral_cascadeSum_mul_rpow k (Fin.tail ms) (Fin.tail μs)
      (A := fun zs => A (Fin.cons z zs)) (G := fun zs => G (Fin.cons z zs))
      (hA.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
      (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
      (fun zs => hGpos _) hz hm hsm' (fun i => hlt i.succ)
    rw [hQ z] at h
    exact h
  have hTm : Measurable fun z => cascadeTilt k (Fin.tail ms) (Fin.tail μs)
      (fun zs => G (Fin.cons z zs)) (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs)) :=
    measurable_cascadeTilt_prod k (Fin.tail ms) (Fin.tail μs)
      (Gs := fun z zs => G (Fin.cons z zs))
      (As := fun z zs => A (Fin.cons z zs) / G (Fin.cons z zs))
      (hG.comp measurable_fin_cons)
      ((hA.comp measurable_fin_cons).div (hG.comp measurable_fin_cons))
  have hI : Measurable fun z => cascadeRec k (Fin.tail ms) (Fin.tail μs)
      (fun zs => G (Fin.cons z zs)) ^ ms 0
    * cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
        (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs)) := (hR.pow_const _).mul hTm
  rw [lintegral_prod (fun p : T × CascadeSpace T k =>
    cascadeSum k (fun zs => A (Fin.cons p.1 zs)) p.2
      * cascadeSum k (fun zs => G (Fin.cons p.1 zs)) p.2 ^ (ms 0 - 1))
    (hvA.mul (hvG.pow_const _)).aemeasurable]
  rw [lintegral_congr_ae hin, cascadeTilt_succ, hκ]
  have hW : ∀ z : T, cascadeW k ms μs G z
        * cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
            (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs))
      = (R ^ ms 0)⁻¹ * (cascadeRec k (Fin.tail ms) (Fin.tail μs)
          (fun zs => G (Fin.cons z zs)) ^ ms 0
        * cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
            (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs))) := by
    intro z
    rw [cascadeW, ENNReal.div_rpow_of_nonneg _ _ hm.le, div_eq_mul_inv]
    ring
  simp_rw [hW]
  rw [lintegral_const_mul _ hI]
  have hL : ∫⁻ z, cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
          (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs))
        * (cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
          * cascadeConst k (ms 0) (Fin.tail ms)) ∂μs 0
      = (∫⁻ z, cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
          * cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
              (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs)) ∂μs 0)
        * cascadeConst k (ms 0) (Fin.tail ms) := by
    rw [← lintegral_mul_const _ hI]
    exact lintegral_congr fun z => by ring
  rw [hL]
  have halg : ∀ I : ℝ≥0∞,
      ((R ^ ms 0)⁻¹ * I) * (cascadeConst k (ms 0) (Fin.tail ms) * R ^ ms 0)
        = (I * cascadeConst k (ms 0) (Fin.tail ms)) * ((R ^ ms 0)⁻¹ * R ^ ms 0) := by
    intro I
    ring
  rw [halg, ENNReal.inv_mul_cancel hRm0 hRmtop, mul_one]

/-- **Talagrand's identity (14.26)–(14.27)**: for weights `u*_α G(z_α)`, the cascade Gibbs average
of `A/G` is the tilted average `𝔼(W₁ ⋯ W_k (A/G))`. -/
theorem lintegral_cascadeSum_div_cascadeSum : ∀ (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {A G : (Fin k → T) → ℝ≥0∞}, Measurable A → Measurable G →
    (∀ zs, 0 < G zs) → ∫⁻ zs, G zs ∂Measure.pi μs ≠ ∞ →
    StrictMono ms → (∀ i, 0 < ms i) → (∀ i, ms i < 1) →
    ∫⁻ ω, cascadeSum k A ω / cascadeSum k G ω ∂cascadeLaw k ms μs
      = cascadeTilt k ms μs G (fun zs => A zs / G zs)
  | 0, ms, μs, _, A, G, hA, hG, _, _, _, _, _ => by
      have hf : Measurable fun ω : CascadeSpace T 0 => cascadeSum 0 A ω / cascadeSum 0 G ω :=
        (measurable_cascadeSum 0 hA).div (measurable_cascadeSum 0 hG)
      rw [cascadeLaw_zero, lintegral_dirac' _ hf]
      rfl
  | k + 1, ms, μs, _, A, G, hA, hG, hGpos, hfin, hsm, hpos, hlt => by
      have hm : 0 < ms 0 := hpos 0
      have hm1 : ms 0 < 1 := hlt 0
      have hsm' : StrictMono (Fin.cons (ms 0) (Fin.tail ms) : Fin (k + 1) → ℝ) := by
        rw [Fin.cons_self_tail]
        exact hsm
      have hposTail : ∀ i, 0 < Fin.tail ms i := fun i => hpos i.succ
      have hfinTail : ∀ᵐ z ∂μs 0,
          ∫⁻ zs, G (Fin.cons z zs) ∂Measure.pi (Fin.tail μs) ≠ ∞ :=
        ae_lintegral_pi_cons_ne_top k μs hG hfin
      set η := (μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs)) with hη
      set vA : T × CascadeSpace T k → ℝ≥0∞ :=
        fun p => cascadeSum k (fun zs => A (Fin.cons p.1 zs)) p.2 with hvA_def
      set vG : T × CascadeSpace T k → ℝ≥0∞ :=
        fun p => cascadeSum k (fun zs => G (Fin.cons p.1 zs)) p.2 with hvG_def
      have hvA : Measurable vA :=
        measurable_cascadeSum_prod k (α := T) (G := fun z zs => A (Fin.cons z zs))
          (hA.comp measurable_fin_cons)
      have hvG : Measurable vG :=
        measurable_cascadeSum_prod k (α := T) (G := fun z zs => G (Fin.cons z zs))
          (hG.comp measurable_fin_cons)
      have hlaw := hasLaw_superCounting_cascadeLaw k ms μs
      have hsumA : ∀ ω, cascadeSum (k + 1) A ω = pdSum vA (superCounting ω) := fun ω => rfl
      have hsumG : ∀ ω, cascadeSum (k + 1) G ω = pdSum vG (superCounting ω) := fun ω => rfl
      have hVpos : ∀ᵐ p ∂η, 0 < vG p := by
        rw [hη, Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const hvG)]
        refine Filter.Eventually.of_forall fun z => ?_
        exact ae_cascadeSum_pos k (Fin.tail ms) (Fin.tail μs)
          (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
          (fun zs => hGpos _) hposTail
      have hR : Measurable fun z => cascadeRec k (Fin.tail ms) (Fin.tail μs)
          (fun zs => G (Fin.cons z zs)) := measurable_cascadeRec_cons k _ _ hG
      have hQ : ∀ z, ∫⁻ ω', vG (z, ω') ^ ms 0 ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
          = cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
            * cascadeConst k (ms 0) (Fin.tail ms) := fun z =>
        lintegral_cascadeSum_rpow k (Fin.tail ms) (Fin.tail μs)
          (G := fun zs => G (Fin.cons z zs))
          (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
          hm hsm' (fun i => hlt i.succ)
      have hQ' : ∀ z, ∫⁻ ω, cascadeSum k (fun zs => G (Fin.cons z zs)) ω ^ ms 0
          ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
          = cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
            * cascadeConst k (ms 0) (Fin.tail ms) := hQ
      obtain ⟨hCk0, hCktop⟩ := cascadeConst_pos_ne_top k hm hsm' (fun i => hlt i.succ)
      set R := cascadeRec (k + 1) ms μs G with hRdef
      have hR0 : R ≠ 0 := (cascadeRec_pos (k + 1) ms μs hG hGpos hpos).ne'
      have hRtop : R ≠ ∞ :=
        cascadeRec_ne_top (k + 1) ms μs hG hpos (fun i => (hlt i).le) hfin
      have hRm0 : R ^ ms 0 ≠ 0 := by
        simpa using (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 hR0) hm.le).ne'
      have hRmtop : R ^ ms 0 ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hm.le hRtop
      have hκ : ∫⁻ p, vG p ^ ms 0 ∂η = cascadeConst k (ms 0) (Fin.tail ms) * R ^ ms 0 := by
        rw [hη, lintegral_prod _ (hvG.pow_const _).aemeasurable]
        simp_rw [hQ]
        rw [lintegral_mul_const _ (hR.pow_const _), hRdef, cascadeRec_succ, ← ENNReal.rpow_mul,
          one_div_mul_cancel hm.ne', ENNReal.rpow_one, mul_comm]
      have hκtop : ∫⁻ p, vG p ^ ms 0 ∂η ≠ ∞ := by
        rw [hκ]
        exact ENNReal.mul_ne_top hCktop hRmtop
      have hκ0 : ∫⁻ p, vG p ^ ms 0 ∂η ≠ 0 := by
        rw [hκ]
        exact mul_ne_zero hCk0.ne' hRm0
      -- transport to the Poisson–Dirichlet process and use the `a = 0` identity
      have htrans : ∫⁻ ω, cascadeSum (k + 1) A ω / cascadeSum (k + 1) G ω
            ∂cascadeLaw (k + 1) ms μs
          = ∫⁻ N, pdSum vA N * (pdSum vG N)⁻¹ ∂pdProcess (ms 0) η := by
        simp_rw [hsumA, hsumG, div_eq_mul_inv]
        exact hlaw.lintegral_comp
          ((measurable_pdSum hvA).mul (measurable_pdSum hvG).inv).aemeasurable
      rw [htrans, lintegral_pdSum_mul_inv_pdSum hm hm1 η hvA hvG hVpos hκtop]
      -- the numerator, by the one-insertion moment at level `k`
      have hin : ∀ᵐ z ∂μs 0, ∫⁻ ω', vA (z, ω') * vG (z, ω') ^ (ms 0 - 1)
            ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
          = cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
              (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs))
            * (cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
              * cascadeConst k (ms 0) (Fin.tail ms)) := by
        filter_upwards [hfinTail] with z hz
        have h := lintegral_cascadeSum_mul_rpow k (Fin.tail ms) (Fin.tail μs)
          (A := fun zs => A (Fin.cons z zs)) (G := fun zs => G (Fin.cons z zs))
          (hA.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
          (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
          (fun zs => hGpos _) hz hm hsm' (fun i => hlt i.succ)
        rw [hQ' z] at h
        exact h
      have hTm : Measurable fun z => cascadeTilt k (Fin.tail ms) (Fin.tail μs)
          (fun zs => G (Fin.cons z zs)) (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs)) :=
        measurable_cascadeTilt_prod k (Fin.tail ms) (Fin.tail μs)
          (Gs := fun z zs => G (Fin.cons z zs))
          (As := fun z zs => A (Fin.cons z zs) / G (Fin.cons z zs))
          (hG.comp measurable_fin_cons)
          ((hA.comp measurable_fin_cons).div (hG.comp measurable_fin_cons))
      have hI : Measurable fun z => cascadeRec k (Fin.tail ms) (Fin.tail μs)
          (fun zs => G (Fin.cons z zs)) ^ ms 0
        * cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
            (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs)) := (hR.pow_const _).mul hTm
      have hnum : ∫⁻ p, vA p * vG p ^ (ms 0 - 1) ∂η
          = cascadeTilt (k + 1) ms μs G (fun zs => A zs / G zs) * ∫⁻ p, vG p ^ ms 0 ∂η := by
        rw [hη, lintegral_prod (fun p : T × CascadeSpace T k => vA p * vG p ^ (ms 0 - 1))
          (hvA.mul (hvG.pow_const _)).aemeasurable]
        rw [lintegral_congr_ae hin, cascadeTilt_succ, hκ]
        have hW : ∀ z : T, cascadeW k ms μs G z
              * cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
                  (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs))
            = (R ^ ms 0)⁻¹ * (cascadeRec k (Fin.tail ms) (Fin.tail μs)
                (fun zs => G (Fin.cons z zs)) ^ ms 0
              * cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
                  (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs))) := by
          intro z
          rw [cascadeW, ENNReal.div_rpow_of_nonneg _ _ hm.le, div_eq_mul_inv]
          ring
        simp_rw [hW]
        rw [lintegral_const_mul _ hI]
        have hL : ∫⁻ z, cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
                (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs))
              * (cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
                * cascadeConst k (ms 0) (Fin.tail ms)) ∂μs 0
            = (∫⁻ z, cascadeRec k (Fin.tail ms) (Fin.tail μs)
                  (fun zs => G (Fin.cons z zs)) ^ ms 0
                * cascadeTilt k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
                    (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs)) ∂μs 0)
              * cascadeConst k (ms 0) (Fin.tail ms) := by
          rw [← lintegral_mul_const _ hI]
          exact lintegral_congr fun z => by ring
        rw [hL]
        have halg : ∀ I : ℝ≥0∞,
            ((R ^ ms 0)⁻¹ * I) * (cascadeConst k (ms 0) (Fin.tail ms) * R ^ ms 0)
              = (I * cascadeConst k (ms 0) (Fin.tail ms)) * ((R ^ ms 0)⁻¹ * R ^ ms 0) := by
          intro I
          ring
        rw [halg, ENNReal.inv_mul_cancel hRm0 hRmtop, mul_one]
      rw [hnum, mul_assoc, ENNReal.mul_inv_cancel hκ0 hκtop, mul_one]

/-- **The case `F = 0` of (14.27)**: for a constant `G` every `W_p` is `1`, and the cascade Gibbs
average is the plain product average — the statement that the marks of a branch chosen according
to the cascade weights have the law of the marks. -/
theorem lintegral_cascadeSum_div_cascadeSum_const (k : ℕ) (ms : Fin k → ℝ)
    (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)] {A : (Fin k → T) → ℝ≥0∞}
    (hA : Measurable A) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ∞)
    (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1) :
    ∫⁻ ω, cascadeSum k A ω / cascadeSum k (fun _ => c) ω ∂cascadeLaw k ms μs
      = ∫⁻ zs, A zs / c ∂Measure.pi μs := by
  have hfin : ∫⁻ zs, (fun _ : Fin k → T => c) zs ∂Measure.pi μs ≠ ∞ := by
    rw [lintegral_const, measure_univ, mul_one]
    exact hctop
  rw [lintegral_cascadeSum_div_cascadeSum k ms μs hA measurable_const
    (fun _ => pos_iff_ne_zero.2 hc0) hfin hsm hpos hlt,
    cascadeTilt_const k ms μs hc0 hctop hpos (A := fun zs => A zs / c)
      (hA.div measurable_const)]

/-- **`𝔼⟨U²⟩ = 𝔼(W₁ ⋯ W_k U²)`**, the identity Talagrand uses just after (14.30): for `k ≤ r` the
tilted square is the cascade Gibbs average of `U²`, which is the term `p = k+1` of (14.32). -/
theorem cascadeTiltSq_eq_lintegral_cascadeSum_div (k : ℕ) (ms : Fin k → ℝ)
    (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)] {A G : (Fin k → T) → ℝ≥0∞}
    (hA : Measurable A) (hG : Measurable G) (hGpos : ∀ zs, 0 < G zs)
    (hfin : ∫⁻ zs, G zs ∂Measure.pi μs ≠ ∞) (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i)
    (hlt : ∀ i, ms i < 1) {r : ℕ} (hr : k ≤ r) :
    cascadeTiltSq k r ms μs G (fun zs => A zs / G zs)
      = ∫⁻ ω, cascadeSum k (fun zs => A zs ^ 2 / G zs) ω / cascadeSum k G ω
          ∂cascadeLaw k ms μs := by
  have hfun : (fun zs => (A zs / G zs) ^ 2) = fun zs => (A zs ^ 2 / G zs) / G zs := by
    funext zs
    simp only [div_eq_mul_inv, mul_pow]
    ring
  rw [cascadeTiltSq_of_le k r hr ms μs G (fun zs => A zs / G zs),
    lintegral_cascadeSum_div_cascadeSum k ms μs (A := fun zs => A zs ^ 2 / G zs) (G := G)
      ((hA.pow_const 2).div hG) hG hGpos hfin hsm hpos hlt, hfun]

end ProbabilityTheory
