/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.PointProcess.CascadeGibbs

/-!
# Talagrand's second-order identities (14.31)–(14.33)

Talagrand, *Mean Field Models for Spin Glasses*, Vol. II, §14.3. For a cascade with weights
`u*_α`, a positive `G = exp F` and a numerator `A`, write `⟨U⟩` for the Gibbs average of
`U = A / G`. Talagrand's (14.32) reads

`𝔼 ⟨U⟩² = ∑_{1 ≤ p ≤ k+1} (m_p - m_{p-1}) 𝔼(W₁ ⋯ W_{p-1} (𝔼_p W_p ⋯ W_k U)²)`,

and its refinement (14.33), obtained by attaching a random sign to the level-`r` prefix, is

`𝔼 ⟨1_{α|r = γ|r} U(α) U(γ)⟩ = ∑_{r < p ≤ k+1} (m_p - m_{p-1}) 𝔼(W₁ ⋯ W_{p-1}
  (𝔼_p W_p ⋯ W_k U)²)`.

Both are the case `a = 0` of a single statement with a free exponent
(`lintegral_cascadeSq_mul_rpow_num`),

`𝔼 Q_r(A) S_G^{a-2} = (∑_{r ≤ j ≤ k} (m_{j+1} - m_j)/(1-a) · 𝔼(W₁ ⋯ W_j (𝔼_{j+1} W_{j+1} ⋯ W_k U)²))
  · 𝔼 S_G^a`,

where `Q_r(A) = ∑_{α|r = γ|r} u*_α u*_γ A(z_α) A(z_γ)` is `cascadeSq` with numerator `A`, and
`m_0` is replaced by `a` (`mExt'`). The exponent has to be free because at the higher levels of
the cascade the sub-partition functions enter with the power `m_p`; this is the same phenomenon
as in `lintegral_cascadeSum_mul_rpow` and `lintegral_cascadeSq_mul_rpow`, of which this is the
common generalization (`A = G` gives the latter).

The proof is induction on the number of levels from the **one-level second-order identity**
`lintegral_pdSum_sq_mul_rpow_pdSum`: at `r = 0` the top level of the cascade contributes both an
off-diagonal term, which by `lintegral_offDiag_pdProcess` is the square of a first-order quantity
and produces the term `j = 0`, and a diagonal term, which reproduces the identity one level down;
at `r + 1` only the diagonal survives. Talagrand instead differentiates (14.26) in `t`; this
route stays inside the `ℝ≥0∞` calculus and needs no differentiation under the integral sign.

## Main statements

- `ProbabilityTheory.lintegral_cascadeSq_mul_rpow_num`: the identity with a free exponent.
- `ProbabilityTheory.lintegral_cascadeSq_num_mul_inv_sq`: **(14.33)**.
- `ProbabilityTheory.lintegral_cascadeSum_div_sq`: **(14.32)**.
-/

open MeasureTheory Set Filter Function
open scoped ENNReal Topology BigOperators

namespace ProbabilityTheory

open ENNReal

universe u

variable {T : Type u} [MeasurableSpace T] [Nonempty T]

/-- Shifting the summation index of a sum over `Finset.Ico`. -/
private lemma sum_Ico_shift (n r : ℕ) (F : ℕ → ℝ≥0∞) :
    ∑ j ∈ Finset.Ico r (n + 1), F (j + 1) = ∑ j ∈ Finset.Ico (r + 1) (n + 2), F j := by
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range,
    show n + 2 - (r + 1) = n + 1 - r by omega]
  exact Finset.sum_congr rfl fun i _ => by rw [show r + i + 1 = r + 1 + i by omega]

/-- The algebraic recombination of the two terms produced by the one-level second-order
identity. -/
private lemma combine_off_diag (Koff Ksq T S κ Ma c d : ℝ≥0∞) (h1 : Koff * κ ^ 2 = c * Ma)
    (h2 : Ksq * κ = d * Ma) :
    Koff * (T * κ) ^ 2 + Ksq * (S * κ) = (c * T ^ 2 + S * d) * Ma := by
  calc Koff * (T * κ) ^ 2 + Ksq * (S * κ)
      = T ^ 2 * (Koff * κ ^ 2) + S * (Ksq * κ) := by ring
    _ = T ^ 2 * (c * Ma) + S * (d * Ma) := by rw [h1, h2]
    _ = (c * T ^ 2 + S * d) * Ma := by ring

/-- **Talagrand's second-order identity with a free exponent**, the common generalization of
(14.31), (14.32), (14.33) and `lintegral_cascadeSq_mul_rpow`: for `0 ≤ a < 1` with `a < m_i` for
all `i`,

`𝔼 Q_r(A) S_G^{a-2}
  = (∑_{r ≤ j ≤ k} (m_{j+1} - m_j)/(1-a) · 𝔼(W₁ ⋯ W_j (𝔼_{j+1} W_{j+1} ⋯ W_k (A/G))²)) · 𝔼 S_G^a`,

`m_0` being replaced by `a`. For `A = G` with `G` finite every tilted square is `1`
(`cascadeTiltSq_one`) and the sum telescopes to `(1 - m_r)/(1 - a)`, which is
`lintegral_cascadeSq_mul_rpow`. -/
theorem lintegral_cascadeSq_mul_rpow_num (k : ℕ) :
    ∀ (ms : Fin k → ℝ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
      {A G : (Fin k → T) → ℝ≥0∞}, Measurable A → Measurable G → (∀ zs, 0 < G zs) →
      ∫⁻ zs, G zs ∂Measure.pi μs ≠ ∞ → StrictMono ms → (∀ i, ms i < 1) →
      ∀ {a : ℝ}, 0 ≤ a → a < 1 → (∀ i, a < ms i) → ∀ r : ℕ,
      ∫⁻ ω, cascadeSq k r A ω * cascadeSum k G ω ^ (a - 2) ∂cascadeLaw k ms μs
        = (∑ j ∈ Finset.Ico r (k + 1),
            ENNReal.ofReal ((mExt' ms a (j + 1) - mExt' ms a j) / (1 - a))
              * cascadeTiltSq k j ms μs G (fun zs => A zs / G zs))
          * ∫⁻ ω, cascadeSum k G ω ^ a ∂cascadeLaw k ms μs := by
  induction k with
  | zero =>
    intro ms μs _ A G hA hG hGpos hfin _ _ a ha0 ha1 _ r
    have hG0 : G Fin.elim0 ≠ 0 := (hGpos _).ne'
    have hGtop : G Fin.elim0 ≠ ∞ := by
      rw [Measure.pi_of_empty, lintegral_dirac' _ hG] at hfin
      exact fun h => hfin (by rw [← h]; exact congrArg G (Subsingleton.elim _ _))
    have hf1 : Measurable fun ω : CascadeSpace T 0 =>
        cascadeSq 0 r A ω * cascadeSum 0 G ω ^ (a - 2) :=
      (measurable_cascadeSq 0 r hA).mul ((measurable_cascadeSum 0 hG).pow_const _)
    have hf2 : Measurable fun ω : CascadeSpace T 0 => cascadeSum 0 G ω ^ a :=
      (measurable_cascadeSum 0 hG).pow_const _
    rw [cascadeLaw_zero, lintegral_dirac' _ hf1, lintegral_dirac' _ hf2]
    rcases r with _ | r
    · rw [← Finset.range_eq_Ico, Finset.sum_range_one]
      have hc : ENNReal.ofReal ((mExt' ms a (0 + 1) - mExt' ms a 0) / (1 - a)) = 1 := by
        rw [mExt'_zero, mExt'_succ_eq, mExt_of_zero_lt (r := 0 + 1) (by omega),
          div_self (show (1 : ℝ) - a ≠ 0 by linarith), ENNReal.ofReal_one]
      simp only [hc, one_mul, cascadeSq_zero, cascadeSum_zero, cascadeTiltSq_zero,
        cascadeTilt_zero]
      rw [ENNReal.rpow_sub _ _ hG0 hGtop, ENNReal.rpow_two, div_eq_mul_inv, div_eq_mul_inv,
        mul_pow, ← ENNReal.inv_pow]
      ring
    · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, zero_mul,
        cascadeSq_zero_succ, zero_mul]
  | succ k ih =>
    intro ms μs _ A G hA hG hGpos hfin hsm hlt a ha0 ha1 ham r
    have hm : 0 < ms 0 := lt_of_le_of_lt ha0 (ham 0)
    have ham0 : a < ms 0 := ham 0
    have hm1 : ms 0 < 1 := hlt 0
    have h1m : (1 : ℝ) - ms 0 ≠ 0 := by linarith
    have h1a : (1 : ℝ) - a ≠ 0 := by linarith
    have hposAll : ∀ i, 0 < ms i := fun i => lt_of_le_of_lt ha0 (ham i)
    have hsm' : StrictMono (Fin.cons (ms 0) (Fin.tail ms) : Fin (k + 1) → ℝ) := by
      rw [Fin.cons_self_tail]
      exact hsm
    have hposTail : ∀ i, 0 < Fin.tail ms i := fun i => hposAll i.succ
    have hfinTail : ∀ᵐ z ∂μs 0,
        ∫⁻ zs, G (Fin.cons z zs) ∂Measure.pi (Fin.tail μs) ≠ ∞ :=
      ae_lintegral_pi_cons_ne_top k μs hG hfin
    have hconsA : Measurable (uncurry fun z : T => fun zs : Fin k → T => A (Fin.cons z zs)) :=
      hA.comp measurable_fin_cons
    have hconsG : Measurable (uncurry fun z : T => fun zs : Fin k → T => G (Fin.cons z zs)) :=
      hG.comp measurable_fin_cons
    set η := (μs 0).prod (cascadeLaw k (Fin.tail ms) (Fin.tail μs)) with hη
    set vG : T × CascadeSpace T k → ℝ≥0∞ :=
      fun p => cascadeSum k (fun zs => G (Fin.cons p.1 zs)) p.2 with hvG_def
    have hvG : Measurable vG :=
      measurable_cascadeSum_prod k (α := T) (G := fun z zs => G (Fin.cons z zs)) hconsG
    have hlaw := hasLaw_superCounting_cascadeLaw k ms μs
    have hsumG : ∀ ω, cascadeSum (k + 1) G ω = pdSum vG (superCounting ω) := fun ω => rfl
    have hVpos : ∀ᵐ p ∂η, 0 < vG p := by
      rw [hη, Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const hvG)]
      refine Filter.Eventually.of_forall fun z => ?_
      exact ae_cascadeSum_pos k (Fin.tail ms) (Fin.tail μs)
        (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
        (fun zs => hGpos _) hposTail
    have hRm : Measurable fun z => cascadeRec k (Fin.tail ms) (Fin.tail μs)
        (fun zs => G (Fin.cons z zs)) := measurable_cascadeRec_cons k _ _ hG
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
    have hRtop : R ≠ ∞ := cascadeRec_ne_top (k + 1) ms μs hG hposAll (fun i => (hlt i).le) hfin
    have hRm0 : R ^ ms 0 ≠ 0 := by
      simpa using (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 hR0) hm.le).ne'
    have hRmtop : R ^ ms 0 ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hm.le hRtop
    have hκ : ∫⁻ p, vG p ^ ms 0 ∂η = cascadeConst k (ms 0) (Fin.tail ms) * R ^ ms 0 := by
      rw [hη, lintegral_prod (fun p : T × CascadeSpace T k => vG p ^ ms 0)
        (hvG.pow_const _).aemeasurable]
      simp_rw [hQ]
      rw [lintegral_mul_const _ (hRm.pow_const _), hRdef, cascadeRec_succ, ← ENNReal.rpow_mul,
        one_div_mul_cancel hm.ne', ENNReal.rpow_one, mul_comm]
    have hκtop : ∫⁻ p, vG p ^ ms 0 ∂η ≠ ∞ := by
      rw [hκ]
      exact ENNReal.mul_ne_top hCktop hRmtop
    have htransG : ∫⁻ ω, cascadeSum (k + 1) G ω ^ a ∂cascadeLaw (k + 1) ms μs
        = ∫⁻ N, pdSum vG N ^ a ∂pdProcess (ms 0) η := by
      simp_rw [hsumG]
      exact hlaw.lintegral_comp ((measurable_pdSum hvG).pow_const _).aemeasurable
    have hoff := ofReal_pdOffConst_mul_lintegral hm hm1 η hvG hVpos hκtop ha0 ham0
    have hsqc := ofReal_pdSqConst_mul_lintegral hm hm1 η hvG hVpos hκtop ha0 ham0
    have hWmul : ∀ z, cascadeRec k (Fin.tail ms) (Fin.tail μs)
          (fun zs => G (Fin.cons z zs)) ^ ms 0
        = cascadeW k ms μs G z * R ^ ms 0 := by
      intro z
      rw [cascadeW, ENNReal.div_rpow_of_nonneg _ _ hm.le, ENNReal.div_mul_cancel hRm0 hRmtop]
    have hTm : ∀ j : ℕ, Measurable fun z => cascadeTiltSq k j (Fin.tail ms) (Fin.tail μs)
        (fun zs => G (Fin.cons z zs)) (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs)) :=
      fun j => measurable_cascadeTiltSq_prod k j (Fin.tail ms) (Fin.tail μs)
        (Gs := fun z zs => G (Fin.cons z zs))
        (As := fun z zs => A (Fin.cons z zs) / G (Fin.cons z zs)) hconsG (hconsA.div hconsG)
    have hWT : ∀ j : ℕ, Measurable fun z : T => cascadeW k ms μs G z
        * cascadeTiltSq k j (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs))
            (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs)) :=
      fun j => (measurable_cascadeW k ms μs hG).mul (hTm j)
    -- the coefficients of the sub-cascade combine with `(1 - m₁)/(1 - a)` into the right ones
    have hcoef : ∀ j : ℕ, ENNReal.ofReal ((1 - ms 0) / (1 - a))
          * ENNReal.ofReal ((mExt' (Fin.tail ms) (ms 0) (j + 1)
              - mExt' (Fin.tail ms) (ms 0) j) / (1 - ms 0))
        = ENNReal.ofReal ((mExt' ms a (j + 1 + 1) - mExt' ms a (j + 1)) / (1 - a)) := by
      intro j
      rw [← ENNReal.ofReal_mul (div_nonneg (by linarith) (by linarith)),
        mExt'_succ ms a (j + 1), mExt'_succ ms a j]
      congr 1
      field_simp
    -- the diagonal term, by the induction hypothesis on the sub-cascades
    have hdiag : ∀ r' : ℕ,
        ∫⁻ p, cascadeSq k r' (fun zs => A (Fin.cons p.1 zs)) p.2 * vG p ^ (ms 0 - 2) ∂η
          = (∑ j ∈ Finset.Ico r' (k + 1),
              ENNReal.ofReal ((mExt' (Fin.tail ms) (ms 0) (j + 1)
                  - mExt' (Fin.tail ms) (ms 0) j) / (1 - ms 0))
                * cascadeTiltSq (k + 1) (j + 1) ms μs G (fun zs => A zs / G zs))
            * ∫⁻ p, vG p ^ ms 0 ∂η := by
      intro r'
      have hB : Measurable fun p : T × CascadeSpace T k =>
          cascadeSq k r' (fun zs => A (Fin.cons p.1 zs)) p.2 :=
        measurable_cascadeSq_prod k r' (α := T) (G := fun z zs => A (Fin.cons z zs)) hconsA
      rw [hη, lintegral_prod (fun p : T × CascadeSpace T k =>
        cascadeSq k r' (fun zs => A (Fin.cons p.1 zs)) p.2 * vG p ^ (ms 0 - 2))
        (hB.mul (hvG.pow_const _)).aemeasurable]
      have hfib : ∀ᵐ z ∂μs 0, ∫⁻ ω', cascadeSq k r' (fun zs => A (Fin.cons z zs)) ω'
            * vG (z, ω') ^ (ms 0 - 2) ∂cascadeLaw k (Fin.tail ms) (Fin.tail μs)
          = (∑ j ∈ Finset.Ico r' (k + 1),
              ENNReal.ofReal ((mExt' (Fin.tail ms) (ms 0) (j + 1)
                  - mExt' (Fin.tail ms) (ms 0) j) / (1 - ms 0))
                * cascadeTiltSq k j (Fin.tail ms) (Fin.tail μs)
                    (fun zs => G (Fin.cons z zs))
                    (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs)))
            * (cascadeRec k (Fin.tail ms) (Fin.tail μs) (fun zs => G (Fin.cons z zs)) ^ ms 0
              * cascadeConst k (ms 0) (Fin.tail ms)) := by
        filter_upwards [hfinTail] with z hz
        have h := ih (Fin.tail ms) (Fin.tail μs) (A := fun zs => A (Fin.cons z zs))
          (G := fun zs => G (Fin.cons z zs))
          (hA.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
          (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
          (fun zs => hGpos _) hz (strictMono_of_strictMono_cons hsm') (fun i => hlt i.succ)
          hm.le hm1 (fun i => hsm (Fin.succ_pos i)) r'
        rw [hQ' z] at h
        exact h
      rw [lintegral_congr_ae hfib]
      simp_rw [hWmul]
      have hpt : ∀ z : T, (∑ j ∈ Finset.Ico r' (k + 1),
              ENNReal.ofReal ((mExt' (Fin.tail ms) (ms 0) (j + 1)
                  - mExt' (Fin.tail ms) (ms 0) j) / (1 - ms 0))
                * cascadeTiltSq k j (Fin.tail ms) (Fin.tail μs)
                    (fun zs => G (Fin.cons z zs))
                    (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs)))
            * (cascadeW k ms μs G z * R ^ ms 0 * cascadeConst k (ms 0) (Fin.tail ms))
          = ∑ j ∈ Finset.Ico r' (k + 1), (R ^ ms 0 * cascadeConst k (ms 0) (Fin.tail ms)
              * ENNReal.ofReal ((mExt' (Fin.tail ms) (ms 0) (j + 1)
                  - mExt' (Fin.tail ms) (ms 0) j) / (1 - ms 0)))
              * (cascadeW k ms μs G z * cascadeTiltSq k j (Fin.tail ms) (Fin.tail μs)
                  (fun zs => G (Fin.cons z zs))
                  (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs))) := by
        intro z
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      simp_rw [hpt]
      rw [lintegral_finsetSum (μ := μs 0) (Finset.Ico r' (k + 1))
        (f := fun (j : ℕ) (z : T) => (R ^ ms 0 * cascadeConst k (ms 0) (Fin.tail ms)
            * ENNReal.ofReal ((mExt' (Fin.tail ms) (ms 0) (j + 1)
                - mExt' (Fin.tail ms) (ms 0) j) / (1 - ms 0)))
            * (cascadeW k ms μs G z * cascadeTiltSq k j (Fin.tail ms) (Fin.tail μs)
                (fun zs => G (Fin.cons z zs))
                (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs))))
        (fun j _ => measurable_const.mul (hWT j))]
      have hterm : ∀ j : ℕ, ∫⁻ z, (R ^ ms 0 * cascadeConst k (ms 0) (Fin.tail ms)
              * ENNReal.ofReal ((mExt' (Fin.tail ms) (ms 0) (j + 1)
                  - mExt' (Fin.tail ms) (ms 0) j) / (1 - ms 0)))
              * (cascadeW k ms μs G z * cascadeTiltSq k j (Fin.tail ms) (Fin.tail μs)
                  (fun zs => G (Fin.cons z zs))
                  (fun zs => A (Fin.cons z zs) / G (Fin.cons z zs))) ∂μs 0
          = (R ^ ms 0 * cascadeConst k (ms 0) (Fin.tail ms)
              * ENNReal.ofReal ((mExt' (Fin.tail ms) (ms 0) (j + 1)
                  - mExt' (Fin.tail ms) (ms 0) j) / (1 - ms 0)))
            * cascadeTiltSq (k + 1) (j + 1) ms μs G (fun zs => A zs / G zs) := by
        intro j
        rw [lintegral_const_mul _ (hWT j), cascadeTiltSq_succ]
      simp_rw [hterm]
      rw [hκ, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rcases r with _ | r
    · -- `Q₀ = S²`: the top level contributes both an off-diagonal and a diagonal term
      set vA : T × CascadeSpace T k → ℝ≥0∞ :=
        fun p => cascadeSum k (fun zs => A (Fin.cons p.1 zs)) p.2 with hvA_def
      have hvA : Measurable vA :=
        measurable_cascadeSum_prod k (α := T) (G := fun z zs => A (Fin.cons z zs)) hconsA
      have hsumA : ∀ ω, cascadeSum (k + 1) A ω = pdSum vA (superCounting ω) := fun ω => rfl
      have htrans : ∫⁻ ω, cascadeSq (k + 1) 0 A ω * cascadeSum (k + 1) G ω ^ (a - 2)
            ∂cascadeLaw (k + 1) ms μs
          = ∫⁻ N, pdSum vA N ^ 2 * pdSum vG N ^ (a - 2) ∂pdProcess (ms 0) η := by
        have hpt : ∀ ω : CascadeSpace T (k + 1),
            cascadeSq (k + 1) 0 A ω * cascadeSum (k + 1) G ω ^ (a - 2)
              = pdSum vA (superCounting ω) ^ 2 * pdSum vG (superCounting ω) ^ (a - 2) := by
          intro ω
          rw [cascadeSq_zero, hsumA, hsumG, pow_two]
        simp_rw [hpt]
        exact hlaw.lintegral_comp (((measurable_pdSum hvA).pow_const 2).mul
          ((measurable_pdSum hvG).pow_const _)).aemeasurable
      have hnum : ∫⁻ p, vA p * vG p ^ (ms 0 - 1) ∂η
          = cascadeTilt (k + 1) ms μs G (fun zs => A zs / G zs) * ∫⁻ p, vG p ^ ms 0 ∂η :=
        lintegral_prod_cascadeSum_mul_rpow k ms μs hA hG hGpos hfin hsm hlt hposAll
      have hsq : ∫⁻ p, vA p ^ 2 * vG p ^ (ms 0 - 2) ∂η
          = (∑ j ∈ Finset.Ico 0 (k + 1),
              ENNReal.ofReal ((mExt' (Fin.tail ms) (ms 0) (j + 1)
                  - mExt' (Fin.tail ms) (ms 0) j) / (1 - ms 0))
                * cascadeTiltSq (k + 1) (j + 1) ms μs G (fun zs => A zs / G zs))
            * ∫⁻ p, vG p ^ ms 0 ∂η := by
        rw [← hdiag 0]
        exact lintegral_congr fun p => by rw [pow_two, cascadeSq_zero]
      rw [htrans, htransG,
        lintegral_pdSum_sq_mul_rpow_pdSum hm hm1 η hvA hvG hVpos hκtop ham0, hnum, hsq,
        combine_off_diag _ _ _ _ _ _ _ _ hoff hsqc]
      congr 1
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < k + 2), ← sum_Ico_shift k 0,
        Finset.sum_mul]
      have hbot : ENNReal.ofReal ((mExt' ms a (0 + 1) - mExt' ms a 0) / (1 - a))
            * cascadeTiltSq (k + 1) 0 ms μs G (fun zs => A zs / G zs)
          = ENNReal.ofReal ((ms 0 - a) / (1 - a))
            * cascadeTilt (k + 1) ms μs G (fun zs => A zs / G zs) ^ 2 := by
        rw [cascadeTiltSq_zero, mExt'_zero, zero_add, mExt'_succ_eq, mExt_one]
      rw [hbot]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by
        rw [mul_comm _ (ENNReal.ofReal ((1 - ms 0) / (1 - a))), ← mul_assoc, hcoef j]
    · -- `Q_{r+1} = ∑_j u_j² Q_r^{(j)}`: only the diagonal survives
      have hB : Measurable fun p : T × CascadeSpace T k =>
          cascadeSq k r (fun zs => A (Fin.cons p.1 zs)) p.2 :=
        measurable_cascadeSq_prod k r (α := T) (G := fun z zs => A (Fin.cons z zs)) hconsA
      have htrans : ∫⁻ ω, cascadeSq (k + 1) (r + 1) A ω * cascadeSum (k + 1) G ω ^ (a - 2)
            ∂cascadeLaw (k + 1) ms μs
          = ∫⁻ N, (∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1
              * cascadeSq k r (fun zs => A (Fin.cons p.2.1 zs)) p.2.2 ∂N)
              * pdSum vG N ^ (a - 2) ∂pdProcess (ms 0) η := by
        have hpt : ∀ ω : CascadeSpace T (k + 1),
            cascadeSq (k + 1) (r + 1) A ω * cascadeSum (k + 1) G ω ^ (a - 2)
              = (∫⁻ p, ENNReal.ofReal p.1 * ENNReal.ofReal p.1
                  * cascadeSq k r (fun zs => A (Fin.cons p.2.1 zs)) p.2.2 ∂superCounting ω)
                * pdSum vG (superCounting ω) ^ (a - 2) := fun ω => rfl
        simp_rw [hpt]
        have hUW : Measurable fun p : ℝ × (T × CascadeSpace T k) =>
            ENNReal.ofReal p.1 * ENNReal.ofReal p.1
              * cascadeSq k r (fun zs => A (Fin.cons p.2.1 zs)) p.2.2 :=
          ((ENNReal.measurable_ofReal.comp measurable_fst).mul
            (ENNReal.measurable_ofReal.comp measurable_fst)).mul (hB.comp measurable_snd)
        exact hlaw.lintegral_comp
          ((Measure.measurable_lintegral hUW).mul ((measurable_pdSum hvG).pow_const _)).aemeasurable
      rw [htrans, htransG,
        lintegral_pdSumSq_mul_rpow_pdSum hm hm1 η hB hvG hVpos hκtop ham0, hdiag r,
        ← mul_assoc, mul_comm (ENNReal.ofReal (pdSqConst (ms 0) a (stableConst (ms 0))
          (∫⁻ p, vG p ^ ms 0 ∂η).toReal)), mul_assoc, hsqc, ← mul_assoc, ← sum_Ico_shift k r]
      congr 1
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm _ (ENNReal.ofReal ((1 - ms 0) / (1 - a))), ← mul_assoc, hcoef j]

/-! ### The identities of §14.3 -/

/-- **Talagrand's (14.33)**: for the cascade Gibbs average and `0 ≤ r ≤ k + 1`,

`𝔼 ⟨1_{α|r = γ|r} U(α) U(γ)⟩
  = ∑_{r < p ≤ k+1} (m_p - m_{p-1}) 𝔼(W₁ ⋯ W_{p-1} (𝔼_p W_p ⋯ W_k U)²)`,

with `U = A / G` and the conventions `m_0 = 0`, `m_{k+1} = 1`. At `A = G` it is
`lintegral_cascadeSq_mul_inv_sq`, `𝔼 ⟨1_{α|r = γ|r}⟩ = 1 - m_r`. -/
theorem lintegral_cascadeSq_num_mul_inv_sq (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {A G : (Fin k → T) → ℝ≥0∞} (hA : Measurable A)
    (hG : Measurable G) (hGpos : ∀ zs, 0 < G zs) (hfin : ∫⁻ zs, G zs ∂Measure.pi μs ≠ ∞)
    (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1) (r : ℕ) :
    ∫⁻ ω, cascadeSq k r A ω * (cascadeSum k G ω)⁻¹ ^ 2 ∂cascadeLaw k ms μs
      = ∑ j ∈ Finset.Ico r (k + 1), ENNReal.ofReal (mExt ms (j + 1) - mExt ms j)
          * cascadeTiltSq k j ms μs G (fun zs => A zs / G zs) := by
  have h := lintegral_cascadeSq_mul_rpow_num k ms μs hA hG hGpos hfin hsm hlt
    (a := 0) le_rfl one_pos hpos r
  simp only [ENNReal.rpow_zero, lintegral_const, measure_univ, mul_one, sub_zero, div_one,
    mExt'_zero_exp] at h
  rw [← h]
  refine lintegral_congr fun ω => ?_
  rw [zero_sub, ENNReal.rpow_neg, ENNReal.rpow_two, ENNReal.inv_pow]

/-- **Talagrand's (14.32)**: the disorder average of the square of the cascade Gibbs average,

`𝔼 ⟨U⟩² = ∑_{1 ≤ p ≤ k+1} (m_p - m_{p-1}) 𝔼(W₁ ⋯ W_{p-1} (𝔼_p W_p ⋯ W_k U)²)`,

with `U = A / G`. -/
theorem lintegral_cascadeSum_div_sq (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {A G : (Fin k → T) → ℝ≥0∞} (hA : Measurable A)
    (hG : Measurable G) (hGpos : ∀ zs, 0 < G zs) (hfin : ∫⁻ zs, G zs ∂Measure.pi μs ≠ ∞)
    (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1) :
    ∫⁻ ω, (cascadeSum k A ω / cascadeSum k G ω) ^ 2 ∂cascadeLaw k ms μs
      = ∑ j ∈ Finset.range (k + 1), ENNReal.ofReal (mExt ms (j + 1) - mExt ms j)
          * cascadeTiltSq k j ms μs G (fun zs => A zs / G zs) := by
  have h := lintegral_cascadeSq_num_mul_inv_sq k ms μs hA hG hGpos hfin hsm hpos hlt 0
  rw [← Finset.range_eq_Ico] at h
  rw [← h]
  refine lintegral_congr fun ω => ?_
  rw [cascadeSq_zero, div_eq_mul_inv, mul_pow, ← pow_two]

/-- **Proposition 14.3.2** (Talagrand Vol. II, (14.37)): for `1 ≤ r ≤ k + 1`,

`𝔼 ⟨1_{(α,γ) = r} U(α) U(γ)⟩ = (m_r - m_{r-1}) 𝔼(W₁ ⋯ W_{r-1} (𝔼_r W_r ⋯ W_k U)²)`,

where `1_{(α,γ)=r} = 1_{α|(r-1) = γ|(r-1)} - 1_{α|r = γ|r}`. Stated additively, as subtraction in
`ℝ≥0∞` is truncated: the level-`r` average plus the term is the level-`(r-1)` average. At `A = G`
it is `lintegral_cascadePairIndicator`, Proposition 14.3.3. -/
theorem lintegral_cascadeSq_num_succ_add (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {A G : (Fin k → T) → ℝ≥0∞} (hA : Measurable A)
    (hG : Measurable G) (hGpos : ∀ zs, 0 < G zs) (hfin : ∫⁻ zs, G zs ∂Measure.pi μs ≠ ∞)
    (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1) {j : ℕ} (hj : j ≤ k) :
    (∫⁻ ω, cascadeSq k (j + 1) A ω * (cascadeSum k G ω)⁻¹ ^ 2 ∂cascadeLaw k ms μs)
        + ENNReal.ofReal (mExt ms (j + 1) - mExt ms j)
          * cascadeTiltSq k j ms μs G (fun zs => A zs / G zs)
      = ∫⁻ ω, cascadeSq k j A ω * (cascadeSum k G ω)⁻¹ ^ 2 ∂cascadeLaw k ms μs := by
  rw [lintegral_cascadeSq_num_mul_inv_sq k ms μs hA hG hGpos hfin hsm hpos hlt j,
    lintegral_cascadeSq_num_mul_inv_sq k ms μs hA hG hGpos hfin hsm hpos hlt (j + 1),
    Finset.sum_eq_sum_Ico_succ_bot (by omega : j < k + 1)]
  ring


end ProbabilityTheory
