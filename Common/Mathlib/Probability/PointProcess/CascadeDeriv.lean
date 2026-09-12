/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.PointProcess.CascadeTiltMeasure
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The derivative of the Parisi recursion in a parameter

For a family `F_λ` of terminal functions with a bounded derivative in `λ`, the recursion
`F₁(λ) = parisiRec k ms μs (F_λ)` is differentiable in `λ`, with derivative the **tilted average
of the derivative**,

`d/dλ F₁(λ) = 𝔼(W₁ ⋯ W_k ∂_λ F_λ)`,

the average against `cascadeTiltMeasure` (`hasDerivAt_parisiRec`). This is Talagrand's
differentiation formula `Y'_p = 𝔼_p(W_p Y'_{p+1})` (Vol. II, (14.185), (14.215)), iterated over
the levels: the derivative of a log-partition function is a Gibbs average, level by level. The
proof is an induction on the levels with differentiation under the integral sign
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`); the only hypotheses are joint
measurability, the bound `|∂_λ F_λ| ≤ C`, and Talagrand's (14.4) at the point of
differentiation, which the bound propagates to a neighbourhood
(`lintegral_ofReal_exp_le_of_le`).
-/

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace ProbabilityTheory

open ENNReal

universe u

variable {T : Type u} [MeasurableSpace T]

/-! ### Two elementary bounds -/

/-- `F ≤ F₀ + c` pointwise gives `∫ e^F ≤ e^c ∫ e^{F₀}`: Talagrand's (14.4) propagates. -/
lemma lintegral_ofReal_exp_le_of_le {k : ℕ} (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {F F₀ : (Fin k → T) → ℝ} {c : ℝ}
    (h : ∀ zs, F zs ≤ F₀ zs + c) :
    ∫⁻ zs, ENNReal.ofReal (Real.exp (F zs)) ∂Measure.pi μs
      ≤ ENNReal.ofReal (Real.exp c) * ∫⁻ zs, ENNReal.ofReal (Real.exp (F₀ zs)) ∂Measure.pi μs := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun zs => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith [h zs]))

/-- The mean value inequality for a real function with a bounded derivative. -/
lemma abs_sub_le_mul_abs_sub_of_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    {C : ℝ} (hC : ∀ x, |f' x| ≤ C) (x y : ℝ) : |f y - f x| ≤ C * |y - x| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Set.univ) (f := f)
    (f' := f') (fun x _ => (hf x).hasDerivWithinAt)
    (fun x _ => by rw [Real.norm_eq_abs]; exact hC x) convex_univ (Set.mem_univ x)
    (Set.mem_univ y)
  simpa only [Real.norm_eq_abs] using h

/-! ### The derivative of the recursion -/

/-- **The derivative of the Parisi recursion in a parameter** (Talagrand's (14.185), (14.215),
iterated): for terminal functions `F_λ` with `|∂_λ F_λ| ≤ C`, jointly measurable, satisfying (14.4)
at `λ₀`, the recursion is differentiable at `λ₀` with derivative the tilted average
`𝔼(W₁ ⋯ W_k ∂_λ F_{λ₀})` against `cascadeTiltMeasure`. -/
theorem hasDerivAt_parisiRec [Nonempty T] : ∀ (k : ℕ) (ms : Fin k → ℝ) (μs : Fin k → Measure T)
    [∀ i, IsProbabilityMeasure (μs i)] {F F' : ℝ → (Fin k → T) → ℝ},
    Measurable (uncurry F) → Measurable (uncurry F') →
    (∀ l zs, HasDerivAt (fun l => F l zs) (F' l zs) l) → ∀ {C : ℝ}, (∀ l zs, |F' l zs| ≤ C) →
    (∀ i, 0 < ms i) → (∀ i, ms i ≤ 1) → ∀ {l₀ : ℝ},
    ∫⁻ zs, ENNReal.ofReal (Real.exp (F l₀ zs)) ∂Measure.pi μs ≠ ∞ →
    HasDerivAt (fun l => parisiRec k ms μs (F l))
      (∫ zs, F' l₀ zs ∂cascadeTiltMeasure k ms μs (fun zs => ENNReal.ofReal (Real.exp (F l₀ zs))))
      l₀ := by
  intro k
  induction k with
  | zero =>
    intro ms μs _ F F' _ _ hd C _ _ _ l₀ _
    have hG : Measurable fun zs : Fin 0 → T => ENNReal.ofReal (Real.exp (F l₀ zs)) :=
      Subsingleton.measurable
    have hfin : ∫⁻ zs, ENNReal.ofReal (Real.exp (F l₀ zs)) ∂Measure.pi μs ≠ ∞ := by
      rw [Measure.pi_of_empty, lintegral_dirac' _ hG]
      exact ENNReal.ofReal_ne_top
    rw [integral_cascadeTiltMeasure 0 ms μs hG (fun _ => ENNReal.ofReal_pos.2 (Real.exp_pos _))
      (fun i => i.elim0) (fun i => i.elim0) hfin, Measure.pi_of_empty,
      integral_dirac' _ _ Subsingleton.measurable.stronglyMeasurable]
    simp only [cascadeTiltDensity_zero, ENNReal.toReal_one, one_smul, parisiRec_zero]
    have := hd l₀ (fun a => isEmptyElim a)
    convert this using 2
    exact congrArg _ (Subsingleton.elim _ _)
  | succ k ih =>
    intro ms μs _ F F' hF hF' hd C hC hpos hle l₀ hfin
    have hm : 0 < ms 0 := hpos 0
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC l₀ (fun _ => Classical.arbitrary T))
    have hpos' : ∀ i : Fin k, 0 < Fin.tail ms i := fun i => hpos i.succ
    have hle' : ∀ i : Fin k, Fin.tail ms i ≤ 1 := fun i => hle i.succ
    -- the branch functions
    set G : ℝ → (Fin (k + 1) → T) → ℝ≥0∞ := fun l zs => ENNReal.ofReal (Real.exp (F l zs))
      with hGdef
    set G₁ : ℝ → T → (Fin k → T) → ℝ≥0∞ :=
      fun l z ys => ENNReal.ofReal (Real.exp (F l (Fin.cons z ys))) with hG₁def
    set R : ℝ → T → ℝ :=
      fun l z => parisiRec k (Fin.tail ms) (Fin.tail μs) (fun ys => F l (Fin.cons z ys)) with hRdef
    set D : ℝ → T → ℝ := fun l z => ∫ ys, F' l (Fin.cons z ys)
      ∂cascadeTiltMeasure k (Fin.tail ms) (Fin.tail μs) (G₁ l z) with hDdef
    -- measurability
    have hFl : ∀ l, Measurable (F l) := fun l =>
      hF.comp (measurable_const.prodMk measurable_id)
    have hF'l : ∀ l, Measurable (F' l) := fun l =>
      hF'.comp (measurable_const.prodMk measurable_id)
    have hGm : ∀ l, Measurable (G l) := fun l =>
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hFl l))
    have hGpos : ∀ l zs, 0 < G l zs := fun l zs => ENNReal.ofReal_pos.2 (Real.exp_pos _)
    have hcons : ∀ z : T, Measurable fun ys : Fin k → T => (Fin.cons z ys : Fin (k + 1) → T) :=
      fun z => measurable_fin_cons.comp (measurable_const.prodMk measurable_id)
    have hG₁m : ∀ l z, Measurable (G₁ l z) := fun l z => (hGm l).comp (hcons z)
    have hG₁pos : ∀ l z ys, 0 < G₁ l z ys := fun l z ys => hGpos l _
    have hFcons : ∀ z : T, Measurable (uncurry fun (l : ℝ) (ys : Fin k → T) =>
        F l (Fin.cons z ys)) := fun z =>
      hF.comp (measurable_fst.prodMk (measurable_fin_cons.comp
        (measurable_const.prodMk measurable_snd)))
    have hF'cons : ∀ z : T, Measurable (uncurry fun (l : ℝ) (ys : Fin k → T) =>
        F' l (Fin.cons z ys)) := fun z =>
      hF'.comp (measurable_fst.prodMk (measurable_fin_cons.comp
        (measurable_const.prodMk measurable_snd)))
    have hG₁joint : ∀ l, Measurable (uncurry fun (z : T) (ys : Fin k → T) => G₁ l z ys) :=
      fun l => (hGm l).comp measurable_fin_cons
    have hRz : ∀ l, Measurable fun z => cascadeRec k (Fin.tail ms) (Fin.tail μs) (G₁ l z) :=
      fun l => measurable_cascadeRec_prod k (Fin.tail ms) (Fin.tail μs) (hG₁joint l)
    have hRm : ∀ l, Measurable (R l) := fun l => (hRz l).ennreal_toReal.log
    -- Lipschitz control of the terminal functions, and (14.4) everywhere
    have hLip : ∀ l zs, F l zs ≤ F l₀ zs + C * |l - l₀| := fun l zs => by
      have := abs_sub_le_mul_abs_sub_of_hasDerivAt (fun l => hd l zs) (fun l => hC l zs) l₀ l
      linarith [le_abs_self (F l zs - F l₀ zs)]
    have hfinl : ∀ l, ∫⁻ zs, G l zs ∂Measure.pi μs ≠ ∞ := fun l =>
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)
        (lintegral_ofReal_exp_le_of_le μs (hLip l))
    have hcasc : ∀ l, cascadeRec (k + 1) ms μs (G l) ≠ ∞ := fun l =>
      cascadeRec_ne_top (k + 1) ms μs (hGm l) hpos hle (hfinl l)
    have hbranch : ∀ᵐ z ∂μs 0, ∀ l, ∫⁻ ys, G₁ l z ys ∂Measure.pi (Fin.tail μs) ≠ ∞ := by
      filter_upwards [ae_lintegral_pi_cons_ne_top k μs (hGm l₀) hfin] with z hz
      intro l
      exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hz)
        (lintegral_ofReal_exp_le_of_le (Fin.tail μs) (F := fun ys => F l (Fin.cons z ys))
          (F₀ := fun ys => F l₀ (Fin.cons z ys)) fun ys => hLip l _)
    -- the induction hypothesis along almost every branch
    have hIH : ∀ᵐ z ∂μs 0, ∀ l, HasDerivAt (fun l => R l z) (D l z) l := by
      filter_upwards [hbranch] with z hz
      intro l
      exact ih (Fin.tail ms) (Fin.tail μs) (hFcons z) (hF'cons z) (fun l ys => hd l _)
        (fun l ys => hC l _) hpos' hle' (hz l)
    have hDbound : ∀ᵐ z ∂μs 0, ∀ l, |D l z| ≤ C := by
      filter_upwards [hbranch] with z hz
      intro l
      have := isProbabilityMeasure_cascadeTiltMeasure k (Fin.tail ms) (Fin.tail μs) (hG₁m l z)
        (hG₁pos l z) hpos' hle' (hz l)
      have h := norm_integral_le_of_norm_le_const
        (μ := cascadeTiltMeasure k (Fin.tail ms) (Fin.tail μs) (G₁ l z))
        (f := fun ys => F' l (Fin.cons z ys)) (C := C)
        (Filter.Eventually.of_forall fun ys => by rw [Real.norm_eq_abs]; exact hC l _)
      rwa [probReal_univ, mul_one, Real.norm_eq_abs] at h
    have hRlip : ∀ᵐ z ∂μs 0, ∀ l, |R l z - R l₀ z| ≤ C * |l - l₀| := by
      filter_upwards [hIH, hDbound] with z hz hz'
      intro l
      exact abs_sub_le_mul_abs_sub_of_hasDerivAt (f := fun l => R l z) (f' := fun l => D l z)
        hz hz' l₀ l
    -- the recursion in real form
    have hE : ∀ l, parisiRec (k + 1) ms μs (F l)
        = (1 / ms 0) * Real.log (∫ z, Real.exp (ms 0 * R l z) ∂μs 0) := fun l =>
      parisiRec_succ k ms μs (hFl l) hpos (hcasc l)
    -- integrability at `l₀`
    have hRzpos : ∀ z, 0 < cascadeRec k (Fin.tail ms) (Fin.tail μs) (G₁ l₀ z) := fun z =>
      cascadeRec_pos k _ _ (hG₁m l₀ z) (hG₁pos l₀ z) hpos'
    have hRzfin : ∀ᵐ z ∂μs 0, cascadeRec k (Fin.tail ms) (Fin.tail μs) (G₁ l₀ z) ≠ ∞ := by
      filter_upwards [hbranch] with z hz
      exact cascadeRec_ne_top k _ _ (hG₁m l₀ z) hpos' hle' (hz l₀)
    have hexpR : ∀ᵐ z ∂μs 0, Real.exp (ms 0 * R l₀ z)
        = (cascadeRec k (Fin.tail ms) (Fin.tail μs) (G₁ l₀ z) ^ ms 0).toReal := by
      filter_upwards [hRzfin] with z hz
      have hpos'' : 0 < (cascadeRec k (Fin.tail ms) (Fin.tail μs) (G₁ l₀ z)).toReal :=
        ENNReal.toReal_pos (hRzpos z).ne' hz
      rw [← ENNReal.toReal_rpow, Real.rpow_def_of_pos hpos'', mul_comm]
      rfl
    have hlint : ∫⁻ z, cascadeRec k (Fin.tail ms) (Fin.tail μs) (G₁ l₀ z) ^ ms 0 ∂μs 0 ≠ ∞ := by
      rw [← cascadeRec_rpow_eq_lintegral k ms μs (G l₀) hm]
      exact ENNReal.rpow_ne_top_of_nonneg hm.le (hcasc l₀)
    have hIint : Integrable (fun z => Real.exp (ms 0 * R l₀ z)) (μs 0) :=
      (integrable_toReal_of_lintegral_ne_top ((hRz l₀).pow_const _).aemeasurable hlint).congr
        (hexpR.mono fun z hz => hz.symm)
    have hIpos : 0 < ∫ z, Real.exp (ms 0 * R l₀ z) ∂μs 0 := integral_exp_pos hIint
    -- measurability of the tilted derivative in the first mark
    have hDmeas : AEStronglyMeasurable (fun z => D l₀ z) (μs 0) := by
      have hjoint : Measurable fun q : T × (Fin k → T) =>
          (cascadeTiltDensity k (Fin.tail ms) (Fin.tail μs) (G₁ l₀ q.1) q.2).toReal
            * F' l₀ (Fin.cons q.1 q.2) :=
        (measurable_cascadeTiltDensity_prod k (Fin.tail ms) (Fin.tail μs)
          (hG₁joint l₀)).ennreal_toReal.mul ((hF'l l₀).comp measurable_fin_cons)
      have hsm := hjoint.stronglyMeasurable.integral_prod_right'
        (ν := Measure.pi (Fin.tail μs))
      refine hsm.aestronglyMeasurable.congr ?_
      filter_upwards [hbranch] with z hz
      rw [hDdef]
      simp only
      rw [integral_cascadeTiltMeasure k (Fin.tail ms) (Fin.tail μs) (hG₁m l₀ z) (hG₁pos l₀ z)
        hpos' hle' (hz l₀)]
      simp only [smul_eq_mul]
    -- differentiation under the integral sign
    have hexpm : ∀ l, Measurable fun z => Real.exp (ms 0 * R l z) := fun l =>
      Real.measurable_exp.comp ((hRm l).const_mul _)
    have hderivI := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μs 0)
      (s := Metric.ball l₀ 1) (F := fun l z => Real.exp (ms 0 * R l z))
      (F' := fun l z => Real.exp (ms 0 * R l z) * (ms 0 * D l z))
      (bound := fun z => ms 0 * C * Real.exp (ms 0 * C) * Real.exp (ms 0 * R l₀ z))
      (Metric.ball_mem_nhds _ one_pos)
      (Filter.Eventually.of_forall fun l => (hexpm l).aestronglyMeasurable) hIint
      (((hexpm l₀).aestronglyMeasurable).mul (hDmeas.const_mul _)) ?_ (hIint.const_mul _) ?_
    · -- the derivative of the recursion
      have hlog := (hderivI.2.log hIpos.ne').const_mul (1 / ms 0)
      refine (hlog.congr_of_eventuallyEq (Filter.Eventually.of_forall hE)).congr_deriv ?_
      -- the derivative is the tilted average
      rw [integral_cascadeTiltMeasure_succ k ms μs (hGm l₀) (hGpos l₀) hpos hle hfin (hF'l l₀)
        (hC l₀)]
      set I : ℝ := ∫ z, Real.exp (ms 0 * R l₀ z) ∂μs 0 with hIdef
      have hI : I = (cascadeRec (k + 1) ms μs (G l₀)).toReal ^ ms 0 := by
        rw [hIdef, integral_congr_ae hexpR, integral_toReal ((hRz l₀).pow_const _).aemeasurable
          (ae_lt_top ((hRz l₀).pow_const _) hlint), ← cascadeRec_rpow_eq_lintegral k ms μs (G l₀)
          hm, ENNReal.toReal_rpow]
      have hW : ∀ᵐ z ∂μs 0, (cascadeW k ms μs (G l₀) z).toReal
          = Real.exp (ms 0 * R l₀ z) / I := by
        filter_upwards [hRzfin, hexpR] with z hz hz'
        rw [cascadeW, ← ENNReal.toReal_rpow, ENNReal.toReal_div,
          Real.div_rpow ENNReal.toReal_nonneg ENNReal.toReal_nonneg, hI, hz',
          ← ENNReal.toReal_rpow]
      have hsplit : (∫ z, Real.exp (ms 0 * R l₀ z) * (ms 0 * D l₀ z) ∂μs 0)
          = ms 0 * ∫ z, Real.exp (ms 0 * R l₀ z) * D l₀ z ∂μs 0 := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
      rw [hsplit]
      have hm0 : ms 0 ≠ 0 := hm.ne'
      have hcalc : (1 / ms 0) * (ms 0 * (∫ z, Real.exp (ms 0 * R l₀ z) * D l₀ z ∂μs 0) / I)
          = ∫ z, (Real.exp (ms 0 * R l₀ z) / I) * D l₀ z ∂μs 0 := by
        rw [show (1 / ms 0) * (ms 0 * (∫ z, Real.exp (ms 0 * R l₀ z) * D l₀ z ∂μs 0) / I)
            = (∫ z, Real.exp (ms 0 * R l₀ z) * D l₀ z ∂μs 0) / I by
          field_simp, ← integral_div]
        exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
      rw [hcalc]
      exact (integral_congr_ae (hW.mono fun z hz => by rw [hz])).symm
    · -- the bound on the derivative
      filter_upwards [hRlip, hDbound] with z hz hz'
      intro l hl
      have hl' : |l - l₀| < 1 := by simpa [Real.dist_eq] using hl
      have h1 : Real.exp (ms 0 * R l z) ≤ Real.exp (ms 0 * R l₀ z) * Real.exp (ms 0 * C) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have := hz l
        have h2 : R l z - R l₀ z ≤ C * |l - l₀| := (le_abs_self _).trans this
        have h3 : C * |l - l₀| ≤ C := by
          calc C * |l - l₀| ≤ C * 1 := mul_le_mul_of_nonneg_left hl'.le hC0
            _ = C := mul_one C
        nlinarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul, abs_of_pos hm]
      calc Real.exp (ms 0 * R l z) * (ms 0 * |D l z|)
          ≤ (Real.exp (ms 0 * R l₀ z) * Real.exp (ms 0 * C)) * (ms 0 * C) :=
            mul_le_mul h1 (mul_le_mul_of_nonneg_left (hz' l) hm.le)
              (mul_nonneg hm.le (abs_nonneg _)) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
        _ = ms 0 * C * Real.exp (ms 0 * C) * Real.exp (ms 0 * R l₀ z) := by ring
    · -- differentiability of the integrand
      filter_upwards [hIH] with z hz
      intro l _
      exact ((hz l).const_mul (ms 0)).exp

end ProbabilityTheory
