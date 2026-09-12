/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.LevelBoundLaw
import Common.Mathlib.Probability.PointProcess.CascadeJensenLower
import Common.Mathlib.Probability.PointProcess.CascadeExponent

/-!
# Integrability of the logarithm of a cascade sum, jointly in a parameter

For branch functions `G θ : (Fin k → T) → ℝ≥0∞` depending on a parameter `θ`, the quantity
`log (∑_α v_α G_θ(z_α))` — the integrand of Talagrand's Theorem 14.2.1 — is integrable jointly
in the cascade weights, the parameter and the marks as soon as `∫∫ G` and `∫∫ |log G|` are finite
(`integrable_log_cascadeSum_div_prod`). The two tails are controlled by `log x ≤ x` and by
**Jensen's inequality for the branch chosen according to the weights**,
`log ∑_α v_α G(z_α) ≥ ∑_α v_α log G(z_α)` (`tsum_mul_log_le_log_tsum_mul`, the tangent-line
form of the concavity of `log`), whose expectation is `∫ log G` by the branch-law identity
(`lintegral_cascadeSum_div_cascadeSum_one_prod`). Theorem 14.2.1 conditionally on `θ` then
evaluates the joint integral (`integral_log_cascadeSum_div_prod_eq`).
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

noncomputable section

/-! ### Jensen's inequality for weighted sums, in tangent-line form -/

/-- **Jensen's inequality for `log` and a countable convex combination**:
`∑ pᵢ log gᵢ ≤ log (∑ pᵢ gᵢ)`, from `log y ≤ log m + (y - m)/m`. -/
theorem tsum_mul_log_le_log_tsum_mul {ι : Type*} {p g : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hg : ∀ i, 0 < g i) (hps : Summable p) (hp1 : ∑' i, p i = 1)
    (hpg : Summable fun i => p i * g i) (hm : 0 < ∑' i, p i * g i)
    (hpl : Summable fun i => p i * Real.log (g i)) :
    ∑' i, p i * Real.log (g i) ≤ Real.log (∑' i, p i * g i) := by
  set m := ∑' i, p i * g i with hmdef
  have key : ∀ i, p i * Real.log (g i) ≤ (Real.log m - 1) * p i + (1 / m) * (p i * g i) := by
    intro i
    have h1 := Real.log_le_sub_one_of_pos (div_pos (hg i) hm)
    rw [Real.log_div (hg i).ne' hm.ne'] at h1
    have h2 : Real.log (g i) ≤ Real.log m - 1 + (1 / m) * g i := by
      have : g i / m = (1 / m) * g i := by ring
      linarith
    calc p i * Real.log (g i) ≤ p i * (Real.log m - 1 + (1 / m) * g i) :=
          mul_le_mul_of_nonneg_left h2 (hp i)
      _ = (Real.log m - 1) * p i + (1 / m) * (p i * g i) := by ring
  have hsum : Summable fun i => (Real.log m - 1) * p i + (1 / m) * (p i * g i) :=
    (hps.mul_left _).add (hpg.mul_left _)
  calc ∑' i, p i * Real.log (g i)
      ≤ ∑' i, ((Real.log m - 1) * p i + (1 / m) * (p i * g i)) := hpl.tsum_le_tsum key hsum
    _ = (Real.log m - 1) * ∑' i, p i + (1 / m) * ∑' i, p i * g i := by
        rw [(hps.mul_left _).tsum_add (hpg.mul_left _), tsum_mul_left, tsum_mul_left]
    _ = Real.log m := by
        rw [hp1, ← hmdef, mul_one, one_div, inv_mul_cancel₀ hm.ne']
        ring

/-! ### The two-sided bound on `log (S/W)` -/

variable {T : Type*} [MeasurableSpace T] (k : ℕ)

/-- `|log (S/W)| ≤ S/W + T/W` where `S = ∑_α u*_α G(z_α)` and `T = ∑_α u*_α |log G(z_α)|`:
the upper tail by `log x ≤ x`, the lower tail by Jensen's inequality. -/
theorem abs_log_cascadeSum_div_le (w : CascadeWeights k) (hW0 : weightSum k w ≠ 0)
    (hW : weightSum k w ≠ ∞) {G : (Fin k → T) → ℝ≥0∞} (hGm : Measurable G)
    (hGpos : ∀ x, 0 < G x) (hGfin : ∀ x, G x ≠ ∞) (z : CascadeMarks T k)
    (hS : cascadeSum k G (cascadeZip k (w, z)) ≠ ∞)
    (hT : cascadeSum k (fun x => ‖Real.log (G x).toReal‖ₑ) (cascadeZip k (w, z)) ≠ ∞) :
    |Real.log ((cascadeSum k G (cascadeZip k (w, z))).toReal / (weightSum k w).toReal)|
      ≤ (cascadeSum k G (cascadeZip k (w, z))).toReal / (weightSum k w).toReal
        + (cascadeSum k (fun x => ‖Real.log (G x).toReal‖ₑ) (cascadeZip k (w, z))).toReal
          / (weightSum k w).toReal := by
  have hw : ∀ α, branchWeight k w α ≠ ∞ :=
    fun α => ne_top_of_le_ne_top hW (branchWeight_le_weightSum k w α)
  have hTm : Measurable fun x => ‖Real.log (G x).toReal‖ₑ :=
    (Real.measurable_log.comp (ENNReal.measurable_toReal.comp hGm)).enorm
  set Wr : ℝ := (weightSum k w).toReal with hWr
  have hWpos : 0 < Wr := ENNReal.toReal_pos hW0 hW
  set S : ℝ := (cascadeSum k G (cascadeZip k (w, z))).toReal with hSdef
  set Tr : ℝ := (cascadeSum k (fun x => ‖Real.log (G x).toReal‖ₑ) (cascadeZip k (w, z))).toReal
    with hTdef
  -- the real forms of the sums
  have hSum : S = ∑' α, (branchWeight k w α).toReal * (G (branchMarks k z α)).toReal := by
    rw [hSdef, cascadeSum_cascadeZip k hGm,
      ENNReal.tsum_toReal_eq fun α => ENNReal.mul_ne_top (hw α) (hGfin _)]
    simp_rw [ENNReal.toReal_mul]
  have hTum : Tr = ∑' α, (branchWeight k w α).toReal
      * |Real.log (G (branchMarks k z α)).toReal| := by
    rw [hTdef, cascadeSum_cascadeZip k hTm,
      ENNReal.tsum_toReal_eq fun α => ENNReal.mul_ne_top (hw α) enorm_ne_top]
    simp_rw [ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs]
  have hWsum : ∑' α, (branchWeight k w α).toReal = Wr := by
    rw [hWr, weightSum, ENNReal.tsum_toReal_eq hw]
  -- summability
  have hsS : Summable fun α => (branchWeight k w α).toReal * (G (branchMarks k z α)).toReal := by
    have := ENNReal.summable_toReal (f := fun α => branchWeight k w α * G (branchMarks k z α))
      (by rw [← cascadeSum_cascadeZip k hGm]; exact hS)
    simpa only [ENNReal.toReal_mul] using this
  have hsT : Summable fun α => (branchWeight k w α).toReal
      * |Real.log (G (branchMarks k z α)).toReal| := by
    have := ENNReal.summable_toReal
      (f := fun α => branchWeight k w α * ‖Real.log (G (branchMarks k z α)).toReal‖ₑ)
      (by rw [← cascadeSum_cascadeZip k hTm]; exact hT)
    simpa only [ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs] using this
  have hsW : Summable fun α => (branchWeight k w α).toReal :=
    ENNReal.summable_toReal (by rw [← weightSum]; exact hW)
  -- the convex combination
  set p : (Fin k → ℕ × ℕ) → ℝ := fun α => (branchWeight k w α).toReal / Wr with hpdef
  set g : (Fin k → ℕ × ℕ) → ℝ := fun α => (G (branchMarks k z α)).toReal with hgdef
  have hp : ∀ α, 0 ≤ p α := fun α => div_nonneg ENNReal.toReal_nonneg hWpos.le
  have hgpos : ∀ α, 0 < g α := fun α => ENNReal.toReal_pos (hGpos _).ne' (hGfin _)
  have hps : Summable p := hsW.div_const _
  have hp1 : ∑' α, p α = 1 := by
    simp only [hpdef]
    rw [tsum_div_const, hWsum, div_self hWpos.ne']
  have hpg_eq : (fun α => p α * g α)
      = fun α => ((branchWeight k w α).toReal * (G (branchMarks k z α)).toReal) / Wr := by
    funext α
    simp only [hpdef, hgdef]
    ring
  have hpl_eq : (fun α => p α * |Real.log (g α)|)
      = fun α =>
          ((branchWeight k w α).toReal * |Real.log (G (branchMarks k z α)).toReal|) / Wr := by
    funext α
    simp only [hpdef, hgdef]
    ring
  have hpg : Summable fun α => p α * g α := by
    rw [hpg_eq]
    exact hsS.div_const _
  have hmeq : ∑' α, p α * g α = S / Wr := by
    rw [hpg_eq, tsum_div_const, hSum]
  have hpl_abs : Summable fun α => p α * |Real.log (g α)| := by
    rw [hpl_eq]
    exact hsT.div_const _
  have hTeq : Tr / Wr = ∑' α, p α * |Real.log (g α)| := by
    rw [hpl_eq, tsum_div_const, hTum]
  have hpl : Summable fun α => p α * Real.log (g α) :=
    Summable.of_norm_bounded hpl_abs fun α => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp α)]
  -- positivity of `S`
  obtain ⟨α₀, hα₀⟩ : ∃ α₀, branchWeight k w α₀ ≠ 0 := by
    by_contra hcon
    exact hW0 (ENNReal.tsum_eq_zero.2 fun α => by simpa using fun h => hcon ⟨α, h⟩)
  have hSpos : 0 < S := by
    refine ENNReal.toReal_pos ?_ hS
    intro h0
    have := le_cascadeSum_cascadeZip k w hGm z α₀
    rw [h0] at this
    exact absurd (le_antisymm this bot_le) (mul_ne_zero hα₀ (hGpos _).ne')
  have hmpos : 0 < ∑' α, p α * g α := by
    rw [hmeq]
    exact div_pos hSpos hWpos
  -- Jensen
  have hjensen := tsum_mul_log_le_log_tsum_mul hp hgpos hps hp1 hpg hmpos hpl
  rw [hmeq] at hjensen
  have hlow : -(Tr / Wr) ≤ ∑' α, p α * Real.log (g α) := by
    rw [hTeq, ← tsum_neg]
    refine hpl_abs.neg.tsum_le_tsum (fun α => ?_) hpl
    have h1 := neg_abs_le (Real.log (g α))
    have h2 := hp α
    nlinarith
  have hup : Real.log (S / Wr) ≤ S / Wr :=
    (Real.log_le_sub_one_of_pos (div_pos hSpos hWpos)).trans (by linarith)
  have hTnn : 0 ≤ Tr / Wr := div_nonneg ENNReal.toReal_nonneg hWpos.le
  have hSnn : 0 ≤ S / Wr := div_nonneg ENNReal.toReal_nonneg hWpos.le
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-! ### Joint integrability and the evaluation by Theorem 14.2.1 -/

universe u

variable {T' : Type u} [MeasurableSpace T'] [Nonempty T'] {Θ : Type u} [MeasurableSpace Θ]
  (Pθ : Measure Θ) [IsProbabilityMeasure Pθ] (ms : Fin k → ℝ) (μs : Fin k → Measure T')
  [∀ i, IsProbabilityMeasure (μs i)] (G : Θ → (Fin k → T') → ℝ≥0∞)

omit [Nonempty T'] in
/-- `∫⁻ S_θ/W` over the weights, the parameter and the marks is `∫⁻ ∫⁻ G`. -/
lemma lintegral_cascadeSum_div_prod_eq (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i)
    (hlt : ∀ i, ms i < 1) (hGm : Measurable (Function.uncurry G)) :
    ∫⁻ q : CascadeWeights k × (Θ × CascadeMarks T' k),
        cascadeSum k (G q.2.1) (cascadeZip k (q.1, q.2.2))
          / cascadeSum k (fun _ => 1) (cascadeZip k (q.1, q.2.2))
        ∂(cascadeWeightsLaw k ms).prod (Pθ.prod (cascadeMarksLaw k μs))
      = ∫⁻ θ, ∫⁻ x, G θ x ∂Measure.pi μs ∂Pθ := by
  have hGm' : ∀ θ, Measurable (G θ) := fun θ => by
    have := hGm.comp (measurable_const.prodMk measurable_id :
      Measurable fun x : Fin k → T' => (θ, x))
    exact this
  have hφ : Measurable fun p : Θ × (CascadeWeights k × CascadeMarks T' k) =>
      ((p.2.1, (p.1, p.2.2)) : CascadeWeights k × (Θ × CascadeMarks T' k)) :=
    (measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hmeas : Measurable fun q : CascadeWeights k × (Θ × CascadeMarks T' k) =>
      cascadeSum k (G q.2.1) (cascadeZip k (q.1, q.2.2))
        / cascadeSum k (fun _ => 1) (cascadeZip k (q.1, q.2.2)) := by
    have h1 := (measurable_cascadeSum_prod k (G := G) hGm).comp
      ((measurable_fst.comp measurable_snd).prodMk ((measurable_cascadeZip k).comp
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd))) :
        Measurable fun q : CascadeWeights k × (Θ × CascadeMarks T' k) =>
          (q.2.1, cascadeZip k (q.1, q.2.2)))
    have h2 := (measurable_cascadeSum k (measurable_const : Measurable fun _ : Fin k → T' =>
      (1 : ℝ≥0∞))).comp ((measurable_cascadeZip k).comp
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd)) :
        Measurable fun q : CascadeWeights k × (Θ × CascadeMarks T' k) =>
          cascadeZip k (q.1, q.2.2))
    exact h1.div h2
  have hm2 : Measurable fun a : Θ × (CascadeWeights k × CascadeMarks T' k) =>
      cascadeSum k (G a.1) (cascadeZip k (a.2.1, a.2.2))
        / cascadeSum k (fun _ => 1) (cascadeZip k (a.2.1, a.2.2)) := hmeas.comp hφ
  rw [Measure.prod_swap_left₃ (cascadeWeightsLaw k ms) Pθ (cascadeMarksLaw k μs),
    lintegral_map hmeas hφ]
  change ∫⁻ a : Θ × (CascadeWeights k × CascadeMarks T' k),
      cascadeSum k (G a.1) (cascadeZip k (a.2.1, a.2.2))
        / cascadeSum k (fun _ => 1) (cascadeZip k (a.2.1, a.2.2)) ∂_ = _
  rw [lintegral_prod _ hm2.aemeasurable]
  refine lintegral_congr fun θ => ?_
  exact lintegral_cascadeSum_div_cascadeSum_one_prod k μs (cascadeWeightsLaw k ms)
    (ae_weightSum_ne_zero_ne_top k ms hsm hpos hlt) (hGm' θ)

omit [Nonempty T'] in
lemma measurable_log_cascadeSum_div_prod (hGm : Measurable (Function.uncurry G)) :
    Measurable fun q : CascadeWeights k × (Θ × CascadeMarks T' k) =>
      Real.log ((cascadeSum k (G q.2.1) (cascadeZip k (q.1, q.2.2))).toReal
        / (cascadeSum k (fun _ => 1) (cascadeZip k (q.1, q.2.2))).toReal) := by
  have h1 := (measurable_cascadeSum_prod k (G := G) hGm).comp
    ((measurable_fst.comp measurable_snd).prodMk ((measurable_cascadeZip k).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))) :
      Measurable fun q : CascadeWeights k × (Θ × CascadeMarks T' k) =>
        (q.2.1, cascadeZip k (q.1, q.2.2)))
  have h2 := (measurable_cascadeSum k (measurable_const : Measurable fun _ : Fin k → T' =>
    (1 : ℝ≥0∞))).comp ((measurable_cascadeZip k).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)) :
      Measurable fun q : CascadeWeights k × (Θ × CascadeMarks T' k) =>
        cascadeZip k (q.1, q.2.2))
  exact Real.measurable_log.comp ((ENNReal.measurable_toReal.comp h1).div
    (ENNReal.measurable_toReal.comp h2))

omit [Nonempty T'] [IsProbabilityMeasure Pθ] in
/-- A double integral over the parameter and the marks along a branch, as an integral over the
parameter and the cascade marks. -/
lemma lintegral_lintegral_pi_eq (F : Θ → (Fin k → T') → ℝ≥0∞)
    (hF : Measurable (Function.uncurry F)) (α₀ : Fin k → ℕ × ℕ) :
    ∫⁻ θ, ∫⁻ x, F θ x ∂Measure.pi μs ∂Pθ
      = ∫⁻ q, F q.1 (branchMarks k q.2 α₀) ∂Pθ.prod (cascadeMarksLaw k μs) := by
  have hF' : ∀ θ, Measurable (F θ) := fun θ => by
    have := hF.comp (measurable_const.prodMk measurable_id :
      Measurable fun x : Fin k → T' => (θ, x))
    exact this
  have hm : Measurable fun q : Θ × CascadeMarks T' k => F q.1 (branchMarks k q.2 α₀) :=
    hF.comp (measurable_fst.prodMk ((measurable_branchMarks k α₀).comp measurable_snd))
  rw [lintegral_prod _ hm.aemeasurable]
  refine lintegral_congr fun θ => ?_
  rw [← cascadeMarksLaw_map_branchMarks k μs α₀,
    lintegral_map (hF' θ) (measurable_branchMarks k α₀)]

omit [Nonempty T'] in
/-- **Joint integrability of `log (∑_α v_α G_θ(z_α))`** in the weights, the parameter and the
marks, when `∫∫ G` and `∫∫ |log G|` are finite. -/
theorem integrable_log_cascadeSum_div_prod (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i)
    (hlt : ∀ i, ms i < 1) (hGm : Measurable (Function.uncurry G)) (hGpos : ∀ θ x, 0 < G θ x)
    (hGfin : ∀ θ x, G θ x ≠ ∞) (hint : ∫⁻ θ, ∫⁻ x, G θ x ∂Measure.pi μs ∂Pθ ≠ ∞)
    (hlog : ∫⁻ θ, ∫⁻ x, ‖Real.log (G θ x).toReal‖ₑ ∂Measure.pi μs ∂Pθ ≠ ∞) :
    Integrable (fun q : CascadeWeights k × (Θ × CascadeMarks T' k) =>
        Real.log ((cascadeSum k (G q.2.1) (cascadeZip k (q.1, q.2.2))).toReal
          / (cascadeSum k (fun _ => 1) (cascadeZip k (q.1, q.2.2))).toReal))
      ((cascadeWeightsLaw k ms).prod (Pθ.prod (cascadeMarksLaw k μs))) := by
  set P := (cascadeWeightsLaw k ms).prod (Pθ.prod (cascadeMarksLaw k μs)) with hP
  have hGm' : ∀ θ, Measurable (G θ) := fun θ => by
    have := hGm.comp (measurable_const.prodMk measurable_id :
      Measurable fun x : Fin k → T' => (θ, x))
    exact this
  set Glog : Θ → (Fin k → T') → ℝ≥0∞ := fun θ x => ‖Real.log (G θ x).toReal‖ₑ with hGlog
  have hGlogm : Measurable (Function.uncurry Glog) :=
    (Real.measurable_log.comp (ENNReal.measurable_toReal.comp hGm)).enorm
  -- the two dominating functions
  have hSfin := lintegral_cascadeSum_div_prod_eq k Pθ ms μs G hsm hpos hlt hGm
  have hTfin := lintegral_cascadeSum_div_prod_eq k Pθ ms μs Glog hsm hpos hlt hGlogm
  have hmeasS : Measurable fun q : CascadeWeights k × (Θ × CascadeMarks T' k) =>
      cascadeSum k (G q.2.1) (cascadeZip k (q.1, q.2.2))
        / cascadeSum k (fun _ => 1) (cascadeZip k (q.1, q.2.2)) := by
    have h1 := (measurable_cascadeSum_prod k (G := G) hGm).comp
      ((measurable_fst.comp measurable_snd).prodMk ((measurable_cascadeZip k).comp
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd))) :
        Measurable fun q : CascadeWeights k × (Θ × CascadeMarks T' k) =>
          (q.2.1, cascadeZip k (q.1, q.2.2)))
    have h2 := (measurable_cascadeSum k (measurable_const : Measurable fun _ : Fin k → T' =>
      (1 : ℝ≥0∞))).comp ((measurable_cascadeZip k).comp
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd)) :
        Measurable fun q : CascadeWeights k × (Θ × CascadeMarks T' k) =>
          cascadeZip k (q.1, q.2.2))
    exact h1.div h2
  have hmeasT : Measurable fun q : CascadeWeights k × (Θ × CascadeMarks T' k) =>
      cascadeSum k (Glog q.2.1) (cascadeZip k (q.1, q.2.2))
        / cascadeSum k (fun _ => 1) (cascadeZip k (q.1, q.2.2)) := by
    have h1 := (measurable_cascadeSum_prod k (G := Glog) hGlogm).comp
      ((measurable_fst.comp measurable_snd).prodMk ((measurable_cascadeZip k).comp
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd))) :
        Measurable fun q : CascadeWeights k × (Θ × CascadeMarks T' k) =>
          (q.2.1, cascadeZip k (q.1, q.2.2)))
    have h2 := (measurable_cascadeSum k (measurable_const : Measurable fun _ : Fin k → T' =>
      (1 : ℝ≥0∞))).comp ((measurable_cascadeZip k).comp
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd)) :
        Measurable fun q : CascadeWeights k × (Θ × CascadeMarks T' k) =>
          cascadeZip k (q.1, q.2.2))
    exact h1.div h2
  have hSint : Integrable (fun q : CascadeWeights k × (Θ × CascadeMarks T' k) =>
      (cascadeSum k (G q.2.1) (cascadeZip k (q.1, q.2.2))
        / cascadeSum k (fun _ => 1) (cascadeZip k (q.1, q.2.2))).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hmeasS.aemeasurable (by rw [hSfin]; exact hint)
  have hTint : Integrable (fun q : CascadeWeights k × (Θ × CascadeMarks T' k) =>
      (cascadeSum k (Glog q.2.1) (cascadeZip k (q.1, q.2.2))
        / cascadeSum k (fun _ => 1) (cascadeZip k (q.1, q.2.2))).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hmeasT.aemeasurable (by rw [hTfin]; exact hlog)
  have hSlt : ∀ᵐ q ∂P, cascadeSum k (G q.2.1) (cascadeZip k (q.1, q.2.2))
      / cascadeSum k (fun _ => 1) (cascadeZip k (q.1, q.2.2)) < ∞ :=
    ae_lt_top hmeasS (by rw [hSfin]; exact hint)
  have hTlt : ∀ᵐ q ∂P, cascadeSum k (Glog q.2.1) (cascadeZip k (q.1, q.2.2))
      / cascadeSum k (fun _ => 1) (cascadeZip k (q.1, q.2.2)) < ∞ :=
    ae_lt_top hmeasT (by rw [hTfin]; exact hlog)
  -- the weights are a.s. of positive finite mass
  have hmW : Measurable fun q : CascadeWeights k × (Θ × CascadeMarks T' k) => weightSum k q.1 :=
    (measurable_weightSum k).comp measurable_fst
  have haeW : ∀ᵐ q ∂P, weightSum k q.1 ≠ 0 ∧ weightSum k q.1 ≠ ∞ := by
    have hmeasW : MeasurableSet {q : CascadeWeights k × (Θ × CascadeMarks T' k) |
        weightSum k q.1 ≠ 0 ∧ weightSum k q.1 ≠ ∞} :=
      (hmW (measurableSet_singleton 0)).compl.inter (hmW (measurableSet_singleton ∞)).compl
    rw [Measure.ae_prod_iff_ae_ae hmeasW]
    filter_upwards [ae_weightSum_ne_zero_ne_top k ms hsm hpos hlt] with w hw
    exact Filter.Eventually.of_forall fun _ => hw
  -- measurability of the integrand
  have hmeasL := measurable_log_cascadeSum_div_prod k G hGm
  have hbound : Integrable (fun q : CascadeWeights k × (Θ × CascadeMarks T' k) =>
      (cascadeSum k (G q.2.1) (cascadeZip k (q.1, q.2.2))
        / cascadeSum k (fun _ => 1) (cascadeZip k (q.1, q.2.2))).toReal
      + (cascadeSum k (Glog q.2.1) (cascadeZip k (q.1, q.2.2))
        / cascadeSum k (fun _ => 1) (cascadeZip k (q.1, q.2.2))).toReal) P := hSint.add hTint
  refine hbound.mono' hmeasL.aestronglyMeasurable ?_
  filter_upwards [hSlt, hTlt, haeW] with q hqS hqT hqW
  rw [cascadeSum_one_cascadeZip] at hqS hqT
  have hS : cascadeSum k (G q.2.1) (cascadeZip k (q.1, q.2.2)) ≠ ∞ := by
    intro h
    rw [h, ENNReal.top_div_of_ne_top hqW.2] at hqS
    exact absurd hqS (lt_irrefl _)
  have hT : cascadeSum k (Glog q.2.1) (cascadeZip k (q.1, q.2.2)) ≠ ∞ := by
    intro h
    rw [h, ENNReal.top_div_of_ne_top hqW.2] at hqT
    exact absurd hqT (lt_irrefl _)
  rw [Real.norm_eq_abs, ENNReal.toReal_div, ENNReal.toReal_div, cascadeSum_one_cascadeZip]
  exact abs_log_cascadeSum_div_le k q.1 hqW.1 hqW.2 (hGm' q.2.1) (hGpos q.2.1) (hGfin q.2.1)
    q.2.2 hS hT

omit [Nonempty T'] in
/-- The joint integrability, in the order (parameter, weights, marks). -/
theorem integrable_log_cascadeSum_div_prod' (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i)
    (hlt : ∀ i, ms i < 1) (hGm : Measurable (Function.uncurry G)) (hGpos : ∀ θ x, 0 < G θ x)
    (hGfin : ∀ θ x, G θ x ≠ ∞) (hint : ∫⁻ θ, ∫⁻ x, G θ x ∂Measure.pi μs ∂Pθ ≠ ∞)
    (hlog : ∫⁻ θ, ∫⁻ x, ‖Real.log (G θ x).toReal‖ₑ ∂Measure.pi μs ∂Pθ ≠ ∞) :
    Integrable (fun p : Θ × (CascadeWeights k × CascadeMarks T' k) =>
        Real.log ((cascadeSum k (G p.1) (cascadeZip k (p.2.1, p.2.2))).toReal
          / (cascadeSum k (fun _ => 1) (cascadeZip k (p.2.1, p.2.2))).toReal))
      (Pθ.prod ((cascadeWeightsLaw k ms).prod (cascadeMarksLaw k μs))) := by
  have hI := integrable_log_cascadeSum_div_prod k Pθ ms μs G hsm hpos hlt hGm hGpos hGfin hint hlog
  have hφ : Measurable fun p : Θ × (CascadeWeights k × CascadeMarks T' k) =>
      ((p.2.1, (p.1, p.2.2)) : CascadeWeights k × (Θ × CascadeMarks T' k)) :=
    (measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hmeasL := measurable_log_cascadeSum_div_prod k G hGm
  have hswap := Measure.prod_swap_left₃ (cascadeWeightsLaw k ms) Pθ (cascadeMarksLaw k μs)
  exact (integrable_map_measure hmeasL.aestronglyMeasurable hφ.aemeasurable).1 (hswap ▸ hI)

/-- **Theorem 14.2.1 conditionally on the parameter**: at each `θ`,
`∫ log (∑_α v_α G_θ(z_α) / ∑_α v_α) d(w, z) = log cascadeRec(G_θ)`. -/
theorem integral_log_cascadeSum_div_eq_of (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i)
    (hlt : ∀ i, ms i < 1) (hGm : Measurable (Function.uncurry G)) (hGpos : ∀ θ x, 0 < G θ x)
    (hfin : ∀ θ, cascadeRec k ms μs (G θ) ≠ ∞) (θ : Θ) :
    (∫ y : CascadeWeights k × CascadeMarks T' k,
        Real.log ((cascadeSum k (G θ) (cascadeZip k (y.1, y.2))).toReal
          / (cascadeSum k (fun _ => 1) (cascadeZip k (y.1, y.2))).toReal)
        ∂(cascadeWeightsLaw k ms).prod (cascadeMarksLaw k μs))
      = Real.log (cascadeRec k ms μs (G θ)).toReal := by
  have hGm' : Measurable (G θ) := by
    have := hGm.comp (measurable_const.prodMk measurable_id :
      Measurable fun x : Fin k → T' => (θ, x))
    exact this
  have hmeasF : Measurable fun ω : CascadeSpace T' k =>
      Real.log ((cascadeSum k (G θ) ω).toReal / (cascadeSum k (fun _ => 1) ω).toReal) :=
    Real.measurable_log.comp ((ENNReal.measurable_toReal.comp
      (measurable_cascadeSum k hGm')).div
        (ENNReal.measurable_toReal.comp (measurable_cascadeSum k measurable_const)))
  rw [← integral_log_cascadeSum_div_eq k ms μs hGm' (hGpos θ) hsm hpos hlt (hfin θ),
    cascadeLaw_eq_map_cascadeZip,
    integral_map (measurable_cascadeZip k).aemeasurable hmeasF.aestronglyMeasurable]

/-- **The uniform bound**: for any exponents `0 < m_p ≤ 1`, at a.e. `θ`,
`|log cascadeRec(G_θ)| ≤ |∫ log G_θ| + ∫ G_θ` — the two-sided Jensen bound
`∫ log G_θ ≤ log cascadeRec(G_θ) ≤ log ∫ G_θ ≤ ∫ G_θ` (`integral_le_parisiRec`,
`parisiRec_le_log_integral_exp`), whose right-hand side does not depend on the exponents. -/
theorem ae_norm_log_cascadeRec_le (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (hGm : Measurable (Function.uncurry G)) (hGpos : ∀ θ x, 0 < G θ x)
    (hGfin : ∀ θ x, G θ x ≠ ∞) (hint : ∫⁻ θ, ∫⁻ x, G θ x ∂Measure.pi μs ∂Pθ ≠ ∞)
    (hlog : ∫⁻ θ, ∫⁻ x, ‖Real.log (G θ x).toReal‖ₑ ∂Measure.pi μs ∂Pθ ≠ ∞) :
    ∀ᵐ θ ∂Pθ, ‖Real.log (cascadeRec k ms μs (G θ)).toReal‖
      ≤ |∫ x, Real.log (G θ x).toReal ∂Measure.pi μs| + (∫⁻ x, G θ x ∂Measure.pi μs).toReal := by
  have hGθ : ∀ θ, Measurable (G θ) := fun θ =>
    hGm.comp (measurable_const.prodMk measurable_id)
  have hIm : Measurable fun θ => ∫⁻ x, G θ x ∂Measure.pi μs :=
    Measurable.lintegral_prod_right' hGm
  have hlogI : Integrable (fun p : Θ × (Fin k → T') => Real.log (G p.1 p.2).toReal)
      (Pθ.prod (Measure.pi μs)) := by
    refine ⟨hGm.ennreal_toReal.log.aestronglyMeasurable, ?_⟩
    have hm : AEMeasurable (fun p : Θ × (Fin k → T') => ‖Real.log (G p.1 p.2).toReal‖ₑ)
        (Pθ.prod (Measure.pi μs)) := hGm.ennreal_toReal.log.enorm.aemeasurable
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hm]
    exact hlog.lt_top
  filter_upwards [ae_lt_top hIm hint, hlogI.prod_right_ae] with θ hθ hθi
  -- `G θ = exp F` for `F = log G θ`
  set F : (Fin k → T') → ℝ := fun x => Real.log (G θ x).toReal with hF
  have hGeq : (fun x => ENNReal.ofReal (Real.exp (F x))) = G θ := by
    funext x
    rw [hF]
    simp only
    rw [Real.exp_log (ENNReal.toReal_pos (hGpos θ x).ne' (hGfin θ x)),
      ENNReal.ofReal_toReal (hGfin θ x)]
  have hFm : Measurable F := (hGθ θ).ennreal_toReal.log
  have hθi' : Integrable F (Measure.pi μs) := hθi
  have hfin' : ∫⁻ x, ENNReal.ofReal (Real.exp (F x)) ∂Measure.pi μs ≠ ∞ := by
    rw [hGeq]
    exact hθ.ne
  have hlow := integral_le_parisiRec k ms μs hFm hpos hle hfin' hθi'
  have hup := parisiRec_le_log_integral_exp k ms μs hFm hpos hle hfin'
  unfold parisiRec at hlow hup
  rw [hGeq] at hlow hup
  have hup' : Real.log (cascadeRec k ms μs (G θ)).toReal
      ≤ (∫⁻ x, G θ x ∂Measure.pi μs).toReal :=
    hup.trans (Real.log_le_self ENNReal.toReal_nonneg)
  rw [Real.norm_eq_abs]
  have h0 := ENNReal.toReal_nonneg (a := ∫⁻ x, G θ x ∂Measure.pi μs)
  have h1 := abs_nonneg (∫ x, F x ∂Measure.pi μs)
  refine abs_le.2 ⟨?_, ?_⟩
  · linarith [neg_abs_le (∫ x, F x ∂Measure.pi μs)]
  · linarith

/-- `|∫ log G_θ| + ∫ G_θ` is integrable in `θ` (Fubini). -/
theorem integrable_abs_integral_log_add_toReal_lintegral (hGm : Measurable (Function.uncurry G))
    (hint : ∫⁻ θ, ∫⁻ x, G θ x ∂Measure.pi μs ∂Pθ ≠ ∞)
    (hlog : ∫⁻ θ, ∫⁻ x, ‖Real.log (G θ x).toReal‖ₑ ∂Measure.pi μs ∂Pθ ≠ ∞) :
    Integrable (fun θ => |∫ x, Real.log (G θ x).toReal ∂Measure.pi μs|
      + (∫⁻ x, G θ x ∂Measure.pi μs).toReal) Pθ := by
  have hIm : Measurable fun θ => ∫⁻ x, G θ x ∂Measure.pi μs :=
    Measurable.lintegral_prod_right' hGm
  have hGI : Integrable (fun θ => (∫⁻ x, G θ x ∂Measure.pi μs).toReal) Pθ :=
    integrable_toReal_of_lintegral_ne_top hIm.aemeasurable hint
  have hlogI : Integrable (fun p : Θ × (Fin k → T') => Real.log (G p.1 p.2).toReal)
      (Pθ.prod (Measure.pi μs)) := by
    refine ⟨hGm.ennreal_toReal.log.aestronglyMeasurable, ?_⟩
    have hm : AEMeasurable (fun p : Θ × (Fin k → T') => ‖Real.log (G p.1 p.2).toReal‖ₑ)
        (Pθ.prod (Measure.pi μs)) := hGm.ennreal_toReal.log.enorm.aemeasurable
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hm]
    exact hlog.lt_top
  exact hlogI.integral_prod_left.abs.add hGI

/-- **`log cascadeRec(G_θ)` is integrable in the parameter** when `∫∫ G` and `∫∫ |log G|` are
finite, for any exponents `0 < m_p ≤ 1` (the uniform bound `ae_norm_log_cascadeRec_le`). -/
theorem integrable_log_cascadeRec (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (hGm : Measurable (Function.uncurry G)) (hGpos : ∀ θ x, 0 < G θ x)
    (hGfin : ∀ θ x, G θ x ≠ ∞) (hint : ∫⁻ θ, ∫⁻ x, G θ x ∂Measure.pi μs ∂Pθ ≠ ∞)
    (hlog : ∫⁻ θ, ∫⁻ x, ‖Real.log (G θ x).toReal‖ₑ ∂Measure.pi μs ∂Pθ ≠ ∞) :
    Integrable (fun θ => Real.log (cascadeRec k ms μs (G θ)).toReal) Pθ :=
  Integrable.mono' (integrable_abs_integral_log_add_toReal_lintegral k Pθ μs G hGm hint hlog)
    ((measurable_cascadeRec_prod k ms μs hGm).ennreal_toReal.log).aestronglyMeasurable
    (ae_norm_log_cascadeRec_le k Pθ ms μs G hpos hle hGm hGpos hGfin hint hlog)

/-- **`∫ log cascadeRec(G_θ) dθ` is continuous in the exponents on `(0, 1]^k`**: dominated
convergence with the uniform bound `ae_norm_log_cascadeRec_le` and `continuousOn_cascadeRec`. -/
theorem continuousOn_integral_log_cascadeRec (hGm : Measurable (Function.uncurry G))
    (hGpos : ∀ θ x, 0 < G θ x) (hGfin : ∀ θ x, G θ x ≠ ∞)
    (hint : ∫⁻ θ, ∫⁻ x, G θ x ∂Measure.pi μs ∂Pθ ≠ ∞)
    (hlog : ∫⁻ θ, ∫⁻ x, ‖Real.log (G θ x).toReal‖ₑ ∂Measure.pi μs ∂Pθ ≠ ∞) :
    ContinuousOn (fun ms => ∫ θ, Real.log (cascadeRec k ms μs (G θ)).toReal ∂Pθ)
      (Set.pi Set.univ fun _ => Set.Ioc (0 : ℝ) 1) := by
  intro ms₀ hmem
  have hms₀ := hmem
  simp only [Set.mem_univ_pi, Set.mem_Ioc] at hms₀
  have hGθ : ∀ θ, Measurable (G θ) := fun θ =>
    hGm.comp (measurable_const.prodMk measurable_id)
  have hIm : Measurable fun θ => ∫⁻ x, G θ x ∂Measure.pi μs :=
    Measurable.lintegral_prod_right' hGm
  refine tendsto_integral_filter_of_dominated_convergence
    (fun θ => |∫ x, Real.log (G θ x).toReal ∂Measure.pi μs|
      + (∫⁻ x, G θ x ∂Measure.pi μs).toReal)
    (Filter.Eventually.of_forall fun ms =>
      ((measurable_cascadeRec_prod k ms μs hGm).ennreal_toReal.log).aestronglyMeasurable)
    (eventually_nhdsWithin_of_forall fun ms hms => ?_)
    (integrable_abs_integral_log_add_toReal_lintegral k Pθ μs G hGm hint hlog) ?_
  · simp only [Set.mem_univ_pi, Set.mem_Ioc] at hms
    exact ae_norm_log_cascadeRec_le k Pθ ms μs G (fun i => (hms i).1) (fun i => (hms i).2) hGm
      hGpos hGfin hint hlog
  · filter_upwards [ae_lt_top hIm hint] with θ hθ
    have hc := continuousOn_cascadeRec k μs (hGθ θ) hθ.ne ms₀ hmem
    have hne : cascadeRec k ms₀ μs (G θ) ≠ ∞ := ne_top_of_le_ne_top hθ.ne
      (cascadeRec_le_lintegral_pi k ms₀ μs (hGθ θ) (fun i => (hms₀ i).1) (fun i => (hms₀ i).2))
    have hpos' : 0 < cascadeRec k ms₀ μs (G θ) :=
      cascadeRec_pos k ms₀ μs (hGθ θ) (hGpos θ) (fun i => (hms₀ i).1)
    have h1 : Tendsto (fun ms => (cascadeRec k ms μs (G θ)).toReal)
        (𝓝[Set.pi Set.univ fun _ => Set.Ioc (0 : ℝ) 1] ms₀)
        (𝓝 (cascadeRec k ms₀ μs (G θ)).toReal) :=
      (ENNReal.tendsto_toReal hne).comp hc.tendsto
    exact (Real.continuousAt_log (ENNReal.toReal_pos hpos'.ne' hne).ne').tendsto.comp h1

/-- **`∫ F₁(θ) dθ` is continuous in the exponents on `(0, 1]^k`**, Talagrand's form: for
`F₁ = parisiRec k ms μs (F θ)` with `∫∫ exp F < ∞` and `∫∫ |F| < ∞`. -/
theorem continuousOn_integral_parisiRec {F : Θ → (Fin k → T') → ℝ}
    (hFm : Measurable (Function.uncurry F))
    (hint : ∫⁻ θ, ∫⁻ x, ENNReal.ofReal (Real.exp (F θ x)) ∂Measure.pi μs ∂Pθ ≠ ∞)
    (habs : ∫⁻ θ, ∫⁻ x, ‖F θ x‖ₑ ∂Measure.pi μs ∂Pθ ≠ ∞) :
    ContinuousOn (fun ms => ∫ θ, parisiRec k ms μs (F θ) ∂Pθ)
      (Set.pi Set.univ fun _ => Set.Ioc (0 : ℝ) 1) := by
  have h1 : ∀ x : ℝ, (ENNReal.ofReal (Real.exp x)).toReal = Real.exp x := fun x =>
    ENNReal.toReal_ofReal (Real.exp_pos x).le
  refine continuousOn_integral_log_cascadeRec k Pθ μs
    (fun θ x => ENNReal.ofReal (Real.exp (F θ x)))
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hFm))
    (fun θ x => ENNReal.ofReal_pos.2 (Real.exp_pos _)) (fun θ x => ENNReal.ofReal_ne_top) hint ?_
  simp only [h1, Real.log_exp]
  exact habs

omit [Nonempty T'] [IsProbabilityMeasure Pθ] in
/-- **The cascade sums are almost surely finite**, jointly in the parameter, the weights and the
marks, when `∫ G_θ d(μ₁ ⊗ ⋯ ⊗ μ_k) < ∞` for every `θ`: by the branch-law identity
`lintegral_cascadeSum_cascadeZip` and the almost-sure finiteness of the total weight. -/
theorem ae_cascadeSum_cascadeZip_lt_top (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i)
    (hlt : ∀ i, ms i < 1) (hGm : Measurable (Function.uncurry G))
    (hint : ∀ θ, ∫⁻ x, G θ x ∂Measure.pi μs ≠ ∞) :
    ∀ᵐ q ∂Pθ.prod ((cascadeWeightsLaw k ms).prod (cascadeMarksLaw k μs)),
      cascadeSum k (G q.1) (cascadeZip k (q.2.1, q.2.2)) < ∞ := by
  have hGθ : ∀ θ, Measurable (G θ) := fun θ =>
    hGm.comp (measurable_const.prodMk measurable_id)
  have hmeas : Measurable fun q : Θ × (CascadeWeights k × CascadeMarks T' k) =>
      cascadeSum k (G q.1) (cascadeZip k (q.2.1, q.2.2)) :=
    (measurable_cascadeSum_prod k (G := G) hGm).comp
      (measurable_fst.prodMk ((measurable_cascadeZip k).comp measurable_snd))
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_lt hmeas measurable_const)]
  refine Filter.Eventually.of_forall fun θ => ?_
  have hmeas' : Measurable fun r : CascadeWeights k × CascadeMarks T' k =>
      cascadeSum k (G θ) (cascadeZip k (r.1, r.2)) :=
    (measurable_cascadeSum k (hGθ θ)).comp (measurable_cascadeZip k)
  show ∀ᵐ r ∂(cascadeWeightsLaw k ms).prod (cascadeMarksLaw k μs),
    cascadeSum k (G θ) (cascadeZip k (r.1, r.2)) < ∞
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_lt hmeas' measurable_const)]
  filter_upwards [ae_weightSum_ne_zero_ne_top k ms hsm hpos hlt] with w hw
  show ∀ᵐ z ∂cascadeMarksLaw k μs, cascadeSum k (G θ) (cascadeZip k (w, z)) < ∞
  refine ae_lt_top ((measurable_cascadeSum k (hGθ θ)).comp
    ((measurable_cascadeZip k).comp (measurable_const.prodMk measurable_id))) ?_
  rw [lintegral_cascadeSum_cascadeZip k μs w (hGθ θ)]
  exact ENNReal.mul_ne_top hw.2 (hint θ)

omit [Nonempty T'] [IsProbabilityMeasure Pθ] in
/-- The total weight is almost surely positive and finite, jointly in the parameter and the
marks. -/
theorem ae_weightSum_prod (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1) :
    ∀ᵐ q ∂Pθ.prod ((cascadeWeightsLaw k ms).prod (cascadeMarksLaw k μs)),
      weightSum k q.2.1 ≠ 0 ∧ weightSum k q.2.1 ≠ ∞ := by
  have hset : MeasurableSet {q : Θ × (CascadeWeights k × CascadeMarks T' k) |
      weightSum k q.2.1 ≠ 0 ∧ weightSum k q.2.1 ≠ ∞} := by
    have h1 := (measurable_weightSum k).comp (measurable_fst.comp measurable_snd :
      Measurable fun q : Θ × (CascadeWeights k × CascadeMarks T' k) => q.2.1)
    exact (h1 (measurableSet_singleton 0)).compl.inter (h1 (measurableSet_singleton ∞)).compl
  rw [Measure.ae_prod_iff_ae_ae hset]
  refine Filter.Eventually.of_forall fun θ => ?_
  have hset' : MeasurableSet {r : CascadeWeights k × CascadeMarks T' k |
      weightSum k r.1 ≠ 0 ∧ weightSum k r.1 ≠ ∞} := by
    have h1 := (measurable_weightSum k).comp (measurable_fst :
      Measurable fun r : CascadeWeights k × CascadeMarks T' k => r.1)
    exact (h1 (measurableSet_singleton 0)).compl.inter (h1 (measurableSet_singleton ∞)).compl
  show ∀ᵐ r ∂(cascadeWeightsLaw k ms).prod (cascadeMarksLaw k μs),
    weightSum k r.1 ≠ 0 ∧ weightSum k r.1 ≠ ∞
  rw [Measure.ae_prod_iff_ae_ae hset']
  filter_upwards [ae_weightSum_ne_zero_ne_top k ms hsm hpos hlt] with w hw
  exact Filter.Eventually.of_forall fun _ => hw

/-- **Theorem 14.2.1 conditionally on the parameter, integrated**:
`∫ log (∑_α v_α G_θ(z_α) / ∑_α v_α) = ∫ log cascadeRec(G_θ) dθ`. -/
theorem integral_log_cascadeSum_div_prod_eq (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i)
    (hlt : ∀ i, ms i < 1) (hGm : Measurable (Function.uncurry G)) (hGpos : ∀ θ x, 0 < G θ x)
    (hGfin : ∀ θ x, G θ x ≠ ∞) (hint : ∫⁻ θ, ∫⁻ x, G θ x ∂Measure.pi μs ∂Pθ ≠ ∞)
    (hlog : ∫⁻ θ, ∫⁻ x, ‖Real.log (G θ x).toReal‖ₑ ∂Measure.pi μs ∂Pθ ≠ ∞)
    (hfin : ∀ θ, cascadeRec k ms μs (G θ) ≠ ∞) :
    (∫ q : CascadeWeights k × (Θ × CascadeMarks T' k),
        Real.log ((cascadeSum k (G q.2.1) (cascadeZip k (q.1, q.2.2))).toReal
          / (cascadeSum k (fun _ => 1) (cascadeZip k (q.1, q.2.2))).toReal)
        ∂(cascadeWeightsLaw k ms).prod (Pθ.prod (cascadeMarksLaw k μs)))
      = ∫ θ, Real.log (cascadeRec k ms μs (G θ)).toReal ∂Pθ := by
  have hφ : Measurable fun p : Θ × (CascadeWeights k × CascadeMarks T' k) =>
      ((p.2.1, (p.1, p.2.2)) : CascadeWeights k × (Θ × CascadeMarks T' k)) :=
    (measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hmeasL := measurable_log_cascadeSum_div_prod k G hGm
  have hI' := integrable_log_cascadeSum_div_prod' k Pθ ms μs G hsm hpos hlt hGm hGpos hGfin hint
    hlog
  rw [Measure.prod_swap_left₃ (cascadeWeightsLaw k ms) Pθ (cascadeMarksLaw k μs),
    integral_map hφ.aemeasurable hmeasL.aestronglyMeasurable]
  change (∫ p : Θ × (CascadeWeights k × CascadeMarks T' k),
      Real.log ((cascadeSum k (G p.1) (cascadeZip k (p.2.1, p.2.2))).toReal
        / (cascadeSum k (fun _ => 1) (cascadeZip k (p.2.1, p.2.2))).toReal) ∂_) = _
  rw [integral_prod _ hI']
  exact integral_congr_ae (Filter.Eventually.of_forall fun θ =>
    integral_log_cascadeSum_div_eq_of k ms μs G hsm hpos hlt hGm hGpos hfin θ)

end

end SpinGlass
