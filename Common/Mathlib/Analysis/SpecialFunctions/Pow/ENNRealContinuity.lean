/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Joint continuity of `x ^ y` on `ℝ≥0∞ × ℝ`

`(x, y) ↦ x ^ y` is continuous at every point of `ℝ≥0∞ × ℝ` with `x ∉ {0, ∞}` or `y ≠ 0`
(`ENNReal.continuousAt_rpow`), the exact analogue of `NNReal.continuousAt_rpow` and
`Real.continuousAt_rpow`; Mathlib only has the continuity in `x` at a fixed exponent
(`ENNReal.continuous_rpow_const`). The four exceptional points `(0, 0)` and `(∞, 0)` are genuine:
`0 ^ y` jumps from `∞` to `0` and `∞ ^ y` from `0` to `∞` as `y` crosses `0`.
`Filter.Tendsto.ennrpow` is the corresponding statement for limits.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace ENNReal

/-- At `(∞, y)` with `0 < y`: `x ^ y' ≥ x ^ (y/2) → ∞` on `{1 ≤ x, y/2 ≤ y'}`. -/
private lemma tendsto_rpow_nhds_top_of_pos {y : ℝ} (hy : 0 < y) :
    Tendsto (fun p : ℝ≥0∞ × ℝ => p.1 ^ p.2) (𝓝 ((⊤ : ℝ≥0∞), y)) (𝓝 ⊤) := by
  have h1 : Tendsto (fun p : ℝ≥0∞ × ℝ => p.1 ^ (y / 2)) (𝓝 ((⊤ : ℝ≥0∞), y)) (𝓝 ⊤) := by
    have := (continuous_rpow_const (y := y / 2)).tendsto (⊤ : ℝ≥0∞)
    rw [top_rpow_of_pos (by positivity)] at this
    exact this.comp (continuous_fst.tendsto _)
  refine tendsto_nhds_top_mono h1 ?_
  have hA : ∀ᶠ p : ℝ≥0∞ × ℝ in 𝓝 ((⊤ : ℝ≥0∞), y), 1 ≤ p.1 :=
    ((continuous_fst.tendsto _).eventually (lt_mem_nhds one_lt_top)).mono fun p hp => hp.le
  have hB : ∀ᶠ p : ℝ≥0∞ × ℝ in 𝓝 ((⊤ : ℝ≥0∞), y), y / 2 ≤ p.2 :=
    ((continuous_snd.tendsto _).eventually (lt_mem_nhds (by linarith : y / 2 < y))).mono
      fun p hp => hp.le
  filter_upwards [hA, hB] with p hp1 hp2
  exact rpow_le_rpow_of_exponent_le hp1 hp2

/-- At `(0, y)` with `0 < y`: `x ^ y' ≤ x ^ (y/2) → 0` on `{x ≤ 1, y/2 ≤ y'}`. -/
private lemma tendsto_rpow_nhds_zero_of_pos {y : ℝ} (hy : 0 < y) :
    Tendsto (fun p : ℝ≥0∞ × ℝ => p.1 ^ p.2) (𝓝 ((0 : ℝ≥0∞), y)) (𝓝 0) := by
  have h1 : Tendsto (fun p : ℝ≥0∞ × ℝ => p.1 ^ (y / 2)) (𝓝 ((0 : ℝ≥0∞), y)) (𝓝 0) := by
    have := (continuous_rpow_const (y := y / 2)).tendsto (0 : ℝ≥0∞)
    rw [zero_rpow_of_pos (by positivity)] at this
    exact this.comp (continuous_fst.tendsto _)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1
    (Eventually.of_forall fun _ => zero_le) ?_
  have hA : ∀ᶠ p : ℝ≥0∞ × ℝ in 𝓝 ((0 : ℝ≥0∞), y), p.1 ≤ 1 :=
    ((continuous_fst.tendsto _).eventually (gt_mem_nhds zero_lt_one)).mono fun p hp => hp.le
  have hB : ∀ᶠ p : ℝ≥0∞ × ℝ in 𝓝 ((0 : ℝ≥0∞), y), y / 2 ≤ p.2 :=
    ((continuous_snd.tendsto _).eventually (lt_mem_nhds (by linarith : y / 2 < y))).mono
      fun p hp => hp.le
  filter_upwards [hA, hB] with p hp1 hp2
  exact rpow_le_rpow_of_exponent_ge hp1 hp2

/-- At `(c, y)` with `c ∈ (0, ∞)`: transport `NNReal.continuousAt_rpow` along the coercion. -/
private lemma tendsto_rpow_nhds_coe {c : ℝ≥0} (hc : c ≠ 0) (y : ℝ) :
    Tendsto (fun p : ℝ≥0∞ × ℝ => p.1 ^ p.2) (𝓝 ((c : ℝ≥0∞), y)) (𝓝 ((c : ℝ≥0∞) ^ y)) := by
  have hT : Tendsto (fun p : ℝ≥0∞ × ℝ => (p.1.toNNReal, p.2)) (𝓝 ((c : ℝ≥0∞), y))
      (𝓝 (c, y)) := by
    have h1 : Tendsto (fun p : ℝ≥0∞ × ℝ => p.1.toNNReal) (𝓝 ((c : ℝ≥0∞), y)) (𝓝 c) := by
      have := (tendsto_toNNReal (coe_ne_top (r := c))).comp
        (continuous_fst.tendsto ((c : ℝ≥0∞), y))
      exact this
    exact h1.prodMk_nhds (continuous_snd.tendsto _)
  have h2 := (NNReal.continuousAt_rpow (x := c) (y := y) (Or.inl hc)).tendsto.comp hT
  have h3 : Tendsto (fun p : ℝ≥0∞ × ℝ => ((p.1.toNNReal ^ p.2 : ℝ≥0) : ℝ≥0∞))
      (𝓝 ((c : ℝ≥0∞), y)) (𝓝 ((c ^ y : ℝ≥0) : ℝ≥0∞)) := tendsto_coe.2 h2
  rw [coe_rpow_of_ne_zero hc] at h3
  refine h3.congr' ?_
  have hA : ∀ᶠ p : ℝ≥0∞ × ℝ in 𝓝 ((c : ℝ≥0∞), y), p.1 < ⊤ :=
    (continuous_fst.tendsto _).eventually (gt_mem_nhds coe_lt_top)
  have hB : ∀ᶠ p : ℝ≥0∞ × ℝ in 𝓝 ((c : ℝ≥0∞), y), 0 < p.1 :=
    (continuous_fst.tendsto _).eventually (lt_mem_nhds (coe_pos.2 (pos_iff_ne_zero.2 hc)))
  filter_upwards [hA, hB] with p hp1 hp2
  have hne : p.1.toNNReal ≠ 0 := by
    rw [Ne, toNNReal_eq_zero_iff, not_or]
    exact ⟨hp2.ne', hp1.ne⟩
  rw [coe_rpow_of_ne_zero hne, coe_toNNReal hp1.ne]

/-- Joint continuity of `x ^ y` at every `(x, y)` with `0 < y`. -/
theorem continuousAt_rpow_of_pos {x : ℝ≥0∞} {y : ℝ} (hy : 0 < y) :
    ContinuousAt (fun p : ℝ≥0∞ × ℝ => p.1 ^ p.2) (x, y) := by
  rcases eq_or_ne x ⊤ with rfl | hxt
  · rw [ContinuousAt, top_rpow_of_pos hy]
    exact tendsto_rpow_nhds_top_of_pos hy
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [ContinuousAt, zero_rpow_of_pos hy]
    exact tendsto_rpow_nhds_zero_of_pos hy
  lift x to ℝ≥0 using hxt
  exact tendsto_rpow_nhds_coe (by exact_mod_cast hx0) y

/-- **Joint continuity of `x ^ y` on `ℝ≥0∞ × ℝ`**, at every point with `x ∉ {0, ∞}` or `y ≠ 0`
(the analogue of `NNReal.continuousAt_rpow`). -/
theorem continuousAt_rpow {x : ℝ≥0∞} {y : ℝ} (h : (x ≠ 0 ∧ x ≠ ⊤) ∨ y ≠ 0) :
    ContinuousAt (fun p : ℝ≥0∞ × ℝ => p.1 ^ p.2) (x, y) := by
  rcases h with ⟨hx0, hxt⟩ | hy
  · lift x to ℝ≥0 using hxt
    exact tendsto_rpow_nhds_coe (by exact_mod_cast hx0) y
  rcases lt_or_gt_of_ne hy with hy | hy
  · -- `x ^ y = (x ^ (-y))⁻¹` with `0 < -y`
    have h1 : ContinuousAt (fun p : ℝ≥0∞ × ℝ => (p.1 ^ (-p.2))⁻¹) (x, y) := by
      have h2 : ContinuousAt (fun p : ℝ≥0∞ × ℝ => (p.1, -p.2)) (x, y) :=
        (continuous_fst.prodMk continuous_snd.neg).continuousAt
      have h3 : ContinuousAt (fun q : ℝ≥0∞ × ℝ => q.1 ^ q.2) (x, -y) :=
        continuousAt_rpow_of_pos (neg_pos.2 hy)
      exact continuous_inv.continuousAt.comp (h3.comp_of_eq h2 rfl)
    refine h1.congr (Eventually.of_forall fun p => ?_)
    simp only [rpow_neg, inv_inv]
  · exact continuousAt_rpow_of_pos hy

end ENNReal

/-- `m x ^ r x → a ^ b` when `m → a` and `r → b`, for `a ∉ {0, ∞}` or `b ≠ 0`. -/
theorem Filter.Tendsto.ennrpow {α : Type*} {f : Filter α} {m : α → ℝ≥0∞} {r : α → ℝ}
    {a : ℝ≥0∞} {b : ℝ} (hm : Tendsto m f (𝓝 a)) (hr : Tendsto r f (𝓝 b))
    (h : (a ≠ 0 ∧ a ≠ ⊤) ∨ b ≠ 0) : Tendsto (fun x => m x ^ r x) f (𝓝 (a ^ b)) :=
  (ENNReal.continuousAt_rpow h).tendsto.comp (hm.prodMk_nhds hr)
