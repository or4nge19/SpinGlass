/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.PointProcess.Cascade

/-!
# Linearity and monotonicity of the cascade sum

`cascadeSum k G ω = ∑_α u*_α G(z_α)` is additive, positively homogeneous and monotone in the
branch function `G` (`cascadeSum_add`, `cascadeSum_const_mul`, `cascadeSum_mono`), level by level
from the corresponding properties of the weighted sum `pdSum`.
-/

open MeasureTheory Set Function
open scoped ENNReal

namespace ProbabilityTheory

universe u

noncomputable section

section pdSum

variable {M : Type*} [MeasurableSpace M]

lemma pdSum_add {v w : M → ℝ≥0∞} (hv : Measurable v) (N : Measure (ℝ × M)) :
    pdSum (fun m => v m + w m) N = pdSum v N + pdSum w N := by
  unfold pdSum
  simp_rw [mul_add]
  exact lintegral_add_left (measurable_ofReal_mul hv) _

lemma pdSum_const_mul (c : ℝ≥0∞) {v : M → ℝ≥0∞} (hv : Measurable v) (N : Measure (ℝ × M)) :
    pdSum (fun m => c * v m) N = c * pdSum v N := by
  unfold pdSum
  simp_rw [mul_left_comm _ c]
  exact lintegral_const_mul c (measurable_ofReal_mul hv)

lemma pdSum_mono {v w : M → ℝ≥0∞} (h : ∀ m, v m ≤ w m) (N : Measure (ℝ × M)) :
    pdSum v N ≤ pdSum w N :=
  lintegral_mono fun p => mul_le_mul' le_rfl (h p.2)

end pdSum

variable {T : Type u} [MeasurableSpace T]

/-- **Additivity of the cascade sum** in the branch function. -/
theorem cascadeSum_add (k : ℕ) :
    ∀ {G H : (Fin k → T) → ℝ≥0∞}, Measurable G → Measurable H → ∀ ω : CascadeSpace T k,
      cascadeSum k (fun z => G z + H z) ω = cascadeSum k G ω + cascadeSum k H ω := by
  induction k with
  | zero =>
    intro G H _ _ ω
    rfl
  | succ k ih =>
    intro G H hG hH ω
    rw [cascadeSum_succ, cascadeSum_succ, cascadeSum_succ]
    have hv : Measurable fun p : T × CascadeSpace T k =>
        cascadeSum k (fun zs => G (Fin.cons p.1 zs)) p.2 :=
      measurable_cascadeSum_prod k (α := T) (G := fun z zs => G (Fin.cons z zs))
        (hG.comp measurable_fin_cons)
    have hpt : (fun p : T × CascadeSpace T k =>
          cascadeSum k (fun zs => G (Fin.cons p.1 zs) + H (Fin.cons p.1 zs)) p.2)
        = fun p => cascadeSum k (fun zs => G (Fin.cons p.1 zs)) p.2
          + cascadeSum k (fun zs => H (Fin.cons p.1 zs)) p.2 :=
      funext fun p =>
        ih (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id)))
          (hH.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id))) p.2
    rw [hpt]
    exact pdSum_add hv _

/-- **Positive homogeneity of the cascade sum** in the branch function. -/
theorem cascadeSum_const_mul (k : ℕ) (c : ℝ≥0∞) :
    ∀ {G : (Fin k → T) → ℝ≥0∞}, Measurable G → ∀ ω : CascadeSpace T k,
      cascadeSum k (fun z => c * G z) ω = c * cascadeSum k G ω := by
  induction k with
  | zero =>
    intro G _ ω
    rfl
  | succ k ih =>
    intro G hG ω
    rw [cascadeSum_succ, cascadeSum_succ]
    have hv : Measurable fun p : T × CascadeSpace T k =>
        cascadeSum k (fun zs => G (Fin.cons p.1 zs)) p.2 :=
      measurable_cascadeSum_prod k (α := T) (G := fun z zs => G (Fin.cons z zs))
        (hG.comp measurable_fin_cons)
    have hpt : (fun p : T × CascadeSpace T k =>
          cascadeSum k (fun zs => c * G (Fin.cons p.1 zs)) p.2)
        = fun p => c * cascadeSum k (fun zs => G (Fin.cons p.1 zs)) p.2 :=
      funext fun p =>
        ih (hG.comp (measurable_fin_cons.comp (measurable_const.prodMk measurable_id))) p.2
    rw [hpt]
    exact pdSum_const_mul c hv _

/-- **Monotonicity of the cascade sum** in the branch function. -/
theorem cascadeSum_mono (k : ℕ) :
    ∀ {G H : (Fin k → T) → ℝ≥0∞}, (∀ z, G z ≤ H z) → ∀ ω : CascadeSpace T k,
      cascadeSum k G ω ≤ cascadeSum k H ω := by
  induction k with
  | zero =>
    intro G H h ω
    exact h _
  | succ k ih =>
    intro G H h ω
    rw [cascadeSum_succ, cascadeSum_succ]
    exact pdSum_mono (fun p : T × CascadeSpace T k => ih (fun zs => h (Fin.cons p.1 zs)) p.2) _

end

end ProbabilityTheory
