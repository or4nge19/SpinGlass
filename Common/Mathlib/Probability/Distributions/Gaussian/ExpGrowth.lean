/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Functions of exponential growth and Gaussian integrals

`HasExpGrowth F` means `|F x| ≤ C exp (c |x|)` for some `C` and some `c ≥ 0`, and
`HasLinearGrowth A` means `|A x| ≤ a + b |x|`. Functions of exponential growth are integrable
against every real Gaussian law (`HasExpGrowth.integrable_gaussianReal`), and
`x ↦ ∫ F (x + z) dγ(z)` is differentiable with derivative `∫ F' (x + z) dγ(z)` as soon as `F`
and `F'` have exponential growth (`hasDerivAt_integral_comp_add_gaussianReal`). These are the
integrability and differentiation facts behind Talagrand's operators `T_{m,v}` (Vol. II, §14.7).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-- `F` has exponential growth: `|F x| ≤ C exp (c |x|)` for some `C` and some `c ≥ 0`. -/
def HasExpGrowth (F : ℝ → ℝ) : Prop := ∃ C c : ℝ, 0 ≤ c ∧ ∀ x, |F x| ≤ C * Real.exp (c * |x|)

/-- `A` has linear growth: `|A x| ≤ a + b |x|` for some `a` and some `b ≥ 0`. -/
def HasLinearGrowth (A : ℝ → ℝ) : Prop := ∃ a b : ℝ, 0 ≤ b ∧ ∀ x, |A x| ≤ a + b * |x|

/-- `exp (c |x|)` is integrable against every real Gaussian law. -/
lemma integrable_exp_mul_abs_gaussianReal (μ : ℝ) (v : ℝ≥0) (c : ℝ) :
    Integrable (fun x => Real.exp (c * |x|)) (gaussianReal μ v) := by
  have hg : Integrable (fun x => Real.exp (c * x) + Real.exp (-c * x)) (gaussianReal μ v) :=
    (integrable_exp_mul_gaussianReal (μ := μ) (v := v) c).add
      (integrable_exp_mul_gaussianReal (μ := μ) (v := v) (-c))
  refine hg.mono' (Real.continuous_exp.comp
    (continuous_const.mul continuous_abs)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    linarith [Real.exp_pos (-c * x)]
  · rw [abs_of_nonpos hx, show c * -x = -c * x by ring]
    linarith [Real.exp_pos (c * x)]

/-- A function with a Lipschitz bound is Lipschitz with the corresponding nonnegative constant. -/
lemma lipschitzWith_toNNReal_of_abs_sub_le {f : ℝ → ℝ} {L : ℝ}
    (h : ∀ x y, |f y - f x| ≤ L * |y - x|) : LipschitzWith (Real.toNNReal L) f := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq]
  have h1 : |f x - f y| ≤ L * |x - y| := h y x
  refine h1.trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) (abs_nonneg _))

namespace HasExpGrowth

variable {F G : ℝ → ℝ}

lemma of_abs_le {C c : ℝ} (hc : 0 ≤ c) (h : ∀ x, |F x| ≤ C * Real.exp (c * |x|)) :
    HasExpGrowth F := ⟨C, c, hc, h⟩

lemma of_bounded {C : ℝ} (h : ∀ x, |F x| ≤ C) : HasExpGrowth F :=
  ⟨C, 0, le_rfl, fun x => by simpa using h x⟩

lemma const (c : ℝ) : HasExpGrowth fun _ => c := of_bounded fun _ => le_rfl

/-- The constant `C` in an exponential bound is nonnegative. -/
lemma nonneg_of_bound {C c : ℝ} (h : ∀ x, |F x| ≤ C * Real.exp (c * |x|)) : 0 ≤ C := by
  have := (abs_nonneg (F 0)).trans (h 0)
  simpa using this

lemma add (hF : HasExpGrowth F) (hG : HasExpGrowth G) : HasExpGrowth fun x => F x + G x := by
  obtain ⟨C₁, c₁, hc₁, h₁⟩ := hF
  obtain ⟨C₂, c₂, hc₂, h₂⟩ := hG
  have hC₁ := nonneg_of_bound h₁
  have hC₂ := nonneg_of_bound h₂
  refine ⟨C₁ + C₂, max c₁ c₂, le_max_of_le_left hc₁, fun x => ?_⟩
  have e₁ : Real.exp (c₁ * |x|) ≤ Real.exp (max c₁ c₂ * |x|) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg x))
  have e₂ : Real.exp (c₂ * |x|) ≤ Real.exp (max c₁ c₂ * |x|) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg x))
  calc |F x + G x| ≤ |F x| + |G x| := abs_add_le _ _
    _ ≤ C₁ * Real.exp (c₁ * |x|) + C₂ * Real.exp (c₂ * |x|) := add_le_add (h₁ x) (h₂ x)
    _ ≤ C₁ * Real.exp (max c₁ c₂ * |x|) + C₂ * Real.exp (max c₁ c₂ * |x|) :=
        add_le_add (mul_le_mul_of_nonneg_left e₁ hC₁) (mul_le_mul_of_nonneg_left e₂ hC₂)
    _ = (C₁ + C₂) * Real.exp (max c₁ c₂ * |x|) := by ring

lemma mul (hF : HasExpGrowth F) (hG : HasExpGrowth G) : HasExpGrowth fun x => F x * G x := by
  obtain ⟨C₁, c₁, hc₁, h₁⟩ := hF
  obtain ⟨C₂, c₂, hc₂, h₂⟩ := hG
  have hC₁ := nonneg_of_bound h₁
  refine ⟨C₁ * C₂, c₁ + c₂, add_nonneg hc₁ hc₂, fun x => ?_⟩
  rw [abs_mul, add_mul, Real.exp_add]
  calc |F x| * |G x| ≤ (C₁ * Real.exp (c₁ * |x|)) * (C₂ * Real.exp (c₂ * |x|)) :=
        mul_le_mul (h₁ x) (h₂ x) (abs_nonneg _) (mul_nonneg hC₁ (Real.exp_pos _).le)
    _ = C₁ * C₂ * (Real.exp (c₁ * |x|) * Real.exp (c₂ * |x|)) := by ring

lemma const_mul (hF : HasExpGrowth F) (a : ℝ) : HasExpGrowth fun x => a * F x :=
  (const a).mul hF

lemma neg (hF : HasExpGrowth F) : HasExpGrowth fun x => -F x := by
  obtain ⟨C, c, hc, h⟩ := hF
  exact ⟨C, c, hc, fun x => by rw [abs_neg]; exact h x⟩

lemma sub (hF : HasExpGrowth F) (hG : HasExpGrowth G) : HasExpGrowth fun x => F x - G x := by
  simpa [sub_eq_add_neg] using hF.add hG.neg

lemma pow (hF : HasExpGrowth F) (n : ℕ) : HasExpGrowth fun x => F x ^ n := by
  induction n with
  | zero => simpa using const 1
  | succ n ih => simpa [pow_succ] using ih.mul hF

lemma abs (hF : HasExpGrowth F) : HasExpGrowth fun x => |F x| := by
  obtain ⟨C, c, hc, h⟩ := hF
  exact ⟨C, c, hc, fun x => by rw [abs_abs]; exact h x⟩

/-- Shifting the argument preserves exponential growth. -/
lemma comp_add_const (hF : HasExpGrowth F) (a : ℝ) : HasExpGrowth fun x => F (a + x) := by
  obtain ⟨C, c, hc, h⟩ := hF
  refine ⟨C * Real.exp (c * |a|), c, hc, fun x => ?_⟩
  have hC := nonneg_of_bound h
  calc |F (a + x)| ≤ C * Real.exp (c * |a + x|) := h _
    _ ≤ C * Real.exp (c * (|a| + |x|)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
          (mul_le_mul_of_nonneg_left (abs_add_le _ _) hc)) hC
    _ = C * Real.exp (c * |a|) * Real.exp (c * |x|) := by rw [mul_add, Real.exp_add]; ring

/-- Scaling the argument preserves exponential growth. -/
lemma comp_const_mul (hF : HasExpGrowth F) (a : ℝ) : HasExpGrowth fun x => F (a * x) := by
  obtain ⟨C, c, hc, h⟩ := hF
  refine ⟨C, c * |a|, mul_nonneg hc (abs_nonneg a), fun x => ?_⟩
  have := h (a * x)
  rwa [abs_mul, ← mul_assoc] at this

/-- A uniform exponential bound on `F (x + z)` for `x` in a ball. -/
lemma bound_shift (hF : HasExpGrowth F) (x₀ r : ℝ) :
    ∃ C c : ℝ, 0 ≤ c ∧ ∀ x ∈ Metric.ball x₀ r, ∀ z, |F (x + z)| ≤ C * Real.exp (c * |z|) := by
  obtain ⟨C, c, hc, h⟩ := hF
  have hC := nonneg_of_bound h
  refine ⟨C * Real.exp (c * (|x₀| + r)), c, hc, fun x hx z => ?_⟩
  have hx' : |x| ≤ |x₀| + r := by
    have := Metric.mem_ball.1 hx
    rw [Real.dist_eq] at this
    calc |x| = |x₀ + (x - x₀)| := by ring_nf
      _ ≤ |x₀| + |x - x₀| := abs_add_le _ _
      _ ≤ |x₀| + r := by linarith
  calc |F (x + z)| ≤ C * Real.exp (c * |x + z|) := h _
    _ ≤ C * Real.exp (c * ((|x₀| + r) + |z|)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hc)) hC
        linarith [abs_add_le x z]
    _ = C * Real.exp (c * (|x₀| + r)) * Real.exp (c * |z|) := by rw [mul_add, Real.exp_add]; ring

/-- Functions of exponential growth are Gaussian-integrable. -/
lemma integrable_gaussianReal (hF : HasExpGrowth F) {μ : ℝ} {v : ℝ≥0}
    (hFm : AEStronglyMeasurable F (gaussianReal μ v)) : Integrable F (gaussianReal μ v) := by
  obtain ⟨C, c, _, h⟩ := hF
  exact ((integrable_exp_mul_abs_gaussianReal μ v c).const_mul C).mono' hFm
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact h x)

end HasExpGrowth

namespace HasLinearGrowth

variable {A : ℝ → ℝ}

/-- A Lipschitz function has linear growth. -/
lemma of_lipschitz {L : ℝ} (h : ∀ x y, |A y - A x| ≤ L * |y - x|) : HasLinearGrowth A := by
  have hL : 0 ≤ L := by
    have := h 0 1
    have h1 : |(1 : ℝ) - 0| = 1 := by norm_num
    rw [h1, mul_one] at this
    exact (abs_nonneg _).trans this
  refine ⟨|A 0|, L, hL, fun x => ?_⟩
  have h2 := h 0 x
  rw [sub_zero] at h2
  calc |A x| = |A 0 + (A x - A 0)| := by ring_nf
    _ ≤ |A 0| + |A x - A 0| := abs_add_le _ _
    _ ≤ |A 0| + L * |x| := by gcongr

lemma toHasExpGrowth (hA : HasLinearGrowth A) : HasExpGrowth A := by
  obtain ⟨a, b, hb, h⟩ := hA
  refine ⟨|a| + b, b + 1, by linarith, fun x => ?_⟩
  have h1 : |x| ≤ Real.exp ((b + 1) * |x|) := by
    have e1 : |x| + 1 ≤ Real.exp |x| := Real.add_one_le_exp |x|
    have e2 : Real.exp |x| ≤ Real.exp ((b + 1) * |x|) :=
      Real.exp_le_exp.2 (by nlinarith [abs_nonneg x])
    linarith
  have h2 : 1 ≤ Real.exp ((b + 1) * |x|) := Real.one_le_exp (by positivity)
  calc |A x| ≤ a + b * |x| := h x
    _ ≤ |a| + b * |x| := by linarith [le_abs_self a]
    _ ≤ (|a| + b) * Real.exp ((b + 1) * |x|) := by
        nlinarith [mul_nonneg (abs_nonneg a) (sub_nonneg.2 h2), mul_nonneg hb (sub_nonneg.2 h1)]

/-- `exp (m A)` has exponential growth when `A` has linear growth. -/
lemma exp_mul (hA : HasLinearGrowth A) (m : ℝ) : HasExpGrowth fun x => Real.exp (m * A x) := by
  obtain ⟨a, b, hb, h⟩ := hA
  refine ⟨Real.exp (|m| * a), |m| * b, mul_nonneg (abs_nonneg m) hb, fun x => ?_⟩
  rw [abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  calc m * A x ≤ |m * A x| := le_abs_self _
    _ = |m| * |A x| := abs_mul _ _
    _ ≤ |m| * (a + b * |x|) := mul_le_mul_of_nonneg_left (h x) (abs_nonneg m)
    _ = |m| * a + |m| * b * |x| := by ring

/-- Adding a constant preserves linear growth. -/
lemma add_const (hA : HasLinearGrowth A) (c : ℝ) : HasLinearGrowth fun x => A x + c := by
  obtain ⟨a, b, hb, h⟩ := hA
  refine ⟨a + |c|, b, hb, fun x => ?_⟩
  calc |A x + c| ≤ |A x| + |c| := abs_add_le _ _
    _ ≤ a + b * |x| + |c| := by linarith [h x]
    _ = a + |c| + b * |x| := by ring

lemma comp_add_const (hA : HasLinearGrowth A) (c : ℝ) : HasLinearGrowth fun x => A (c + x) := by
  obtain ⟨a, b, hb, h⟩ := hA
  refine ⟨a + b * |c|, b, hb, fun x => ?_⟩
  calc |A (c + x)| ≤ a + b * |c + x| := h _
    _ ≤ a + b * (|c| + |x|) := by nlinarith [abs_add_le c x, hb]
    _ = a + b * |c| + b * |x| := by ring

lemma of_bounded_deriv {A' : ℝ → ℝ} (hA : ∀ x, HasDerivAt A (A' x) x) {L : ℝ}
    (hL : ∀ x, |A' x| ≤ L) : HasLinearGrowth A := by
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  refine ⟨|A 0|, L, hL0, fun x => ?_⟩
  have key : |A x - A 0| ≤ L * |x - 0| := by
    -- mean value inequality on the segment
    have hd : ∀ y ∈ Set.uIcc 0 x, HasDerivWithinAt A (A' y) (Set.uIcc 0 x) y :=
      fun y _ => (hA y).hasDerivWithinAt
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := L)
      (fun y hy => hd y hy) (fun y _ => by rw [Real.norm_eq_abs]; exact hL y)
      (convex_uIcc 0 x) (Set.left_mem_uIcc) (Set.right_mem_uIcc)
    simpa [Real.norm_eq_abs] using this
  calc |A x| = |A 0 + (A x - A 0)| := by ring_nf
    _ ≤ |A 0| + |A x - A 0| := abs_add_le _ _
    _ ≤ |A 0| + L * |x| := by
        rw [sub_zero] at key
        linarith

end HasLinearGrowth

/-- **Differentiation under a Gaussian integral of a shifted function**: if `F` and `F'` have
exponential growth, `x ↦ ∫ F (x + z) dγ(z)` has derivative `∫ F' (x + z) dγ(z)`. -/
theorem hasDerivAt_integral_comp_add_gaussianReal {F F' : ℝ → ℝ}
    (hF : ∀ y, HasDerivAt F (F' y) y) (hFg : HasExpGrowth F) (hF'g : HasExpGrowth F')
    (hF'm : Measurable F') (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    HasDerivAt (fun x => ∫ z, F (x + z) ∂gaussianReal μ v)
      (∫ z, F' (x + z) ∂gaussianReal μ v) x := by
  obtain ⟨C, c, _, hb⟩ := hF'g.bound_shift x 1
  have hFm : Measurable F :=
    (continuous_iff_continuousAt.2 fun y => (hF y).continuousAt).measurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gaussianReal μ v)
    (F := fun x z => F (x + z)) (F' := fun x z => F' (x + z))
    (bound := fun z => C * Real.exp (c * |z|)) (s := Metric.ball x 1)
    (Metric.ball_mem_nhds x one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.Eventually.of_forall fun y =>
      (hFm.comp (measurable_const.add measurable_id)).aestronglyMeasurable
  · exact (hFg.comp_add_const x).integrable_gaussianReal
      (hFm.comp (measurable_const.add measurable_id)).aestronglyMeasurable
  · exact (hF'm.comp (measurable_const.add measurable_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z y hy => by
      rw [Real.norm_eq_abs]; exact hb y hy z
  · exact (integrable_exp_mul_abs_gaussianReal μ v c).const_mul C
  · exact Filter.Eventually.of_forall fun z y _ => (hF (y + z)).comp_add_const y z

end ProbabilityTheory
