/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.Distributions.Gaussian.HeatSemigroup
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Integral

/-!
# Talagrand's operators `T_{m,v}`: the Cole–Hopf transform of Gaussian smoothing

`coleHopf m v A x = (1/m) log 𝔼 exp (m A(x + g√v))` for `m ≠ 0`, and `𝔼 A(x + g√v)` for `m = 0`
(Talagrand Vol. II, (14.193)–(14.194); `g` standard Gaussian). It is the Cole–Hopf solution of the
viscous Hamilton–Jacobi equation `∂_v B = B''/2 + (m/2) B'²`, the Parisi PDE at one level.
For `A` of linear growth with a derivative `A'` of exponential growth:

- `hasDerivAt_coleHopf` (14.202): `B' = 𝔼 (A'(Y) Q)` with `Y = x + g√v`,
  `Q = exp m (A(Y) − B(x))`, `𝔼 Q = 1` (`integral_coleHopfQ`);
- `abs_integral_mul_coleHopfQ_le`: `|B'| ≤ sup |A'|`;
- `hasDerivAt_integral_deriv_mul_coleHopfQ` (14.203):
  `B'' = 𝔼 (A''(Y) Q) + m 𝔼 (A'(Y)² Q) − m B'²`;
- `integral_sq_mul_coleHopfQ_sub_sq_nonneg` (the Cauchy–Schwarz step of (14.198));
- `coleHopf_mono`, `coleHopf_add_const`, `coleHopf_comp_const_add`: monotone in the function,
  commutes with adding a constant and with translations — from which, for *every* exponent and
  with no differentiability, `T_{m,v}` preserves Lipschitz constants
  (`abs_coleHopf_sub_le_of_lipschitz`, Talagrand's `|A_p'| ≤ 1` of (14.271)), is a contraction for
  the sup norm (`abs_coleHopf_sub_le_of_sup`), and is strongly continuous in the variance on
  Lipschitz functions with modulus `T_{m,v}(L|·|)(0)` (`abs_coleHopf_sub_self_le`,
  `tendsto_coleHopfModulus`, `abs_coleHopf_sub_coleHopf_le`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-- **Talagrand's operator `T_{m,v}`** (Vol. II, (14.193)): `(1/m) log 𝔼 exp (m A(x + g√v))` for
`m ≠ 0`, and `𝔼 A(x + g√v)` for `m = 0`. -/
noncomputable def coleHopf (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ) (x : ℝ) : ℝ :=
  if m = 0 then ∫ z, A (x + z) ∂gaussianReal 0 v
  else (1 / m) * Real.log (∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v)

/-- **The tilt weight** `Q = exp m (A(Y) − B(x))` of (14.201). -/
noncomputable def coleHopfQ (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ) (x z : ℝ) : ℝ :=
  Real.exp (m * (A (x + z) - coleHopf m v A x))

variable {m : ℝ} {v : ℝ≥0} {A A' A'' B : ℝ → ℝ}

lemma coleHopf_of_ne (hm : m ≠ 0) (v : ℝ≥0) (A : ℝ → ℝ) (x : ℝ) :
    coleHopf m v A x = (1 / m) * Real.log (∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v) :=
  ite_eq_right hm

@[simp] lemma coleHopf_zero (v : ℝ≥0) (A : ℝ → ℝ) (x : ℝ) :
    coleHopf 0 v A x = ∫ z, A (x + z) ∂gaussianReal 0 v := ite_eq_left rfl

/-- **`T_{m,0}` is the identity**: a level with zero variance does nothing. -/
@[simp] lemma coleHopf_zero_var (m : ℝ) (A : ℝ → ℝ) (x : ℝ) : coleHopf m 0 A x = A x := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [coleHopf_zero, gaussianReal_zero_var, integral_dirac]
    simp
  · rw [coleHopf_of_ne hm, gaussianReal_zero_var, integral_dirac]
    simp only [add_zero, Real.log_exp]
    field_simp

@[simp] lemma coleHopfQ_zero (v : ℝ≥0) (A : ℝ → ℝ) (x z : ℝ) : coleHopfQ 0 v A x z = 1 := by
  simp [coleHopfQ]

lemma coleHopfQ_pos (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ) (x z : ℝ) : 0 < coleHopfQ m v A x z :=
  Real.exp_pos _

lemma measurable_coleHopfQ (hAm : Measurable A) (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    Measurable (coleHopfQ m v A x) :=
  Real.measurable_exp.comp (measurable_const.mul
    ((hAm.comp (measurable_const.add measurable_id)).sub measurable_const))

section Growth

variable (hA : HasLinearGrowth A) (hAm : Measurable A)
include hA hAm

lemma integrable_exp_mul_comp_add (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    Integrable (fun z => Real.exp (m * A (x + z))) (gaussianReal 0 v) :=
  ((hA.comp_add_const x).exp_mul m).integrable_gaussianReal
    (Real.measurable_exp.comp (measurable_const.mul
      (hAm.comp (measurable_const.add measurable_id)))).aestronglyMeasurable

lemma integral_exp_mul_comp_add_pos (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    0 < ∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v :=
  integral_exp_pos (integrable_exp_mul_comp_add hA hAm m v x)

/-- `exp (m B(x)) = 𝔼 exp (m A(x + g√v))`. -/
lemma exp_mul_coleHopf (hm : m ≠ 0) (v : ℝ≥0) (x : ℝ) :
    Real.exp (m * coleHopf m v A x) = ∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v := by
  rw [coleHopf_of_ne hm, ← mul_assoc, mul_one_div_cancel hm, one_mul,
    Real.exp_log (integral_exp_mul_comp_add_pos hA hAm m v x)]

/-- `Q = exp (m A(Y)) / 𝔼 exp (m A(Y))`. -/
lemma coleHopfQ_eq (hm : m ≠ 0) (v : ℝ≥0) (x z : ℝ) :
    coleHopfQ m v A x z
      = Real.exp (m * A (x + z)) / ∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v := by
  rw [coleHopfQ, mul_sub, Real.exp_sub, exp_mul_coleHopf hA hAm hm]

lemma integrable_coleHopfQ (hm : m ≠ 0) (v : ℝ≥0) (x : ℝ) :
    Integrable (coleHopfQ m v A x) (gaussianReal 0 v) := by
  have h := (integrable_exp_mul_comp_add hA hAm m v x).div_const
    (∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v)
  exact h.congr (Filter.Eventually.of_forall fun z => (coleHopfQ_eq hA hAm hm v x z).symm)

/-- **`𝔼 Q = 1`** ((14.201)). -/
lemma integral_coleHopfQ (hm : m ≠ 0) (v : ℝ≥0) (x : ℝ) :
    ∫ z, coleHopfQ m v A x z ∂gaussianReal 0 v = 1 := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun z => coleHopfQ_eq hA hAm hm v x z),
    integral_div, div_self (integral_exp_mul_comp_add_pos hA hAm m v x).ne']

/-- A function of exponential growth, weighted by `Q`, is integrable. -/
lemma integrable_mul_coleHopfQ (hm : m ≠ 0) {G : ℝ → ℝ} (hG : HasExpGrowth G)
    (hGm : Measurable G) (v : ℝ≥0) (x : ℝ) :
    Integrable (fun z => G (x + z) * coleHopfQ m v A x z) (gaussianReal 0 v) := by
  have h1 : HasExpGrowth fun z => G (x + z) * Real.exp (m * A (x + z)) :=
    (hG.comp_add_const x).mul ((hA.comp_add_const x).exp_mul m)
  have h2 : Integrable (fun z => G (x + z) * Real.exp (m * A (x + z))) (gaussianReal 0 v) :=
    h1.integrable_gaussianReal ((hGm.comp (measurable_const.add measurable_id)).mul
      (Real.measurable_exp.comp (measurable_const.mul
        (hAm.comp (measurable_const.add measurable_id))))).aestronglyMeasurable
  refine (h2.div_const (∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v)).congr
    (Filter.Eventually.of_forall fun z => ?_)
  beta_reduce
  rw [coleHopfQ_eq hA hAm hm, mul_div_assoc]

/-- The `Q`-average of a function bounded by `L` is bounded by `L`. -/
lemma abs_integral_mul_coleHopfQ_le (hm : m ≠ 0) {G : ℝ → ℝ} (hGm : Measurable G) {L : ℝ}
    (hL : ∀ y, |G y| ≤ L) (v : ℝ≥0) (x : ℝ) :
    |∫ z, G (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v| ≤ L := by
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  have hQi := integrable_coleHopfQ hA hAm hm v x
  have hint : Integrable (fun z => G (x + z) * coleHopfQ m v A x z) (gaussianReal 0 v) :=
    integrable_mul_coleHopfQ hA hAm hm (HasExpGrowth.of_bounded hL) hGm v x
  calc |∫ z, G (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v|
      ≤ ∫ z, |G (x + z) * coleHopfQ m v A x z| ∂gaussianReal 0 v := by
        have := norm_integral_le_integral_norm (μ := gaussianReal 0 v)
          (fun z => G (x + z) * coleHopfQ m v A x z)
        simpa [Real.norm_eq_abs] using this
    _ ≤ ∫ z, L * coleHopfQ m v A x z ∂gaussianReal 0 v := by
        refine integral_mono hint.abs (hQi.const_mul L) fun z => ?_
        rw [abs_mul, abs_of_pos (coleHopfQ_pos m v A x z)]
        exact mul_le_mul_of_nonneg_right (hL _) (coleHopfQ_pos m v A x z).le
    _ = L := by rw [integral_const_mul, integral_coleHopfQ hA hAm hm, mul_one]

end Growth

lemma measurable_of_hasDerivAt (hA : ∀ y, HasDerivAt A (A' y) y) : Measurable A :=
  (continuous_iff_continuousAt.2 fun y => (hA y).continuousAt).measurable

section Deriv

variable (hA : ∀ y, HasDerivAt A (A' y) y) (hAg : HasLinearGrowth A)
  (hA'g : HasExpGrowth A') (hA'm : Measurable A')
include hA hAg hA'g hA'm

/-- The derivative of `x ↦ 𝔼 exp (m A(x + g√v))`. -/
lemma hasDerivAt_integral_exp_mul (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    HasDerivAt (fun x => ∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v)
      (∫ z, m * A' (x + z) * Real.exp (m * A (x + z)) ∂gaussianReal 0 v) x := by
  have hF : ∀ y, HasDerivAt (fun y => Real.exp (m * A y)) (m * A' y * Real.exp (m * A y)) y := by
    intro y
    have := ((hA y).const_mul m).exp
    simpa [mul_comm] using this
  exact hasDerivAt_integral_comp_add_gaussianReal hF (hAg.exp_mul m)
    ((hA'g.const_mul m).mul (hAg.exp_mul m))
    ((measurable_const.mul hA'm).mul (Real.measurable_exp.comp (measurable_const.mul
      (measurable_of_hasDerivAt hA)))) 0 v x

/-- **Talagrand's (14.202)**: `B' = 𝔼 (A'(Y) Q)`. -/
theorem hasDerivAt_coleHopf (hm : m ≠ 0) (v : ℝ≥0) (x : ℝ) :
    HasDerivAt (coleHopf m v A) (∫ z, A' (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v) x := by
  have hAm := measurable_of_hasDerivAt hA
  have hfun : coleHopf m v A
      = fun x => (1 / m) * Real.log (∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v) :=
    funext fun x => coleHopf_of_ne hm v A x
  rw [hfun]
  have hI := hasDerivAt_integral_exp_mul hA hAg hA'g hA'm m v x
  have hpos := integral_exp_mul_comp_add_pos hAg hAm m v x
  refine ((hI.log hpos.ne').const_mul (1 / m)).congr_deriv ?_
  have e2 : ∫ z, A' (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v
      = (∫ z, A' (x + z) * Real.exp (m * A (x + z)) ∂gaussianReal 0 v)
        / ∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v := by
    rw [← integral_div]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
      beta_reduce
      rw [coleHopfQ_eq hAg hAm hm v x z, mul_div_assoc])
  have e3 : (∫ z, m * A' (x + z) * Real.exp (m * A (x + z)) ∂gaussianReal 0 v)
      = m * ∫ z, A' (x + z) * Real.exp (m * A (x + z)) ∂gaussianReal 0 v := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
      beta_reduce
      ring)
  rw [e2, e3]
  field_simp

end Deriv

section SecondDeriv

variable (hA : ∀ y, HasDerivAt A (A' y) y) (hA' : ∀ y, HasDerivAt A' (A'' y) y)
  (hAg : HasLinearGrowth A) (hA'g : HasExpGrowth A') (hA''g : HasExpGrowth A'')
  (hA''m : Measurable A'')
include hA hA' hAg hA'g hA''g hA''m

/-- **Talagrand's (14.203)**: `B'' = 𝔼 (A''(Y) Q) + m 𝔼 (A'(Y)² Q) − m B'²`. -/
theorem hasDerivAt_integral_deriv_mul_coleHopfQ (hm : m ≠ 0) (v : ℝ≥0) (x : ℝ) :
    HasDerivAt (fun x => ∫ z, A' (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v)
      (∫ z, (A'' (x + z) + m * A' (x + z) ^ 2) * coleHopfQ m v A x z ∂gaussianReal 0 v
        - m * (∫ z, A' (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v) ^ 2) x := by
  have hA'm : Measurable A' :=
    (continuous_iff_continuousAt.2 fun y => (hA' y).continuousAt).measurable
  have hAm := measurable_of_hasDerivAt hA
  -- the numerator `N(x) = 𝔼 (A'(Y) exp (m A(Y)))` and the denominator `I(x)`
  set I : ℝ → ℝ := fun x => ∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v with hI
  set N : ℝ → ℝ := fun x => ∫ z, A' (x + z) * Real.exp (m * A (x + z)) ∂gaussianReal 0 v with hN
  have hIpos : ∀ x, 0 < I x := fun x => integral_exp_mul_comp_add_pos hAg hAm m v x
  have hfun : (fun x => ∫ z, A' (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v)
      = fun x => N x / I x := by
    funext x
    rw [hN, hI]
    simp only
    rw [← integral_div]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
      beta_reduce
      rw [coleHopfQ_eq hAg hAm hm v x z, mul_div_assoc])
  have hdI : HasDerivAt I (m * N x) x := by
    have h := hasDerivAt_integral_exp_mul hA hAg hA'g hA'm m v x
    refine h.congr_deriv ?_
    rw [hN]
    simp only
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
      beta_reduce
      ring)
  have hdN : HasDerivAt N
      (∫ z, (A'' (x + z) + m * A' (x + z) ^ 2) * Real.exp (m * A (x + z)) ∂gaussianReal 0 v) x := by
    have hF : ∀ y, HasDerivAt (fun y => A' y * Real.exp (m * A y))
        ((A'' y + m * A' y ^ 2) * Real.exp (m * A y)) y := by
      intro y
      have h1 := ((hA y).const_mul m).exp
      have := (hA' y).mul h1
      refine this.congr_deriv ?_
      ring
    exact hasDerivAt_integral_comp_add_gaussianReal hF (hA'g.mul (hAg.exp_mul m))
      ((hA''g.add ((hA'g.pow 2).const_mul m)).mul (hAg.exp_mul m))
      ((hA''m.add (measurable_const.mul (hA'm.pow_const 2))).mul
        (Real.measurable_exp.comp (measurable_const.mul hAm))) 0 v x
  rw [hfun]
  refine (hdN.div hdI (hIpos x).ne').congr_deriv ?_
  -- rewrite the two `Q`-averages as quotients
  have e1 : ∫ z, (A'' (x + z) + m * A' (x + z) ^ 2) * coleHopfQ m v A x z ∂gaussianReal 0 v
      = (∫ z, (A'' (x + z) + m * A' (x + z) ^ 2) * Real.exp (m * A (x + z)) ∂gaussianReal 0 v)
        / I x := by
    rw [← integral_div]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
      beta_reduce
      rw [coleHopfQ_eq hAg hAm hm v x z, mul_div_assoc])
  have e2 : ∫ z, A' (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v = N x / I x := by
    rw [hN]
    simp only
    rw [← integral_div]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
      beta_reduce
      rw [coleHopfQ_eq hAg hAm hm v x z, mul_div_assoc])
  rw [e1, e2]
  field_simp

end SecondDeriv

section CauchySchwarz

variable (hA : HasLinearGrowth A) (hAm : Measurable A)
include hA hAm

/-- **Cauchy–Schwarz under the tilt** (the step `B'² ≤ 𝔼 (A'(Y)² Q)` of (14.204)): for a `G` of
exponential growth, `(𝔼 (G(Y) Q))² ≤ 𝔼 (G(Y)² Q)`. -/
theorem sq_integral_mul_coleHopfQ_le (hm : m ≠ 0) {G : ℝ → ℝ} (hG : HasExpGrowth G)
    (hGm : Measurable G) (v : ℝ≥0) (x : ℝ) :
    (∫ z, G (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v) ^ 2
      ≤ ∫ z, G (x + z) ^ 2 * coleHopfQ m v A x z ∂gaussianReal 0 v := by
  set c := ∫ z, G (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v with hc
  have hQi := integrable_coleHopfQ hA hAm hm v x
  have h1 := integrable_mul_coleHopfQ hA hAm hm hG hGm v x
  have h2 := integrable_mul_coleHopfQ hA hAm hm (hG.pow 2) (hGm.pow_const 2) v x
  have hnn : 0 ≤ ∫ z, (G (x + z) - c) ^ 2 * coleHopfQ m v A x z ∂gaussianReal 0 v :=
    integral_nonneg fun z => mul_nonneg (sq_nonneg _) (coleHopfQ_pos m v A x z).le
  have hexp : ∫ z, (G (x + z) - c) ^ 2 * coleHopfQ m v A x z ∂gaussianReal 0 v
      = (∫ z, G (x + z) ^ 2 * coleHopfQ m v A x z ∂gaussianReal 0 v)
        - 2 * c * (∫ z, G (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v)
        + c ^ 2 * ∫ z, coleHopfQ m v A x z ∂gaussianReal 0 v := by
    have hi : ∀ z, (G (x + z) - c) ^ 2 * coleHopfQ m v A x z
        = G (x + z) ^ 2 * coleHopfQ m v A x z - 2 * c * (G (x + z) * coleHopfQ m v A x z)
          + c ^ 2 * coleHopfQ m v A x z := fun z => by ring
    simp_rw [hi]
    have h1' : Integrable (fun z => 2 * c * (G (x + z) * coleHopfQ m v A x z)) (gaussianReal 0 v) :=
      h1.const_mul _
    have hs : Integrable (fun z => G (x + z) ^ 2 * coleHopfQ m v A x z
        - 2 * c * (G (x + z) * coleHopfQ m v A x z)) (gaussianReal 0 v) := h2.sub h1'
    have hq : Integrable (fun z => c ^ 2 * coleHopfQ m v A x z) (gaussianReal 0 v) :=
      hQi.const_mul _
    rw [integral_add hs hq, integral_sub h2 h1', integral_const_mul, integral_const_mul]
  rw [hexp, integral_coleHopfQ hA hAm hm, ← hc] at hnn
  nlinarith [hnn]

end CauchySchwarz

/-! ### Jensen: (14.197) -/

/-- **Talagrand's (14.197)**: for `0 < m ≤ 1`, `exp B(x) ≤ 𝔼 exp A(x + g√v)`. -/
theorem coleHopf_le_log_integral_exp (hA : HasLinearGrowth A) (hAm : Measurable A) (hm : 0 < m)
    (hm1 : m ≤ 1) (v : ℝ≥0) (x : ℝ) :
    coleHopf m v A x ≤ Real.log (∫ z, Real.exp (A (x + z)) ∂gaussianReal 0 v) := by
  rw [coleHopf_of_ne hm.ne']
  have hintA : Integrable (fun z => Real.exp (A (x + z))) (gaussianReal 0 v) := by
    simpa using integrable_exp_mul_comp_add hA hAm 1 v x
  have hposA : 0 < ∫ z, Real.exp (A (x + z)) ∂gaussianReal 0 v := integral_exp_pos hintA
  have hposm := integral_exp_mul_comp_add_pos hA hAm m v x
  have hJ : ∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v
      ≤ (∫ z, Real.exp (A (x + z)) ∂gaussianReal 0 v) ^ m := by
    have h1 : (fun z => Real.exp (m * A (x + z))) = fun z => Real.exp (A (x + z)) ^ m :=
      funext fun z => by rw [mul_comm, Real.exp_mul]
    rw [h1]
    exact ConcaveOn.le_map_integral (Real.concaveOn_rpow hm.le hm1)
      (Real.continuous_rpow_const hm.le).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le) hintA
      ((integrable_exp_mul_comp_add hA hAm m v x).congr (Filter.Eventually.of_forall fun z => by
        change Real.exp (m * A (x + z)) = Real.exp (A (x + z)) ^ m
        rw [mul_comm, Real.exp_mul]))
  calc (1 / m) * Real.log (∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v)
      ≤ (1 / m) * Real.log ((∫ z, Real.exp (A (x + z)) ∂gaussianReal 0 v) ^ m) :=
        mul_le_mul_of_nonneg_left (Real.log_le_log hposm hJ) (by positivity)
    _ = Real.log (∫ z, Real.exp (A (x + z)) ∂gaussianReal 0 v) := by
        rw [Real.log_rpow hposA, ← mul_assoc, one_div_mul_cancel hm.ne', one_mul]

/-! ### The semigroup law (14.195) -/

/-- **Lemma 14.7.1**: `T_{m,a} ∘ T_{m,b} = T_{m,a+b}`. -/
theorem coleHopf_coleHopf (hA : HasLinearGrowth A) (hAm : Measurable A) (m : ℝ)
    (a b : ℝ≥0) (x : ℝ) :
    coleHopf m a (coleHopf m b A) x = coleHopf m (a + b) A x := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [coleHopf_zero]
    exact integral_integral_comp_add_gaussianReal hA.toHasExpGrowth hAm a b x
  · have hIb : ∀ y, Real.exp (m * coleHopf m b A y)
        = ∫ z, Real.exp (m * A (y + z)) ∂gaussianReal 0 b :=
      fun y => exp_mul_coleHopf hA hAm hm b y
    rw [coleHopf_of_ne hm, coleHopf_of_ne hm]
    congr 2
    simp_rw [hIb]
    exact integral_integral_comp_add_gaussianReal (hA.exp_mul m)
      (Real.measurable_exp.comp (measurable_const.mul hAm)) a b x

/-! ### The variance derivative (14.199) -/

section Var

variable (hA : ∀ y, HasDerivAt A (A' y) y) (hA' : ∀ y, HasDerivAt A' (A'' y) y)
  (hAg : HasLinearGrowth A) (hA'g : HasExpGrowth A') (hA''g : HasExpGrowth A'')
  (hA''c : Continuous A'')
include hA hA' hAg hA'g hA''g hA''c

/-- **The chain rule for `T_{m,·} A` along a curve `v ↦ (y(v), σ(v))`** in the point and the
variance: `d/dv B(y(v), σ(v)) = y'(v) 𝔼(A'(Y) Q) + (σ'(v)/2) 𝔼((A''(Y) + m A'(Y)²) Q)`, with
`Y = y(v) + g√σ(v)` and `Q` the tilt at `(y(v), σ(v))`. A corollary of the chain rule for the
Gaussian heat semigroup, `hasDerivAt_integral_comp_add_gaussianReal_curve`, applied to the
integrand `exp (m A)`. -/
theorem hasDerivAt_coleHopf_comp (hm : m ≠ 0) {y σ y' σ' : ℝ → ℝ} {v₀ : ℝ}
    (hy : ∀ᶠ v in 𝓝 v₀, HasDerivAt y (y' v) v) (hy'c : ContinuousAt y' v₀)
    (hσ : ∀ᶠ v in 𝓝 v₀, HasDerivAt σ (σ' v) v) (hσ'c : ContinuousAt σ' v₀) (hσ₀ : 0 < σ v₀) :
    HasDerivAt (fun v => coleHopf m (Real.toNNReal (σ v)) A (y v))
      (y' v₀ * ∫ z, A' (y v₀ + z) * coleHopfQ m (Real.toNNReal (σ v₀)) A (y v₀) z
          ∂gaussianReal 0 (Real.toNNReal (σ v₀))
        + σ' v₀ * ((1 / 2) * ∫ z, (A'' (y v₀ + z) + m * A' (y v₀ + z) ^ 2)
          * coleHopfQ m (Real.toNNReal (σ v₀)) A (y v₀) z
          ∂gaussianReal 0 (Real.toNNReal (σ v₀)))) v₀ := by
  have hAm : Measurable A := measurable_of_hasDerivAt hA
  have hA'm : Measurable A' := measurable_of_hasDerivAt hA'
  have hAc : Continuous A := continuous_iff_continuousAt.2 fun w => (hA w).continuousAt
  have hA'c : Continuous A' := continuous_iff_continuousAt.2 fun w => (hA' w).continuousAt
  -- the derivatives of the integrand `E = exp (m A)`
  have hEd : ∀ w, HasDerivAt (fun w => Real.exp (m * A w))
      (m * A' w * Real.exp (m * A w)) w := fun w =>
    (((hA w).const_mul m).exp).congr_deriv (by ring)
  have hE'd : ∀ w, HasDerivAt (fun w => m * A' w * Real.exp (m * A w))
      ((m * A'' w + m ^ 2 * A' w ^ 2) * Real.exp (m * A w)) w := fun w =>
    ((((hA' w).const_mul m).mul (((hA w).const_mul m).exp))).congr_deriv (by ring)
  have hEg : HasExpGrowth fun w => Real.exp (m * A w) := hAg.exp_mul m
  have hE'g : HasExpGrowth fun w => m * A' w * Real.exp (m * A w) :=
    (hA'g.const_mul m).mul hEg
  have hE''g : HasExpGrowth fun w => (m * A'' w + m ^ 2 * A' w ^ 2) * Real.exp (m * A w) :=
    ((hA''g.const_mul m).add ((hA'g.pow 2).const_mul (m ^ 2))).mul hEg
  have hE''c : Continuous fun w => (m * A'' w + m ^ 2 * A' w ^ 2) * Real.exp (m * A w) :=
    ((continuous_const.mul hA''c).add (continuous_const.mul (hA'c.pow 2))).mul
      (Real.continuous_exp.comp (continuous_const.mul hAc))
  have hmain := hasDerivAt_integral_comp_add_gaussianReal_curve hEd hE'd hEg hE'g hE''g hE''c
    hy hy'c hσ hσ'c hσ₀
  -- `B = (1/m) log 𝔼 exp (m A)`
  have hfun : (fun v => coleHopf m (Real.toNNReal (σ v)) A (y v))
      = fun v => (1 / m) * Real.log (∫ z, Real.exp (m * A (y v + z))
          ∂gaussianReal 0 (Real.toNNReal (σ v))) :=
    funext fun v => coleHopf_of_ne hm _ A _
  rw [hfun]
  have hJpos := integral_exp_mul_comp_add_pos hAg hAm m (Real.toNNReal (σ v₀)) (y v₀)
  refine ((hmain.log hJpos.ne').const_mul (1 / m)).congr_deriv ?_
  -- the two numerators carry a factor `m`, and dividing by `J` turns `exp (m A)` into `Q`
  have eN : (∫ z, m * A' (y v₀ + z) * Real.exp (m * A (y v₀ + z))
        ∂gaussianReal 0 (Real.toNNReal (σ v₀)))
      = m * ∫ z, A' (y v₀ + z) * Real.exp (m * A (y v₀ + z))
        ∂gaussianReal 0 (Real.toNNReal (σ v₀)) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by beta_reduce; ring)
  have eM : (∫ z, (m * A'' (y v₀ + z) + m ^ 2 * A' (y v₀ + z) ^ 2)
        * Real.exp (m * A (y v₀ + z)) ∂gaussianReal 0 (Real.toNNReal (σ v₀)))
      = m * ∫ z, (A'' (y v₀ + z) + m * A' (y v₀ + z) ^ 2) * Real.exp (m * A (y v₀ + z))
        ∂gaussianReal 0 (Real.toNNReal (σ v₀)) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by beta_reduce; ring)
  have eQ1 : ∫ z, A' (y v₀ + z) * coleHopfQ m (Real.toNNReal (σ v₀)) A (y v₀) z
        ∂gaussianReal 0 (Real.toNNReal (σ v₀))
      = (∫ z, A' (y v₀ + z) * Real.exp (m * A (y v₀ + z))
          ∂gaussianReal 0 (Real.toNNReal (σ v₀)))
        / ∫ z, Real.exp (m * A (y v₀ + z)) ∂gaussianReal 0 (Real.toNNReal (σ v₀)) := by
    rw [← integral_div]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
      beta_reduce
      rw [coleHopfQ_eq hAg hAm hm _ _ z, mul_div_assoc])
  have eQ2 : ∫ z, (A'' (y v₀ + z) + m * A' (y v₀ + z) ^ 2)
        * coleHopfQ m (Real.toNNReal (σ v₀)) A (y v₀) z ∂gaussianReal 0 (Real.toNNReal (σ v₀))
      = (∫ z, (A'' (y v₀ + z) + m * A' (y v₀ + z) ^ 2) * Real.exp (m * A (y v₀ + z))
          ∂gaussianReal 0 (Real.toNNReal (σ v₀)))
        / ∫ z, Real.exp (m * A (y v₀ + z)) ∂gaussianReal 0 (Real.toNNReal (σ v₀)) := by
    rw [← integral_div]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
      beta_reduce
      rw [coleHopfQ_eq hAg hAm hm _ _ z, mul_div_assoc])
  rw [eN, eM, eQ1, eQ2]
  field_simp

/-- **Talagrand's (14.199)**, in tilted form: as a function of the variance,
`∂_v B = (1/2) 𝔼 ((A''(Y) + m A'(Y)²) Q)`. -/
theorem hasDerivAt_coleHopf_var (hm : m ≠ 0) {s₀ : ℝ} (hs₀ : 0 < s₀) (x : ℝ) :
    HasDerivAt (fun s : ℝ => coleHopf m (Real.toNNReal s) A x)
      ((1 / 2) * ∫ z, (A'' (x + z) + m * A' (x + z) ^ 2)
        * coleHopfQ m (Real.toNNReal s₀) A x z ∂gaussianReal 0 (Real.toNNReal s₀)) s₀ := by
  have h := hasDerivAt_coleHopf_comp hA hA' hAg hA'g hA''g hA''c hm (y := fun _ => x)
    (σ := fun s => s) (y' := fun _ => 0) (σ' := fun _ => 1) (v₀ := s₀)
    (Filter.Eventually.of_forall fun v => hasDerivAt_const v x) continuousAt_const
    (Filter.Eventually.of_forall fun v => hasDerivAt_id v) continuousAt_const hs₀
  simpa using h

/-- **Talagrand's (14.199), the Parisi PDE at one level**: `∂_v B = B''/2 + (m/2) B'²`, with
`B' = 𝔼 (A'(Y) Q)` and `B'' = 𝔼 ((A''(Y) + m A'(Y)²) Q) − m B'²` from (14.202)–(14.203). -/
theorem hasDerivAt_coleHopf_var' (hm : m ≠ 0) {s₀ : ℝ} (hs₀ : 0 < s₀) (x : ℝ) :
    HasDerivAt (fun s : ℝ => coleHopf m (Real.toNNReal s) A x)
      ((1 / 2) * (∫ z, (A'' (x + z) + m * A' (x + z) ^ 2)
          * coleHopfQ m (Real.toNNReal s₀) A x z ∂gaussianReal 0 (Real.toNNReal s₀)
        - m * (∫ z, A' (x + z) * coleHopfQ m (Real.toNNReal s₀) A x z
          ∂gaussianReal 0 (Real.toNNReal s₀)) ^ 2)
        + (m / 2) * (∫ z, A' (x + z) * coleHopfQ m (Real.toNNReal s₀) A x z
          ∂gaussianReal 0 (Real.toNNReal s₀)) ^ 2) s₀ :=
  (hasDerivAt_coleHopf_var hA hA' hAg hA'g hA''g hA''c hm hs₀ x).congr_deriv (by ring)

end Var

/-! ### Continuity of tilted averages, Lipschitz bounds, and the second level -/

section Continuity

variable {G : ℝ → ℝ}

/-- Continuity of `x ↦ 𝔼 (G(x + g√v) exp (m A(x + g√v)))` for continuous `G`, `A` of exponential
growth (dominated convergence). -/
lemma continuous_integral_comp_add_mul_exp (hG : Continuous G) (hGg : HasExpGrowth G)
    (hAc : Continuous A) (hAg : HasLinearGrowth A) (m : ℝ) (v : ℝ≥0) :
    Continuous fun x => ∫ z, G (x + z) * Real.exp (m * A (x + z)) ∂gaussianReal 0 v := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨C, c, _, hb⟩ := (hGg.mul (hAg.exp_mul m)).bound_shift x₀ 1
  have hcont : ∀ x : ℝ, Continuous fun z => G (x + z) * Real.exp (m * A (x + z)) := fun x =>
    (hG.comp (continuous_const.add continuous_id)).mul
      (Real.continuous_exp.comp (continuous_const.mul
        (hAc.comp (continuous_const.add continuous_id))))
  refine continuousAt_of_dominated (μ := gaussianReal 0 v)
    (F := fun x z => G (x + z) * Real.exp (m * A (x + z)))
    (bound := fun z => C * Real.exp (c * |z|))
    (Filter.Eventually.of_forall fun x => (hcont x).aestronglyMeasurable) ?_
    ((integrable_exp_mul_abs_gaussianReal 0 v c).const_mul C)
    (Filter.Eventually.of_forall fun z => ((hG.comp (continuous_id.add continuous_const)).mul
      (Real.continuous_exp.comp (continuous_const.mul
        (hAc.comp (continuous_id.add continuous_const))))).continuousAt)
  filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with x hx
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs]
    exact hb x hx z

/-- **`T_{m,v}A(x)` is jointly continuous in the point and the variance** (the variance being
`max v 0`), for `A` continuous of linear growth. -/
theorem continuous_coleHopf (hAc : Continuous A) (hAg : HasLinearGrowth A) (m : ℝ) :
    Continuous fun p : ℝ × ℝ => coleHopf m (Real.toNNReal p.2) A p.1 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [coleHopf_zero]
    exact continuous_integral_comp_add_gaussianReal hAc hAg.toHasExpGrowth
  · have h1 : Continuous fun p : ℝ × ℝ =>
        ∫ z, Real.exp (m * A (p.1 + z)) ∂gaussianReal 0 (Real.toNNReal p.2) :=
      continuous_integral_comp_add_gaussianReal
        (Real.continuous_exp.comp (continuous_const.mul hAc)) (hAg.exp_mul m)
    have h2 : ∀ p : ℝ × ℝ, (∫ z, Real.exp (m * A (p.1 + z))
        ∂gaussianReal 0 (Real.toNNReal p.2)) ≠ 0 := fun p =>
      (integral_exp_mul_comp_add_pos hAg hAc.measurable m _ _).ne'
    have h3 : Continuous fun p : ℝ × ℝ => 1 / m * Real.log (∫ z, Real.exp (m * A (p.1 + z))
        ∂gaussianReal 0 (Real.toNNReal p.2)) := continuous_const.mul (h1.log h2)
    simpa only [coleHopf_of_ne hm] using h3

/-- The value at a point is continuous in the variance. -/
lemma continuous_coleHopf_var (hAc : Continuous A) (hAg : HasLinearGrowth A) (m x : ℝ) :
    Continuous fun v : ℝ => coleHopf m (Real.toNNReal v) A x :=
  (continuous_coleHopf hAc hAg m).comp (continuous_const.prodMk continuous_id)

/-- Continuity of a tilted average `x ↦ 𝔼 (G(Y) Q)` in `x`. -/
lemma continuous_integral_mul_coleHopfQ (hG : Continuous G) (hGg : HasExpGrowth G)
    (hAc : Continuous A) (hAg : HasLinearGrowth A) (hm : m ≠ 0) (v : ℝ≥0) :
    Continuous fun x => ∫ z, G (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v := by
  have hAm : Measurable A := hAc.measurable
  have h1 := continuous_integral_comp_add_mul_exp hG hGg hAc hAg m v
  have h2 := continuous_integral_comp_add_mul_exp continuous_const (HasExpGrowth.const 1) hAc hAg
    m v
  simp only [one_mul] at h2
  have hpos : ∀ x, 0 < ∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v :=
    fun x => integral_exp_mul_comp_add_pos hAg hAm m v x
  have hfun : (fun x => ∫ z, G (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v)
      = fun x => (∫ z, G (x + z) * Real.exp (m * A (x + z)) ∂gaussianReal 0 v)
        / ∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v := by
    funext x
    rw [← integral_div]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
      beta_reduce
      rw [coleHopfQ_eq hAg hAm hm v x z, mul_div_assoc])
  rw [hfun]
  exact h1.div h2 fun x => (hpos x).ne'

/-- The bound `|𝔼(G(Y) Q)| ≤ sup |G|` for every exponent (`Q = 1` when `m = 0`). -/
lemma abs_integral_mul_coleHopfQ_le' (hAg : HasLinearGrowth A) (hAm : Measurable A) (m : ℝ)
    {G : ℝ → ℝ} (hGm : Measurable G) {L : ℝ} (hL : ∀ y, |G y| ≤ L) (v : ℝ≥0) (x : ℝ) :
    |∫ z, G (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v| ≤ L := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [coleHopfQ_zero, mul_one]
    have h := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 v)
      (f := fun z => G (x + z)) (C := L)
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hL _)
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at h
  · exact abs_integral_mul_coleHopfQ_le hAg hAm hm hGm hL v x

/-- Continuity in `x` of a tilted average `𝔼(G(Y) Q)`, for every exponent. -/
lemma continuous_integral_mul_coleHopfQ' (hAc : Continuous A) (hAg : HasLinearGrowth A) (m : ℝ)
    {G : ℝ → ℝ} (hGc : Continuous G) (hGg : HasExpGrowth G) (v : ℝ≥0) :
    Continuous fun x => ∫ z, G (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v := by
  rcases eq_or_ne m 0 with rfl | hm
  · have h := (continuous_integral_comp_add_gaussianReal hGc hGg).comp
      (continuous_id.prodMk (continuous_const (y := (v : ℝ))))
    simp only [coleHopfQ_zero, mul_one]
    simpa [Function.comp_def, Real.toNNReal_coe] using h
  · exact continuous_integral_mul_coleHopfQ hGc hGg hAc hAg hm v

end Continuity

/-- **`T_{m,v}` is monotone in the function**, for every exponent `m`. -/
theorem coleHopf_mono (hAg : HasLinearGrowth A) (hAm : Measurable A) (hBg : HasLinearGrowth B)
    (hBm : Measurable B) (hAB : ∀ x, A x ≤ B x) (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    coleHopf m v A x ≤ coleHopf m v B x := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [coleHopf_zero]
    exact integral_mono
      ((hAg.toHasExpGrowth.comp_add_const x).integrable_gaussianReal
        (hAm.comp (measurable_const_add x)).aestronglyMeasurable)
      ((hBg.toHasExpGrowth.comp_add_const x).integrable_gaussianReal
        (hBm.comp (measurable_const_add x)).aestronglyMeasurable) fun z => hAB _
  · have hpA := integral_exp_mul_comp_add_pos hAg hAm m v x
    have hpB := integral_exp_mul_comp_add_pos hBg hBm m v x
    rw [coleHopf_of_ne hm, coleHopf_of_ne hm]
    rcases hm.lt_or_gt with hm' | hm'
    · -- `m < 0`: the integrals are reversed, and `1/m < 0` reverses again
      have hle : (∫ z, Real.exp (m * B (x + z)) ∂gaussianReal 0 v)
          ≤ ∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v :=
        integral_mono (integrable_exp_mul_comp_add hBg hBm m v x)
          (integrable_exp_mul_comp_add hAg hAm m v x)
          fun z => Real.exp_le_exp.2 (by nlinarith [hAB (x + z)])
      have hlog := Real.log_le_log hpB hle
      have h1 : 1 / m ≤ 0 := by
        rw [one_div]
        exact inv_nonpos.2 hm'.le
      nlinarith [hlog]
    · have hle : (∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v)
          ≤ ∫ z, Real.exp (m * B (x + z)) ∂gaussianReal 0 v :=
        integral_mono (integrable_exp_mul_comp_add hAg hAm m v x)
          (integrable_exp_mul_comp_add hBg hBm m v x)
          fun z => Real.exp_le_exp.2 (by nlinarith [hAB (x + z)])
      have hlog := Real.log_le_log hpA hle
      have h1 : 0 ≤ 1 / m := by positivity
      nlinarith [hlog]

/-- **`T_{m,v}` commutes with adding a constant**. -/
theorem coleHopf_add_const (hAg : HasLinearGrowth A) (hAm : Measurable A) (c : ℝ) (m : ℝ)
    (v : ℝ≥0) (x : ℝ) : coleHopf m v (fun y => A y + c) x = coleHopf m v A x + c := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [coleHopf_zero]
    rw [integral_add ((hAg.toHasExpGrowth.comp_add_const x).integrable_gaussianReal
      (hAm.comp (measurable_const_add x)).aestronglyMeasurable) (integrable_const c),
      integral_const, probReal_univ, one_smul]
  · have hpA := integral_exp_mul_comp_add_pos hAg hAm m v x
    have he : (∫ z, Real.exp (m * (A (x + z) + c)) ∂gaussianReal 0 v)
        = Real.exp (m * c) * ∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
        beta_reduce
        rw [← Real.exp_add]
        congr 1
        ring)
    rw [coleHopf_of_ne hm, coleHopf_of_ne hm, he,
      Real.log_mul (Real.exp_ne_zero _) hpA.ne', Real.log_exp]
    field_simp
    ring

/-- `T_{m,v}` commutes with translations of the argument. -/
theorem coleHopf_comp_const_add (A : ℝ → ℝ) (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    coleHopf m v (fun w => A (t + w)) 0 = coleHopf m v A t := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [coleHopf_zero, coleHopf_zero]
    simp only [zero_add]
  · rw [coleHopf_of_ne hm, coleHopf_of_ne hm]
    simp only [zero_add]

/-- **`T_{m,v}` preserves Lipschitz bounds**, for every exponent `m`: a consequence of
monotonicity and translation invariance alone (Talagrand's `|A_p'| ≤ 1` of (14.271)). -/
theorem abs_coleHopf_sub_le_of_lipschitz (m : ℝ) {L : ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ L * |y - x|) (v : ℝ≥0) (x y : ℝ) :
    |coleHopf m v A y - coleHopf m v A x| ≤ L * |y - x| := by
  have hAg : HasLinearGrowth A := HasLinearGrowth.of_lipschitz hA
  have hshift : ∀ t : ℝ, HasLinearGrowth (fun w => A (t + w)) := fun t => hAg.comp_add_const t
  have hshiftm : ∀ t : ℝ, Measurable fun w => A (t + w) := fun t =>
    hAm.comp (measurable_const_add t)
  have key : ∀ x y : ℝ, coleHopf m v A y ≤ coleHopf m v A x + L * |y - x| := by
    intro x y
    have h1 : ∀ w, A (y + w) ≤ A (x + w) + L * |y - x| := by
      intro w
      have h0 := hA (x + w) (y + w)
      have h2 : |y + w - (x + w)| = |y - x| := by ring_nf
      rw [h2] at h0
      linarith [le_abs_self (A (y + w) - A (x + w))]
    calc coleHopf m v A y = coleHopf m v (fun w => A (y + w)) 0 :=
          (coleHopf_comp_const_add _ _ _ _).symm
      _ ≤ coleHopf m v (fun w => A (x + w) + L * |y - x|) 0 :=
          coleHopf_mono (hshift y) (hshiftm y)
            (HasLinearGrowth.add_const (hshift x) _) ((hshiftm x).add_const _) h1 m v 0
      _ = coleHopf m v A x + L * |y - x| := by
          rw [coleHopf_add_const (hshift x) (hshiftm x), coleHopf_comp_const_add]
  refine abs_sub_le_iff.2 ⟨?_, ?_⟩
  · linarith [key x y]
  · have h3 := key y x
    rw [show |x - y| = |y - x| from abs_sub_comm _ _] at h3
    linarith

/-! ### Monotonicity, contraction and strong continuity -/

lemma hasLinearGrowth_const_mul_abs (L : ℝ) : HasLinearGrowth fun t : ℝ => L * |t| :=
  ⟨0, |L|, abs_nonneg _, fun t => by rw [abs_mul, abs_abs, zero_add]⟩

lemma measurable_const_mul_abs (L : ℝ) : Measurable fun t : ℝ => L * |t| :=
  measurable_const.mul continuous_abs.measurable

/-- **`T_{m,v}` is a contraction for the sup norm**: for every exponent `m`. -/
theorem abs_coleHopf_sub_le_of_sup (hAg : HasLinearGrowth A) (hAm : Measurable A)
    (hBg : HasLinearGrowth B) (hBm : Measurable B) {ε : ℝ} (hAB : ∀ y, |A y - B y| ≤ ε)
    (m : ℝ) (v : ℝ≥0) (x : ℝ) : |coleHopf m v A x - coleHopf m v B x| ≤ ε := by
  have key : ∀ (C D : ℝ → ℝ), HasLinearGrowth C → Measurable C → HasLinearGrowth D →
      Measurable D → (∀ y, C y ≤ D y + ε) → coleHopf m v C x ≤ coleHopf m v D x + ε := by
    intro C D hCg hCm hDg hDm hCD
    calc coleHopf m v C x ≤ coleHopf m v (fun y => D y + ε) x :=
          coleHopf_mono hCg hCm (hDg.add_const _) (hDm.add_const _) hCD m v x
      _ = coleHopf m v D x + ε := coleHopf_add_const hDg hDm _ _ _ _
  refine abs_sub_le_iff.2 ⟨?_, ?_⟩
  · have h := key A B hAg hAm hBg hBm fun y => by linarith [le_abs_self (A y - B y), hAB y]
    linarith
  · have h := key B A hBg hBm hAg hAm fun y => by
      have := neg_abs_le (A y - B y)
      linarith [hAB y]
    linarith

/-- **`T_{m,v}A` differs from `A` by at most `T_{m,v}(L|·|)(0)`**, uniformly in the point, for
`L`-Lipschitz `A`: a consequence of monotonicity and translation invariance. -/
theorem coleHopf_sub_self_le {L : ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ L * |y - x|) (m : ℝ) (v : ℝ≥0) (y : ℝ) :
    coleHopf m v A y - A y ≤ coleHopf m v (fun t => L * |t|) 0 := by
  have hAg : HasLinearGrowth A := HasLinearGrowth.of_lipschitz hA
  have h1 : ∀ t, A (y + t) ≤ L * |t| + A y := by
    intro t
    have h0 := hA y (y + t)
    have h2 : |y + t - y| = |t| := by ring_nf
    rw [h2] at h0
    linarith [le_abs_self (A (y + t) - A y)]
  have h2 : coleHopf m v A y ≤ coleHopf m v (fun t => L * |t|) 0 + A y := by
    calc coleHopf m v A y = coleHopf m v (fun t => A (y + t)) 0 :=
          (coleHopf_comp_const_add _ _ _ _).symm
      _ ≤ coleHopf m v (fun t => L * |t| + A y) 0 :=
          coleHopf_mono (hAg.comp_add_const y) (hAm.comp (measurable_const_add y))
            (HasLinearGrowth.add_const (hasLinearGrowth_const_mul_abs L) _)
            ((measurable_const_mul_abs L).add_const _) h1 m v 0
      _ = coleHopf m v (fun t => L * |t|) 0 + A y :=
          coleHopf_add_const (hasLinearGrowth_const_mul_abs L) (measurable_const_mul_abs L) _ _ _ _
  linarith

/-- The lower half of the previous bound. -/
theorem le_coleHopf_sub_self {L : ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ L * |y - x|) (m : ℝ) (v : ℝ≥0) (y : ℝ) :
    coleHopf m v (fun t => -L * |t|) 0 ≤ coleHopf m v A y - A y := by
  have hAg : HasLinearGrowth A := HasLinearGrowth.of_lipschitz hA
  have h1 : ∀ t, -L * |t| + A y ≤ A (y + t) := by
    intro t
    have h0 := hA y (y + t)
    have h2 : |y + t - y| = |t| := by ring_nf
    rw [h2] at h0
    have h3 := neg_abs_le (A (y + t) - A y)
    have h4 : -L * |t| = -(L * |t|) := by ring
    rw [h4]
    linarith
  have h2 : coleHopf m v (fun t => -L * |t| + A y) 0 ≤ coleHopf m v (fun t => A (y + t)) 0 :=
    coleHopf_mono (HasLinearGrowth.add_const (hasLinearGrowth_const_mul_abs (-L)) _)
      ((measurable_const_mul_abs (-L)).add_const _) (hAg.comp_add_const y)
      (hAm.comp (measurable_const_add y)) h1 m v 0
  rw [coleHopf_add_const (hasLinearGrowth_const_mul_abs (-L)) (measurable_const_mul_abs (-L))
    _ _ _ _, coleHopf_comp_const_add] at h2
  linarith

/-- **The modulus of continuity of `T_{m,·}` on `L`-Lipschitz functions**: the operator's own
action on `L|·|`. It vanishes as the variance does (`tendsto_coleHopfModulus`) and controls both
`T_{m,v}A − A` and `T_{m,v}A − T_{m,v'}A`, uniformly in the point. -/
noncomputable def coleHopfModulus (m L : ℝ) (v : ℝ≥0) : ℝ :=
  max (coleHopf m v (fun t => L * |t|) 0) (-coleHopf m v (fun t => -L * |t|) 0)

/-- **Two-sided form**: `T_{m,v}A` differs from `A` by at most `coleHopfModulus m L v`, uniformly
in the point. -/
theorem abs_coleHopf_sub_self_le {L : ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ L * |y - x|) (m : ℝ) (v : ℝ≥0) (y : ℝ) :
    |coleHopf m v A y - A y| ≤ coleHopfModulus m L v := by
  rw [coleHopfModulus]
  refine abs_le.2 ⟨?_, ?_⟩
  · have h := le_coleHopf_sub_self hAm hA m v y
    have h2 : -max (coleHopf m v (fun t => L * |t|) 0) (-coleHopf m v (fun t => -L * |t|) 0)
        ≤ coleHopf m v (fun t => -L * |t|) 0 := by
      rw [neg_le]
      exact le_max_right _ _
    linarith
  · exact (coleHopf_sub_self_le hAm hA m v y).trans (le_max_left _ _)

/-- **The modulus vanishes as the variance does**, so the semigroup is strongly continuous at
`v = 0` on `L`-Lipschitz functions, *uniformly* in the point. -/
theorem tendsto_coleHopfModulus (m L : ℝ) :
    Tendsto (fun v : ℝ => coleHopfModulus m L (Real.toNNReal v)) (𝓝 0) (𝓝 0) := by
  simp only [coleHopfModulus]
  have hc : ∀ c : ℝ, Continuous fun v : ℝ => coleHopf m (Real.toNNReal v) (fun t => c * |t|) 0 :=
    fun c => (continuous_coleHopf (continuous_const.mul continuous_abs)
      (hasLinearGrowth_const_mul_abs c) m).comp (continuous_const.prodMk continuous_id)
  have h0 : ∀ c : ℝ, coleHopf m (Real.toNNReal (0 : ℝ)) (fun t => c * |t|) 0 = 0 := by
    intro c
    rw [Real.toNNReal_zero, coleHopf_zero_var]
    simp
  have h1 := ((hc L).continuousAt (x := (0 : ℝ))).tendsto
  have h2 := ((hc (-L)).continuousAt (x := (0 : ℝ))).tendsto
  rw [h0 L] at h1
  rw [h0 (-L)] at h2
  have := (h1.max h2.neg)
  simpa using this

/-- **The semigroup is uniformly continuous in the variance** on `L`-Lipschitz functions: by the
semigroup property and the sup-norm contraction, the difference is controlled by the modulus at
the *increment* of the variance. -/
theorem abs_coleHopf_sub_coleHopf_le {L : ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ L * |y - x|) (m : ℝ) {v v' : ℝ≥0} (hle : v' ≤ v) (y : ℝ) :
    |coleHopf m v A y - coleHopf m v' A y| ≤ coleHopfModulus m L (v - v') := by
  have hAg : HasLinearGrowth A := HasLinearGrowth.of_lipschitz hA
  have hsplit : coleHopf m v A y = coleHopf m v' (coleHopf m (v - v') A) y := by
    rw [coleHopf_coleHopf hAg hAm m v' (v - v') y, add_tsub_cancel_of_le hle]
  rw [hsplit]
  refine abs_coleHopf_sub_le_of_sup ?_ ?_ hAg hAm ?_ m v' y
  · exact HasLinearGrowth.of_lipschitz
      (abs_coleHopf_sub_le_of_lipschitz m hAm hA (v - v'))
  · exact (lipschitzWith_toNNReal_of_abs_sub_le
      (abs_coleHopf_sub_le_of_lipschitz m hAm hA (v - v'))).continuous.measurable
  · exact fun z => abs_coleHopf_sub_self_le hAm hA m (v - v') z

/-- **Uniform continuity in the variance**, symmetric form: the increment is measured in `ℝ`. -/
theorem abs_coleHopf_sub_coleHopf_le' {L : ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ L * |y - x|) (m : ℝ) (v v' : ℝ≥0) (y : ℝ) :
    |coleHopf m v A y - coleHopf m v' A y|
      ≤ max (coleHopf m (Real.toNNReal (|(v : ℝ) - (v' : ℝ)|)) (fun t => L * |t|) 0)
        (-coleHopf m (Real.toNNReal (|(v : ℝ) - (v' : ℝ)|)) (fun t => -L * |t|) 0) := by
  have key : ∀ w w' : ℝ≥0, w' ≤ w → Real.toNNReal (|(w : ℝ) - (w' : ℝ)|) = w - w' := by
    intro w w' hle
    have h1 : (0 : ℝ) ≤ (w : ℝ) - (w' : ℝ) := by
      have : (w' : ℝ) ≤ (w : ℝ) := by exact_mod_cast hle
      linarith
    refine NNReal.coe_injective ?_
    rw [abs_of_nonneg h1, Real.coe_toNNReal _ h1, NNReal.coe_sub hle]
  rcases le_total v' v with hle | hle
  · rw [key v v' hle]
    exact abs_coleHopf_sub_coleHopf_le hAm hA m hle y
  · rw [abs_sub_comm ((v : ℝ)) ((v' : ℝ)), key v' v hle, abs_sub_comm]
    exact abs_coleHopf_sub_coleHopf_le hAm hA m hle y

section Lipschitz

variable (hA : ∀ y, HasDerivAt A (A' y) y) (hAg : HasLinearGrowth A)
  (hA'g : HasExpGrowth A') (hA'm : Measurable A')
include hA hAg hA'g hA'm

/-- **`T_{m,v} A` is Lipschitz with the constant of `A`**: `|B(y) − B(x)| ≤ L |y − x|` when
`|A'| ≤ L`. -/
lemma abs_coleHopf_sub_le (hm : m ≠ 0) {L : ℝ} (hL : ∀ y, |A' y| ≤ L) (v : ℝ≥0) (x y : ℝ) :
    |coleHopf m v A y - coleHopf m v A x| ≤ L * |y - x| := by
  have hAm := measurable_of_hasDerivAt hA
  have hd : ∀ t ∈ Set.uIcc x y, HasDerivWithinAt (coleHopf m v A)
      (∫ z, A' (t + z) * coleHopfQ m v A t z ∂gaussianReal 0 v) (Set.uIcc x y) t :=
    fun t _ => (hasDerivAt_coleHopf hA hAg hA'g hA'm hm v t).hasDerivWithinAt
  have hb : ∀ t ∈ Set.uIcc x y,
      ‖∫ z, A' (t + z) * coleHopfQ m v A t z ∂gaussianReal 0 v‖ ≤ L := fun t _ => by
    rw [Real.norm_eq_abs]
    exact abs_integral_mul_coleHopfQ_le hAg hAm hm hA'm hL v t
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_uIcc x y)
    Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [Real.norm_eq_abs] using this

end Lipschitz

section TwoLevels

/-! The second level: `C(v) = T_{m', a − v} (B(·, v))(x)` with `B(·, v) = T_{m, v} A`, Talagrand's
`C(x, v, m)` of (14.205) as a function of the split point `v`. -/

variable (hA : ∀ y, HasDerivAt A (A' y) y) (hA' : ∀ y, HasDerivAt A' (A'' y) y)
  (hA''c : Continuous A'') {L L₂ : ℝ} (hL : ∀ y, |A' y| ≤ L) (hL₂ : ∀ y, |A'' y| ≤ L₂)
include hA hA' hA''c hL hL₂

omit hA' hA''c hL₂ in
lemma hasLinearGrowth_of_bounded_deriv' : HasLinearGrowth A :=
  HasLinearGrowth.of_bounded_deriv hA hL

omit hA''c hL₂ in
/-- **`B'` is bounded by `L`**. -/
lemma abs_deriv_coleHopf_le (hm : m ≠ 0) (v : ℝ≥0) (x : ℝ) :
    |∫ z, A' (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v| ≤ L :=
  abs_integral_mul_coleHopfQ_le (HasLinearGrowth.of_bounded_deriv hA hL)
    (measurable_of_hasDerivAt hA) hm (measurable_of_hasDerivAt hA') hL v x

/-- **`𝔼((A'' + m A'²) Q)` is bounded by `L₂ + |m| L²`**. -/
lemma abs_integral_deriv2_coleHopfQ_le (hm : m ≠ 0) (v : ℝ≥0) (x : ℝ) :
    |∫ z, (A'' (x + z) + m * A' (x + z) ^ 2) * coleHopfQ m v A x z ∂gaussianReal 0 v|
      ≤ L₂ + |m| * L ^ 2 := by
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  refine abs_integral_mul_coleHopfQ_le (HasLinearGrowth.of_bounded_deriv hA hL)
    (measurable_of_hasDerivAt hA) hm
    (hA''c.measurable.add (measurable_const.mul ((measurable_of_hasDerivAt hA').pow_const 2)))
    (fun y => ?_) v x
  calc |A'' y + m * A' y ^ 2| ≤ |A'' y| + |m * A' y ^ 2| := abs_add_le _ _
    _ ≤ L₂ + |m| * L ^ 2 := by
        rw [abs_mul, abs_pow]
        have := hL y
        have := abs_nonneg (A' y)
        gcongr
        exact hL₂ y


/-- The derivative of `v ↦ B(x + g√(a − v), v)` (the inner function of (14.205)):
`−(g/(2√(a−v))) B'(Z, v) + ∂_v B(Z, v)`, `Z = x + g√(a − v)`. -/
lemma hasDerivAt_coleHopf_shift_sqrt (hm : m ≠ 0) {a v : ℝ} (hv : 0 < v) (hva : v < a) (x g : ℝ) :
    HasDerivAt (fun v => coleHopf m (Real.toNNReal v) A (x + Real.sqrt (a - v) * g))
      (-(g / (2 * Real.sqrt (a - v))) * (∫ z, A' (x + Real.sqrt (a - v) * g + z)
          * coleHopfQ m (Real.toNNReal v) A (x + Real.sqrt (a - v) * g) z
          ∂gaussianReal 0 (Real.toNNReal v))
        + 1 * ((1 / 2) * ∫ z, (A'' (x + Real.sqrt (a - v) * g + z)
          + m * A' (x + Real.sqrt (a - v) * g + z) ^ 2)
          * coleHopfQ m (Real.toNNReal v) A (x + Real.sqrt (a - v) * g) z
          ∂gaussianReal 0 (Real.toNNReal v))) v := by
  have hAg : HasLinearGrowth A := HasLinearGrowth.of_bounded_deriv hA hL
  have hA'g : HasExpGrowth A' := HasExpGrowth.of_bounded hL
  have hA''g : HasExpGrowth A'' := HasExpGrowth.of_bounded hL₂
  have hy : ∀ᶠ v' in 𝓝 v, HasDerivAt (fun v => x + Real.sqrt (a - v) * g)
      (-(g / (2 * Real.sqrt (a - v'))) ) v' := by
    filter_upwards [Iio_mem_nhds hva] with v' hv'
    have hv'' : v' < a := hv'
    have h1 : HasDerivAt (fun v => a - v) (-1) v' := (hasDerivAt_id v').const_sub a
    have h2 : HasDerivAt (fun v => Real.sqrt (a - v)) (1 / (2 * Real.sqrt (a - v')) * -1) v' :=
      (Real.hasDerivAt_sqrt (sub_pos.2 hv'').ne').comp v' h1
    have h3 := (h2.mul_const g).const_add x
    exact h3.congr_deriv (by ring)
  have hy'c : ContinuousAt (fun v => -(g / (2 * Real.sqrt (a - v)))) v := by
    have hsq : ContinuousAt (fun v => Real.sqrt (a - v)) v :=
      (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).continuousAt
    have hne : 2 * Real.sqrt (a - v) ≠ 0 := by
      have := Real.sqrt_pos.2 (by linarith : 0 < a - v)
      positivity
    exact ((continuousAt_const.div (continuousAt_const.mul hsq) hne)).neg
  have h := hasDerivAt_coleHopf_comp hA hA' hAg hA'g hA''g hA''c hm
    (y := fun v => x + Real.sqrt (a - v) * g) (σ := fun v => v)
    (y' := fun v => -(g / (2 * Real.sqrt (a - v)))) (σ' := fun _ => 1) (v₀ := v)
    hy hy'c (Filter.Eventually.of_forall fun v => hasDerivAt_id v) continuousAt_const hv
  exact h

/-- **Lemma 14.7.3, (14.207)** for `m' ≠ 0`: with `B(·, v) = T_{m,v} A` and
`C(v) = T_{m', a−v}(B(·, v))(x)`, `∂_v C = ((m − m')/2) 𝔼(B'(Z, v)² R)`, `Z = x + g√(a − v)`,
`R = exp m'(B(Z, v) − C(v))`. -/
theorem hasDerivAt_coleHopf_coleHopf_var_of_ne {m' a : ℝ} (hm : m ≠ 0) (hm' : m' ≠ 0) {v₀ : ℝ}
    (hv₀ : 0 < v₀) (hva : v₀ < a) (x : ℝ) :
    HasDerivAt (fun v : ℝ => coleHopf m' (Real.toNNReal (a - v)) (coleHopf m (Real.toNNReal v) A) x)
      (((m - m') / 2) * ∫ z, (∫ w, A' (x + z + w)
            * coleHopfQ m (Real.toNNReal v₀) A (x + z) w ∂gaussianReal 0 (Real.toNNReal v₀)) ^ 2
          * coleHopfQ m' (Real.toNNReal (a - v₀)) (coleHopf m (Real.toNNReal v₀) A) x z
          ∂gaussianReal 0 (Real.toNNReal (a - v₀))) v₀ := by
  have hAg : HasLinearGrowth A := HasLinearGrowth.of_bounded_deriv hA hL
  have hA'g : HasExpGrowth A' := HasExpGrowth.of_bounded hL
  have hA''g : HasExpGrowth A'' := HasExpGrowth.of_bounded hL₂
  have hAm := measurable_of_hasDerivAt hA
  have hA'm := measurable_of_hasDerivAt hA'
  have hAc : Continuous A := continuous_iff_continuousAt.2 fun y => (hA y).continuousAt
  have hA'c : Continuous A' := continuous_iff_continuousAt.2 fun y => (hA' y).continuousAt
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  have hL₂0 : 0 ≤ L₂ := (abs_nonneg _).trans (hL₂ 0)
  -- the objects at a fixed variance `v`
  set B : ℝ → ℝ → ℝ := fun v y => coleHopf m (Real.toNNReal v) A y with hBdef
  set B1 : ℝ → ℝ → ℝ := fun v y => ∫ w, A' (y + w) * coleHopfQ m (Real.toNNReal v) A y w
    ∂gaussianReal 0 (Real.toNNReal v) with hB1def
  set B2 : ℝ → ℝ → ℝ := fun v y => ∫ w, (A'' (y + w) + m * A' (y + w) ^ 2)
    * coleHopfQ m (Real.toNNReal v) A y w ∂gaussianReal 0 (Real.toNNReal v) with hB2def
  have hB1 : ∀ v y, HasDerivAt (B v) (B1 v y) y := fun v y =>
    hasDerivAt_coleHopf hA hAg hA'g hA'm hm (Real.toNNReal v) y
  have hB1' : ∀ v y, HasDerivAt (B1 v) (B2 v y - m * B1 v y ^ 2) y := fun v y =>
    hasDerivAt_integral_deriv_mul_coleHopfQ hA hA' hAg hA'g hA''g hA''c.measurable hm
      (Real.toNNReal v) y
  have hB1b : ∀ v y, |B1 v y| ≤ L := fun v y =>
    abs_deriv_coleHopf_le hA hA' hL hm (Real.toNNReal v) y
  have hB2b : ∀ v y, |B2 v y| ≤ L₂ + |m| * L ^ 2 := fun v y =>
    abs_integral_deriv2_coleHopfQ_le hA hA' hA''c hL hL₂ hm (Real.toNNReal v) y
  have hB1c : ∀ v, Continuous (B1 v) := fun v =>
    continuous_integral_mul_coleHopfQ hA'c hA'g hAc hAg hm (Real.toNNReal v)
  have hB2c : ∀ v, Continuous (B2 v) := fun v =>
    continuous_integral_mul_coleHopfQ (hA''c.add (continuous_const.mul (hA'c.pow 2)))
      (hA''g.add ((hA'g.pow 2).const_mul m)) hAc hAg hm (Real.toNNReal v)
  have hBc : ∀ v, Continuous (B v) := fun v =>
    continuous_iff_continuousAt.2 fun y => (hB1 v y).continuousAt
  have hBlip : ∀ v y, |B v y - B v x| ≤ L * |y - x| := fun v y =>
    abs_coleHopf_sub_le hA hAg hA'g hA'm hm hL (Real.toNNReal v) x y
  have hBvc : ContinuousAt (fun v => B v x) v₀ :=
    (hasDerivAt_coleHopf_var hA hA' hAg hA'g hA''g hA''c hm hv₀ x).continuousAt
  -- the exponential of `m' C(v)` as a standard Gaussian integral
  set Z : ℝ → ℝ → ℝ := fun v g => x + Real.sqrt (a - v) * g with hZdef
  set W : ℝ → ℝ := fun v => ∫ g, Real.exp (m' * B v (Z v g)) ∂gaussianReal 0 1 with hWdef
  have hBlg : ∀ v, HasLinearGrowth (B v) := fun v =>
    HasLinearGrowth.of_bounded_deriv (hB1 v) (hB1b v)
  have hWeq : ∀ v, v < a → W v = ∫ z, Real.exp (m' * B v (x + z))
      ∂gaussianReal 0 (Real.toNNReal (a - v)) := by
    intro v hv
    have hmeas : AEStronglyMeasurable (fun z => Real.exp (m' * B v (x + z)))
        (gaussianReal 0 (Real.toNNReal (a - v))) :=
      (Real.measurable_exp.comp (measurable_const.mul ((hBc v).measurable.comp
        (measurable_const.add measurable_id)))).aestronglyMeasurable
    rw [hWdef]
    simp only
    rw [integral_gaussianReal_eq_integral_sqrt_mul (Real.toNNReal (a - v)) hmeas,
      Real.coe_toNNReal (a - v) (by linarith)]
  have hfun : ∀ᶠ v in 𝓝 v₀, coleHopf m' (Real.toNNReal (a - v)) (B v) x
      = (1 / m') * Real.log (W v) := by
    filter_upwards [Iio_mem_nhds hva] with v hv
    rw [coleHopf_of_ne hm', hWeq v hv]
  have hWpos : 0 < W v₀ := by
    rw [hWeq v₀ hva]
    exact integral_exp_mul_comp_add_pos (hBlg v₀) (hBc v₀).measurable m' _ x
  -- the good neighbourhood and the uniform bound
  set r : ℝ := Real.sqrt a with hr
  set k : ℝ := 1 / (2 * Real.sqrt ((a - v₀) / 2)) with hk
  have hk0 : 0 ≤ k := by positivity
  set K₂ : ℝ := (L₂ + |m| * L ^ 2) / 2 with hK₂
  have hK₂0 : 0 ≤ K₂ := by positivity
  set c : ℝ := |m'| * L * r + 1 with hc
  have hc0 : 0 ≤ c := by positivity
  set K : ℝ := |m'| * (k * L + K₂) * Real.exp (|m'| * (|B v₀ x| + 1)) with hK
  have hs : ∀ᶠ v in 𝓝 v₀, (0 < v ∧ v < a) ∧ (v₀ / 2 < v ∧ v < (v₀ + a) / 2)
      ∧ |B v x - B v₀ x| < 1 := by
    have h1 : ∀ᶠ v in 𝓝 v₀, 0 < v ∧ v < a := Ioo_mem_nhds hv₀ hva
    have h2 : ∀ᶠ v in 𝓝 v₀, v₀ / 2 < v ∧ v < (v₀ + a) / 2 :=
      Ioo_mem_nhds (by linarith) (by linarith)
    have h3 : ∀ᶠ v in 𝓝 v₀, |B v x - B v₀ x| < 1 := by
      have := hBvc.eventually (Metric.ball_mem_nhds (B v₀ x) one_pos)
      filter_upwards [this] with v hv
      simpa [Real.dist_eq] using hv
    filter_upwards [h1, h2, h3] with v a b c
    exact ⟨a, b, c⟩
  obtain ⟨t, ht, hts⟩ := hs.exists_mem
  -- the derivative of `W`
  set D : ℝ → ℝ → ℝ := fun v g => -(g / (2 * Real.sqrt (a - v))) * B1 v (Z v g)
    + 1 * ((1 / 2) * B2 v (Z v g)) with hDdef
  have hmeasF : ∀ v, AEStronglyMeasurable (fun g => Real.exp (m' * B v (Z v g)))
      (gaussianReal 0 1) := fun v =>
    (Real.continuous_exp.comp (continuous_const.mul ((hBc v).comp
      (continuous_const.add (continuous_const.mul continuous_id))))).aestronglyMeasurable
  have hdW : HasDerivAt W (∫ g, m' * D v₀ g * Real.exp (m' * B v₀ (Z v₀ g)) ∂gaussianReal 0 1)
      v₀ := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gaussianReal 0 1)
      (F := fun v g => Real.exp (m' * B v (Z v g)))
      (F' := fun v g => m' * D v g * Real.exp (m' * B v (Z v g)))
      (bound := fun g => K * Real.exp (c * |g|)) ht
      (Filter.Eventually.of_forall hmeasF) ?_ ?_ ?_ ?_ ?_).2
    · -- integrability at `v₀`
      have hg : HasExpGrowth fun g => Real.exp (m' * B v₀ (Z v₀ g)) := by
        refine ⟨Real.exp (|m'| * (|B v₀ x| + L * Real.sqrt (a - v₀) * 0)) * 1,
          |m'| * L * Real.sqrt (a - v₀), by positivity, fun g => ?_⟩
        rw [abs_of_pos (Real.exp_pos _), mul_one, ← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have h1 : |B v₀ (Z v₀ g)| ≤ |B v₀ x| + L * (Real.sqrt (a - v₀) * |g|) := by
          have := hBlip v₀ (Z v₀ g)
          rw [hZdef] at this ⊢
          simp only at this ⊢
          rw [show x + Real.sqrt (a - v₀) * g - x = Real.sqrt (a - v₀) * g by ring, abs_mul,
            abs_of_nonneg (Real.sqrt_nonneg _)] at this
          linarith [abs_sub_abs_le_abs_sub (B v₀ (x + Real.sqrt (a - v₀) * g)) (B v₀ x)]
        calc m' * B v₀ (Z v₀ g) ≤ |m'| * |B v₀ (Z v₀ g)| := by
              rw [← abs_mul]; exact le_abs_self _
          _ ≤ |m'| * (|B v₀ x| + L * (Real.sqrt (a - v₀) * |g|)) :=
              mul_le_mul_of_nonneg_left h1 (abs_nonneg m')
          _ = |m'| * (|B v₀ x| + L * Real.sqrt (a - v₀) * 0)
              + |m'| * L * Real.sqrt (a - v₀) * |g| := by ring
      exact hg.integrable_gaussianReal (hmeasF v₀)
    · have hc1 := hB1c v₀
      have hc2 := hB2c v₀
      have hc0 := hBc v₀
      have : Continuous fun g => m' * D v₀ g * Real.exp (m' * B v₀ (Z v₀ g)) := by
        simp only [hDdef, hZdef]
        fun_prop
      exact this.aestronglyMeasurable
    · -- the uniform bound
      refine Filter.Eventually.of_forall fun g v hv => ?_
      obtain ⟨⟨hv0, hva'⟩, ⟨hs1, hs2⟩, hB⟩ := hts v hv
      have hav : (a - v₀) / 2 < a - v := by linarith
      have hsq_le : Real.sqrt (a - v) ≤ r := Real.sqrt_le_sqrt (by linarith)
      have hinv_le : 1 / (2 * Real.sqrt (a - v)) ≤ k := by
        rw [hk]
        refine one_div_le_one_div_of_le (by positivity) ?_
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hav.le) two_pos.le
      have hg_le : |g| ≤ Real.exp |g| := by linarith [Real.add_one_le_exp |g|]
      have hBx : |B v x| ≤ |B v₀ x| + 1 := by
        linarith [abs_sub_abs_le_abs_sub (B v x) (B v₀ x)]
      have hBZ : |B v (Z v g)| ≤ |B v₀ x| + 1 + L * (r * |g|) := by
        have := hBlip v (Z v g)
        rw [hZdef] at this ⊢
        simp only at this ⊢
        rw [show x + Real.sqrt (a - v) * g - x = Real.sqrt (a - v) * g by ring, abs_mul,
          abs_of_nonneg (Real.sqrt_nonneg _)] at this
        have h2 : Real.sqrt (a - v) * |g| ≤ r * |g| :=
          mul_le_mul_of_nonneg_right hsq_le (abs_nonneg g)
        nlinarith [abs_sub_abs_le_abs_sub (B v (x + Real.sqrt (a - v) * g)) (B v x), hL0]
      have hexp : Real.exp (m' * B v (Z v g))
          ≤ Real.exp (|m'| * (|B v₀ x| + 1)) * Real.exp (|m'| * L * r * |g|) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        calc m' * B v (Z v g) ≤ |m'| * |B v (Z v g)| := by
              rw [← abs_mul]; exact le_abs_self _
          _ ≤ |m'| * (|B v₀ x| + 1 + L * (r * |g|)) :=
              mul_le_mul_of_nonneg_left hBZ (abs_nonneg m')
          _ = |m'| * (|B v₀ x| + 1) + |m'| * L * r * |g| := by ring
      have hD : |D v g| ≤ (k * L + K₂) * Real.exp |g| := by
        rw [hDdef]
        simp only
        calc |-(g / (2 * Real.sqrt (a - v))) * B1 v (Z v g) + 1 * (1 / 2 * B2 v (Z v g))|
            ≤ |-(g / (2 * Real.sqrt (a - v))) * B1 v (Z v g)| + |1 * (1 / 2 * B2 v (Z v g))| :=
              abs_add_le _ _
          _ ≤ k * L * |g| + K₂ := by
              rw [abs_mul, abs_neg, abs_div, abs_of_pos (by positivity :
                (0 : ℝ) < 2 * Real.sqrt (a - v)), abs_mul, abs_one, one_mul, abs_mul,
                abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
              have e1 : |g| / (2 * Real.sqrt (a - v)) * |B1 v (Z v g)| ≤ k * L * |g| := by
                calc |g| / (2 * Real.sqrt (a - v)) * |B1 v (Z v g)|
                    = (1 / (2 * Real.sqrt (a - v))) * |B1 v (Z v g)| * |g| := by ring
                  _ ≤ k * L * |g| := by gcongr; exact hB1b v _
              have e2 : 1 / 2 * |B2 v (Z v g)| ≤ K₂ := by
                rw [hK₂]
                linarith [hB2b v (Z v g)]
              linarith
          _ ≤ (k * L + K₂) * Real.exp |g| := by
              have h1 : 1 ≤ Real.exp |g| := Real.one_le_exp (abs_nonneg g)
              nlinarith [mul_nonneg (mul_nonneg hk0 hL0) (sub_nonneg.2 hg_le),
                mul_nonneg hK₂0 (sub_nonneg.2 h1)]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc |m'| * |D v g| * Real.exp (m' * B v (Z v g))
          ≤ |m'| * ((k * L + K₂) * Real.exp |g|)
            * (Real.exp (|m'| * (|B v₀ x| + 1)) * Real.exp (|m'| * L * r * |g|)) := by
            gcongr
        _ = K * Real.exp (c * |g|) := by
            rw [hK, hc, show (|m'| * L * r + 1) * |g| = |m'| * L * r * |g| + |g| by ring,
              Real.exp_add]
            ring
    · exact (integrable_exp_mul_abs_gaussianReal 0 1 c).const_mul K
    · -- differentiability of the inner function along the curve
      refine Filter.Eventually.of_forall fun g v hv => ?_
      obtain ⟨⟨hv0, hva'⟩, _, _⟩ := hts v hv
      have h := hasDerivAt_coleHopf_shift_sqrt hA hA' hA''c hL hL₂ hm hv0 hva' x g
      have h2 := (h.const_mul m').exp
      refine h2.congr_deriv ?_
      rw [hDdef, hB1def, hB2def, hZdef]
      simp only
      ring
  -- Stein's lemma on the `g`-term
  set Z₀ : ℝ → ℝ := fun g => x + Real.sqrt (a - v₀) * g with hZ₀
  have hsq0 : 0 < Real.sqrt (a - v₀) := Real.sqrt_pos.2 (by linarith)
  have hΦ : ∀ g, HasDerivAt (fun g => B1 v₀ (Z₀ g) * Real.exp (m' * B v₀ (Z₀ g)))
      (Real.sqrt (a - v₀) * ((B2 v₀ (Z₀ g) - m * B1 v₀ (Z₀ g) ^ 2 + m' * B1 v₀ (Z₀ g) ^ 2)
        * Real.exp (m' * B v₀ (Z₀ g)))) g := by
    intro g
    have h1 : HasDerivAt Z₀ (Real.sqrt (a - v₀)) g := by
      have := ((hasDerivAt_id g).const_mul (Real.sqrt (a - v₀))).const_add x
      simpa [hZ₀] using this
    have h2 : HasDerivAt (fun g => B1 v₀ (Z₀ g))
        ((B2 v₀ (Z₀ g) - m * B1 v₀ (Z₀ g) ^ 2) * Real.sqrt (a - v₀)) g :=
      (hB1' v₀ _).comp g h1
    have h3 : HasDerivAt (fun g => Real.exp (m' * B v₀ (Z₀ g)))
        (Real.exp (m' * B v₀ (Z₀ g)) * (m' * (B1 v₀ (Z₀ g) * Real.sqrt (a - v₀)))) g :=
      (((hB1 v₀ _).comp g h1).const_mul m').exp
    exact (h2.mul h3).congr_deriv (by ring)
  have hEg : HasExpGrowth fun g => Real.exp (m' * B v₀ (Z₀ g)) := by
    have h := (((hBlg v₀).exp_mul m').comp_add_const x).comp_const_mul (Real.sqrt (a - v₀))
    exact h
  have hΦg : HasExpGrowth fun g => B1 v₀ (Z₀ g) * Real.exp (m' * B v₀ (Z₀ g)) :=
    (HasExpGrowth.of_bounded fun g => hB1b v₀ (Z₀ g)).mul hEg
  have hΦ'g : HasExpGrowth fun g => Real.sqrt (a - v₀)
      * ((B2 v₀ (Z₀ g) - m * B1 v₀ (Z₀ g) ^ 2 + m' * B1 v₀ (Z₀ g) ^ 2)
        * Real.exp (m' * B v₀ (Z₀ g))) := by
    have hb : HasExpGrowth fun g => B2 v₀ (Z₀ g) - m * B1 v₀ (Z₀ g) ^ 2
        + m' * B1 v₀ (Z₀ g) ^ 2 :=
      HasExpGrowth.of_bounded fun g => by
        calc |B2 v₀ (Z₀ g) - m * B1 v₀ (Z₀ g) ^ 2 + m' * B1 v₀ (Z₀ g) ^ 2|
            ≤ |B2 v₀ (Z₀ g)| + |m| * L ^ 2 + |m'| * L ^ 2 := by
              have h1 := hB1b v₀ (Z₀ g)
              have h2 : |B1 v₀ (Z₀ g) ^ 2| ≤ L ^ 2 := by
                rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
              calc |B2 v₀ (Z₀ g) - m * B1 v₀ (Z₀ g) ^ 2 + m' * B1 v₀ (Z₀ g) ^ 2|
                  ≤ |B2 v₀ (Z₀ g) - m * B1 v₀ (Z₀ g) ^ 2| + |m' * B1 v₀ (Z₀ g) ^ 2| :=
                    abs_add_le _ _
                _ ≤ |B2 v₀ (Z₀ g)| + |m * B1 v₀ (Z₀ g) ^ 2| + |m' * B1 v₀ (Z₀ g) ^ 2| := by
                    linarith [abs_sub (B2 v₀ (Z₀ g)) (m * B1 v₀ (Z₀ g) ^ 2)]
                _ ≤ |B2 v₀ (Z₀ g)| + |m| * L ^ 2 + |m'| * L ^ 2 := by
                    rw [abs_mul, abs_mul]
                    gcongr
          _ ≤ (L₂ + |m| * L ^ 2) + |m| * L ^ 2 + |m'| * L ^ 2 := by
              linarith [hB2b v₀ (Z₀ g)]
    exact (hb.mul hEg).const_mul _
  have hΦ'c : Continuous fun g => Real.sqrt (a - v₀)
      * ((B2 v₀ (Z₀ g) - m * B1 v₀ (Z₀ g) ^ 2 + m' * B1 v₀ (Z₀ g) ^ 2)
        * Real.exp (m' * B v₀ (Z₀ g))) := by
    have hZc : Continuous Z₀ := continuous_const.add (continuous_const.mul continuous_id)
    have hc1 := hB1c v₀
    have hc2 := hB2c v₀
    have hc0 := hBc v₀
    fun_prop
  have hstein := stein_lemma_gaussianReal_of_expGrowth' (v := 1) hΦ hΦ'c hΦg hΦ'g
  simp only [NNReal.coe_one, one_mul] at hstein
  -- assemble
  have hd := ((hdW.log hWpos.ne').const_mul (1 / m')).congr_of_eventuallyEq hfun
  refine hd.congr_deriv ?_
  -- integrability of the pieces
  have hZc : Continuous Z₀ := continuous_const.add (continuous_const.mul continuous_id)
  have hi1 : Integrable (fun g => g * (B1 v₀ (Z₀ g) * Real.exp (m' * B v₀ (Z₀ g))))
      (gaussianReal 0 1) := by
    have hg : HasExpGrowth fun g : ℝ => g :=
      ⟨1, 1, zero_le_one, fun g => by
        rw [one_mul, one_mul]
        linarith [Real.add_one_le_exp |g|]⟩
    exact (hg.mul hΦg).integrable_gaussianReal (measurable_id.mul
      (((hB1c v₀).comp hZc).mul (Real.continuous_exp.comp
        (continuous_const.mul ((hBc v₀).comp hZc)))).measurable).aestronglyMeasurable
  have hi2 : Integrable (fun g => B2 v₀ (Z₀ g) * Real.exp (m' * B v₀ (Z₀ g))) (gaussianReal 0 1) :=
    ((HasExpGrowth.of_bounded fun g => hB2b v₀ (Z₀ g)).mul hEg).integrable_gaussianReal
      (((hB2c v₀).comp hZc).mul (Real.continuous_exp.comp
        (continuous_const.mul ((hBc v₀).comp hZc)))).measurable.aestronglyMeasurable
  have hi3 : Integrable (fun g => B1 v₀ (Z₀ g) ^ 2 * Real.exp (m' * B v₀ (Z₀ g)))
      (gaussianReal 0 1) :=
    ((HasExpGrowth.of_bounded fun g => hB1b v₀ (Z₀ g)).pow 2 |>.mul hEg).integrable_gaussianReal
      ((((hB1c v₀).comp hZc).pow 2).mul (Real.continuous_exp.comp
        (continuous_const.mul ((hBc v₀).comp hZc)))).measurable.aestronglyMeasurable
  -- `W'(v₀)` split into the `g`-term and the `∂_v` term
  have e1 : (∫ g, m' * D v₀ g * Real.exp (m' * B v₀ (Z v₀ g)) ∂gaussianReal 0 1)
      = (-(m' / (2 * Real.sqrt (a - v₀)))) * (∫ g, g * (B1 v₀ (Z₀ g)
          * Real.exp (m' * B v₀ (Z₀ g))) ∂gaussianReal 0 1)
        + (m' / 2) * ∫ g, B2 v₀ (Z₀ g) * Real.exp (m' * B v₀ (Z₀ g)) ∂gaussianReal 0 1 := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hi1.const_mul _)
      (hi2.const_mul _)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun g => by
      rw [hDdef, hZdef, hZ₀]
      beta_reduce
      ring)
  have e2 : (∫ g, Real.sqrt (a - v₀) * ((B2 v₀ (Z₀ g) - m * B1 v₀ (Z₀ g) ^ 2
      + m' * B1 v₀ (Z₀ g) ^ 2) * Real.exp (m' * B v₀ (Z₀ g))) ∂gaussianReal 0 1)
      = Real.sqrt (a - v₀) * ((∫ g, B2 v₀ (Z₀ g) * Real.exp (m' * B v₀ (Z₀ g)) ∂gaussianReal 0 1)
        + (m' - m) * ∫ g, B1 v₀ (Z₀ g) ^ 2 * Real.exp (m' * B v₀ (Z₀ g)) ∂gaussianReal 0 1) := by
    rw [integral_const_mul]
    congr 1
    rw [← integral_const_mul, ← integral_add hi2 (hi3.const_mul _)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun g => by
      beta_reduce
      ring)
  -- scale back to the variance `a − v₀`
  have hav0 : (Real.toNNReal (a - v₀) : ℝ) = a - v₀ := Real.coe_toNNReal _ (by linarith)
  have e3 : (∫ g, B1 v₀ (Z₀ g) ^ 2 * Real.exp (m' * B v₀ (Z₀ g)) ∂gaussianReal 0 1)
      = ∫ z, B1 v₀ (x + z) ^ 2 * Real.exp (m' * B v₀ (x + z))
          ∂gaussianReal 0 (Real.toNNReal (a - v₀)) := by
    have hmeas3 : AEStronglyMeasurable (fun z => B1 v₀ (x + z) ^ 2 * Real.exp (m' * B v₀ (x + z)))
        (gaussianReal 0 (Real.toNNReal (a - v₀))) :=
      ((((hB1c v₀).comp (continuous_const.add continuous_id)).pow 2).mul
        (Real.continuous_exp.comp (continuous_const.mul ((hBc v₀).comp
          (continuous_const.add continuous_id))))).measurable.aestronglyMeasurable
    rw [integral_gaussianReal_eq_integral_sqrt_mul (Real.toNNReal (a - v₀)) hmeas3, hav0]
  have e4 : ∫ z, B1 v₀ (x + z) ^ 2 * coleHopfQ m' (Real.toNNReal (a - v₀)) (B v₀) x z
      ∂gaussianReal 0 (Real.toNNReal (a - v₀))
      = (∫ z, B1 v₀ (x + z) ^ 2 * Real.exp (m' * B v₀ (x + z))
          ∂gaussianReal 0 (Real.toNNReal (a - v₀))) / W v₀ := by
    rw [hWeq v₀ hva, ← integral_div]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
      beta_reduce
      rw [coleHopfQ_eq (hBlg v₀) (hBc v₀).measurable hm' (Real.toNNReal (a - v₀)) x z,
        mul_div_assoc])
  change (1 / m') * ((∫ g, m' * D v₀ g * Real.exp (m' * B v₀ (Z v₀ g)) ∂gaussianReal 0 1) / W v₀)
    = ((m - m') / 2) * ∫ z, B1 v₀ (x + z) ^ 2
        * coleHopfQ m' (Real.toNNReal (a - v₀)) (B v₀) x z ∂gaussianReal 0 (Real.toNNReal (a - v₀))
  rw [e1, hstein, e2, e4, ← e3]
  field_simp
  ring

/-- **Lemma 14.7.3 for `m' = 0`**: the outer operator is the plain Gaussian average, the tilt `R`
is `1`, and `∂_v C = (m/2) 𝔼(B'(Z, v)²)`. -/
theorem hasDerivAt_coleHopf_coleHopf_var_zero {a : ℝ} (hm : m ≠ 0) {v₀ : ℝ}
    (hv₀ : 0 < v₀) (hva : v₀ < a) (x : ℝ) :
    HasDerivAt (fun v : ℝ => coleHopf 0 (Real.toNNReal (a - v)) (coleHopf m (Real.toNNReal v) A) x)
      ((m / 2) * ∫ z, (∫ w, A' (x + z + w)
            * coleHopfQ m (Real.toNNReal v₀) A (x + z) w ∂gaussianReal 0 (Real.toNNReal v₀)) ^ 2
          ∂gaussianReal 0 (Real.toNNReal (a - v₀))) v₀ := by
  have hAg : HasLinearGrowth A := HasLinearGrowth.of_bounded_deriv hA hL
  have hA'g : HasExpGrowth A' := HasExpGrowth.of_bounded hL
  have hA''g : HasExpGrowth A'' := HasExpGrowth.of_bounded hL₂
  have hAm := measurable_of_hasDerivAt hA
  have hA'm := measurable_of_hasDerivAt hA'
  have hAc : Continuous A := continuous_iff_continuousAt.2 fun y => (hA y).continuousAt
  have hA'c : Continuous A' := continuous_iff_continuousAt.2 fun y => (hA' y).continuousAt
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  have hL₂0 : 0 ≤ L₂ := (abs_nonneg _).trans (hL₂ 0)
  have ha₀ : 0 < a - v₀ := by linarith
  -- the objects at a fixed variance `v`
  set B : ℝ → ℝ → ℝ := fun v y => coleHopf m (Real.toNNReal v) A y with hBdef
  set B1 : ℝ → ℝ → ℝ := fun v y => ∫ w, A' (y + w) * coleHopfQ m (Real.toNNReal v) A y w
    ∂gaussianReal 0 (Real.toNNReal v) with hB1def
  set B2 : ℝ → ℝ → ℝ := fun v y => ∫ w, (A'' (y + w) + m * A' (y + w) ^ 2)
    * coleHopfQ m (Real.toNNReal v) A y w ∂gaussianReal 0 (Real.toNNReal v) with hB2def
  have hB1 : ∀ v y, HasDerivAt (B v) (B1 v y) y := fun v y =>
    hasDerivAt_coleHopf hA hAg hA'g hA'm hm (Real.toNNReal v) y
  have hB1' : ∀ v y, HasDerivAt (B1 v) (B2 v y - m * B1 v y ^ 2) y := fun v y =>
    hasDerivAt_integral_deriv_mul_coleHopfQ hA hA' hAg hA'g hA''g hA''c.measurable hm
      (Real.toNNReal v) y
  have hB1b : ∀ v y, |B1 v y| ≤ L := fun v y =>
    abs_deriv_coleHopf_le hA hA' hL hm (Real.toNNReal v) y
  have hB2b : ∀ v y, |B2 v y| ≤ L₂ + |m| * L ^ 2 := fun v y =>
    abs_integral_deriv2_coleHopfQ_le hA hA' hA''c hL hL₂ hm (Real.toNNReal v) y
  have hB1c : ∀ v, Continuous (B1 v) := fun v =>
    continuous_integral_mul_coleHopfQ hA'c hA'g hAc hAg hm (Real.toNNReal v)
  have hB2c : ∀ v, Continuous (B2 v) := fun v =>
    continuous_integral_mul_coleHopfQ (hA''c.add (continuous_const.mul (hA'c.pow 2)))
      (hA''g.add ((hA'g.pow 2).const_mul m)) hAc hAg hm (Real.toNNReal v)
  have hBc : ∀ v, Continuous (B v) := fun v =>
    continuous_iff_continuousAt.2 fun y => (hB1 v y).continuousAt
  have hBlg : ∀ v, HasLinearGrowth (B v) := fun v =>
    HasLinearGrowth.of_bounded_deriv (hB1 v) (hB1b v)
  -- the chain rule for the inner function, in the form the master lemma expects
  have hΦ : ∀ᶠ v in 𝓝 v₀, ∀ g, HasDerivAt (fun v => B v (x + Real.sqrt (a - v) * g))
      (B1 v (x + Real.sqrt (a - v) * g) * (0 + (-1) / (2 * Real.sqrt (a - v)) * g)
        + (1 / 2) * B2 v (x + Real.sqrt (a - v) * g)) v := by
    filter_upwards [Ioo_mem_nhds hv₀ hva] with v hv g
    exact (hasDerivAt_coleHopf_shift_sqrt hA hA' hA''c hL hL₂ hm hv.1 hv.2 x g).congr_deriv (by
      ring)
  -- the uniform bounds and integrability the master chain rule needs
  have hwb : ∃ C c : ℝ, 0 ≤ c ∧ ∀ᶠ v in 𝓝 v₀, ∀ w, |B1 v w| ≤ C * Real.exp (c * |w|) :=
    ⟨L, 0, le_rfl, Filter.Eventually.of_forall fun v w => by simpa using hB1b v w⟩
  have hvb : ∃ C c : ℝ, 0 ≤ c ∧ ∀ᶠ v in 𝓝 v₀, ∀ w,
      |(1 / 2) * B2 v w| ≤ C * Real.exp (c * |w|) := by
    refine ⟨(L₂ + |m| * L ^ 2) / 2, 0, le_rfl, Filter.Eventually.of_forall fun v w => ?_⟩
    rw [abs_mul, zero_mul, Real.exp_zero, mul_one,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    calc 1 / 2 * |B2 v w| ≤ 1 / 2 * (L₂ + |m| * L ^ 2) := by gcongr; exact hB2b v w
      _ = (L₂ + |m| * L ^ 2) / 2 := by ring
  have hBshift : Continuous fun g => B v₀ (x + Real.sqrt (a - v₀) * g) :=
    (hBc v₀).comp (continuous_const.add (continuous_const.mul continuous_id))
  have hint : Integrable (fun g => B v₀ (x + Real.sqrt (a - v₀) * g)) (gaussianReal 0 1) :=
    (((hBlg v₀).toHasExpGrowth.comp_add_const x).comp_const_mul
      (Real.sqrt (a - v₀))).integrable_gaussianReal hBshift.aestronglyMeasurable
  have hwwg : HasExpGrowth fun w => B2 v₀ w - m * B1 v₀ w ^ 2 := by
    refine HasExpGrowth.of_bounded (C := L₂ + |m| * L ^ 2 + |m| * L ^ 2) fun w => ?_
    have h1 : |B1 v₀ w| ^ 2 ≤ L ^ 2 := by
      have := hB1b v₀ w
      nlinarith [abs_nonneg (B1 v₀ w)]
    calc |B2 v₀ w - m * B1 v₀ w ^ 2| = |B2 v₀ w + -(m * B1 v₀ w ^ 2)| := by rw [sub_eq_add_neg]
      _ ≤ |B2 v₀ w| + |-(m * B1 v₀ w ^ 2)| := abs_add_le _ _
      _ = |B2 v₀ w| + |m| * |B1 v₀ w| ^ 2 := by rw [abs_neg, abs_mul, abs_pow]
      _ ≤ L₂ + |m| * L ^ 2 + |m| * L ^ 2 :=
          add_le_add (hB2b v₀ w) (mul_le_mul_of_nonneg_left h1 (abs_nonneg m))
  have hmain := hasDerivAt_integral_curve_gaussianReal (H := fun w v => B v w)
    (Hw := fun w v => B1 v w) (Hww := fun w v => B2 v w - m * B1 v w ^ 2)
    (Hv := fun w v => (1 / 2) * B2 v w) (y := fun _ => x) (σ := fun v => a - v)
    (y' := fun _ => 0) (σ' := fun _ => -1) (v₀ := v₀) ha₀
    (Filter.Eventually.of_forall fun v => hasDerivAt_const v x) continuousAt_const
    (Filter.Eventually.of_forall fun v => (hasDerivAt_id v).const_sub a) continuousAt_const
    hΦ (fun v => (hBc v).measurable) (hB1c v₀).measurable
    (measurable_const.mul (hB2c v₀).measurable) hwb hvb hint (hB1' v₀)
    ((hB2c v₀).sub (continuous_const.mul ((hB1c v₀).pow 2))) hwwg
  -- identify the two sides
  have hmeas : ∀ v : ℝ, AEStronglyMeasurable (fun z => B v (x + z))
      (gaussianReal 0 (Real.toNNReal (a - v))) := fun v =>
    ((hBc v).comp (continuous_const.add continuous_id)).aestronglyMeasurable
  have hfun : ∀ᶠ v in 𝓝 v₀, (∫ g, B v (x + Real.sqrt (a - v) * g) ∂gaussianReal 0 1)
      = coleHopf 0 (Real.toNNReal (a - v)) (B v) x := by
    filter_upwards [Iio_mem_nhds hva] with v hv
    have hv' : v < a := hv
    rw [coleHopf_zero, integral_gaussianReal_eq_integral_sqrt_mul (Real.toNNReal (a - v))
      (hmeas v), Real.coe_toNNReal (a - v) (by linarith)]
  refine (hmain.congr_of_eventuallyEq (hfun.mono fun v hv => hv.symm)).congr_deriv ?_
  have hsq : AEStronglyMeasurable (fun z => B1 v₀ (x + z) ^ 2)
      (gaussianReal 0 (Real.toNNReal (a - v₀))) :=
    (((hB1c v₀).comp (continuous_const.add continuous_id)).pow 2).aestronglyMeasurable
  calc (∫ g, (0 : ℝ) * B1 v₀ (x + Real.sqrt (a - v₀) * g)
          + (-1 : ℝ) / 2 * (B2 v₀ (x + Real.sqrt (a - v₀) * g)
            - m * B1 v₀ (x + Real.sqrt (a - v₀) * g) ^ 2)
          + 1 / 2 * B2 v₀ (x + Real.sqrt (a - v₀) * g) ∂gaussianReal 0 1)
      = ∫ g, m / 2 * B1 v₀ (x + Real.sqrt (a - v₀) * g) ^ 2 ∂gaussianReal 0 1 :=
        integral_congr_ae (Filter.Eventually.of_forall fun g => by ring)
    _ = m / 2 * ∫ g, B1 v₀ (x + Real.sqrt (a - v₀) * g) ^ 2 ∂gaussianReal 0 1 :=
        integral_const_mul _ _
    _ = m / 2 * ∫ z, B1 v₀ (x + z) ^ 2 ∂gaussianReal 0 (Real.toNNReal (a - v₀)) := by
        rw [integral_gaussianReal_eq_integral_sqrt_mul (Real.toNNReal (a - v₀)) hsq,
          Real.coe_toNNReal (a - v₀) ha₀.le]

/-- **Lemma 14.7.3, (14.207)**: with `B(·, v) = T_{m,v} A` and `C(v) = T_{m', a−v}(B(·, v))(x)`,
`∂_v C = ((m − m')/2) 𝔼(B'(Z, v)² R)`, where `Z = x + g√(a − v)` and
`R = exp m'(B(Z, v) − C(v))` is the tilt of the outer operator (`R = 1` when `m' = 0`). -/
theorem hasDerivAt_coleHopf_coleHopf_var {m' a : ℝ} (hm : m ≠ 0) {v₀ : ℝ}
    (hv₀ : 0 < v₀) (hva : v₀ < a) (x : ℝ) :
    HasDerivAt (fun v : ℝ => coleHopf m' (Real.toNNReal (a - v)) (coleHopf m (Real.toNNReal v) A) x)
      (((m - m') / 2) * ∫ z, (∫ w, A' (x + z + w)
            * coleHopfQ m (Real.toNNReal v₀) A (x + z) w ∂gaussianReal 0 (Real.toNNReal v₀)) ^ 2
          * coleHopfQ m' (Real.toNNReal (a - v₀)) (coleHopf m (Real.toNNReal v₀) A) x z
          ∂gaussianReal 0 (Real.toNNReal (a - v₀))) v₀ := by
  rcases eq_or_ne m' 0 with rfl | hm'
  · simpa using hasDerivAt_coleHopf_coleHopf_var_zero hA hA' hA''c hL hL₂ hm hv₀ hva x
  · exact hasDerivAt_coleHopf_coleHopf_var_of_ne hA hA' hA''c hL hL₂ hm hm' hv₀ hva x

end TwoLevels

/-! ### The derivative in the exponent `m` -/

section MDeriv

variable (hA : HasLinearGrowth A) (hAm : Measurable A)
include hA hAm

/-- The derivative of `m ↦ 𝔼 exp (m A(x + g√v))`. -/
lemma hasDerivAt_integral_exp_mul_exponent (v : ℝ≥0) (x m₀ : ℝ) :
    HasDerivAt (fun m => ∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v)
      (∫ z, A (x + z) * Real.exp (m₀ * A (x + z)) ∂gaussianReal 0 v) m₀ := by
  obtain ⟨a, b, hb, hab⟩ := hA
  have ha : 0 ≤ a := by have := (abs_nonneg _).trans (hab 0); simpa using this
  set a' : ℝ := a + b * |x| with ha'
  have ha'0 : 0 ≤ a' := by positivity
  have hshift : ∀ z, |A (x + z)| ≤ a' + b * |z| := fun z => by
    calc |A (x + z)| ≤ a + b * |x + z| := hab _
      _ ≤ a + b * (|x| + |z|) := by gcongr; exact abs_add_le _ _
      _ = a' + b * |z| := by rw [ha']; ring
  have hAmz : Measurable fun z => A (x + z) := hAm.comp (measurable_const.add measurable_id)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gaussianReal 0 v)
    (F := fun m z => Real.exp (m * A (x + z)))
    (F' := fun m z => A (x + z) * Real.exp (m * A (x + z)))
    (bound := fun z => Real.exp ((|m₀| + 2) * a') * Real.exp ((|m₀| + 2) * b * |z|))
    (s := Metric.ball m₀ 1) (Metric.ball_mem_nhds _ one_pos)
    (Filter.Eventually.of_forall fun m => (Real.measurable_exp.comp
      (measurable_const.mul hAmz)).aestronglyMeasurable)
    (integrable_exp_mul_comp_add ⟨a, b, hb, hab⟩ hAm m₀ v x)
    (hAmz.mul (Real.measurable_exp.comp (measurable_const.mul hAmz))).aestronglyMeasurable ?_
    ((integrable_exp_mul_abs_gaussianReal 0 v ((|m₀| + 2) * b)).const_mul _) ?_).2
  · refine Filter.Eventually.of_forall fun z m hm => ?_
    have hm' : |m| ≤ |m₀| + 1 := by
      have := Metric.mem_ball.1 hm
      rw [Real.dist_eq] at this
      linarith [abs_sub_abs_le_abs_sub m m₀]
    have h1 : |A (x + z)| ≤ Real.exp (a' + b * |z|) := by
      linarith [hshift z, Real.add_one_le_exp (a' + b * |z|)]
    have h2 : Real.exp (m * A (x + z)) ≤ Real.exp ((|m₀| + 1) * (a' + b * |z|)) := by
      refine Real.exp_le_exp.2 ?_
      calc m * A (x + z) ≤ |m| * |A (x + z)| := by rw [← abs_mul]; exact le_abs_self _
        _ ≤ (|m₀| + 1) * (a' + b * |z|) :=
            mul_le_mul hm' (hshift z) (abs_nonneg _) (by positivity)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |A (x + z)| * Real.exp (m * A (x + z))
        ≤ Real.exp (a' + b * |z|) * Real.exp ((|m₀| + 1) * (a' + b * |z|)) :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp ((|m₀| + 2) * a') * Real.exp ((|m₀| + 2) * b * |z|) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
  · refine Filter.Eventually.of_forall fun z m _ => ?_
    have := ((hasDerivAt_id m).mul_const (A (x + z))).exp
    simpa [mul_comm] using this

/-- **Talagrand's (14.259)**: `∂_m T_{m,v} A(x) = (1/m) (𝔼 (A(Y) Q) − B(x))`, the derivative of the
Cole–Hopf transform in the exponent. -/
theorem hasDerivAt_coleHopf_exponent (hm : m ≠ 0) (v : ℝ≥0) (x : ℝ) :
    HasDerivAt (fun m => coleHopf m v A x)
      ((1 / m) * ((∫ z, A (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v) - coleHopf m v A x))
      m := by
  have hfun : ∀ᶠ m' in 𝓝 m, coleHopf m' v A x
      = Real.log (∫ z, Real.exp (m' * A (x + z)) ∂gaussianReal 0 v) / m' := by
    filter_upwards [isOpen_ne.mem_nhds hm] with m' hm'
    rw [coleHopf_of_ne hm', one_div, inv_mul_eq_div]
  have hI := hasDerivAt_integral_exp_mul_exponent hA hAm v x m
  have hpos := integral_exp_mul_comp_add_pos hA hAm m v x
  have hd := ((hI.log hpos.ne').div (hasDerivAt_id m) hm).congr_of_eventuallyEq hfun
  refine hd.congr_deriv ?_
  have e1 : ∫ z, A (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v
      = (∫ z, A (x + z) * Real.exp (m * A (x + z)) ∂gaussianReal 0 v)
        / ∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v := by
    rw [← integral_div]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
      beta_reduce
      rw [coleHopfQ_eq hA hAm hm v x z, mul_div_assoc])
  rw [e1, coleHopf_of_ne hm]
  simp only [id_eq]
  field_simp
  ring_nf

end MDeriv

end ProbabilityTheory
