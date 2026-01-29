/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Real.StarOrdered
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular

open MeasureTheory Filter Set Real
open scoped ProbabilityTheory NNReal ENNReal Filter Topology

/-!
# Gaussian integration by parts via exponential tilt (Stein’s identity)

We prove Stein’s lemma and the integration by parts formula for real Gaussian
measures by an explicit control of the exponential tilt and a dominated
differentiation argument. The presentation is self–contained and works in full
generality for one–dimensional (possibly degenerate) Gaussians, under minimal,
standard hypotheses on the test function.

Let `γ_{μ,v}` denote the law of the real normal `N(μ,v)` (variance `v : ℝ≥0`).
For `v ≠ 0` (non-degenerate, centered case) and a test function `F : ℝ → ℝ`
which is `C¹` with polynomial growth (for `F` and `F'`), we show
  E[X F(X)] = v · E[F'(X)]   for X ∼ N(0,v).

The proof follows the canonical route:

1. Exponential tilt and shift:
   For the centered Gaussian density `φ_v(x)`, and `t ∈ ℝ`,
     exp(t x − v t²/2) φ_v(x) = φ_v(x − v t).
   Hence, for every test function `F`,
     E[F(X) exp(tX − v t²/2)] = E[F(X + v t)]  (X ∼ N(0,v)).

2. Difference–quotient bounds:
   We establish sharp, uniform (in `t` near `0`) bounds for
     (exp(t x − v t²/2) − 1)/t,
   derived from the generic inequality `|exp a − 1| ≤ |a| exp |a|`
   and exact algebra on the tilt exponent. This yields an
   exponential–linear integrable majorant after composing with `F`.

3. Dominated differentiation:
   Using the previous step, we differentiate under the integral sign at `t = 0`
   and identify both one–sided derivatives:
     (d/dt)|_{t=0} E[F(X) exp(tX − v t²/2)] = E[X F(X)],
     (d/dt)|_{t=0} E[F(X + v t)]           = v · E[F'(X)].
   Equality of left and right derivatives yields Stein’s identity.

4. Degenerate case:
   If `v = 0`, `γ_{μ,0}` is the Dirac mass at `μ`. All statements reduce to
   trivial identities and are handled uniformly in the API.

Main statements:

- `gaussianTilt_eq_shift`:
    Exponential tilt equals a spatial shift of the test function:
    ∫ F(x) exp(t x − v t²/2) dγ_{0,v}(x) = ∫ F(x + v t) dγ_{0,v}(x).

- `tiltKernel_diffquot_uniform_bound`:
    Uniform (in `t` near `0`) exponential–linear bound for the centered difference quotient
    of the kernel `exp(t x − v t²/2)`.

- `HasModerateGrowth`:
    A simple “polynomial growth” predicate on `F` and `F'` ensuring all integrability
    requirements against a Gaussian. This replaces ad‑hoc, local integrability checks.

- `gaussianTilt_hasDerivAt_left`, `gaussianTilt_hasDerivAt_right`:
    Differentiation under the integral sign at `t = 0` for the tilted functional.

- `stein_lemma_gaussianReal` and `gaussianReal_integration_by_parts`:
    Measure–level statements for `N(0,v)` with `v ≠ 0`.

- `gaussianRV_integration_by_parts` and
  `gaussian_integration_by_parts_general`:
    Random-variable versions for centered and non–centered Gaussians, respectively.

Auxiliary integrability layer:

- Polynomial × sub-Gaussian integrability:
    We prove
      (1+|x|)^k exp(s x²) ∈ L¹(γ_{0,v})
    for every `k : ℕ` whenever either `v = 0` or `s < 1/(2v)`.
    In particular, for `s = 1/(4v)` (non-degenerate) we get the explicit bound
      exp(|x|²/(4v)).
    This is the only analytic input needed for dominated differentiation.

Design notes and future extensions:

- The arguments are written for ℝ and make sharp, explicit use of the 1D tilt
  algebra. The architecture is ready for a finite–dimensional extension
  (`ℝ^n` with the Euclidean norm), where the Cameron–Martin formula replaces
  the 1D tilt identity and the same dominated-differentiation pattern applies.

- The degenerate case is treated uniformly by the Dirac–mass API.

- When interacting with Lebesgue measure, we use the standard `withDensity` and
  `MeasurePreserving` API; addition by a constant is measure–preserving and is
  the canonical tool to implement the change of variables needed in Step 1.

References:
- C. Stein (1972). A bound for the error in the normal approximation to the
  distribution of a sum of dependent random variables.
- M. Talagrand (2011). Upper and Lower Bounds for Stochastic Processes.

-/
namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- If `f` is ae strongly measurable, then so is `‖f x‖^p`.
(The converse is false in general and was incorrectly stated before.) -/
lemma AEStronglyMeasurable.norm_rpow
    {E : Type*} [NormedAddCommGroup E] {f : α → E} {p : ℝ}
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => ‖f x‖ ^ p) μ := by
  have : AEMeasurable (fun x => ‖f x‖ ^ p) μ :=
    hf.norm.aemeasurable.pow_const p
  exact this.aestronglyMeasurable

end MeasureTheory

variable {Ω : Type*} [MeasureSpace Ω]

namespace ProbabilityTheory

/-- A random variable `g` is Gaussian with mean `μ` and variance `v` if its law is
`gaussianReal μ v`. -/
def IsGaussianRV (g : Ω → ℝ) (μ : ℝ) (v : ℝ≥0) : Prop :=
  Measure.map g ℙ = gaussianReal μ v

/-- A random variable `g` is centered Gaussian with variance `v` if its law is
`gaussianReal 0 v`. -/
def IsCenteredGaussianRV (g : Ω → ℝ) (v : ℝ≥0) : Prop :=
  IsGaussianRV g 0 v

/-- Second central moment of a (possibly non–centered) real Gaussian. -/
lemma integral_sq_sub_mean_gaussianReal (μ : ℝ) (v : ℝ≥0) :
    ∫ x, (x - μ)^2 ∂ gaussianReal μ v = v := by
  have h := variance_id_gaussianReal (μ := μ) (v := v)
  have := congrArg id h
  simpa using
    (by
      erw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at h
      exact h)

/-- Second moment of a centered Gaussian (mean = 0). -/
lemma integral_sq_gaussianReal_centered (v : ℝ≥0) :
    ∫ x, x^2 ∂ gaussianReal 0 v = v := by
  simpa using (integral_sq_sub_mean_gaussianReal (μ := 0) (v := v))

/-- Exponential tilt identity for the centered Gaussian density. -/
lemma gaussian_tilt_identity_zero
    {v : ℝ≥0} (hv : v ≠ 0) :
    ∀ t x : ℝ,
      Real.exp (t * x - (v:ℝ) * t^2 / 2) * gaussianPDFReal 0 v x
        = gaussianPDFReal 0 v (x - (v:ℝ) * t) := by
  intro t x
  have hvpos : 0 < (v:ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hsq : (x - (v:ℝ) * t)^2 = x^2 - 2 * (v:ℝ) * t * x + (v:ℝ)^2 * t^2 := by
    ring
  have hExp :
      (t * x - (v:ℝ) * t^2 / 2) - x^2 / (2 * (v:ℝ))
        = - ((x - (v:ℝ) * t)^2) / (2 * (v:ℝ)) := by
    have h2vne : (2 * (v:ℝ)) ≠ 0 := by nlinarith
    apply (mul_right_cancel₀ h2vne)
    have hL :
        ((t * x - (v:ℝ) * t^2 / 2) - x^2 / (2 * (v:ℝ))) * (2 * (v:ℝ))
          = 2 * (v:ℝ) * t * x - (v:ℝ)^2 * t^2 - x^2 := by ring_nf; aesop
    have hR :
        (- ((x - (v:ℝ) * t)^2) / (2 * (v:ℝ))) * (2 * (v:ℝ))
          = - (x - (v:ℝ) * t)^2 := by
      field_simp [h2vne]
    have hR' :
        - (x - (v:ℝ) * t)^2 = 2 * (v:ℝ) * t * x - (v:ℝ)^2 * t^2 - x^2 := by
      calc
        - (x - (v:ℝ) * t)^2
            = - (x^2 - 2 * (v:ℝ) * t * x + (v:ℝ)^2 * t^2) := by simp [hsq]
        _ = (-x^2 + 2 * (v:ℝ) * t * x - (v:ℝ)^2 * t^2) := by ring
        _ = 2 * (v:ℝ) * t * x - (v:ℝ)^2 * t^2 - x^2 := by ring
    aesop
  have : gaussianPDFReal 0 v x
      = (√(2 * π * (v:ℝ)))⁻¹ * Real.exp (- x^2 / (2 * (v:ℝ))) := by
    simp [gaussianPDFReal, sub_eq_add_neg, mul_comm, mul_left_comm]
  have : Real.exp (t * x - (v:ℝ) * t^2 / 2) * gaussianPDFReal 0 v x
      = (√(2 * π * (v:ℝ)))⁻¹
          * Real.exp ((t * x - (v:ℝ) * t^2 / 2) - x^2 / (2 * (v:ℝ))) := by
    simp [this, sub_eq_add_neg, Real.exp_add, add_assoc, mul_comm, mul_left_comm, mul_assoc]
    ring_nf
  calc
    Real.exp (t * x - (v:ℝ) * t^2 / 2) * gaussianPDFReal 0 v x
        = (√(2 * π * (v:ℝ)))⁻¹
            * Real.exp ((t * x - (v:ℝ) * t^2 / 2) - x^2 / (2 * (v:ℝ))) := this
    _ = (√(2 * π * (v:ℝ)))⁻¹
            * Real.exp ( - ((x - (v:ℝ) * t)^2) / (2 * (v:ℝ)) ) := by
          simp [hExp]
    _ = gaussianPDFReal 0 v (x - (v:ℝ) * t) := by
          simp [gaussianPDFReal, sub_eq_add_neg, mul_comm, mul_left_comm, pow_two]

/-- Tilted Gaussian expectation functional. -/
noncomputable def gaussianTilt (F : ℝ → ℝ) (v : ℝ≥0) (t : ℝ) : ℝ :=
  ∫ x, F x * Real.exp (t * x - (v:ℝ) * t^2 / 2) ∂ (gaussianReal 0 v)

lemma gaussianTilt_eq_shift
    {v : ℝ≥0} (hv : v ≠ 0) {F : ℝ → ℝ} :
    ∀ t, gaussianTilt F v t
        = ∫ x, F (x + (v:ℝ) * t) ∂ (gaussianReal 0 v) := by
  intro t
  set φ := fun (μ₀ : ℝ) x => gaussianPDFReal μ₀ v x
  set c := (v : ℝ) * t
  have hConv :
    ∀ (μ₀ : ℝ) (f : ℝ → ℝ),
      (∫ x, f x ∂ gaussianReal μ₀ v)
        = ∫ x, φ μ₀ x • f x :=
      fun μ₀ f => integral_gaussianReal_eq_integral_smul
        (μ := μ₀) (v := v) hv (f := f)
  have h1 :
      gaussianTilt F v t
        = ∫ x, F x * Real.exp (t * x - (v:ℝ) * t^2 / 2) * φ 0 x := by
    simp [gaussianTilt, hConv 0, φ, mul_comm, mul_left_comm]
  have hTilt :
      ∀ x,
        Real.exp (t * x - (v:ℝ) * t^2 / 2) * φ 0 x
          = φ 0 (x - c) := by
    intro x
    simpa [φ, c] using gaussian_tilt_identity_zero (v := v) hv t x
  have h2 :
      gaussianTilt F v t
        = ∫ x, F x * φ 0 (x - c) := by
    calc
      gaussianTilt F v t
          = ∫ x, F x * Real.exp (t * x - (v:ℝ) * t^2 / 2) * φ 0 x := h1
      _ = ∫ x, F x * (Real.exp (t * x - (v:ℝ) * t^2 / 2) * φ 0 x) := by
            simp [mul_comm, mul_left_comm]
      _ = ∫ x, F x * φ 0 (x - c) := by
            simp [hTilt]
  have hTrans :
      (∫ x, F x * φ 0 (x - c))
        = ∫ x, F (x + c) * φ 0 x := by
    let g := fun x : ℝ => F x * φ 0 (x - c)
    have hInv : (∫ x, g (x + c)) = ∫ x, g x := by
      simpa using
        (integral_add_right_eq_self (μ := (volume : Measure ℝ)) (f := g) c)
    have : (fun x => g (x + c)) = fun x => F (x + c) * φ 0 x := by
      funext x; simp [g, φ, sub_eq_add_neg, add_assoc]
    simpa [g, this, φ, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hInv.symm
  have hR :
      (∫ x, F (x + c) * φ 0 x)
        = ∫ x, F (x + c) ∂ gaussianReal 0 v := by
    have hConv' := hConv 0 (fun x => F (x + c))
    simpa [φ, mul_comm, mul_left_comm, mul_assoc] using hConv'.symm
  calc
    gaussianTilt F v t
        = ∫ x, F x * φ 0 (x - c) := h2
    _ = ∫ x, F (x + c) * φ 0 x := hTrans
    _ = ∫ x, F (x + c) ∂ gaussianReal 0 v := hR

/-! ### Prerequisites for the proof of `gaussianTilt_hasDerivAt_left`

We isolate:
1. A core kernel `tiltKernel`.
2. Pointwise derivative lemmas for the kernel and the integrand.
3. A (local-in-`t`) domination lemma suitable for applying differentiation
   under the integral sign at `t = 0`. -/

/-- The (centered) Gaussian exponential tilt kernel (no prefactor `F x`). -/
@[simp] noncomputable def tiltKernel (v : ℝ≥0) (t x : ℝ) : ℝ :=
  Real.exp (t * x - (v : ℝ) * t^2 / 2)

/-- Pointwise derivative of the quadratic–linear exponent inside the kernel. -/
lemma hasDerivAt_tiltExponent
    (v : ℝ≥0) (x t : ℝ) :
  HasDerivAt (fun s => s * x - (v:ℝ) * s^2 / 2) (x - (v:ℝ) * t) t := by
  have h1 : HasDerivAt (fun s : ℝ => s * x) x t := by
    simpa [mul_comm] using (hasDerivAt_id t).mul_const x
  have h2 : HasDerivAt (fun s : ℝ => (v:ℝ) * s^2 / 2) ((v:ℝ) * t) t := by
    have hpow : HasDerivAt (fun s : ℝ => s^2) (2 * t) t := by
      simpa using (hasDerivAt_pow (n := 2) t)
    have := hpow.const_mul ((v:ℝ)/2)
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using this
  have hsub := h1.sub h2
  simpa using hsub

/-- Derivative of the tilt kernel in `t`. -/
lemma hasDerivAt_tiltKernel (v : ℝ≥0) (x t : ℝ) :
  HasDerivAt (fun s => tiltKernel v s x)
    ((x - (v:ℝ) * t) * tiltKernel v t x) t := by
  have hExp := hasDerivAt_tiltExponent v x t
  have := (Real.hasDerivAt_exp _).comp t hExp
  simpa [tiltKernel, mul_comm, mul_left_comm, mul_assoc] using this

/-- Specialization of `hasDerivAt_tiltKernel` at `t = 0`. -/
lemma hasDerivAt_tiltKernel_at0 (v : ℝ≥0) (x : ℝ) :
  HasDerivAt (fun s => tiltKernel v s x) (x) 0 := by
  simpa [tiltKernel] using
    (hasDerivAt_tiltKernel v x 0)

/-- Derivative of the full integrand (with fixed space parameter `x`)
    before multiplying by the test function `F x`. -/
lemma hasDerivAt_F_mul_tiltKernel
    (v : ℝ≥0) (F : ℝ → ℝ) (x t : ℝ) :
  HasDerivAt (fun s => F x * tiltKernel v s x)
    (F x * (x - (v:ℝ) * t) * tiltKernel v t x) t := by
  have hk := hasDerivAt_tiltKernel v x t
  simpa [tiltKernel, mul_comm, mul_left_comm, mul_assoc] using hk.const_mul (F x)

/-- Specialization at `t = 0`: derivative is `F x * x`. -/
lemma hasDerivAt_F_mul_tiltKernel_at0
    (v : ℝ≥0) (F : ℝ → ℝ) (x : ℝ) :
  HasDerivAt (fun s => F x * tiltKernel v s x) (F x * x) 0 := by
  simpa using
    (hasDerivAt_F_mul_tiltKernel v F x 0)

/-- The integrand (as a 2-variable function) used in `gaussianTilt`. -/
@[simp] noncomputable def gaussianTiltIntegrand (F : ℝ → ℝ) (v : ℝ≥0) (t x : ℝ) : ℝ :=
  F x * tiltKernel v t x

/-- Pointwise derivative (in `t`) of the integrand (parametrized by `x`). -/
lemma hasDerivAt_gaussianTiltIntegrand
    (v : ℝ≥0) (F : ℝ → ℝ) (x t : ℝ) :
  HasDerivAt (fun s => gaussianTiltIntegrand F v s x)
    (F x * (x - (v:ℝ) * t) * tiltKernel v t x) t := by
  simpa [gaussianTiltIntegrand] using
    hasDerivAt_F_mul_tiltKernel v F x t

/-- Pointwise derivative (in `t`) at `0` of the integrand: `F x * x`. -/
lemma hasDerivAt_gaussianTiltIntegrand_at0
    (v : ℝ≥0) (F : ℝ → ℝ) (x : ℝ) :
  HasDerivAt (fun s => gaussianTiltIntegrand F v s x)
    (F x * x) 0 := by
  simpa [gaussianTiltIntegrand] using
    hasDerivAt_F_mul_tiltKernel_at0 v F x

/-! ### Refined uniform bounds for the tilt kernel (replacing the coarse placeholder)

We give standard (sharp enough) analytic inequalities used to justify dominated
convergence.  No ad–hoc `nlinarith` placeholders remain.
-/

/-- Basic upper bound: the exponential tilt never exceeds `exp (|t| |x|)`. -/
lemma tiltKernel_le_exp_abs (v : ℝ≥0) (t x : ℝ) :
  tiltKernel v t x ≤ Real.exp (|t| * |x|) := by
  have hineq :
      t * x - (v:ℝ) * t^2 / 2 ≤ |t| * |x| := by
    have hx : t * x ≤ |t| * |x| := by
      have := abs_mul t x
      exact (le_abs_self _).trans (by simp [abs_mul])
    have : t * x - (v:ℝ) * t^2 / 2 ≤ t * x := by
      have : 0 ≤ (v:ℝ) * t^2 / 2 := by
        have : 0 ≤ (v:ℝ) := v.property
        have : 0 ≤ t^2 := by nlinarith
        nlinarith
      linarith
    exact this.trans hx
  simpa [tiltKernel] using (Real.exp_le_exp.mpr hineq)

/-- Triangle inequality in the form used later. -/
lemma abs_add_le_abs_add_abs (x y : ℝ) : |x + y| ≤ |x| + |y| :=
  abs_add_le _ _

/-- Positive–increment representation: for `a > 0`,
`exp a - 1 = a * exp c` for some `c ∈ (0,a)`. -/
lemma exp_sub_one_pos_rep {a : ℝ} (h : 0 < a) :
    ∃ c ∈ Set.Ioo 0 a, Real.exp a - 1 = a * Real.exp c := by
  have hcont : ContinuousOn Real.exp (Icc 0 a) := Real.continuous_exp.continuousOn
  have hder : ∀ x ∈ Ioo 0 a, HasDerivAt Real.exp (Real.exp x) x :=
    by intro x _; exact Real.hasDerivAt_exp x
  obtain ⟨c, hcIoo, hcEq⟩ :=
    exists_hasDerivAt_eq_slope (f := Real.exp) (f' := fun x => Real.exp x)
      (a := 0) (b := a) h hcont hder
  have hEq' : Real.exp a - 1 = a * Real.exp c := by
    have : Real.exp c = (Real.exp a - 1) / a := by
      simp [hcEq, sub_eq_add_neg]
    have ha : a ≠ 0 := ne_of_gt h
    field_simp [this, ha] at *; exact id (Eq.symm this)
  exact ⟨c, hcIoo, hEq'⟩

/-- Negative–increment representation: for `a < 0`,
`exp a - 1 = a * exp c` for some `c ∈ (a,0)`. -/
lemma exp_sub_one_neg_rep {a : ℝ} (h : a < 0) :
    ∃ c ∈ Set.Ioo a 0, Real.exp a - 1 = a * Real.exp c := by
  have hcont : ContinuousOn Real.exp (Icc a 0) := Real.continuous_exp.continuousOn
  have hder : ∀ x ∈ Ioo a 0, HasDerivAt Real.exp (Real.exp x) x :=
    by intro x _; exact Real.hasDerivAt_exp x
  obtain ⟨c, hcIoo, hcEq⟩ :=
    exists_hasDerivAt_eq_slope (f := Real.exp) (f' := fun x => Real.exp x)
      (a := a) (b := 0) h hcont hder
  have ha0 : a ≠ 0 := ne_of_lt h
  have hEq' : Real.exp a - 1 = a * Real.exp c := by
    have h1 : Real.exp c = (1 - Real.exp a)/(-a) := by
      simpa [sub_eq_add_neg] using hcEq
    have hflip : (1 - Real.exp a)/(-a) = (Real.exp a - 1)/a := by
      have htmp : (1 - Real.exp a)/(-a) = -(1 - Real.exp a)/a := by
        field_simp [ha0, sub_eq_add_neg]
      have hnum : -(1 - Real.exp a) = Real.exp a - 1 := by
        simp
      simp [htmp, hnum]
    have hExpc : Real.exp c = (Real.exp a - 1)/a := by
      simpa [hflip] using h1
    have : a * Real.exp c = Real.exp a - 1 := by
      field_simp [ha0, hExpc]; grind
    exact this.symm
  exact ⟨c, hcIoo, hEq'⟩

/-- Sharp inequality `|exp a - 1| ≤ |a| * exp |a|`. -/
lemma abs_exp_sub_one_le_abs_mul_exp (a : ℝ) :
    |Real.exp a - 1| ≤ |a| * Real.exp |a| := by
  classical
  by_cases h0 : a = 0
  · subst h0; simp
  have hsign : 0 < a ∨ a < 0 := lt_or_gt_of_ne (ne_comm.mp h0)
  rcases hsign with hpos | hneg
  · -- a > 0
    rcases exp_sub_one_pos_rep hpos with ⟨c, hcIoo, hRep⟩
    have hAbs : |Real.exp a - 1| = |a| * Real.exp c := by
      simp [hRep, abs_mul, abs_of_pos hpos]
    have hc_le : c ≤ a := (Set.mem_Ioo.1 hcIoo).2.le
    have hMon : Real.exp c ≤ Real.exp a := Real.exp_le_exp.mpr hc_le
    have : Real.exp c ≤ Real.exp |a| := by simpa [abs_of_pos hpos]
    calc
      |Real.exp a - 1| = |a| * Real.exp c := hAbs
      _ ≤ |a| * Real.exp |a| := mul_le_mul_of_nonneg_left this (abs_nonneg _)
  · -- a < 0
    rcases exp_sub_one_neg_rep hneg with ⟨c, hcIoo, hRep⟩
    have hAbs : |Real.exp a - 1| = |a| * Real.exp c := by
      simp [hRep, abs_mul, abs_of_neg hneg]
    have hc_le0 : c ≤ 0 := (Set.mem_Ioo.1 hcIoo).2.le
    have hLe0 : Real.exp c ≤ Real.exp 0 := Real.exp_le_exp.mpr hc_le0
    have h0Le : Real.exp 0 ≤ Real.exp |a| := by
      have : |a| = -a := abs_of_neg hneg
      have : 0 ≤ -a := neg_nonneg.mpr (le_of_lt hneg)
      simp
    have hMon : Real.exp c ≤ Real.exp |a| := hLe0.trans h0Le
    calc
      |Real.exp a - 1| = |a| * Real.exp c := hAbs
      _ ≤ |a| * Real.exp |a| := mul_le_mul_of_nonneg_left hMon (abs_nonneg _)

/-- Monotonicity of division by a nonnegative (possibly zero) real.  (If the
denominator is zero both sides are zero in a field, so the inequality holds.) -/
lemma div_le_div_of_le_of_nonneg {a b c : ℝ} (h : a ≤ b) (hc : 0 ≤ c) :
  a / c ≤ b / c := by
  have : 0 ≤ c⁻¹ := inv_nonneg.mpr hc
  simpa [div_eq_mul_inv] using (mul_le_mul_of_nonneg_right h this)

/-- Commuting variant of `mul_div_cancel'`. -/
lemma mul_div_cancel_left' {G : Type*} [CommGroupWithZero G] (a : G) {b : G} (hb : b ≠ 0) :
  b * a / b = a := by
  rw [mul_comm];rw [propext (div_eq_iff_mul_eq hb)]

/-! ### Difference–quotient bounds for the tilt kernel  -/
/-- Absolute-value bound on the exponent of the Gaussian tilt kernel.  -/
lemma abs_tiltExponent_bound (v : ℝ≥0) (t x : ℝ) :
    |t * x - (v:ℝ) * t^2 / 2| ≤ |t| * |x| + (v:ℝ) * t^2 / 2 := by
  have hx : |t * x| = |t| * |x| := by simp [abs_mul]
  have hv : 0 ≤ (v:ℝ) * t^2 / 2 := by
    have hv' : 0 ≤ (v:ℝ) := v.property
    have ht2 : 0 ≤ t^2 := sq_nonneg _
    have : 0 ≤ (v:ℝ) * t^2 := mul_nonneg hv' ht2
    exact (div_nonneg this (by norm_num))
  have hAbsV : |(v:ℝ) * t^2 / 2| = (v:ℝ) * t^2 / 2 := by
    simp [abs_of_nonneg hv]
  have hAbsVneg : |-(v:ℝ) * t^2 / 2| = (v:ℝ) * t^2 / 2 := by
    have h' : (-(v:ℝ) * t^2 / 2) = -((v:ℝ) * t^2 / 2) := by ring
    simp
    aesop
  calc
    |t * x - (v:ℝ) * t^2 / 2|
        = |t * x + (-(v:ℝ) * t^2 / 2)| := by ring_nf
    _ ≤ |t * x| + |-(v:ℝ) * t^2 / 2| := abs_add_le _ _
    _ = |t| * |x| + (v:ℝ) * t^2 / 2 := by
          simp [hx]
          aesop

/-- Algebraic factorization of the tilt exponent. -/
lemma tiltExponent_factor (v : ℝ≥0) (t x : ℝ) :
    t * x - (v:ℝ) * t^2 / 2 = t * (x - (v:ℝ) * t / 2) := by
  ring

/-- Cancellation lemma giving the normalized absolute value after factoring. -/
lemma abs_tiltExponent_div_eq (v : ℝ≥0) {t x : ℝ} (ht : t ≠ 0) :
    |t * x - (v:ℝ) * t^2 / 2| / |t| = |x - (v:ℝ) * t / 2| := by
  have hfac := tiltExponent_factor (v := v) (t := t) (x := x)
  have hne : |t| ≠ 0 := abs_ne_zero.mpr ht
  simp [hfac, abs_mul, hne]

/-- Absolute value of the scaled term `|(v) * t / 2|`. -/
lemma abs_nnreal_mul_div_two (v : ℝ≥0) (t : ℝ) :
    |(v:ℝ) * t / 2| = (v:ℝ) * |t| / 2 := by
  have hv : 0 ≤ (v:ℝ) := v.property
  have h1 : |((v:ℝ) * t) / 2| = |(v:ℝ) * t| / |2| := abs_div _ _
  have h2 : |(v:ℝ) * t| = (v:ℝ) * |t| := by
    simp [abs_mul, abs_of_nonneg hv, mul_comm]
  have h3 : |2| = (2:ℝ) := by norm_num
  simpa [h2, h3] using h1

/-- Triangle-type bound specialized to the inner expression. (Fixed version) -/
lemma abs_x_sub_vt_half_le (v : ℝ≥0) (t x : ℝ) :
    |x - (v:ℝ) * t / 2| ≤ |x| + (v:ℝ) * |t| / 2 := by
  have h₁ : |x - (v:ℝ) * t / 2| ≤ |x| + |(v:ℝ) * t / 2| := by
    have hrewrite : x - (v:ℝ) * t / 2 = x + (-((v:ℝ) * t / 2)) := by ring
    simpa [hrewrite, abs_neg] using
      (abs_add_le x (-((v:ℝ) * t / 2)))
  have h₂ : |(v:ℝ) * t / 2| = (v:ℝ) * |t| / 2 :=
    abs_nnreal_mul_div_two v t
  simpa [h₂, add_comm, add_left_comm, add_assoc] using h₁

/-- Main divided bound reduced to the inner absolute value (nonzero `t`). -/
lemma abs_tiltExponent_div_le_inner (v : ℝ≥0) {t x : ℝ} (ht : t ≠ 0) :
    |t * x - (v:ℝ) * t^2 / 2| / |t| ≤ |x - (v:ℝ) * t / 2| := by
  simp [abs_tiltExponent_div_eq (v := v) ht]

/-- Final divided bound (original statement), now factored through helper lemmas. -/
lemma abs_tiltExponent_div_bound (v : ℝ≥0) {t x : ℝ} (ht : t ≠ 0) :
    |t * x - (v:ℝ) * t^2 / 2| / |t| ≤ |x| + (v:ℝ) * |t| / 2 := by
  calc
    |t * x - (v:ℝ) * t^2 / 2| / |t|
        ≤ |x - (v:ℝ) * t / 2| := abs_tiltExponent_div_le_inner (v := v) ht
    _ ≤ |x| + (v:ℝ) * |t| / 2 := abs_x_sub_vt_half_le (v := v) (t := t) (x := x)

/-- Exponential bound on the absolute-value exponent. -/
lemma exp_abs_tiltExponent_bound (v : ℝ≥0) (t x : ℝ) :
  Real.exp |t * x - (v:ℝ) * t^2 / 2|
    ≤ Real.exp (|t| * |x| + (v:ℝ) * t^2 / 2) := by
  exact Real.exp_le_exp.mpr (abs_tiltExponent_bound v t x)

/-! ### Difference–quotient bounds for the exponential -/

/-- Generic bound on the difference–quotient of the exponential function.
No Gaussian parameters appear here. -/
lemma abs_exp_sub_one_div_le (a t : ℝ) (ht : t ≠ 0) :
    |(Real.exp a - 1) / t| ≤ |a| / |t| * Real.exp |a| := by
  have h₁ : |Real.exp a - 1| ≤ |a| * Real.exp |a| :=
    abs_exp_sub_one_le_abs_mul_exp a
  have hpos : 0 < |t| := abs_pos.mpr ht
  have h₂ : |Real.exp a - 1| / |t| ≤ |a| * Real.exp |a| / |t| :=
    (div_le_div_of_le_of_nonneg h₁ (le_of_lt hpos))
  have h₃ : |(Real.exp a - 1) / t| ≤ |a| * Real.exp |a| / |t| := by
    simpa [abs_div] using h₂
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h₃

/-- Tilt-specific algebraic step: bounding the factor `|a| / |t|`
by a *linear–quadratic* expression in `x` and `|t|`.  This is exactly the
content of `abs_tiltExponent_div_bound`, but we expose it under the shorter
name `abs_tiltExponent_div_le_linQuad`. -/
lemma abs_tiltExponent_div_le_linQuad
    (v : ℝ≥0) {t x : ℝ} (ht : t ≠ 0) :
    let a : ℝ := t * x - (v:ℝ) * t^2 / 2;
    |a| / |t| ≤ |x| + (v:ℝ) * |t| / 2 := by
  intro a
  have := abs_tiltExponent_div_bound (v := v) (t := t) (x := x) ht
  simpa [a] using this

/-! ### Core difference–quotient bound  -/

/-- Core bound for the centred difference quotient of the **Gaussian tilt
kernel** -/
lemma tiltKernel_diffquot_bound_core
    (v : ℝ≥0) {t x : ℝ} (ht : t ≠ 0) :
  |(tiltKernel v t x - 1) / t|
    ≤ (|x| + (v:ℝ) * |t| / 2)
        * Real.exp (|t| * |x| + (v:ℝ) * t^2 / 2) := by
  set a : ℝ := t * x - (v:ℝ) * t^2 / 2
  have h₁ := abs_exp_sub_one_div_le a t ht
  have h₂ := abs_tiltExponent_div_le_linQuad (v := v) (t := t) (x := x) ht
  have h₃ : Real.exp |a| ≤ Real.exp (|t| * |x| + (v:ℝ) * t^2 / 2) :=
    exp_abs_tiltExponent_bound v t x
  calc
    |(tiltKernel v t x - 1) / t|
        = |(Real.exp a - 1) / t| := by
            simp [tiltKernel, a]
    _ ≤ (|a| / |t|) * Real.exp |a| := by
            simpa [mul_comm] using h₁
    _ ≤ (|x| + (v:ℝ) * |t| / 2) * Real.exp |a| := by
            gcongr;
    _ ≤ (|x| + (v:ℝ) * |t| / 2)
          * Real.exp (|t| * |x| + (v:ℝ) * t^2 / 2) := by
            gcongr;

/-- Uniform-in-x difference–quotient bound (all t, including 0). -/
lemma tiltKernel_diffquot_bound (v : ℝ≥0) (t x : ℝ) :
  |(tiltKernel v t x - 1) / t|
    ≤ (|x| + (v:ℝ) * |t| / 2)
        * Real.exp (|t| * |x| + (v:ℝ) * t^2 / 2) := by
  by_cases ht : t = 0
  · subst ht
    have : 0 ≤ (|x| + (v:ℝ) * 0 / 2)
        * Real.exp (0 * |x| + (v:ℝ) * 0^2 / 2) := by positivity
    simp [tiltKernel]
  · exact tiltKernel_diffquot_bound_core v ht

lemma tiltKernel_diffquot_bound_of_le (v : ℝ≥0) {t x δ : ℝ}
    (hδ : 0 ≤ δ) (ht : |t| ≤ δ) :
  |(tiltKernel v t x - 1) / t|
      ≤ (|x| + (v:ℝ) * δ / 2)
          * Real.exp (δ * |x| + (v:ℝ) * δ^2 / 2) := by
  have hcore := tiltKernel_diffquot_bound v t x
  have hFactor :
      |x| + (v:ℝ) * |t| / 2 ≤ |x| + (v:ℝ) * δ / 2 := by
    have hvnon : 0 ≤ (v:ℝ) := v.property
    have h_mul : (v:ℝ) * |t| ≤ (v:ℝ) * δ :=
      mul_le_mul_of_nonneg_left ht hvnon
    have h_half :
        (v:ℝ) * |t| / 2 ≤ (v:ℝ) * δ / 2 := by
      have : (0 : ℝ) ≤ (2 : ℝ)⁻¹ := by norm_num
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using mul_le_mul_of_nonneg_right h_mul this
    exact (add_le_add_iff_left |x|).mpr h_half
  have hExpArg :
      |t| * |x| + (v:ℝ) * t^2 / 2
        ≤ δ * |x| + (v:ℝ) * δ^2 / 2 := by
    have h1 : |t| * |x| ≤ δ * |x| :=
      mul_le_mul_of_nonneg_right ht (abs_nonneg _)
    have h_sq : t^2 ≤ δ^2 := by
      have h_abs : |t| ≤ δ := ht
      have habs : |t| ≤ |δ| := by
        simpa [abs_of_nonneg hδ] using h_abs
      simpa using (sq_le_sq).mpr habs
    have h2_base : (v:ℝ) * t^2 ≤ (v:ℝ) * δ^2 :=
      mul_le_mul_of_nonneg_left h_sq (by exact v.property)
    have : (0 : ℝ) ≤ (2 : ℝ)⁻¹ := by norm_num
    have h2 :
        (v:ℝ) * t^2 / 2 ≤ (v:ℝ) * δ^2 / 2 := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using mul_le_mul_of_nonneg_right h2_base this
    linarith
  have hExpMono :
      Real.exp (|t| * |x| + (v:ℝ) * t^2 / 2)
        ≤ Real.exp (δ * |x| + (v:ℝ) * δ^2 / 2) :=
    Real.exp_le_exp.mpr hExpArg
  have hpos₁ : 0 ≤ Real.exp (|t| * |x| + (v:ℝ) * t^2 / 2) := by positivity
  have hpos₂ : 0 ≤ Real.exp (δ * |x| + (v:ℝ) * δ^2 / 2) := by positivity
  calc
    |(tiltKernel v t x - 1) / t|
        ≤ (|x| + (v:ℝ) * |t| / 2)
            * Real.exp (|t| * |x| + (v:ℝ) * t^2 / 2) := hcore
    _ ≤ (|x| + (v:ℝ) * δ / 2)
            * Real.exp (δ * |x| + (v:ℝ) * δ^2 / 2) := by
      have h_comb :
          (|x| + (v:ℝ) * |t| / 2)
              * Real.exp (|t| * |x| + (v:ℝ) * t^2 / 2)
            ≤ (|x| + (v:ℝ) * δ / 2)
              * Real.exp (δ * |x| + (v:ℝ) * δ^2 / 2) :=
        mul_le_mul hFactor hExpMono
          hpos₁
          (by
            have habs : 0 ≤ |x| := abs_nonneg _
            have hvδ : 0 ≤ (v:ℝ) * δ / 2 := by
              have hv : 0 ≤ (v:ℝ) := v.property
              have hδ' : 0 ≤ δ := hδ
              nlinarith
            nlinarith)
      simpa using h_comb

/-- Final pointwise δ–bound (public version). -/
lemma tiltKernel_diffquot_pointwise_bound
    (v : ℝ≥0) {δ t x : ℝ} (hδ : 0 ≤ δ) (ht : |t| ≤ δ) :
  |(tiltKernel v t x - 1) / t|
    ≤ (|x| + (v:ℝ) * δ / 2)
        * Real.exp (δ * |x| + (v:ℝ) * δ^2 / 2) :=
  tiltKernel_diffquot_bound_of_le v hδ ht

/-! ### Uniform‐in‐`t` bounds -/

/-- `|t| ≤ δ` happens eventually in the neighbourhood of `0` (any `δ > 0`). -/
lemma eventually_abs_le (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), |t| ≤ δ := by
  have hOpen : IsOpen {t : ℝ | |t| < δ} :=
    isOpen_lt continuous_abs continuous_const
  have hMem : (0 : ℝ) ∈ {t : ℝ | |t| < δ} := by simp [hδ]
  have hNhds : {t : ℝ | |t| < δ} ∈ 𝓝 (0 : ℝ) :=
    hOpen.mem_nhds hMem
  filter_upwards [hNhds] with t ht
  exact (le_of_lt ht)

/-- Upgrade the exponent
    `exp (δ |x| + v δ² / 2) ≤ exp (v δ / 2) · exp (δ |x|)`
whenever `0 ≤ v` and `δ ∈ (0,1]`. This is the only non-trivial analytic step
needed in the uniform bound. -/
lemma exp_factor_le_product
    (v : ℝ≥0) {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1) (x : ℝ) :
    Real.exp (δ * |x| + (v : ℝ) * δ^2 / 2)
      ≤ Real.exp ((v : ℝ) * δ / 2) * Real.exp (δ * |x|) := by
  have hδsq : δ^2 ≤ δ := by
    have : δ * δ ≤ δ * 1 := mul_le_mul_of_nonneg_left hδ₁ (le_of_lt hδ₀)
    simpa [pow_two] using this
  have hv : 0 ≤ (v : ℝ) := v.property
  have hMul : (v : ℝ) * δ^2 ≤ (v : ℝ) * δ := mul_le_mul_of_nonneg_left hδsq hv
  have hExpArg :
      δ * |x| + (v : ℝ) * δ^2 / 2
        ≤ δ * |x| + (v : ℝ) * δ / 2 := by
    have : (v : ℝ) * δ^2 / 2 ≤ (v : ℝ) * δ / 2 := by
      nlinarith [hMul]
    linarith
  have := Real.exp_le_exp.mpr hExpArg
  simpa [Real.exp_add, mul_comm, mul_left_comm, mul_assoc] using this

/-- Enhanced *pointwise* δ–bound (linear-quadratic ↝ linear × exp) that will
be used in the uniform lemma. -/
lemma tiltKernel_diffquot_pointwise_bound'
    (v : ℝ≥0) {δ t x : ℝ} (hδ : 0 ≤ δ) (ht : |t| ≤ δ)
    (hδ₁ : δ ≤ 1) :
  |(tiltKernel v t x - 1) / t|
    ≤ (|x| + (v : ℝ) * δ / 2)
        * Real.exp ((v : ℝ) * δ / 2) * Real.exp (δ * |x|) := by
  have h₀ :=
    tiltKernel_diffquot_pointwise_bound (v := v) (δ := δ) (t := t) (x := x) hδ ht
  by_cases hδ0 : δ = 0
  · subst hδ0
    simpa using h₀
  · have hδpos : 0 < δ := lt_of_le_of_ne' hδ hδ0
    have hExpUpgrade :
        Real.exp (δ * |x| + (v : ℝ) * δ^2 / 2)
          ≤ Real.exp ((v : ℝ) * δ / 2) * Real.exp (δ * |x|) :=
      exp_factor_le_product v hδpos hδ₁ x
    have hlin : 0 ≤ |x| + (v : ℝ) * δ / 2 := by
      have hx : 0 ≤ |x| := abs_nonneg _
      have hvδ : 0 ≤ (v : ℝ) * δ / 2 := by
        have hv : 0 ≤ (v : ℝ) := v.property
        have hδ' : 0 ≤ δ := hδ
        have hmul : 0 ≤ (v : ℝ) * δ := mul_nonneg hv hδ'
        exact div_nonneg hmul (by norm_num)
      exact add_nonneg hx hvδ
    have hMul :
        (|x| + (v : ℝ) * δ / 2) * Real.exp (δ * |x| + (v : ℝ) * δ^2 / 2)
          ≤ (|x| + (v : ℝ) * δ / 2)
              * (Real.exp ((v : ℝ) * δ / 2) * Real.exp (δ * |x|)) :=
      mul_le_mul_of_nonneg_left hExpUpgrade hlin
    exact (le_trans h₀ (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hMul))

/-- *Elementary* eventual property:
`(∀ᶠ t, |t| ≤ δ)` together with the enhanced pointwise bound. -/
lemma eventually_diffquot_enhanced
    (v : ℝ≥0) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1) :
  ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
    |t| ≤ δ ∧
    ∀ x,
      |(tiltKernel v t x - 1) / t|
        ≤ (|x| + (v : ℝ) * δ / 2)
            * Real.exp ((v : ℝ) * δ / 2) * Real.exp (δ * |x|) := by
  have hSmall := eventually_abs_le δ hδ₀
  filter_upwards [hSmall] with t ht_small
  refine And.intro ht_small ?_
  intro x
  have :=
    tiltKernel_diffquot_pointwise_bound' (v := v) (δ := δ) (t := t) (x := x)
      (hδ := (le_of_lt hδ₀)) (ht := ht_small) hδ₁
  simpa using this

/-! ### Uniform bound -/

/-- Uniform (in `t` close to `0`) *exponential–linear* bound on the centred
difference quotient of the Gaussian tilt kernel.  This is now just a thin
wrapper around the auxiliary lemmas above. -/
lemma tiltKernel_diffquot_uniform_bound
    (v : ℝ≥0) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1) :
  ∀ᶠ t in 𝓝 (0 : ℝ),
    |t| ≤ δ ∧
    ∀ x,
      |(tiltKernel v t x - 1) / t|
        ≤ (|x| + (v : ℝ) * δ / 2)
            * Real.exp ((v : ℝ) * δ / 2) * Real.exp (δ * |x|) :=
  eventually_diffquot_enhanced v δ hδ₀ hδ₁

/-- Final domination lemma (state-of-art version):
For any fixed `δ ∈ (0,1]`, and any function `F`, for `|t| ≤ δ` we have
  | (F x * tiltKernel v t x - F x) / t |
    ≤ |F x| * (|x| + (v:ℝ) * δ / 2) * Real.exp ((v:ℝ) * δ / 2) * Real.exp (δ * |x|).

Uses the uniform kernel difference–quotient bound and a simple factorization. -/
lemma gaussianTilt_diffquot_dom
    (v : ℝ≥0) (F : ℝ → ℝ)
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1) :
  ∀ᶠ t in 𝓝 (0 : ℝ),
    |t| ≤ δ ∧
    ∀ x,
      |(F x * tiltKernel v t x - F x) / t|
        ≤ |F x| * (|x| + (v:ℝ) * δ / 2)
            * Real.exp ((v:ℝ) * δ / 2) * Real.exp (δ * |x|) := by
  refine (tiltKernel_diffquot_uniform_bound v δ hδ₀ hδ₁).mono ?_
  intro t ht
  refine And.intro ht.left ?_
  intro x
  have hcore := ht.right x
  have hfact : F x * tiltKernel v t x - F x = F x * (tiltKernel v t x - 1) := by ring
  calc
    |(F x * tiltKernel v t x - F x) / t|
        = |(F x * (tiltKernel v t x - 1)) / t| := by aesop
    _ = |F x| * |(tiltKernel v t x - 1) / t| := by
          simp [div_eq_mul_inv, abs_mul, mul_comm, mul_left_comm, mul_assoc]
    _ ≤ |F x| * ((|x| + (v:ℝ) * δ / 2) * Real.exp ((v:ℝ) * δ / 2) * Real.exp (δ * |x|)) :=
          mul_le_mul_of_nonneg_left hcore (abs_nonneg _)
    _ = |F x| * (|x| + (v:ℝ) * δ / 2)
          * Real.exp ((v:ℝ) * δ / 2) * Real.exp (δ * |x|) := by
          ring_nf

/-!
## Moderate growth shortcut

To ease usage of the Gaussian integration by parts lemma, we introduce a (very
simple) predicate `HasModerateGrowth F` asserting polynomial growth bounds on
`F` and its derivative.  From this, integrability of the required functions
under a (centered) Gaussian measure follows, so the user does not have to
establish the integrability hypotheses manually each time.

-/

/-- `HasModerateGrowth F` means that `F` and its (real) derivative grow at most
polynomially: there are constants `C` and an exponent `m` such that both
`|F x|` and `|deriv F x|` are bounded by `C (1 + |x|)^m`.  This (very) classical
condition implies integrability of the functions we need against a Gaussian
measure. -/
def HasModerateGrowth (F : ℝ → ℝ) : Prop :=
  ∃ (C : ℝ) (m : ℕ), 0 < C ∧
    (∀ x, |F x| ≤ C * (1 + |x|)^m) ∧
    (∀ x, |deriv F x| ≤ C * (1 + |x|)^m)

/-- All absolute moments `|x|^k` are integrable under any centered real Gaussian. -/
lemma integrable_abs_pow_gaussianReal_centered
    (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => |x| ^ k) (gaussianReal 0 v) := by
  cases k with
  | zero =>
      have h : Integrable (fun _ : ℝ => (1 : ℝ)) (gaussianReal 0 v) :=
        integrable_const (μ := gaussianReal 0 v) (c := (1 : ℝ))
      simp [pow_zero]
  | succ k =>
      have hmem :
          MemLp (fun x : ℝ => x) ((Nat.succ k : ℝ≥0∞)) (gaussianReal 0 v) := by
        simpa using
          (memLp_id_gaussianReal' (μ := 0) (v := v)
            (p := (Nat.succ k : ℝ≥0∞)) (by simp))
      have hInt_norm_rpow :
          Integrable
            (fun x : ℝ => ‖(fun y : ℝ => y) x‖ ^ (((Nat.succ k : ℝ≥0∞)).toReal))
            (gaussianReal 0 v) := by
        simpa using
          hmem.integrable_norm_rpow (by simp : ((Nat.succ k : ℝ≥0∞)) ≠ 0)
      have hInt_abs_rpow :
          Integrable (fun x : ℝ => |x| ^ (((Nat.succ k : ℝ≥0∞)).toReal))
            (gaussianReal 0 v) := by
        simpa [Real.norm_eq_abs] using hInt_norm_rpow
      have h_toNat :
              (fun x : ℝ => |x| ^ (((Nat.succ k : ℝ≥0∞)).toReal))
                =ᵐ[gaussianReal 0 v] (fun x : ℝ => |x| ^ (Nat.succ k)) := by
            have ht : (((Nat.succ k : ℝ≥0∞)).toReal) = (Nat.succ k : ℝ) := by
              aesop
            exact ae_of_all (gaussianReal 0 v) (fun x => by
              have hx : 0 ≤ |x| := abs_nonneg x
              rw [ht]
              exact rpow_natCast |x| k.succ)
      exact (hInt_abs_rpow.congr h_toNat)

/-- Polynomial moment `(1 + |x|)^k` integrable under any centered real Gaussian. -/
lemma integrable_one_add_abs_pow_gaussianReal_centered
    (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|)^k) (gaussianReal 0 v) := by
  classical
  have hpow :
      (fun x : ℝ => (1 + |x|)^k)
        =
      (fun x : ℝ =>
        ∑ j ∈ Finset.range (k + 1),
          (Nat.choose k j : ℝ) * |x| ^ j) := by
    funext x
    have : (1 + |x|)^k = (|x| + 1)^k := by
      ring
    simpa [this, one_pow, mul_comm, mul_left_comm, mul_assoc]
      using (add_pow |x| (1 : ℝ) k)
  rw [hpow]
  refine
    integrable_finset_sum
        (s := Finset.range (k + 1)) (μ := gaussianReal 0 v) ?_
  intro j hj
  have hjInt : Integrable (fun x : ℝ => |x| ^ j) (gaussianReal 0 v) :=
    integrable_abs_pow_gaussianReal_centered v j
  let Δ : ℝ := (Nat.choose k j : ℝ)
  have : Integrable (fun x : ℝ => Δ * |x| ^ j) (gaussianReal 0 v) :=
    hjInt.const_mul Δ
  simpa [Δ, mul_comm, mul_left_comm, mul_assoc] using this

/-- A measurable‐version of the moderate‐growth ⇒ integrability lemma. -/
theorem HasModerateGrowth.integrable_pair'
    {F : ℝ → ℝ} {v : ℝ≥0} (hF : HasModerateGrowth F)
    (hF_meas : AEStronglyMeasurable F (gaussianReal 0 v))
    (hF'_meas : AEStronglyMeasurable (fun x => deriv F x) (gaussianReal 0 v)) :
    Integrable (fun x => x * F x) (gaussianReal 0 v)
      ∧ Integrable (fun x => deriv F x) (gaussianReal 0 v) := by
  rcases hF with ⟨C, m, hCpos, hFbound, hF'bound⟩
  have hMom_m  : Integrable (fun x : ℝ => (1 + |x|)^m)     (gaussianReal 0 v) :=
    integrable_one_add_abs_pow_gaussianReal_centered v m
  have hMom_mp1 : Integrable (fun x : ℝ => (1 + |x|)^(m+1)) (gaussianReal 0 v) :=
    integrable_one_add_abs_pow_gaussianReal_centered v (m + 1)
  have hInt_dF : Integrable (fun x => deriv F x) (gaussianReal 0 v) := by
    refine Integrable.mono' ((hMom_m).const_mul C) hF'_meas ?_
    refine ae_of_all _ (fun x => ?_)
    have hCle : 0 ≤ C := le_of_lt hCpos
    simpa [Real.norm_eq_abs, abs_of_nonneg hCle,
      mul_comm, mul_left_comm, mul_assoc] using (hF'bound x)
  have h_xF_meas :
      AEStronglyMeasurable (fun x : ℝ => x * F x) (gaussianReal 0 v) :=
    (aestronglyMeasurable_id.mul hF_meas)
  have hInt_xF : Integrable (fun x => x * F x) (gaussianReal 0 v) := by
    refine Integrable.mono' ((hMom_mp1).const_mul C) h_xF_meas ?_
    refine ae_of_all _ (fun x => ?_)
    have hCle : 0 ≤ C := le_of_lt hCpos
    -- `|x| ≤ 1 + |x|`
    have hx_le : |x| ≤ 1 + |x| := by
      have := abs_nonneg x; linarith
    -- `|x| * (1 + |x|)^m ≤ (1 + |x|)^(m+1)`
    have hx_pow :
        |x| * (1 + |x|)^m ≤ (1 + |x|)^(m + 1) := by
      have hbase : 0 ≤ (1 + |x|)^m :=
        pow_nonneg (by have := abs_nonneg x; linarith) _
      have := mul_le_mul_of_nonneg_right hx_le hbase
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using this
    have hFx : |F x| ≤ C * (1 + |x|)^m := hFbound x
    have h1 : |x| * |F x| ≤ |x| * (C * (1 + |x|)^m) :=
      mul_le_mul_of_nonneg_left hFx (abs_nonneg _)
    have h2 : |x| * (C * (1 + |x|)^m) = C * (|x| * (1 + |x|)^m) := by ring
    have h3 : C * (|x| * (1 + |x|)^m) ≤ C * (1 + |x|)^(m + 1) :=
      mul_le_mul_of_nonneg_left hx_pow hCle
    have : |x * F x| ≤ C * (1 + |x|)^(m + 1) := by
      calc
        |x * F x| = |x| * |F x| := by simp [abs_mul]
        _ ≤ |x| * (C * (1 + |x|)^m) := h1
        _ = C * (|x| * (1 + |x|)^m) := h2
        _ ≤ C * (1 + |x|)^(m + 1)   := h3
    exact this

  exact ⟨hInt_xF, hInt_dF⟩

theorem HasModerateGrowth.integrable_pair
    {F : ℝ → ℝ} {v : ℝ≥0} (hF : HasModerateGrowth F)
    (hF_meas : AEStronglyMeasurable F (gaussianReal 0 v))
    (hF'_meas : AEStronglyMeasurable (fun x => deriv F x) (gaussianReal 0 v)) :
    Integrable (fun x => x * F x) (gaussianReal 0 v)
      ∧ Integrable (fun x => deriv F x) (gaussianReal 0 v) :=
  HasModerateGrowth.integrable_pair' (v := v) hF hF_meas hF'_meas

section DominationExponentialUpgrade

variable {v : ℝ≥0} {δ : ℝ}

/-! ### Elementary linear–quadratic “Young” bounds  -/

section YoungBounds

open Real

/-- Core algebraic inequality
`4 v δ |x| ≤ |x|² + 4 v² δ²`, obtained from the non-negativity of
`(|x| − 2 v δ)²`.  Only the assumption `0 < v : ℝ` is needed. -/
lemma four_mul_mul_le_sq_add_sq
    {v δ x : ℝ} (_ : 0 < v) :
    4 * v * δ * |x| ≤ |x| ^ 2 + 4 * v ^ 2 * δ ^ 2 := by
  have hsq : 0 ≤ (|x| - 2 * v * δ) ^ 2 := by
    exact sq_nonneg _
  have hsq_exp : (|x| - 2 * v * δ) ^ 2 =
      |x| ^ 2 - 4 * v * δ * |x| + 4 * v ^ 2 * δ ^ 2 := by ring
  have : 4 * v * δ * |x| ≤ |x| ^ 2 + 4 * v ^ 2 * δ ^ 2 := by
    -- `0 ≤ A - B`  ⇒  `B ≤ A`.
    have : 0 ≤ |x| ^ 2 - 4 * v * δ * |x| + 4 * v ^ 2 * δ ^ 2 := by
      simpa [hsq_exp] using hsq
    linarith
  simpa using this

/-- “Young” inequality in *undivided* form
`4 v δ |x| ≤ |x|² + 4 v² δ²`. -/
lemma young_linear_quadratic_mul
    {v δ x : ℝ} (hv : 0 < v) :
    4 * v * δ * |x| ≤ |x| ^ 2 + 4 * v ^ 2 * δ ^ 2 :=
  four_mul_mul_le_sq_add_sq hv

namespace Real

open Real

lemma div_le_iff_of_pos {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b c : α} (hc : 0 < c) :
    a ≤ b / c ↔ a * c ≤ b := by
  simp [div_eq_mul_inv]
  rw [@le_iff_le_iff_lt_iff_lt]
  exact mul_inv_lt_iff₀ hc

end Real
open Real


section YoungBounds

open Real

/-- Divided Young inequality
`δ |x| ≤ |x|² /(4 v) + v δ²` (with `v > 0`). -/
lemma young_linear_quadratic_div
    {v δ x : ℝ} (hv : 0 < v) :
    δ * |x| ≤ |x| ^ 2 / (4 * v) + v * δ ^ 2 := by
  have h₀ := young_linear_quadratic_mul (v := v) (δ := δ) (x := x) hv
  have hpos : 0 < 4 * v := by
    have : (0 : ℝ) < 4 := by norm_num
    exact mul_pos this hv
  have h₁ : δ * |x| ≤ (|x| ^ 2 + 4 * v ^ 2 * δ ^ 2) / (4 * v) := by
    have hmul : (δ * |x|) * (4 * v) ≤ |x| ^ 2 + 4 * v ^ 2 * δ ^ 2 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using h₀
    exact (div_le_iff_of_pos hpos).mpr hmul
  have h_split :
      (|x| ^ 2 + 4 * v ^ 2 * δ ^ 2) / (4 * v)
        = |x| ^ 2 / (4 * v) + v * δ ^ 2 := by
    field_simp [mul_comm, mul_left_comm, mul_assoc]
  aesop

/-- **Young inequality (Gaussian form) for `ℝ≥0` variance**. -/
lemma young_linear_quadratic_bound
    (x δ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    δ * |x| ≤ |x|^2 / (4 * (v : ℝ)) + (v : ℝ) * δ^2 := by
  have hv_pos : 0 < (v : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hv)
  simpa using (young_linear_quadratic_div (x := x) (δ := δ) hv_pos)

/-- Exponential linear-vs-quadratic domination (explicit constant):
for `v > 0` we have
  exp (δ |x|) ≤ exp ( (v:ℝ) * δ^2 ) * exp ( |x|^2 / (4 v) ). -/
lemma exp_abs_linear_le_gaussian_aux
    (δ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    ∀ x, Real.exp (δ * |x|)
        ≤ Real.exp ((v:ℝ) * δ^2) * Real.exp (|x|^2 / (4 * (v:ℝ))) := by
  intro x
  have h := young_linear_quadratic_bound x δ v hv
  have : δ * |x| ≤ (|x|^2) / (4 * (v:ℝ)) + (v:ℝ) * δ^2 := by aesop
  have hExp := Real.exp_le_exp.mpr this
  simpa [Real.exp_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
    mul_assoc] using hExp

/-- Polynomial growth control transferred to the profile used in
`gaussianTilt_diffquot_dom_integrable`: from moderate growth of `F` we get
a bound of the form
  |F x| * (|x| + 1) ≤ C' * (1 + |x|)^{m+1}. -/
lemma HasModerateGrowth.bound_F_mul_linear
    {F : ℝ → ℝ} (hF : HasModerateGrowth F) :
  ∃ (C : ℝ) (m : ℕ) (_ : 0 < C),
    ∀ x, |F x| * (|x| + 1) ≤ C * (1 + |x|)^(m+1) := by
  rcases hF with ⟨C, m, hCpos, hFbound, _⟩
  have h₂ : ∀ x, |F x| * (|x| + 1) ≤ (C * 2) * (1 + |x|)^(m+1) := by
    intro x
    have hF' := hFbound x
    have hlin : (|x| + 1) ≤ 2 * (1 + |x|) := by nlinarith [abs_nonneg x]
    have : |F x| * (|x| + 1) ≤ |F x| * (2 * (1 + |x|)) :=
      mul_le_mul_of_nonneg_left hlin (abs_nonneg _)
    have : |F x| * (|x| + 1) ≤ 2 * |F x| * (1 + |x|) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have hFpow :
        |F x| ≤ C * (1 + |x|)^m := hF'
    have : 2 * |F x| * (1 + |x|) ≤ 2 * (C * (1 + |x|)^m) * (1 + |x|) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hFpow (by norm_num))
        (by nlinarith [abs_nonneg x])
    have hpow :
        2 * (C * (1 + |x|)^m) * (1 + |x|)
          = (C * 2) * (1 + |x|)^(m+1) := by
          simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]
    have := le_trans this (by
    aesop)
    have hstep :
        |F x| * (|x| + 1) ≤ 2 * C * (1 + |x|)^(m+1) := by
      have h1 :
          |F x| * (|x| + 1) ≤ 2 * |F x| * (1 + |x|) := by
        aesop
      have h2 :
          2 * |F x| * (1 + |x|) ≤ 2 * (C * (1 + |x|)^m) * (1 + |x|) := by aesop
      have h3 :
          2 * (C * (1 + |x|)^m) * (1 + |x|) = 2 * C * (1 + |x|)^(m+1) := by
        simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]
      linarith
    simpa [mul_comm, mul_left_comm, mul_assoc] using hstep
  refine ⟨C * 2, m, by nlinarith, h₂⟩

namespace Measure

open MeasureTheory

/-- Any Borel function is integrable with respect to a Dirac measure: the
`L¹`‐norm collapses to the single (finite) value at the support point. -/
lemma integrable_dirac
    {f : ℝ → ℝ} {a : ℝ} (hf : Measurable f) :
    Integrable f (Measure.dirac a) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  have hEval :
      (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ∂ Measure.dirac a) =
        (‖f a‖₊ : ℝ≥0∞) := by
    simp
  have : (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ∂ Measure.dirac a) < ∞ := by
    simp [hEval, show ((‖f a‖₊ : ℝ≥0∞) < ∞) by simp]
  exact this
end Measure
open Measure

/-!
### Structured domination lemmas for `( |x| + B )^k` and Gaussian integrability

We factor the proof of
`Integrable fun x => (|x| + 2)^k * exp (-a * x^2)`
into small reusable lemmas.  The bound is intentionally *coarse* but
polynomial × Gaussian is always integrable, so sharp constants are irrelevant.
-/

section PolyGaussianDomination

namespace Real

/-- Convenience wrapper (ℝ‐specialization) of `pow_le_pow_of_le_left`. -/
lemma pow_le_pow_of_le_left {x y : ℝ} {k : ℕ}
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    x^k ≤ y^k :=
  pow_le_pow_left₀ hx hxy k

/-- Elementary inequality: `|x| + B ≤ 2 * max B |x|`. -/
lemma abs_add_const_le_two_mul_max (B x : ℝ) :
    |x| + B ≤ 2 * max B |x| := by
  have h₁ : |x| ≤ max B |x| := le_max_right _ _
  have h₂ : B   ≤ max B |x| := le_max_left  _ _
  have h : |x| + B ≤ max B |x| + max B |x| := add_le_add h₁ h₂
  simpa [two_mul, add_comm, add_left_comm, add_assoc] using h

/-- Power version (requires nonnegativity of the base):
If `0 ≤ |x| + B` then `( |x| + B)^k ≤ (2)^k * (max B |x|)^k`.  (This
hypothesis is satisfied, for instance, when `0 ≤ B`.) -/
lemma pow_abs_add_const_le_two_pow_mul_max
    (B x : ℝ) (k : ℕ) (hbase : 0 ≤ |x| + B) :
    (|x| + B)^k ≤ (2 : ℝ)^k * (max B |x|)^k := by
  have hineq := abs_add_const_le_two_mul_max B x
  have hpow : (|x| + B)^k ≤ (2 * max B |x|)^k :=
    pow_le_pow_of_le_left hbase hineq
  have hfac : (2 * max B |x|)^k = (2 : ℝ)^k * (max B |x|)^k := by
    simp [mul_comm]
    exact mul_pow (max B |x|) 2 k
  aesop

/-- Convenience specialization of the previous lemma when `B ≥ 0`. -/
lemma pow_abs_add_const_le_two_pow_mul_max_of_nonneg
    {B x : ℝ} (k : ℕ) (hB : 0 ≤ B) :
    (|x| + B)^k ≤ (2 : ℝ)^k * (max B |x|)^k :=
  pow_abs_add_const_le_two_pow_mul_max B x k
    (add_nonneg (abs_nonneg _) hB)

/-- Auxiliary bound turning the `max` into a product of two simpler factors:
`(max B |x|)^k ≤ (max B 1)^k * (1 + |x|^k)`. -/
lemma max_pow_le_max1_pow_mul_one_add_abs_pow (B x : ℝ) (k : ℕ) :
    (max B |x|)^k ≤ (max B 1)^k * (1 + |x|^k) := by
  have hx0 : 0 ≤ |x| := abs_nonneg _
  by_cases h1 : |x| ≤ 1
  · -- Case |x| ≤ 1
    have hmax : max B |x| ≤ max B 1 := by
      exact max_le_max le_rfl h1
    have hpos : 0 ≤ max B |x| := le_trans hx0 (le_max_right _ _)
    have hpow : (max B |x|)^k ≤ (max B 1)^k :=
      pow_le_pow_of_le_left hpos hmax
    have h1pow : (1 : ℝ) ≤ 1 + |x|^k := by
      have : 0 ≤ |x|^k := pow_nonneg hx0 _
      linarith
    have hnon : 0 ≤ (max B 1)^k := by
      have : 0 ≤ max B 1 := Preorder.le_trans 0 (max B |x|) (max B 1) hpos hmax
      exact pow_nonneg this _
    have : (max B |x|)^k ≤ (max B 1)^k * (1 + |x|^k) := by
      have hmul := mul_le_mul_of_nonneg_left h1pow hnon
      have hmul' : max B 1 ^ k ≤ max B 1 ^ k * (1 + |x| ^ k) := by
        simp
      simpa [one_mul] using (le_trans hpow hmul')
    simpa using this
  · -- Case |x| ≥ 1
    have hx1 : 1 ≤ |x| := le_of_lt (lt_of_not_ge h1)
    have hmax :
        max B |x| ≤ (max B 1) * |x| := by
      cases le_total B |x| with
      | inl hB =>
          have hM1 : 1 ≤ max B 1 := le_max_right _ _
          have : max B |x| = |x| := by simpa [max_comm] using max_eq_right hB
          have hMul : |x| ≤ (max B 1) * |x| :=
            by
              have : 1 ≤ max B 1 := hM1
              have hxpos : 0 ≤ |x| := hx0
              have := mul_le_mul_of_nonneg_right this hxpos
              simpa [one_mul] using this
          simpa [this]
      | inr hB =>
          have hM1 : max B 1 = B := by
            have : 1 ≤ B := le_trans (by norm_num) (le_trans hx1 hB)
            exact max_eq_left this
          have hxpos : 0 ≤ |x| := hx0
          have hx1' : (1 : ℝ) ≤ |x| := hx1
          have : B ≤ B * |x| := by
            have hBpos : 0 ≤ B := le_trans hx0 hB
            have := mul_le_mul_of_nonneg_left hx1' hBpos
            simpa [one_mul] using this
          aesop
    have hposM : 0 ≤ max B |x| := le_trans hx0 (le_max_right _ _)
    have hpow : (max B |x|)^k ≤ ((max B 1) * |x|)^k :=
      pow_le_pow_of_le_left hposM hmax
    have : ((max B 1) * |x|)^k = (max B 1)^k * |x|^k := by
      simp [mul_comm]
      exact mul_pow |x| (max B 1) k
    have hle : (max B |x|)^k ≤ (max B 1)^k * |x|^k :=
      by simpa [this] using hpow
    have hAbsorb : (max B 1)^k * |x|^k ≤ (max B 1)^k * (1 + |x|^k) := by
      have h1 : |x|^k ≤ 1 + |x|^k := by
        have : 0 ≤ |x|^k := pow_nonneg hx0 _
        linarith
      have hnon : 0 ≤ (max B 1)^k := by
        have : 0 ≤ max B 1 := by aesop
        exact pow_nonneg this _
      simp [mul_comm]
    exact le_trans hle hAbsorb

/-- Refined global domination (improved constant) for nonnegative `B`:
`(|x| + B)^k ≤ (2^k * (max B 1)^k) * (1 + |x|^k)`. -/
lemma pow_abs_add_const_global_refined
    (k : ℕ) {B x : ℝ} (hB : 0 ≤ B) :
    (|x| + B)^k ≤ (2 : ℝ)^k * (max B 1)^k * (1 + |x|^k) := by
  have h₁ := pow_abs_add_const_le_two_pow_mul_max_of_nonneg (B := B) (x := x) k hB
  have h₂ := max_pow_le_max1_pow_mul_one_add_abs_pow B x k
  have h₂' :
      (2 : ℝ)^k * (max B |x|)^k
        ≤ (2 : ℝ)^k * ((max B 1)^k * (1 + |x|^k)) :=
    mul_le_mul_of_nonneg_left h₂ (by positivity)
  have hChain :=
    le_trans h₁ h₂'
  simpa [mul_comm, mul_left_comm, mul_assoc] using hChain

/-- Existence version (with `B ≥ 0`) giving a constant `C` so that
`(|x| + B)^k ≤ C * (1 + |x|^k)`. -/
lemma pow_abs_add_const_global
    (k : ℕ) {B : ℝ} (hB : 0 ≤ B) :
  ∃ C > 0, ∀ x : ℝ, (|x| + B)^k ≤ C * (1 + |x|^k) := by
  let C := (2 : ℝ)^k * (max B 1)^k
  have hCpos : 0 < C := by
    have h1 : 0 < (2 : ℝ)^k := by positivity
    have h2 : 0 < (max B 1)^k := by
      have : 0 < max B 1 := by aesop
      exact pow_pos this _
    exact mul_pos h1 h2
  refine ⟨C, hCpos, ?_⟩
  intro x
  have h := pow_abs_add_const_global_refined k (B := B) (x := x) hB
  simpa [C, mul_comm, mul_left_comm, mul_assoc] using h
end Real

open Real

/-- Integrability of `|x|^k * exp (-a x^2)` for `a > 0`.  We obtain it from the
library lemma with *unsigned* monomial by taking absolute values. -/
lemma integrable_abs_pow_mul_exp_neg_mul_sq
    {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Integrable (fun x : ℝ => |x|^k * Real.exp (-a * x^2)) := by
  classical
  have hk : (-1 : ℝ) < (k : ℝ) := by
    have : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le _
    linarith
  have h := integrable_rpow_mul_exp_neg_mul_sq ha (s := (k : ℝ)) hk
  have h_norm : Integrable (fun x : ℝ => |x^(k : ℝ) * Real.exp (-a * x^2)|) := h.norm
  have hEq : (fun x : ℝ => |x|^k * Real.exp (-a * x^2))
           = (fun x : ℝ => |x^(k : ℝ) * Real.exp (-a * x^2)|) := by
    funext x
    have hx : 0 ≤ |x| := abs_nonneg _
    have hexp_pos : 0 < Real.exp (-a * x^2) := Real.exp_pos _
    rw [abs_mul, abs_of_pos hexp_pos]
    have h_rpow : |x^(k : ℝ)| = |x|^(k : ℝ) := by
      aesop
    rw [h_rpow]
    aesop
  rwa [hEq]

/-- Core Gaussian integrability block. -/
lemma integrable_exp_neg_mul_sq' {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp (-a * x^2)) := by
  simpa using integrable_exp_neg_mul_sq ha

/-- Helper (all `B : ℝ`): there is a constant `C > 0` with
`| (|x| + B)^k | ≤ C * (1 + |x|^k)`.  (Coarse global polynomial domination.) -/
lemma pow_abs_add_const_global_allB (k : ℕ) (B : ℝ) :
  ∃ C > 0, ∀ x : ℝ, |(|x| + B)^k| ≤ C * (1 + |x|^k) := by
  classical
  obtain ⟨C, hCpos, hDom⟩ :=
    Real.pow_abs_add_const_global (k := k) (B := |B|) (hB := abs_nonneg _)
  refine ⟨C, hCpos, ?_⟩
  intro x
  have h1 : |(|x| + B)^k| = |(|x| + B)| ^ k := by
    simp [abs_pow]
  have h2 : |(|x| + B)| ≤ |x| + |B| := by
    have := abs_add_le (|x|) B
    simpa using this
  have h2pow : |(|x| + B)| ^ k ≤ (|x| + |B|)^k :=
    pow_le_pow_left₀ (abs_nonneg _) h2 k
  have : |(|x| + B)^k| ≤ (|x| + |B|)^k := by simpa [h1]
  have hDom' := hDom x
  exact this.trans hDom'

/-- Main domination/integrability lemma:
`( |x| + B)^k * exp(-a x^2)` integrable for `a > 0`, any real `B`. -/
lemma integrable_polyShift_mul_exp_neg_mul_sq
    {a B : ℝ} (ha : 0 < a) (k : ℕ) :
    Integrable (fun x : ℝ => (|x| + B)^k * Real.exp (- a * x^2)) := by
  classical
  have hBase := integrable_exp_neg_mul_sq' (a := a) ha
  have hMoment := integrable_abs_pow_mul_exp_neg_mul_sq (a := a) ha k
  obtain ⟨C, hCpos, hDom⟩ := pow_abs_add_const_global_allB k B
  have hPoint :
      ∀ x, ‖(|x| + B)^k * Real.exp (-a * x^2)‖
          ≤ C * ( (1 + |x|^k) * Real.exp (-a * x^2)) := by
    intro x
    have hExpPos : 0 ≤ Real.exp (-a * x^2) := by positivity
    have hDom' : |(|x| + B)^k| ≤ C * (1 + |x|^k) := hDom x
    have : ‖(|x| + B)^k * Real.exp (-a * x^2)‖
            = |(|x| + B)^k| * Real.exp (-a * x^2) := by
      simp [Real.norm_eq_abs]
    have : |(|x| + B)^k| * Real.exp (-a * x^2)
          ≤ (C * (1 + |x|^k)) * Real.exp (-a * x^2) :=
      mul_le_mul_of_nonneg_right hDom' hExpPos
    simpa [this, mul_comm, mul_left_comm, mul_assoc]
  have hIntDom :
      Integrable (fun x : ℝ => (1 + |x|^k) * Real.exp (-a * x^2)) := by
    have hEq :
        (fun x : ℝ => (1 + |x|^k) * Real.exp (-a * x^2))
          = (fun x => Real.exp (-a * x^2))
            + (fun x => |x|^k * Real.exp (-a * x^2)) := by
      funext x; simp [add_mul]
    rw [hEq]
    exact hBase.add hMoment
  have hIntDomC :
      Integrable (fun x : ℝ => C * ((1 + |x|^k) * Real.exp (-a * x^2))) :=
    hIntDom.const_mul _
  refine hIntDomC.mono' ?_ (ae_of_all _ hPoint)
  have hMeasPoly : Measurable fun x : ℝ => (|x| + B)^k :=
    (measurable_abs.add measurable_const).pow_const _
  have hMeasExp : Measurable fun x : ℝ => Real.exp (-a * x^2) :=
    (Real.continuous_exp.comp
      (continuous_const.mul (continuous_id'.pow 2))).measurable
  exact (hMeasPoly.mul hMeasExp).aestronglyMeasurable

end PolyGaussianDomination

/-- Integrability of `( |x| + 2)^k * exp(-a x^2)` for `a > 0`. -/
lemma integrable_polynomial_exp_neg_mul_sq
    {k : ℕ} {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => (|x| + 2)^k * Real.exp (- a * x^2)) volume := by
  simpa using
    (integrable_polyShift_mul_exp_neg_mul_sq (a := a) (B := 2) ha k)

/-- Degenerate (variance = 0) real Gaussian is the Dirac mass at the mean.
(Provide this alias if missing in the snapshot.) -/
@[simp] lemma gaussianReal_dirac (μ : ℝ) :
    gaussianReal μ (0 : ℝ≥0) = Measure.dirac μ := by
  classical
  simp [gaussianReal]

open ProbabilityTheory

/-! ### Polynomial moment integrability -/

/-- Degenerate case: integrability of `(1 + |x|)^k` under the Dirac measure. -/
lemma gaussianReal_integrable_one_add_abs_pow_deg
    (k : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|)^k) (gaussianReal 0 (0 : ℝ≥0)) := by
  classical
  have : gaussianReal 0 (0 : ℝ≥0) = Measure.dirac 0 := by simp
  have hMeas : Measurable (fun x : ℝ => (1 + |x|)^k) :=
    (measurable_const.add measurable_abs).pow_const _
  simpa [this, abs_of_nonneg (show 0 ≤ (0:ℝ) by simp)] using
    Measure.integrable_dirac hMeas

/-- Explicit constants (decay rate `a` and normalizing factor `c`) giving the
centered Gaussian pdf as `c * exp(-a x^2)` in the non–degenerate case. -/
lemma gaussianPDF_centered_const_mul_exp
    {v : ℝ≥0} (hv : v ≠ 0) :
  let a : ℝ := 1 / (2 * (v : ℝ))
  let c : ℝ := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  (0 < a) ∧ (0 < c) ∧
    (∀ x : ℝ, gaussianPDF 0 v x = ENNReal.ofReal (c * Real.exp (- a * x^2))) := by
  classical
  intro a c
  have hvpos : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have ha : 0 < a := by
    have : 0 < 2 * (v : ℝ) := by nlinarith
    simp [a, one_div]
    aesop
  have hc : 0 < c := by
    have : 0 < Real.sqrt (2 * Real.pi * (v : ℝ)) := by
      have : 0 < 2 * Real.pi * (v : ℝ) := by
        have hπ : 0 < Real.pi := Real.pi_pos
        nlinarith
      exact Real.sqrt_pos.mpr this
    simp [c]
    aesop
  refine ⟨ha, hc, ?_⟩
  intro x
  simp [gaussianPDF, gaussianPDFReal, a, c, div_eq_mul_inv,
    mul_comm, mul_left_comm]

/-- Lebesgue–integrability of the polynomial times Gaussian kernel
`(1 + |x|)^k * exp (-a x^2)` for every `a > 0`. -/
lemma integrable_one_add_abs_pow_mul_exp
    {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|)^k * Real.exp (- a * x^2)) := by
  have hEq : (fun x : ℝ => (1 + |x|)^k * Real.exp (- a * x^2))
            = (fun x : ℝ => (|x| + 1)^k * Real.exp (- a * x^2)) := by
    funext x; simp [add_comm]
  have h := integrable_polyShift_mul_exp_neg_mul_sq
              (a := a) (B := 1) ha k
  aesop

section GaussianPolynomialMomentRewrite

variable {v : ℝ≥0} (hv : v ≠ 0) (k : ℕ)

private lemma gaussian_poly_pow_nonneg :
  ∀ x : ℝ, 0 ≤ (1 + |x|)^k := by
  intro x; exact pow_nonneg (by nlinarith [abs_nonneg x]) _

private lemma gaussian_poly_exp_nonneg
  {a : ℝ} : ∀ x : ℝ, 0 ≤ Real.exp (- a * x^2) := by
  intro x; positivity

/-- Unfold the (non–degenerate) centered Gaussian as a withDensity integral. -/
lemma lintegral_gaussian_poly_step1 (hv : v ≠ 0) (k : ℕ) :
  (∫⁻ x, (‖(1 + |x|)^k‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
    = ∫⁻ x, (‖(1 + |x|)^k‖₊ : ℝ≥0∞) * gaussianPDF 0 v x := by
  classical
  have hμ : gaussianReal 0 v = volume.withDensity (gaussianPDF 0 v) := by
    simp [gaussianReal, hv]
  have h_meas_poly :
      Measurable (fun x : ℝ => (‖(1 + |x|)^k‖₊ : ℝ≥0∞)) := by
    have hRew :
        (fun x : ℝ => (‖(1 + |x|)^k‖₊ : ℝ≥0∞))
          = fun x => ENNReal.ofReal ((1 + |x|)^k) := by
      funext x
      have hx : 0 ≤ (1 + |x|)^k :=
        (gaussian_poly_pow_nonneg (k := k) x)
      simp [Real.nnnorm_of_nonneg hx]; rw [← ENNReal.ofReal_eq_coe_nnreal]
    rw [hRew]
    exact ENNReal.measurable_ofReal.comp ((measurable_const.add measurable_abs).pow_const k)
  have h_meas_pdf : Measurable (gaussianPDF 0 v) :=
    measurable_gaussianPDF _ _
  rw [hμ]
  have h_eq :=
    lintegral_withDensity_eq_lintegral_mul volume
      h_meas_pdf
      h_meas_poly
  simpa [mul_comm, mul_left_comm, mul_assoc] using h_eq

/-- Rewrite the integral of the polynomial under the Gaussian
density by substituting the explicit `(a,c)` exponential form of the pdf. -/
lemma lintegral_gaussian_poly_step2
    (hv : v ≠ 0) (k : ℕ) :
  let a : ℝ := 1 / (2 * (v : ℝ))
  let c : ℝ := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  (∫⁻ x, (‖(1 + |x|)^k‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
    =
  ∫⁻ x,
    (‖(1 + |x|)^k‖₊ : ℝ≥0∞) *
      ENNReal.ofReal (c * Real.exp (- a * x^2)) := by
  classical
  intro a c
  have h₁ :=
    lintegral_gaussian_poly_step1
      (v := v) (hv := hv) (k := k)
  obtain ⟨_ha, _hc, hpdf⟩ :=
    gaussianPDF_centered_const_mul_exp (v := v) hv
  have h₂ :
      (∫⁻ x,
          (‖(1 + |x|)^k‖₊ : ℝ≥0∞) * gaussianPDF 0 v x)
        =
      ∫⁻ x,
          (‖(1 + |x|)^k‖₊ : ℝ≥0∞) *
            ENNReal.ofReal (c * Real.exp (- a * x^2)) := by
    aesop
  aesop

/-- For every non-negative real `r`, `ENNReal.ofReal r` coincides with the
corresponding coercion of the `nnnorm`.  (Tiny wrapper around
`Real.nnnorm_of_nonneg` / `ofReal_eq_coe_nnreal`.) -/
@[simp] lemma ofReal_eq_nnnorm {r : ℝ} (hr : 0 ≤ r) :
    (‖r‖₊ : ℝ≥0∞) = ENNReal.ofReal r := by
  rw [nnnorm_of_nonneg hr]; rw [← ENNReal.ofReal_eq_coe_nnreal]

/-- Splitting rule for `ofReal` on a non-negative product, with the *forward*
orientation that is more convenient for rewriting. -/
@[simp] lemma ofReal_mul'
    {a b : ℝ} (_ : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal (a * b) =
      ENNReal.ofReal a * ENNReal.ofReal b := by
  rw [ENNReal.ofReal_mul' hb]

/-- `nnnorm` of the polynomial–exponential product that appears in the
Gaussian moment lemmas.  Stated once and for all so that later proofs can
`rw [nnnorm_poly_exp]` instead of reproducing the same reasoning. -/
@[simp] lemma nnnorm_poly_exp
    {k : ℕ} {a x : ℝ} (hk : 0 ≤ (1 + |x|)^k)
    (h_exp : 0 ≤ Real.exp (-a * x^2)) :
    (‖((1 + |x|)^k * Real.exp (-a * x^2))‖₊ : ℝ≥0∞)
      = ENNReal.ofReal ((1 + |x|)^k * Real.exp (-a * x^2)) := by
  have h_nonneg : 0 ≤ (1 + |x|)^k * Real.exp (-a * x^2) :=
    mul_nonneg hk h_exp
  simpa [Real.norm_eq_abs, abs_of_nonneg h_nonneg]
    using ofReal_eq_nnnorm h_nonneg

/-- *pointwise* factorisation lemma.
It rewrites the product of the polynomial factor and the Gaussian kernel

    `‖(1+|x|)^k‖₊ ⋅ ofReal (c · exp (-a x²))`

as the product of the normalising constant `ofReal c` and the
`nnnorm` of the full polynomial–exponential factor. -/
lemma gaussian_poly_pointwise_factor
    {k : ℕ} {a c : ℝ} (hc_pos : 0 < c) :
    ∀ x : ℝ,
      (‖(1 + |x|)^k‖₊ : ℝ≥0∞) *
        ENNReal.ofReal (c * Real.exp (-a * x^2))
        =
      ENNReal.ofReal c *
        (‖((1 + |x|)^k * Real.exp (-a * x^2))‖₊ : ℝ≥0∞) := by
  intro x
  have h_pow_nonneg : 0 ≤ (1 + |x|) ^ k := by
    have : 0 ≤ (1 : ℝ) + |x| := by linarith [abs_nonneg x]
    exact pow_nonneg this _
  have h_exp_nonneg : 0 ≤ Real.exp (-a * x^2) := (Real.exp_pos _).le

  calc
    (‖(1 + |x|)^k‖₊ : ℝ≥0∞) * ENNReal.ofReal (c * Real.exp (-a * x^2))
      = ENNReal.ofReal ((1 + |x|)^k) * ENNReal.ofReal (c * Real.exp (-a * x^2)) := by
        rw [ofReal_eq_nnnorm h_pow_nonneg]
    _ = ENNReal.ofReal ((1 + |x|)^k) * (ENNReal.ofReal c * ENNReal.ofReal (Real.exp (-a * x^2))) := by
        rw [ofReal_mul' hc_pos.le h_exp_nonneg]
    _ = ENNReal.ofReal c * (ENNReal.ofReal ((1 + |x|)^k) * ENNReal.ofReal (Real.exp (-a * x^2))) := by
        rw [← mul_assoc, mul_comm (ENNReal.ofReal c)]; rw [mul_right_comm]
    _ = ENNReal.ofReal c * ENNReal.ofReal ((1 + |x|)^k * Real.exp (-a * x^2)) := by
        rw [← ofReal_mul' h_pow_nonneg h_exp_nonneg]
    _ = ENNReal.ofReal c * (‖((1 + |x|)^k * Real.exp (-a * x^2))‖₊ : ℝ≥0∞) := by
        rw [← nnnorm_poly_exp h_pow_nonneg h_exp_nonneg]

/-- Pull out the constant `c` from the Lebesgue integral. -/
lemma lintegral_gaussian_poly_step4
  {a c : ℝ} (_ : 0 < c) :
  (∫⁻ x,
     ENNReal.ofReal c *
       (‖((1 + |x|)^k * Real.exp (- a * x^2))‖₊ : ℝ≥0∞))
    =
  ENNReal.ofReal c *
    (∫⁻ x,
       (‖((1 + |x|)^k * Real.exp (- a * x^2))‖₊ : ℝ≥0∞)) := by
  classical
  have hpow : Measurable fun x : ℝ => (1 + |x|)^k :=
    (measurable_const.add measurable_abs).pow_const k
  have hExp : Measurable fun x : ℝ => Real.exp (- a * x^2) :=
    (Real.continuous_exp.comp
      (continuous_const.mul (continuous_id'.pow 2))).measurable
  have h_meas :
      Measurable (fun x : ℝ =>
        (‖((1 + |x|)^k * Real.exp (- a * x^2))‖₊ : ℝ≥0∞)) := by
    have hnon :
        (fun x : ℝ =>
          (‖((1 + |x|)^k * Real.exp (- a * x^2))‖₊ : ℝ≥0∞))
        =
        (fun x : ℝ =>
          ENNReal.ofReal ((1 + |x|)^k * Real.exp (- a * x^2))) := by
      funext x
      have : 0 ≤ (1 + |x|)^k * Real.exp (- a * x^2) := by
        have h1 : 0 ≤ (1 + |x|)^k :=
          pow_nonneg (by nlinarith [abs_nonneg x]) _
        have h2 : 0 ≤ Real.exp (- a * x^2) := by positivity
        exact mul_nonneg h1 h2
      rw [ofReal_eq_nnnorm this]
    rw [hnon]
    exact ENNReal.measurable_ofReal.comp (hpow.mul hExp)
  exact lintegral_const_mul _ h_meas

lemma lintegral_one_add_abs_pow_gaussian_rewrite
    (hv : v ≠ 0) (k : ℕ) :
  let a : ℝ := 1 / (2 * (v : ℝ))
  let c : ℝ := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  (∫⁻ x,
      (‖(1 + |x|)^k‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
    =
  ENNReal.ofReal c *
    (∫⁻ x,
      (‖((1 + |x|)^k * Real.exp (- a * x^2))‖₊ : ℝ≥0∞)) := by
  classical
  intro a c
  obtain ⟨ha, hc, hpdf⟩ := gaussianPDF_centered_const_mul_exp (v := v) hv
  have h2 := lintegral_gaussian_poly_step2 (v := v) hv k
  have hPoint :
      ∀ x : ℝ,
        (‖(1 + |x|)^k‖₊ : ℝ≥0∞) *
          ENNReal.ofReal (c * Real.exp (- a * x^2))
        =
        ENNReal.ofReal c *
          (‖((1 + |x|)^k * Real.exp (- a * x^2))‖₊ : ℝ≥0∞) :=
    gaussian_poly_pointwise_factor (k := k) (a := a) hc
  have h3 :
      ∫⁻ x,
        (‖(1 + |x|)^k‖₊ : ℝ≥0∞) *
          ENNReal.ofReal (c * Real.exp (- a * x^2))
        =
      ∫⁻ x,
        ENNReal.ofReal c *
          (‖((1 + |x|)^k * Real.exp (- a * x^2))‖₊ : ℝ≥0∞) :=
    lintegral_congr_ae (ae_of_all _ hPoint)
  have h4 := lintegral_gaussian_poly_step4 (k := k) (a := a) (c := c) hc
  calc
    (∫⁻ x, (‖(1 + |x|)^k‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
        =
      ∫⁻ x,
        (‖(1 + |x|)^k‖₊ : ℝ≥0∞) *
          ENNReal.ofReal (c * Real.exp (- a * x^2)) := h2
    _ =
      ∫⁻ x,
        ENNReal.ofReal c *
          (‖((1 + |x|)^k * Real.exp (- a * x^2))‖₊ : ℝ≥0∞) := h3
    _ =
      ENNReal.ofReal c *
        (∫⁻ x,
          (‖((1 + |x|)^k * Real.exp (- a * x^2))‖₊ : ℝ≥0∞)) := h4
end GaussianPolynomialMomentRewrite

/-- Final integrability lemma (non–degenerate centered Gaussian): the polynomial
moment `(1 + |x|)^k` has finite expectation under `gaussianReal 0 v`.  This is a
thin wrapper combining the preceding structural lemmas. -/
lemma gaussianReal_integrable_one_add_abs_pow_pos
    {v : ℝ≥0} (hv : v ≠ 0) (k : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|)^k) (gaussianReal 0 v) := by
  classical
  set a : ℝ := 1 / (2 * (v : ℝ))
  set c : ℝ := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  have hConsts := gaussianPDF_centered_const_mul_exp (v := v) hv
  rcases hConsts with ⟨ha, hc, hpdf⟩
  have hCore :
      Integrable (fun x : ℝ =>
          (1 + |x|)^k * Real.exp (- a * x^2)) :=
    integrable_one_add_abs_pow_mul_exp (a := a) ha k
  have hAEs :
      AEStronglyMeasurable (fun x : ℝ => (1 + |x|)^k) (gaussianReal 0 v) :=
    ((measurable_const.add measurable_abs).pow_const _).aestronglyMeasurable
  refine ⟨hAEs, ?_⟩
  have hRewrite :=
    lintegral_one_add_abs_pow_gaussian_rewrite (v := v) hv k
  have hCoreFin :
      (∫⁻ x,
        (‖((1 + |x|)^k * Real.exp (- a * x^2))‖₊ : ℝ≥0∞)) < ∞ := hCore.2
  have hcFin : (ENNReal.ofReal c) < ∞ := by
    simp
  have hProdFin :
      (ENNReal.ofReal c) *
        (∫⁻ x,
          (‖((1 + |x|)^k * Real.exp (- a * x^2))‖₊ : ℝ≥0∞)) < ∞ :=
    ENNReal.mul_lt_top hcFin hCoreFin
  have hLHSfin :
      (∫⁻ x, (‖(1 + |x|)^k‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v) < ∞ := by
    aesop
  exact hLHSfin

/-- Centered case: integrability of `(1 + |x|)^k` under the Gaussian measure. -/
lemma gaussianReal_integrable_one_add_abs_pow_centered
    (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|)^k) (gaussianReal 0 v) := by
  classical
  by_cases hv : v = 0
  · simpa [hv] using gaussianReal_integrable_one_add_abs_pow_deg k
  · exact gaussianReal_integrable_one_add_abs_pow_pos (v := v) hv k

/-- Shifted case: integrability of `(1 + |x - μ|)^k` under the Gaussian measure. -/
lemma gaussianReal_integrable_one_add_abs_pow_shift
    (μ : ℝ) (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => (1 + |x - μ|)^k) (gaussianReal μ v) := by
  classical
  have hmap :
      (gaussianReal 0 v).map (fun x => x + μ) = gaussianReal μ v :=
    by simpa using gaussianReal_map_add_const (μ := 0) (v := v) μ
  have hCent := gaussianReal_integrable_one_add_abs_pow_centered (v := v) k
  have hMeas :
      Measurable (fun y : ℝ => (1 + |y - μ|)^k) :=
    (measurable_const.add ((measurable_id.sub measurable_const).abs)).pow_const _
  refine ⟨hMeas.aestronglyMeasurable, ?_⟩
  have hg : Measurable (fun x : ℝ => x + μ) :=
    measurable_id.add measurable_const
  have hf :
      Measurable (fun y : ℝ =>
        (‖(1 + |y - μ|)^k‖₊ : ℝ≥0∞)) := by
    have hrew :
        (fun y : ℝ =>
          (‖(1 + |y - μ|)^k‖₊ : ℝ≥0∞))
        =
        (fun y : ℝ =>
          ENNReal.ofReal ((1 + |y - μ|)^k)) := by
      funext y
      have hy : 0 ≤ (1 + |y - μ|)^k := by
        have : 0 ≤ (1 : ℝ) + |y - μ| := by nlinarith [abs_nonneg (y - μ)]
        exact pow_nonneg this _
      simpa [Real.norm_eq_abs, abs_of_nonneg hy] using ofReal_eq_nnnorm hy
    rw [hrew]; rw [← hrew]; rw [hrew]
    simpa [hrew] using ENNReal.measurable_ofReal.comp hMeas
  have hlin :
      (∫⁻ y, (‖(1 + |y - μ|)^k‖₊ : ℝ≥0∞) ∂ gaussianReal μ v)
        =
      (∫⁻ x, (‖(1 + |(x + μ) - μ|)^k‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v) := by
    simpa [hmap, Function.comp] using
      (lintegral_map (μ := gaussianReal 0 v)
        (g := fun x : ℝ => x + μ)
        (f := fun y : ℝ => (‖(1 + |y - μ|)^k‖₊ : ℝ≥0∞))
        (hf := hf) (hg := hg))
  have hCentFin :
      (∫⁻ x, (‖(1 + |x|)^k‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v) < ∞ := hCent.2
  have hRHSfin :
      (∫⁻ x, (‖(1 + |(x + μ) - μ|)^k‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v) < ∞ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, add_neg_cancel] using hCentFin
  have hLHSfin :
      (∫⁻ y, (‖(1 + |y - μ|)^k‖₊ : ℝ≥0∞) ∂ gaussianReal μ v) < ∞ := by
    aesop
  exact hLHSfin

lemma gaussianReal_integrable_one_add_abs_pow
    (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => (1 + ‖x‖) ^ k) (gaussianReal 0 v) := by
  simpa [Real.norm_eq_abs] using
    gaussianReal_integrable_one_add_abs_pow_centered (v := v) k

/-! ### General polynomial × sub-Gaussian exponential integrability under a Gaussian law

We split `integrable_polynomial_exp_quadratic_gaussian` into higher–generality lemmas:
1) A parameterized lemma for non-degenerate Gaussians with any exponent `s < 1/(2v)`.
2) A wrapper that includes the degenerate Dirac case.
3) The original lemma as a short corollary with `s = 1/(4v)`.
-/

/-- Combine the exponents on `x^2`: `exp (s x^2) * exp (-(a) x^2) = exp (-(a - s) x^2)`. -/
private lemma exp_sq_combine (s a x : ℝ) :
  Real.exp (s * x^2) * Real.exp (-(a) * x^2) = Real.exp (-(a - s) * x^2) := by
  have hsum : s * x^2 + (-(a) * x^2) = (-(a - s)) * x^2 := by
    ring
  calc
    Real.exp (s * x^2) * Real.exp (-(a) * x^2)
        = Real.exp (s * x^2 + (-(a) * x^2)) := by
          simp [Real.exp_add]
    _ = Real.exp (-(a - s) * x^2) := by aesop


/-- Core integrability transfer (non-degenerate Gaussian):
Let `v ≠ 0`. Put `a := 1/(2v)`. If `s < a` and the Lebesgue integral of
`x ↦ g x * exp (-(a - s) x^2)` is finite, then
`x ↦ g x * exp (s x^2)` is integrable w.r.t. `gaussianReal 0 v`.

Only measurability of `g` and pointwise nonnegativity are required. -/
private lemma measurable_nnnorm_of_nonneg_of_measurable
    {f : ℝ → ℝ} (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) :
    Measurable (fun x : ℝ => (‖f x‖₊ : ℝ≥0∞)) := by
  have hRew :
      (fun x : ℝ => (‖f x‖₊ : ℝ≥0∞)) = fun x => ENNReal.ofReal (f x) := by
    funext x
    simpa [Real.norm_eq_abs, abs_of_nonneg (h0 x)]
      using ofReal_eq_nnnorm (h0 x)
  simpa [hRew] using ENNReal.measurable_ofReal.comp hf

/-- With-density rewrite of the L¹-seminorm under `gaussianReal 0 v` (non-degenerate). -/
private lemma lintegral_nnnorm_wrt_gaussian_eq_mul_pdf
    {v : ℝ≥0} (hv : v ≠ 0) {f : ℝ → ℝ}
    (h : Measurable (fun x => (‖f x‖₊ : ℝ≥0∞))) :
  (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
    =
  ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) * gaussianPDF 0 v x := by
  have hμ : gaussianReal 0 v = volume.withDensity (gaussianPDF 0 v) := by
    simp [gaussianReal, hv]
  have hEq :=
    lintegral_withDensity_eq_lintegral_mul volume
      (measurable_gaussianPDF 0 v) h
  simpa [hμ, mul_comm, mul_left_comm, mul_assoc] using hEq

/-- Pointwise factorization against the explicit Gaussian pdf kernel.
It pulls out the pdf normalizing constant and leaves a pure Lebesgue kernel. -/
private lemma gaussian_pdf_pointwise_factor
    {v : ℝ≥0} (_ : v ≠ 0)
    {g : ℝ → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    {s a c : ℝ}
    (hpdf :
      ∀ x : ℝ, gaussianPDF 0 v x = ENNReal.ofReal (c * Real.exp (-(a) * x^2))) :
  ∀ x : ℝ,
    (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) * gaussianPDF 0 v x
      =
    ENNReal.ofReal c *
      (‖(g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2)))‖₊ : ℝ≥0∞) := by
  intro x
  have h_exp2 : 0 ≤ Real.exp (-(a) * x^2) := (Real.exp_pos _).le
  have h_exp1 : 0 ≤ Real.exp (s * x^2) := (Real.exp_pos _).le
  have hf_nonneg : 0 ≤ g x * Real.exp (s * x^2) :=
    mul_nonneg (hg0 x) h_exp1
  have hpdfx := hpdf x
  calc
    (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) * gaussianPDF 0 v x
        = (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞)
            * ENNReal.ofReal (c * Real.exp (-(a) * x^2)) := by
          rw [hpdfx]
    _ = (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞)
            * (ENNReal.ofReal c * ENNReal.ofReal (Real.exp (-(a) * x^2))) := by
          rw [ENNReal.ofReal_mul' h_exp2]
    _ = ENNReal.ofReal c *
            ((‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞)
              * ENNReal.ofReal (Real.exp (-(a) * x^2))) := by
          rw [mul_left_comm]
    _ = ENNReal.ofReal c *
            (ENNReal.ofReal (g x * Real.exp (s * x^2))
              * ENNReal.ofReal (Real.exp (-(a) * x^2))) := by
          have hnn :
              (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞)
                = ENNReal.ofReal (g x * Real.exp (s * x^2)) := by
            rw [nnnorm_of_nonneg hf_nonneg, ← ENNReal.ofReal_eq_coe_nnreal]
          rw [hnn]
    _ = ENNReal.ofReal c *
            ENNReal.ofReal ((g x * Real.exp (s * x^2))
              * Real.exp (-(a) * x^2)) := by
          rw [← ENNReal.ofReal_mul' h_exp2]
    _ = ENNReal.ofReal c *
          ENNReal.ofReal (g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2))) := by
      have hassoc :
        (g x * Real.exp (s * x^2)) * Real.exp (-(a) * x^2)
          = g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2)) := by
        simp [mul_assoc]
      aesop
    _ = ENNReal.ofReal c *
          (‖(g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2)))‖₊ : ℝ≥0∞) := by
      have hnon :
        0 ≤ g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2)) :=
        mul_nonneg (hg0 x) (mul_nonneg h_exp1 h_exp2)
      have htoNN :
          ENNReal.ofReal (g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2)))
            = (‖(g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2)))‖₊ : ℝ≥0∞) := by
        rw [nnnorm_of_nonneg hnon, ← ENNReal.ofReal_eq_coe_nnreal]
      aesop

/-- Combine the two exponential factors on `x^2` inside the lintegrand. -/
private lemma lintegral_congr_exp_sq_combine
    {g : ℝ → ℝ} (hg0 : ∀ x, 0 ≤ g x) {s a : ℝ} :
  (∫⁻ x,
      (‖(g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2)))‖₊ : ℝ≥0∞))
    =
  (∫⁻ x, (‖(g x * Real.exp (-(a - s) * x^2))‖₊ : ℝ≥0∞)) := by
  apply lintegral_congr_ae
  refine ae_of_all _ ?_
  intro x
  have hposL : 0 ≤ Real.exp (s * x^2) * Real.exp (-(a) * x^2) := by positivity
  have hposR : 0 ≤ Real.exp (-(a - s) * x^2) := by positivity
  have hL :
      (‖(g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2)))‖₊ : ℝ≥0∞)
        =
      ENNReal.ofReal (g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2))) := by
    have : 0 ≤ g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2)) :=
      mul_nonneg (hg0 x) hposL
    simpa [Real.norm_eq_abs, abs_of_nonneg this] using ofReal_eq_nnnorm this
  have hR :
      (‖(g x * Real.exp (-(a - s) * x^2))‖₊ : ℝ≥0∞)
        =
      ENNReal.ofReal (g x * Real.exp (-(a - s) * x^2)) := by
    have : 0 ≤ g x * Real.exp (-(a - s) * x^2) :=
      mul_nonneg (hg0 x) hposR
    simpa [Real.norm_eq_abs, abs_of_nonneg this] using ofReal_eq_nnnorm this
  have hreal :
      g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2))
        = g x * Real.exp (-(a - s) * x^2) := by
    exact congrArg (fun t => g x * t) (exp_sq_combine s a x)
  calc
    (‖(g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2)))‖₊ : ℝ≥0∞)
        = ENNReal.ofReal (g x * (Real.exp (s * x^2) * Real.exp (-(a) * x^2))) := by
          rw [hL]
    _ = ENNReal.ofReal (g x * Real.exp (-(a - s) * x^2)) := by
          rw [hreal]
    _ = (‖(g x * Real.exp (-(a - s) * x^2))‖₊ : ℝ≥0∞) := by
          exact hR.symm

private lemma gaussian_tilt_lintegral_identity
    {v : ℝ≥0} (hv : v ≠ 0) {g : ℝ → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (s : ℝ) :
  ∃ (a c : ℝ) (_ : 0 < a) (_ : 0 < c),
    (∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
      =
    ENNReal.ofReal c *
      (∫⁻ x, (‖(g x * Real.exp (-(a - s) * x^2))‖₊ : ℝ≥0∞)) := by
  classical
  obtain ⟨ha_pos, hc_pos, hpdf⟩ := gaussianPDF_centered_const_mul_exp (v := v) hv
  refine ⟨(1 / (2 * (v : ℝ))), (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹, ?_, ?_, ?_⟩
  · simpa using ha_pos
  · simpa using hc_pos
  · have hExp : Measurable fun x : ℝ => Real.exp (s * x^2) :=
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id'.pow 2))).measurable
    have hMeas_f : Measurable (fun x : ℝ => (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞)) :=
      measurable_nnnorm_of_nonneg_of_measurable (hg.mul hExp) (by
        intro x; exact mul_nonneg (hg0 x) ((Real.exp_pos _).le))
    have hWD :
        (∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
          =
        ∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) * gaussianPDF 0 v x :=
      lintegral_nnnorm_wrt_gaussian_eq_mul_pdf (v := v) hv hMeas_f
    have hPoint := gaussian_pdf_pointwise_factor (v := v) hv (g := g) hg0
        (s := s) (a := (1 / (2 * (v : ℝ)))) (c := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) hpdf
    have hmeas_inner :
      Measurable (fun x : ℝ =>
        (‖(g x * (Real.exp (s * x^2) * Real.exp (-(1 / (2 * (v : ℝ))) * x^2)))‖₊ : ℝ≥0∞)) := by
      have hexp1 : Measurable fun x : ℝ => Real.exp (s * x^2) :=
        (Real.continuous_exp.comp (continuous_const.mul (continuous_id'.pow 2))).measurable
      have hexp2 : Measurable fun x : ℝ => Real.exp (-(1 / (2 * (v : ℝ))) * x^2) :=
        (Real.continuous_exp.comp (continuous_const.mul (continuous_id'.pow 2))).measurable
      have hreal : Measurable (fun x : ℝ =>
        g x * (Real.exp (s * x^2) * Real.exp (-(1 / (2 * (v : ℝ))) * x^2))) :=
        hg.mul (hexp1.mul hexp2)
      have hnon :
        ∀ x, 0 ≤ g x * (Real.exp (s * x^2) * Real.exp (-(1 / (2 * (v : ℝ))) * x^2)) := by
        intro x
        exact mul_nonneg (hg0 x) (mul_nonneg ((Real.exp_pos _).le) ((Real.exp_pos _).le))
      exact measurable_nnnorm_of_nonneg_of_measurable hreal hnon
    have hA :
        (∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
          =
        ENNReal.ofReal ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹)
          *
        (∫⁻ x,
          (‖(g x * (Real.exp (s * x^2)
                         * Real.exp (-(1 / (2 * (v : ℝ))) * x^2)))‖₊ : ℝ≥0∞)) := by
      calc
        (∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
            = ∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) * gaussianPDF 0 v x := hWD
        _ = ∫⁻ x,
              ENNReal.ofReal ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹)
                *
              (‖(g x * (Real.exp (s * x^2)
                        * Real.exp (-(1 / (2 * (v : ℝ))) * x^2)))‖₊ : ℝ≥0∞) := by
              refine lintegral_congr_ae (ae_of_all _ ?_); intro x; exact hPoint x
        _ =
            ENNReal.ofReal ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹)
              *
            (∫⁻ x,
              (‖(g x * (Real.exp (s * x^2)
                        * Real.exp (-(1 / (2 * (v : ℝ))) * x^2)))‖₊ : ℝ≥0∞)) := by
              exact lintegral_const_mul _ hmeas_inner
    have hLebInt :
        (∫⁻ x,
          (‖(g x * (Real.exp (s * x^2)
                        * Real.exp (-(1 / (2 * (v : ℝ))) * x^2)))‖₊ : ℝ≥0∞))
          =
        (∫⁻ x,
          (‖(g x * Real.exp (-((1 / (2 * (v : ℝ))) - s) * x^2))‖₊ : ℝ≥0∞)) := by
      simpa using
        (lintegral_congr_exp_sq_combine (g := g) hg0 (s := s) (a := (1 / (2 * (v : ℝ)))))
    aesop

/-- Core integrability transfer (non-degenerate Gaussian), refactored:
reduce Gaussian integrability to a Lebesgue integrability at decay `(a - s)`. -/
lemma integrable_subGaussian_tilt_gaussian_nondeg
    {v : ℝ≥0} (hv : v ≠ 0) {s : ℝ}
    (_ : s < 1 / (2 * (v : ℝ)))
    {g : ℝ → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hLeb :
      Integrable (fun x : ℝ =>
        g x * Real.exp (-(1 / (2 * (v : ℝ)) - s) * x^2))) :
    Integrable (fun x : ℝ => g x * Real.exp (s * x^2))
      (gaussianReal 0 v) := by
  classical
  have hMeas_f : Measurable (fun x : ℝ => g x * Real.exp (s * x^2)) :=
    hg.mul ((Real.continuous_exp.comp (continuous_const.mul (continuous_id'.pow 2))).measurable)
  obtain ⟨ha_pos, hc_pos, hpdf⟩ := gaussianPDF_centered_const_mul_exp (v := v) hv
  set a0 : ℝ := 1 / (2 * (v : ℝ)) with ha0_def
  set c0 : ℝ := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ with hc0_def
  have hExp : Measurable (fun x : ℝ => Real.exp (s * x^2)) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_id'.pow 2))).measurable
  have hMeas_nnn :
      Measurable (fun x : ℝ => (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞)) :=
    measurable_nnnorm_of_nonneg_of_measurable (hg.mul hExp) (by
      intro x; exact mul_nonneg (hg0 x) ((Real.exp_pos _).le))
  have hWD :
      (∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
        =
      ∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) * gaussianPDF 0 v x :=
    lintegral_nnnorm_wrt_gaussian_eq_mul_pdf (v := v) hv hMeas_nnn
  have hPoint :
      ∀ x : ℝ,
        (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) * gaussianPDF 0 v x
          =
        ENNReal.ofReal c0 *
          (‖(g x * (Real.exp (s * x^2) * Real.exp (-(a0) * x^2)))‖₊ : ℝ≥0∞) :=
    gaussian_pdf_pointwise_factor (v := v) hv (g := g) hg0
      (s := s) (a := a0) (c := c0) hpdf
  have hmeas_inner :
      Measurable (fun x : ℝ =>
        (‖(g x * (Real.exp (s * x^2) * Real.exp (-(a0) * x^2)))‖₊ : ℝ≥0∞)) := by
    have hexp1 : Measurable fun x : ℝ => Real.exp (s * x^2) :=
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id'.pow 2))).measurable
    have hexp2 : Measurable fun x : ℝ => Real.exp (-(a0) * x^2) :=
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id'.pow 2))).measurable
    have hreal : Measurable (fun x : ℝ =>
      g x * (Real.exp (s * x^2) * Real.exp (-(a0) * x^2))) :=
      hg.mul (hexp1.mul hexp2)
    have hnon :
        ∀ x, 0 ≤ g x * (Real.exp (s * x^2) * Real.exp (-(a0) * x^2)) := by
      intro x
      exact mul_nonneg (hg0 x) (mul_nonneg ((Real.exp_pos _).le) ((Real.exp_pos _).le))
    exact measurable_nnnorm_of_nonneg_of_measurable hreal hnon
  have hA :
      (∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
        =
      ENNReal.ofReal c0 *
        (∫⁻ x,
          (‖(g x * (Real.exp (s * x^2)
                       * Real.exp (-(a0) * x^2)))‖₊ : ℝ≥0∞)) := by
    calc
      (∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
          = ∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) * gaussianPDF 0 v x := hWD
      _ = ∫⁻ x,
            ENNReal.ofReal c0 *
            (‖(g x * (Real.exp (s * x^2)
                      * Real.exp (-(a0) * x^2)))‖₊ : ℝ≥0∞) := by
            refine lintegral_congr_ae (ae_of_all _ ?_); intro x; exact hPoint x
      _ =
          ENNReal.ofReal c0 *
          (∫⁻ x,
            (‖(g x * (Real.exp (s * x^2)
                      * Real.exp (-(a0) * x^2)))‖₊ : ℝ≥0∞)) := by
            exact lintegral_const_mul _ hmeas_inner
  have hLebInt :
      (∫⁻ x,
        (‖(g x * (Real.exp (s * x^2)
                      * Real.exp (-(a0) * x^2)))‖₊ : ℝ≥0∞))
        =
      (∫⁻ x,
        (‖(g x * Real.exp (-((a0) - s) * x^2))‖₊ : ℝ≥0∞)) := by
    simpa using
      (lintegral_congr_exp_sq_combine (g := g) hg0 (s := s) (a := a0))
  have hId :
      (∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v)
        =
      ENNReal.ofReal c0 *
        (∫⁻ x, (‖(g x * Real.exp (-(a0 - s) * x^2))‖₊ : ℝ≥0∞)) := by
    aesop
  have hLebFin :
      (∫⁻ x,
         (‖(g x * Real.exp (-(a0 - s) * x^2))‖₊ : ℝ≥0∞)) < ∞ := hLeb.2
  have hcFin : (ENNReal.ofReal c0) < ∞ := by simp
  have hGFin :
      (∫⁻ x, (‖(g x * Real.exp (s * x^2))‖₊ : ℝ≥0∞) ∂ gaussianReal 0 v) < ∞ := by
    rw [hId]
    exact ENNReal.mul_lt_top hcFin hLebFin
  exact ⟨hMeas_f.aestronglyMeasurable, hGFin⟩

/-- Corollary (non-degenerate): polynomial envelope `g x = (1 + |x|)^k`. -/
lemma integrable_polynomial_exp_sq_gaussian_param_nondeg
    {v : ℝ≥0} (hv : v ≠ 0) (k : ℕ) {s : ℝ}
    (hs : s < 1 / (2 * (v : ℝ))) :
    Integrable (fun x : ℝ => (1 + |x|)^k * Real.exp (s * x^2))
      (gaussianReal 0 v) := by
  classical
  let g : ℝ → ℝ := fun x => (1 + |x|)^k
  have hg : Measurable g :=
    (measurable_const.add measurable_abs).pow_const k
  have hg0 : ∀ x, 0 ≤ g x := by
    intro x; exact pow_nonneg (by nlinarith [abs_nonneg x]) _
  set a : ℝ := 1 / (2 * (v : ℝ))
  have hLeb :
      Integrable (fun x : ℝ => g x * Real.exp (-(a - s) * x^2)) := by
    have hapos : 0 < a - s := sub_pos.mpr hs
    simpa [g] using
      integrable_one_add_abs_pow_mul_exp (a := a - s) hapos k
  simpa [g] using
    integrable_subGaussian_tilt_gaussian_nondeg (v := v) hv hs hg hg0 hLeb

/-- Parameterized polynomial × sub-Gaussian exponential integrability under a centered Gaussian.
Works also in the degenerate (Dirac) case for any real `s`. -/
lemma integrable_polynomial_exp_sq_gaussian_param
    (v : ℝ≥0) (k : ℕ) (s : ℝ) :
    (v = 0 ∨ s < 1 / (2 * (v : ℝ))) →
    Integrable (fun x : ℝ => (1 + |x|)^k * Real.exp (s * x^2)) (gaussianReal 0 v) := by
  classical
  intro hcond
  by_cases hv : v = 0
  · subst hv
    have hdirac : gaussianReal 0 (0 : ℝ≥0) = Measure.dirac 0 := by simp
    have hMeas : Measurable (fun x : ℝ => (1 + |x|)^k * Real.exp (s * x^2)) := by
      have hPoly : Measurable fun x : ℝ => (1 + |x|)^k :=
        (measurable_const.add measurable_abs).pow_const _
      have hExp : Measurable fun x : ℝ => Real.exp (s * x^2) :=
        (Real.continuous_exp.comp (continuous_const.mul (continuous_id'.pow 2))).measurable
      exact hPoly.mul hExp
    have : Integrable (fun x : ℝ => (1 + |x|)^k * Real.exp (s * x^2)) (Measure.dirac 0) :=
      Measure.integrable_dirac hMeas
    simpa [hdirac] using this
  · rcases hcond with hv0 | hs
    · exact False.elim (hv hv0)
    · exact integrable_polynomial_exp_sq_gaussian_param_nondeg hv k hs

lemma integrable_polynomial_exp_quadratic_gaussian
    (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|)^k * Real.exp (|x|^2 / (4 * (v:ℝ))))
      (gaussianReal 0 v) := by
  classical
  by_cases hv : v = 0
  · have : Integrable (fun x : ℝ =>
                (1 + |x|)^k * Real.exp ((1 / (4 * (v:ℝ))) * x^2)) (gaussianReal 0 v) := by
      refine integrable_polynomial_exp_sq_gaussian_param v k (1 / (4 * (v:ℝ))) (Or.inl hv)
    have hAbsSq : ∀ x : ℝ, |x|^2 = x^2 := by
      intro x; simp [pow_two]
    simpa [div_eq_mul_inv, hAbsSq, mul_comm, mul_left_comm, mul_assoc] using this
  · have hvpos : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
    have h4v_pos : 0 < 4 * (v : ℝ) := by nlinarith
    have h2v_pos : 0 < 2 * (v : ℝ) := by nlinarith
    have hs : (1 / (4 * (v : ℝ))) < (1 / (2 * (v : ℝ))) := by
      have hlt : 2 * (v : ℝ) < 4 * (v : ℝ) := by nlinarith
      simpa [one_div] using (one_div_lt_one_div_of_lt h2v_pos hlt)
    have : Integrable (fun x : ℝ =>
                (1 + |x|)^k * Real.exp ((1 / (4 * (v:ℝ))) * x^2)) (gaussianReal 0 v) := by
      refine integrable_polynomial_exp_sq_gaussian_param v k (1 / (4 * (v:ℝ))) (Or.inr ?_)
      simpa [one_div] using hs
    have hAbsSq : ∀ x : ℝ, |x|^2 = x^2 := by
      intro x; simp [pow_two]
    simpa [div_eq_mul_inv, hAbsSq, mul_comm, mul_left_comm, mul_assoc] using this

/-- Main integrability upgrade lemma (state-of-art, no placeholders):
we assume moderate growth of `F`. Then for every `δ > 0`,
  x ↦ |F x| (|x|+1) exp(δ|x|)
is integrable under the centered Gaussian `gaussianReal 0 v` (for any variance `v`).
If `v = 0` (degenerate Gaussian) this is immediate; otherwise we use the
quadratic domination `exp(δ|x|) ≤ exp(v δ^2) * exp(|x|^2/(4v))`
combined with the polynomial bound on `F`. -/
lemma integrable_dom_profile_of_moderateGrowth
    {F : ℝ → ℝ} (hF : HasModerateGrowth F)
    (v : ℝ≥0) (δ : ℝ) (_ : 0 < δ)
    (hFmeas : Measurable F) :
    Integrable (fun x => |F x| * (|x| + 1) * Real.exp (δ * |x|))
      (gaussianReal 0 v) := by
  classical
  by_cases hv : v = 0
  · have hdirac : gaussianReal 0 v = Measure.dirac 0 := by
      simp [hv]
    have hMeas :
        Measurable (fun x : ℝ =>
          |F x| * (|x| + 1) * Real.exp (δ * |x|)) := by
      have hFabs : Measurable fun x : ℝ => |F x| := hFmeas.abs
      have hAbs  : Measurable fun x : ℝ => |x|     := measurable_abs
      have hLin  : Measurable fun x : ℝ => |x| + 1 := hAbs.add measurable_const
      have hExp  : Measurable fun x : ℝ => Real.exp (δ * |x|) :=
        (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).measurable
      simpa [mul_comm, mul_left_comm, mul_assoc]
        using ((hFabs.mul hLin).mul hExp)
    simpa [hdirac] using Measure.integrable_dirac hMeas
  · rcases HasModerateGrowth.bound_F_mul_linear (F := F) hF with
      ⟨C, m, hCpos, hBound⟩
    have hExpDom := exp_abs_linear_le_gaussian_aux δ v hv
    have hAE :
        ∀ᵐ x ∂ gaussianReal 0 v,
          |F x| * (|x| + 1) * Real.exp (δ * |x|)
            ≤ (C * Real.exp ((v:ℝ) * δ^2))
              * (1 + |x|)^(m+1) * Real.exp (|x|^2 / (4 * (v:ℝ))) := by
      refine ae_of_all _ ?_
      intro x
      have h1 := hBound x
      have h2 := hExpDom x
      have hposExp : 0 ≤ Real.exp (δ * |x|) := by positivity
      calc
        |F x| * (|x| + 1) * Real.exp (δ * |x|)
            ≤ (C * (1 + |x|)^(m+1)) * Real.exp (δ * |x|) :=
              (mul_le_mul_of_nonneg_right h1 hposExp)
        _ ≤ (C * (1 + |x|)^(m+1)) *
              (Real.exp ((v:ℝ) * δ^2) * Real.exp (|x|^2 / (4 * (v:ℝ)))) :=
            (mul_le_mul_of_nonneg_left h2 (by positivity))
        _ = (C * Real.exp ((v:ℝ) * δ^2)) * (1 + |x|)^(m+1)
              * Real.exp (|x|^2 / (4 * (v:ℝ))) := by
              ring_nf
    have hDomInt :
        Integrable (fun x =>
          (C * Real.exp ((v:ℝ) * δ^2)) * (1 + |x|)^(m+1)
              * Real.exp (|x|^2 / (4 * (v:ℝ))))
          (gaussianReal 0 v) := by
      have hpoly := integrable_polynomial_exp_quadratic_gaussian v (m+1)
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        hpoly.const_mul (C * Real.exp ((v:ℝ) * δ^2))
    have hAE_norm :
        ∀ᵐ x ∂ gaussianReal 0 v,
          ‖|F x| * (|x| + 1) * Real.exp (δ * |x|)‖
            ≤ (C * Real.exp ((v:ℝ) * δ^2))
              * (1 + |x|)^(m+1) * Real.exp (|x|^2 / (4 * (v:ℝ))) := by
      refine hAE.mono ?_
      intro x hx
      have hnon : 0 ≤ |F x| * (|x| + 1) * Real.exp (δ * |x|) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnon]
      exact hx
    have hFabs : Measurable fun x : ℝ => |F x| := hFmeas.abs
    have hAbs : Measurable fun x : ℝ => |x| := measurable_abs
    have hLin : Measurable fun x : ℝ => |x| + 1 := hAbs.add measurable_const
    have hExp : Measurable fun x : ℝ => Real.exp (δ * |x|) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).measurable
    have hMeas :
        Measurable (fun x : ℝ => |F x| * (|x| + 1) * Real.exp (δ * |x|)) :=
      (hFabs.mul hLin).mul hExp
    refine hDomInt.mono' hMeas.aestronglyMeasurable hAE_norm

lemma integrable_dom_profile
    {F : ℝ → ℝ} (hF : HasModerateGrowth F)
    (v : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) (hFmeas : Measurable F) :
    Integrable (fun x => |F x| * (|x| + 1) * Real.exp (δ * |x|))
      (gaussianReal 0 v) :=
  integrable_dom_profile_of_moderateGrowth hF v δ hδ hFmeas

end YoungBounds
end YoungBounds
end DominationExponentialUpgrade

/-- Domination near zero for the *difference quotient* of the Gaussian tilt integrand.
Requires an explicit integrability assumption on the Gaussian law of the exponential–moment
profile.  This is the version appropriate for a mathlib-quality proof of differentiation
under the integral sign. -/
lemma gaussianTilt_diffquot_dom_integrable
    {v : ℝ≥0} {F : ℝ → ℝ}
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hInt : Integrable (fun x => |F x| * (|x| + 1) * Real.exp (δ * |x|)) (gaussianReal 0 v))
    (hFmeas : Measurable F) :
  ∀ᶠ t in 𝓝 (0 : ℝ),
    |t| ≤ δ ∧
    Integrable (fun x =>
      |(F x * tiltKernel v t x - F x) / t|) (gaussianReal 0 v) := by
  have hdom := gaussianTilt_diffquot_dom (v := v) (F := F) δ hδ₀ hδ₁
  refine hdom.mono ?_
  intro t ht
  refine And.intro ht.left ?_
  have hPoint :
      ∀ x, |(F x * tiltKernel v t x - F x) / t|
          ≤ |F x| * (|x| + (v:ℝ) * δ / 2) * Real.exp ((v:ℝ) * δ / 2) * Real.exp (δ * |x|) := ht.right
  have hC :
      ∀ x, (|x| + (v:ℝ) * δ / 2) ≤ ((v:ℝ) * δ / 2 + 1) * (|x| + 1) := by
    intro x
    have hx : 0 ≤ |x| := abs_nonneg _
    have hvδ : 0 ≤ (v:ℝ) * δ / 2 := by
      have hv0 : 0 ≤ (v:ℝ) := v.property
      have hδ0 : 0 ≤ δ := le_of_lt hδ₀
      nlinarith
    have : |x| + (v:ℝ) * δ / 2 ≤ (|x| + 1) + ((v:ℝ) * δ / 2) * (|x| + 1) := by
      have h1 : |x| ≤ |x| + 1 := by nlinarith
      have h2 : (v:ℝ) * δ / 2 ≤ ((v:ℝ) * δ / 2) * (|x| + 1) := by
        have hpos : 0 ≤ |x| + 1 := by nlinarith
        nlinarith
      nlinarith
    have hfac :
        (|x| + 1) + ((v:ℝ) * δ / 2) * (|x| + 1)
          = ((v:ℝ) * δ / 2 + 1) * (|x| + 1) := by ring
    simpa [hfac]
  have hDomInt :
      Integrable (fun x =>
        |F x| * ((v:ℝ) * δ / 2 + 1) * Real.exp ((v:ℝ) * δ / 2) * (|x| + 1) * Real.exp (δ * |x|))
        (gaussianReal 0 v) := by
    have := hInt.const_mul (((v:ℝ) * δ / 2 + 1) * Real.exp ((v:ℝ) * δ / 2))
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hMeas_tilt : Measurable fun x : ℝ => tiltKernel v t x := by
    have hInner : Continuous fun x : ℝ => t * x - (v:ℝ) * t^2 / 2 :=
      (continuous_const.mul continuous_id).sub continuous_const
    exact (Real.continuous_exp.comp hInner).measurable
  have hAEs_meas :
      AEStronglyMeasurable
        (fun x => |(F x * tiltKernel v t x - F x) / t|) (gaussianReal 0 v) := by
    have hProd : Measurable (fun x : ℝ => F x * tiltKernel v t x) := hFmeas.mul hMeas_tilt
    have hDiff : Measurable (fun x : ℝ => F x * tiltKernel v t x - F x) := hProd.sub hFmeas
    have hQuot : Measurable (fun x : ℝ => (F x * tiltKernel v t x - F x) / t) := Measurable.div_const hDiff t
    exact hQuot.abs.aestronglyMeasurable
  have hAE :
      ∀ᵐ x ∂ gaussianReal 0 v,
        |(F x * tiltKernel v t x - F x) / t|
          ≤ |F x| * ((v:ℝ) * δ / 2 + 1) * Real.exp ((v:ℝ) * δ / 2) * (|x| + 1) * Real.exp (δ * |x|) := by
    refine ae_of_all _ ?_
    intro x
    have hpt := hPoint x
    have hxC := hC x
    have hposExp1 : 0 ≤ Real.exp (δ * |x|) := by positivity
    have hposExp2 : 0 ≤ Real.exp ((v:ℝ) * δ / 2) := by positivity
    have hposF   : 0 ≤ |F x| := abs_nonneg _
    have hxC' :
        |F x| * (|x| + (v:ℝ) * δ / 2) * Real.exp ((v:ℝ) * δ / 2) * Real.exp (δ * |x|)
          ≤ |F x| * ((v:ℝ) * δ / 2 + 1) * Real.exp ((v:ℝ) * δ / 2) * (|x| + 1) * Real.exp (δ * |x|) := by
      have h1 := mul_le_mul_of_nonneg_left hxC hposF
      have h2 := mul_le_mul_of_nonneg_right h1 hposExp2
      have h3 := mul_le_mul_of_nonneg_right h2 hposExp1
      simpa [mul_comm, mul_left_comm, mul_assoc] using h3
    exact hpt.trans hxC'
  have hAE_norm :
      ∀ᵐ x ∂ gaussianReal 0 v,
        ‖|(F x * tiltKernel v t x - F x) / t|‖
          ≤ |F x| * ((v:ℝ) * δ / 2 + 1) * Real.exp ((v:ℝ) * δ / 2) * (|x| + 1) * Real.exp (δ * |x|) := by
    simpa [Real.norm_eq_abs, abs_abs] using hAE
  exact hDomInt.mono' hAEs_meas hAE_norm

/-- Map of a measure by subtraction of a constant. -/
lemma Measure.map_sub_right {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ} (hf : Measurable f) (c : ℝ) :
    μ.map (fun x => f x - c) = (μ.map f).map (· - c) := by
  have hg : Measurable (fun x : ℝ => x - c) :=
    (continuous_id.sub continuous_const).measurable
  simpa [Function.comp] using
    (Measure.map_map (μ := μ) (f := f) (g := fun x : ℝ => x - c) (hf := hf) (hg := hg)).symm


/-- Auxiliary integrability lemma: if both `x ↦ x * F x` and `x ↦ F x`
are integrable under `gaussianReal 0 v`, then any function dominated by
`x ↦ |x * F x| + |F x|` is integrable. -/
lemma Integrable.of_bound_gaussianTilt
    {F : ℝ → ℝ} {v : ℝ≥0}
    (h1 : Integrable (fun x => x * F x) (gaussianReal 0 v))
    (h2 : Integrable (fun x => F x) (gaussianReal 0 v))
    {g : ℝ → ℝ}
    (hg_meas : AEStronglyMeasurable g (gaussianReal 0 v))
    (hg : ∀ᵐ x ∂ gaussianReal 0 v,
      |g x| ≤ |x * F x| + |F x|) :
    Integrable g (gaussianReal 0 v) := by
  have h12 : Integrable (fun x => |x * F x| + |F x|) (gaussianReal 0 v) :=
    (h1.abs.add h2.abs)
  exact h12.mono' hg_meas (hg.mono (by intro x hx; exact hx))

/-- Pointwise derivative bundled as a measurability statement (for use with
parametric integral differentiation lemmas). -/
lemma aestronglyMeasurable_deriv_integrand
    {F : ℝ → ℝ} {v : ℝ≥0}
    (hF : ContDiff ℝ 1 F) :
  AEStronglyMeasurable
    (fun x => F x * x) (gaussianReal 0 v) := by
  have hcont : Continuous F := (hF.continuous)
  have hmeas : Measurable F := hcont.measurable
  have : Measurable (fun x : ℝ => F x * x) :=
    (hmeas.mul measurable_id)
  exact this.aestronglyMeasurable

/-- The Gaussian tilt kernel is nonnegative everywhere. -/
lemma tiltKernel_nonneg (v : ℝ≥0) (t x : ℝ) : 0 ≤ tiltKernel v t x := by
  have : 0 < Real.exp (t * x - (v:ℝ) * t^2 / 2) := Real.exp_pos _
  simpa [tiltKernel] using this.le

lemma gaussianTilt_deriv_dom_bound
    {v : ℝ≥0} (δ : ℝ) (hδ_pos : 0 < δ)
    {F : ℝ → ℝ}
    (t : ℝ) (ht : |t| ≤ δ) (x : ℝ) :
  |F x * (x - (v:ℝ) * t) * tiltKernel v t x|
    ≤ |F x| * ((|(v:ℝ)| * δ) + 1) * (|x| + 1) * Real.exp (δ * |x|) := by
  -- 1) triangle: |x - v t| ≤ |x| + |v| |t|
  have h1 : |x - (v:ℝ) * t| ≤ |x| + |(v:ℝ)| * |t| := by
    have := abs_add_le_abs_add_abs x (-(v:ℝ) * t)
    simpa [sub_eq_add_neg, abs_mul, abs_neg, mul_comm, mul_left_comm, mul_assoc] using this
  -- 2) bound |t| by δ
  have h1' : |x - (v:ℝ) * t| ≤ |x| + |(v:ℝ)| * δ := by
    have hvabs : 0 ≤ |(v:ℝ)| := abs_nonneg _
    have hvd : |(v:ℝ)| * |t| ≤ |(v:ℝ)| * δ :=
      mul_le_mul_of_nonneg_left ht hvabs
    exact le_trans h1 (by linarith)
  -- 3) kernel bound: tiltKernel ≤ exp(|t| |x|) ≤ exp(δ |x|)
  have h2 : tiltKernel v t x ≤ Real.exp (|t| * |x|) :=
    tiltKernel_le_exp_abs v t x
  have h2' : tiltKernel v t x ≤ Real.exp (δ * |x|) := by
    have hmul : |t| * |x| ≤ δ * |x| :=
      mul_le_mul_of_nonneg_right ht (abs_nonneg _)
    exact le_trans h2 (by
      simpa using (Real.exp_le_exp.mpr (by simpa [mul_comm] using hmul)))
  -- 4) absorb linear term: |x| + |v| δ ≤ ((|v| δ)+1)(|x|+1)
  have h3 : (|x| + |(v:ℝ)| * δ) ≤ ((|(v:ℝ)| * δ) + 1) * (|x| + 1) := by
    have hx : 0 ≤ |x| := abs_nonneg _
    have hvδ : 0 ≤ |(v:ℝ)| * δ :=
      mul_nonneg (abs_nonneg _) (le_of_lt hδ_pos)
    nlinarith
  -- 5) we chain multiplicative inequalities with explicit nonnegativity
  have hF_nonneg : 0 ≤ |F x| := abs_nonneg _
  have hK_nonneg : 0 ≤ tiltKernel v t x := tiltKernel_nonneg v t x
  have hExpNonneg : 0 ≤ Real.exp (δ * |x|) := by positivity
  have hxvδ_nonneg : 0 ≤ |x| + |(v:ℝ)| * δ := by nlinarith [abs_nonneg x, abs_nonneg (v:ℝ), hδ_pos.le]
  calc
    |F x * (x - (v:ℝ) * t) * tiltKernel v t x|
        = |F x| * |x - (v:ℝ) * t| * tiltKernel v t x := by
            simp [abs_mul, mul_comm, mul_assoc]
    _ ≤ |F x| * (|x| + |(v:ℝ)| * δ) * tiltKernel v t x := by
          have : |F x| * |x - (v:ℝ) * t| ≤ |F x| * (|x| + |(v:ℝ)| * δ) :=
            mul_le_mul_of_nonneg_left h1' hF_nonneg
          exact mul_le_mul_of_nonneg_right this hK_nonneg
    _ ≤ |F x| * (|x| + |(v:ℝ)| * δ) * Real.exp (δ * |x|) := by
          have hKexp : tiltKernel v t x ≤ Real.exp (δ * |x|) := h2'
          have hconst_nonneg :
              0 ≤ |F x| * (|x| + |(v:ℝ)| * δ) := by
            nlinarith [hF_nonneg, hxvδ_nonneg]
          have := mul_le_mul_of_nonneg_left hKexp hconst_nonneg
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
    _ ≤ |F x| * (((|(v:ℝ)| * δ) + 1) * (|x| + 1)) * Real.exp (δ * |x|) := by
          have : (|x| + |(v:ℝ)| * δ) ≤ ((|(v:ℝ)| * δ) + 1) * (|x| + 1) := h3
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left this hF_nonneg)
            hExpNonneg
    _ = |F x| * ((|(v:ℝ)| * δ) + 1) * (|x| + 1) * Real.exp (δ * |x|) := by
          ring_nf

lemma gaussianTilt_domination_bound
    {v : ℝ≥0} (δ : ℝ) (hδ_pos : 0 < δ)
    {F : ℝ → ℝ} (hF : HasModerateGrowth F) (hF_cont : Continuous F) :
    Integrable (fun x => |F x| * ((|(v:ℝ)| * δ) + 1) * (|x| + 1) * Real.exp (δ * |x|))
      (gaussianReal 0 v) := by
  have hInt := integrable_dom_profile_of_moderateGrowth hF v δ hδ_pos hF_cont.measurable
  convert hInt.const_mul (((|(v:ℝ)|) * δ) + 1) using 1
  funext x; ring

/-- AEStronglyMeasurable of the `t`-tilted integrand in `x` from measurability of `F`. -/
lemma aestronglyMeasurable_gaussianTilt_integrand_of_measurable
    {v : ℝ≥0} {F : ℝ → ℝ} (hFmeas : Measurable F) :
  ∀ t, AEStronglyMeasurable (fun x => F x * tiltKernel v t x) (gaussianReal 0 v) := by
  intro t
  have hTilt : Measurable (fun x => tiltKernel v t x) :=
    (Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).sub continuous_const)).measurable
  exact (hFmeas.mul hTilt).aestronglyMeasurable

/-- AEStronglyMeasurable of the “derivative-at-0” integrand `x ↦ F x * x`
under the Gaussian (only measurability of `F`). -/
lemma aestronglyMeasurable_F_mul_id_of_measurable
    {v : ℝ≥0} {F : ℝ → ℝ} (hFmeas : Measurable F) :
  AEStronglyMeasurable (fun x => F x * x) (gaussianReal 0 v) := by
  exact (hFmeas.mul measurable_id).aestronglyMeasurable

/-- Local dominated-differentiation lemma for the left tilt (general).-/
lemma gaussianTilt_hasDerivAt_left_of_dominated
    {v : ℝ≥0} {F : ℝ → ℝ}
    (hFmeas : Measurable F)
    {δ : ℝ} (hδ_pos : 0 < δ)
    (B : ℝ → ℝ)
    (hB_int : Integrable B (gaussianReal 0 v))
    (hBound :
      ∀ᵐ x ∂ gaussianReal 0 v,
        ∀ t ∈ Metric.ball (0 : ℝ) δ,
          ‖F x * (x - (v : ℝ) * t) * tiltKernel v t x‖ ≤ B x)
    (hF_int : Integrable (fun x => F x) (gaussianReal 0 v)) :
  HasDerivAt (gaussianTilt F v) (∫ x, x * F x ∂ gaussianReal 0 v) 0 := by
  set G  : ℝ → ℝ → ℝ := fun t x => F x * tiltKernel v t x
  set G' : ℝ → ℝ → ℝ := fun t x => F x * (x - (v : ℝ) * t) * tiltKernel v t x
  have hG_meas : ∀ t, AEStronglyMeasurable (G t) (gaussianReal 0 v) :=
    aestronglyMeasurable_gaussianTilt_integrand_of_measurable (v := v) (F := F) hFmeas
  have hG0_int : Integrable (G 0) (gaussianReal 0 v) := by
    simpa [G, tiltKernel] using hF_int
  have hGp0_meas : AEStronglyMeasurable (G' 0) (gaussianReal 0 v) := by
    have : (fun x => G' 0 x) = (fun x => F x * x) := by
      funext x; simp [G', tiltKernel]
    simpa [this] using aestronglyMeasurable_F_mul_id_of_measurable (v := v) (F := F) hFmeas
  have h_bound :
      ∀ᵐ x ∂ gaussianReal 0 v,
        ∀ t ∈ Metric.ball (0 : ℝ) δ, ‖G' t x‖ ≤ B x := by
    simpa [G'] using hBound
  have h_diff :
      ∀ᵐ x ∂ gaussianReal 0 v,
        ∀ t ∈ Metric.ball (0 : ℝ) δ, HasDerivAt (fun s => G s x) (G' t x) t := by
    refine ae_of_all _ ?_
    intro x t _
    simpa [G, G'] using hasDerivAt_gaussianTiltIntegrand (v := v) (F := F) (x := x) (t := t)
  have hDer :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ              := gaussianReal 0 v)
      (F              := G)
      (F'             := G')
      (ε_pos          := hδ_pos)
      (hF_meas        := Eventually.of_forall hG_meas)
      (hF_int         := hG0_int)
      (hF'_meas       := hGp0_meas)
      (h_bound        := h_bound)
      (bound_integrable := hB_int)
      (h_diff         := h_diff)
  simpa [gaussianTilt, G, G', tiltKernel, mul_comm] using hDer.2

lemma gaussianTilt_hasDerivAt_left
    {v : ℝ≥0} (_ : v ≠ 0) {F : ℝ → ℝ}
    (hF  : ContDiff ℝ 1 F)
    (hMod : HasModerateGrowth F) :
    HasDerivAt (gaussianTilt F v)
      (∫ x, x * F x ∂ gaussianReal 0 v) 0 := by
  -- We work with the ball of radius 1 around 0 in `t`.
  let δ : ℝ := 1
  have hδ_pos : 0 < δ := by norm_num
  let B : ℝ → ℝ :=
    fun x => |F x| * ((|(v : ℝ)| * δ) + 1) * (|x| + 1) * Real.exp (δ * |x|)
  have hBound :
      ∀ᵐ x ∂ gaussianReal 0 v,
        ∀ t ∈ Metric.ball (0 : ℝ) δ,
          ‖F x * (x - (v : ℝ) * t) * tiltKernel v t x‖ ≤ B x := by
    refine ae_of_all _ ?_
    intro x t ht
    have ht' : |t| ≤ δ := (mem_ball_zero_iff.mp ht).le
    have h := gaussianTilt_deriv_dom_bound (v := v) (F := F) δ hδ_pos t ht' x
    exact h
  have hB_int :
      Integrable B (gaussianReal 0 v) := by
    simpa [B] using
      gaussianTilt_domination_bound (v := v) (F := F) δ hδ_pos hMod hF.continuous
  have hFmeas : Measurable F := hF.continuous.measurable
  have hG0_int : Integrable (fun x => F x) (gaussianReal 0 v) := by
    have h1 : ∀ x, ‖F x‖ ≤ B x := by
      intro x
      have hGe1_A : 1 ≤ (|(v : ℝ)| * δ + 1) := by
        have hvn : 0 ≤ |(v : ℝ)| * δ := by
          have hvn' : 0 ≤ |(v : ℝ)| := abs_nonneg (v : ℝ)
          have hδn : 0 ≤ δ := le_of_lt hδ_pos
          exact mul_nonneg hvn' hδn
        nlinarith
      have hGe1_B : 1 ≤ |x| + 1 := by nlinarith [abs_nonneg x]
      have hGe1_C : 1 ≤ Real.exp (δ * |x|) := by
        have : 0 ≤ δ * |x| := by
          have hδn : 0 ≤ δ := le_of_lt hδ_pos
          exact mul_nonneg hδn (abs_nonneg _)
        simpa using Real.one_le_exp_iff.mpr this
      have hAB : 1 ≤ ((|(v : ℝ)| * δ + 1) * (|x| + 1)) :=
        one_le_mul_of_one_le_of_one_le hGe1_A hGe1_B
      have hABC : 1 ≤ ((|(v : ℝ)| * δ + 1) * (|x| + 1)) * Real.exp (δ * |x|) := by
        have hAB_nonneg :
            0 ≤ ((|(v : ℝ)| * δ + 1) * (|x| + 1)) := by
          have hA_nonneg : 0 ≤ (|(v : ℝ)| * δ + 1) := by
            have : 0 ≤ |(v : ℝ)| * δ := by
              have hvn' : 0 ≤ |(v : ℝ)| := abs_nonneg (v : ℝ)
              have hδn : 0 ≤ δ := le_of_lt hδ_pos
              exact mul_nonneg hvn' hδn
            linarith
          have hB_nonneg : 0 ≤ (|x| + 1) := by nlinarith [abs_nonneg x]
          exact mul_nonneg hA_nonneg hB_nonneg
        have := mul_le_mul_of_nonneg_left hGe1_C hAB_nonneg
        exact one_le_mul_of_one_le_of_one_le hAB hGe1_C
      have hprod :
          1 ≤ ((|(v : ℝ)| * δ + 1) * (|x| + 1) * Real.exp (δ * |x|)) := by
        exact hABC
      have := mul_le_mul_of_nonneg_left hprod (abs_nonneg (F x))
      simpa [B, Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc] using this
    exact (hB_int.mono' (hFmeas.aestronglyMeasurable) (ae_of_all _ h1))
  exact
    gaussianTilt_hasDerivAt_left_of_dominated
      (v := v) (F := F)
      hFmeas hδ_pos B hB_int hBound hG0_int

/-! ##  Auxiliary lemmas for the right–shift derivative  -/

lemma gaussianTilt_deriv_dom
    {v : ℝ≥0} {F : ℝ → ℝ}
    (hMod : HasModerateGrowth F) :
  ∃ (C : ℝ) (m : ℕ) (_ : 0 < C),
    ∀ t, |t| ≤ 1 →
      ∀ x, |(v : ℝ) * deriv F (x + (v : ℝ) * t)|
        ≤ |(v : ℝ)| * C * (1 + |x| + |(v : ℝ)|) ^ m := by
  rcases hMod with ⟨C, m, hCpos, _hF, hF'⟩
  refine ⟨C, m, hCpos, ?_⟩
  intro t ht x
  have h_deriv : |deriv F (x + (v:ℝ) * t)| ≤ C * (1 + |x + (v:ℝ) * t|) ^ m := by
    simpa using hF' (x + (v:ℝ) * t)
  have h_tri : |x + (v:ℝ) * t| ≤ |x| + |(v:ℝ)| * |t| := by
    simpa [abs_add_le, abs_mul, mul_comm, mul_left_comm, mul_assoc]
      using abs_add_le_abs_add_abs x ((v:ℝ) * t)
  have ht' : |(v:ℝ)| * |t| ≤ |(v:ℝ)| := by
    have := mul_le_mul_of_nonneg_left ht (abs_nonneg (v:ℝ))
    simpa [mul_one] using this
  have h_lin : 1 + |x + (v:ℝ) * t| ≤ 1 + |x| + |(v:ℝ)| := by
    have : |x + (v:ℝ) * t| ≤ |x| + |(v:ℝ)| := le_trans h_tri (by simpa using ht')
    linarith
  have h_baseL : 0 ≤ 1 + |x + (v:ℝ) * t| := by nlinarith [abs_nonneg (x + (v:ℝ) * t)]
  have h_pow :
      (1 + |x + (v:ℝ) * t|) ^ m ≤ (1 + |x| + |(v:ℝ)|) ^ m :=
    Real.pow_le_pow_of_le_left h_baseL h_lin
  have hDerivBound :
      |deriv F (x + (v:ℝ) * t)|
        ≤ C * (1 + |x| + |(v:ℝ)|) ^ m := by
    have hCnn : 0 ≤ C := le_of_lt hCpos
    exact (le_trans h_deriv (mul_le_mul_of_nonneg_left h_pow hCnn))
  have hvnonneg : 0 ≤ (v : ℝ) := v.property
  have hMul :
      (v : ℝ) * |deriv F (x + (v:ℝ) * t)|
        ≤ C * ((v : ℝ) * (1 + |x| + |(v : ℝ)|) ^ m) := by
    have := mul_le_mul_of_nonneg_right hDerivBound hvnonneg
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have : |(v : ℝ) * deriv F (x + (v : ℝ) * t)|
        ≤ C * ((v : ℝ) * (1 + |x| + |(v : ℝ)|) ^ m) := by
    simpa [abs_mul, abs_of_nonneg hvnonneg, mul_comm, mul_left_comm, mul_assoc] using hMul
  simpa [abs_of_nonneg hvnonneg, mul_comm, mul_left_comm, mul_assoc] using this

/-- Integrability (under any centered Gaussian) of the dominating polynomial profile
appearing in `gaussianTilt_deriv_dom`, for the same constants `C, m`. -/
lemma gaussianTilt_deriv_dom_integrable
    {v : ℝ≥0} {F : ℝ → ℝ}
    (_ : HasModerateGrowth F)
    (C : ℝ) (m : ℕ) (hC : 0 < C) :
  Integrable (fun x => |(v : ℝ)| * C * (1 + |x| + |(v : ℝ)|) ^ m)
      (gaussianReal 0 v) := by
  have hMom : Integrable (fun x : ℝ => (1 + |x|) ^ m) (gaussianReal 0 v) :=
    gaussianReal_integrable_one_add_abs_pow_centered (v := v) m
  have hLe :
      ∀ x : ℝ, (1 + |x| + |(v : ℝ)|) ^ m
        ≤ (1 + |(v : ℝ)|) ^ m * (1 + |x|) ^ m := by
    intro x
    have hbaseL : 0 ≤ 1 + |x| + |(v:ℝ)| := by nlinarith [abs_nonneg x, abs_nonneg (v:ℝ)]
    have hxy : 1 + |x| + |(v:ℝ)| ≤ (1 + |x|) * (1 + |(v:ℝ)|) := by
      have hxv : 0 ≤ |x| * |(v:ℝ)| := by exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
      nlinarith
    have hpow :=
      Real.pow_le_pow_of_le_left (k := m) hbaseL hxy
    have hfac : ((1 + |x|) * (1 + |(v:ℝ)|)) ^ m
                = (1 + |(v:ℝ)|) ^ m * (1 + |x|) ^ m := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (mul_pow (1 + |x|) (1 + |(v:ℝ)|) m)
    exact le_of_le_of_eq hpow hfac
  have hIntDom :
      Integrable (fun x : ℝ =>
        (1 + |(v : ℝ)|) ^ m * (1 + |x|) ^ m) (gaussianReal 0 v) :=
    (hMom.const_mul ((1 + |(v : ℝ)|) ^ m))
  have hMeas :
      AEStronglyMeasurable
        (fun x => |(v : ℝ)| * C * (1 + |x| + |(v : ℝ)|) ^ m)
        (gaussianReal 0 v) := by
    have hPoly : Measurable (fun x : ℝ => (1 + |x| + |(v : ℝ)|) ^ m) :=
      (((measurable_const.add measurable_abs).add measurable_const).pow_const _)
    exact ((measurable_const.mul measurable_const).mul hPoly).aestronglyMeasurable
  have hAE :
      ∀ᵐ x ∂ gaussianReal 0 v,
        ‖|(v : ℝ)| * C * (1 + |x| + |(v : ℝ)|) ^ m‖
          ≤ (|(v : ℝ)| * C) * ((1 + |(v : ℝ)|) ^ m * (1 + |x|) ^ m) := by
    refine ae_of_all _ (fun x => ?_)
    have hnn1 : 0 ≤ |(v : ℝ)| := abs_nonneg _
    have hnn2 : 0 ≤ C := le_of_lt hC
    have hnn3 : 0 ≤ (1 + |x| + |(v : ℝ)|) ^ m := by
      have hbase : 0 ≤ 1 + |x| + |(v : ℝ)| := by
        have : 0 ≤ |x| := abs_nonneg _
        have : 0 ≤ |(v : ℝ)| := abs_nonneg _
        nlinarith
      exact pow_nonneg hbase _
    have hLHS_nonneg :
        0 ≤ |(v : ℝ)| * C * (1 + |x| + |(v : ℝ)|) ^ m :=
      mul_nonneg (mul_nonneg hnn1 hnn2) hnn3
    have hDom :
        |(v : ℝ)| * C * (1 + |x| + |(v : ℝ)|) ^ m
          ≤ (|(v : ℝ)| * C) *
              ((1 + |(v : ℝ)|) ^ m * (1 + |x|) ^ m) := by
      have hpoly :=
        mul_le_mul_of_nonneg_left (hLe x) (mul_nonneg hnn1 hnn2)
      simpa [mul_comm, mul_left_comm, mul_assoc] using hpoly
    have hAbs_eq :
        ‖|(v : ℝ)| * C * (1 + |x| + |(v : ℝ)|) ^ m‖
          = (|(v : ℝ)| * C) * (1 + |x| + |(v : ℝ)|) ^ m := by
      have hnonneg :
          0 ≤ (|(v : ℝ)| * C) * (1 + |x| + |(v : ℝ)|) ^ m :=
        mul_nonneg (mul_nonneg hnn1 hnn2) hnn3
      exact norm_of_nonneg hLHS_nonneg
    have : ‖|(v : ℝ)| * C * (1 + |x| + |(v : ℝ)|) ^ m‖
          ≤ (|(v : ℝ)| * C) * ((1 + |(v : ℝ)|) ^ m * (1 + |x|) ^ m) := by
      aesop
    exact this
  exact (hIntDom.const_mul (|(v : ℝ)| * C)).mono' hMeas hAE

/-- Generic shift differentiation lemma:
Assumes integrability of F at t = 0, and domination/integrability for the derivative profile. -/
lemma gaussianTilt_hasDerivAt_right_aux
    {v : ℝ≥0} (hv : v ≠ 0) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F)
    (hF_int : Integrable F (gaussianReal 0 v))
    {C : ℝ} {m : ℕ}
    (hDom : ∀ t, |t| ≤ 1 → ∀ x,
                |(v : ℝ) * deriv F (x + (v : ℝ) * t)|
                  ≤ |(v : ℝ)| * C * (1 + |x| + |(v : ℝ)|)^m)
    (hInt : Integrable (fun x => |(v : ℝ)| * C *
                               (1 + |x| + |(v : ℝ)|)^m) (gaussianReal 0 v)) :
    HasDerivAt (gaussianTilt F v)
      ((v : ℝ) * ∫ x, deriv F x ∂ gaussianReal 0 v) 0 := by
  have hShift := gaussianTilt_eq_shift (v := v) hv (F := F)
  set G  : ℝ → ℝ → ℝ := fun t x => F (x + (v : ℝ) * t)
  set G' : ℝ → ℝ → ℝ := fun t x => (v : ℝ) * deriv F (x + (v : ℝ) * t)
  have hG_meas : ∀ t, AEStronglyMeasurable (G t) (gaussianReal 0 v) := by
    intro t
    have hAdd : Measurable (fun x : ℝ => x + (v : ℝ) * t) :=
      (measurable_id.add measurable_const)
    exact (hF.continuous.measurable.comp hAdd).aestronglyMeasurable
  have hG0_int : Integrable (G 0) (gaussianReal 0 v) := by
    simpa [G] using hF_int
  have hGp0_meas : AEStronglyMeasurable (G' 0) (gaussianReal 0 v) := by
    have hDer_meas : Measurable (deriv F) :=
      (hF.continuous_deriv le_rfl).measurable
    have hEq : (fun x => G' 0 x) = (fun x => (v : ℝ) * deriv F x) := by
      funext x; simp [G']
    simpa [hEq] using (measurable_const.mul hDer_meas).aestronglyMeasurable
  have h_bound :
      ∀ᵐ x ∂ gaussianReal 0 v,
        ∀ t ∈ Metric.ball (0 : ℝ) (1 : ℝ), ‖G' t x‖
          ≤ |(v : ℝ)| * C * (1 + |x| + |(v : ℝ)|)^m := by
    refine ae_of_all _ (fun x => ?_)
    intro t ht
    have ht' : |t| ≤ 1 := (mem_ball_zero_iff.mp ht).le
    change |(v : ℝ) * deriv F (x + (v : ℝ) * t)|
            ≤ |(v : ℝ)| * C * (1 + |x| + |(v : ℝ)|)^m
    exact hDom t ht' x
  have h_diff :
      ∀ᵐ x ∂ gaussianReal 0 v,
        ∀ t ∈ Metric.ball (0 : ℝ) (1 : ℝ),
          HasDerivAt (fun s => G s x) (G' t x) t := by
    refine ae_of_all _ (fun x => ?_)
    intro t _ht
    have hInner0 : HasDerivAt (fun s : ℝ => (v : ℝ) * s) (v : ℝ) t := by
      simpa [mul_one] using (hasDerivAt_id t).const_mul (v : ℝ)
    have hInner : HasDerivAt (fun s : ℝ => x + (v : ℝ) * s) (v : ℝ) t :=
      hInner0.const_add x
    have hOuter : HasDerivAt F (deriv F (x + (v : ℝ) * t)) (x + (v : ℝ) * t) :=
      (hF.differentiable one_ne_zero _).hasDerivAt
    simpa [G, G', mul_comm] using hOuter.comp t hInner
  have hDer :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ              := gaussianReal 0 v)
      (F              := G)
      (F'             := G')
      (ε_pos          := show (0 : ℝ) < 1 by norm_num)
      (hF_meas        := Eventually.of_forall hG_meas)
      (hF_int         := hG0_int)
      (hF'_meas       := hGp0_meas)
      (h_bound        := h_bound)
      (bound_integrable := hInt)
      (h_diff         := h_diff)
  have hRewr : (fun t => ∫ x, G t x ∂ gaussianReal 0 v) = gaussianTilt F v := by
    funext t; simpa [G] using (hShift t).symm
  have hDerVal :
      (∫ x, G' 0 x ∂ gaussianReal 0 v)
        = (v : ℝ) * ∫ x, deriv F x ∂ gaussianReal 0 v := by
    simp [G', integral_const_mul]
  have : HasDerivAt (gaussianTilt F v)
            (∫ x, G' 0 x ∂ gaussianReal 0 v) 0 := by
    simpa [hRewr] using hDer.2
  simpa [hDerVal]

lemma gaussianTilt_hasDerivAt_right
    {v : ℝ≥0} (hv : v ≠ 0) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F)
    (hMod : HasModerateGrowth F) :
    HasDerivAt (gaussianTilt F v)
      ((v : ℝ) * ∫ x, deriv F x ∂ gaussianReal 0 v) 0 := by
  rcases gaussianTilt_deriv_dom (v := v) hMod with
    ⟨C, m, hCpos, hDom⟩
  have hInt :
      Integrable (fun x => |(v : ℝ)| * C * (1 + |x| + |(v : ℝ)|) ^ m)
        (gaussianReal 0 v) :=
    gaussianTilt_deriv_dom_integrable (v := v) (F := F) hMod C m hCpos
  let δ : ℝ := 1
  let B : ℝ → ℝ :=
    fun x => |F x| * ((|(v : ℝ)| * δ) + 1) * (|x| + 1) * Real.exp (δ * |x|)
  have hB_int :
      Integrable B (gaussianReal 0 v) := by
    have hFcont : Continuous F := hF.continuous
    simpa [B] using
      gaussianTilt_domination_bound (v := v) (F := F) δ (by norm_num) hMod hFcont
  have hFmeas : Measurable F := hF.continuous.measurable
  have hF_int : Integrable F (gaussianReal 0 v) := by
    have h1 : ∀ x, ‖F x‖ ≤ B x := by
      intro x
      have hA : 1 ≤ (|(v : ℝ)| * δ + 1) := by
        have hvn : 0 ≤ |(v : ℝ)| * δ :=
          mul_nonneg (abs_nonneg _) (by norm_num)
        nlinarith
      have hB' : 1 ≤ |x| + 1 := by nlinarith [abs_nonneg x]
      have hC : 1 ≤ Real.exp (δ * |x|) := by
        have : 0 ≤ δ * |x| := by nlinarith [abs_nonneg x]
        simpa using Real.one_le_exp_iff.mpr this
      have hprod :
          1 ≤ ((|(v : ℝ)| * δ + 1) * (|x| + 1) * Real.exp (δ * |x|)) := by
        have hAB := one_le_mul_of_one_le_of_one_le hA hB'
        have := one_le_mul_of_one_le_of_one_le hAB hC
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      have := mul_le_mul_of_nonneg_left hprod (abs_nonneg (F x))
      simpa [B, Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc] using this
    exact (hB_int.mono' (hFmeas.aestronglyMeasurable) (ae_of_all _ h1))
  exact gaussianTilt_hasDerivAt_right_aux hv hF hF_int hDom hInt

/-- **Stein's lemma (centered Gaussian)**; split proof via the two derivative lemmas.
This version assumes moderate growth (which implies the needed integrability). -/
theorem stein_lemma_gaussianReal
    {v : ℝ≥0} (hv : v ≠ 0) {F : ℝ → ℝ}
    (hF  : ContDiff ℝ 1 F)
    (hMod : HasModerateGrowth F) :
    ∫ x, x * F x ∂ (gaussianReal 0 v)
      = (v : ℝ) * ∫ x, deriv F x ∂ (gaussianReal 0 v) := by
  -- Left and right derivatives of the Gaussian tilt at 0 coincide and identify both sides.
  have hL := gaussianTilt_hasDerivAt_left  (v := v) hv hF hMod
  have hR := gaussianTilt_hasDerivAt_right (v := v) hv hF hMod
  -- Uniqueness of the derivative at a point gives equality of the derivative values.
  exact hL.unique hR

/-- Measure-level Gaussian integration by parts (from Stein's lemma).
Assumes moderate growth (no separate integrability hypotheses needed). -/
lemma gaussianReal_integration_by_parts
    {F : ℝ → ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hF  : ContDiff ℝ 1 F)
    (hMod : HasModerateGrowth F) :
    ∫ x, x * F x ∂(gaussianReal 0 v)
      = (v : ℝ) * ∫ x, deriv F x ∂(gaussianReal 0 v) :=
  stein_lemma_gaussianReal hv hF hMod

lemma IsCenteredGaussianRV.expectation_comp
    {g : Ω → ℝ} {v : ℝ≥0} (hg : IsCenteredGaussianRV g v)
    (hgAE : AEMeasurable g ℙ)
    {Φ : ℝ → ℝ} (hInt : Integrable Φ (gaussianReal 0 v)) :
    ∫ ω, Φ (g ω) ∂ℙ = ∫ x, Φ x ∂(gaussianReal 0 v) := by
  unfold IsCenteredGaussianRV IsGaussianRV at hg
  have hIntLaw : Integrable Φ (Measure.map g ℙ) := by simpa [hg] using hInt
  have hΦ_aesm : AEStronglyMeasurable Φ (Measure.map g ℙ) := hIntLaw.aestronglyMeasurable
  have hMap := integral_map hgAE hΦ_aesm
  rw [← hMap, hg]

-- The second moment is integrable under any centered Gaussian.
lemma integrable_sq_gaussianReal_centered (v : ℝ≥0) :
    Integrable (fun x : ℝ => x^2) (gaussianReal 0 v) := by
  have hMom2 : Integrable (fun x : ℝ => (1 + |x|)^2) (gaussianReal 0 v) :=
    gaussianReal_integrable_one_add_abs_pow_centered (v := v) 2
  have hMeas : Measurable (fun x : ℝ => x^2) :=
    (continuous_id.pow 2).measurable
  have hAE :
      ∀ᵐ x ∂ gaussianReal 0 v, ‖x^2‖ ≤ (1 + |x|)^2 := by
    refine ae_of_all _ (fun x => ?_)
    have hx0 : 0 ≤ |x| := abs_nonneg _
    have hxle : |x| ≤ 1 + |x| := by nlinarith
    have hmul : |x| * |x| ≤ (1 + |x|) * (1 + |x|) :=
      mul_le_mul hxle hxle hx0 (by nlinarith)
    simpa [Real.norm_eq_abs, pow_two, mul_comm, mul_left_comm, mul_assoc] using hmul
  exact hMom2.mono' (hMeas.aestronglyMeasurable) hAE

lemma IsCenteredGaussianRV.secondMoment
    {g : Ω → ℝ} {v : ℝ≥0}
    (hg : IsCenteredGaussianRV g v) (hgMeas : Measurable g) :
    ∫ ω, (g ω)^2 ∂ℙ = v := by
  unfold IsCenteredGaussianRV IsGaussianRV at hg
  have hIntGauss : Integrable (fun x : ℝ => x^2) (gaussianReal 0 v) :=
    integrable_sq_gaussianReal_centered (v := v)
  have hIntLaw : Integrable (fun x : ℝ => x^2) (Measure.map g ℙ) := by
    simpa [hg] using hIntGauss
  have hΦ_aesm :
      AEStronglyMeasurable (fun x : ℝ => x^2) (Measure.map g ℙ) :=
    hIntLaw.aestronglyMeasurable
  have hMap := integral_map hgMeas.aemeasurable hΦ_aesm
  rw [← hMap, hg, integral_sq_gaussianReal_centered (v := v)]

lemma gaussianRV_integration_by_parts
    {g : Ω → ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hg : IsCenteredGaussianRV g v) (hgMeas : Measurable g)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hMod : HasModerateGrowth F) :
    ∫ ω, g ω * F (g ω) ∂ℙ
      = (v : ℝ) * ∫ ω, deriv F (g ω) ∂ℙ := by
  have hΦ1m : Measurable (fun x : ℝ => x * F x) :=
    (measurable_id.mul hF.continuous.measurable)
  have hΦ2m : Measurable (fun x : ℝ => deriv F x) :=
    (hF.continuous_deriv le_rfl).measurable
  classical
  have hModCopy : HasModerateGrowth F := hMod
  rcases hMod with ⟨C, m, hCpos, hFbound, hF'bound⟩
  have hMom_m : Integrable (fun x : ℝ => (1 + |x|) ^ m) (gaussianReal 0 v) :=
    gaussianReal_integrable_one_add_abs_pow_centered (v := v) m
  have hMom_m1 : Integrable (fun x : ℝ => (1 + |x|) ^ (m + 1)) (gaussianReal 0 v) :=
    gaussianReal_integrable_one_add_abs_pow_centered (v := v) (m + 1)
  have hInt1 : Integrable (fun x => x * F x) (gaussianReal 0 v) := by
    have hAE : ∀ᵐ x ∂ gaussianReal 0 v,
        ‖x * F x‖ ≤ C * (1 + |x|) ^ (m + 1) := by
      refine ae_of_all _ (fun x => ?_)
      have hFabs : ‖F x‖ ≤ C * (1 + |x|) ^ m := by
        simpa [Real.norm_eq_abs] using hFbound x
      have hineq : ‖x * F x‖ = |x| * ‖F x‖ := by
        simp [Real.norm_eq_abs]
      have hx : |x| ≤ 1 + |x| := by nlinarith [abs_nonneg x]
      calc
        ‖x * F x‖ = |x| * ‖F x‖ := hineq
        _ ≤ (1 + |x|) * ‖F x‖ :=
          mul_le_mul_of_nonneg_right hx (norm_nonneg _)
        _ ≤ (1 + |x|) * (C * (1 + |x|) ^ m) :=
          mul_le_mul_of_nonneg_left hFabs (by nlinarith [abs_nonneg x])
        _ = C * (1 + |x|) ^ (m + 1) := by
          calc
            (1 + |x|) * (C * (1 + |x|) ^ m)
                = C * ((1 + |x|) * (1 + |x|) ^ m) := by ring
            _ = C * ((1 + |x|) ^ m * (1 + |x|)) := by ring
            _ = C * (1 + |x|) ^ (m + 1) := by
                  simp [pow_succ, mul_comm]
    have hDomInt : Integrable (fun x => C * (1 + |x|) ^ (m + 1)) (gaussianReal 0 v) :=
      (hMom_m1.const_mul C)
    exact hDomInt.mono' (hΦ1m.aestronglyMeasurable) hAE
  have hInt2 : Integrable (fun x => deriv F x) (gaussianReal 0 v) := by
    have hAE : ∀ᵐ x ∂ gaussianReal 0 v,
        ‖deriv F x‖ ≤ C * (1 + |x|) ^ m := by
      exact ae_of_all _ (fun x => by
        simpa [Real.norm_eq_abs] using hF'bound x)
    have hDomInt : Integrable (fun x => C * (1 + |x|) ^ m) (gaussianReal 0 v) :=
      (hMom_m.const_mul C)
    exact hDomInt.mono' ((hF.continuous_deriv le_rfl).measurable.aestronglyMeasurable) hAE
  have h1 := IsCenteredGaussianRV.expectation_comp (g := g) (v := v)
              hg hgMeas.aemeasurable hInt1
  have h2 := IsCenteredGaussianRV.expectation_comp (g := g) (v := v)
              hg hgMeas.aemeasurable hInt2
  calc
    ∫ ω, g ω * F (g ω) ∂ℙ
        = ∫ x, x * F x ∂(gaussianReal 0 v) := h1
    _ = (v : ℝ) * ∫ x, deriv F x ∂(gaussianReal 0 v) :=
        gaussianReal_integration_by_parts (v := v) hv hF hModCopy
    _ = (v : ℝ) * ∫ ω, deriv F (g ω) ∂ℙ := by
        simp [h2]

lemma mul_pos_of_pos_of_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hb_ne : b ≠ 0) : 0 < a * b := by
  have hb_pos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hb_ne)
  exact Left.mul_pos ha hb_pos

theorem gaussian_integration_by_parts_general
    {g : Ω → ℝ} {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hg : IsGaussianRV g μ v) (hgMeas : Measurable g)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hMod : HasModerateGrowth F) :
    ∫ ω, (g ω - μ) * F (g ω) ∂ℙ = (v : ℝ) * ∫ ω, deriv F (g ω) ∂ℙ := by
  let Y : Ω → ℝ := fun ω => g ω - μ
  have hY : IsCenteredGaussianRV Y v := by
    unfold IsCenteredGaussianRV IsGaussianRV Y
    -- map g by (· - μ)
    have hmap :
        Measure.map (fun ω => g ω - μ) ℙ
          = (Measure.map g ℙ).map (fun x : ℝ => x - μ) := by
      simpa [Y, Function.comp] using
        (Measure.map_map
          (hf := hgMeas)
          (hg := (measurable_id.sub measurable_const))
          (μ := ℙ) (f := g) (g := fun x : ℝ => x - μ)).symm
    calc
      Measure.map Y ℙ
          = (Measure.map g ℙ).map (fun x : ℝ => x - μ) := hmap
      _ = (gaussianReal μ v).map (fun x : ℝ => x - μ) := by
            simpa using
              congrArg (fun m : Measure ℝ =>
                Measure.map (fun x : ℝ => x - μ) m) hg
      _ = gaussianReal (μ - μ) v := gaussianReal_map_sub_const (μ := μ) (v := v) μ
      _ = gaussianReal 0 v := by simp
  have hYMeas : Measurable Y := hgMeas.sub measurable_const
  let F_shifted : ℝ → ℝ := fun x => F (x + μ)
  have hF_shifted : ContDiff ℝ 1 F_shifted :=
    hF.comp (contDiff_id.add contDiff_const)
  have h_deriv : deriv F_shifted = fun x => deriv F (x + μ) := by
    funext x
    have hAdd : HasDerivAt (fun x => x + μ) 1 x := by
      simpa using (hasDerivAt_id x).add_const μ
    have hF' : HasDerivAt F (deriv F (x + μ)) (x + μ) :=
      (hF.differentiable one_ne_zero _).hasDerivAt
    exact deriv_comp_add_const F μ x
  have hMod_shifted : HasModerateGrowth F_shifted := by
    rcases hMod with ⟨C, m, hCpos, hFbound, hF'bound⟩
    refine ⟨C * (1 + |μ|) ^ m, m, ?_, ?_, ?_⟩
    · -- show 0 < C * (1 + |μ|)^m
      have hPowPos : 0 < (1 + |μ|) ^ m := by
        have hbase : 0 < 1 + |μ| := by nlinarith [abs_nonneg μ]
        simpa using pow_pos hbase m
      exact Left.mul_pos hCpos hPowPos
    · -- bound for F_shifted
      intro x
      have htri : |x + μ| ≤ |x| + |μ| := by
        simp [abs_add_le]
      have hone_le : 1 + |x + μ| ≤ 1 + |x| + |μ| := by
        have := add_le_add_left htri 1
        simpa [add_comm, add_left_comm, add_assoc] using this
      have hbase : 0 ≤ 1 + |x + μ| := add_nonneg (by norm_num) (abs_nonneg _)
      have hpow_le :
          (1 + |x + μ|) ^ m ≤ (1 + |x| + |μ|) ^ m :=
        Real.pow_le_pow_of_le_left hbase hone_le
      have hmul_le :
          (1 + |x| + |μ|) ^ m ≤ (1 + |μ|) ^ m * (1 + |x|) ^ m := by
        have hbase' : 0 ≤ 1 + |x| + |μ| := by
          have : 0 ≤ |x| := abs_nonneg _; have : 0 ≤ |μ| := abs_nonneg _
          nlinarith
        have hxy : 1 + |x| + |μ| ≤ (1 + |x|) * (1 + |μ|) := by
          have hxμ : 0 ≤ |x| * |μ| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
          nlinarith
        have hpow' := Real.pow_le_pow_of_le_left (k := m) hbase' hxy
        have hfac : ((1 + |x|) * (1 + |μ|)) ^ m
                  = (1 + |μ|) ^ m * (1 + |x|) ^ m := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using mul_pow (1 + |x|) (1 + |μ|) m
        simpa [hfac]
          using hpow'
      have hF_at := hFbound (x + μ)
      have : |F (x + μ)| ≤ C * ((1 + |μ|) ^ m * (1 + |x|) ^ m) :=
        le_trans hF_at (by
          have hCnn : 0 ≤ C := le_of_lt hCpos
          exact mul_le_mul_of_nonneg_left
                  (le_trans hpow_le hmul_le) hCnn)
      simpa [F_shifted, mul_comm, mul_left_comm, mul_assoc]
        using this
    · -- derivative bound for F_shifted
      intro x
      have hF'd_at : |deriv F (x + μ)| ≤ C * (1 + |x + μ|) ^ m := hF'bound (x + μ)
      have hpow_le :
          (1 + |x + μ|) ^ m ≤ (1 + |μ|) ^ m * (1 + |x|) ^ m := by
        have htri : |x + μ| ≤ |x| + |μ| := by
          simp [abs_add_le]
        have hone : 1 + |x + μ| ≤ 1 + |x| + |μ| := by
          have := add_le_add_left htri 1
          simpa [add_comm, add_left_comm, add_assoc] using this
        have hbase : 0 ≤ 1 + |x + μ| := add_nonneg (by norm_num) (abs_nonneg _)
        have h1 : (1 + |x + μ|) ^ m ≤ (1 + |x| + |μ|) ^ m :=
          Real.pow_le_pow_of_le_left (k := m) hbase hone
        have hbase' : 0 ≤ 1 + |x| + |μ| := by
          have : 0 ≤ |x| := abs_nonneg _; have : 0 ≤ |μ| := abs_nonneg _
          nlinarith
        have hxy : 1 + |x| + |μ| ≤ (1 + |x|) * (1 + |μ|) := by
          have hxμ : 0 ≤ |x| * |μ| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
          nlinarith
        have hpow' := Real.pow_le_pow_of_le_left (k := m) hbase' hxy
        have hfac : ((1 + |x|) * (1 + |μ|)) ^ m
                  = (1 + |μ|) ^ m * (1 + |x|) ^ m := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using mul_pow (1 + |x|) (1 + |μ|) m
        exact le_trans h1 (by simpa [hfac] using hpow')
      have hDerAbs : |deriv F_shifted x| = |deriv F (x + μ)| := by
        simp [h_deriv]
      simpa [F_shifted, mul_comm, mul_left_comm, mul_assoc, hDerAbs]
        using
          (le_trans (by simpa [hDerAbs] using hF'd_at)
                    (by
                      have hCnn : 0 ≤ C := le_of_lt hCpos
                      exact mul_le_mul_of_nonneg_left hpow_le hCnn))
  have hIBP :=
    gaussianRV_integration_by_parts (v := v) hv hY hYMeas hF_shifted hMod_shifted
  convert hIBP using 1
  · congr with ω
    simp [Y, F_shifted]
  · congr with ω
    aesop

end ProbabilityTheory
