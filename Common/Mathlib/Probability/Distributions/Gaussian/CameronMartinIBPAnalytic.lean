import Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinIBPDeriv
import Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinFernique
import Common.Mathlib.Probability.Distributions.Gaussian.TiltKernel
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Cameron–Martin IBP: analytic layer

This file provides the analytic infrastructure to differentiate the Cameron–Martin tilt functional
`t ↦ ∫ F(y) · exp(t⟨x,y⟩ - t²‖x‖²/2) dμ(y)` at `t = 0` under the integral sign, yielding
the Gaussian integration-by-parts identity `∫ ⟨x,y⟩ F(y) dμ(y)`.

## Main results

* `cameronMartinTiltKernel_aeEq_tiltKernel`: the Cameron–Martin tilt kernel agrees a.e. with the
  1D `tiltKernel` applied to the coordinate `x y`.
* `integrable_profile_cameronMartin`: the exponential profile `(|x y| + 1) * exp(δ|x y|)` is
  integrable under `μ`, enabling dominated convergence arguments.
* `hasDerivAt_tiltFun_at0_of_bounded`: differentiation under the integral for bounded `F`.
* `hasDerivAt_tiltFun_at0_of_integrable_profile`: differentiation under the integral given
  explicit integrability of the dominating profile.

## Implementation notes

The key technique is to reduce the infinite-dimensional differentiation problem to 1D by
composing with the Cameron–Martin direction `x`, then applying the domination bounds from
`GaussianIntegrationByParts.lean` (specifically `gaussianTilt_deriv_dom_bound`).
-/

open MeasureTheory Filter
open scoped Topology Real ENNReal NNReal

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsGaussian μ]

namespace CameronMartinIBPAnalytic

private lemma cameronMartin_smul_ae (x : cameronMartin μ) (t : ℝ) :
    (fun y : E => (t • (x : Lp ℝ 2 μ)) y) =ᵐ[μ] fun y : E => t * x y := by
  simpa [Pi.smul_apply] using (Lp.coeFn_smul (c := t) (f := (x : Lp ℝ 2 μ)))

private lemma abs_mul_mul_eq_mul_mul (t a : ℝ) : |t| * (|t| * a) = t * (t * a) := by
  have ht : |t| * |t| = t * t := abs_mul_abs_self t
  calc
    |t| * (|t| * a) = (|t| * |t|) * a := (mul_assoc (|t|) (|t|) a).symm
    _ = (t * t) * a := congrArg (fun s => s * a) ht
    _ = t * (t * a) := mul_assoc t t a

/-- A.e. identification of the Cameron–Martin tilt kernel with the 1D `tiltKernel`
for the centered real Gaussian law of `x`. -/
lemma cameronMartinTiltKernel_aeEq_tiltKernel (x : cameronMartin μ) (t : ℝ) :
    (fun y : E => cameronMartinTiltKernel (μ := μ) x t y)
      =ᵐ[μ] fun y : E => tiltKernel (‖x‖₊ ^ 2) t (x y) := by
  filter_upwards [cameronMartin_smul_ae (μ := μ) x t] with y hy
  have habs :
      |t| * (|t| * (‖(↑x : Lp ℝ 2 μ)‖ * ‖(↑x : Lp ℝ 2 μ)‖))
        = t * (t * (‖(↑x : Lp ℝ 2 μ)‖ * ‖(↑x : Lp ℝ 2 μ)‖)) :=
    abs_mul_mul_eq_mul_mul t (‖(↑x : Lp ℝ 2 μ)‖ * ‖(↑x : Lp ℝ 2 μ)‖)
  simp [cameronMartinTiltKernel, tiltKernel, hy, habs, norm_smul, Real.norm_eq_abs, pow_two,
    mul_assoc, mul_left_comm, mul_comm]

private lemma memLp_abs_add_one_gaussianReal (v : ℝ≥0) :
    MemLp (fun u : ℝ => |u| + 1) (2 : ℝ≥0∞) (gaussianReal 0 v) := by
  have h2 : MemLp (fun u : ℝ => u) (2 : ℝ≥0∞) (gaussianReal 0 v) := by
    simpa using memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := v) (p := (2 : ℝ≥0∞)) (by simp)
  simpa [Real.norm_eq_abs, add_comm, add_left_comm, add_assoc] using h2.norm.add (memLp_const (c := (1 : ℝ)))

private lemma exp_mul_abs_le_add_exp (a u : ℝ) :
    Real.exp (a * |u|) ≤ Real.exp (a * u) + Real.exp (-a * u) := by
  by_cases hu : 0 ≤ u
  · have : |u| = u := abs_of_nonneg hu
    simpa [this, sub_eq_add_neg] using
      (le_add_of_nonneg_right (a := Real.exp (a * u)) (b := Real.exp (-a * u))
        (by positivity : (0 : ℝ) ≤ Real.exp (-a * u)))
  · have : |u| = -u := abs_of_neg (lt_of_not_ge hu)
    have h :
        Real.exp (-a * u) ≤ Real.exp (-a * u) + Real.exp (a * u) :=
      le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ Real.exp (a * u))
    simpa [this, add_comm, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg] using h

private lemma integrable_exp_mul_abs_gaussianReal (v : ℝ≥0) (a : ℝ) :
    Integrable (fun u : ℝ => Real.exp (a * |u|)) (gaussianReal 0 v) := by
  have hpos : Integrable (fun u : ℝ => Real.exp (a * u)) (gaussianReal 0 v) :=
    integrable_exp_mul_gaussianReal (μ := (0 : ℝ)) (v := v) (t := a)
  have hneg : Integrable (fun u : ℝ => Real.exp (-a * u)) (gaussianReal 0 v) :=
    integrable_exp_mul_gaussianReal (μ := (0 : ℝ)) (v := v) (t := -a)
  have hmeas : Measurable (fun u : ℝ => Real.exp (a * |u|)) := by fun_prop
  refine (hpos.add hneg).mono' hmeas.aestronglyMeasurable (ae_of_all _ (fun u => ?_))
  simpa [mul_assoc] using exp_mul_abs_le_add_exp a u

private lemma memLp_exp_abs_gaussianReal (v : ℝ≥0) (δ : ℝ) :
    MemLp (fun u : ℝ => Real.exp (δ * |u|)) (2 : ℝ≥0∞) (gaussianReal 0 v) := by
  have hmeas : AEStronglyMeasurable (fun u : ℝ => Real.exp (δ * |u|)) (gaussianReal 0 v) := by
    fun_prop
  refine (memLp_two_iff_integrable_sq hmeas).2 ?_
  have h : Integrable (fun u : ℝ => Real.exp ((2 * δ) * |u|)) (gaussianReal 0 v) :=
    integrable_exp_mul_abs_gaussianReal (v := v) (a := 2 * δ)
  have hsq : (fun u : ℝ => (Real.exp (δ * |u|)) ^ 2) = fun u : ℝ => Real.exp ((2 * δ) * |u|) := by
    funext u
    calc
      (Real.exp (δ * |u|)) ^ 2 = Real.exp (δ * |u|) * Real.exp (δ * |u|) := by simp [pow_two]
      _ = Real.exp (δ * |u| + δ * |u|) := (Real.exp_add _ _).symm
      _ = Real.exp ((2 * δ) * |u|) := by ring_nf
  simpa [hsq] using h

private lemma integrable_profile_gaussianReal (v : ℝ≥0) {δ : ℝ} (_hδ : 0 < δ) :
    Integrable (fun u : ℝ => (|u| + 1) * Real.exp (δ * |u|)) (gaussianReal 0 v) :=
  by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (MemLp.integrable_mul (memLp_abs_add_one_gaussianReal v) (memLp_exp_abs_gaussianReal v δ))

/-- The domination profile `(|x y| + 1) * exp(δ |x y|)` is integrable under `μ`. -/
lemma integrable_profile_cameronMartin (x : cameronMartin μ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun y : E => (|x y| + 1) * Real.exp (δ * |x y|)) μ := by
  have hx := hasLaw_cameronMartin (μ := μ) x
  have : Integrable (fun u : ℝ => (|u| + 1) * Real.exp (δ * |u|)) (Measure.map x μ) := by
    simpa [hx.map_eq] using (integrable_profile_gaussianReal (v := (‖x‖₊ ^ 2)) hδ)
  exact this.comp_aemeasurable hx.aemeasurable

private lemma memLp_abs_add_one_sq_gaussianReal (v : ℝ≥0) :
    MemLp (fun u : ℝ => (|u| + 1) ^ 2) (2 : ℝ≥0∞) (gaussianReal 0 v) := by
  haveI : ProbabilityTheory.IsGaussian (gaussianReal (0 : ℝ) v) := by infer_instance
  have hmeas : AEStronglyMeasurable (fun u : ℝ => (|u| + 1) ^ 2) (gaussianReal 0 v) := by fun_prop
  refine (memLp_two_iff_integrable_sq hmeas).2 ?_
  have h : Integrable (fun u : ℝ => (1 + ‖u‖) ^ (4 : ℕ)) (gaussianReal (0 : ℝ) v) :=
    ProbabilityTheory.IsGaussian.integrable_one_add_norm_pow (μ := gaussianReal (0 : ℝ) v) 4
  have h' : Integrable (fun u : ℝ => (|u| + 1) ^ 4) (gaussianReal 0 v) := by
    simpa [Real.norm_eq_abs, add_comm] using h
  have hsq : (fun u : ℝ => ((|u| + 1) ^ 2) ^ 2) = fun u : ℝ => (|u| + 1) ^ 4 := by
    funext u
    simpa using (pow_mul (|u| + 1) 2 2).symm
  simpa [hsq] using h'

private lemma memLp_exp_abs_sq_gaussianReal (v : ℝ≥0) (δ : ℝ) :
    MemLp (fun u : ℝ => (Real.exp (δ * |u|)) ^ 2) (2 : ℝ≥0∞) (gaussianReal 0 v) := by
  have hmeas : AEStronglyMeasurable (fun u : ℝ => (Real.exp (δ * |u|)) ^ 2) (gaussianReal 0 v) := by
    fun_prop
  refine (memLp_two_iff_integrable_sq hmeas).2 ?_
  have h : Integrable (fun u : ℝ => Real.exp ((4 * δ) * |u|)) (gaussianReal 0 v) :=
    integrable_exp_mul_abs_gaussianReal (v := v) (a := 4 * δ)
  have hsq : (fun u : ℝ => ((Real.exp (δ * |u|)) ^ 2) ^ 2) = fun u : ℝ => Real.exp ((4 * δ) * |u|) := by
    funext u
    have hsq1 : (Real.exp (δ * |u|)) ^ 2 = Real.exp ((2 * δ) * |u|) := by
      calc
        (Real.exp (δ * |u|)) ^ 2 = Real.exp (δ * |u|) * Real.exp (δ * |u|) := by simp [pow_two]
        _ = Real.exp (δ * |u| + δ * |u|) := (Real.exp_add _ _).symm
        _ = Real.exp ((2 * δ) * |u|) := by ring_nf
    calc
      ((Real.exp (δ * |u|)) ^ 2) ^ 2 = (Real.exp ((2 * δ) * |u|)) ^ 2 := by simp [hsq1]
      _ = Real.exp ((4 * δ) * |u|) := by
            calc
              (Real.exp ((2 * δ) * |u|)) ^ 2
                  = Real.exp ((2 * δ) * |u|) * Real.exp ((2 * δ) * |u|) := by simp [pow_two]
              _ = Real.exp (((2 * δ) * |u|) + ((2 * δ) * |u|)) := (Real.exp_add _ _).symm
              _ = Real.exp ((4 * δ) * |u|) := by ring_nf
  simpa [hsq] using h

private lemma integrable_profile_sq_gaussianReal (v : ℝ≥0) {δ : ℝ} (_hδ : 0 < δ) :
    Integrable (fun u : ℝ => ((|u| + 1) * Real.exp (δ * |u|)) ^ 2) (gaussianReal 0 v) := by
  have hInt :
      Integrable (fun u : ℝ => (|u| + 1) ^ 2 * (Real.exp (δ * |u|)) ^ 2) (gaussianReal 0 v) :=
    MemLp.integrable_mul (memLp_abs_add_one_sq_gaussianReal v) (memLp_exp_abs_sq_gaussianReal v δ)
  have hrew :
      (fun u : ℝ => ((|u| + 1) * Real.exp (δ * |u|)) ^ 2)
        = fun u : ℝ => (|u| + 1) ^ 2 * (Real.exp (δ * |u|)) ^ 2 := by
    funext u; ring
  simpa [hrew] using hInt

/-- The exponential domination profile `( |x y| + 1 ) * exp(δ |x y|)` belongs to `L²`. -/
lemma memLp_profile_cameronMartin (x : cameronMartin μ) {δ : ℝ} (hδ : 0 < δ) :
    MemLp (fun y : E => (|x y| + 1) * Real.exp (δ * |x y|)) 2 μ := by
  have hx := hasLaw_cameronMartin (μ := μ) x
  have hsq : Integrable (fun y : E => ((|x y| + 1) * Real.exp (δ * |x y|)) ^ 2) μ := by
    have : Integrable (fun u : ℝ => ((|u| + 1) * Real.exp (δ * |u|)) ^ 2) (Measure.map x μ) := by
      simpa [hx.map_eq] using (integrable_profile_sq_gaussianReal (v := (‖x‖₊ ^ 2)) hδ)
    exact this.comp_aemeasurable hx.aemeasurable
  have hmeas :
      AEStronglyMeasurable (fun y : E => (|x y| + 1) * Real.exp (δ * |x y|)) μ := by
    have : Measurable (fun y : E => (|x y| + 1) * Real.exp (δ * |x y|)) := by
      fun_prop
    exact this.aestronglyMeasurable
  exact (MeasureTheory.memLp_two_iff_integrable_sq hmeas).2 (by
    simpa [pow_two] using hsq)

/-
Implementation note: the proofs of the shift/tilt differentiation theorems are factored into
small helper lemmas so that the exported statements remain short, without restating theorems or
introducing bespoke structures.
-/

section ShiftFun

variable (F : E → ℝ)

omit [CompleteSpace E] [SecondCountableTopology E] [IsGaussian μ] in
lemma aestronglyMeasurable_shiftFun_integrand (hF_meas : Measurable F) (v : E) :
    ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (fun y : E => F (y + t • v)) μ :=
  Filter.Eventually.of_forall (fun t =>
    (hF_meas.comp (by fun_prop)).aestronglyMeasurable)

omit [CompleteSpace E] [SecondCountableTopology E] [IsGaussian μ] in
lemma aestronglyMeasurable_shiftFun_integrandDeriv_at0
    {F' : E → E →L[ℝ] ℝ} (hF'cont : Continuous F') (v : E) :
    AEStronglyMeasurable (fun y : E => (F' y) v) μ := by
  exact ((ContinuousLinearMap.measurable_apply v).comp hF'cont.measurable).aestronglyMeasurable

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [SecondCountableTopology E] in
lemma hasDerivAt_shiftFun_integrand
    {F' : E → E →L[ℝ] ℝ} (hF' : ∀ y, HasFDerivAt F (F' y) y) (v : E)
    (t : ℝ) (y : E) :
    HasDerivAt (fun s => F (y + s • v)) ((F' (y + t • v)) v) t := by
  have hline : HasDerivAt (fun s : ℝ => y + s • v) v t := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (HasDerivAt.smul_const (hasDerivAt_id t) v).const_add y
  simpa using ((hF' (y + t • v)).comp_hasDerivAt t hline)

omit [BorelSpace E] [CompleteSpace E] [SecondCountableTopology E] [IsGaussian μ] in
lemma norm_shiftFun_integrandDeriv_le_of_norm_fderiv_le
    {F' : E → E →L[ℝ] ℝ} (hfderiv : ∀ y, fderiv ℝ F y = F' y) (v : E)
    (bound : E → ℝ) {δ : ℝ}
    (hbound : ∀ᵐ y ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) δ, ‖(fderiv ℝ F (y + t • v)) v‖ ≤ bound y) :
    ∀ᵐ y ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) δ, ‖(F' (y + t • v)) v‖ ≤ bound y := by
  filter_upwards [hbound] with y hy t ht
  simpa [hfderiv (y + t • v)] using hy t ht

end ShiftFun

private lemma hasDerivAt_shiftFun_at0_of_integrable_bound_core
    (x : cameronMartin μ) (F : E → ℝ) (hF_meas : Measurable F)
    {δ : ℝ} (hδ : 0 < δ)
    (hF_int : Integrable F μ)
    (bound : E → ℝ) (hbound_int : Integrable bound μ)
    (hbound : ∀ᵐ y ∂μ,
      ∀ t ∈ Metric.ball (0 : ℝ) δ, ‖(fderiv ℝ F (y + t • cmCoe x)) (cmCoe x)‖ ≤ bound y)
    {F' : E → E →L[ℝ] ℝ} (hF'cont : Continuous F') (hF' : ∀ y, HasFDerivAt F (F' y) y)
    (hfderiv : ∀ y, fderiv ℝ F y = F' y) :
    HasDerivAt (fun t => cameronMartinShiftFun (μ := μ) x F t)
      (∫ y, (fderiv ℝ F y) (cmCoe x) ∂μ) 0 := by
  let v : E := cmCoe x
  let G : ℝ → E → ℝ := fun t y => F (y + t • v)
  let G' : ℝ → E → ℝ := fun t y => (F' (y + t • v)) v
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := G) (F' := G') (s := Metric.ball (0 : ℝ) δ) (x₀ := (0 : ℝ))
      (bound := bound) (Metric.ball_mem_nhds _ hδ)
      (aestronglyMeasurable_shiftFun_integrand (μ := μ) (F := F) hF_meas v)
      (by simpa [G] using hF_int)
      (by
        simpa [G', zero_smul, add_zero] using
          (aestronglyMeasurable_shiftFun_integrandDeriv_at0 (μ := μ) hF'cont v))
      (norm_shiftFun_integrandDeriv_le_of_norm_fderiv_le (μ := μ) (F := F) hfderiv v bound
        (by simpa [v] using hbound))
      hbound_int
      (ae_of_all _ (fun y t ht => by
        simpa [G, G'] using hasDerivAt_shiftFun_integrand (F := F) hF' v t y))
  have hInt0 : (∫ y, G' 0 y ∂μ) = ∫ y, (fderiv ℝ F y) v ∂μ := by
    refine integral_congr_ae (ae_of_all _ (fun y => by simp [G', v, hfderiv y]))
  simpa [cameronMartinShiftFun, G, v, hInt0] using h.2

/-- Differentiate the Cameron–Martin shift functional at `t = 0` under a local domination hypothesis. -/
theorem hasDerivAt_shiftFun_at0_of_integrable_bound
    (x : cameronMartin μ) (F : E → ℝ) (hF_meas : Measurable F) (hF_c1 : ContDiff ℝ 1 F)
    {δ : ℝ} (hδ : 0 < δ)
    (hF_int : Integrable F μ)
    (bound : E → ℝ) (hbound_int : Integrable bound μ)
    (hbound : ∀ᵐ y ∂μ,
        ∀ t ∈ Metric.ball (0 : ℝ) δ, ‖(fderiv ℝ F (y + t • cmCoe x)) (cmCoe x)‖ ≤ bound y) :
    HasDerivAt (fun t => cameronMartinShiftFun (μ := μ) x F t)
      (∫ y, (fderiv ℝ F y) (cmCoe x) ∂μ) 0 := by
  classical
  rcases (contDiff_one_iff_hasFDerivAt.mp hF_c1) with ⟨F', hF'cont, hF'⟩
  exact hasDerivAt_shiftFun_at0_of_integrable_bound_core (μ := μ) x F hF_meas hδ hF_int bound
    hbound_int hbound hF'cont hF' (fun y => (hF' y).fderiv)

/-- Differentiate the Cameron–Martin shift functional at `t = 0` for bounded `F`. -/
theorem hasDerivAt_shiftFun_at0_bounded
    (x : cameronMartin μ) (F : E → ℝ) (hF_meas : Measurable F) (hF_c1 : ContDiff ℝ 1 F)
    {M0 M1 : ℝ} (hF_bdd : ∀ y, |F y| ≤ M0) (hF'_bdd : ∀ y, ‖fderiv ℝ F y‖ ≤ M1) :
    HasDerivAt (fun t => cameronMartinShiftFun (μ := μ) x F t)
      (∫ y, (fderiv ℝ F y) (cmCoe x) ∂μ) 0 := by
  have hF_int : Integrable F μ :=
    (integrable_const (μ := μ) (c := (|M0| : ℝ))).mono' hF_meas.aestronglyMeasurable <|
      ae_of_all _ (fun y => by simpa [Real.norm_eq_abs] using (hF_bdd y).trans (le_abs_self M0))
  let bound : E → ℝ := fun _ => (|M1| * ‖cmCoe x‖ : ℝ)
  have hbound_int : Integrable bound μ := integrable_const _
  have hbound : ∀ᵐ y ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) 1,
      ‖(fderiv ℝ F (y + t • cmCoe x)) (cmCoe x)‖ ≤ bound y := by
    refine ae_of_all _ (fun y t _ => ?_)
    have hOp := (fderiv ℝ F (y + t • cmCoe x)).le_opNorm (cmCoe x)
    have hB : ‖fderiv ℝ F (y + t • cmCoe x)‖ ≤ |M1| :=
      (hF'_bdd (y + t • cmCoe x)).trans (le_abs_self _)
    simpa [bound, mul_assoc] using hOp.trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  simpa using
    hasDerivAt_shiftFun_at0_of_integrable_bound (μ := μ) x F hF_meas hF_c1 (δ := (1 : ℝ))
      (by norm_num) hF_int bound hbound_int hbound

/-- Differentiate the Cameron–Martin shift functional at `t = 0` under polynomial growth. -/
theorem hasDerivAt_shiftFun_at0_polyGrowth
    (x : cameronMartin μ) (F : E → ℝ) (hF_meas : Measurable F) (hF_c1 : ContDiff ℝ 1 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ y, |F y| ≤ C * (1 + ‖y‖) ^ m)
    (hF'_growth : ∀ y, ‖fderiv ℝ F y‖ ≤ C * (1 + ‖y‖) ^ m) :
    HasDerivAt (fun t => cameronMartinShiftFun (μ := μ) x F t)
      (∫ y, (fderiv ℝ F y) (cmCoe x) ∂μ) 0 := by
  have hbase : Integrable (fun y : E => (1 + ‖y‖) ^ m) μ :=
    ProbabilityTheory.IsGaussian.integrable_one_add_norm_pow (μ := μ) m
  have hF_int : Integrable F μ :=
    (hbase.const_mul C).mono' hF_meas.aestronglyMeasurable <|
      ae_of_all _ (fun y => by simpa [Real.norm_eq_abs] using hF_growth y)
  let v : E := cmCoe x
  let bound : E → ℝ := fun y => (C * ‖v‖ * (1 + ‖v‖) ^ m) * (1 + ‖y‖) ^ m
  have hbound_int : Integrable bound μ := by
    simpa [bound, mul_assoc, mul_comm, mul_left_comm] using
      (hbase.const_mul (C * ‖v‖ * (1 + ‖v‖) ^ m))
  have hbound : ∀ᵐ y ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) (1 : ℝ),
      ‖(fderiv ℝ F (y + t • v)) v‖ ≤ bound y := by
    refine ae_of_all _ (fun y t ht => ?_)
    have ht1 : ‖t‖ ≤ (1 : ℝ) := le_of_lt (by simpa [Metric.mem_ball, Real.norm_eq_abs] using ht)
    have hnorm : ‖y + t • v‖ ≤ ‖y‖ + ‖v‖ := by
      have : ‖t • v‖ ≤ ‖v‖ := by simpa [norm_smul] using mul_le_mul_of_nonneg_right ht1 (norm_nonneg v)
      have htmp : ‖y‖ + ‖t • v‖ ≤ ‖y‖ + ‖v‖ := by
        simpa [add_comm] using add_le_add_right this ‖y‖
      exact (norm_add_le _ _).trans htmp
    have hle : 1 + ‖y + t • v‖ ≤ (1 + ‖v‖) * (1 + ‖y‖) := by
      have h1 : (1 : ℝ) + ‖y + t • v‖ ≤ (1 : ℝ) + (‖y‖ + ‖v‖) := by
        simpa [add_assoc, add_left_comm, add_comm] using (add_le_add_left hnorm 1)
      have h2 : (1 : ℝ) + (‖y‖ + ‖v‖) ≤ (1 + ‖v‖) * (1 + ‖y‖) := by
        nlinarith [norm_nonneg y, norm_nonneg v]
      exact h1.trans h2
    have hp : (1 + ‖y + t • v‖) ^ m ≤ ((1 + ‖v‖) * (1 + ‖y‖)) ^ m :=
      pow_le_pow_left₀ (by positivity) hle m
    have hOp := (fderiv ℝ F (y + t • v)).le_opNorm v
    have hB : ‖fderiv ℝ F (y + t • v)‖ ≤ C * (1 + ‖y + t • v‖) ^ m := hF'_growth (y + t • v)
    have : ‖(fderiv ℝ F (y + t • v)) v‖ ≤ (C * ‖v‖) * ((1 + ‖v‖) ^ m * (1 + ‖y‖) ^ m) := by
      calc
        ‖(fderiv ℝ F (y + t • v)) v‖ ≤ ‖fderiv ℝ F (y + t • v)‖ * ‖v‖ := hOp
        _ ≤ (C * (1 + ‖y + t • v‖) ^ m) * ‖v‖ := by gcongr
        _ ≤ (C * ((1 + ‖v‖) * (1 + ‖y‖)) ^ m) * ‖v‖ := by gcongr
        _ = (C * ‖v‖) * ((1 + ‖v‖) ^ m * (1 + ‖y‖) ^ m) := by
            simp [mul_assoc, mul_comm, mul_left_comm, mul_pow]
    -- final rearrangement to match `bound`
    simpa [bound, mul_assoc, mul_comm, mul_left_comm] using this
  simpa using
    hasDerivAt_shiftFun_at0_of_integrable_bound (μ := μ) x F hF_meas hF_c1 (δ := (1 : ℝ))
      (by norm_num) hF_int bound hbound_int hbound

/-
### Tilt functional: helper lemmas
-/

private lemma one_le_tilt_profile
    (x : cameronMartin μ) {δ : ℝ} (hδ : 0 < δ) (y : E) :
    (1 : ℝ) ≤ (δ * (‖x‖₊ ^ 2 : ℝ) + 1) * ((|x y| + 1) * Real.exp (δ * |x y|)) := by
  have hv : (1 : ℝ) ≤ δ * (‖x‖₊ ^ 2 : ℝ) + 1 := by
    have : 0 ≤ δ * (‖x‖₊ ^ 2 : ℝ) := mul_nonneg (le_of_lt hδ) (by positivity)
    linarith
  have hx : (1 : ℝ) ≤ |x y| + 1 := by nlinarith [abs_nonneg (x y)]
  have hexp : (1 : ℝ) ≤ Real.exp (δ * |x y|) := by
    have : 0 ≤ δ * |x y| := mul_nonneg (le_of_lt hδ) (abs_nonneg _)
    simpa using Real.one_le_exp_iff.mpr this
  have hxe : (1 : ℝ) ≤ (|x y| + 1) * Real.exp (δ * |x y|) := by
    have h0 : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
    simpa [one_mul] using mul_le_mul hx hexp h0 (by positivity)
  have h0 : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
  simpa [one_mul] using mul_le_mul hv hxe h0 (by positivity)

private lemma integrable_tilt_integrand_at0_of_integrable_profile
    (x : cameronMartin μ) (F : E → ℝ) (hF_meas : Measurable F)
    {δ : ℝ} (hδ : 0 < δ)
    (hInt : Integrable (fun y : E =>
      |F y| * (δ * (‖x‖₊ ^ 2 : ℝ) + 1) * ((|x y| + 1) * Real.exp (δ * |x y|))) μ) :
    Integrable (fun y : E => F y) μ := by
  have hmeas : AEStronglyMeasurable F μ := hF_meas.aestronglyMeasurable
  refine hInt.mono' hmeas ?_
  refine ae_of_all _ (fun y => ?_)
  have hfac : (1 : ℝ) ≤ (δ * (‖x‖₊ ^ 2 : ℝ) + 1) * ((|x y| + 1) * Real.exp (δ * |x y|)) :=
    one_le_tilt_profile (μ := μ) x hδ y
  have : |F y| ≤ |F y| * ((δ * (‖x‖₊ ^ 2 : ℝ) + 1) * ((|x y| + 1) * Real.exp (δ * |x y|))) := by
    simpa [mul_one] using mul_le_mul_of_nonneg_left hfac (abs_nonneg (F y))
  simpa [Real.norm_eq_abs, mul_assoc, mul_left_comm, mul_comm] using this

private lemma cameronMartinTiltFun_eq_integral_tiltKernel
    (x : cameronMartin μ) (F : E → ℝ) (t : ℝ) :
    cameronMartinTiltFun (μ := μ) x F t
      = ∫ y, F y * tiltKernel (‖x‖₊ ^ 2) t (x y) ∂μ := by
  have hk :
      (fun y : E => cameronMartinTiltKernel (μ := μ) x t y)
        =ᵐ[μ] fun y : E => tiltKernel (‖x‖₊ ^ 2) t (x y) :=
    cameronMartinTiltKernel_aeEq_tiltKernel (μ := μ) x t
  have hker :
      (fun y : E => cameronMartinTiltKernel (μ := μ) x t y * F y)
        =ᵐ[μ] fun y : E => F y * tiltKernel (‖x‖₊ ^ 2) t (x y) := by
    filter_upwards [hk] with y hy
    simp [hy, mul_comm]
  simpa [cameronMartinTiltFun] using integral_congr_ae hker

/-- Differentiate the Cameron–Martin tilt functional at `t = 0`, assuming an integrable domination profile. -/
theorem hasDerivAt_tiltFun_at0_of_integrable_profile
    (x : cameronMartin μ) (F : E → ℝ) (hF_meas : Measurable F)
    {δ : ℝ} (hδ : 0 < δ)
    (hInt : Integrable (fun y : E =>
      |F y| * (δ * (‖x‖₊ ^ 2 : ℝ) + 1) * ((|x y| + 1) * Real.exp (δ * |x y|))) μ) :
    HasDerivAt (fun t => cameronMartinTiltFun (μ := μ) x F t)
      (∫ y, (x y) * F y ∂μ) 0 := by
  let v : ℝ≥0 := ‖x‖₊ ^ 2
  let H : ℝ → E → ℝ := fun t y => F y * tiltKernel v t (x y)
  let H' : ℝ → E → ℝ := fun t y => F y * ((x y - (v : ℝ) * t) * tiltKernel v t (x y))
  have hx : AEMeasurable (fun y : E => x y) μ := (hasLaw_cameronMartin (μ := μ) x).aemeasurable
  have hH_meas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (H t) μ :=
    Filter.Eventually.of_forall (fun t => by
      have hcont : Continuous (fun u : ℝ => tiltKernel v t u) := by simp [tiltKernel]; continuity
      have htilt : AEStronglyMeasurable (fun y : E => tiltKernel v t (x y)) μ :=
        (hcont.measurable.comp_aemeasurable hx).aestronglyMeasurable
      simpa [H, mul_assoc] using (hF_meas.aestronglyMeasurable.mul htilt))
  have hH0 : Integrable (H 0) μ := by
    have hF_int : Integrable F μ :=
      integrable_tilt_integrand_at0_of_integrable_profile (μ := μ) x F hF_meas hδ hInt
    simpa [H, tiltKernel] using hF_int
  have hH'0 : AEStronglyMeasurable (H' 0) μ := by
    have hx' : AEStronglyMeasurable (fun y : E => x y) μ := hx.aestronglyMeasurable
    have hEq : (fun y : E => H' 0 y) = fun y : E => F y * x y := by
      funext y
      simp [H', tiltKernel, mul_comm]
    simpa [hEq] using (hF_meas.aestronglyMeasurable.mul hx')
  have hBnd : ∀ᵐ y ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) δ, ‖H' t y‖ ≤
      |F y| * (δ * (v : ℝ) + 1) * ((|x y| + 1) * Real.exp (δ * |x y|)) := by
    refine ae_of_all _ (fun y t ht => ?_)
    have ht1 : |t| ≤ δ := le_of_lt (by simpa [Metric.mem_ball, Real.norm_eq_abs] using ht)
    have h := gaussianTilt_deriv_dom_bound (v := v) (δ := δ) (hδ_pos := hδ) (F := fun _ : ℝ => F y) t ht1 (x := x y)
    simpa [H', Real.norm_eq_abs, mul_assoc, mul_left_comm, mul_comm] using h
  have hdiff : ∀ᵐ y ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) δ, HasDerivAt (fun s => H s y) (H' t y) t := by
    refine ae_of_all _ (fun y t ht => ?_)
    simpa [H, H', mul_assoc, mul_left_comm, mul_comm] using
      hasDerivAt_F_mul_tiltKernel (v := v) (F := fun _ : ℝ => F y) (x := (x y)) (t := t)
  have hs : Metric.ball (0 : ℝ) δ ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hδ
  have hInt' :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := H) (F' := H') (s := Metric.ball (0 : ℝ) δ) (x₀ := (0 : ℝ))
      (bound := fun y : E => |F y| * (δ * (v : ℝ) + 1) * ((|x y| + 1) * Real.exp (δ * |x y|)))
      hs hH_meas hH0 hH'0 hBnd hInt hdiff
  have hEq : (fun t => cameronMartinTiltFun (μ := μ) x F t) =ᶠ[𝓝 (0 : ℝ)] fun t => ∫ y, H t y ∂μ :=
    Filter.Eventually.of_forall (fun t => by
      have hv : v = ‖x‖₊ ^ 2 := rfl
      simpa [H, hv] using (cameronMartinTiltFun_eq_integral_tiltKernel (μ := μ) x F t))
  have h0 : (∫ y, H' 0 y ∂μ) = ∫ y, (x y) * F y ∂μ := by
    refine integral_congr_ae (ae_of_all _ (fun y => by
      simp [H', mul_comm]))
  have hDer : HasDerivAt (fun t => cameronMartinTiltFun (μ := μ) x F t) (∫ y, H' 0 y ∂μ) 0 :=
    hInt'.2.congr_of_eventuallyEq hEq
  simpa [h0] using hDer

/-- Differentiate the Cameron–Martin tilt functional at `t = 0` for bounded `F`. -/
theorem hasDerivAt_tiltFun_at0_bounded
    (x : cameronMartin μ) (F : E → ℝ) (hF_meas : Measurable F)
    {M0 : ℝ} (hF_bdd : ∀ y, |F y| ≤ M0) :
    HasDerivAt (fun t => cameronMartinTiltFun (μ := μ) x F t)
      (∫ y, (x y) * F y ∂μ) 0 := by
  have hprof := integrable_profile_cameronMartin (μ := μ) x (δ := (1 : ℝ)) (by norm_num)
  have hInt :
      Integrable (fun y : E =>
        |F y| * ((1 : ℝ) * (‖x‖₊ ^ 2 : ℝ) + 1) * ((|x y| + 1) * Real.exp ((1 : ℝ) * |x y|))) μ := by
    have hcoef0 : 0 ≤ ((1 : ℝ) * (‖x‖₊ ^ 2 : ℝ) + 1) := by positivity
    have hdom : Integrable (fun y : E => (|M0| * (((1 : ℝ) * (‖x‖₊ ^ 2 : ℝ) + 1))) *
        ((|x y| + 1) * Real.exp ((1 : ℝ) * |x y|))) μ :=
      hprof.const_mul (|M0| * (((1 : ℝ) * (‖x‖₊ ^ 2 : ℝ) + 1)))
    refine hdom.mono' (by fun_prop) (ae_of_all _ (fun y => ?_))
    have hy : |F y| ≤ |M0| := (hF_bdd y).trans (le_abs_self _)
    have hpos : 0 ≤ ((|x y| + 1) * Real.exp ((1 : ℝ) * |x y|)) := by positivity
    let A : ℝ :=
      ((1 : ℝ) * (‖x‖₊ ^ 2 : ℝ) + 1) * ((|x y| + 1) * Real.exp ((1 : ℝ) * |x y|))
    have hA : 0 ≤ A := by
      dsimp [A]
      exact mul_nonneg hcoef0 hpos
    have hmul : |F y| * A ≤ |M0| * A := mul_le_mul_of_nonneg_right hy hA
    have hFA : 0 ≤ |F y| * A := mul_nonneg (abs_nonneg _) hA
    calc
      ‖|F y| * ((1 : ℝ) * (‖x‖₊ ^ 2 : ℝ) + 1) * ((|x y| + 1) * Real.exp ((1 : ℝ) * |x y|))‖
          = ‖|F y| * A‖ := by simp [A, mul_assoc, mul_comm]
      _ = |F y| * A := by simp [Real.norm_of_nonneg hFA]
      _ ≤ |M0| * A := hmul
      _ = (|M0| * ((1 : ℝ) * (‖x‖₊ ^ 2 : ℝ) + 1)) *
            ((|x y| + 1) * Real.exp ((1 : ℝ) * |x y|)) := by
          simp [A, mul_assoc, mul_comm]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    hasDerivAt_tiltFun_at0_of_integrable_profile (μ := μ) x F hF_meas (δ := (1 : ℝ)) (by norm_num) hInt

/-- Differentiate the Cameron–Martin tilt functional at `t = 0` under polynomial growth. -/
theorem hasDerivAt_tiltFun_at0_polyGrowth
    (x : cameronMartin μ) (F : E → ℝ) (hF_meas : Measurable F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ y, |F y| ≤ C * (1 + ‖y‖) ^ m)
    {δ : ℝ} (hδ : 0 < δ) :
    HasDerivAt (fun t => cameronMartinTiltFun (μ := μ) x F t)
      (∫ y, (x y) * F y ∂μ) 0 := by
  -- `|F| ∈ L^2` by Fernique, and the exponential profile is in `L^2` by 1D reduction.
  have hAbs_meas : AEStronglyMeasurable (fun y : E => |F y|) μ :=
    (hF_meas.abs).aestronglyMeasurable
  have hAbs_sq_int : Integrable (fun y : E => (|F y|) ^ 2) μ := by
    have hbase :
        Integrable (fun y : E => (1 + ‖y‖) ^ (2 * m)) μ :=
      ProbabilityTheory.IsGaussian.integrable_one_add_norm_pow (μ := μ) (2 * m)
    have hdom : Integrable (fun y : E => (C ^ 2) * (1 + ‖y‖) ^ (2 * m)) μ :=
      hbase.const_mul (C ^ 2)
    refine hdom.mono' (by fun_prop) (ae_of_all _ (fun y => ?_))
    have hFy : |F y| ≤ C * (1 + ‖y‖) ^ m := hF_growth y
    have hnonneg : 0 ≤ C * (1 + ‖y‖) ^ m := by positivity
    have hsq : (|F y|) ^ 2 ≤ (C * (1 + ‖y‖) ^ m) ^ 2 := by
      simpa [pow_two] using
        (mul_le_mul hFy hFy (abs_nonneg _) hnonneg)
    have : (C * (1 + ‖y‖) ^ m) ^ 2 = (C ^ 2) * (1 + ‖y‖) ^ (2 * m) := by
      simp [pow_two, pow_mul, mul_assoc, mul_left_comm, mul_comm]
    have hnonneg' : 0 ≤ (|F y|) ^ 2 := by positivity
    have : ‖(|F y|) ^ 2‖ ≤ (C ^ 2) * (1 + ‖y‖) ^ (2 * m) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg', this] using hsq
    exact this
  have hAbs_L2 : MemLp (fun y : E => |F y|) 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hAbs_meas).2 (by
      simpa [pow_two] using hAbs_sq_int)
  have hProf_L2 : MemLp (fun y : E => (|x y| + 1) * Real.exp (δ * |x y|)) 2 μ :=
    memLp_profile_cameronMartin (μ := μ) x hδ
  have hprod :
      Integrable (fun y : E => |F y| * ((|x y| + 1) * Real.exp (δ * |x y|))) μ := by
    simpa [mul_assoc] using (MeasureTheory.MemLp.integrable_mul hAbs_L2 hProf_L2)
  have hInt :
      Integrable
        (fun y : E =>
          |F y| * (δ * (‖x‖₊ ^ 2 : ℝ) + 1) * ((|x y| + 1) * Real.exp (δ * |x y|))) μ := by
    -- constant factor `(δ * ‖x‖^2 + 1)` does not depend on `y`
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (hprod.const_mul (δ * (‖x‖₊ ^ 2 : ℝ) + 1))
  exact hasDerivAt_tiltFun_at0_of_integrable_profile (μ := μ) x F hF_meas hδ hInt

end CameronMartinIBPAnalytic

open CameronMartinIBPAnalytic
--set_option maxHeartbeats 1000000 in
/-- **Gaussian IBP (Cameron–Martin, bounded baseline).**

This is the infinite-dimensional “measure-level” IBP:
`∫ (x y) * F y dμ = ∫ (fderiv F y) (cmCoe x) dμ`,
proved by differentiating the Cameron–Martin identity at `t = 0` under the integral sign. -/
theorem cameronMartin_integral_by_parts_bounded
    (x : cameronMartin μ) (F : E → ℝ)
    (hF_meas : Measurable F)
    (hF_c1 : ContDiff ℝ 1 F)
    (hF_bdd : ∃ M : ℝ, ∀ y, |F y| ≤ M)
    (hF'_bdd : ∃ M : ℝ, ∀ y, ‖fderiv ℝ F y‖ ≤ M) :
    (∫ y, (x y) * F y ∂μ) = ∫ y, (fderiv ℝ F y) (cmCoe x) ∂μ := by
  rcases hF_bdd with ⟨M0, hM0⟩
  rcases hF'_bdd with ⟨M1, hM1⟩
  have hShift :=
    CameronMartinIBPAnalytic.hasDerivAt_shiftFun_at0_bounded (μ := μ) x F hF_meas hF_c1 hM0 hM1
  have hTilt :=
    CameronMartinIBPAnalytic.hasDerivAt_tiltFun_at0_bounded (μ := μ) x F hF_meas hM0
  exact cameronMartin_integral_by_parts_of_hasDerivAt (μ := μ) x F hF_meas hShift hTilt

/-- **Gaussian IBP (Cameron–Martin, polynomial growth).**

This is the measure-level IBP under the natural polynomial growth assumptions on `F` and `fderiv F`,
with integrability discharged via Fernique + the 1D domination profile along the Cameron–Martin
coordinate. -/
theorem cameronMartin_integral_by_parts_polyGrowth
    (x : cameronMartin μ) (F : E → ℝ)
    (hF_meas : Measurable F)
    (hF_c1 : ContDiff ℝ 1 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ y, |F y| ≤ C * (1 + ‖y‖) ^ m)
    (hF'_growth : ∀ y, ‖fderiv ℝ F y‖ ≤ C * (1 + ‖y‖) ^ m) :
    (∫ y, (x y) * F y ∂μ) = ∫ y, (fderiv ℝ F y) (cmCoe x) ∂μ := by
  have hShift :=
    CameronMartinIBPAnalytic.hasDerivAt_shiftFun_at0_polyGrowth (μ := μ)
      x F hF_meas hF_c1 hC hF_growth hF'_growth
  have hTilt :=
    CameronMartinIBPAnalytic.hasDerivAt_tiltFun_at0_polyGrowth (μ := μ)
      x F hF_meas hC hF_growth (δ := 1) (by norm_num)
  exact cameronMartin_integral_by_parts_of_hasDerivAt (μ := μ) x F hF_meas hShift hTilt

/-- **Gaussian IBP (Cameron–Martin, dominated shift + integrable tilt profile).**

This is the same measure-level IBP as `cameronMartin_integral_by_parts_bounded`, but with:
- shift derivative justified by a *local-in-`t`* domination hypothesis;
- tilt derivative justified by an *integrable profile* (cf. `hasDerivAt_tiltFun_at0_of_integrable_profile`). -/
theorem cameronMartin_integral_by_parts_of_integrable_bound
    (x : cameronMartin μ) (F : E → ℝ)
    (hF_meas : Measurable F)
    (hF_c1 : ContDiff ℝ 1 F)
    {δ : ℝ} (hδ : 0 < δ)
    (hF_int : Integrable F μ)
    (bound : E → ℝ) (hbound_int : Integrable bound μ)
    (hbound :  ∀ᵐ y ∂μ,
        ∀ t ∈ Metric.ball (0 : ℝ) δ, ‖(fderiv ℝ F (y + t • cmCoe x)) (cmCoe x)‖ ≤ bound y)
    (hTiltInt : Integrable
        (fun y : E =>
          |F y| * (δ * (‖x‖₊ ^ 2 : ℝ) + 1) * ((|x y| + 1) * Real.exp (δ * |x y|))) μ) :
    (∫ y, (x y) * F y ∂μ) = ∫ y, (fderiv ℝ F y) (cmCoe x) ∂μ := by
  have hShift :=
    CameronMartinIBPAnalytic.hasDerivAt_shiftFun_at0_of_integrable_bound (μ := μ)
      x F hF_meas hF_c1 hδ hF_int bound hbound_int hbound
  have hTilt :=
    CameronMartinIBPAnalytic.hasDerivAt_tiltFun_at0_of_integrable_profile (μ := μ)
      x F hF_meas hδ hTiltInt
  exact cameronMartin_integral_by_parts_of_hasDerivAt (μ := μ) x F hF_meas hShift hTilt

end ProbabilityTheory
