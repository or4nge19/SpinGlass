import SpinGlass.Mathlib.Probability.Distributions.Gaussian.CameronMartinIBPDeriv
import SpinGlass.Mathlib.Probability.Distributions.Gaussian.CameronMartinFernique
import SpinGlass.Mathlib.Probability.Distributions.GaussianIntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

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

/-- A tiny helper: the constant function `1` has moderate growth (in the 1D sense). -/
lemma hasModerateGrowth_one : HasModerateGrowth (fun _ : ℝ => (1 : ℝ)) := by
  refine ⟨1, 0, by norm_num, ?_, ?_⟩ <;> intro x <;> simp [pow_zero]

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

private lemma integrable_profile_gaussianReal (v : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun u : ℝ => (|u| + 1) * Real.exp (δ * |u|)) (gaussianReal 0 v) := by
  have h := integrable_dom_profile (hF := hasModerateGrowth_one) (v := v) (hδ := hδ)
    (hFmeas := measurable_const)
  simpa using h

lemma integrable_profile_cameronMartin (x : cameronMartin μ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun y : E => (|x y| + 1) * Real.exp (δ * |x y|)) μ := by
  have hx := hasLaw_cameronMartin (μ := μ) x
  have : Integrable (fun u : ℝ => (|u| + 1) * Real.exp (δ * |u|)) (Measure.map x μ) := by
    simpa [hx.map_eq] using (integrable_profile_gaussianReal (v := (‖x‖₊ ^ 2)) hδ)
  exact this.comp_aemeasurable hx.aemeasurable

private lemma hasModerateGrowth_sq_add_one : HasModerateGrowth (fun u : ℝ => u ^ 2 + 1) := by
  refine ⟨2, 2, by norm_num, ?_, ?_⟩
  · intro u
    have hu : 0 ≤ u ^ 2 + 1 := by nlinarith [sq_nonneg u]
    have habs : |u ^ 2 + 1| = u ^ 2 + 1 := abs_of_nonneg hu
    have hsq : (1 + |u|) ^ 2 = u ^ 2 + 2 * |u| + 1 := by
      -- expand and normalize; use `|u| * |u| = u * u`
      simp [pow_two, mul_add, add_mul, abs_mul_abs_self, add_assoc, add_left_comm, add_comm]
      ring_nf
    have hpow₁ : u ^ 2 + 1 ≤ (1 + |u|) ^ 2 := by
      have : (u ^ 2 + 1 : ℝ) ≤ u ^ 2 + 2 * |u| + 1 := by nlinarith [abs_nonneg u]
      -- rewrite the RHS as `(1 + |u|)^2`
      simpa [hsq] using this
    have hpow₂ : u ^ 2 + 1 ≤ 2 * (u ^ 2 + 1) := by nlinarith [hu]
    have hpow₃ : 2 * (u ^ 2 + 1) ≤ 2 * (1 + |u|) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hpow₁ (by norm_num : (0 : ℝ) ≤ 2)
    have hpow : u ^ 2 + 1 ≤ 2 * (1 + |u|) ^ 2 := hpow₂.trans hpow₃
    simpa [habs] using hpow
  · intro u
    have hderiv : deriv (fun u : ℝ => u ^ 2 + 1) u = 2 * u := by
      simp [pow_one]
    have hle_abs : |u| ≤ (1 + |u|) ^ 2 := by
      have : 0 ≤ (1 : ℝ) + |u| + |u| ^ 2 := by positivity
      -- `(1 + |u|)^2 = 1 + 2|u| + |u|^2 ≥ |u|`
      nlinarith [this]
    have hle : |2 * u| ≤ 2 * (1 + |u|) ^ 2 := by
      calc
        |2 * u| = (2 : ℝ) * |u| := by simp [abs_mul]
        _ ≤ (2 : ℝ) * (1 + |u|) ^ 2 := by
              exact mul_le_mul_of_nonneg_left hle_abs (by norm_num)
    simpa [hderiv]

private lemma integrable_profile_sq_gaussianReal (v : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun u : ℝ => ((|u| + 1) * Real.exp (δ * |u|)) ^ 2) (gaussianReal 0 v) := by
  have hInt_dom :=
    integrable_dom_profile_of_moderateGrowth (F := fun u : ℝ => u ^ 2 + 1) hasModerateGrowth_sq_add_one
      v (2 * δ) (by nlinarith) (by fun_prop)
  -- Dominate the square by the `integrable_dom_profile` integrand (up to a constant).
  refine (hInt_dom.const_mul 2).mono' (by fun_prop) (ae_of_all _ (fun u => ?_))
  have habs : (|u| + 1) ^ 2 ≤ 2 * (u ^ 2 + 1) := by
    have h2 : 2 * |u| ≤ u ^ 2 + 1 := by
      -- AM-GM with `a = |u|`, `b = 1`: `2ab ≤ a^2 + b^2`.
      simpa [mul_assoc, pow_two, sq_abs] using (two_mul_le_add_sq (|u|) (1 : ℝ))
    have hsq : (|u| + 1) ^ 2 = u ^ 2 + 2 * |u| + 1 := by
      simp [pow_two, mul_add, add_mul, abs_mul_abs_self, add_assoc, add_left_comm, add_comm]
      ring_nf
    have hle₁ : u ^ 2 + 2 * |u| ≤ u ^ 2 + (u ^ 2 + 1) := by
      simpa [add_assoc, add_comm, add_left_comm] using (add_le_add_left h2 (u ^ 2))
    have hle₂ : u ^ 2 + 2 * |u| + 1 ≤ u ^ 2 + (u ^ 2 + 1) + 1 := by
      simpa [add_assoc, add_comm, add_left_comm] using (add_le_add_right hle₁ 1)
    have : u ^ 2 + (u ^ 2 + 1) + 1 = 2 * (u ^ 2 + 1) := by ring_nf
    simpa [hsq, this] using hle₂
  have hnonneg_sq : 0 ≤ ((|u| + 1) * Real.exp (δ * |u|)) ^ 2 := by positivity
  have hFpos : 0 ≤ (u ^ 2 + 1 : ℝ) := by nlinarith [sq_nonneg u]
  have habsF : |u ^ 2 + 1| = u ^ 2 + 1 := abs_of_nonneg hFpos
  have hexp :
      (Real.exp (δ * |u|)) ^ 2 = Real.exp ((2 * δ) * |u|) := by
    calc
      (Real.exp (δ * |u|)) ^ 2 = Real.exp (δ * |u|) * Real.exp (δ * |u|) := by simp [pow_two]
      _ = Real.exp (δ * |u| + δ * |u|) := (Real.exp_add _ _).symm
      _ = Real.exp ((2 * δ) * |u|) := by ring_nf
  have hlin : (1 : ℝ) ≤ |u| + 1 := by nlinarith [abs_nonneg u]
  have hmul : (u ^ 2 + 1 : ℝ) ≤ (u ^ 2 + 1) * (|u| + 1) := by
    simpa [mul_one, habsF] using (mul_le_mul_of_nonneg_left hlin hFpos)
  have hnorm :
      ‖((|u| + 1) * Real.exp (δ * |u|)) ^ 2‖ = ((|u| + 1) * Real.exp (δ * |u|)) ^ 2 := by
    simpa using Real.norm_of_nonneg hnonneg_sq
  -- pointwise inequality
  calc
    ‖((|u| + 1) * Real.exp (δ * |u|)) ^ 2‖
        = ((|u| + 1) * Real.exp (δ * |u|)) ^ 2 := hnorm
    _ = (|u| + 1) ^ 2 * (Real.exp (δ * |u|)) ^ 2 := by ring
    _ ≤ (2 * (u ^ 2 + 1)) * Real.exp ((2 * δ) * |u|) := by
          -- use `habs` and rewrite the exponential square
          have := mul_le_mul_of_nonneg_right habs (by positivity : 0 ≤ (Real.exp (δ * |u|)) ^ 2)
          simpa [hexp, mul_assoc, mul_left_comm, mul_comm] using this
    _ ≤ 2 * (|u ^ 2 + 1| * (|u| + 1) * Real.exp ((2 * δ) * |u|)) := by
          -- insert an extra factor `( |u| + 1 ) ≥ 1`
          have hmul' :
              (u ^ 2 + 1) * Real.exp ((2 * δ) * |u|) ≤
                (u ^ 2 + 1) * (|u| + 1) * Real.exp ((2 * δ) * |u|) := by
            have : (u ^ 2 + 1) * Real.exp ((2 * δ) * |u|) ≤
                ((u ^ 2 + 1) * (|u| + 1)) * Real.exp ((2 * δ) * |u|) := by
              exact mul_le_mul_of_nonneg_right hmul (by positivity)
            simpa [mul_assoc] using this
          simpa [habsF, mul_assoc, mul_left_comm, mul_comm] using
            (mul_le_mul_of_nonneg_left hmul' (by positivity : 0 ≤ (2 : ℝ)))

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
  -- `MemLp` with `p=2` from integrability of the square
  exact (MeasureTheory.memLp_two_iff_integrable_sq hmeas).2 (by
    simpa [pow_two] using hsq)

theorem hasDerivAt_shiftFun_at0_bounded
    (x : cameronMartin μ) (F : E → ℝ) (hF_meas : Measurable F) (hF_c1 : ContDiff ℝ 1 F)
    {M0 M1 : ℝ} (hF_bdd : ∀ y, |F y| ≤ M0) (hF'_bdd : ∀ y, ‖fderiv ℝ F y‖ ≤ M1) :
    HasDerivAt (fun t => cameronMartinShiftFun (μ := μ) x F t)
      (∫ y, (fderiv ℝ F y) (cmCoe x) ∂μ) 0 := by
  rcases (contDiff_one_iff_hasFDerivAt.mp hF_c1) with ⟨F', hF'cont, hF'⟩
  have hfderiv : ∀ y, fderiv ℝ F y = F' y := fun y => (hF' y).fderiv
  let v : E := cmCoe x
  let G : ℝ → E → ℝ := fun t y => F (y + t • v)
  let G' : ℝ → E → ℝ := fun t y => (F' (y + t • v)) v
  have hG_meas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (G t) μ :=
    Filter.Eventually.of_forall (fun t => (hF_meas.comp (by fun_prop)).aestronglyMeasurable)
  have hG0_int : Integrable (G 0) μ :=
    (integrable_const (μ := μ) (c := (|M0| : ℝ))).mono'
      ((hF_meas.comp (by fun_prop)).aestronglyMeasurable)
      (ae_of_all _ (fun y => by
        have h := hF_bdd y
        simpa [G, v, Real.norm_eq_abs] using h.trans (le_abs_self _)))
  have hG'_meas0 : AEStronglyMeasurable (G' 0) μ := by
    have : Measurable (fun y : E => (F' y) v) :=
      (ContinuousLinearMap.measurable_apply v).comp hF'cont.measurable
    simpa [G', v] using this.aestronglyMeasurable
  have h_bound : ∀ᵐ y ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) 1, ‖G' t y‖ ≤ (|M1| * ‖v‖) := by
    refine ae_of_all _ (fun y t ht => ?_)
    have hOp : ‖(F' (y + t • v)) v‖ ≤ ‖F' (y + t • v)‖ * ‖v‖ :=
      (F' (y + t • v)).le_opNorm v
    have hB : ‖F' (y + t • v)‖ ≤ |M1| := by
      have : ‖fderiv ℝ F (y + t • v)‖ ≤ M1 := hF'_bdd (y + t • v)
      simpa [hfderiv (y + t • v)] using this.trans (le_abs_self _)
    simpa [G', v, mul_assoc] using hOp.trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  have hBound_int : Integrable (fun _ : E => (|M1| * ‖v‖ : ℝ)) μ :=
    integrable_const (μ := μ) (c := (|M1| * ‖v‖ : ℝ))
  have h_diff : ∀ᵐ y ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) 1, HasDerivAt (fun s => G s y) (G' t y) t := by
    refine ae_of_all _ (fun y t ht => ?_)
    have hline : HasDerivAt (fun s : ℝ => y + s • v) v t := by
      simpa [add_comm, add_left_comm, add_assoc] using (HasDerivAt.smul_const (hasDerivAt_id t) v).const_add y
    simpa [G, G'] using ((hF' (y + t • v)).comp_hasDerivAt t hline)
  have hs : Metric.ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ (by norm_num)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := G) (F' := G') (s := Metric.ball (0 : ℝ) 1) (x₀ := (0 : ℝ))
      (bound := fun _ : E => (|M1| * ‖v‖ : ℝ)) hs hG_meas hG0_int hG'_meas0 h_bound hBound_int h_diff
  have hInt0 : (∫ y, G' 0 y ∂μ) = ∫ y, (fderiv ℝ F y) v ∂μ := by
    refine integral_congr_ae (ae_of_all _ (fun y => by simp [G', v, hfderiv y]))
  simpa [cameronMartinShiftFun, G, v, hInt0] using h.2

theorem hasDerivAt_shiftFun_at0_of_integrable_bound
    (x : cameronMartin μ) (F : E → ℝ) (hF_meas : Measurable F) (hF_c1 : ContDiff ℝ 1 F)
    {δ : ℝ} (hδ : 0 < δ)
    (hF_int : Integrable F μ)
    (bound : E → ℝ) (hbound_int : Integrable bound μ)
    (hbound : ∀ᵐ y ∂μ,
        ∀ t ∈ Metric.ball (0 : ℝ) δ, ‖(fderiv ℝ F (y + t • cmCoe x)) (cmCoe x)‖ ≤ bound y) :
    HasDerivAt (fun t => cameronMartinShiftFun (μ := μ) x F t)
      (∫ y, (fderiv ℝ F y) (cmCoe x) ∂μ) 0 := by
  rcases (contDiff_one_iff_hasFDerivAt.mp hF_c1) with ⟨F', hF'cont, hF'⟩
  have hfderiv : ∀ y, fderiv ℝ F y = F' y := fun y => (hF' y).fderiv
  let v : E := cmCoe x
  let G : ℝ → E → ℝ := fun t y => F (y + t • v)
  let G' : ℝ → E → ℝ := fun t y => (F' (y + t • v)) v
  have hG_meas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (G t) μ :=
    Filter.Eventually.of_forall (fun t => (hF_meas.comp (by fun_prop)).aestronglyMeasurable)
  have hG0_int : Integrable (G 0) μ := by simpa [G] using hF_int
  have hG'_meas0 : AEStronglyMeasurable (G' 0) μ := by
    have : Measurable (fun y : E => (F' y) v) :=
      (ContinuousLinearMap.measurable_apply v).comp hF'cont.measurable
    simpa [G', v] using this.aestronglyMeasurable
  have h_bound : ∀ᵐ y ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) δ, ‖G' t y‖ ≤ bound y := by
    filter_upwards [hbound] with y hy t ht
    have : ‖(fderiv ℝ F (y + t • v)) v‖ ≤ bound y := by
      simpa [v] using hy t ht
    simpa [G', v, hfderiv (y + t • v)] using this
  have h_diff : ∀ᵐ y ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) δ, HasDerivAt (fun s => G s y) (G' t y) t := by
    refine ae_of_all _ (fun y t ht => ?_)
    have hline : HasDerivAt (fun s : ℝ => y + s • v) v t := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (HasDerivAt.smul_const (hasDerivAt_id t) v).const_add y
    simpa [G, G'] using ((hF' (y + t • v)).comp_hasDerivAt t hline)
  have hs : Metric.ball (0 : ℝ) δ ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hδ
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := G) (F' := G') (s := Metric.ball (0 : ℝ) δ) (x₀ := (0 : ℝ))
      (bound := bound) hs hG_meas hG0_int hG'_meas0 h_bound hbound_int h_diff
  have hInt0 : (∫ y, G' 0 y ∂μ) = ∫ y, (fderiv ℝ F y) v ∂μ := by
    refine integral_congr_ae (ae_of_all _ (fun y => by simp [G', v, hfderiv y]))
  simpa [cameronMartinShiftFun, G, v, hInt0] using h.2

theorem hasDerivAt_shiftFun_at0_polyGrowth
    (x : cameronMartin μ) (F : E → ℝ) (hF_meas : Measurable F) (hF_c1 : ContDiff ℝ 1 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ y, |F y| ≤ C * (1 + ‖y‖) ^ m)
    (hF'_growth : ∀ y, ‖fderiv ℝ F y‖ ≤ C * (1 + ‖y‖) ^ m) :
    HasDerivAt (fun t => cameronMartinShiftFun (μ := μ) x F t)
      (∫ y, (fderiv ℝ F y) (cmCoe x) ∂μ) 0 := by
  rcases (contDiff_one_iff_hasFDerivAt.mp hF_c1) with ⟨F', hF'cont, hF'⟩
  have hfderiv : ∀ y, fderiv ℝ F y = F' y := fun y => (hF' y).fderiv
  let v : E := cmCoe x
  let G : ℝ → E → ℝ := fun t y => F (y + t • v)
  let G' : ℝ → E → ℝ := fun t y => (F' (y + t • v)) v
  have hG_meas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (G t) μ :=
    .of_forall (fun t => (hF_meas.comp (by fun_prop)).aestronglyMeasurable)
  have hG0_int : Integrable (G 0) μ := by
    have hbase : Integrable (fun y : E => (1 + ‖y‖) ^ m) μ :=
      ProbabilityTheory.IsGaussian.integrable_one_add_norm_pow (μ := μ) m
    refine (hbase.const_mul C).mono' (hG_meas.self_of_nhds) (ae_of_all _ (fun y => ?_))
    simpa [G, Real.norm_eq_abs] using hF_growth y
  have hG'_meas0 : AEStronglyMeasurable (G' 0) μ := by
    have : Measurable (fun y : E => (F' y) v) :=
      (ContinuousLinearMap.measurable_apply v).comp hF'cont.measurable
    simpa [G', v] using this.aestronglyMeasurable
  let bound : E → ℝ := fun y =>
    (C * (2 : ℝ) ^ (m - 1) * ‖v‖) * ((1 + ‖v‖) ^ m + ‖y‖ ^ m)
  have h_bound : ∀ᵐ y ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) 1, ‖G' t y‖ ≤ bound y := by
    refine ae_of_all _ (fun y t ht => ?_)
    have ht1 : ‖t‖ ≤ (1 : ℝ) := le_of_lt (by simpa [Metric.mem_ball, Real.norm_eq_abs] using ht)
    have hnorm : ‖y + t • v‖ ≤ ‖y‖ + ‖v‖ := by
      have ht' : ‖t • v‖ ≤ ‖v‖ := by
        simpa [norm_smul] using mul_le_mul_of_nonneg_right ht1 (norm_nonneg v)
      have htmp : ‖y‖ + ‖t • v‖ ≤ ‖y‖ + ‖v‖ := by
        simpa [add_comm] using (add_le_add_right ht' ‖y‖)
      exact (norm_add_le _ _).trans htmp
    have hOp : ‖(F' (y + t • v)) v‖ ≤ ‖F' (y + t • v)‖ * ‖v‖ :=
      (F' (y + t • v)).le_opNorm v
    have hB : ‖F' (y + t • v)‖ ≤ C * (1 + ‖y + t • v‖) ^ m := by
      have : ‖fderiv ℝ F (y + t • v)‖ ≤ C * (1 + ‖y + t • v‖) ^ m := hF'_growth (y + t • v)
      simpa [hfderiv (y + t • v)] using this
    have h1 : (1 + ‖y + t • v‖) ^ m ≤ (1 + (‖y‖ + ‖v‖)) ^ m := by
      have hbase : (1 : ℝ) + ‖y + t • v‖ ≤ 1 + (‖y‖ + ‖v‖) := by
        simpa [add_comm, add_left_comm, add_assoc] using (add_le_add_right hnorm 1)
      exact pow_le_pow_left₀ (by positivity) hbase m
    have h2 : (1 + (‖y‖ + ‖v‖)) ^ m ≤ (2 : ℝ) ^ (m - 1) * ((1 + ‖v‖) ^ m + ‖y‖ ^ m) := by
      have : (1 + (‖y‖ + ‖v‖)) ^ m = ((1 + ‖v‖) + ‖y‖) ^ m := by ring
      simpa [this, add_comm, add_left_comm, add_assoc] using
        (add_pow_le (a := (1 + ‖v‖ : ℝ)) (b := (‖y‖ : ℝ)) (by positivity) (by positivity) m)
    have hmul : ‖F' (y + t • v)‖ ≤ C * (2 : ℝ) ^ (m - 1) * ((1 + ‖v‖) ^ m + ‖y‖ ^ m) := by
      calc
        ‖F' (y + t • v)‖ ≤ C * (1 + ‖y + t • v‖) ^ m := hB
        _ ≤ C * (1 + (‖y‖ + ‖v‖)) ^ m := by gcongr
        _ ≤ C * ((2 : ℝ) ^ (m - 1) * ((1 + ‖v‖) ^ m + ‖y‖ ^ m)) := by gcongr
        _ = C * (2 : ℝ) ^ (m - 1) * ((1 + ‖v‖) ^ m + ‖y‖ ^ m) := by ring
    have : ‖G' t y‖ ≤ bound y := by
      have := hOp.trans (mul_le_mul_of_nonneg_right hmul (norm_nonneg _))
      simpa [G', bound, mul_assoc, mul_left_comm, mul_comm] using this
    exact this
  have hBound_int : Integrable bound μ := by
    have hpow : Integrable (fun y : E => ‖y‖ ^ m) μ :=
      ProbabilityTheory.IsGaussian.integrable_norm_pow (μ := μ) m
    have hsum : Integrable (fun y : E => (1 + ‖v‖) ^ m + ‖y‖ ^ m) μ :=
      (integrable_const (μ := μ) (c := ((1 + ‖v‖) ^ m : ℝ))).add hpow
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using
      (hsum.const_mul (C * (2 : ℝ) ^ (m - 1) * ‖v‖))
  have h_diff : ∀ᵐ y ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) 1, HasDerivAt (fun s => G s y) (G' t y) t := by
    refine ae_of_all _ (fun y t _ht => ?_)
    have hline : HasDerivAt (fun s : ℝ => y + s • v) v t := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (HasDerivAt.smul_const (hasDerivAt_id t) v).const_add y
    simpa [G, G'] using ((hF' (y + t • v)).comp_hasDerivAt t hline)
  have hs : Metric.ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ (by norm_num)
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := G) (F' := G') (s := Metric.ball (0 : ℝ) 1) (x₀ := (0 : ℝ))
      (bound := bound) hs hG_meas hG0_int hG'_meas0 h_bound hBound_int h_diff
  have hInt0 : (∫ y, G' 0 y ∂μ) = ∫ y, (fderiv ℝ F y) v ∂μ := by
    refine integral_congr_ae (ae_of_all _ (fun y => by simp [G', v, hfderiv y]))
  simpa [cameronMartinShiftFun, G, v, bound, hInt0] using h.2

theorem hasDerivAt_tiltFun_at0_bounded
    (x : cameronMartin μ) (F : E → ℝ) (hF_meas : Measurable F)
    {M0 : ℝ} (hF_bdd : ∀ y, |F y| ≤ M0) :
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
  have hH0 : Integrable (H 0) μ :=
    (integrable_const (μ := μ) (c := (|M0| : ℝ))).mono' (hH_meas.self_of_nhds)
      (ae_of_all _ (fun y => by
        have h := hF_bdd y
        simpa [H, tiltKernel, Real.norm_eq_abs] using h.trans (le_abs_self _)))
  have hH'0 : AEStronglyMeasurable (H' 0) μ := by
    have hx' : AEStronglyMeasurable (fun y : E => x y) μ := hx.aestronglyMeasurable
    have hEq : (fun y : E => H' 0 y) = fun y : E => F y * x y := by
      funext y
      simp [H', tiltKernel, mul_comm]
    simpa [hEq] using (hF_meas.aestronglyMeasurable.mul hx')
  have hBnd : ∀ᵐ y ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) 1, ‖H' t y‖ ≤ |F y| * ((v : ℝ) + 1) * (|x y| + 1) * Real.exp ((1 : ℝ) * |x y|) := by
    refine ae_of_all _ (fun y t ht => ?_)
    have ht1 : |t| ≤ (1 : ℝ) := le_of_lt (by simpa [Metric.mem_ball, Real.norm_eq_abs] using ht)
    have h := gaussianTilt_deriv_dom_bound (v := v) (δ := (1 : ℝ)) (hδ_pos := by norm_num) (F := fun _ : ℝ => F y) t ht1 (x := x y)
    simpa [H', Real.norm_eq_abs, mul_assoc, mul_left_comm, mul_comm] using h
  have hBnd_int : Integrable (fun y : E => |F y| * ((v : ℝ) + 1) * (|x y| + 1) * Real.exp ((1 : ℝ) * |x y|)) μ := by
    have hprof := integrable_profile_cameronMartin (μ := μ) x (δ := (1 : ℝ)) (by norm_num)
    have hcoef : 0 ≤ (v : ℝ) + 1 := by simpa using add_nonneg v.property zero_le_one
    have hg : Integrable (fun y : E => (|M0| * ((v : ℝ) + 1)) * ((|x y| + 1) * Real.exp ((1 : ℝ) * |x y|))) μ :=
      hprof.const_mul (|M0| * ((v : ℝ) + 1))
    refine hg.mono' (by fun_prop) (ae_of_all _ (fun y => ?_))
    have hy : |F y| ≤ |M0| := (hF_bdd y).trans (le_abs_self _)
    have hpos : 0 ≤ (|x y| + 1) * Real.exp ((1 : ℝ) * |x y|) := by positivity
    have hle : |F y| * ((v : ℝ) + 1) * ((|x y| + 1) * Real.exp ((1 : ℝ) * |x y|))
        ≤ |M0| * ((v : ℝ) + 1) * ((|x y| + 1) * Real.exp ((1 : ℝ) * |x y|)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hy hcoef) hpos
    have hnon : 0 ≤ |F y| * ((v : ℝ) + 1) * ((|x y| + 1) * Real.exp ((1 : ℝ) * |x y|)) :=
      mul_nonneg (mul_nonneg (abs_nonneg _) hcoef) hpos
    have : ‖|F y| * ((v : ℝ) + 1) * ((|x y| + 1) * Real.exp ((1 : ℝ) * |x y|))‖
        ≤ |M0| * ((v : ℝ) + 1) * ((|x y| + 1) * Real.exp ((1 : ℝ) * |x y|)) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hnon]
      simpa [mul_assoc, mul_left_comm, mul_comm] using hle
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hdiff : ∀ᵐ y ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) 1, HasDerivAt (fun s => H s y) (H' t y) t := by
    refine ae_of_all _ (fun y t ht => ?_)
    simpa [H, H', mul_assoc, mul_left_comm, mul_comm] using
      hasDerivAt_F_mul_tiltKernel (v := v) (F := fun _ : ℝ => F y) (x := (x y)) (t := t)
  have hs : Metric.ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ (by norm_num)
  have hInt :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := H) (F' := H') (s := Metric.ball (0 : ℝ) 1) (x₀ := (0 : ℝ))
      (bound := fun y : E => |F y| * ((v : ℝ) + 1) * (|x y| + 1) * Real.exp ((1 : ℝ) * |x y|))
      hs hH_meas hH0 hH'0 hBnd hBnd_int hdiff
  have hEq : (fun t => cameronMartinTiltFun (μ := μ) x F t) =ᶠ[𝓝 (0 : ℝ)] fun t => ∫ y, H t y ∂μ :=
    Filter.Eventually.of_forall (fun t => by
      have hk : (fun y : E => cameronMartinTiltKernel (μ := μ) x t y)
            =ᵐ[μ] fun y : E => tiltKernel (‖x‖₊ ^ 2) t (x y) :=
        cameronMartinTiltKernel_aeEq_tiltKernel (μ := μ) x t
      have hker : (fun y : E => cameronMartinTiltKernel (μ := μ) x t y * F y)
            =ᵐ[μ] fun y : E => H t y := by
        filter_upwards [hk] with y hy
        simp [H, v, hy, mul_comm]
      exact integral_congr_ae hker)
  have h0 : (∫ y, H' 0 y ∂μ) = ∫ y, (x y) * F y ∂μ := by
    refine integral_congr_ae (ae_of_all _ (fun y => by simp [H', tiltKernel, mul_comm]))
  have hDer : HasDerivAt (fun t => cameronMartinTiltFun (μ := μ) x F t) (∫ y, H' 0 y ∂μ) 0 :=
    hInt.2.congr_of_eventuallyEq hEq
  simpa [h0] using hDer

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
    have hmeas : AEStronglyMeasurable (H 0) μ := hH_meas.self_of_nhds
    have hbound : ∀ᵐ y ∂μ, ‖H 0 y‖ ≤
        |F y| * (δ * (v : ℝ) + 1) * ((|x y| + 1) * Real.exp (δ * |x y|)) := by
      refine ae_of_all _ (fun y => ?_)
      have hv1 : (1 : ℝ) ≤ δ * (v : ℝ) + 1 := by
        have : 0 ≤ δ * (v : ℝ) := mul_nonneg (le_of_lt hδ) v.property
        linarith
      have hx1 : (1 : ℝ) ≤ |x y| + 1 := by nlinarith [abs_nonneg (x y)]
      have hexp : 1 ≤ Real.exp (δ * |x y|) := by
        have : 0 ≤ δ * |x y| := mul_nonneg (le_of_lt hδ) (abs_nonneg _)
        simpa using Real.one_le_exp_iff.mpr this
      have hab : (1 : ℝ) ≤ (|x y| + 1) * Real.exp (δ * |x y|) := by
        have h0 : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
        simpa [one_mul] using (mul_le_mul hx1 hexp h0 (by positivity))
      have hprod1 :
          (1 : ℝ) ≤ (δ * (v : ℝ) + 1) * ((|x y| + 1) * Real.exp (δ * |x y|)) := by
        have h0 : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
        simpa [one_mul] using (mul_le_mul hv1 hab h0 (by positivity))
      have : |F y| ≤ |F y| * ((δ * (v : ℝ) + 1) * ((|x y| + 1) * Real.exp (δ * |x y|))) := by
        simpa [mul_one] using (mul_le_mul_of_nonneg_left hprod1 (abs_nonneg (F y)))
      simpa [H, tiltKernel, Real.norm_eq_abs, mul_assoc, mul_left_comm, mul_comm] using this
    -- `hInt` dominates `H 0` since the profile factor is ≥ 1.
    exact hInt.mono' hmeas hbound
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
      have hk :
          (fun y : E => cameronMartinTiltKernel (μ := μ) x t y)
            =ᵐ[μ] fun y : E => tiltKernel (‖x‖₊ ^ 2) t (x y) :=
        cameronMartinTiltKernel_aeEq_tiltKernel (μ := μ) x t
      have hker :
          (fun y : E => cameronMartinTiltKernel (μ := μ) x t y * F y)
            =ᵐ[μ] fun y : E => H t y := by
        filter_upwards [hk] with y hy
        have hv : v = ‖x‖₊ ^ 2 := rfl
        change cameronMartinTiltKernel (μ := μ) x t y * F y = F y * tiltKernel v t (x y)
        rw [hy, hv.symm]
        exact mul_comm _ _
      exact integral_congr_ae hker)
  have h0 : (∫ y, H' 0 y ∂μ) = ∫ y, (x y) * F y ∂μ := by
    refine integral_congr_ae (ae_of_all _ (fun y => by
      simp [H', mul_comm]))
  have hDer : HasDerivAt (fun t => cameronMartinTiltFun (μ := μ) x F t) (∫ y, H' 0 y ∂μ) 0 :=
    hInt'.2.congr_of_eventuallyEq hEq
  simpa [h0] using hDer

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
    -- rewrite the RHS square
    have : (C * (1 + ‖y‖) ^ m) ^ 2 = (C ^ 2) * (1 + ‖y‖) ^ (2 * m) := by
      simp [pow_two, pow_mul, mul_assoc, mul_left_comm, mul_comm, Nat.mul_comm]
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
set_option maxHeartbeats 1000000 in
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
