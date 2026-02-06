import Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinTilt
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Cameron–Martin IBP scaffold (infinite-dimensional, measure-level)

This file provides the **core measure-level identity** underlying Gaussian integration by parts
in the Cameron–Martin framework:

`∫ F(y + cmCoe (t • x)) dμ = ∫ exp((t•x) y - ‖t•x‖^2/2) * F(y) dμ`,

for `x : cameronMartin μ`.

This is the principled starting point for an infinite-dimensional GIBP: one then differentiates
at `t = 0` using a dominated differentiation theorem (`Analysis/Calculus/ParametricIntegral`),
with integrability justified by Fernique-type estimates in concrete applications.
-/

open MeasureTheory Filter
open ContinuousLinearMap
open scoped ENNReal NNReal Topology InnerProductSpace

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsGaussian μ]

/-! ## Tilt = shift for Bochner integrals (real-valued) -/

/-- The shifted integral functional \(t \mapsto \int F(y + \mathrm{cmCoe}(t\cdot x))\,d\mu\). -/
noncomputable def cameronMartinShiftFun (x : cameronMartin μ) (F : E → ℝ) (t : ℝ) : ℝ :=
  ∫ y, F (y + cmCoe (t • x)) ∂μ

/-- The Cameron–Martin tilt kernel \( \exp(\langle t x, y\rangle - \|t x\|^2/2)\). -/
noncomputable def cameronMartinTiltKernel (x : cameronMartin μ) (t : ℝ) (y : E) : ℝ :=
  Real.exp ((t • x) y - ‖t • x‖ ^ 2 / 2)

/-- The tilted integral functional \(t \mapsto \int \exp(\cdots)\,F(y)\,d\mu\). -/
noncomputable def cameronMartinTiltFun (x : cameronMartin μ) (F : E → ℝ) (t : ℝ) : ℝ :=
  ∫ y, cameronMartinTiltKernel (μ := μ) x t y * F y ∂μ

/-- Real-integral form of the Cameron–Martin tilt/shift identity (scalar parameter `t`). -/
theorem integral_add_cmCoe_smul_eq
    (x : cameronMartin μ) (t : ℝ) (F : E → ℝ) (hF : Measurable F) :
    (∫ y, F (y + cmCoe (t • x)) ∂μ)
      =
      ∫ y, Real.exp ((t • x) y - ‖t • x‖ ^ 2 / 2) * F y ∂μ := by
  classical
  -- Step 1: rewrite the LHS as an integral against the pushforward measure.
  let g : E → E := fun y => y + cmCoe (t • x)
  have hg : Measurable g := by fun_prop
  have hF_ae : AEStronglyMeasurable F (Measure.map g μ) := hF.aestronglyMeasurable
  have hF_aeμ : AEStronglyMeasurable F μ := hF.aestronglyMeasurable
  have h_map :
      (∫ y, F (y + cmCoe (t • x)) ∂μ) = ∫ y, F y ∂(Measure.map g μ) := by
    simpa [g, Function.comp] using
      (MeasureTheory.integral_map (μ := μ) (φ := g) hg.aemeasurable hF_ae).symm
  -- Step 2: use the Cameron–Martin theorem to identify the pushforward with `withDensity`.
  have hμ :
      Measure.map g μ
        =
      μ.withDensity (fun y ↦ ENNReal.ofReal (Real.exp ((t • x) y - ‖t • x‖ ^ 2 / 2))) := by
    simpa [g] using (map_add_cameronMartin_eq_withDensity_smul_raw (μ := μ) x t)
  -- Step 3: rewrite the integral against `withDensity` as an integral against `μ`.
  have hlt : (∀ᵐ y ∂μ, (ENNReal.ofReal (Real.exp ((t • x) y - ‖t • x‖ ^ 2 / 2))) < ∞) := by
    filter_upwards with y
    simp
  have hwd :
      (∫ y, F y ∂(μ.withDensity (fun y ↦ ENNReal.ofReal (Real.exp ((t • x) y - ‖t • x‖ ^ 2 / 2)))))
        =
      ∫ y, (ENNReal.ofReal (Real.exp ((t • x) y - ‖t • x‖ ^ 2 / 2))).toReal • F y ∂μ := by
    simpa using
      (integral_withDensity_eq_integral_toReal_smul
        (μ := μ)
        (f := fun y ↦ ENNReal.ofReal (Real.exp ((t • x) y - ‖t • x‖ ^ 2 / 2)))
        (f_meas := by
          fun_prop)
        (hf_lt_top := hlt)
        (g := F))
  calc
    (∫ y, F (y + cmCoe (t • x)) ∂μ)
        = ∫ y, F y ∂(Measure.map g μ) := h_map
    _ = ∫ y, F y ∂(μ.withDensity (fun y ↦ ENNReal.ofReal (Real.exp ((t • x) y - ‖t • x‖ ^ 2 / 2)))) := by
          simp [hμ]
    _ = ∫ y, (ENNReal.ofReal (Real.exp ((t • x) y - ‖t • x‖ ^ 2 / 2))).toReal • F y ∂μ := hwd
    _ = ∫ y, Real.exp ((t • x) y - ‖t • x‖ ^ 2 / 2) * F y ∂μ := by
          have hnonneg :
              ∀ y : E, 0 ≤ Real.exp ((t • x) y - ‖t • x‖ ^ 2 / 2) := fun y =>
                by
                  have : 0 < Real.exp ((t • x) y - ‖t • x‖ ^ 2 / 2) := Real.exp_pos _
                  exact this.le
          refine integral_congr_ae ?_
          filter_upwards with y
          have htoReal :
              (ENNReal.ofReal (Real.exp ((t • x) y - ‖t • x‖ ^ 2 / 2))).toReal
                = Real.exp ((t • x) y - ‖t • x‖ ^ 2 / 2) :=
            ENNReal.toReal_ofReal (hnonneg y)
          calc
            (ENNReal.ofReal (Real.exp ((t • x) y - ‖t • x‖ ^ 2 / 2))).toReal • F y
                = (ENNReal.ofReal (Real.exp ((t • x) y - ‖t • x‖ ^ 2 / 2))).toReal * F y := by
                    simp [smul_eq_mul]
            _ = Real.exp ((t • x) y - ‖t • x‖ ^ 2 / 2) * F y := by
                    rw [htoReal]

/-- Packaged form: `cameronMartinShiftFun = cameronMartinTiltFun`. -/
theorem cameronMartinShiftFun_eq_cameronMartinTiltFun
    (x : cameronMartin μ) (F : E → ℝ) (t : ℝ) (hF : Measurable F) :
    cameronMartinShiftFun (μ := μ) x F t = cameronMartinTiltFun (μ := μ) x F t := by
  simpa [cameronMartinShiftFun, cameronMartinTiltFun, cameronMartinTiltKernel] using
    (integral_add_cmCoe_smul_eq (μ := μ) (x := x) (t := t) (F := F) hF)

/-- Same identity, writing the translation as `t • cmCoe x` using linearity of `cmCoe`. -/
theorem integral_add_smul_cmCoe_eq
    (x : cameronMartin μ) (t : ℝ) (F : E → ℝ) (hF : Measurable F) :
    (∫ y, F (y + t • cmCoe x) ∂μ)  =  ∫ y, Real.exp ((t • x) y - ‖t • x‖ ^ 2 / 2) * F y ∂μ := by
  simpa [map_smul] using (integral_add_cmCoe_smul_eq (μ := μ) (x := x) (t := t) (F := F) hF)

end ProbabilityTheory
