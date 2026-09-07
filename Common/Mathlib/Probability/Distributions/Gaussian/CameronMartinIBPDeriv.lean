import Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinIBP
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Cameron–Martin IBP: abstract step

If tilt equals shift near `0` and both are differentiable at `0`, uniqueness of derivatives yields
Gaussian IBP. Main: `cameronMartin_integral_by_parts_of_hasDerivAt`.
-/

open MeasureTheory Filter
open scoped Topology

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsGaussian μ]

/-! ## IBP as “derivative of tilt = derivative of shift” -/

/-- If tilt equals shift near `0` and both are differentiable at `0`, the derivative integrals coincide. -/
theorem cameronMartin_integral_by_parts_of_hasDerivAt
    (x : cameronMartin μ) (F : E → ℝ) (hF : Measurable F)
    (hShift : HasDerivAt (fun t => cameronMartinShiftFun (μ := μ) x F t) (∫ y, (fderiv ℝ F y)
    (cmCoe x) ∂μ) 0) (hTilt : HasDerivAt (fun t => cameronMartinTiltFun (μ := μ) x F t)
        (∫ y, (x y) * F y ∂μ)  0) : (∫ y, (x y) * F y ∂μ) = ∫ y, (fderiv ℝ F y) (cmCoe x) ∂μ := by
  have hEq : (fun t => cameronMartinShiftFun (μ := μ) x F t) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => cameronMartinTiltFun (μ := μ) x F t) := Filter.Eventually.of_forall (fun t =>
      cameronMartinShiftFun_eq_cameronMartinTiltFun (μ := μ) x F t hF)
  have hShift' : HasDerivAt (fun t => cameronMartinTiltFun (μ := μ) x F t)
        (∫ y, (fderiv ℝ F y) (cmCoe x) ∂μ) 0 := hShift.congr_of_eventuallyEq hEq.symm
  -- Uniqueness of derivatives at a point.
  have hderiv_eq := HasDerivAt.unique hShift' hTilt
  simp [hderiv_eq]

end ProbabilityTheory
