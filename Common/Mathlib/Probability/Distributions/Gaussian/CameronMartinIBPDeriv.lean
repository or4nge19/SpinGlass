import Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinIBP
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Cameron–Martin IBP: abstract differentiation step

This file isolates the **conceptual core** of Gaussian integration-by-parts in the
Cameron–Martin framework:

1. `cameronMartinShiftFun = cameronMartinTiltFun` (tilt = shift),
2. compute `HasDerivAt` of both sides at `t = 0`,
3. conclude the IBP identity by uniqueness of derivatives.

The heavy analytic work (dominated differentiation, Fernique bounds, growth assumptions on the
test function) is *not* done here: it is intended to be provided in application-specific layers.
-/

open MeasureTheory Filter
open scoped Topology

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsGaussian μ]

/-! ## IBP as “derivative of tilt = derivative of shift” -/

/--
**Cameron–Martin integration by parts (abstract form).**

Assume:
- the shift functional and the tilt functional are equal (`tilt = shift`) in a neighborhood of `0`,
- each side is differentiable at `0` with the stated derivatives.

Then the two derivative integrals coincide, giving the Gaussian IBP identity.

This lemma is intentionally minimal: it is the *formal* differentiation step.
-/
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
