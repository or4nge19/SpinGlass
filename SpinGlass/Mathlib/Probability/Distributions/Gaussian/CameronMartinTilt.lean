import SpinGlass.Mathlib.Probability.Distributions.Gaussian.CameronMartinThm

/-!
# Cameron–Martin theorem: scalar-parameter corollaries

This file provides  lemmas specializing the Cameron–Martin theorem to the common
“scalar parameter” form `t • x`.
-/

open MeasureTheory Filter Complex
open scoped ENNReal NNReal Topology InnerProductSpace

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsGaussian μ]

/-- Cameron–Martin theorem, packaged for `t • x` (raw exponent form). -/
theorem map_add_cameronMartin_eq_withDensity_smul_raw (x : cameronMartin μ) (t : ℝ) :
    μ.map (fun y ↦ y + cmCoe (t • x))
      =
      μ.withDensity (fun y ↦ ENNReal.ofReal (.exp ((t • x) y - ‖t • x‖ ^ 2 / 2))) := by
  simpa using (map_add_cameronMartin_eq_withDensity (μ := μ) (x := (t • x)))

/-- Absolute continuity for translation by `cmCoe (t • x)`. -/
theorem absolutelyContinuous_map_add_cameronMartin_smul_raw (x : cameronMartin μ) (t : ℝ) :
    μ.map (fun y ↦ y + cmCoe (t • x)) ≪ μ := by
  simpa using (absolutelyContinuous_map_add_cameronMartin (μ := μ) (x := (t • x)))

/-- The “tilted expectation functional” associated with `t • x` (nonnegative version). -/
noncomputable
def cameronMartinTilt (x : cameronMartin μ) (F : E → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, F y * ENNReal.ofReal (.exp ((t • x) y - ‖t • x‖ ^ 2 / 2)) ∂μ

/-- `lintegral` form of the Cameron–Martin theorem (raw), for `t • x`. -/
theorem lintegral_add_cmCoe_smul_eq (x : cameronMartin μ) (t : ℝ) (F : E → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ y, F (y + cmCoe (t • x)) ∂μ)
      =
      ∫⁻ y, F y * (ENNReal.ofReal (.exp ((t • x) y - ‖t • x‖ ^ 2 / 2))) ∂μ := by
  set g : E → E := fun y ↦ y + cmCoe (t • x)
  have hg : Measurable g := by
    fun_prop
  have hμ :
      μ.map g = μ.withDensity (fun y ↦ ENNReal.ofReal (.exp ((t • x) y - ‖t • x‖ ^ 2 / 2))) := by
    simpa [g] using (map_add_cameronMartin_eq_withDensity_smul_raw (μ := μ) x t)
  calc
    (∫⁻ y, F (y + cmCoe (t • x)) ∂μ)
        = ∫⁻ y, F y ∂(μ.map g) := by
            simpa [g, Function.comp] using (lintegral_comp (μ := μ) (f := F) (g := g) hF hg)
    _ = ∫⁻ y, F y ∂(μ.withDensity fun y ↦ ENNReal.ofReal (.exp ((t • x) y - ‖t • x‖ ^ 2 / 2))) := by
            simp [hμ]
    _ =
        ∫⁻ y, ((fun y ↦ ENNReal.ofReal (.exp ((t • x) y - ‖t • x‖ ^ 2 / 2))) * F) y ∂μ := by
            simpa using
              (lintegral_withDensity_eq_lintegral_mul μ
                (f := fun y ↦ ENNReal.ofReal (.exp ((t • x) y - ‖t • x‖ ^ 2 / 2))) (by fun_prop) hF)
    _ = ∫⁻ y, F y * (ENNReal.ofReal (.exp ((t • x) y - ‖t • x‖ ^ 2 / 2))) ∂μ := by
            simp [Pi.mul_apply, mul_comm]

/-- `cameronMartinTilt` equals the translated `lintegral` (the “tilt = shift” form). -/
theorem cameronMartinTilt_eq_lintegral_shift (x : cameronMartin μ) (F : E → ℝ≥0∞) (t : ℝ)
    (hF : Measurable F) :
    cameronMartinTilt (μ := μ) x F t = ∫⁻ y, F (y + cmCoe (t • x)) ∂μ := by
  simpa [cameronMartinTilt] using
    (lintegral_add_cmCoe_smul_eq (μ := μ) (x := x) (t := t) (F := F) hF).symm

end ProbabilityTheory
