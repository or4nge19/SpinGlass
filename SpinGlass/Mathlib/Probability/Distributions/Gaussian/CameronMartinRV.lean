import SpinGlass.Mathlib.Probability.Distributions.Gaussian.CameronMartinTilt

/-!
# Cameron–Martin theorem: random-variable (HasLaw) corollaries

This file transports the measure-level Cameron–Martin shift/tilt identity to random variables
using `ProbabilityTheory.HasLaw`.

It avoids committing to a specific “Gaussian random variable” structure (finite-dimensional,
Hilbert, etc.). Downstream files can provide `HasLaw` instances and then use these lemmas.
-/

open MeasureTheory
open scoped ENNReal Real Topology

namespace ProbabilityTheory

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace E] [SecondCountableTopology E]

variable {P : Measure Ω} {μ : Measure E} [IsGaussian μ] {X : Ω → E}

/-- `HasLaw` version of `lintegral_add_cmCoe_smul_eq`. -/
theorem HasLaw.lintegral_add_cmCoe_smul_eq (hX : HasLaw X μ P) (x : cameronMartin μ) (t : ℝ)
    (F : E → ℝ≥0∞) (hF : Measurable F) : (∫⁻ ω, F (X ω + cmCoe (t • x)) ∂P)  =
      ∫⁻ ω, F (X ω) * ENNReal.ofReal (Real.exp ((t • x) (X ω) - ‖t • x‖ ^ 2 / 2)) ∂P := by
  have h_left : (∫⁻ ω, F (X ω + cmCoe (t • x)) ∂P) = ∫⁻ y, F (y + cmCoe (t • x)) ∂μ := by
    simpa [Function.comp] using
      (ProbabilityTheory.HasLaw.lintegral_comp (X := X) (μ := μ) (P := P) (hX := hX)
        (f := fun y : E => F (y + cmCoe (t • x))) (by fun_prop))
  have h_right :
      (∫⁻ ω, F (X ω) * ENNReal.ofReal (Real.exp ((t • x) (X ω) - ‖t • x‖ ^ 2 / 2)) ∂P) =
        ∫⁻ y, F y * ENNReal.ofReal (Real.exp ((t • x) y - ‖t • x‖ ^ 2 / 2)) ∂μ := by
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (ProbabilityTheory.HasLaw.lintegral_comp (X := X) (μ := μ) (P := P) (hX := hX)
        (f := fun y : E => F y * ENNReal.ofReal (Real.exp ((t • x) y - ‖t • x‖ ^ 2 / 2)))
        (by fun_prop))
  have hμ :=
    ProbabilityTheory.lintegral_add_cmCoe_smul_eq (μ := μ) (x := x) (t := t) (F := F) hF
  calc
    (∫⁻ ω, F (X ω + cmCoe (t • x)) ∂P)
        = ∫⁻ y, F (y + cmCoe (t • x)) ∂μ := h_left
    _ = ∫⁻ y, F y * ENNReal.ofReal (Real.exp ((t • x) y - ‖t • x‖ ^ 2 / 2)) ∂μ := hμ
    _ = ∫⁻ ω, F (X ω) * ENNReal.ofReal (Real.exp ((t • x) (X ω) - ‖t • x‖ ^ 2 / 2)) ∂P := by
          simpa using h_right.symm

/-!
### Law-level corollaries

These package Cameron–Martin as a statement about the law of the translated random variable.
-/

/-- If `X` has law `μ`, then `X + cmCoe (t • x)` has the `withDensity` law from Cameron–Martin. -/
theorem HasLaw.hasLaw_add_cmCoe_smul_withDensity_raw (hX : HasLaw X μ P) (x : cameronMartin μ) (t : ℝ) :
    HasLaw (fun ω : Ω ↦ X ω + cmCoe (t • x))
      (μ.withDensity (fun y ↦ ENNReal.ofReal (Real.exp ((t • x) y - ‖t • x‖ ^ 2 / 2)))) P := by
  set g : E → E := fun y ↦ y + cmCoe (t • x)
  have hg : Measurable g := by
    fun_prop
  have h_pres : MeasureTheory.MeasurePreserving g μ (μ.map g) := ⟨hg, rfl⟩
  have hY : HasLaw g (μ.map g) μ := h_pres.hasLaw
  have h_comp : HasLaw (g ∘ X) (μ.map g) P := hY.comp hX
  have hμ' :
      μ.map g =
        μ.withDensity (fun y ↦ ENNReal.ofReal (Real.exp ((t • x) y - ‖t • x‖ ^ 2 / 2))) := by
    simpa [g] using (ProbabilityTheory.map_add_cameronMartin_eq_withDensity_smul_raw (μ := μ) x t)
  have h_comp' :
      HasLaw (fun ω : Ω ↦ X ω + cmCoe (t • x)) (μ.map g) P :=
    h_comp.congr (ae_of_all _ (fun ω => by simp [g, Function.comp]))
  refine ⟨h_comp'.aemeasurable, ?_⟩
  simpa [hμ'] using h_comp'.map_eq

end ProbabilityTheory
