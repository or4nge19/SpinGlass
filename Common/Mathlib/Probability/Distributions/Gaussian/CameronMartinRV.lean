import Common.Mathlib.Probability.Distributions.Gaussian.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Measurable

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

namespace HasLaw

private lemma integral_cm_mul_eq (hX : ProbabilityTheory.HasLaw X μ P)
    (x : cameronMartin μ) (F : E → ℝ) (hF_meas : Measurable F) :
    (∫ ω, (x (X ω)) * F (X ω) ∂P) = ∫ y, (x y) * F y ∂μ := by
  have hx : AEStronglyMeasurable (fun y : E => x y) μ := by
    simpa using (MeasureTheory.Lp.aestronglyMeasurable (x : Lp ℝ 2 μ))
  have hFx : AEStronglyMeasurable (fun y : E => (x y) * F y) μ :=
    (hx.mul hF_meas.aestronglyMeasurable)
  simpa [Function.comp] using
    (hX.integral_comp (μ := μ) (P := P) (f := fun y : E => (x y) * F y) hFx)

private lemma integral_fderiv_apply_cmCoe_eq (hX : ProbabilityTheory.HasLaw X μ P)
    (x : cameronMartin μ) (F : E → ℝ) :
    (∫ ω, (fderiv ℝ F (X ω)) (cmCoe x) ∂P) = ∫ y, (fderiv ℝ F y) (cmCoe x) ∂μ := by
  have hmeas : Measurable (fun y : E => (fderiv ℝ F y) (cmCoe x)) :=
    measurable_fderiv_apply_const ℝ F (cmCoe x)
  simpa [Function.comp] using
    (hX.integral_comp (μ := μ) (P := P)
      (f := fun y : E => (fderiv ℝ F y) (cmCoe x)) hmeas.aestronglyMeasurable)

end HasLaw

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

/-!
### Random-variable IBP corollaries

These transport the **measure-level** Cameron–Martin IBP to random variables via `HasLaw`.
-/

theorem HasLaw.cameronMartin_integral_by_parts_polyGrowth
    (hX : HasLaw X μ P) (x : cameronMartin μ) (F : E → ℝ)
    (hF_meas : Measurable F) (hF_c1 : ContDiff ℝ 1 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ y, |F y| ≤ C * (1 + ‖y‖) ^ m)
    (hF'_growth : ∀ y, ‖fderiv ℝ F y‖ ≤ C * (1 + ‖y‖) ^ m) :
    (∫ ω, (x (X ω)) * F (X ω) ∂P) = ∫ ω, (fderiv ℝ F (X ω)) (cmCoe x) ∂P := by
  have hIBP :
      (∫ y, (x y) * F y ∂μ) = ∫ y, (fderiv ℝ F y) (cmCoe x) ∂μ :=
    ProbabilityTheory.cameronMartin_integral_by_parts_polyGrowth (μ := μ)
      x F hF_meas hF_c1 hC hF_growth hF'_growth
  -- chain the measure-level IBP through `HasLaw.integral_comp`
  calc
    (∫ ω, (x (X ω)) * F (X ω) ∂P) = ∫ y, (x y) * F y ∂μ :=
      HasLaw.integral_cm_mul_eq (P := P) (μ := μ) hX x F hF_meas
    _ = ∫ y, (fderiv ℝ F y) (cmCoe x) ∂μ := hIBP
    _ = (∫ ω, (fderiv ℝ F (X ω)) (cmCoe x) ∂P) := by
          simpa using (HasLaw.integral_fderiv_apply_cmCoe_eq (P := P) (μ := μ) hX x F).symm

theorem HasLaw.cameronMartin_integral_by_parts_bounded
    (hX : HasLaw X μ P) (x : cameronMartin μ) (F : E → ℝ)
    (hF_meas : Measurable F) (hF_c1 : ContDiff ℝ 1 F)
    (hF_bdd : ∃ M : ℝ, ∀ y, |F y| ≤ M)
    (hF'_bdd : ∃ M : ℝ, ∀ y, ‖fderiv ℝ F y‖ ≤ M) :
    (∫ ω, (x (X ω)) * F (X ω) ∂P) = ∫ ω, (fderiv ℝ F (X ω)) (cmCoe x) ∂P := by
  have hIBP :
      (∫ y, (x y) * F y ∂μ) = ∫ y, (fderiv ℝ F y) (cmCoe x) ∂μ :=
    ProbabilityTheory.cameronMartin_integral_by_parts_bounded (μ := μ)
      x F hF_meas hF_c1 hF_bdd hF'_bdd
  calc
    (∫ ω, (x (X ω)) * F (X ω) ∂P) = ∫ y, (x y) * F y ∂μ :=
      HasLaw.integral_cm_mul_eq (P := P) (μ := μ) hX x F hF_meas
    _ = ∫ y, (fderiv ℝ F y) (cmCoe x) ∂μ := hIBP
    _ = (∫ ω, (fderiv ℝ F (X ω)) (cmCoe x) ∂P) := by
          simpa using (HasLaw.integral_fderiv_apply_cmCoe_eq (P := P) (μ := μ) hX x F).symm

theorem HasLaw.cameronMartin_integral_by_parts_of_integrable_bound
    (hX : HasLaw X μ P) (x : cameronMartin μ) (F : E → ℝ)
    (hF_meas : Measurable F) (hF_c1 : ContDiff ℝ 1 F)
    {δ : ℝ} (hδ : 0 < δ)
    (hF_int : Integrable F μ)
    (bound : E → ℝ) (hbound_int : Integrable bound μ)
    (hbound :  ∀ᵐ y ∂μ,
        ∀ t ∈ Metric.ball (0 : ℝ) δ, ‖(fderiv ℝ F (y + t • cmCoe x)) (cmCoe x)‖ ≤ bound y)
    (hTiltInt : Integrable
        (fun y : E =>
          |F y| * (δ * (‖x‖₊ ^ 2 : ℝ) + 1) * ((|x y| + 1) * Real.exp (δ * |x y|))) μ) :
    (∫ ω, (x (X ω)) * F (X ω) ∂P) = ∫ ω, (fderiv ℝ F (X ω)) (cmCoe x) ∂P := by
  have hIBP :
      (∫ y, (x y) * F y ∂μ) = ∫ y, (fderiv ℝ F y) (cmCoe x) ∂μ :=
    ProbabilityTheory.cameronMartin_integral_by_parts_of_integrable_bound (μ := μ)
      x F hF_meas hF_c1 hδ hF_int bound hbound_int hbound hTiltInt
  calc
    (∫ ω, (x (X ω)) * F (X ω) ∂P) = ∫ y, (x y) * F y ∂μ :=
      HasLaw.integral_cm_mul_eq (P := P) (μ := μ) hX x F hF_meas
    _ = ∫ y, (fderiv ℝ F y) (cmCoe x) ∂μ := hIBP
    _ = (∫ ω, (fderiv ℝ F (X ω)) (cmCoe x) ∂P) := by
          simpa using (HasLaw.integral_fderiv_apply_cmCoe_eq (P := P) (μ := μ) hX x F).symm

end ProbabilityTheory
