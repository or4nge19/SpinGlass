import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Gaussian.Basic

/-!
# Gaussian measures are sub-Gaussian (linear functionals)

This file provides a bridge between Mathlib's `IsGaussian` predicate and the
sub-Gaussian mgf API (`ProbabilityTheory.HasSubgaussianMGF`).

The main statement is: for a Gaussian measure `μ` on a real Banach space `E`, any continuous linear
functional `L : StrongDual ℝ E` is *sub-Gaussian after centering*:
`x ↦ L x - μ[L]` has sub-Gaussian mgf with parameter `(Var[L; μ]).toNNReal`.

This is an equality-level statement, proved by pushing forward to `ℝ` and using the explicit mgf of
`gaussianReal`.
-/

open MeasureTheory ProbabilityTheory
open scoped Real NNReal

namespace ProbabilityTheory

namespace IsGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

variable {μ : Measure E} [ProbabilityTheory.IsGaussian μ]

/-- A continuous linear functional of a Gaussian measure is sub-Gaussian after centering. -/
theorem hasSubgaussianMGF_centered_dual (L : StrongDual ℝ E) :
    ProbabilityTheory.HasSubgaussianMGF (fun x : E => L x - μ[L]) (Var[L; μ]).toNNReal μ := by
  let m : ℝ := μ[L]
  let v : ℝ≥0 := (Var[L; μ]).toNNReal
  have hmapL : μ.map L = ProbabilityTheory.gaussianReal (μ[L]) (Var[L; μ]).toNNReal :=
    ProbabilityTheory.IsGaussian.map_eq_gaussianReal (μ := μ) L
  have hmap :
      μ.map (fun x : E => L x - m) = ProbabilityTheory.gaussianReal 0 v := by
    have hcomp : (fun x : E => L x - m) = (fun y : ℝ => y - m) ∘ L := rfl
    have hL_meas : Measurable L := by
      simpa using (L.continuous.measurable : Measurable (fun x : E => L x))
    have hsub_meas : Measurable (fun y : ℝ => y - m) := by fun_prop
    calc
      μ.map (fun x : E => L x - m)
          = μ.map ((fun y : ℝ => y - m) ∘ L) := by simp [hcomp]
      _ = (μ.map L).map (fun y : ℝ => y - m) := by
            simpa using (Measure.map_map hsub_meas hL_meas).symm
      _ = (ProbabilityTheory.gaussianReal m v).map (fun y : ℝ => y - m) := by
            simpa [m, v] using congrArg (fun ν => ν.map (fun y : ℝ => y - m)) hmapL
      _ = ProbabilityTheory.gaussianReal 0 v := by
            simpa [sub_self, m] using
              (ProbabilityTheory.gaussianReal_map_sub_const (μ := m) (v := v) m)
  refine ⟨?_, ?_⟩
  · intro t
    have hint : Integrable (fun y : ℝ => rexp (t * y)) (ProbabilityTheory.gaussianReal 0 v) :=
      ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := (0 : ℝ)) (v := v) t
    have hint' : Integrable (fun y : ℝ => rexp (t * y)) (μ.map (fun x : E => L x - m)) := by
      simpa [hmap] using hint
    simpa [m, Function.comp] using
      (hint'.comp_measurable (by fun_prop : Measurable (fun x : E => L x - m)))
  · intro t
    have hmgf :
        ProbabilityTheory.mgf (fun x : E => L x - m) μ t
          = rexp (0 * t + v * t ^ 2 / 2) := by
      simpa [hmap] using
        (ProbabilityTheory.mgf_gaussianReal (p := μ) (X := fun x : E => L x - m)
          (μ := (0 : ℝ)) (v := v) (hX := hmap) t)
    have hmgf' :
        ProbabilityTheory.mgf (fun x : E => L x - m) μ t = rexp (v * t ^ 2 / 2) := by
      simpa [zero_mul, zero_add, add_assoc] using hmgf
    simp [m, v, hmgf']

end IsGaussian

end ProbabilityTheory
