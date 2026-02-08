import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

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
            exact (Measure.map_map hsub_meas hL_meas).symm
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

/-- Chernoff (one-sided) tail bound for a centered Gaussian linear functional. -/
theorem measure_ge_le_centered_dual (L : StrongDual ℝ E) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {x : E | ε ≤ L x - μ[L]} ≤ rexp (-ε ^ 2 / (2 * (Var[L; μ]).toNNReal)) := by
  simpa using (hasSubgaussianMGF_centered_dual (μ := μ) L).measure_ge_le hε

/-- Two-sided tail bound for a centered Gaussian linear functional. -/
theorem measure_ge_le_abs_centered_dual (L : StrongDual ℝ E) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {x : E | ε ≤ |L x - μ[L]|}
      ≤ (2 : ℝ) * rexp (-ε ^ 2 / (2 * (Var[L; μ]).toNNReal)) := by
  let X : E → ℝ := fun x => L x - μ[L]
  have hX : ProbabilityTheory.HasSubgaussianMGF X (Var[L; μ]).toNNReal μ := by
    simpa [X] using hasSubgaussianMGF_centered_dual (μ := μ) L
  have hpos : μ.real {x : E | ε ≤ X x} ≤ rexp (-ε ^ 2 / (2 * (Var[L; μ]).toNNReal)) := by
    simpa [X] using hX.measure_ge_le hε
  have hneg : μ.real {x : E | ε ≤ -X x} ≤ rexp (-ε ^ 2 / (2 * (Var[L; μ]).toNNReal)) := by
    simpa [X] using (hX.neg.measure_ge_le hε)
  have hset :
      {x : E | ε ≤ |X x|} = {x : E | ε ≤ X x} ∪ {x : E | ε ≤ -X x} := by
    ext x
    simp [le_abs]
  calc
    μ.real {x : E | ε ≤ |L x - μ[L]|}
        = μ.real {x : E | ε ≤ |X x|} := by simp [X]
    _ = μ.real ({x : E | ε ≤ X x} ∪ {x : E | ε ≤ -X x}) := by simp [hset]
    _ ≤ μ.real {x : E | ε ≤ X x} + μ.real {x : E | ε ≤ -X x} := by
          simpa using (MeasureTheory.measureReal_union_le (μ := μ)
            ({x : E | ε ≤ X x}) ({x : E | ε ≤ -X x}))
    _ ≤ rexp (-ε ^ 2 / (2 * (Var[L; μ]).toNNReal))
          + rexp (-ε ^ 2 / (2 * (Var[L; μ]).toNNReal)) := by
          gcongr
    _ = (2 : ℝ) * rexp (-ε ^ 2 / (2 * (Var[L; μ]).toNNReal)) := by
          simpa using (two_mul (rexp (-ε ^ 2 / (2 * (Var[L; μ]).toNNReal)))).symm

end IsGaussian

namespace HasGaussianLaw

variable {Ω E : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {X : Ω → E}

/-- A Gaussian random variable has sub-Gaussian mgf after applying a linear functional and centering. -/
theorem hasSubgaussianMGF_centered_dual (hX : ProbabilityTheory.HasGaussianLaw X P) (L : StrongDual ℝ E) :
    ProbabilityTheory.HasSubgaussianMGF
        (fun ω : Ω => L (X ω) - P[fun ω : Ω => L (X ω)])
        (Var[fun ω : Ω => L (X ω); P]).toNNReal P := by
  let μ : Measure E := P.map X
  haveI : ProbabilityTheory.IsGaussian μ := ProbabilityTheory.HasGaussianLaw.isGaussian_map hX
  have hμ :
      ProbabilityTheory.HasSubgaussianMGF (fun x : E => L x - μ[L]) (Var[L; μ]).toNNReal μ :=
    ProbabilityTheory.IsGaussian.hasSubgaussianMGF_centered_dual (μ := μ) L
  have hPull :
      ProbabilityTheory.HasSubgaussianMGF (fun ω : Ω => (fun x : E => L x - μ[L]) (X ω))
          (Var[L; μ]).toNNReal P :=
    ProbabilityTheory.HasSubgaussianMGF.of_map (ProbabilityTheory.HasGaussianLaw.aemeasurable hX) hμ
  have hmean : μ[L] = P[fun ω : Ω => L (X ω)] := by
    simpa [μ] using
      (MeasureTheory.integral_map (μ := P) (φ := X) (f := L)
        (ProbabilityTheory.HasGaussianLaw.aemeasurable hX) (by fun_prop))
  have hVar : Var[L; μ] = Var[fun ω : Ω => L (X ω); P] := by
    simpa [μ, Function.comp] using
      (ProbabilityTheory.variance_map (μ := P) (Y := X) (X := L) (hX := by fun_prop)
        (ProbabilityTheory.HasGaussianLaw.aemeasurable hX))
  have hPull' :
      ProbabilityTheory.HasSubgaussianMGF
          (fun ω : Ω => L (X ω) - P[fun ω : Ω => L (X ω)]) (Var[L; μ]).toNNReal P := by
    refine hPull.congr ?_
    filter_upwards [] with ω
    simp [hmean, μ]
  simpa [hVar] using hPull'

/-- Chernoff (one-sided) tail bound for a centered Gaussian linear functional of a Gaussian RV. -/
theorem measure_ge_le_centered_dual (hX : ProbabilityTheory.HasGaussianLaw X P) (L : StrongDual ℝ E)
    {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω : Ω | ε ≤ L (X ω) - P[fun ω : Ω => L (X ω)]}
      ≤ rexp (-ε ^ 2 / (2 * (Var[fun ω : Ω => L (X ω); P]).toNNReal)) := by
  simpa using (hasSubgaussianMGF_centered_dual (X := X) (P := P) hX L).measure_ge_le hε

/-- Two-sided tail bound for a centered Gaussian linear functional of a Gaussian RV. -/
theorem measure_ge_le_abs_centered_dual (hX : ProbabilityTheory.HasGaussianLaw X P) (L : StrongDual ℝ E)
    {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω : Ω | ε ≤ |L (X ω) - P[fun ω : Ω => L (X ω)]|}
      ≤ (2 : ℝ) * rexp (-ε ^ 2 / (2 * (Var[fun ω : Ω => L (X ω); P]).toNNReal)) := by
  let Y : Ω → ℝ := fun ω : Ω => L (X ω) - P[fun ω : Ω => L (X ω)]
  have hY : ProbabilityTheory.HasSubgaussianMGF Y (Var[fun ω : Ω => L (X ω); P]).toNNReal P :=
    hasSubgaussianMGF_centered_dual (X := X) (P := P) hX L
  have hpos : P.real {ω : Ω | ε ≤ Y ω}
      ≤ rexp (-ε ^ 2 / (2 * (Var[fun ω : Ω => L (X ω); P]).toNNReal)) := by
    simpa [Y] using hY.measure_ge_le hε
  have hneg : P.real {ω : Ω | ε ≤ -Y ω}
      ≤ rexp (-ε ^ 2 / (2 * (Var[fun ω : Ω => L (X ω); P]).toNNReal)) := by
    simpa [Y] using (hY.neg.measure_ge_le hε)
  have hset : {ω : Ω | ε ≤ |Y ω|} = {ω : Ω | ε ≤ Y ω} ∪ {ω : Ω | ε ≤ -Y ω} := by
    ext ω
    simp [le_abs]
  calc
    P.real {ω : Ω | ε ≤ |L (X ω) - P[fun ω : Ω => L (X ω)]|}
        = P.real {ω : Ω | ε ≤ |Y ω|} := by simp [Y]
    _ = P.real ({ω : Ω | ε ≤ Y ω} ∪ {ω : Ω | ε ≤ -Y ω}) := by simp [hset]
    _ ≤ P.real {ω : Ω | ε ≤ Y ω} + P.real {ω : Ω | ε ≤ -Y ω} := by
          simpa using
            (MeasureTheory.measureReal_union_le (μ := P) ({ω : Ω | ε ≤ Y ω}) ({ω : Ω | ε ≤ -Y ω}))
    _ ≤ rexp (-ε ^ 2 / (2 * (Var[fun ω : Ω => L (X ω); P]).toNNReal))
          + rexp (-ε ^ 2 / (2 * (Var[fun ω : Ω => L (X ω); P]).toNNReal)) := by
          gcongr
    _ = (2 : ℝ) * rexp (-ε ^ 2 / (2 * (Var[fun ω : Ω => L (X ω); P]).toNNReal)) := by
          simpa using
            (two_mul (rexp (-ε ^ 2 / (2 * (Var[fun ω : Ω => L (X ω); P]).toNNReal)))).symm

end HasGaussianLaw

end ProbabilityTheory
