import SpinGlass.Mathlib.Probability.Distributions.Gaussian.CameronMartinTilt

/-!
# Fernique consequences for Cameron–Martin usage

This file provides small, reusable lemmas that let us *use* Fernique's theorem in downstream
arguments (dominated convergence/differentiation under Gaussian measures) without redoing the
measure-theoretic work each time.

The key point: for a Gaussian measure `μ` on a second-countable Banach space, Fernique gives
integrability of `x ↦ exp (C * ‖x‖^2)` for some `C>0`. From this, we can derive exponential-square
integrability for any continuous linear functional.

This file is **additive** and does not change existing Cameron–Martin theorems.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Real Topology

namespace ProbabilityTheory

namespace IsGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E]
  {μ : Measure E} [ProbabilityTheory.IsGaussian μ]

/-- Fernique theorem, re-exposed in a convenient form (using `rexp`). -/
theorem exists_C_pos_integrable_rexp_norm_sq :
    ∃ C : ℝ, 0 < C ∧ Integrable (fun x : E ↦ rexp (C * ‖x‖ ^ 2)) μ := by
  simpa using (ProbabilityTheory.IsGaussian.exists_integrable_exp_sq (μ := μ))

/-- Any continuous linear functional is in `L^p` (all finite `p`) under a Gaussian measure. -/
theorem memLp_strongDual (L : StrongDual ℝ E) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp L p μ := by
  -- `id` is in `L^p` by Fernique, hence so is any continuous linear map composed with `id`.
  simpa using (L.comp_memLp' (ProbabilityTheory.IsGaussian.memLp_id (μ := μ) p hp))

/-- As a consequence, `|L x|^n` is integrable for all `n`. -/
theorem integrable_abs_pow_strongDual (L : StrongDual ℝ E) (n : ℕ) :
    Integrable (fun x : E ↦ |L x| ^ n) μ := by
  -- Use `L^p` with `p = max 1 n`, then lower the exponent to `n` and use `integrable_norm_pow'`.
  let q : ℕ := max 1 n
  have hLp : MemLp L q μ :=
    memLp_strongDual (μ := μ) L q (by simp)
  have hn_le : (n : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by
    exact_mod_cast (Nat.le_max_right 1 n)
  have hLp' : MemLp L n μ := hLp.mono_exponent hn_le
  have : IsFiniteMeasure μ := by infer_instance
  have hIntPow : Integrable (fun x : E ↦ ‖L x‖ ^ n) μ :=
    MeasureTheory.MemLp.integrable_norm_pow' (μ := μ) (f := fun x : E ↦ L x) hLp'
  simpa [Real.norm_eq_abs] using hIntPow

/-- A Fernique corollary: every continuous linear functional has some exponential-square moment. -/
theorem exists_C_pos_integrable_rexp_sq_dual (L : StrongDual ℝ E) :
    ∃ C : ℝ, 0 < C ∧ Integrable (fun x : E ↦ rexp (C * (L x) ^ 2)) μ := by
  obtain ⟨A, hApos, hA⟩ := exists_C_pos_integrable_rexp_norm_sq (μ := μ) (E := E)
  let C : ℝ := A / (‖L‖ ^ 2 + 1)
  have hCpos : 0 < C := by
    have hden : 0 < ‖L‖ ^ 2 + 1 := by nlinarith [sq_nonneg ‖L‖]
    exact div_pos hApos hden
  refine ⟨C, hCpos, ?_⟩
  refine (MeasureTheory.Integrable.mono (μ := μ) (g := fun x : E ↦ rexp (A * ‖x‖ ^ 2)) hA
    (hf := by fun_prop) ?_)
  refine ae_of_all _ (fun x ↦ ?_)
  have hLx : |L x| ≤ ‖L‖ * ‖x‖ := by
    simpa [Real.norm_eq_abs] using (L.le_opNorm x)
  have hsq : (L x) ^ 2 ≤ (‖L‖ ^ 2) * (‖x‖ ^ 2) := by
    have hmul :
        |L x| * |L x| ≤ (‖L‖ * ‖x‖) * (‖L‖ * ‖x‖) := by
      exact mul_le_mul hLx hLx (by positivity) (by positivity)
    have hpow : |L x| ^ 2 ≤ (‖L‖ * ‖x‖) ^ 2 := by
      simpa [pow_two] using hmul
    simpa [sq_abs, pow_two, mul_assoc, mul_left_comm, mul_comm] using hpow
  have hCA : C * ‖L‖ ^ 2 ≤ A := by
    have hden : 0 < ‖L‖ ^ 2 + 1 := by nlinarith [sq_nonneg ‖L‖]
    have hfrac : ‖L‖ ^ 2 / (‖L‖ ^ 2 + 1) ≤ (1 : ℝ) := by
      have : ‖L‖ ^ 2 ≤ ‖L‖ ^ 2 + 1 := by linarith [sq_nonneg ‖L‖]
      exact (div_le_one hden).2 this
    calc
      C * ‖L‖ ^ 2 = A * (‖L‖ ^ 2 / (‖L‖ ^ 2 + 1)) := by
        simp [C, div_eq_mul_inv, mul_left_comm, mul_comm]
      _ ≤ A * 1 := by gcongr
      _ = A := by simp
  have hexp : C * (L x) ^ 2 ≤ A * ‖x‖ ^ 2 := by
    calc
      C * (L x) ^ 2 ≤ C * ((‖L‖ ^ 2) * (‖x‖ ^ 2)) := by gcongr
      _ = (C * ‖L‖ ^ 2) * ‖x‖ ^ 2 := by ring
      _ ≤ (A) * ‖x‖ ^ 2 := by gcongr
  have h_exp_le : rexp (C * (L x) ^ 2) ≤ rexp (A * ‖x‖ ^ 2) := by
    simpa using Real.exp_le_exp.mpr hexp
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), abs_of_nonneg (Real.exp_nonneg _)]
    using h_exp_le

end IsGaussian

end ProbabilityTheory
