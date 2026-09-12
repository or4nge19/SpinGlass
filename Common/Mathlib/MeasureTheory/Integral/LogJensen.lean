/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Jensen's inequality for the logarithm

`∫ log f ≤ log ∫ f` on a probability space, for a positive integrable `f` with integrable
logarithm (`integral_log_le_log_integral`). Mathlib's `ConcaveOn.le_map_integral` needs the
function to be continuous on a *closed* set containing the values, which excludes `log` on
`(0, ∞)`; the tangent-line bound `log y ≤ y - 1` at `y = f / ∫ f` gives it directly.
-/

open MeasureTheory

/-- **Jensen's inequality for `log`** on a probability space: `∫ log f ≤ log ∫ f` for a
positive integrable `f` with integrable logarithm. -/
theorem integral_log_le_log_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : ∀ᵐ ω ∂μ, 0 < f ω) (hfi : Integrable f μ)
    (hli : Integrable (fun ω => Real.log (f ω)) μ) :
    ∫ ω, Real.log (f ω) ∂μ ≤ Real.log (∫ ω, f ω ∂μ) := by
  set c := ∫ ω, f ω ∂μ with hc
  have hcpos : 0 < c := by
    rw [hc, integral_pos_iff_support_of_nonneg_ae (hf.mono fun ω h => h.le) hfi]
    have h1 : Function.support f =ᵐ[μ] (Set.univ : Set Ω) := by
      rw [Filter.eventuallyEq_set]
      filter_upwards [hf] with ω h
      simp [Function.mem_support, h.ne']
    rw [measure_congr h1, measure_univ]
    exact one_pos
  have hpt : ∀ᵐ ω ∂μ, Real.log (f ω) ≤ Real.log c + (f ω / c - 1) := by
    filter_upwards [hf] with ω h
    have := Real.log_le_sub_one_of_pos (div_pos h hcpos)
    rw [Real.log_div h.ne' hcpos.ne'] at this
    linarith
  have hg : Integrable (fun ω => f ω / c - 1) μ := (hfi.div_const c).sub (integrable_const _)
  have hi2 : Integrable (fun ω => Real.log c + (f ω / c - 1)) μ := (integrable_const _).add hg
  calc ∫ ω, Real.log (f ω) ∂μ ≤ ∫ ω, (Real.log c + (f ω / c - 1)) ∂μ :=
        integral_mono_ae hli hi2 hpt
    _ = Real.log c := by
        rw [integral_add (integrable_const _) hg, integral_const,
          integral_sub (hfi.div_const c) (integrable_const _), integral_div, integral_const, ← hc]
        simp [hcpos.ne']
