/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Products of sums in `ℝ≥0∞`, and integrals against sums of Dirac measures

In `ℝ≥0∞` every family is summable, so the product of two sums expands unconditionally into a
double sum (`ENNReal.tsum_mul_tsum`), and in particular the diagonal is dominated by the product
of the sums (`ENNReal.tsum_mul_le_mul_tsum`, `ENNReal.sum_mul_le_mul_sum`):

`∑ᵢ aᵢ bᵢ ≤ (∑ᵢ aᵢ) (∑ⱼ bⱼ)`.

Measure-theoretically this says that for a measure `N` which is a (countable) sum of Dirac
measures — a *counting measure* — the product of two integrals dominates the integral of the
product,

`∫⁻ f g dN ≤ (∫⁻ f dN) (∫⁻ g dN)`

(`MeasureTheory.lintegral_mul_le_mul_lintegral_finsetSum_dirac`,
`MeasureTheory.lintegral_mul_le_mul_lintegral_sum`); equivalently `‖·‖₂ ≤ ‖·‖₁` for counting
measures. This fails for general measures: for `N = c • δ_x` it is exactly `c ≤ c²`.
-/

open MeasureTheory
open scoped ENNReal

namespace ENNReal

variable {ι κ : Type*}

/-- **The product of two sums in `ℝ≥0∞`** is the double sum, unconditionally. -/
protected theorem tsum_mul_tsum (f : ι → ℝ≥0∞) (g : κ → ℝ≥0∞) :
    ((∑' i, f i) * ∑' j, g j) = ∑' i, ∑' j, f i * g j := by
  rw [← ENNReal.tsum_mul_right]
  exact tsum_congr fun i => ENNReal.tsum_mul_left.symm

/-- **The diagonal of a product of sums**: `∑ᵢ aᵢ bᵢ ≤ (∑ᵢ aᵢ)(∑ⱼ bⱼ)` in `ℝ≥0∞`. -/
protected theorem tsum_mul_le_mul_tsum (f g : ι → ℝ≥0∞) :
    ∑' i, f i * g i ≤ (∑' i, f i) * ∑' j, g j := by
  rw [ENNReal.tsum_mul_tsum]
  exact ENNReal.tsum_le_tsum fun i => ENNReal.le_tsum (f := fun j => f i * g j) i

/-- `∑' i, (f i)² ≤ (∑' i, f i)²` in `ℝ≥0∞`. -/
protected theorem tsum_sq_le_sq_tsum (f : ι → ℝ≥0∞) : ∑' i, f i ^ 2 ≤ (∑' i, f i) ^ 2 := by
  simp_rw [sq]
  exact ENNReal.tsum_mul_le_mul_tsum f f

/-- **The diagonal of a product of finite sums** in `ℝ≥0∞`. -/
protected theorem sum_mul_le_mul_sum (s : Finset ι) (f g : ι → ℝ≥0∞) :
    ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, f i) * ∑ j ∈ s, g j := by
  rw [Finset.sum_mul_sum]
  exact Finset.sum_le_sum fun i hi =>
    Finset.single_le_sum (f := fun j => f i * g j) (fun _ _ => bot_le) hi

end ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {ι : Type*} {f g : α → ℝ≥0∞}

/-- **For a finite counting measure the product of the integrals dominates the integral of the
product.** -/
theorem lintegral_mul_le_mul_lintegral_finsetSum_dirac (s : Finset ι) (x : ι → α)
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ y, f y * g y ∂∑ i ∈ s, Measure.dirac (x i))
      ≤ (∫⁻ y, f y ∂∑ i ∈ s, Measure.dirac (x i)) * ∫⁻ y, g y ∂∑ i ∈ s, Measure.dirac (x i) := by
  have hfg : Measurable fun y => f y * g y := hf.mul hg
  rw [lintegral_finsetSum_measure, lintegral_finsetSum_measure, lintegral_finsetSum_measure]
  simp_rw [lintegral_dirac' _ hf, lintegral_dirac' _ hg, lintegral_dirac' _ hfg]
  exact ENNReal.sum_mul_le_mul_sum s _ _

/-- **The bound passes to countable sums of measures.** -/
theorem lintegral_mul_le_mul_lintegral_sum (μ : ι → Measure α)
    (h : ∀ i, (∫⁻ y, f y * g y ∂μ i) ≤ (∫⁻ y, f y ∂μ i) * ∫⁻ y, g y ∂μ i) :
    (∫⁻ y, f y * g y ∂Measure.sum μ)
      ≤ (∫⁻ y, f y ∂Measure.sum μ) * ∫⁻ y, g y ∂Measure.sum μ := by
  rw [lintegral_sum_measure, lintegral_sum_measure, lintegral_sum_measure]
  exact (ENNReal.tsum_le_tsum h).trans (ENNReal.tsum_mul_le_mul_tsum _ _)

/-- **For a counting measure the product of the integrals dominates the integral of the
product**: `∫⁻ f g dN ≤ (∫⁻ f dN) (∫⁻ g dN)` when `N = ∑ᵢ δ_{xᵢ}`. -/
theorem lintegral_mul_le_mul_lintegral_sum_dirac (x : ι → α) (hf : Measurable f)
    (hg : Measurable g) :
    (∫⁻ y, f y * g y ∂Measure.sum fun i => Measure.dirac (x i))
      ≤ (∫⁻ y, f y ∂Measure.sum fun i => Measure.dirac (x i))
        * ∫⁻ y, g y ∂Measure.sum fun i => Measure.dirac (x i) := by
  have hfg : Measurable fun y => f y * g y := hf.mul hg
  refine lintegral_mul_le_mul_lintegral_sum _ fun i => ?_
  rw [lintegral_dirac' _ hf, lintegral_dirac' _ hg, lintegral_dirac' _ hfg]

end MeasureTheory
