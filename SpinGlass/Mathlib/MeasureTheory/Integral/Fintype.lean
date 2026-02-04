import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable

open scoped BigOperators

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {G : Type*} [NormedAddCommGroup G]

theorem integrable_fintype_sum {ι : Type*} [Fintype ι] (f : ι → α → G)
    (hf : ∀ i, Integrable (f i) μ) :
    Integrable (fun a => ∑ i, f i a) μ := by
  classical
  simpa using
    (integrable_finset_sum (μ := μ) (s := (Finset.univ : Finset ι))
      (f := fun i => f i) (by intro i hi; simpa using hf i))

theorem integral_fintype_sum {ι : Type*} [Fintype ι] (f : ι → α → G)
    (hf : ∀ i, Integrable (f i) μ) :
    (∫ a, (∑ i, f i a) ∂μ) = ∑ i, ∫ a, f i a ∂μ := by
  classical
  simpa using
    (integral_finset_sum (μ := μ) (s := (Finset.univ : Finset ι))
      (f := fun i => f i) (by intro i hi; simpa using hf i))

theorem sum_integral_fintype_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (g : ι → κ → α → G)
    (hg : ∀ i k, Integrable (g i k) μ) :
    (∑ i, ∫ a, (∑ k, g i k a) ∂μ) = ∫ a, (∑ i, ∑ k, g i k a) ∂μ := by
  classical
  have hInt : ∀ i, Integrable (fun a => ∑ k, g i k a) μ :=
    fun i => integrable_fintype_sum (μ := μ) (f := fun k => g i k) (fun k => hg i k)
  simpa using (integral_fintype_sum (μ := μ) (f := fun i => fun a => ∑ k, g i k a) hInt).symm

end MeasureTheory

