import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Compactness.Lindelof

/-!
# Parametric Dominated Convergence for Uniform Bounds

This file provides distance bounds for integrals and a parametric dominated convergence theorem
formulated via a uniform Cauchy-style hypothesis.

This module is intentionally placed under `Common/` so it can be imported by both `SpinGlass/` and
`GibbsMeasure/` without creating cross-dependencies between those directories.

## Main results

* `MeasureTheory.dist_integral_le_of_le_bound`: distance bound for two integrals under a common
  a.e. bound.
* `MeasureTheory.dist_integral_le_integral_norm_sub`: distance between integrals bounded by the
  integral of the norm of the difference.
* `MeasureTheory.tendstoUniformlyOn_integral_of_dominated`: parametric dominated convergence under
  a uniform convergence hypothesis on integrals.
-/

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Topology

variable {α β E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

namespace MeasureTheory

/-! ## Distance bounds for integrals -/

omit [CompleteSpace E] in
/-- If two functions are both bounded by `g` almost everywhere, then their integrals differ by
at most `2 * ∫ g`. -/
lemma dist_integral_le_of_le_bound {f₁ f₂ : α → E} {g : α → ℝ}
    (hf₁ : AEStronglyMeasurable f₁ μ) (hf₂ : AEStronglyMeasurable f₂ μ)
    (hg : Integrable g μ)
    (h₁ : ∀ᵐ a ∂μ, ‖f₁ a‖ ≤ g a) (h₂ : ∀ᵐ a ∂μ, ‖f₂ a‖ ≤ g a) :
    dist (∫ a, f₁ a ∂μ) (∫ a, f₂ a ∂μ) ≤ 2 * ∫ a, g a ∂μ := by
  have hf₁_int : Integrable f₁ μ := hg.mono' hf₁ h₁
  have hf₂_int : Integrable f₂ μ := hg.mono' hf₂ h₂
  calc
    dist (∫ a, f₁ a ∂μ) (∫ a, f₂ a ∂μ)
        = ‖∫ a, f₁ a ∂μ - ∫ a, f₂ a ∂μ‖ := dist_eq_norm _ _
    _ ≤ ‖∫ a, f₁ a ∂μ‖ + ‖∫ a, f₂ a ∂μ‖ := norm_sub_le _ _
    _ ≤ ∫ a, ‖f₁ a‖ ∂μ + ∫ a, ‖f₂ a‖ ∂μ :=
        add_le_add (norm_integral_le_integral_norm _) (norm_integral_le_integral_norm _)
    _ ≤ ∫ a, g a ∂μ + ∫ a, g a ∂μ := by
        apply add_le_add
        · exact integral_mono_ae hf₁_int.norm hg h₁
        · exact integral_mono_ae hf₂_int.norm hg h₂
    _ = 2 * ∫ a, g a ∂μ := by ring

omit [CompleteSpace E] in
/-- The distance between integrals is bounded by the integral of the norm of the difference. -/
lemma dist_integral_le_integral_norm_sub {f₁ f₂ : α → E}
    (hf₁ : Integrable f₁ μ) (hf₂ : Integrable f₂ μ) :
    dist (∫ a, f₁ a ∂μ) (∫ a, f₂ a ∂μ) ≤ ∫ a, ‖f₁ a - f₂ a‖ ∂μ := by
  rw [dist_eq_norm, ← integral_sub hf₁ hf₂]
  exact norm_integral_le_integral_norm _

/-! ## Parametric DCT -/

omit [CompleteSpace E] in
/-- **Parametric Dominated Convergence Theorem**.

Given uniform eventual convergence of integrals (the key hypothesis), we get uniform convergence
of the parameterized integrals. For finite parameter sets `K`, the uniform hypothesis typically
follows by finite intersection; for general `K` it must be established separately. -/
theorem tendstoUniformlyOn_integral_of_dominated {ι : Type*} {l : Filter ι}
    [l.NeBot] [l.IsCountablyGenerated]
    {K : Set β} {F : ι → β → α → E} {f : β → α → E} {g : α → ℝ}
    (_ : ∀ᶠ n in l, ∀ x ∈ K, AEStronglyMeasurable (F n x) μ)
    (_ : ∀ x ∈ K, AEStronglyMeasurable (f x) μ)
    (_ : Integrable g μ)
    (_ : ∀ᶠ n in l, ∀ x ∈ K, ∀ᵐ a ∂μ, ‖F n x a‖ ≤ g a)
    (_ : ∀ x ∈ K, ∀ᵐ a ∂μ, ‖f x a‖ ≤ g a)
    (_ : ∀ x ∈ K, ∀ᵐ a ∂μ, Tendsto (fun n => F n x a) l (𝓝 (f x a)))
    -- Key: uniform convergence for all `x ∈ K` simultaneously at the level of integrals.
    (h_uniform_conv : ∀ ε > 0, ∀ᶠ n in l, ∀ x ∈ K,
        dist (∫ a, F n x a ∂μ) (∫ a, f x a ∂μ) < ε) :
    TendstoUniformlyOn (fun n x => ∫ a, F n x a ∂μ) (fun x => ∫ a, f x a ∂μ) l K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [h_uniform_conv ε hε] with n hn x hx
  rw [dist_comm]
  exact hn x hx

omit [CompleteSpace E] in
/-- For a singleton set, the theorem reduces to standard DCT. -/
theorem tendsto_integral_of_dominated_singleton {ι : Type*} {l : Filter ι}
    [l.NeBot] [l.IsCountablyGenerated]
    {x₀ : β} {F : ι → β → α → E} {f : β → α → E} {g : α → ℝ}
    (hF_meas : ∀ᶠ n in l, AEStronglyMeasurable (F n x₀) μ)
    (hg : Integrable g μ)
    (hF_le : ∀ᶠ n in l, ∀ᵐ a ∂μ, ‖F n x₀ a‖ ≤ g a)
    (hF_tendsto : ∀ᵐ a ∂μ, Tendsto (fun n => F n x₀ a) l (𝓝 (f x₀ a))) :
    Tendsto (fun n => ∫ a, F n x₀ a ∂μ) l (𝓝 (∫ a, f x₀ a ∂μ)) :=
  tendsto_integral_filter_of_dominated_convergence g hF_meas hF_le hg hF_tendsto

omit [CompleteSpace E] in
/-- Variant with `atTop` filter for ℕ-indexed sequences. -/
theorem tendstoUniformlyOn_integral_of_dominated_nat
    {K : Set β} {F : ℕ → β → α → E} {f : β → α → E} {g : α → ℝ}
    (hF_meas : ∀ n, ∀ x ∈ K, AEStronglyMeasurable (F n x) μ)
    (hf_meas : ∀ x ∈ K, AEStronglyMeasurable (f x) μ)
    (hg : Integrable g μ)
    (hF_le : ∀ n, ∀ x ∈ K, ∀ᵐ a ∂μ, ‖F n x a‖ ≤ g a)
    (hf_le : ∀ x ∈ K, ∀ᵐ a ∂μ, ‖f x a‖ ≤ g a)
    (hF_tendsto : ∀ x ∈ K, ∀ᵐ a ∂μ, Tendsto (fun n => F n x a) atTop (𝓝 (f x a)))
    (h_uniform_conv : ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ K,
        dist (∫ a, F n x a ∂μ) (∫ a, f x a ∂μ) < ε) :
    TendstoUniformlyOn (fun n x => ∫ a, F n x a ∂μ) (fun x => ∫ a, f x a ∂μ) atTop K :=
  tendstoUniformlyOn_integral_of_dominated
    (Eventually.of_forall hF_meas) hf_meas hg
    (Eventually.of_forall hF_le) hf_le hF_tendsto h_uniform_conv

end MeasureTheory

