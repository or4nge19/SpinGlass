/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.FiniteGibbs.ParameterDerivative
import SpinGlass.FiniteGibbs.Kernel
import SpinGlass.FiniteGibbs.Integrability
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The integrated energy fluctuation

Talagrand, Vol. II, §12.1, equation (12.9): for a Hamiltonian `H + x H'` depending affinely on a
parameter `x`, the **total Gibbs fluctuation of `H'`, integrated over the parameter**, equals the
increment of the derivative of the mean free energy:

`∫_a^b 𝔼⟨(H' - ⟨H'⟩)²⟩ dx = n (p'(b) - p'(a))`.

The mechanism is convexity: `n Φ''(x) = ⟨(H' - ⟨H'⟩)²⟩` pointwise
(`hessian_free_energy_self_eq_variance`), so the fluctuation is a second derivative and its
integral telescopes. The consequence Talagrand draws is that the fluctuation must be *small for
most `x`* whenever `p'` is bounded independently of the volume — this is the self-averaging of the
energy, and, through `ghirlandaGuerra_error_le`, the mechanism by which the Ghirlanda–Guerra
identities become exact in the limit.

Nothing here is Gaussian, and nothing is asymptotic: the identity holds for an arbitrary pair of
integrable random Hamiltonians at every finite volume.

## Main statements

- `SpinGlass.FiniteGibbs.hasDerivAt_integral_free_energy_density` — `p'(x) = -𝔼⟨H'⟩/n`
  (differentiation under the integral; Talagrand Vol. II, (12.6)–(12.7)).
- `SpinGlass.FiniteGibbs.hasDerivAt_integral_gibbs_average` — `p''(x) = 𝔼⟨(H' - ⟨H'⟩)²⟩/n`
  (Talagrand Vol. II, (12.8)).
- `SpinGlass.FiniteGibbs.integral_fluctuation_eq_sub` — **equation (12.9)**.
-/

open MeasureTheory Real BigOperators Filter Topology
open scoped ContDiff

namespace SpinGlass

namespace FiniteGibbs

noncomputable section

variable {α : Type*} [Fintype α] [Nonempty α]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {U V : Ω → EnergySpace α}

/-! ### Measurability and integrability along the path -/

lemma measurable_gibbs_average_path (hU : Measurable U) (hV : Measurable V) (x : ℝ) :
    Measurable fun w => gibbs_average (α := α) (U w + x • V w) (V w) := by
  classical
  have hpath : Measurable fun w => U w + x • V w := by fun_prop
  have hpmf : ∀ σ : α, Measurable fun w => gibbs_pmf (α := α) (U w + x • V w) σ := fun σ =>
    ((contDiff_gibbs_pmf (α := α) σ).continuous.measurable).comp hpath
  have hev : ∀ σ : α, Measurable fun w => (V w) σ := fun σ =>
    (measurable_eval (α := α) σ).comp hV
  simpa [gibbs_average] using
    Finset.measurable_sum (s := (Finset.univ : Finset α))
      (fun σ _ => (hpmf σ).mul (hev σ))

lemma measurable_hessian_path (n : ℕ) (hU : Measurable U) (hV : Measurable V) (x : ℝ) :
    Measurable fun w =>
      hessian_free_energy (α := α) n (U w + x • V w) (V w) (V w) := by
  classical
  have hpath : Measurable fun w => U w + x • V w := by fun_prop
  have hpmf : ∀ σ : α, Measurable fun w => gibbs_pmf (α := α) (U w + x • V w) σ := fun σ =>
    ((contDiff_gibbs_pmf (α := α) σ).continuous.measurable).comp hpath
  have hev : ∀ σ : α, Measurable fun w => (V w) σ := fun σ =>
    (measurable_eval (α := α) σ).comp hV
  have h1 : Measurable fun w =>
      ∑ σ : α, gibbs_pmf (α := α) (U w + x • V w) σ * (V w) σ * (V w) σ :=
    Finset.measurable_sum _ fun σ _ => ((hpmf σ).mul (hev σ)).mul (hev σ)
  have h2 : Measurable fun w =>
      ∑ σ : α, gibbs_pmf (α := α) (U w + x • V w) σ * (V w) σ :=
    Finset.measurable_sum _ fun σ _ => (hpmf σ).mul (hev σ)
  simpa [hessian_free_energy] using (h1.sub (h2.mul h2)).const_mul (1 / (n : ℝ))

lemma integrable_free_energy_density_path (hU : Measurable U) (hV : Measurable V)
    (hUi : Integrable (fun w => ‖U w‖) P) (hVi : Integrable (fun w => ‖V w‖) P) (n : ℕ) (x : ℝ) :
    Integrable (fun w => free_energy_density (α := α) n (U w + x • V w)) P := by
  refine integrable_free_energy_density_of_integrable_norm (α := α) P n (by fun_prop) ?_
  refine Integrable.mono' (hUi.add (hVi.const_mul |x|)) (by fun_prop) ?_
  filter_upwards with w
  have hb : ‖U w + x • V w‖ ≤ ‖U w‖ + |x| * ‖V w‖ := by
    refine (norm_add_le _ _).trans_eq ?_
    rw [norm_smul, Real.norm_eq_abs]
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hb

omit [IsProbabilityMeasure P] in
lemma integrable_hessian_path (hU : Measurable U) (hV : Measurable V)
    (hVi2 : Integrable (fun w => ‖V w‖ ^ 2) P) (n : ℕ) (x : ℝ) :
    Integrable (fun w =>
      hessian_free_energy (α := α) n (U w + x • V w) (V w) (V w)) P := by
  refine Integrable.mono' (hVi2.const_mul (2 / (n : ℝ)))
    (measurable_hessian_path n hU hV x).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  have h := abs_hessian_free_energy_le (α := α) n (U w + x • V w) (V w) (V w)
  rw [Real.norm_eq_abs]
  calc |hessian_free_energy (α := α) n (U w + x • V w) (V w) (V w)|
      ≤ (2 / (n : ℝ)) * ‖V w‖ * ‖V w‖ := h
    _ = (2 / (n : ℝ)) * ‖V w‖ ^ 2 := by ring

/-! ### Differentiating under the integral -/

/-- **The derivative of the mean free energy along an affine path in the Hamiltonian**:
`p'(x) = -𝔼⟨H'⟩ / n`. Talagrand Vol. II, (12.6)–(12.7). -/
theorem hasDerivAt_integral_free_energy_density (hU : Measurable U) (hV : Measurable V)
    (hUi : Integrable (fun w => ‖U w‖) P) (hVi : Integrable (fun w => ‖V w‖) P)
    (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ w, free_energy_density (α := α) n (U w + y • V w) ∂P)
      (∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w) ∂P) x := by
  classical
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y w => free_energy_density (α := α) n (U w + y • V w))
    (F' := fun y w => -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + y • V w) (V w))
    (bound := fun w => (1 / (n : ℝ)) * ‖V w‖)
    (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun y => ?_)
    (integrable_free_energy_density_path hU hV hUi hVi n x)
    ((measurable_gibbs_average_path hU hV x).const_mul _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w y _ => ?_) (hVi.const_mul _)
    (Filter.Eventually.of_forall fun w y _ => ?_)).2
  · exact ((contDiff_free_energy_density (α := α) (n := n)).continuous.measurable.comp
      (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_neg,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (n : ℝ))]
    exact mul_le_mul_of_nonneg_left (abs_gibbs_average_le (α := α) _ _) (by positivity)
  · exact hasDerivAt_free_energy_density_add_smul (α := α) n (U w) (V w) y

omit [IsProbabilityMeasure P] in
/-- **The second derivative of the mean free energy is the mean Gibbs fluctuation.**
Talagrand Vol. II, (12.8). -/
theorem hasDerivAt_integral_gibbs_average (hU : Measurable U) (hV : Measurable V)
    (hVi : Integrable (fun w => ‖V w‖) P) (hVi2 : Integrable (fun w => ‖V w‖ ^ 2) P)
    (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + y • V w) (V w) ∂P)
      (∫ w, hessian_free_energy (α := α) n (U w + x • V w) (V w) (V w) ∂P) x := by
  classical
  have hint0 : Integrable
      (fun w => -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w)) P := by
    refine Integrable.mono' (hVi.const_mul (1 / (n : ℝ)))
      ((measurable_gibbs_average_path hU hV x).const_mul _).aestronglyMeasurable ?_
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_mul, abs_neg,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (n : ℝ))]
    exact mul_le_mul_of_nonneg_left (abs_gibbs_average_le (α := α) _ _) (by positivity)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y w => -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + y • V w) (V w))
    (F' := fun y w => hessian_free_energy (α := α) n (U w + y • V w) (V w) (V w))
    (bound := fun w => (2 / (n : ℝ)) * ‖V w‖ ^ 2)
    (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun y =>
      ((measurable_gibbs_average_path hU hV y).const_mul _).aestronglyMeasurable)
    hint0
    (measurable_hessian_path n hU hV x).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w y _ => ?_) (hVi2.const_mul _)
    (Filter.Eventually.of_forall fun w y _ =>
      hasDerivAt_gibbsAverage_add_smul (α := α) n (U w) (V w) y)).2
  have := abs_hessian_free_energy_le (α := α) n (U w + y • V w) (V w) (V w)
  rw [Real.norm_eq_abs]
  calc |hessian_free_energy (α := α) n (U w + y • V w) (V w) (V w)|
      ≤ (2 / (n : ℝ)) * ‖V w‖ * ‖V w‖ := this
    _ = (2 / (n : ℝ)) * ‖V w‖ ^ 2 := by ring

/-! ### The fundamental theorem of calculus: equation (12.9) -/

/-- The Gibbs variance depends continuously on the parameter. -/
lemma continuous_hessian_path (n : ℕ) (H W : EnergySpace α) :
    Continuous fun x : ℝ => hessian_free_energy (α := α) n (H + x • W) W W := by
  classical
  have hpath : Continuous fun x : ℝ => H + x • W := by fun_prop
  have hp : ∀ σ : α, Continuous fun x : ℝ => gibbs_pmf (α := α) (H + x • W) σ := fun σ =>
    (contDiff_gibbs_pmf (α := α) σ).continuous.comp hpath
  have h1 : Continuous fun x : ℝ =>
      ∑ σ : α, gibbs_pmf (α := α) (H + x • W) σ * W σ * W σ :=
    continuous_finsetSum _ fun σ _ => ((hp σ).mul continuous_const).mul continuous_const
  have h2 : Continuous fun x : ℝ =>
      ∑ σ : α, gibbs_pmf (α := α) (H + x • W) σ * W σ :=
    continuous_finsetSum _ fun σ _ => (hp σ).mul continuous_const
  simpa [hessian_free_energy] using ((h1.sub (h2.mul h2)).const_mul (1 / (n : ℝ)))

omit [IsProbabilityMeasure P] in
/-- The mean Gibbs variance depends continuously on the parameter. -/
lemma continuous_integral_hessian_path (hU : Measurable U) (hV : Measurable V)
    (hVi2 : Integrable (fun w => ‖V w‖ ^ 2) P) (n : ℕ) :
    Continuous fun x : ℝ =>
      ∫ w, hessian_free_energy (α := α) n (U w + x • V w) (V w) (V w) ∂P := by
  refine continuous_of_dominated
    (fun x => (measurable_hessian_path n hU hV x).aestronglyMeasurable)
    (fun x => Filter.Eventually.of_forall fun w => ?_) (hVi2.const_mul (2 / (n : ℝ)))
    (Filter.Eventually.of_forall fun w => continuous_hessian_path n (U w) (V w))
  have h := abs_hessian_free_energy_le (α := α) n (U w + x • V w) (V w) (V w)
  rw [Real.norm_eq_abs]
  calc |hessian_free_energy (α := α) n (U w + x • V w) (V w) (V w)|
      ≤ (2 / (n : ℝ)) * ‖V w‖ * ‖V w‖ := h
    _ = (2 / (n : ℝ)) * ‖V w‖ ^ 2 := by ring

omit [IsProbabilityMeasure P] in
/-- **Talagrand, Vol. II, equation (12.9).** The mean Gibbs fluctuation of the direction `V`,
integrated over the parameter, is the increment of the derivative of the mean free energy:

`∫_a^b 𝔼⟨(V - ⟨V⟩)²⟩/n dx = p'(b) - p'(a)`.

Since the integrand is nonnegative, this bounds the *total* fluctuation over any parameter window
by an increment of `p'`. That is the mechanism by which the energy self-averages: if `p'` is
bounded uniformly in the volume, the fluctuation must be small for most parameter values. -/
theorem integral_fluctuation_eq_sub (hU : Measurable U) (hV : Measurable V)
    (hVi : Integrable (fun w => ‖V w‖) P) (hVi2 : Integrable (fun w => ‖V w‖ ^ 2) P)
    (n : ℕ) (a b : ℝ) :
    (∫ x in a..b, ∫ w, hessian_free_energy (α := α) n (U w + x • V w) (V w) (V w) ∂P)
      = (∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + b • V w) (V w) ∂P)
        - ∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + a • V w) (V w) ∂P :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_integral_gibbs_average hU hV hVi hVi2 n x)
    ((continuous_integral_hessian_path hU hV hVi2 n).intervalIntegrable a b)

omit [IsProbabilityMeasure P] in
/-- **Equation (12.9) in variance form.** -/
theorem integral_variance_eq_sub (hU : Measurable U) (hV : Measurable V)
    (hVi : Integrable (fun w => ‖V w‖) P) (hVi2 : Integrable (fun w => ‖V w‖ ^ 2) P)
    (n : ℕ) (a b : ℝ) :
    (∫ x in a..b, ∫ w, (1 / (n : ℝ)) *
        ∑ σ : α, gibbs_pmf (α := α) (U w + x • V w) σ
          * ((V w) σ - gibbs_average (α := α) (U w + x • V w) (V w)) ^ 2 ∂P)
      = (∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + b • V w) (V w) ∂P)
        - ∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + a • V w) (V w) ∂P := by
  rw [← integral_fluctuation_eq_sub hU hV hVi hVi2 n a b]
  refine intervalIntegral.integral_congr fun x _ => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  exact (hessian_free_energy_self_eq_variance (α := α) n (U w + x • V w) (V w)).symm

end

end FiniteGibbs

end SpinGlass
