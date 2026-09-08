/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.FiniteGibbs.FluctuationIntegral
import SpinGlass.FiniteGibbs.GGError
import Common.Mathlib.MeasureTheory.Integral.CauchySchwarz

/-!
# Self-averaging of the energy

Talagrand, Vol. II, §12.1, equation (12.10): the **mean absolute** Gibbs fluctuation of the
normalised energy, integrated over the parameter, obeys

`∫_a^b 𝔼⟨|V/n - ⟨V/n⟩|⟩ dx ≤ √( (b-a) · (p'(b) - p'(a)) / n )`.

Three applications of Cauchy–Schwarz turn the `L²` identity `(12.9)` into this `L¹` bound: one
inside the Gibbs bracket (`sq_sum_gibbs_pmf_mul_abs_le`), one against the disorder, and one against
the parameter (`intervalIntegral.integral_le_sqrt_mul_integral_sq`). When `p'` is bounded uniformly
in the volume — which for the SK model is `deriv_skFreeEnergy_nonneg_le` — the right-hand side is
`O(n^{-1/2})`, so the energy per site self-averages for almost every parameter value. This is the
quantitative content of Talagrand's Theorem 12.1.1, and the reason the Ghirlanda–Guerra identities
become exact in the thermodynamic limit.

## Main statements

- `SpinGlass.FiniteGibbs.sq_gibbs_average_abs_sub_le` — Cauchy–Schwarz inside the Gibbs bracket.
- `SpinGlass.FiniteGibbs.integral_absFluct_le_sqrt` — Cauchy–Schwarz against the disorder.
- `SpinGlass.FiniteGibbs.intervalIntegral_absFluct_le` — **equation (12.10)**.
-/

open MeasureTheory Real BigOperators Filter Topology Set

namespace SpinGlass

namespace FiniteGibbs

noncomputable section

variable {α : Type*} [Fintype α] [Nonempty α]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {U V : Ω → EnergySpace α}

/-! ### Measurability and continuity of the mean absolute fluctuation -/

omit [IsProbabilityMeasure P] in
lemma measurable_absFluct_path (n : ℕ) (hU : Measurable U) (hV : Measurable V) (x : ℝ) :
    Measurable fun w => (1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w)
      (fun σ => |V w σ - gibbs_average (α := α) (U w + x • V w) (V w)|) := by
  classical
  have hpath : Measurable fun w => U w + x • V w := by fun_prop
  have hpmf : ∀ σ : α, Measurable fun w => gibbs_pmf (α := α) (U w + x • V w) σ := fun σ =>
    ((contDiff_gibbs_pmf (α := α) σ).continuous.measurable).comp hpath
  have hev : ∀ σ : α, Measurable fun w => (V w) σ := fun σ =>
    (measurable_eval (α := α) σ).comp hV
  have hmean : Measurable fun w => gibbs_average (α := α) (U w + x • V w) (V w) :=
    measurable_gibbs_average_path hU hV x
  simp only [gibbs_average]
  refine (Finset.measurable_sum _ fun σ _ => (hpmf σ).mul ?_).const_mul _
  have hd : Measurable fun w => (V w) σ - gibbs_average (α := α) (U w + x • V w) (V w) :=
    (hev σ).sub hmean
  fun_prop

omit [IsProbabilityMeasure P] in
lemma continuous_absFluct_path (n : ℕ) (H W : EnergySpace α) :
    Continuous fun x : ℝ => (1 / (n : ℝ)) * gibbs_average (α := α) (H + x • W)
      (fun σ => |W σ - gibbs_average (α := α) (H + x • W) W|) := by
  classical
  have hpath : Continuous fun x : ℝ => H + x • W := by fun_prop
  have hp : ∀ σ : α, Continuous fun x : ℝ => gibbs_pmf (α := α) (H + x • W) σ := fun σ =>
    ((contDiff_gibbs_pmf (α := α) σ).continuous).comp hpath
  have hmean : Continuous fun x : ℝ => gibbs_average (α := α) (H + x • W) W := by
    simp only [gibbs_average]
    exact continuous_finsetSum _ fun σ _ => (hp σ).mul continuous_const
  simp only [gibbs_average]
  exact (continuous_finsetSum _ fun σ _ =>
    (hp σ).mul ((continuous_const.sub hmean).abs)).const_mul _

/-! ### Cauchy–Schwarz inside the Gibbs bracket -/

/-- **Cauchy–Schwarz inside the Gibbs bracket, normalised**: the square of the mean absolute
fluctuation is at most `1/n` times the second derivative of the free energy. -/
lemma sq_gibbs_average_abs_sub_le (n : ℕ) (K W : EnergySpace α) :
    ((1 / (n : ℝ)) * gibbs_average (α := α) K
        (fun σ => |W σ - gibbs_average (α := α) K W|)) ^ 2
      ≤ (1 / (n : ℝ)) * hessian_free_energy (α := α) n K W W := by
  have hcs := sq_sum_gibbs_pmf_mul_abs_le (α := α) K
    (fun σ => W σ - gibbs_average (α := α) K W)
  rw [hessian_free_energy_self_eq_variance (α := α) n K W]
  calc ((1 / (n : ℝ)) * gibbs_average (α := α) K
          (fun σ => |W σ - gibbs_average (α := α) K W|)) ^ 2
      = (1 / (n : ℝ)) ^ 2 * (gibbs_average (α := α) K
          (fun σ => |W σ - gibbs_average (α := α) K W|)) ^ 2 := by ring
    _ ≤ (1 / (n : ℝ)) ^ 2 * (∑ σ : α, gibbs_pmf (α := α) K σ
          * (W σ - gibbs_average (α := α) K W) ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    _ = (1 / (n : ℝ)) * ((1 / (n : ℝ)) * ∑ σ : α, gibbs_pmf (α := α) K σ
          * (W σ - gibbs_average (α := α) K W) ^ 2) := by ring

/-! ### Cauchy–Schwarz against the disorder -/

omit [Nonempty α] [IsProbabilityMeasure P] in
lemma memLp_two_norm (hV : Measurable V) (hVi2 : Integrable (fun w => ‖V w‖ ^ 2) P) :
    MemLp (fun w => ‖V w‖) 2 P := by
  refine (memLp_two_iff_integrable_sq_norm (hV.norm.aestronglyMeasurable)).2 ?_
  simpa [Real.norm_eq_abs, sq_abs] using hVi2

/-- **Cauchy–Schwarz against the disorder**: the mean absolute fluctuation is at most the square
root of `1/n` times the mean square fluctuation. -/
lemma integral_absFluct_le_sqrt (n : ℕ) (hU : Measurable U)
    (hV : Measurable V) (hVi2 : Integrable (fun w => ‖V w‖ ^ 2) P) (x : ℝ) :
    (∫ w, (1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w)
        (fun σ => |V w σ - gibbs_average (α := α) (U w + x • V w) (V w)|) ∂P)
      ≤ Real.sqrt ((1 / (n : ℝ)) *
          ∫ w, hessian_free_energy (α := α) n (U w + x • V w) (V w) (V w) ∂P) := by
  classical
  set G : Ω → ℝ := fun w => (1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w)
    (fun σ => |V w σ - gibbs_average (α := α) (U w + x • V w) (V w)|) with hG
  have hGmeas : Measurable G := measurable_absFluct_path n hU hV x
  have hGnn : ∀ w, 0 ≤ G w := fun w => by
    rw [hG]
    exact mul_nonneg (by positivity)
      (gibbs_average_abs_sub_nonneg (α := α) (U w + x • V w) (V w) _)
  have hGb : ∀ w, ‖G w‖ ≤ ‖(1 / (n : ℝ)) * (2 * ‖V w‖)‖ := by
    intro w
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hGnn w),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 / (n : ℝ)) * (2 * ‖V w‖)), hG]
    exact mul_le_mul_of_nonneg_left
      (gibbs_average_abs_sub_gibbs_average_le (α := α) (U w + x • V w) (V w)) (by positivity)
  have hGmem : MemLp G 2 P :=
    (((memLp_two_norm hV hVi2).const_mul 2).const_mul (1 / (n : ℝ))).of_le
      hGmeas.aestronglyMeasurable (Eventually.of_forall hGb)
  -- Cauchy–Schwarz against the probability measure `P`.
  have hCS := MeasureTheory.sq_integral_le_measureReal_univ_mul_integral_sq (μ := P) hGmem
  have huniv : P.real Set.univ = 1 := by simp [measureReal_def]
  rw [huniv, one_mul] at hCS
  have hHint : Integrable (fun w =>
      hessian_free_energy (α := α) n (U w + x • V w) (V w) (V w)) P :=
    integrable_hessian_path hU hV hVi2 n x
  have hmono : (∫ w, G w ^ 2 ∂P)
      ≤ ∫ w, (1 / (n : ℝ)) * hessian_free_energy (α := α) n (U w + x • V w) (V w) (V w) ∂P :=
    integral_mono hGmem.integrable_sq (hHint.const_mul _)
      fun w => sq_gibbs_average_abs_sub_le (α := α) n (U w + x • V w) (V w)
  rw [integral_const_mul] at hmono
  have hIntnn : 0 ≤ ∫ w, G w ∂P := integral_nonneg hGnn
  calc (∫ w, G w ∂P) = Real.sqrt ((∫ w, G w ∂P) ^ 2) := (Real.sqrt_sq hIntnn).symm
    _ ≤ Real.sqrt ((1 / (n : ℝ)) *
          ∫ w, hessian_free_energy (α := α) n (U w + x • V w) (V w) (V w) ∂P) :=
        Real.sqrt_le_sqrt (le_trans hCS hmono)

/-! ### Cauchy–Schwarz against the parameter: equation (12.10) -/

omit [IsProbabilityMeasure P] in
lemma continuous_integral_absFluct_path (n : ℕ) (hU : Measurable U) (hV : Measurable V)
    (hVi : Integrable (fun w => ‖V w‖) P) :
    Continuous fun x : ℝ => ∫ w, (1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w)
      (fun σ => |V w σ - gibbs_average (α := α) (U w + x • V w) (V w)|) ∂P := by
  refine continuous_of_dominated
    (fun x => (measurable_absFluct_path n hU hV x).aestronglyMeasurable)
    (fun x => Filter.Eventually.of_forall fun w => ?_)
    ((hVi.const_mul 2).const_mul (1 / (n : ℝ)))
    (Filter.Eventually.of_forall fun w => continuous_absFluct_path n (U w) (V w))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (n : ℝ)),
    abs_of_nonneg (gibbs_average_abs_sub_nonneg (α := α) (U w + x • V w) (V w) _)]
  exact mul_le_mul_of_nonneg_left
    (gibbs_average_abs_sub_gibbs_average_le (α := α) (U w + x • V w) (V w)) (by positivity)

omit [IsProbabilityMeasure P] in
lemma integral_hessian_path_le (n : ℕ) (hU : Measurable U) (hV : Measurable V)
    (hVi2 : Integrable (fun w => ‖V w‖ ^ 2) P) (x : ℝ) :
    (∫ w, hessian_free_energy (α := α) n (U w + x • V w) (V w) (V w) ∂P)
      ≤ (2 / (n : ℝ)) * ∫ w, ‖V w‖ ^ 2 ∂P := by
  rw [← integral_const_mul]
  refine integral_mono (integrable_hessian_path hU hV hVi2 n x) (hVi2.const_mul _) fun w => ?_
  have h := hessian_free_energy_self_le (α := α) n (U w + x • V w) (V w)
  calc hessian_free_energy (α := α) n (U w + x • V w) (V w) (V w)
      ≤ (2 / (n : ℝ)) * ‖V w‖ * ‖V w‖ := h
    _ = (2 / (n : ℝ)) * ‖V w‖ ^ 2 := by ring

/-- **Talagrand, Vol. II, equation (12.10).** The mean *absolute* Gibbs fluctuation of the
normalised energy, integrated over the parameter, is at most

`√( (b - a) · (p'(b) - p'(a)) / n )`.

Three Cauchy–Schwarz steps — inside the Gibbs bracket, against the disorder, and against the
parameter — turn the `L²` identity `(12.9)` into this `L¹` bound. When `p'` is bounded uniformly in
the volume the right-hand side is `O(n^{-1/2})`: the energy per site self-averages. -/
theorem intervalIntegral_absFluct_le (n : ℕ) (hU : Measurable U) (hV : Measurable V)
    (hVi : Integrable (fun w => ‖V w‖) P) (hVi2 : Integrable (fun w => ‖V w‖ ^ 2) P)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, ∫ w, (1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w)
        (fun σ => |V w σ - gibbs_average (α := α) (U w + x • V w) (V w)|) ∂P)
      ≤ Real.sqrt ((b - a) * ((1 / (n : ℝ)) *
          ((∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + b • V w) (V w) ∂P)
            - ∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + a • V w) (V w) ∂P))) := by
  classical
  set S : ℝ → ℝ := fun x =>
    ∫ w, hessian_free_energy (α := α) n (U w + x • V w) (V w) (V w) ∂P with hS
  set A : ℝ → ℝ := fun x => ∫ w, (1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w)
    (fun σ => |V w σ - gibbs_average (α := α) (U w + x • V w) (V w)|) ∂P with hA
  have hScont : Continuous S := continuous_integral_hessian_path hU hV hVi2 n
  have hAcont : Continuous A := continuous_integral_absFluct_path n hU hV hVi
  have hSnn : ∀ x, 0 ≤ S x := fun x =>
    integral_nonneg fun w => hessian_free_energy_self_nonneg (α := α) n (U w + x • V w) (V w)
  have hnn : ∀ x, (0 : ℝ) ≤ (1 / (n : ℝ)) * S x := fun x => by
    have := hSnn x; positivity
  have hAle : ∀ x, A x ≤ Real.sqrt ((1 / (n : ℝ)) * S x) := fun x =>
    integral_absFluct_le_sqrt n hU hV hVi2 x
  have hsqcont : Continuous fun x : ℝ => Real.sqrt ((1 / (n : ℝ)) * S x) :=
    Real.continuous_sqrt.comp (continuous_const.mul hScont)
  -- Step 1: interval monotonicity.
  have h1 : (∫ x in a..b, A x) ≤ ∫ x in a..b, Real.sqrt ((1 / (n : ℝ)) * S x) :=
    intervalIntegral.integral_mono_on hab (hAcont.intervalIntegrable a b)
      (hsqcont.intervalIntegrable a b) fun x _ => hAle x
  -- Step 2: Cauchy–Schwarz against the parameter.
  have hmem : MemLp (fun x : ℝ => Real.sqrt ((1 / (n : ℝ)) * S x)) 2
      (volume.restrict (Set.Ioc a b)) := by
    refine MemLp.of_bound (hsqcont.aestronglyMeasurable)
      (Real.sqrt ((1 / (n : ℝ)) * ((2 / (n : ℝ)) * ∫ w, ‖V w‖ ^ 2 ∂P)))
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    refine Real.sqrt_le_sqrt ?_
    exact mul_le_mul_of_nonneg_left (integral_hessian_path_le n hU hV hVi2 x) (by positivity)
  have h2 := intervalIntegral.integral_le_sqrt_mul_integral_sq hab hmem
    (fun x _ => Real.sqrt_nonneg _)
  -- Step 3: the squared integrand is `(1/n) S`, whose interval integral is `(12.9)`.
  have hsq : ∀ x : ℝ, Real.sqrt ((1 / (n : ℝ)) * S x) ^ 2 = (1 / (n : ℝ)) * S x := fun x =>
    Real.sq_sqrt (hnn x)
  have h3 : (∫ x in a..b, Real.sqrt ((1 / (n : ℝ)) * S x) ^ 2)
      = (1 / (n : ℝ)) *
          ((∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + b • V w) (V w) ∂P)
            - ∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + a • V w) (V w) ∂P) := by
    rw [intervalIntegral.integral_congr (g := fun x => (1 / (n : ℝ)) * S x)
      fun x _ => hsq x, intervalIntegral.integral_const_mul, hS,
      integral_fluctuation_eq_sub hU hV hVi hVi2 n a b]
  rw [h3] at h2
  exact le_trans h1 h2

end

end FiniteGibbs

end SpinGlass
