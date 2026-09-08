/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.FiniteGibbs.SelfAveraging
import Common.Mathlib.Analysis.Convex.GriffithsMean
import Common.Mathlib.MeasureTheory.Integral.MonotoneShift

/-!
# Self-averaging of the mean energy over the disorder

`SpinGlass.FiniteGibbs.intervalIntegral_absFluct_le` controls the fluctuation of the energy under
the *Gibbs* measure. The other half of Talagrand's Theorem 12.1.1 controls its fluctuation under
the *disorder*: `𝔼|⟨V/n⟩ - 𝔼⟨V/n⟩|`, i.e. `𝔼|θ'(x) - p'(x)|` for the free energy `θ` of a single
sample and its mean `p`.

Convexity converts a bound on `𝔼|θ - p|` into a bound on `𝔼|θ' - p'|`
(`ConvexOn.integral_abs_deriv_sub_le`, Talagrand's Lemmas 12.1.5–12.1.6) at the price of a factor
`1/δ` and an error `p'(x+δ) - p'(x-δ)`; integrating in `x` the latter telescopes
(`intervalIntegral.integral_sub_shift_le_of_monotone`), leaving

`∫_a^b 𝔼|⟨V/n⟩ - 𝔼⟨V/n⟩| dx ≤ 2δ (p'(b+δ) - p'(a-δ)) + 3(b-a)C/δ`

for any `C` bounding `𝔼|θ(y) - p(y)|`. Optimising `δ ≍ √C` gives `O(√C)`; for a Gaussian disorder
`C = O(n^{-1/2})` by Gaussian concentration, so the bound is `O(n^{-1/4})` — exactly the rate of
Talagrand's Theorem 12.1.1.

## Main statements

- `SpinGlass.FiniteGibbs.intervalIntegral_integral_abs_meanEnergy_sub_le`.
-/

open MeasureTheory Real BigOperators Filter Topology Set

namespace SpinGlass

namespace FiniteGibbs

noncomputable section

variable {α : Type*} [Fintype α] [Nonempty α]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {U V : Ω → EnergySpace α}

/-! ### The mean free energy is convex, differentiable, and its derivative is monotone -/

lemma convexOn_integral_free_energy_density (n : ℕ) (hU : Measurable U) (hV : Measurable V)
    (hUi : Integrable (fun w => ‖U w‖) P) (hVi : Integrable (fun w => ‖V w‖) P) :
    ConvexOn ℝ (univ : Set ℝ)
      fun x => ∫ w, free_energy_density (α := α) n (U w + x • V w) ∂P := by
  refine ⟨convex_univ, fun s _ t _ c d hc hd hcd => ?_⟩
  have hpt : ∀ w, free_energy_density (α := α) n (U w + (c * s + d * t) • V w)
      ≤ c * free_energy_density (α := α) n (U w + s • V w)
        + d * free_energy_density (α := α) n (U w + t • V w) := by
    intro w
    have h := (convexOn_free_energy_density_comp_affine (α := α) n (U w) (V w)).2
      (mem_univ s) (mem_univ t) hc hd hcd
    simpa [smul_eq_mul] using h
  have hIs : Integrable (fun w => c * free_energy_density (α := α) n (U w + s • V w)) P :=
    (integrable_free_energy_density_path hU hV hUi hVi n s).const_mul c
  have hIt : Integrable (fun w => d * free_energy_density (α := α) n (U w + t • V w)) P :=
    (integrable_free_energy_density_path hU hV hUi hVi n t).const_mul d
  have hIsum : Integrable (fun w => c * free_energy_density (α := α) n (U w + s • V w)
      + d * free_energy_density (α := α) n (U w + t • V w)) P := hIs.add hIt
  have hmono := integral_mono
    (integrable_free_energy_density_path hU hV hUi hVi n (c * s + d * t)) hIsum hpt
  rw [integral_add hIs hIt, integral_const_mul, integral_const_mul] at hmono
  simpa [smul_eq_mul] using hmono

lemma differentiableAt_integral_free_energy_density (n : ℕ) (hU : Measurable U)
    (hV : Measurable V) (hUi : Integrable (fun w => ‖U w‖) P)
    (hVi : Integrable (fun w => ‖V w‖) P) (x : ℝ) :
    DifferentiableAt ℝ (fun y : ℝ => ∫ w, free_energy_density (α := α) n (U w + y • V w) ∂P) x :=
  (hasDerivAt_integral_free_energy_density (α := α) (P := P) hU hV hUi hVi n x).differentiableAt

lemma deriv_integral_free_energy_density (n : ℕ) (hU : Measurable U) (hV : Measurable V)
    (hUi : Integrable (fun w => ‖U w‖) P) (hVi : Integrable (fun w => ‖V w‖) P) (x : ℝ) :
    deriv (fun y : ℝ => ∫ w, free_energy_density (α := α) n (U w + y • V w) ∂P) x
      = -∫ w, (1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w) ∂P := by
  rw [(hasDerivAt_integral_free_energy_density hU hV hUi hVi n x).deriv, ← integral_neg]
  exact integral_congr_ae (Filter.Eventually.of_forall fun w => by ring)

lemma monotone_deriv_integral_free_energy_density (n : ℕ) (hU : Measurable U) (hV : Measurable V)
    (hUi : Integrable (fun w => ‖U w‖) P) (hVi : Integrable (fun w => ‖V w‖) P) :
    Monotone (deriv fun y : ℝ => ∫ w, free_energy_density (α := α) n (U w + y • V w) ∂P) := by
  have h := (convexOn_integral_free_energy_density (α := α) n hU hV hUi hVi).monotoneOn_deriv
    (fun x _ => differentiableAt_integral_free_energy_density (α := α) n hU hV hUi hVi x)
  intro x y hxy
  exact h (mem_univ x) (mem_univ y) hxy

/-! ### Continuity in the parameter -/

omit [IsProbabilityMeasure P] in
lemma abs_integral_gibbs_average_path_le (n : ℕ) (hU : Measurable U) (hV : Measurable V)
    (hVi : Integrable (fun w => ‖V w‖) P) (x : ℝ) :
    |∫ w, (1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w) ∂P|
      ≤ (1 / (n : ℝ)) * ∫ w, ‖V w‖ ∂P := by
  have hint : Integrable
      (fun w => (1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w)) P := by
    refine Integrable.mono' (hVi.const_mul (1 / (n : ℝ)))
      ((measurable_gibbs_average_path hU hV x).const_mul _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (n : ℝ))]
    exact mul_le_mul_of_nonneg_left (abs_gibbs_average_le (α := α) _ _) (by positivity)
  calc |∫ w, (1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w) ∂P|
      ≤ ∫ w, |(1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w)| ∂P := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := P)
          (fun w => (1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w))
    _ ≤ ∫ w, (1 / (n : ℝ)) * ‖V w‖ ∂P := by
        refine integral_mono hint.abs (hVi.const_mul _) fun w => ?_
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (n : ℝ))]
        exact mul_le_mul_of_nonneg_left (abs_gibbs_average_le (α := α) _ _) (by positivity)
    _ = (1 / (n : ℝ)) * ∫ w, ‖V w‖ ∂P := integral_const_mul _ _

omit [IsProbabilityMeasure P] in
lemma continuous_integral_gibbs_average_path (n : ℕ) (hU : Measurable U) (hV : Measurable V)
    (hVi : Integrable (fun w => ‖V w‖) P) :
    Continuous fun x : ℝ =>
      ∫ w, (1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w) ∂P := by
  refine continuous_of_dominated
    (fun x => ((measurable_gibbs_average_path hU hV x).const_mul _).aestronglyMeasurable)
    (fun x => Filter.Eventually.of_forall fun w => ?_) (hVi.const_mul (1 / (n : ℝ)))
    (Filter.Eventually.of_forall fun w =>
      (continuous_gibbs_average_path (α := α) (U w) (V w)).const_mul _)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (n : ℝ))]
  exact mul_le_mul_of_nonneg_left (abs_gibbs_average_le (α := α) _ _) (by positivity)

lemma continuous_integral_abs_meanEnergy_sub (n : ℕ) (hU : Measurable U) (hV : Measurable V)
    (hVi : Integrable (fun w => ‖V w‖) P) :
    Continuous fun x : ℝ => ∫ w, |(1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w)
      - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P| ∂P := by
  have hq := continuous_integral_gibbs_average_path (α := α) n hU hV hVi
  refine continuous_of_dominated (fun x => ?_) (fun x => Filter.Eventually.of_forall fun w => ?_)
    ((hVi.const_mul (1 / (n : ℝ))).add
      (integrable_const ((1 / (n : ℝ)) * ∫ w, ‖V w‖ ∂P)))
    (Filter.Eventually.of_forall fun w => ?_)
  · have hm : Measurable fun w => (1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w)
        - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P :=
      ((measurable_gibbs_average_path hU hV x).const_mul _).sub measurable_const
    have : Measurable fun w => |(1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w)
        - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P| := by
      fun_prop
    exact this.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_abs]
    refine (abs_sub _ _).trans (add_le_add ?_ (abs_integral_gibbs_average_path_le n hU hV hVi x))
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (n : ℝ))]
    exact mul_le_mul_of_nonneg_left (abs_gibbs_average_le (α := α) _ _) (by positivity)
  · exact (((continuous_gibbs_average_path (α := α) (U w) (V w)).const_mul _).sub hq).abs

/-! ### The second half of Theorem 12.1.1 -/

/-- **The mean energy self-averages over the disorder.** For any `C` bounding the mean absolute
deviation of the free energy from its mean, and any window width `δ > 0`,

`∫_a^b 𝔼|⟨V/n⟩ - 𝔼⟨V/n⟩| dx ≤ 2δ (p'(b+δ) - p'(a-δ)) + 3(b-a)C/δ`.

Talagrand, Vol. II, §12.1, the passage from (12.5) to (12.7): convexity converts concentration of
the free energy into concentration of its derivative, and the resulting error telescopes when
integrated in the parameter. Optimising `δ ≍ √C` gives `O(√C)`. -/
theorem intervalIntegral_integral_abs_meanEnergy_sub_le
    (n : ℕ) (hU : Measurable U) (hV : Measurable V)
    (hUi : Integrable (fun w => ‖U w‖) P) (hVi : Integrable (fun w => ‖V w‖) P)
    {δ C : ℝ} (hδ : 0 < δ) {a b : ℝ} (hab : a ≤ b)
    (hC : ∀ y ∈ Set.Icc (a - δ) (b + δ), (∫ w, |free_energy_density (α := α) n (U w + y • V w)
        - ∫ w', free_energy_density (α := α) n (U w' + y • V w') ∂P| ∂P) ≤ C) :
    (∫ x in a..b, ∫ w, |(1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w)
        - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P| ∂P)
      ≤ 2 * δ *
          (deriv (fun y : ℝ => ∫ w, free_energy_density (α := α) n (U w + y • V w) ∂P) (b + δ)
            - deriv (fun y : ℝ => ∫ w, free_energy_density (α := α) n (U w + y • V w) ∂P) (a - δ))
        + 3 * (b - a) * C / δ := by
  classical
  set θ : Ω → ℝ → ℝ := fun w x => free_energy_density (α := α) n (U w + x • V w) with hθ
  set p : ℝ → ℝ := fun x => ∫ w, free_energy_density (α := α) n (U w + x • V w) ∂P with hp
  set A : ℝ → ℝ := fun x => ∫ w, |(1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w)
    - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P| ∂P with hA
  have hθconv : ∀ w, ConvexOn ℝ (univ : Set ℝ) (θ w) := fun w => by
    have := convexOn_free_energy_density_comp_affine (α := α) n (U w) (V w)
    simpa [hθ] using this
  have hpconv : ConvexOn ℝ (univ : Set ℝ) p :=
    convexOn_integral_free_energy_density (α := α) n hU hV hUi hVi
  have hθderiv : ∀ (w : Ω) (x : ℝ), HasDerivAt (θ w)
      (-(1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w)) x := fun w x =>
    hasDerivAt_free_energy_density_add_smul (α := α) n (U w) (V w) x
  have hpderiv : ∀ x : ℝ, HasDerivAt p
      (∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w) ∂P) x := fun x =>
    hasDerivAt_integral_free_energy_density (α := α) (P := P) hU hV hUi hVi n x
  have hθd : ∀ (w : Ω) (x : ℝ), DifferentiableAt ℝ (θ w) x := fun w x =>
    (hθderiv w x).differentiableAt
  have hpd : ∀ x : ℝ, DifferentiableAt ℝ p x := fun x => (hpderiv x).differentiableAt
  have hIabs : ∀ y : ℝ, Integrable (fun w => |θ w y - p y|) P := fun y =>
    ((integrable_free_energy_density_path hU hV hUi hVi n y).sub (integrable_const (p y))).abs
  -- The pointwise (in `x`) Griffiths estimate.
  have hAle : ∀ x ∈ Set.Icc a b, A x ≤ (deriv p (x + δ) - deriv p (x - δ)) + 3 * C / δ := by
    intro x hx
    have hgr := ConvexOn.integral_abs_deriv_sub_le (P := P) (S := (univ : Set ℝ)) (θ := θ)
      (p := p) (x := x) (b := δ) hθconv hpconv hδ (by simp) (by simp) (by simp)
      (fun w => hθd w x) (hpd x) (hpd (x - δ)) (hpd (x + δ))
      (hIabs x) (hIabs (x - δ)) (hIabs (x + δ))
    have hqeq : deriv p x
        = -∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P := by
      rw [(hpderiv x).deriv, ← integral_neg]
      exact integral_congr_ae (Filter.Eventually.of_forall fun w' => by ring)
    have hptw : ∀ w : Ω,
        |(1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w)
          - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P|
          = |deriv (θ w) x - deriv p x| := by
      intro w
      rw [(hθderiv w x).deriv, hqeq, ← abs_neg]
      congr 1
      ring
    have hAeq : A x = ∫ w, |deriv (θ w) x - deriv p x| ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall hptw)
    rw [hAeq]
    refine hgr.trans ?_
    have hbound : (∫ w, |θ w (x + δ) - p (x + δ)| ∂P) + (∫ w, |θ w (x - δ) - p (x - δ)| ∂P)
        + ∫ w, |θ w x - p x| ∂P ≤ 3 * C := by
      have h1 := hC (x + δ) ⟨by linarith [hx.1, hδ], by linarith [hx.2]⟩
      have h2 := hC (x - δ) ⟨by linarith [hx.1], by linarith [hx.2, hδ]⟩
      have h3 := hC x ⟨by linarith [hx.1, hδ], by linarith [hx.2, hδ]⟩
      simp only [hθ, hp] at h1 h2 h3 ⊢
      linarith
    have hdiv : ((∫ w, |θ w (x + δ) - p (x + δ)| ∂P) + (∫ w, |θ w (x - δ) - p (x - δ)| ∂P)
          + ∫ w, |θ w x - p x| ∂P) / δ ≤ 3 * C / δ := by
      gcongr
    linarith
  -- Integrate the estimate in `x`.
  have hAcont : Continuous A := continuous_integral_abs_meanEnergy_sub (α := α) n hU hV hVi
  have hmono : Monotone (deriv p) :=
    monotone_deriv_integral_free_energy_density (α := α) n hU hV hUi hVi
  have hmonoAdd : Monotone fun x : ℝ => deriv p (x + δ) := fun x y hxy => hmono (by linarith)
  have hmonoSub : Monotone fun x : ℝ => deriv p (x - δ) := fun x y hxy => hmono (by linarith)
  have hIntAdd : IntervalIntegrable (fun x : ℝ => deriv p (x + δ)) volume a b :=
    ((hmonoAdd.monotoneOn (Set.uIcc a b)).intervalIntegrable)
  have hIntSub : IntervalIntegrable (fun x : ℝ => deriv p (x - δ)) volume a b :=
    ((hmonoSub.monotoneOn (Set.uIcc a b)).intervalIntegrable)
  have hRint : IntervalIntegrable (fun x : ℝ => (deriv p (x + δ) - deriv p (x - δ)) + 3 * C / δ)
      volume a b := (hIntAdd.sub hIntSub).add intervalIntegrable_const
  have hstep1 : (∫ x in a..b, A x)
      ≤ ∫ x in a..b, ((deriv p (x + δ) - deriv p (x - δ)) + 3 * C / δ) :=
    intervalIntegral.integral_mono_on hab (hAcont.intervalIntegrable a b) hRint hAle
  have hshift : (∫ x in a..b, (deriv p (x + δ) - deriv p (x - δ)))
      ≤ 2 * δ * (deriv p (b + δ) - deriv p (a - δ)) :=
    intervalIntegral.integral_sub_shift_le_of_monotone hmono hδ
  have hsplit : (∫ x in a..b, ((deriv p (x + δ) - deriv p (x - δ)) + 3 * C / δ))
      = (∫ x in a..b, (deriv p (x + δ) - deriv p (x - δ))) + (b - a) * (3 * C / δ) := by
    rw [intervalIntegral.integral_add (hIntAdd.sub hIntSub) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
  rw [hsplit] at hstep1
  have hfin : (b - a) * (3 * C / δ) = 3 * (b - a) * C / δ := by ring
  rw [hfin] at hstep1
  linarith

/-! ### Theorem 12.1.1: the two halves combined -/

omit [IsProbabilityMeasure P] in
/-- The Gibbs mean absolute deviation of `W/n` from **any** constant splits into its deviation from
its own Gibbs mean plus the deviation of that mean from the constant. -/
lemma gibbs_average_abs_smul_sub_const_le (n : ℕ) (K W : EnergySpace α) (c : ℝ) :
    gibbs_average (α := α) K (fun σ => |(1 / (n : ℝ)) * W σ - c|)
      ≤ (1 / (n : ℝ)) * gibbs_average (α := α) K
            (fun σ => |W σ - gibbs_average (α := α) K W|)
        + |(1 / (n : ℝ)) * gibbs_average (α := α) K W - c| := by
  classical
  have hnn : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have hpt : ∀ σ : α, |(1 / (n : ℝ)) * W σ - c|
      ≤ (1 / (n : ℝ)) * |W σ - gibbs_average (α := α) K W|
        + |(1 / (n : ℝ)) * gibbs_average (α := α) K W - c| := by
    intro σ
    have htri : |(1 / (n : ℝ)) * W σ - c|
        ≤ |(1 / (n : ℝ)) * W σ - (1 / (n : ℝ)) * gibbs_average (α := α) K W|
          + |(1 / (n : ℝ)) * gibbs_average (α := α) K W - c| :=
      abs_sub_le _ _ _
    have heq : |(1 / (n : ℝ)) * W σ - (1 / (n : ℝ)) * gibbs_average (α := α) K W|
        = (1 / (n : ℝ)) * |W σ - gibbs_average (α := α) K W| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hnn]
    rw [heq] at htri
    exact htri
  calc gibbs_average (α := α) K (fun σ => |(1 / (n : ℝ)) * W σ - c|)
      ≤ ∑ σ : α, gibbs_pmf (α := α) K σ
          * ((1 / (n : ℝ)) * |W σ - gibbs_average (α := α) K W|
            + |(1 / (n : ℝ)) * gibbs_average (α := α) K W - c|) :=
        Finset.sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_left (hpt σ) (gibbs_pmf_nonneg (α := α) K σ)
    _ = (1 / (n : ℝ)) * gibbs_average (α := α) K
            (fun σ => |W σ - gibbs_average (α := α) K W|)
          + |(1 / (n : ℝ)) * gibbs_average (α := α) K W - c| := by
        simp only [gibbs_average, mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_gibbs_pmf (α := α) K, one_mul]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun σ _ => by ring

omit [IsProbabilityMeasure P] in
lemma measurable_totalFluct_path (n : ℕ) (hU : Measurable U) (hV : Measurable V) (x : ℝ) :
    Measurable fun w => gibbs_average (α := α) (U w + x • V w)
      (fun σ => |(1 / (n : ℝ)) * V w σ
        - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P|) := by
  classical
  have hpath : Measurable fun w => U w + x • V w := by fun_prop
  have hpmf : ∀ σ : α, Measurable fun w => gibbs_pmf (α := α) (U w + x • V w) σ := fun σ =>
    ((contDiff_gibbs_pmf (α := α) σ).continuous.measurable).comp hpath
  have hev : ∀ σ : α, Measurable fun w => (V w) σ := fun σ =>
    (measurable_eval (α := α) σ).comp hV
  simp only [gibbs_average]
  refine Finset.measurable_sum _ fun σ _ => (hpmf σ).mul ?_
  have hd : Measurable fun w => (1 / (n : ℝ)) * (V w) σ
      - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P :=
    ((hev σ).const_mul _).sub measurable_const
  fun_prop

lemma integrable_totalFluct_path (n : ℕ) (hU : Measurable U) (hV : Measurable V)
    (hVi : Integrable (fun w => ‖V w‖) P) (x : ℝ) :
    Integrable (fun w => gibbs_average (α := α) (U w + x • V w)
      (fun σ => |(1 / (n : ℝ)) * V w σ
        - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P|)) P := by
  have hdom : Integrable (fun w => (1 / (n : ℝ)) * ‖V w‖
      + (1 / (n : ℝ)) * ∫ w', ‖V w'‖ ∂P) P :=
    (hVi.const_mul (1 / (n : ℝ))).add (integrable_const _)
  refine Integrable.mono' hdom
    (measurable_totalFluct_path n hU hV x).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (gibbs_average_abs_smul_sub_const_nonneg (α := α) n (U w + x • V w) (V w) _)]
  refine (gibbs_average_abs_smul_sub_const_le_norm (α := α) n (U w + x • V w) (V w) _).trans ?_
  exact add_le_add le_rfl (abs_integral_gibbs_average_path_le n hU hV hVi x)

lemma continuous_integral_totalFluct (n : ℕ) (hU : Measurable U) (hV : Measurable V)
    (hVi : Integrable (fun w => ‖V w‖) P) :
    Continuous fun x : ℝ => ∫ w, gibbs_average (α := α) (U w + x • V w)
      (fun σ => |(1 / (n : ℝ)) * V w σ
        - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P|) ∂P := by
  classical
  have hq := continuous_integral_gibbs_average_path (α := α) n hU hV hVi
  have hdom : Integrable (fun w => (1 / (n : ℝ)) * ‖V w‖
      + (1 / (n : ℝ)) * ∫ w', ‖V w'‖ ∂P) P :=
    (hVi.const_mul (1 / (n : ℝ))).add (integrable_const _)
  refine continuous_of_dominated
    (fun x => (measurable_totalFluct_path n hU hV x).aestronglyMeasurable)
    (fun x => Filter.Eventually.of_forall fun w => ?_) hdom
    (Filter.Eventually.of_forall fun w => ?_)
  · rw [Real.norm_eq_abs,
      abs_of_nonneg (gibbs_average_abs_smul_sub_const_nonneg (α := α) n (U w + x • V w) (V w) _)]
    refine (gibbs_average_abs_smul_sub_const_le_norm (α := α) n (U w + x • V w) (V w) _).trans ?_
    exact add_le_add le_rfl (abs_integral_gibbs_average_path_le n hU hV hVi x)
  · have hpath : Continuous fun x : ℝ => U w + x • V w := by fun_prop
    have hp : ∀ σ : α, Continuous fun x : ℝ => gibbs_pmf (α := α) (U w + x • V w) σ := fun σ =>
      ((contDiff_gibbs_pmf (α := α) σ).continuous).comp hpath
    simp only [gibbs_average]
    exact continuous_finsetSum _ fun σ _ => (hp σ).mul ((continuous_const.sub hq).abs)

/-- **The total fluctuation of the energy splits into its Gibbs part and its disorder part.**
Talagrand, Vol. II, §12.1: the passage from Theorem 12.1.1 to the two integrals (12.4) and (12.5).
Bounding the two summands by `intervalIntegral_absFluct_le` and
`intervalIntegral_integral_abs_meanEnergy_sub_le` gives Theorem 12.1.1. -/
theorem intervalIntegral_integral_totalFluct_le (n : ℕ) (hU : Measurable U) (hV : Measurable V)
    (hVi : Integrable (fun w => ‖V w‖) P) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, ∫ w, gibbs_average (α := α) (U w + x • V w)
        (fun σ => |(1 / (n : ℝ)) * V w σ
          - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P|) ∂P)
      ≤ (∫ x in a..b, ∫ w, (1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w)
            (fun σ => |V w σ - gibbs_average (α := α) (U w + x • V w) (V w)|) ∂P)
        + ∫ x in a..b, ∫ w, |(1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w)
            - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P| ∂P := by
  classical
  have hcont0 := continuous_integral_totalFluct (α := α) n hU hV hVi
  have hcont1 := continuous_integral_absFluct_path (α := α) n hU hV hVi
  have hcont2 := continuous_integral_abs_meanEnergy_sub (α := α) n hU hV hVi
  have hI1 : ∀ x : ℝ, Integrable (fun w => (1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w)
      (fun σ => |V w σ - gibbs_average (α := α) (U w + x • V w) (V w)|)) P := by
    intro x
    refine Integrable.mono' ((hVi.const_mul 2).const_mul (1 / (n : ℝ)))
      (measurable_absFluct_path n hU hV x).aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (n : ℝ)),
      abs_of_nonneg (gibbs_average_abs_sub_nonneg (α := α) (U w + x • V w) (V w) _)]
    exact mul_le_mul_of_nonneg_left
      (gibbs_average_abs_sub_gibbs_average_le (α := α) (U w + x • V w) (V w)) (by positivity)
  have hI2 : ∀ x : ℝ, Integrable (fun w =>
      |(1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w)
        - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P|) P := by
    intro x
    have hdom : Integrable (fun w => (1 / (n : ℝ)) * ‖V w‖
        + (1 / (n : ℝ)) * ∫ w', ‖V w'‖ ∂P) P :=
      (hVi.const_mul (1 / (n : ℝ))).add (integrable_const _)
    have hmeas : Measurable fun w =>
        |(1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w)
          - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P| := by
      have hd : Measurable fun w => (1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w)
          - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P :=
        ((measurable_gibbs_average_path hU hV x).const_mul _).sub measurable_const
      fun_prop
    refine Integrable.mono' hdom hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    refine (abs_sub _ _).trans (add_le_add ?_ (abs_integral_gibbs_average_path_le n hU hV hVi x))
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (n : ℝ))]
    exact mul_le_mul_of_nonneg_left (abs_gibbs_average_le (α := α) _ _) (by positivity)
  -- Split the `w`-integral pointwise in `x`.
  have hstep : ∀ x : ℝ, (∫ w, gibbs_average (α := α) (U w + x • V w)
        (fun σ => |(1 / (n : ℝ)) * V w σ
          - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P|) ∂P)
      ≤ (∫ w, (1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w)
            (fun σ => |V w σ - gibbs_average (α := α) (U w + x • V w) (V w)|) ∂P)
        + ∫ w, |(1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w)
            - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P| ∂P := by
    intro x
    have hsum : Integrable (fun w =>
        (1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w)
            (fun σ => |V w σ - gibbs_average (α := α) (U w + x • V w) (V w)|)
          + |(1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w)
            - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P|) P :=
      (hI1 x).add (hI2 x)
    have hmono := integral_mono (integrable_totalFluct_path n hU hV hVi x) hsum
      (fun w => gibbs_average_abs_smul_sub_const_le (α := α) n (U w + x • V w) (V w) _)
    rwa [integral_add (hI1 x) (hI2 x)] at hmono
  -- Integrate the split in `x`.
  rw [← intervalIntegral.integral_add (hcont1.intervalIntegrable a b)
    (hcont2.intervalIntegrable a b)]
  refine intervalIntegral.integral_mono_on hab (hcont0.intervalIntegrable a b)
    ((hcont1.add hcont2).intervalIntegrable a b) fun x _ => hstep x

end

end FiniteGibbs

end SpinGlass
