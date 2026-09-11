/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.FiniteGibbs.WeightedInterpolation

/-!
# From a bound on the Guerra trace to the free-energy comparison

Guerra's interpolation schemes (Talagrand Vol. II, Lemma 14.4.1 in one dimension, Lemma 14.6.1 for
coupled copies) all end the same way: the weighted Guerra trace of the two kernels is bounded,
pointwise in the Hamiltonian, by an expression of the form

`(1/2) c₀ + (1/2) ∑_{x,y} g_x g_y θ(x, y)`   (`treeBoundIntegrand`),

a constant plus the Gibbs average of a bounded function of a pair of replicas, and the comparison
bound `wFreeEnergy_sub_le` then gives `𝔼 F_w(U + c) - 𝔼 F_w(V + c) ≤ ∫₀¹ b(t) dt` with `b(t)` the
average of that expression along the interpolation. This file does that step once and for all
(`wFreeEnergy_sub_le_of_le_treeBoundIntegrand`): the integrability along the path and the
continuity of `b` in `t` (dominated convergence, `continuous_guerraBoundFn`) are discharged from
the boundedness of the Gibbs weights alone.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable {A : Type*} [Fintype A]

/-! ### Continuity of the weighted Gibbs weights -/

lemma continuous_wZ (wt : A → ℝ) : Continuous fun H : FiniteGibbs.EnergySpace A => wZ wt H := by
  unfold wZ
  refine continuous_finsetSum _ fun x _ => continuous_const.mul (Real.continuous_exp.comp ?_)
  exact ((continuous_apply x).comp (PiLp.continuous_ofLp 2 (fun _ : A => ℝ))).neg

lemma continuous_wGibbs (wt : A → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0) (x : A) :
    Continuous fun H : FiniteGibbs.EnergySpace A => wGibbs wt H x := by
  unfold wGibbs
  refine (continuous_const.mul (Real.continuous_exp.comp ?_)).div (continuous_wZ wt)
    fun H => (wZ_pos wt hwt hne H).ne'
  exact ((continuous_apply x).comp (PiLp.continuous_ofLp 2 (fun _ : A => ℝ))).neg

lemma continuous_wGuerraTrace (wt : A → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (K₁ K₂ : A → A → ℝ) (n : ℕ) :
    Continuous fun H : FiniteGibbs.EnergySpace A => wGuerraTrace wt K₁ K₂ n H := by
  unfold wGuerraTrace
  refine continuous_const.mul ((continuous_finsetSum _ fun x _ =>
    continuous_const.mul (continuous_wGibbs wt hwt hne x)).sub
    (continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun y _ =>
      continuous_const.mul ((continuous_wGibbs wt hwt hne x).mul (continuous_wGibbs wt hwt hne y))))

/-- The integrand of the bound (14.79):
`(1/2)(ξ(1) - ξ'(q̄)) + (1/2) ∑_{x,y} g_x g_y θ(q_{x,y})`. -/
def treeBoundIntegrand (wt : A → ℝ) (c₀ : ℝ) (θq : A → A → ℝ) (H : FiniteGibbs.EnergySpace A) :
    ℝ :=
  (1 / 2) * c₀ + (1 / 2) * ∑ x, ∑ y, wGibbs wt H x * wGibbs wt H y * θq x y

lemma continuous_treeBoundIntegrand (wt : A → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (c₀ : ℝ) (θq : A → A → ℝ) :
    Continuous fun H : FiniteGibbs.EnergySpace A => treeBoundIntegrand wt c₀ θq H := by
  unfold treeBoundIntegrand
  refine continuous_const.add (continuous_const.mul (continuous_finsetSum _ fun x _ =>
    continuous_finsetSum _ fun y _ =>
      ((continuous_wGibbs wt hwt hne x).mul (continuous_wGibbs wt hwt hne y)).mul continuous_const))

lemma abs_treeBoundIntegrand_le (wt : A → ℝ) (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0)
    (c₀ : ℝ) (θq : A → A → ℝ) (H : FiniteGibbs.EnergySpace A) :
    |treeBoundIntegrand wt c₀ θq H| ≤ (1 / 2) * |c₀| + (1 / 2) * ∑ x, ∑ y, |θq x y| := by
  unfold treeBoundIntegrand
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  · rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    rw [abs_mul]
    refine (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)).trans (one_mul _).le
    rw [abs_of_nonneg (mul_nonneg (wGibbs_nonneg wt hwt hne H x) (wGibbs_nonneg wt hwt hne H y))]
    exact mul_le_one₀ (wGibbs_le_one wt hwt hne H x) (wGibbs_nonneg wt hwt hne H y)
      (wGibbs_le_one wt hwt hne H y)

/-! ### The integrated bound -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {K₁ K₂ : A → A → ℝ}

/-- The bound `b(t) = ∫ [(1/2) c₀ + (1/2) ⟨θ⟩_{H_t}] dP` along the interpolation `H_t = Z_t + c`. -/
def guerraBoundFn (G₁ : GaussianField (α := A) P K₁) (G₂ : GaussianField (α := A) P K₂)
    (wt : A → ℝ) (c₀ : ℝ) (θq : A → A → ℝ) (c : FiniteGibbs.EnergySpace A) (t : ℝ) : ℝ :=
  ∫ p : PairSpace A, treeBoundIntegrand wt c₀ θq (gaussianInterp t p + c) ∂pairLaw G₁ G₂

/-- The integrated bound is continuous in `t`, by dominated convergence: the integrand is
continuous in `t` and bounded by a constant. -/
lemma continuous_guerraBoundFn (G₁ : GaussianField (α := A) P K₁)
    (G₂ : GaussianField (α := A) P K₂) (hindep : G₁.U ⟂ᵢ[P] G₂.U) (wt : A → ℝ)
    (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0) (c₀ : ℝ) (θq : A → A → ℝ)
    (c : FiniteGibbs.EnergySpace A) :
    Continuous (guerraBoundFn G₁ G₂ wt c₀ θq c) := by
  have := isGaussian_pairLaw G₁ G₂ hindep
  unfold guerraBoundFn
  refine continuous_of_dominated (fun t => ?_)
    (bound := fun _ => (1 / 2) * |c₀| + (1 / 2) * ∑ x, ∑ y, |θq x y|)
    (fun t => Filter.Eventually.of_forall fun p => ?_) (integrable_const _)
    (Filter.Eventually.of_forall fun p => ?_)
  · exact ((continuous_treeBoundIntegrand wt hwt hne c₀ θq).comp
      ((gaussianInterp t).continuous.add continuous_const)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact abs_treeBoundIntegrand_le wt hwt hne c₀ θq _
  · exact (continuous_treeBoundIntegrand wt hwt hne c₀ θq).comp
      ((continuous_gaussianInterp_apply p).add continuous_const)

/-- **From a pointwise bound on the Guerra trace to the free-energy comparison.** If for every
Hamiltonian `wGuerraTrace wt K₁ K₂ n H ≤ (1/2) c₀ + (1/2) ⟨θ⟩_H`, then

`𝔼 F_w(U + c) - 𝔼 F_w(V + c) ≤ ∫₀¹ 𝔼 [(1/2) c₀ + (1/2) ⟨θ⟩_{H_t}] dt`.

This is the common final step of Guerra's one-dimensional scheme (Lemma 14.4.1) and of its
two-dimensional version for coupled copies (Lemma 14.6.1). -/
theorem wFreeEnergy_sub_le_of_le_treeBoundIntegrand (G₁ : GaussianField (α := A) P K₁)
    (G₂ : GaussianField (α := A) P K₂) (hindep : G₁.U ⟂ᵢ[P] G₂.U) (wt : A → ℝ)
    (hwt : ∀ x, 0 ≤ wt x) (hne : ∃ x, wt x ≠ 0) (n : ℕ) (c : FiniteGibbs.EnergySpace A) (c₀ : ℝ)
    (θq : A → A → ℝ)
    (hle : ∀ H : FiniteGibbs.EnergySpace A,
      wGuerraTrace wt K₁ K₂ n H ≤ treeBoundIntegrand wt c₀ θq H) :
    (∫ ω, wFreeEnergy wt n (G₁.U ω + c) ∂P) - (∫ ω, wFreeEnergy wt n (G₂.U ω + c) ∂P)
      ≤ ∫ t in (0 : ℝ)..1, guerraBoundFn G₁ G₂ wt c₀ θq c t := by
  have := isGaussian_pairLaw G₁ G₂ hindep
  have hcontb := continuous_guerraBoundFn G₁ G₂ hindep wt hwt hne c₀ θq c
  refine wFreeEnergy_sub_le G₁ G₂ hindep wt hwt hne c n (fun t _ => ?_)
    (hcontb.intervalIntegrable 0 1)
  have hcontT := continuous_wGuerraTrace wt hwt hne K₁ K₂ n
  have hint1 : Integrable (fun p : PairSpace A =>
      wGuerraTrace wt K₁ K₂ n (gaussianInterp t p + c)) (pairLaw G₁ G₂) := by
    refine Integrable.of_bound ((hcontT.comp
      ((gaussianInterp t).continuous.add continuous_const)).aestronglyMeasurable)
      ((1 / (2 * (n : ℝ))) * ((∑ x, |K₁ x x - K₂ x x|) + ∑ x, ∑ y, |K₁ x y - K₂ x y|))
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    exact abs_wGuerraTrace_le wt hwt hne _ _ n _
  have hint2 : Integrable (fun p : PairSpace A =>
      treeBoundIntegrand wt c₀ θq (gaussianInterp t p + c)) (pairLaw G₁ G₂) := by
    refine Integrable.of_bound (((continuous_treeBoundIntegrand wt hwt hne c₀ θq).comp
      ((gaussianInterp t).continuous.add continuous_const)).aestronglyMeasurable)
      ((1 / 2) * |c₀| + (1 / 2) * ∑ x, ∑ y, |θq x y|) (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    exact abs_treeBoundIntegrand_le wt hwt hne c₀ θq _
  exact integral_mono hint1 hint2 fun p => hle _

end

end SpinGlass
