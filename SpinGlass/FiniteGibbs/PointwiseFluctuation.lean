/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.FiniteGibbs.DerivSelfAveraging
import SpinGlass.FiniteGibbs.FluctuationIntegral
import SpinGlass.FiniteGibbs.EnergyFluctuation
import Common.Mathlib.Analysis.Convex.GriffithsMean
import Common.Mathlib.Analysis.Convex.GriffithsLemma

/-!
# Energy self-averaging at a fixed parameter

Talagrand, *Mean Field Models for Spin Glasses*, Vol. II, Theorem 12.1.3 (Panchenko), with its
Lemmas 12.1.7–12.1.9, in the general finite-Gibbs setting: a Hamiltonian `U + x • V` on a finite
configuration space, with `U`, `V` random and integrable.

Theorem 12.1.1 controls the energy fluctuation `𝔼⟨|V/n - 𝔼⟨V/n⟩|⟩` only after integration over a
window of the parameter `x`. Theorem 12.1.3 controls it at a *fixed* `x`, as soon as the mean free
energies `p_N` converge pointwise to a limit `𝒫` differentiable at `x`. The mechanism:

* the **Gibbs part** `𝔼⟨|V - ⟨V⟩|⟩/n` is dominated by the two-replica quantity
  `ψ(x) = 𝔼⟨|V(σ¹) - V(σ²)|⟩/n`, whose square is `O(p''(x)/n)` (Lemma 12.1.7, (12.17)) and whose
  derivative is `O(p''(x))` (Lemma 12.1.7, (12.18)): `ψ ∓ 4p'` are monotone, so `ψ(x)` is at most
  `ψ(y) + 4 D(x,b)` for every `y` in the window, where `D(x,b) = p'(x+b) - p'(x-b)`; averaging in
  `y` and using `∫_{x-b}^{x+b} p'' = D(x,b)` gives Lemma 12.1.8;
* the **disorder part** `𝔼|⟨V⟩/n - 𝔼⟨V⟩/n|` is the fluctuation of the derivative of the sample
  free energy, controlled by Griffiths' lemma in mean (`ConvexOn.integral_abs_deriv_sub_le`);
* `D(x,b)` is small for `N` large and `b` small by convexity and the differentiability of `𝒫`
  (Lemma 12.1.9, `ConvexOn.exists_eventually_deriv_sub_deriv_le`).

## Main statements

- `SpinGlass.FiniteGibbs.pairAverage`, `pairDeriv`: the two-replica bracket `⟨|V(σ¹) - V(σ²)|⟩`
  and its derivative along the path.
- `SpinGlass.FiniteGibbs.hasDerivAt_pairFluct`, `abs_integral_pairDeriv_le`: Lemma 12.1.7 (12.18).
- `SpinGlass.FiniteGibbs.pairFluct_le`: Lemma 12.1.7 (12.17), in the form
  `ψ(y) ≤ η/(2n) + (2/η) p''(y)`.
- `SpinGlass.FiniteGibbs.pairFluct_le_window`: **Lemma 12.1.8**.
- `SpinGlass.FiniteGibbs.integral_abs_gibbs_average_sub_le_window`: the disorder part.
- `SpinGlass.FiniteGibbs.integral_totalFluct_le_window`: **Theorem 12.1.3 at finite volume**, the
  quantitative bound behind Panchenko's theorem.
- `SpinGlass.FiniteGibbs.tendsto_zero_of_le_window`: the passage to the limit, first `N → ∞`, then
  `b → 0`.
-/

open MeasureTheory Real BigOperators Filter Topology Set

namespace SpinGlass

namespace FiniteGibbs

noncomputable section

variable {α : Type*} [Fintype α] [Nonempty α]

/-! ### The two-replica bracket and its derivative -/

/-- The two-replica Gibbs bracket `⟨|v(σ¹) - v(σ²)|⟩` of the direction `v`. -/
def pairAverage (H v : EnergySpace α) : ℝ :=
  gibbs_average_n_det (α := α) (n := 2) H (fun σs => |v (σs 0) - v (σs 1)|)

/-- The derivative of `y ↦ ⟨|v(σ¹) - v(σ²)|⟩_{H + y v}`: the Gibbs covariance of `|v¹ - v²|` with
`2⟨v⟩ - v¹ - v²`. -/
def pairDeriv (H v : EnergySpace α) : ℝ :=
  ∑ σ : α, ∑ τ : α, gibbs_pmf (α := α) H σ * gibbs_pmf (α := α) H τ * |v σ - v τ|
    * ((gibbs_average (α := α) H v - v σ) + (gibbs_average (α := α) H v - v τ))

omit [Nonempty α] in
lemma pairAverage_eq_sum (H v : EnergySpace α) :
    pairAverage H v
      = ∑ σ : α, ∑ τ : α, gibbs_pmf (α := α) H σ * gibbs_pmf (α := α) H τ * |v σ - v τ| :=
  gibbs_average_two (α := α) H (fun σ τ => |v σ - v τ|)

lemma pairAverage_nonneg (H v : EnergySpace α) : 0 ≤ pairAverage H v := by
  rw [pairAverage_eq_sum]
  exact Finset.sum_nonneg fun σ _ => Finset.sum_nonneg fun τ _ =>
    mul_nonneg (mul_nonneg (gibbs_pmf_nonneg (α := α) H σ) (gibbs_pmf_nonneg (α := α) H τ))
      (abs_nonneg _)

lemma pairAverage_le_two_norm (H v : EnergySpace α) : pairAverage H v ≤ 2 * ‖v‖ := by
  rw [pairAverage_eq_sum]
  have hpt : ∀ σ τ : α, |v σ - v τ| ≤ 2 * ‖v‖ := fun σ τ => by
    have h1 : |v σ| ≤ ‖v‖ := abs_apply_le_norm (α := α) v σ
    have h2 : |v τ| ≤ ‖v‖ := abs_apply_le_norm (α := α) v τ
    calc |v σ - v τ| ≤ |v σ| + |v τ| := abs_sub _ _
      _ ≤ 2 * ‖v‖ := by linarith
  calc ∑ σ : α, ∑ τ : α, gibbs_pmf (α := α) H σ * gibbs_pmf (α := α) H τ * |v σ - v τ|
      ≤ ∑ σ : α, ∑ τ : α, gibbs_pmf (α := α) H σ * gibbs_pmf (α := α) H τ * (2 * ‖v‖) := by
        refine Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun τ _ => ?_
        exact mul_le_mul_of_nonneg_left (hpt σ τ)
          (mul_nonneg (gibbs_pmf_nonneg (α := α) H σ) (gibbs_pmf_nonneg (α := α) H τ))
    _ = 2 * ‖v‖ := by
        simp only [← Finset.sum_mul, ← Finset.mul_sum, sum_gibbs_pmf, one_mul, mul_one]

/-- The one-replica bracket of `|v - ⟨v⟩|` is dominated by the two-replica bracket of
`|v(σ¹) - v(σ²)|` (Jensen over the second replica). -/
lemma gibbs_average_abs_sub_le_pairAverage (H v : EnergySpace α) :
    gibbs_average (α := α) H (fun σ => |v σ - gibbs_average (α := α) H v|)
      ≤ pairAverage H v := by
  rw [pairAverage_eq_sum, gibbs_average]
  refine Finset.sum_le_sum fun σ _ => ?_
  have hp := gibbs_pmf_nonneg (α := α) H σ
  have hsub : v σ - gibbs_average (α := α) H v
      = ∑ τ : α, gibbs_pmf (α := α) H τ * (v σ - v τ) := by
    simp only [gibbs_average, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_gibbs_pmf,
      one_mul]
  calc gibbs_pmf (α := α) H σ * |v σ - gibbs_average (α := α) H v|
      = gibbs_pmf (α := α) H σ * |∑ τ : α, gibbs_pmf (α := α) H τ * (v σ - v τ)| := by rw [hsub]
    _ ≤ gibbs_pmf (α := α) H σ * ∑ τ : α, gibbs_pmf (α := α) H τ * |v σ - v τ| := by
        refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans ?_) hp
        refine Finset.sum_le_sum fun τ _ => ?_
        rw [abs_mul, abs_of_nonneg (gibbs_pmf_nonneg (α := α) H τ)]
    _ = ∑ τ : α, gibbs_pmf (α := α) H σ * gibbs_pmf (α := α) H τ * |v σ - v τ| := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun τ _ => by ring

/-- The two-replica bracket of `2(v¹ - ⟨v⟩)² + 2(v² - ⟨v⟩)²` is four times the Gibbs variance. -/
lemma sum_sum_gibbs_pmf_mul_two_sq_add (H v : EnergySpace α) :
    ∑ σ : α, ∑ τ : α, gibbs_pmf (α := α) H σ * gibbs_pmf (α := α) H τ
        * (2 * (v σ - gibbs_average (α := α) H v) ^ 2
          + 2 * (v τ - gibbs_average (α := α) H v) ^ 2)
      = 4 * ∑ σ : α, gibbs_pmf (α := α) H σ * (v σ - gibbs_average (α := α) H v) ^ 2 := by
  set m := gibbs_average (α := α) H v
  set S := ∑ σ : α, gibbs_pmf (α := α) H σ * (v σ - m) ^ 2 with hS
  have hinner : ∀ σ : α, ∑ τ : α, gibbs_pmf (α := α) H σ * gibbs_pmf (α := α) H τ
      * (2 * (v σ - m) ^ 2 + 2 * (v τ - m) ^ 2)
      = 2 * (gibbs_pmf (α := α) H σ * (v σ - m) ^ 2) + 2 * gibbs_pmf (α := α) H σ * S := by
    intro σ
    have hpt : ∀ τ : α, gibbs_pmf (α := α) H σ * gibbs_pmf (α := α) H τ
        * (2 * (v σ - m) ^ 2 + 2 * (v τ - m) ^ 2)
        = (2 * (gibbs_pmf (α := α) H σ * (v σ - m) ^ 2)) * gibbs_pmf (α := α) H τ
          + (2 * gibbs_pmf (α := α) H σ) * (gibbs_pmf (α := α) H τ * (v τ - m) ^ 2) :=
      fun τ => by ring
    rw [Finset.sum_congr rfl fun τ _ => hpt τ, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, sum_gibbs_pmf, mul_one]
  rw [Finset.sum_congr rfl fun σ _ => hinner σ, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, ← Finset.mul_sum, sum_gibbs_pmf]
  ring

/-- **Lemma 12.1.7, (12.18), at the Gibbs level**: `|∂_y ⟨|v¹ - v²|⟩| ≤ 4 ⟨(v - ⟨v⟩)²⟩`. -/
lemma abs_pairDeriv_le (H v : EnergySpace α) :
    |pairDeriv H v|
      ≤ 4 * ∑ σ : α, gibbs_pmf (α := α) H σ * (v σ - gibbs_average (α := α) H v) ^ 2 := by
  set m := gibbs_average (α := α) H v
  rw [← sum_sum_gibbs_pmf_mul_two_sq_add]
  refine (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum fun σ _ => Finset.abs_sum_le_sum_abs _ _).trans ?_)
  refine Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun τ _ => ?_
  have hp := mul_nonneg (gibbs_pmf_nonneg (α := α) H σ) (gibbs_pmf_nonneg (α := α) H τ)
  rw [mul_assoc, abs_mul, abs_of_nonneg hp]
  refine mul_le_mul_of_nonneg_left ?_ hp
  rw [abs_mul, abs_abs]
  have h1 : |v σ - v τ| * |(m - v σ) + (m - v τ)|
      ≤ ((v σ - v τ) ^ 2 + ((m - v σ) + (m - v τ)) ^ 2) / 2 := by
    nlinarith [sq_nonneg (|v σ - v τ| - |(m - v σ) + (m - v τ)|), sq_abs (v σ - v τ),
      sq_abs ((m - v σ) + (m - v τ))]
  nlinarith [h1, sq_nonneg (v σ - m), sq_nonneg (v τ - m)]

/-- **Lemma 12.1.7, (12.17), at the Gibbs level**, by the elementary inequality
`|a| ≤ η/2 + a²/(2η)`: `⟨|v¹ - v²|⟩ ≤ η/2 + (2/η) ⟨(v - ⟨v⟩)²⟩`. -/
lemma pairAverage_le (H v : EnergySpace α) {η : ℝ} (hη : 0 < η) :
    pairAverage H v
      ≤ η / 2 + (2 / η) * ∑ σ : α, gibbs_pmf (α := α) H σ
          * (v σ - gibbs_average (α := α) H v) ^ 2 := by
  set m := gibbs_average (α := α) H v
  have hsq : ∑ σ : α, ∑ τ : α, gibbs_pmf (α := α) H σ * gibbs_pmf (α := α) H τ * (v σ - v τ) ^ 2
      ≤ 4 * ∑ σ : α, gibbs_pmf (α := α) H σ * (v σ - m) ^ 2 := by
    rw [← sum_sum_gibbs_pmf_mul_two_sq_add]
    refine Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun τ _ => ?_
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg (gibbs_pmf_nonneg (α := α) H σ) (gibbs_pmf_nonneg (α := α) H τ))
    nlinarith [sq_nonneg ((v σ - m) + (v τ - m))]
  have hpt : ∀ σ τ : α, |v σ - v τ| ≤ η / 2 + (v σ - v τ) ^ 2 / (2 * η) := by
    intro σ τ
    rw [div_add_div _ _ (two_ne_zero) (by positivity), le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (η - |v σ - v τ|), sq_abs (v σ - v τ), abs_nonneg (v σ - v τ)]
  calc pairAverage H v
      = ∑ σ : α, ∑ τ : α, gibbs_pmf (α := α) H σ * gibbs_pmf (α := α) H τ * |v σ - v τ| :=
        pairAverage_eq_sum H v
    _ ≤ ∑ σ : α, ∑ τ : α, gibbs_pmf (α := α) H σ * gibbs_pmf (α := α) H τ
          * (η / 2 + (v σ - v τ) ^ 2 / (2 * η)) := by
        refine Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun τ _ => ?_
        exact mul_le_mul_of_nonneg_left (hpt σ τ)
          (mul_nonneg (gibbs_pmf_nonneg (α := α) H σ) (gibbs_pmf_nonneg (α := α) H τ))
    _ = η / 2 + (1 / (2 * η)) * ∑ σ : α, ∑ τ : α,
          gibbs_pmf (α := α) H σ * gibbs_pmf (α := α) H τ * (v σ - v τ) ^ 2 := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        · simp only [← Finset.sum_mul, ← Finset.mul_sum, sum_gibbs_pmf, one_mul, mul_one]
        · refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
          ring
    _ ≤ η / 2 + (1 / (2 * η)) * (4 * ∑ σ : α, gibbs_pmf (α := α) H σ * (v σ - m) ^ 2) := by
        gcongr
    _ = η / 2 + (2 / η) * ∑ σ : α, gibbs_pmf (α := α) H σ * (v σ - m) ^ 2 := by
        field_simp
        ring

/-- The Gibbs variance is at most `4‖v‖²`. -/
lemma sum_gibbs_pmf_mul_sq_sub_average_le (H v : EnergySpace α) :
    ∑ σ : α, gibbs_pmf (α := α) H σ * (v σ - gibbs_average (α := α) H v) ^ 2 ≤ 4 * ‖v‖ ^ 2 := by
  have hpt : ∀ σ : α, (v σ - gibbs_average (α := α) H v) ^ 2 ≤ 4 * ‖v‖ ^ 2 := by
    intro σ
    have h := abs_sum_gibbs_pmf_mul_apply_sub_apply_le_two_norm (α := α) H v σ
    change |gibbs_average (α := α) H v - v σ| ≤ 2 * ‖v‖ at h
    rw [abs_sub_comm] at h
    have h0 : 0 ≤ |v σ - gibbs_average (α := α) H v| := abs_nonneg _
    calc (v σ - gibbs_average (α := α) H v) ^ 2
        = |v σ - gibbs_average (α := α) H v| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * ‖v‖) ^ 2 := by gcongr
      _ = 4 * ‖v‖ ^ 2 := by ring
  calc ∑ σ : α, gibbs_pmf (α := α) H σ * (v σ - gibbs_average (α := α) H v) ^ 2
      ≤ ∑ σ : α, gibbs_pmf (α := α) H σ * (4 * ‖v‖ ^ 2) :=
        Finset.sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_left (hpt σ) (gibbs_pmf_nonneg (α := α) H σ)
    _ = 4 * ‖v‖ ^ 2 := by rw [← Finset.sum_mul, sum_gibbs_pmf, one_mul]

/-- The derivative of the two-replica bracket along the affine path `y ↦ H + y • v`. -/
theorem hasDerivAt_pairAverage (H v : EnergySpace α) (x : ℝ) :
    HasDerivAt (fun y : ℝ => pairAverage (H + y • v) v) (pairDeriv (H + x • v) v) x := by
  classical
  have hpath : HasDerivAt (fun y : ℝ => H + y • v) v x := by
    simpa using ((hasDerivAt_id x).smul_const v).const_add H
  have hd := (differentiableAt_gibbs_average_n_det (α := α) 2 (H + x • v)
    (fun σs => |v (σs 0) - v (σs 1)|)).hasFDerivAt.comp_hasDerivAt x hpath
  refine hd.congr_deriv ?_
  rw [fderiv_gibbs_average_n_det_apply, pairDeriv,
    ← Equiv.sum_comp (finTwoArrowEquiv α).symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
  simp only [finTwoArrowEquiv_symm_apply, Fin.prod_univ_two, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, gibbs_average]
  ring

/-! ### Measurability along a random path -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {U V : Ω → EnergySpace α}

lemma measurable_pairAverage_path (hU : Measurable U) (hV : Measurable V) (x : ℝ) :
    Measurable fun w => pairAverage (U w + x • V w) (V w) := by
  classical
  have hpath : Measurable fun w => U w + x • V w := by fun_prop
  have hpmf : ∀ σ : α, Measurable fun w => gibbs_pmf (α := α) (U w + x • V w) σ := fun σ =>
    ((contDiff_gibbs_pmf (α := α) σ).continuous.measurable).comp hpath
  have hev : ∀ σ : α, Measurable fun w => (V w) σ := fun σ =>
    (measurable_eval (α := α) σ).comp hV
  simp only [pairAverage_eq_sum]
  refine Finset.measurable_sum _ fun σ _ => Finset.measurable_sum _ fun τ _ => ?_
  exact ((hpmf σ).mul (hpmf τ)).mul (continuous_abs.measurable.comp ((hev σ).sub (hev τ)))

lemma measurable_pairDeriv_path (hU : Measurable U) (hV : Measurable V) (x : ℝ) :
    Measurable fun w => pairDeriv (U w + x • V w) (V w) := by
  classical
  have hpath : Measurable fun w => U w + x • V w := by fun_prop
  have hpmf : ∀ σ : α, Measurable fun w => gibbs_pmf (α := α) (U w + x • V w) σ := fun σ =>
    ((contDiff_gibbs_pmf (α := α) σ).continuous.measurable).comp hpath
  have hev : ∀ σ : α, Measurable fun w => (V w) σ := fun σ =>
    (measurable_eval (α := α) σ).comp hV
  have hav := measurable_gibbs_average_path (α := α) hU hV x
  simp only [pairDeriv]
  refine Finset.measurable_sum _ fun σ _ => Finset.measurable_sum _ fun τ _ => ?_
  exact (((hpmf σ).mul (hpmf τ)).mul (continuous_abs.measurable.comp ((hev σ).sub (hev τ)))).mul
    ((hav.sub (hev σ)).add (hav.sub (hev τ)))

omit [IsProbabilityMeasure P] in
lemma integrable_pairAverage_path (hU : Measurable U) (hV : Measurable V)
    (hVi : Integrable (fun w => ‖V w‖) P) (n : ℕ) (x : ℝ) :
    Integrable (fun w => (1 / (n : ℝ)) * pairAverage (U w + x • V w) (V w)) P := by
  refine Integrable.mono' ((hVi.const_mul 2).const_mul (1 / (n : ℝ)))
    ((measurable_pairAverage_path hU hV x).const_mul _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ)),
    abs_of_nonneg (pairAverage_nonneg _ _)]
  exact mul_le_mul_of_nonneg_left (pairAverage_le_two_norm _ _) (by positivity)

/-! ### Lemma 12.1.7: the derivative of `ψ` -/

omit [IsProbabilityMeasure P] in
/-- **The two-replica fluctuation `ψ` is differentiable in the parameter**, with derivative
`𝔼[pairDeriv]/n`; differentiation under the integral sign, dominated by `16‖V‖²/n`. -/
theorem hasDerivAt_pairFluct (hU : Measurable U) (hV : Measurable V)
    (hVi : Integrable (fun w => ‖V w‖) P) (hVi2 : Integrable (fun w => ‖V w‖ ^ 2) P)
    (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ w, (1 / (n : ℝ)) * pairAverage (U w + y • V w) (V w) ∂P)
      (∫ w, (1 / (n : ℝ)) * pairDeriv (U w + x • V w) (V w) ∂P) x := by
  classical
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y w => (1 / (n : ℝ)) * pairAverage (U w + y • V w) (V w))
    (F' := fun y w => (1 / (n : ℝ)) * pairDeriv (U w + y • V w) (V w))
    (bound := fun w => (1 / (n : ℝ)) * (16 * ‖V w‖ ^ 2))
    (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun y =>
      ((measurable_pairAverage_path hU hV y).const_mul _).aestronglyMeasurable)
    (integrable_pairAverage_path hU hV hVi n x)
    ((measurable_pairDeriv_path hU hV x).const_mul _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w y _ => ?_) ((hVi2.const_mul 16).const_mul _)
    (Filter.Eventually.of_forall fun w y _ => ?_)).2
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc |pairDeriv (U w + y • V w) (V w)|
        ≤ 4 * ∑ σ : α, gibbs_pmf (α := α) (U w + y • V w) σ
            * ((V w) σ - gibbs_average (α := α) (U w + y • V w) (V w)) ^ 2 :=
          abs_pairDeriv_le _ _
      _ ≤ 4 * (4 * ‖V w‖ ^ 2) := by
          gcongr
          exact sum_gibbs_pmf_mul_sq_sub_average_le _ _
      _ = 16 * ‖V w‖ ^ 2 := by ring
  · exact (hasDerivAt_pairAverage (U w) (V w) y).const_mul _

omit [IsProbabilityMeasure P] in
/-- **Lemma 12.1.7, (12.18)**: `|ψ'(x)| ≤ 4 p''(x)`, where `p''(x) = 𝔼⟨(V - ⟨V⟩)²⟩/n` is the
mean Gibbs fluctuation. -/
theorem abs_integral_pairDeriv_le (hU : Measurable U) (hV : Measurable V)
    (hVi2 : Integrable (fun w => ‖V w‖ ^ 2) P) (n : ℕ) (x : ℝ) :
    |∫ w, (1 / (n : ℝ)) * pairDeriv (U w + x • V w) (V w) ∂P|
      ≤ 4 * ∫ w, hessian_free_energy (α := α) n (U w + x • V w) (V w) (V w) ∂P := by
  have hpt : ∀ w, |(1 / (n : ℝ)) * pairDeriv (U w + x • V w) (V w)|
      ≤ 4 * hessian_free_energy (α := α) n (U w + x • V w) (V w) (V w) := by
    intro w
    rw [hessian_free_energy_self_eq_variance, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))]
    have := abs_pairDeriv_le (U w + x • V w) (V w)
    have h0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    calc (1 / (n : ℝ)) * |pairDeriv (U w + x • V w) (V w)|
        ≤ (1 / (n : ℝ)) * (4 * ∑ σ : α, gibbs_pmf (α := α) (U w + x • V w) σ
            * ((V w) σ - gibbs_average (α := α) (U w + x • V w) (V w)) ^ 2) :=
          mul_le_mul_of_nonneg_left this h0
      _ = 4 * ((1 / (n : ℝ)) * ∑ σ : α, gibbs_pmf (α := α) (U w + x • V w) σ
            * ((V w) σ - gibbs_average (α := α) (U w + x • V w) (V w)) ^ 2) := by ring
  have hI := integrable_hessian_path (α := α) hU hV hVi2 n x
  calc |∫ w, (1 / (n : ℝ)) * pairDeriv (U w + x • V w) (V w) ∂P|
      ≤ ∫ w, |(1 / (n : ℝ)) * pairDeriv (U w + x • V w) (V w)| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ w, 4 * hessian_free_energy (α := α) n (U w + x • V w) (V w) (V w) ∂P := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => abs_nonneg _)
          (hI.const_mul 4) (Filter.Eventually.of_forall hpt)
    _ = 4 * ∫ w, hessian_free_energy (α := α) n (U w + x • V w) (V w) (V w) ∂P :=
        integral_const_mul _ _

/-- **Lemma 12.1.7, (12.17)**, in the form `ψ(y) ≤ η/(2n) + (2/η) p''(y)` for every `η > 0`. -/
theorem pairFluct_le (hU : Measurable U) (hV : Measurable V)
    (hVi : Integrable (fun w => ‖V w‖) P) (hVi2 : Integrable (fun w => ‖V w‖ ^ 2) P)
    (n : ℕ) (y : ℝ) {η : ℝ} (hη : 0 < η) :
    (∫ w, (1 / (n : ℝ)) * pairAverage (U w + y • V w) (V w) ∂P)
      ≤ η / (2 * (n : ℝ))
        + (2 / η) * ∫ w, hessian_free_energy (α := α) n (U w + y • V w) (V w) (V w) ∂P := by
  have hpt : ∀ w, (1 / (n : ℝ)) * pairAverage (U w + y • V w) (V w)
      ≤ η / (2 * (n : ℝ))
        + (2 / η) * hessian_free_energy (α := α) n (U w + y • V w) (V w) (V w) := by
    intro w
    rw [hessian_free_energy_self_eq_variance]
    have := pairAverage_le (U w + y • V w) (V w) hη
    have h0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    calc (1 / (n : ℝ)) * pairAverage (U w + y • V w) (V w)
        ≤ (1 / (n : ℝ)) * (η / 2 + (2 / η) * ∑ σ : α, gibbs_pmf (α := α) (U w + y • V w) σ
            * ((V w) σ - gibbs_average (α := α) (U w + y • V w) (V w)) ^ 2) :=
          mul_le_mul_of_nonneg_left this h0
      _ = η / (2 * (n : ℝ)) + (2 / η) * ((1 / (n : ℝ)) * ∑ σ : α,
            gibbs_pmf (α := α) (U w + y • V w) σ
              * ((V w) σ - gibbs_average (α := α) (U w + y • V w) (V w)) ^ 2) := by
          rw [mul_add]
          congr 1
          · ring
          · ring
  have hI := integrable_hessian_path (α := α) hU hV hVi2 n y
  calc (∫ w, (1 / (n : ℝ)) * pairAverage (U w + y • V w) (V w) ∂P)
      ≤ ∫ w, (η / (2 * (n : ℝ))
          + (2 / η) * hessian_free_energy (α := α) n (U w + y • V w) (V w) (V w)) ∂P :=
        integral_mono (integrable_pairAverage_path hU hV hVi n y)
          ((integrable_const _).add (hI.const_mul _)) hpt
    _ = η / (2 * (n : ℝ))
        + (2 / η) * ∫ w, hessian_free_energy (α := α) n (U w + y • V w) (V w) (V w) ∂P := by
        rw [integral_add (integrable_const _) (hI.const_mul _), integral_const,
          integral_const_mul, probReal_univ, one_smul]

/-! ### Lemma 12.1.8: the monotone sandwich and the window bound -/

/-- The derivative `p'` of the mean free energy, as the function `y ↦ -𝔼⟨V⟩_y/n`. -/
lemma deriv_integral_free_energy_density_eq (hU : Measurable U) (hV : Measurable V)
    (hUi : Integrable (fun w => ‖U w‖) P) (hVi : Integrable (fun w => ‖V w‖) P) (n : ℕ) :
    deriv (fun y : ℝ => ∫ w, free_energy_density (α := α) n (U w + y • V w) ∂P)
      = fun y => ∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + y • V w) (V w) ∂P :=
  funext fun y => (hasDerivAt_integral_free_energy_density (α := α) hU hV hUi hVi n y).deriv

omit [IsProbabilityMeasure P] in
/-- `p'` is monotone: `p'' ≥ 0`. -/
lemma monotone_integral_neg_gibbs_average (hU : Measurable U) (hV : Measurable V)
    (hVi : Integrable (fun w => ‖V w‖) P) (hVi2 : Integrable (fun w => ‖V w‖ ^ 2) P) (n : ℕ) :
    Monotone fun y : ℝ =>
      ∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + y • V w) (V w) ∂P := by
  refine monotone_of_deriv_nonneg
    (fun y => (hasDerivAt_integral_gibbs_average (α := α) hU hV hVi hVi2 n y).differentiableAt)
    fun y => ?_
  rw [(hasDerivAt_integral_gibbs_average (α := α) hU hV hVi hVi2 n y).deriv]
  exact integral_nonneg fun w => hessian_free_energy_self_nonneg (α := α) n _ _

omit [IsProbabilityMeasure P] in
/-- **`ψ - 4p'` is nonincreasing and `ψ + 4p'` is nondecreasing**, by Lemma 12.1.7 (12.18). -/
theorem pairFluct_le_pairFluct_add (hU : Measurable U) (hV : Measurable V)
    (hVi : Integrable (fun w => ‖V w‖) P) (hVi2 : Integrable (fun w => ‖V w‖ ^ 2) P)
    (n : ℕ) (x y : ℝ) :
    (∫ w, (1 / (n : ℝ)) * pairAverage (U w + x • V w) (V w) ∂P)
      ≤ (∫ w, (1 / (n : ℝ)) * pairAverage (U w + y • V w) (V w) ∂P)
        + 4 * |(∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w) ∂P)
            - ∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + y • V w) (V w) ∂P| := by
  have hψd : ∀ z, HasDerivAt
      (fun z : ℝ => ∫ w, (1 / (n : ℝ)) * pairAverage (U w + z • V w) (V w) ∂P)
      (∫ w, (1 / (n : ℝ)) * pairDeriv (U w + z • V w) (V w) ∂P) z :=
    fun z => hasDerivAt_pairFluct hU hV hVi hVi2 n z
  have hqd : ∀ z, HasDerivAt
      (fun z : ℝ => ∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + z • V w) (V w) ∂P)
      (∫ w, hessian_free_energy (α := α) n (U w + z • V w) (V w) (V w) ∂P) z :=
    fun z => hasDerivAt_integral_gibbs_average (α := α) hU hV hVi hVi2 n z
  have hbound : ∀ z, |∫ w, (1 / (n : ℝ)) * pairDeriv (U w + z • V w) (V w) ∂P|
      ≤ 4 * ∫ w, hessian_free_energy (α := α) n (U w + z • V w) (V w) (V w) ∂P :=
    fun z => abs_integral_pairDeriv_le hU hV hVi2 n z
  have hsub : ∀ z, HasDerivAt (fun z : ℝ =>
      (∫ w, (1 / (n : ℝ)) * pairAverage (U w + z • V w) (V w) ∂P)
        - 4 * ∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + z • V w) (V w) ∂P)
      ((∫ w, (1 / (n : ℝ)) * pairDeriv (U w + z • V w) (V w) ∂P)
        - 4 * ∫ w, hessian_free_energy (α := α) n (U w + z • V w) (V w) (V w) ∂P) z :=
    fun z => (hψd z).sub ((hqd z).const_mul 4)
  have hadd : ∀ z, HasDerivAt (fun z : ℝ =>
      (∫ w, (1 / (n : ℝ)) * pairAverage (U w + z • V w) (V w) ∂P)
        + 4 * ∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + z • V w) (V w) ∂P)
      ((∫ w, (1 / (n : ℝ)) * pairDeriv (U w + z • V w) (V w) ∂P)
        + 4 * ∫ w, hessian_free_energy (α := α) n (U w + z • V w) (V w) (V w) ∂P) z :=
    fun z => (hψd z).add ((hqd z).const_mul 4)
  have hanti : Antitone fun z : ℝ =>
      (∫ w, (1 / (n : ℝ)) * pairAverage (U w + z • V w) (V w) ∂P)
        - 4 * ∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + z • V w) (V w) ∂P := by
    refine antitone_of_deriv_nonpos (fun z => (hsub z).differentiableAt) fun z => ?_
    rw [(hsub z).deriv]
    linarith [(abs_le.1 (hbound z)).2]
  have hmono : Monotone fun z : ℝ =>
      (∫ w, (1 / (n : ℝ)) * pairAverage (U w + z • V w) (V w) ∂P)
        + 4 * ∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + z • V w) (V w) ∂P := by
    refine monotone_of_deriv_nonneg (fun z => (hadd z).differentiableAt) fun z => ?_
    rw [(hadd z).deriv]
    linarith [(abs_le.1 (hbound z)).1]
  have hqm := monotone_integral_neg_gibbs_average hU hV hVi hVi2 n
  rcases le_total y x with hyx | hxy
  · have h := hanti hyx
    have hq' := hqm hyx
    simp only at h hq'
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have h := hmono hxy
    have hq' := hqm hxy
    simp only at h hq'
    rw [abs_of_nonpos (by linarith)]
    linarith

omit [IsProbabilityMeasure P] in
/-- In the window `[x - b, x + b]`, `ψ(x) ≤ ψ(y) + 4 D(x, b)` with `D(x,b) = p'(x+b) - p'(x-b)`. -/
theorem pairFluct_le_pairFluct_add_window (hU : Measurable U) (hV : Measurable V)
    (hVi : Integrable (fun w => ‖V w‖) P) (hVi2 : Integrable (fun w => ‖V w‖ ^ 2) P)
    (n : ℕ) {x b y : ℝ} (hy : y ∈ Icc (x - b) (x + b)) :
    (∫ w, (1 / (n : ℝ)) * pairAverage (U w + x • V w) (V w) ∂P)
      ≤ (∫ w, (1 / (n : ℝ)) * pairAverage (U w + y • V w) (V w) ∂P)
        + 4 * ((∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + (x + b) • V w) (V w) ∂P)
            - ∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + (x - b) • V w) (V w) ∂P) := by
  have hmono := monotone_integral_neg_gibbs_average hU hV hVi hVi2 n
  have h := pairFluct_le_pairFluct_add hU hV hVi hVi2 n x y
  have hxb : x ≤ x + b := by linarith [hy.1, hy.2]
  have hbx : x - b ≤ x := by linarith [hy.1, hy.2]
  have h1 := hmono hy.1
  have h2 := hmono hy.2
  have h3 := hmono hxb
  have h4 := hmono hbx
  simp only at h1 h2 h3 h4
  refine h.trans ?_
  gcongr
  rw [abs_le]
  constructor <;> linarith

omit [IsProbabilityMeasure P] in
/-- **Some point of the window has small `p''`**: since `∫_{x-b}^{x+b} p'' = D(x,b)`, there is
`y ∈ [x-b, x+b]` with `p''(y) ≤ D(x,b)/(2b)`. -/
theorem exists_integral_hessian_le_window (hU : Measurable U) (hV : Measurable V)
    (hVi : Integrable (fun w => ‖V w‖) P) (hVi2 : Integrable (fun w => ‖V w‖ ^ 2) P)
    (n : ℕ) (x : ℝ) {b : ℝ} (hb : 0 < b) :
    ∃ y ∈ Icc (x - b) (x + b),
      (∫ w, hessian_free_energy (α := α) n (U w + y • V w) (V w) (V w) ∂P)
        ≤ ((∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + (x + b) • V w) (V w) ∂P)
            - ∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + (x - b) • V w) (V w) ∂P)
          / (2 * b) := by
  have hcont := continuous_integral_hessian_path (α := α) hU hV hVi2 n
  have hint := integral_fluctuation_eq_sub (α := α) hU hV hVi hVi2 n (x - b) (x + b)
  have hvol : volume (Icc (x - b) (x + b)) = ENNReal.ofReal (2 * b) := by
    rw [Real.volume_Icc]; congr 1; ring
  obtain ⟨y, hy, hle⟩ := exists_le_setAverage (μ := volume) (s := Icc (x - b) (x + b))
    (f := fun z => ∫ w, hessian_free_energy (α := α) n (U w + z • V w) (V w) (V w) ∂P)
    (by rw [hvol]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne')
    (by rw [hvol]; exact ENNReal.ofReal_ne_top) hcont.integrableOn_Icc
  refine ⟨y, hy, hle.trans_eq ?_⟩
  rw [setAverage_eq, measureReal_def, hvol, ENNReal.toReal_ofReal (by positivity), smul_eq_mul,
    ← hint, intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc,
    div_eq_inv_mul]

/-- **Lemma 12.1.8** (Talagrand Vol. II, (12.19), in the form with a free parameter `η`):
`ψ(x) ≤ η/(2n) + D(x,b)/(bη) + 4 D(x,b)`. -/
theorem pairFluct_le_window (hU : Measurable U) (hV : Measurable V)
    (hVi : Integrable (fun w => ‖V w‖) P) (hVi2 : Integrable (fun w => ‖V w‖ ^ 2) P)
    (n : ℕ) (x : ℝ) {b η : ℝ} (hb : 0 < b) (hη : 0 < η) :
    (∫ w, (1 / (n : ℝ)) * pairAverage (U w + x • V w) (V w) ∂P)
      ≤ η / (2 * (n : ℝ))
        + ((∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + (x + b) • V w) (V w) ∂P)
            - ∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + (x - b) • V w) (V w) ∂P)
          / (b * η)
        + 4 * ((∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + (x + b) • V w) (V w) ∂P)
            - ∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + (x - b) • V w) (V w) ∂P) := by
  obtain ⟨y, hy, hle⟩ := exists_integral_hessian_le_window hU hV hVi hVi2 n x hb
  have h1 := pairFluct_le_pairFluct_add_window hU hV hVi hVi2 n hy
  have h2 := pairFluct_le hU hV hVi hVi2 n y hη
  set D := (∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + (x + b) • V w) (V w) ∂P)
    - ∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + (x - b) • V w) (V w) ∂P with hD
  have h3 : (2 / η) * (∫ w, hessian_free_energy (α := α) n (U w + y • V w) (V w) (V w) ∂P)
      ≤ (2 / η) * (D / (2 * b)) := mul_le_mul_of_nonneg_left hle (by positivity)
  have h4 : (2 / η) * (D / (2 * b)) = D / (b * η) := by
    rw [div_mul_div_comm, show η * (2 * b) = 2 * (b * η) by ring,
      mul_div_mul_left _ _ (two_ne_zero : (2 : ℝ) ≠ 0)]
  linarith

/-! ### The disorder part: Griffiths' lemma in mean at a fixed parameter -/

/-- **The fluctuation of the derivative of the sample free energy at a fixed parameter**,
Talagrand Vol. II, (12.16): `𝔼|⟨V⟩/n - 𝔼⟨V⟩/n| ≤ D(x,b) + 3C/b` where `C` bounds the mean
fluctuation of the free energy at the three window points `x - b`, `x`, `x + b`. -/
theorem integral_abs_gibbs_average_sub_le_window (hU : Measurable U) (hV : Measurable V)
    (hUi : Integrable (fun w => ‖U w‖) P) (hVi : Integrable (fun w => ‖V w‖) P)
    (n : ℕ) (x : ℝ) {b : ℝ} (hb : 0 < b) {C : ℝ}
    (hC : ∀ y ∈ Icc (x - b) (x + b), (∫ w, |free_energy_density (α := α) n (U w + y • V w)
        - ∫ w', free_energy_density (α := α) n (U w' + y • V w') ∂P| ∂P) ≤ C) :
    (∫ w, |(1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w)
        - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P| ∂P)
      ≤ ((∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + (x + b) • V w) (V w) ∂P)
            - ∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + (x - b) • V w) (V w) ∂P)
        + 3 * C / b := by
  have hpd : ∀ y, HasDerivAt (fun y : ℝ => ∫ w, free_energy_density (α := α) n (U w + y • V w) ∂P)
      (∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + y • V w) (V w) ∂P) y :=
    fun y => hasDerivAt_integral_free_energy_density (α := α) hU hV hUi hVi n y
  have hint : ∀ y, Integrable (fun w => |free_energy_density (α := α) n (U w + y • V w)
      - ∫ w', free_energy_density (α := α) n (U w' + y • V w') ∂P|) P :=
    fun y => ((integrable_free_energy_density_path hU hV hUi hVi n y).sub
      (integrable_const _)).abs
  have h := ConvexOn.integral_abs_deriv_sub_le (P := P) (S := (univ : Set ℝ))
    (θ := fun w y => free_energy_density (α := α) n (U w + y • V w))
    (p := fun y => ∫ w, free_energy_density (α := α) n (U w + y • V w) ∂P) (x := x) (b := b)
    (fun w => convexOn_free_energy_density_comp_affine (α := α) n (U w) (V w))
    (convexOn_integral_free_energy_density (α := α) n hU hV hUi hVi) hb
    (by simp) (by simp) (by simp)
    (fun w => (hasDerivAt_free_energy_density_add_smul (α := α) n (U w) (V w) x).differentiableAt)
    (hpd x).differentiableAt (hpd (x - b)).differentiableAt (hpd (x + b)).differentiableAt
    (hint x) (hint (x - b)) (hint (x + b))
  beta_reduce at h
  have hderiv : ∀ w, |deriv (fun y => free_energy_density (α := α) n (U w + y • V w)) x
      - deriv (fun y : ℝ => ∫ w, free_energy_density (α := α) n (U w + y • V w) ∂P) x|
      = |(1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w)
          - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P| := by
    intro w
    rw [deriv_free_energy_density_add_smul, (hpd x).deriv]
    simp only [neg_mul, integral_neg, neg_sub_neg]
    rw [abs_sub_comm]
  rw [integral_congr_ae (Filter.Eventually.of_forall hderiv), (hpd (x + b)).deriv,
    (hpd (x - b)).deriv] at h
  refine h.trans ?_
  have hCp := hC (x + b) ⟨by linarith, le_rfl⟩
  have hCm := hC (x - b) ⟨le_rfl, by linarith⟩
  have hC0 := hC x ⟨by linarith, by linarith⟩
  have : ((∫ w, |free_energy_density (α := α) n (U w + (x + b) • V w)
        - ∫ w', free_energy_density (α := α) n (U w' + (x + b) • V w') ∂P| ∂P)
      + (∫ w, |free_energy_density (α := α) n (U w + (x - b) • V w)
        - ∫ w', free_energy_density (α := α) n (U w' + (x - b) • V w') ∂P| ∂P)
      + ∫ w, |free_energy_density (α := α) n (U w + x • V w)
        - ∫ w', free_energy_density (α := α) n (U w' + x • V w') ∂P| ∂P) / b ≤ 3 * C / b := by
    rw [div_le_div_iff_of_pos_right hb]
    linarith
  linarith

/-! ### Theorem 12.1.3 at finite volume -/

lemma measurable_gibbs_absFluct_path (hU : Measurable U) (hV : Measurable V) (x : ℝ) :
    Measurable fun w => gibbs_average (α := α) (U w + x • V w)
      (fun σ => |V w σ - gibbs_average (α := α) (U w + x • V w) (V w)|) := by
  classical
  have hpath : Measurable fun w => U w + x • V w := by fun_prop
  have hpmf : ∀ σ : α, Measurable fun w => gibbs_pmf (α := α) (U w + x • V w) σ := fun σ =>
    ((contDiff_gibbs_pmf (α := α) σ).continuous.measurable).comp hpath
  have hev : ∀ σ : α, Measurable fun w => (V w) σ := fun σ =>
    (measurable_eval (α := α) σ).comp hV
  have hav := measurable_gibbs_average_path (α := α) hU hV x
  simp only [gibbs_average]
  refine Finset.measurable_sum _ fun σ _ => ?_
  exact (hpmf σ).mul (continuous_abs.measurable.comp ((hev σ).sub hav))

omit [IsProbabilityMeasure P] in
lemma integrable_gibbs_absFluct_path (hU : Measurable U) (hV : Measurable V)
    (hVi : Integrable (fun w => ‖V w‖) P) (n : ℕ) (x : ℝ) :
    Integrable (fun w => (1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w)
      (fun σ => |V w σ - gibbs_average (α := α) (U w + x • V w) (V w)|)) P := by
  have h0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  refine Integrable.mono' ((hVi.const_mul 2).const_mul (1 / (n : ℝ)))
    ((measurable_gibbs_absFluct_path (α := α) hU hV x).const_mul _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0,
    abs_of_nonneg (gibbs_average_abs_sub_nonneg (α := α) _ _ _)]
  exact mul_le_mul_of_nonneg_left (gibbs_average_abs_sub_gibbs_average_le (α := α) _ _) h0

omit [IsProbabilityMeasure P] in
lemma integrable_gibbs_average_path (hU : Measurable U) (hV : Measurable V)
    (hVi : Integrable (fun w => ‖V w‖) P) (n : ℕ) (x : ℝ) :
    Integrable (fun w => (1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w)) P := by
  have h0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  refine Integrable.mono' (hVi.const_mul (1 / (n : ℝ)))
    ((measurable_gibbs_average_path (α := α) hU hV x).const_mul _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
  exact mul_le_mul_of_nonneg_left (abs_gibbs_average_le (α := α) _ _) h0

/-- The total energy fluctuation splits into its Gibbs part and its disorder part, at a fixed
parameter. -/
theorem integral_totalFluct_le_add (hU : Measurable U) (hV : Measurable V)
    (hVi : Integrable (fun w => ‖V w‖) P) (n : ℕ) (x : ℝ) :
    (∫ w, gibbs_average (α := α) (U w + x • V w)
        (fun σ => |(1 / (n : ℝ)) * V w σ
          - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P|) ∂P)
      ≤ (∫ w, (1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w)
            (fun σ => |V w σ - gibbs_average (α := α) (U w + x • V w) (V w)|) ∂P)
        + ∫ w, |(1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w)
            - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P| ∂P := by
  have h0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have hpt : ∀ w, gibbs_average (α := α) (U w + x • V w)
      (fun σ => |(1 / (n : ℝ)) * V w σ
        - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P|)
      ≤ (1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w)
            (fun σ => |V w σ - gibbs_average (α := α) (U w + x • V w) (V w)|)
        + |(1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w)
            - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P| := by
    intro w
    set c : ℝ := ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P
    set H := U w + x • V w
    set m := gibbs_average (α := α) H (V w)
    have hsum : ∑ τ : α, gibbs_pmf (α := α) H τ * |(1 / (n : ℝ)) * m - c|
        = |(1 / (n : ℝ)) * m - c| := by
      rw [← Finset.sum_mul, sum_gibbs_pmf, one_mul]
    simp only [gibbs_average, Finset.mul_sum]
    rw [← hsum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun σ _ => ?_
    have hp := gibbs_pmf_nonneg (α := α) H σ
    have htri : |(1 / (n : ℝ)) * V w σ - c|
        ≤ (1 / (n : ℝ)) * |V w σ - m| + |(1 / (n : ℝ)) * m - c| := by
      calc |(1 / (n : ℝ)) * V w σ - c|
          = |(1 / (n : ℝ)) * (V w σ - m) + ((1 / (n : ℝ)) * m - c)| := by congr 1; ring
        _ ≤ |(1 / (n : ℝ)) * (V w σ - m)| + |(1 / (n : ℝ)) * m - c| := abs_add_le _ _
        _ = (1 / (n : ℝ)) * |V w σ - m| + |(1 / (n : ℝ)) * m - c| := by
            rw [abs_mul, abs_of_nonneg h0]
    calc gibbs_pmf (α := α) H σ * |(1 / (n : ℝ)) * V w σ - c|
        ≤ gibbs_pmf (α := α) H σ * ((1 / (n : ℝ)) * |V w σ - m| + |(1 / (n : ℝ)) * m - c|) :=
          mul_le_mul_of_nonneg_left htri hp
      _ = (1 / (n : ℝ)) * (gibbs_pmf (α := α) H σ * |V w σ - m|)
          + gibbs_pmf (α := α) H σ * |(1 / (n : ℝ)) * m - c| := by ring
  have hI1 := integrable_gibbs_absFluct_path (α := α) hU hV hVi n x
  have hI2 : Integrable (fun w => |(1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w)
      - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P|) P :=
    ((integrable_gibbs_average_path (α := α) hU hV hVi n x).sub (integrable_const _)).abs
  calc (∫ w, gibbs_average (α := α) (U w + x • V w)
        (fun σ => |(1 / (n : ℝ)) * V w σ
          - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P|) ∂P)
      ≤ ∫ w, ((1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w)
            (fun σ => |V w σ - gibbs_average (α := α) (U w + x • V w) (V w)|)
          + |(1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w) (V w)
            - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P|) ∂P :=
        integral_mono (integrable_totalFluct_path (α := α) n hU hV hVi x) (hI1.add hI2) hpt
    _ = _ := integral_add hI1 hI2

/-- **Theorem 12.1.3 at finite volume** (Talagrand Vol. II, Panchenko): for every window
half-width `b > 0` and every `η > 0`, the total energy fluctuation at the parameter `x` is at most

`η/(2n) + D(x,b)/(bη) + 5 D(x,b) + 3C/b`,

where `D(x,b) = p'(x+b) - p'(x-b)` is the increment of the derivative of the mean free energy
across the window and `C` bounds the mean fluctuation of the sample free energy on the window. -/
theorem integral_totalFluct_le_window (hU : Measurable U) (hV : Measurable V)
    (hUi : Integrable (fun w => ‖U w‖) P) (hVi : Integrable (fun w => ‖V w‖) P)
    (hVi2 : Integrable (fun w => ‖V w‖ ^ 2) P) (n : ℕ) (x : ℝ) {b η : ℝ} (hb : 0 < b)
    (hη : 0 < η) {C : ℝ}
    (hC : ∀ y ∈ Icc (x - b) (x + b), (∫ w, |free_energy_density (α := α) n (U w + y • V w)
        - ∫ w', free_energy_density (α := α) n (U w' + y • V w') ∂P| ∂P) ≤ C) :
    (∫ w, gibbs_average (α := α) (U w + x • V w)
        (fun σ => |(1 / (n : ℝ)) * V w σ
          - ∫ w', (1 / (n : ℝ)) * gibbs_average (α := α) (U w' + x • V w') (V w') ∂P|) ∂P)
      ≤ η / (2 * (n : ℝ))
        + ((∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + (x + b) • V w) (V w) ∂P)
            - ∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + (x - b) • V w) (V w) ∂P)
          / (b * η)
        + 5 * ((∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + (x + b) • V w) (V w) ∂P)
            - ∫ w, -(1 / (n : ℝ)) * gibbs_average (α := α) (U w + (x - b) • V w) (V w) ∂P)
        + 3 * C / b := by
  have h1 := integral_totalFluct_le_add hU hV hVi n x
  have h2 : (∫ w, (1 / (n : ℝ)) * gibbs_average (α := α) (U w + x • V w)
        (fun σ => |V w σ - gibbs_average (α := α) (U w + x • V w) (V w)|) ∂P)
      ≤ ∫ w, (1 / (n : ℝ)) * pairAverage (U w + x • V w) (V w) ∂P :=
    integral_mono (integrable_gibbs_absFluct_path (α := α) hU hV hVi n x)
      (integrable_pairAverage_path hU hV hVi n x) fun w =>
        mul_le_mul_of_nonneg_left (gibbs_average_abs_sub_le_pairAverage _ _) (by positivity)
  have h3 := pairFluct_le_window hU hV hVi hVi2 n x hb hη
  have h4 := integral_abs_gibbs_average_sub_le_window hU hV hUi hVi n x hb hC
  linarith

/-! ### The passage to the limit -/

/-- **First `N → ∞`, then `b → 0`.** If nonnegative quantities `T N` obey the window bound of
`integral_totalFluct_le_window` with volumes `n N → ∞`, with `D N b` eventually small for a
suitable window (Lemma 12.1.9) and with the concentration constants `C N b → 0` for every fixed
window, then `T N → 0`. -/
theorem tendsto_zero_of_le_window {T : ℕ → ℝ} {D C : ℕ → ℝ → ℝ} {n : ℕ → ℝ}
    (hT : ∀ N, 0 ≤ T N) (hn : Tendsto n atTop atTop)
    (hle : ∀ᶠ N in atTop, ∀ b > 0, ∀ η > 0,
      T N ≤ η / (2 * n N) + D N b / (b * η) + 5 * D N b + 3 * C N b / b)
    (hD : ∀ ε > 0, ∃ b > 0, ∀ᶠ N in atTop, D N b ≤ ε)
    (hC : ∀ b > 0, Tendsto (fun N => C N b) atTop (𝓝 0)) :
    Tendsto T atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨b, hb, hDb⟩ := hD (ε / 40) (by positivity)
  have hη0 : (0 : ℝ) < 1 / (5 * b) := by positivity
  have h1 : ∀ᶠ N in atTop, (1 / (5 * b)) / (2 * n N) ≤ ε / 8 := by
    have := hn.eventually (eventually_ge_atTop (4 * (1 / (5 * b)) / ε))
    filter_upwards [this] with N hN
    have hnpos : 0 < n N := lt_of_lt_of_le (by positivity) hN
    rw [div_le_iff₀ (by positivity)]
    have := (div_le_iff₀ hε).1 hN
    linarith
  have h2 : ∀ᶠ N in atTop, 3 * C N b / b ≤ ε / 8 := by
    have := Metric.tendsto_nhds.1 (hC b hb) _ (by positivity : 0 < ε * b / 24)
    filter_upwards [this] with N hN
    rw [Real.dist_eq, sub_zero, abs_lt] at hN
    rw [div_le_iff₀ hb]
    linarith [hN.2]
  filter_upwards [h1, h2, hDb, hle] with N h1 h2 hDN hleN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hT N)]
  have hle' := hleN b hb (1 / (5 * b)) hη0
  have hD1 : D N b / (b * (1 / (5 * b))) = 5 * D N b := by
    rw [show b * (1 / (5 * b)) = 1 / 5 by field_simp]
    ring
  rw [hD1] at hle'
  linarith

end

end FiniteGibbs

end SpinGlass
