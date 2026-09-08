/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.FiniteGibbs.Calculus
import SpinGlass.FiniteGibbs.Convexity

/-!
# The free energy along an affine path in the Hamiltonian

Every parameter of a mean-field model — the inverse temperature, an external field, the strength of
a perturbation — enters the Hamiltonian affinely, so every parameter derivative of the free energy
is a derivative along a path `x ↦ H + x • V`. Talagrand computes the first two:

* `N Φ'(x) = ⟨-V⟩` — Vol. I, (1.83); Vol. II, (12.6);
* `N Φ''(x) = ⟨V²⟩ - ⟨V⟩² = ⟨(V - ⟨V⟩)²⟩` — Vol. II, (12.8),

and the second is the reason the free energy is convex in every such parameter *and* the reason its
second derivative measures the **fluctuation of the energy** `V` under the Gibbs measure. Both are
proved here at every finite volume, for an arbitrary finite configuration space, with no
probabilistic hypothesis whatsoever: these are identities of ordinary calculus for log-sum-exp.

## Main statements

- `SpinGlass.FiniteGibbs.hasDerivAt_free_energy_density_add_smul` — Vol. I, (1.83).
- `SpinGlass.FiniteGibbs.hasDerivAt_gibbsAverage_add_smul` — Vol. II, (12.8), as a derivative.
- `SpinGlass.FiniteGibbs.hessian_free_energy_self_eq_variance` — the second derivative is the Gibbs
  variance, hence nonnegative: `SpinGlass.FiniteGibbs.hessian_free_energy_self_nonneg`.
-/

open Real BigOperators
open scoped ContDiff

namespace SpinGlass

namespace FiniteGibbs

noncomputable section

variable {α : Type*} [Fintype α] [Nonempty α]

lemma abs_gibbs_average_le (H V : EnergySpace α) :
    |gibbs_average (α := α) H V| ≤ ‖V‖ := by
  classical
  calc |gibbs_average (α := α) H V| ≤ ∑ σ : α, |gibbs_pmf (α := α) H σ * V σ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ : α, gibbs_pmf (α := α) H σ * ‖V‖ := by
        refine Finset.sum_le_sum fun σ _ => ?_
        rw [abs_mul, abs_of_nonneg (gibbs_pmf_nonneg (α := α) H σ)]
        exact mul_le_mul_of_nonneg_left (abs_apply_le_norm (α := α) V σ)
          (gibbs_pmf_nonneg (α := α) H σ)
    _ = ‖V‖ := by rw [← Finset.sum_mul, sum_gibbs_pmf (α := α) H, one_mul]

lemma gibbs_average_abs_le (H V : EnergySpace α) :
    gibbs_average (α := α) H (fun σ => |V σ|) ≤ ‖V‖ := by
  classical
  calc gibbs_average (α := α) H (fun σ => |V σ|)
      ≤ ∑ σ : α, gibbs_pmf (α := α) H σ * ‖V‖ := by
        refine Finset.sum_le_sum fun σ _ => ?_
        exact mul_le_mul_of_nonneg_left (abs_apply_le_norm (α := α) V σ)
          (gibbs_pmf_nonneg (α := α) H σ)
    _ = ‖V‖ := by rw [← Finset.sum_mul, sum_gibbs_pmf (α := α) H, one_mul]

lemma gibbs_average_abs_sub_nonneg (H V : EnergySpace α) (c : ℝ) :
    0 ≤ gibbs_average (α := α) H (fun σ => |V σ - c|) :=
  Finset.sum_nonneg fun σ _ => mul_nonneg (gibbs_pmf_nonneg (α := α) H σ) (abs_nonneg _)

/-- The Gibbs mean absolute deviation of a direction is at most twice its norm. -/
lemma gibbs_average_abs_sub_gibbs_average_le (H V : EnergySpace α) :
    gibbs_average (α := α) H (fun σ => |V σ - gibbs_average (α := α) H V|) ≤ 2 * ‖V‖ := by
  classical
  have hc : |gibbs_average (α := α) H V| ≤ ‖V‖ := abs_gibbs_average_le (α := α) H V
  calc gibbs_average (α := α) H (fun σ => |V σ - gibbs_average (α := α) H V|)
      ≤ ∑ σ : α, gibbs_pmf (α := α) H σ
          * (|V σ| + |gibbs_average (α := α) H V|) := by
        refine Finset.sum_le_sum fun σ _ => ?_
        exact mul_le_mul_of_nonneg_left (abs_sub _ _) (gibbs_pmf_nonneg (α := α) H σ)
    _ = gibbs_average (α := α) H (fun σ => |V σ|) + |gibbs_average (α := α) H V| := by
        simp only [gibbs_average, mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_gibbs_pmf (α := α) H, one_mul]
    _ ≤ ‖V‖ + ‖V‖ := add_le_add (gibbs_average_abs_le (α := α) H V) hc
    _ = 2 * ‖V‖ := by ring

lemma continuous_gibbs_average_path (H W : EnergySpace α) :
    Continuous fun x : ℝ => gibbs_average (α := α) (H + x • W) W := by
  classical
  have hpath : Continuous fun x : ℝ => H + x • W := by fun_prop
  have hp : ∀ σ : α, Continuous fun x : ℝ => gibbs_pmf (α := α) (H + x • W) σ := fun σ =>
    ((contDiff_gibbs_pmf (α := α) σ).continuous).comp hpath
  simp only [gibbs_average]
  exact continuous_finsetSum _ fun σ _ => (hp σ).mul continuous_const

/-- The Gibbs mean absolute deviation of `W/n` from a constant `c` is at most `‖W‖/n + |c|`. -/
lemma gibbs_average_abs_smul_sub_const_le_norm (n : ℕ) (H W : EnergySpace α) (c : ℝ) :
    gibbs_average (α := α) H (fun σ => |(1 / (n : ℝ)) * W σ - c|)
      ≤ (1 / (n : ℝ)) * ‖W‖ + |c| := by
  classical
  have hpt : ∀ σ : α, |(1 / (n : ℝ)) * W σ - c| ≤ (1 / (n : ℝ)) * ‖W‖ + |c| := by
    intro σ
    refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (n : ℝ))]
    exact mul_le_mul_of_nonneg_left (abs_apply_le_norm (α := α) W σ) (by positivity)
  calc gibbs_average (α := α) H (fun σ => |(1 / (n : ℝ)) * W σ - c|)
      ≤ ∑ σ : α, gibbs_pmf (α := α) H σ * ((1 / (n : ℝ)) * ‖W‖ + |c|) :=
        Finset.sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_left (hpt σ) (gibbs_pmf_nonneg (α := α) H σ)
    _ = (1 / (n : ℝ)) * ‖W‖ + |c| := by
        rw [← Finset.sum_mul, sum_gibbs_pmf (α := α) H, one_mul]

lemma gibbs_average_abs_smul_sub_const_nonneg (n : ℕ) (H W : EnergySpace α) (c : ℝ) :
    0 ≤ gibbs_average (α := α) H (fun σ => |(1 / (n : ℝ)) * W σ - c|) :=
  Finset.sum_nonneg fun σ _ => mul_nonneg (gibbs_pmf_nonneg (α := α) H σ) (abs_nonneg _)

/-! ### The first derivative -/

/-- **The first derivative of the free energy along an affine path in the Hamiltonian**:
`d/dx (1/n) log Z(H + x V) = -(1/n) ⟨V⟩`. Talagrand Vol. I, (1.83); Vol. II, (12.6). -/
theorem hasDerivAt_free_energy_density_add_smul (n : ℕ) (H V : EnergySpace α) (x : ℝ) :
    HasDerivAt (fun y : ℝ => free_energy_density (α := α) n (H + y • V))
      (-(1 / (n : ℝ)) * gibbs_average (α := α) (H + x • V) V) x := by
  have hpath : HasDerivAt (fun y : ℝ => H + y • V) V x := by
    simpa using ((hasDerivAt_id x).smul_const V).const_add H
  have h := hasDerivAt_free_energy_density_comp (α := α) n hpath
  rwa [fderiv_free_energy_density_apply (α := α) n (H + x • V) V] at h

@[simp] lemma deriv_free_energy_density_add_smul (n : ℕ) (H V : EnergySpace α) (x : ℝ) :
    deriv (fun y : ℝ => free_energy_density (α := α) n (H + y • V)) x
      = -(1 / (n : ℝ)) * gibbs_average (α := α) (H + x • V) V :=
  (hasDerivAt_free_energy_density_add_smul (α := α) n H V x).deriv

/-! ### The second derivative -/

/-- **The derivative of the Gibbs average along an affine path is the Gibbs covariance.** -/
theorem hasDerivAt_gibbsAverage_add_smul (n : ℕ) (H V : EnergySpace α) (x : ℝ) :
    HasDerivAt (fun y : ℝ => -(1 / (n : ℝ)) * gibbs_average (α := α) (H + y • V) V)
      (hessian_free_energy (α := α) n (H + x • V) V V) x := by
  set F : EnergySpace α → ℝ := fun H' => free_energy_density (α := α) n H' with hF
  have hG : ContDiff ℝ 1 (fun z : EnergySpace α => fderiv ℝ F z) :=
    (contDiff_free_energy_density (α := α) (n := n)).fderiv_right (by simp)
  have hGd : HasFDerivAt (fun z : EnergySpace α => fderiv ℝ F z)
      (fderiv ℝ (fun z : EnergySpace α => fderiv ℝ F z) (H + x • V)) (H + x • V) :=
    ((hG.differentiable (by norm_num)) (H + x • V)).hasFDerivAt
  have hcomp : HasDerivAt (fun y : ℝ => fderiv ℝ F (H + y • V))
      ((fderiv ℝ (fun z : EnergySpace α => fderiv ℝ F z) (H + x • V)) V) x :=
    hGd.comp_hasDerivAt x (by simpa using ((hasDerivAt_id x).smul_const V).const_add H)
  have happ := (ContinuousLinearMap.apply ℝ ℝ V).hasFDerivAt.comp_hasDerivAt x hcomp
  have hval : ∀ y : ℝ, (ContinuousLinearMap.apply ℝ ℝ V) (fderiv ℝ F (H + y • V))
      = -(1 / (n : ℝ)) * gibbs_average (α := α) (H + y • V) V := fun y => by
    simpa [gibbs_average] using fderiv_free_energy_density_apply (α := α) n (H + y • V) V
  have hder : (ContinuousLinearMap.apply ℝ ℝ V)
      ((fderiv ℝ (fun z : EnergySpace α => fderiv ℝ F z) (H + x • V)) V)
      = hessian_free_energy (α := α) n (H + x • V) V V :=
    hessian_free_energy_fderiv_eq_hessian_free_energy (α := α) n (H + x • V) V V
  rw [hder] at happ
  exact happ.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => (hval y).symm)

/-! ### The second derivative is the Gibbs variance -/

/-- **`n Φ''(x) = ⟨(V - ⟨V⟩)²⟩`**: the second derivative of the free energy along an affine path is
the Gibbs variance of the direction. Talagrand Vol. II, (12.8). -/
theorem hessian_free_energy_self_eq_variance (n : ℕ) (H V : EnergySpace α) :
    hessian_free_energy (α := α) n H V V
      = (1 / (n : ℝ)) *
          ∑ σ : α, gibbs_pmf (α := α) H σ * (V σ - gibbs_average (α := α) H V) ^ 2 := by
  classical
  refine congrArg (fun t : ℝ => (1 / (n : ℝ)) * t) ?_
  have hexp : ∀ σ : α, gibbs_pmf (α := α) H σ * (V σ - gibbs_average (α := α) H V) ^ 2
      = gibbs_pmf (α := α) H σ * V σ * V σ
        - 2 * (gibbs_average (α := α) H V) * (gibbs_pmf (α := α) H σ * V σ)
        + (gibbs_average (α := α) H V) ^ 2 * gibbs_pmf (α := α) H σ := by
    intro σ; ring
  rw [Finset.sum_congr rfl fun σ _ => hexp σ]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_gibbs_pmf (α := α) H]
  simp only [gibbs_average]
  ring

/-- **The free energy is convex along every affine path in the Hamiltonian**, quantitatively: the
second derivative is a variance. -/
theorem hessian_free_energy_self_nonneg (n : ℕ) (H V : EnergySpace α) :
    0 ≤ hessian_free_energy (α := α) n H V V := by
  rw [hessian_free_energy_self_eq_variance]
  have : 0 ≤ ∑ σ : α, gibbs_pmf (α := α) H σ * (V σ - gibbs_average (α := α) H V) ^ 2 :=
    Finset.sum_nonneg fun σ _ => mul_nonneg (gibbs_pmf_nonneg (α := α) H σ) (sq_nonneg _)
  positivity

/-- The Gibbs variance is bounded by `‖V‖²`, uniformly in the Hamiltonian. -/
lemma hessian_free_energy_self_le (n : ℕ) (H V : EnergySpace α) :
    hessian_free_energy (α := α) n H V V ≤ (2 / (n : ℝ)) * ‖V‖ * ‖V‖ := by
  have h := abs_hessian_free_energy_le (α := α) n H V V
  exact (le_abs_self _).trans h

end

end FiniteGibbs

end SpinGlass
