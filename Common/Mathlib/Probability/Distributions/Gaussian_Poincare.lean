/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Analysis.Calculus.BoundedFDerivGrowth
import Common.Mathlib.Analysis.Calculus.GradientAPI
import Common.Mathlib.Analysis.InnerProductSpace.PositiveInner
import Common.Mathlib.Probability.Distributions.Gaussian_Rotation

/-!
# The Gaussian covariance inequality, and Poincaré as its diagonal

For a centered Gaussian measure `μ` on a real Hilbert space `H` and `C¹` functionals `f`, `g`
whose derivatives are bounded in norm, write `C = covarianceOperator μ` and

`Q h = ∫ ⟪C (∇ h x), ∇ h x⟫ ∂μ`

for the Dirichlet energy of `h` against the covariance. This file proves

`|cov[f, g; μ]| ≤ √(Q f) √(Q g)`  and  `|cov[f, g; μ]| ≤ ‖C‖ Kf Kg`,

and in particular, taking `g = f`,

`Var[f; μ] ≤ Q f ≤ ‖C‖ K²`,

the Gaussian Poincaré inequality in its sharp form and in its operator-norm form. Neither the
Dirichlet-energy form nor the operator-norm form carries a constant: both are the value of
`∫₀^{π/2} sin θ dθ = 1`.

## The argument

Write `P = μ ⊗ μ` and let `rot θ` be the quarter-turn of `Gaussian_Rotation`. Since `g x - g y` is
the integral of `d/dθ g (rot θ (x, y))` over `θ ∈ [0, π/2]`,

`cov[f, g; μ] = -∫₀^{π/2} ∫ f(x) · (Dg (rot θ (x,y))) (rot⊥ θ (x,y)) dP dθ`

(`abs_covariance_le_of_slice_le` packages this: any bound `|slice θ| ≤ |sin θ| M` gives
`|cov| ≤ M`). `rot θ` preserves `P`, so for each fixed `θ` the inner integral may be read in the
rotated variables, where `x` becomes the *affine* function `cos θ • u - sin θ • v` of the new pair
`(u, v)` and the derivative factor becomes `(Dg u) v`, linear in `v`. One Gaussian integration by
parts in `v` (`integral_inner_mul_eq_integral_fderiv_covarianceOperator`) then trades that linear
factor for a derivative of `f`, producing the chain-rule factor `-sin θ`:

`∫ f(cos θ • u - sin θ • v) (Dg u) v dP = -sin θ ∫ (Df (rot (-θ) p)) (C (∇g p.1)) dP`

(`integral_prod_mul_fderiv_gaussRot_eq`). Bounding the right-hand side by operator norms gives the
`‖C‖ Kf Kg` form; bounding it instead by Cauchy–Schwarz for the positive operator `C`
(`LinearMap.IsPositive.abs_inner_le_half_add_smul`, carrying a free weight `λ > 0`) and using that
`rot (-θ)` again pushes `P` forward to a pair of independent copies of `μ` gives the
Dirichlet-energy form; optimising `λ` at the very end
(`Real.le_sqrt_mul_sqrt_of_forall_pos`) turns the arithmetic–geometric constant into the
Cauchy–Schwarz one, without ever needing Cauchy–Schwarz for an integral. The weight `sin θ`, which
the Cauchy–Schwarz-in-`θ` form of the rotation argument throws away, is what turns the crude
constant `π²/8` into `1`.

The Dirichlet-energy form is the one that is *useful* as well as sharp: for the free energy of a
mean-field model, `∇ log Z` is the Gibbs measure and `Q (log Z)` is a replica overlap, of order
`N`, whereas `‖C‖` is of the order of the number of configurations.

## Main statements

- `ProbabilityTheory.IsGaussian.abs_covariance_le_sqrt_mul_sqrt_integral_inner_covarianceOperator`:
  the covariance inequality in Dirichlet-energy form, with the Cauchy–Schwarz constant.
- `ProbabilityTheory.IsGaussian.abs_covariance_le_half_add_smul_integral_inner_covarianceOperator`:
  its weighted arithmetic–geometric form, from which the above follows by optimising the weight.
- `ProbabilityTheory.IsGaussian.abs_covariance_le_opNorm_covarianceOperator_mul`: the covariance
  inequality in operator-norm form.
- `ProbabilityTheory.IsGaussian.variance_le_integral_inner_covarianceOperator_gradient`: the sharp
  Gaussian Poincaré inequality, the diagonal of the first.
- `ProbabilityTheory.IsGaussian.variance_le_opNorm_covarianceOperator_mul_sq`: its operator-norm
  form.
- `ProbabilityTheory.IsGaussian.integral_sq_dual_le_opNorm_covarianceOperator`: the second moment
  of a dual functional.

## References

* Pisier, *Probabilistic methods in the geometry of Banach spaces*.
* Talagrand, *Mean Field Models for Spin Glasses*, Vol. I, §1.3.
-/

open scoped BigOperators ENNReal NNReal ProbabilityTheory RealInnerProductSpace Topology

open MeasureTheory Filter Real
open scoped Gradient

namespace ProbabilityTheory

namespace IsGaussian

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  {μ : Measure H} [IsGaussian μ]

/-! ### The second moment of a dual functional -/

/-- The second moment of a dual functional is controlled by the covariance operator:
`∫ (L x)² ∂μ ≤ ‖covarianceOperator μ‖ * ‖L‖²`. No centering is needed, because Mathlib's
`covarianceOperator` is the uncentered second-moment operator. -/
lemma integral_sq_dual_le_opNorm_covarianceOperator (L : StrongDual ℝ H) :
    (∫ x : H, (L x) ^ 2 ∂μ) ≤ ‖covarianceOperator μ‖ * ‖L‖ ^ 2 := by
  let h : H := (InnerProductSpace.toDual ℝ H).symm L
  have hL : ∀ x : H, L x = ⟪h, x⟫ := by
    intro x
    simp [h]
  have hLp2 : MemLp (id : H → H) 2 μ := IsGaussian.memLp_two_id (μ := μ)
  have hEq : (∫ x : H, (L x) ^ 2 ∂μ) = ⟪covarianceOperator μ h, h⟫ := by
    calc
      (∫ x : H, (L x) ^ 2 ∂μ) = ∫ x : H, ⟪h, x⟫ ^ 2 ∂μ := by simp [hL]
      _ = ⟪covarianceOperator μ h, h⟫ := by
        have : ⟪covarianceOperator μ h, h⟫ = ∫ x : H, ⟪h, x⟫ ^ 2 ∂μ := by
          simpa [pow_two] using (covarianceOperator_inner (μ := μ) hLp2 h h)
        simp [this]
  calc
    (∫ x : H, (L x) ^ 2 ∂μ) = ⟪covarianceOperator μ h, h⟫ := hEq
    _ ≤ ‖covarianceOperator μ h‖ * ‖h‖ := real_inner_le_norm _ _
    _ ≤ (‖covarianceOperator μ‖ * ‖h‖) * ‖h‖ := by
          gcongr
          exact (covarianceOperator μ).le_opNorm h
    _ = ‖covarianceOperator μ‖ * ‖h‖ ^ 2 := by ring
    _ = ‖covarianceOperator μ‖ * ‖L‖ ^ 2 := by simp [h]

/-! ### One integration by parts along the rotated variables -/

/-- **The integration-by-parts step.** For a `C¹` function `f` with `‖Df‖ ≤ K` and a dual
functional `L`, integrating `f (cos θ • x - sin θ • y) · L y` against a centered Gaussian in `y`
and integrating by parts replaces the linear factor `L y` by a derivative of `f` evaluated against
`C ∇L`, at the cost of the chain-rule factor `-sin θ`. -/
private lemma integral_affine_mul_dual_eq
    (hmean0 : (∫ x : H, x ∂μ) = 0) {f : H → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ x, ‖fderiv ℝ f x‖ ≤ K) (θ : ℝ) (x : H) (L : StrongDual ℝ H) :
    (∫ y : H, f (Real.cos θ • x - Real.sin θ • y) * L y ∂μ)
      = -Real.sin θ * ∫ y : H, (fderiv ℝ f (Real.cos θ • x - Real.sin θ • y))
          (covarianceOperator μ ((InnerProductSpace.toDual ℝ H).symm L)) ∂μ := by
  classical
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0)
  have hfdiff : Differentiable ℝ f := hf.differentiable_one
  set A : H →L[ℝ] H := (-Real.sin θ) • ContinuousLinearMap.id ℝ H with hA
  set F : H → ℝ := fun y => f (Real.cos θ • x - Real.sin θ • y) with hFdef
  set h : H := (InnerProductSpace.toDual ℝ H).symm L with hh
  have hLh : ∀ y : H, L y = ⟪y, h⟫ := by
    intro y
    rw [hh, real_inner_comm]
    simp
  -- the affine substitution and its derivative
  have hAff : ∀ y : H,
      HasFDerivAt (fun z : H => Real.cos θ • x - Real.sin θ • z) A y := by
    intro y
    have hs : HasFDerivAt (fun z : H => Real.sin θ • z)
        (Real.sin θ • ContinuousLinearMap.id ℝ H) y := (hasFDerivAt_id y).const_smul _
    have h0 := (hasFDerivAt_const (Real.cos θ • x) y).sub hs
    have hzero : (0 : H →L[ℝ] H) - Real.sin θ • ContinuousLinearMap.id ℝ H = A := by
      rw [hA, zero_sub, neg_smul]
    rwa [hzero] at h0
  have hFderiv : ∀ y : H,
      fderiv ℝ F y = (fderiv ℝ f (Real.cos θ • x - Real.sin θ • y)).comp A := by
    intro y
    have := ((hfdiff (Real.cos θ • x - Real.sin θ • y)).hasFDerivAt.comp y (hAff y)).fderiv
    simpa [hFdef, Function.comp_def] using this
  have hAnorm : ‖A‖ ≤ |Real.sin θ| := by
    calc ‖A‖ = |Real.sin θ| * ‖ContinuousLinearMap.id ℝ H‖ := by
          rw [hA, norm_smul, Real.norm_eq_abs, abs_neg]
      _ ≤ |Real.sin θ| * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (abs_nonneg _)
      _ = |Real.sin θ| := mul_one _
  have hFderiv_le : ∀ y : H, ‖fderiv ℝ F y‖ ≤ |Real.sin θ| * K := by
    intro y
    rw [hFderiv y]
    calc ‖(fderiv ℝ f (Real.cos θ • x - Real.sin θ • y)).comp A‖
        ≤ ‖fderiv ℝ f (Real.cos θ • x - Real.sin θ • y)‖ * ‖A‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ K * |Real.sin θ| := mul_le_mul (hK _) hAnorm (norm_nonneg _) hK0
      _ = |Real.sin θ| * K := mul_comm _ _
  -- growth hypotheses for the integration by parts
  set C : ℝ := |f 0| + K * ‖x‖ + K with hC
  have hC0 : 0 ≤ C := by positivity
  have hgrowth : ∀ y : H, |F y| ≤ C * (1 + ‖y‖) ^ 1 := by
    intro y
    have h1 : ‖Real.cos θ • x - Real.sin θ • y‖ ≤ ‖x‖ + ‖y‖ := by
      refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_) <;>
        rw [norm_smul, Real.norm_eq_abs]
      · exact mul_le_of_le_one_left (norm_nonneg _) (abs_cos_le_one θ)
      · exact mul_le_of_le_one_left (norm_nonneg _) (abs_sin_le_one θ)
    have h2 : |F y| ≤ |f 0| + K * ‖Real.cos θ • x - Real.sin θ • y‖ := by
      simpa [hFdef, Real.norm_eq_abs] using
        norm_le_add_mul_norm_of_norm_fderiv_le hfdiff hK (Real.cos θ • x - Real.sin θ • y)
    have h3 : |F y| ≤ |f 0| + K * (‖x‖ + ‖y‖) := by
      refine le_trans h2 ?_
      gcongr
    have hy : 0 ≤ ‖y‖ := norm_nonneg y
    have hx : 0 ≤ ‖x‖ := norm_nonneg x
    have hf0 : 0 ≤ |f 0| := abs_nonneg _
    calc |F y| ≤ |f 0| + K * (‖x‖ + ‖y‖) := h3
      _ ≤ C * (1 + ‖y‖) ^ 1 := by
          rw [hC, pow_one]
          nlinarith [mul_nonneg hf0 hy, mul_nonneg (mul_nonneg hK0 hx) hy]
  have hgrowth' : ∀ y : H, ‖fderiv ℝ F y‖ ≤ C * (1 + ‖y‖) ^ 1 := by
    intro y
    have hy : 0 ≤ ‖y‖ := norm_nonneg y
    have hx : 0 ≤ ‖x‖ := norm_nonneg x
    have hf0 : 0 ≤ |f 0| := abs_nonneg _
    have h1 : ‖fderiv ℝ F y‖ ≤ K := by
      refine le_trans (hFderiv_le y) ?_
      calc |Real.sin θ| * K ≤ 1 * K := by
            gcongr
            exact abs_sin_le_one θ
        _ = K := one_mul K
    calc ‖fderiv ℝ F y‖ ≤ K := h1
      _ ≤ C * (1 + ‖y‖) ^ 1 := by
          rw [hC, pow_one]
          nlinarith [mul_nonneg hf0 hy, mul_nonneg (mul_nonneg hK0 hx) hy,
            mul_nonneg hK0 hy]
  have hFc1 : ContDiff ℝ 1 F := by
    have : ContDiff ℝ 1 fun z : H => Real.cos θ • x - Real.sin θ • z :=
      contDiff_const.sub (contDiff_id.const_smul _)
    exact hf.comp this
  have hFmeas : Measurable F := hFc1.continuous.measurable
  -- integration by parts
  have hIBP := integral_inner_mul_eq_integral_fderiv_covarianceOperator (μ := μ) hmean0 h F
    hFmeas hFc1 hC0 hgrowth hgrowth'
  have hLHS : (∫ y : H, f (Real.cos θ • x - Real.sin θ • y) * L y ∂μ)
      = ∫ y : H, ⟪y, h⟫ * F y ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hFdef, hLh y]
    ring
  rw [hLHS, hIBP, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [hFderiv, hA]

/-! ### The rotated slice -/

/-- **The slice bound.** Transporting the integration-by-parts step through the measure-preserving
rotation: for each fixed angle,

`|∫ f(x) · (Dg (rot θ p)) (rot⊥ θ p) d(μ ⊗ μ)| ≤ |sin θ| ‖C‖ Kf Kg`.

The rotation turns `x` into the affine function `cos θ • u - sin θ • v` of the rotated pair, which
is what makes the second variable enter the integrand only through the linear factor `(Dg u) v`,
so that a single Gaussian integration by parts applies. -/
private lemma integral_prod_mul_fderiv_gaussRot_eq
    (hmean0 : (∫ x : H, x ∂μ) = 0)
    {f g : H → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    {Kf Kg : ℝ} (hKf : ∀ x, ‖fderiv ℝ f x‖ ≤ Kf) (hKg : ∀ x, ‖fderiv ℝ g x‖ ≤ Kg) (θ : ℝ) :
    (∫ p : H × H,
        f p.1 * (fderiv ℝ g (gaussRot (H := H) θ p)) (gaussRotOrtho (H := H) θ p) ∂(μ.prod μ))
      = -Real.sin θ * ∫ p : H × H, (fderiv ℝ f (gaussRot (H := H) (-θ) p))
          (covarianceOperator μ (gradient g p.1)) ∂(μ.prod μ) := by
  classical
  have hKf0 : 0 ≤ Kf := le_trans (norm_nonneg _) (hKf 0)
  have hKg0 : 0 ≤ Kg := le_trans (norm_nonneg _) (hKg 0)
  have hcontDg : Continuous fun q : H × H => (fderiv ℝ g q.1 : H → ℝ) q.2 :=
    hg.continuous_fderiv_apply (by simp)
  set Φ : H × H → ℝ :=
    fun q => f (Real.cos θ • q.1 - Real.sin θ • q.2) * (fderiv ℝ g q.1) q.2 with hΦdef
  have hcontΦ : Continuous Φ := by
    refine Continuous.mul ?_ hcontDg
    exact hf.continuous.comp (by fun_prop)
  -- integrability of the rotated integrand
  have hIdLp2 : MemLp (id : H → H) 2 μ := IsGaussian.memLp_two_id (μ := μ)
  have hNormLp2 : MemLp (fun x : H => ‖x‖) 2 μ := by
    simpa using _root_.MeasureTheory.MemLp.norm hIdLp2
  have hn1 : MemLp (fun q : H × H => ‖q.1‖) 2 (μ.prod μ) :=
    _root_.MeasureTheory.MemLp.comp_fst hNormLp2 μ
  have hn2 : MemLp (fun q : H × H => ‖q.2‖) 2 (μ.prod μ) :=
    _root_.MeasureTheory.MemLp.comp_snd hNormLp2 μ
  have hsum : MemLp (fun q : H × H => ‖q.1‖ + ‖q.2‖) 2 (μ.prod μ) := by
    simpa [Pi.add_def] using _root_.MeasureTheory.MemLp.add hn1 hn2
  have hA : MemLp (fun q : H × H => |f 0| + Kf * (‖q.1‖ + ‖q.2‖)) 2 (μ.prod μ) := by
    have h1 : MemLp (fun _ : H × H => |f 0|) 2 (μ.prod μ) := memLp_const _
    have h2 : MemLp (fun q : H × H => Kf * (‖q.1‖ + ‖q.2‖)) 2 (μ.prod μ) :=
      _root_.MeasureTheory.MemLp.const_mul hsum Kf
    simpa [Pi.add_def] using _root_.MeasureTheory.MemLp.add h1 h2
  have hB : MemLp (fun q : H × H => Kg * ‖q.2‖) 2 (μ.prod μ) :=
    _root_.MeasureTheory.MemLp.const_mul hn2 Kg
  have hAB : Integrable (fun q : H × H =>
      (|f 0| + Kf * (‖q.1‖ + ‖q.2‖)) * (Kg * ‖q.2‖)) (μ.prod μ) := by
    simpa [Pi.mul_def] using _root_.MeasureTheory.MemLp.integrable_mul hA hB
  have hΦint : Integrable Φ (μ.prod μ) := by
    refine Integrable.mono' hAB hcontΦ.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    have hx : ‖Real.cos θ • q.1 - Real.sin θ • q.2‖ ≤ ‖q.1‖ + ‖q.2‖ := by
      refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_) <;>
        rw [norm_smul, Real.norm_eq_abs]
      · exact mul_le_of_le_one_left (norm_nonneg _) (abs_cos_le_one θ)
      · exact mul_le_of_le_one_left (norm_nonneg _) (abs_sin_le_one θ)
    have h1' : |f (Real.cos θ • q.1 - Real.sin θ • q.2)|
        ≤ |f 0| + Kf * ‖Real.cos θ • q.1 - Real.sin θ • q.2‖ := by
      simpa [Real.norm_eq_abs] using
        norm_le_add_mul_norm_of_norm_fderiv_le hf.differentiable_one hKf
          (Real.cos θ • q.1 - Real.sin θ • q.2)
    have h1 : |f (Real.cos θ • q.1 - Real.sin θ • q.2)| ≤ |f 0| + Kf * (‖q.1‖ + ‖q.2‖) := by
      refine le_trans h1' ?_
      gcongr
    have h2 : |(fderiv ℝ g q.1) q.2| ≤ Kg * ‖q.2‖ := by
      refine le_trans (by simpa [Real.norm_eq_abs] using
        ContinuousLinearMap.le_opNorm (fderiv ℝ g q.1) q.2) ?_
      gcongr
      exact hKg q.1
    calc ‖Φ q‖ = |f (Real.cos θ • q.1 - Real.sin θ • q.2)| * |(fderiv ℝ g q.1) q.2| := by
          rw [hΦdef, Real.norm_eq_abs, abs_mul]
      _ ≤ (|f 0| + Kf * (‖q.1‖ + ‖q.2‖)) * (Kg * ‖q.2‖) := by
          refine mul_le_mul h1 h2 (abs_nonneg _) ?_
          have : (0 : ℝ) ≤ Kf * (‖q.1‖ + ‖q.2‖) := by positivity
          have h0 : (0 : ℝ) ≤ |f 0| := abs_nonneg _
          linarith
  -- the rotation preserves `μ ⊗ μ`
  have hmap : (μ.prod μ).map (gaussRotMap (H := H) θ) = μ.prod μ :=
    map_gaussRotMap_prod (μ := μ) hmean0 θ
  have hchange : (∫ q : H × H, Φ q ∂(μ.prod μ))
      = ∫ p : H × H, Φ (gaussRotMap (H := H) θ p) ∂(μ.prod μ) := by
    have hmeasRot : AEMeasurable (gaussRotMap (H := H) θ) (μ.prod μ) := by fun_prop
    have hI := integral_map (μ := μ.prod μ) (φ := gaussRotMap (H := H) θ) (f := Φ)
      hmeasRot (by rw [hmap]; exact hcontΦ.aestronglyMeasurable)
    rwa [hmap] at hI
  have hstep1 : (∫ p : H × H,
        f p.1 * (fderiv ℝ g (gaussRot (H := H) θ p)) (gaussRotOrtho (H := H) θ p) ∂(μ.prod μ))
      = ∫ q : H × H, Φ q ∂(μ.prod μ) := by
    rw [hchange]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [hΦdef, gaussRotMap_apply, smul_gaussRot_sub_smul_gaussRotOrtho]
  have hstep2 : (∫ q : H × H, Φ q ∂(μ.prod μ))
      = ∫ x : H, (∫ y : H, f (Real.cos θ • x - Real.sin θ • y) * (fderiv ℝ g x) y ∂μ) ∂μ := by
    simpa [hΦdef] using integral_prod (μ := μ) (ν := μ) (f := Φ) hΦint
  rw [hstep1, hstep2]
  -- one integration by parts inside, then Fubini in the other direction
  have hinner : ∀ x : H,
      (∫ y : H, f (Real.cos θ • x - Real.sin θ • y) * (fderiv ℝ g x) y ∂μ)
        = -Real.sin θ * ∫ y : H, (fderiv ℝ f (Real.cos θ • x - Real.sin θ • y))
            (covarianceOperator μ (gradient g x)) ∂μ := fun x =>
    integral_affine_mul_dual_eq (μ := μ) hmean0 hf hKf θ x (fderiv ℝ g x)
  simp only [hinner]
  rw [integral_const_mul]
  congr 1
  have hrot : ∀ p : H × H,
      gaussRot (H := H) (-θ) p = Real.cos θ • p.1 - Real.sin θ • p.2 := by
    intro p
    simp [gaussRot, sub_eq_add_neg]
  set Ψ : H × H → ℝ :=
    fun p => (fderiv ℝ f (gaussRot (H := H) (-θ) p)) (covarianceOperator μ (gradient g p.1))
    with hΨdef
  have hcontΨ : Continuous Ψ := by
    have hDf : Continuous fun q : H × H => (fderiv ℝ f q.1 : H → ℝ) q.2 :=
      hf.continuous_fderiv_apply (by simp)
    have hrotc : Continuous fun p : H × H => gaussRot (H := H) (-θ) p := by
      simpa [gaussRot] using (by fun_prop : Continuous fun p : H × H =>
        Real.cos (-θ) • p.1 + Real.sin (-θ) • p.2)
    have hgradc : Continuous fun p : H × H => covarianceOperator μ (gradient g p.1) :=
      (covarianceOperator μ).continuous.comp ((ContDiff.continuous_gradient hg).comp continuous_fst)
    simpa [hΨdef, Function.comp_def] using hDf.comp (hrotc.prodMk hgradc)
  have hΨbound : ∀ p : H × H, ‖Ψ p‖ ≤ Kf * (‖covarianceOperator μ‖ * Kg) := by
    intro p
    calc ‖Ψ p‖ ≤ ‖fderiv ℝ f (gaussRot (H := H) (-θ) p)‖
          * ‖covarianceOperator μ (gradient g p.1)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ Kf * (‖covarianceOperator μ‖ * Kg) := by
          refine mul_le_mul (hKf _) ?_ (norm_nonneg _) hKf0
          calc ‖covarianceOperator μ (gradient g p.1)‖
              ≤ ‖covarianceOperator μ‖ * ‖gradient g p.1‖ :=
                (covarianceOperator μ).le_opNorm _
            _ ≤ ‖covarianceOperator μ‖ * Kg := by
                refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
                rw [norm_gradient]
                exact hKg _
  have hΨint : Integrable Ψ (μ.prod μ) :=
    Integrable.mono' (integrable_const (Kf * (‖covarianceOperator μ‖ * Kg)))
      hcontΨ.aestronglyMeasurable (Filter.Eventually.of_forall hΨbound)
  have := integral_prod (μ := μ) (ν := μ) (f := Ψ) hΨint
  rw [this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [hΨdef, hrot]

/-! ### Two bounds on the slice -/

/-- The slice bound in operator-norm form: `|slice θ| ≤ |sin θ| ‖C‖ Kf Kg`. -/
private lemma abs_integral_prod_mul_fderiv_gaussRot_le
    (hmean0 : (∫ x : H, x ∂μ) = 0)
    {f g : H → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    {Kf Kg : ℝ} (hKf : ∀ x, ‖fderiv ℝ f x‖ ≤ Kf) (hKg : ∀ x, ‖fderiv ℝ g x‖ ≤ Kg) (θ : ℝ) :
    |∫ p : H × H,
        f p.1 * (fderiv ℝ g (gaussRot (H := H) θ p)) (gaussRotOrtho (H := H) θ p) ∂(μ.prod μ)|
      ≤ |Real.sin θ| * (‖covarianceOperator μ‖ * (Kf * Kg)) := by
  have hKf0 : 0 ≤ Kf := le_trans (norm_nonneg _) (hKf 0)
  have hKg0 : 0 ≤ Kg := le_trans (norm_nonneg _) (hKg 0)
  rw [integral_prod_mul_fderiv_gaussRot_eq (μ := μ) hmean0 hf hg hKf hKg θ, abs_mul, abs_neg]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hbound : ∀ p : H × H,
      ‖(fderiv ℝ f (gaussRot (H := H) (-θ) p)) (covarianceOperator μ (∇ g p.1))‖
        ≤ ‖covarianceOperator μ‖ * (Kf * Kg) := by
    intro p
    have hg1 : ‖covarianceOperator μ (∇ g p.1)‖ ≤ ‖covarianceOperator μ‖ * Kg := by
      refine le_trans ((covarianceOperator μ).le_opNorm _) ?_
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [norm_gradient]
      exact hKg _
    calc ‖(fderiv ℝ f (gaussRot (H := H) (-θ) p)) (covarianceOperator μ (∇ g p.1))‖
        ≤ ‖fderiv ℝ f (gaussRot (H := H) (-θ) p)‖
            * ‖covarianceOperator μ (∇ g p.1)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ Kf * (‖covarianceOperator μ‖ * Kg) :=
          mul_le_mul (hKf _) hg1 (norm_nonneg _) hKf0
      _ = ‖covarianceOperator μ‖ * (Kf * Kg) := by ring
  calc |∫ p : H × H, (fderiv ℝ f (gaussRot (H := H) (-θ) p))
          (covarianceOperator μ (∇ g p.1)) ∂(μ.prod μ)|
      ≤ ∫ p : H × H, ‖(fderiv ℝ f (gaussRot (H := H) (-θ) p))
          (covarianceOperator μ (∇ g p.1))‖ ∂(μ.prod μ) := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ.prod μ)
          (fun p : H × H => (fderiv ℝ f (gaussRot (H := H) (-θ) p))
            (covarianceOperator μ (∇ g p.1)))
    _ ≤ ∫ _p : H × H, ‖covarianceOperator μ‖ * (Kf * Kg) ∂(μ.prod μ) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (integrable_const _) (Filter.Eventually.of_forall hbound)
    _ = ‖covarianceOperator μ‖ * (Kf * Kg) := by simp [probReal_univ]

/-- The slice bound in quadratic-form shape: `|slice θ| ≤ |sin θ| (λ Qf + Qg/λ)/2` for every
weight `λ > 0`, where `Qh = ∫ ⟪C ∇h, ∇h⟫ dμ`. This is the form that keeps the Poincaré inequality
sharp — Cauchy–Schwarz for the positive operator `C`
(`LinearMap.IsPositive.abs_inner_le_half_add_smul`) is applied *before* passing to operator norms,
and the rotation invariance of `μ ⊗ μ` identifies the law of `gaussRot (-θ)` with `μ`. Carrying the
weight through lets it be optimised at the very end. -/
private lemma abs_integral_prod_mul_fderiv_gaussRot_le_half_add
    (hmean0 : (∫ x : H, x ∂μ) = 0)
    {f g : H → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    {Kf Kg : ℝ} (hKf : ∀ x, ‖fderiv ℝ f x‖ ≤ Kf) (hKg : ∀ x, ‖fderiv ℝ g x‖ ≤ Kg)
    {lam : ℝ} (hlam : 0 < lam) (θ : ℝ) :
    |∫ p : H × H,
        f p.1 * (fderiv ℝ g (gaussRot (H := H) θ p)) (gaussRotOrtho (H := H) θ p) ∂(μ.prod μ)|
      ≤ |Real.sin θ| * ((lam * (∫ x : H, ⟪covarianceOperator μ (∇ g x), ∇ g x⟫ ∂μ)
          + (∫ x : H, ⟪covarianceOperator μ (∇ f x), ∇ f x⟫ ∂μ) / lam) / 2) := by
  classical
  have hKf0 : 0 ≤ Kf := le_trans (norm_nonneg _) (hKf 0)
  have hKg0 : 0 ≤ Kg := le_trans (norm_nonneg _) (hKg 0)
  have hpos : (covarianceOperator μ).toLinearMap.IsPositive := isPositive_covarianceOperator
  set qf : H → ℝ := fun w => ⟪covarianceOperator μ (∇ f w), ∇ f w⟫ with hqf
  set qg : H → ℝ := fun w => ⟪covarianceOperator μ (∇ g w), ∇ g w⟫ with hqg
  -- both quadratic forms are continuous and uniformly bounded
  have hcont_q : ∀ {h : H → ℝ} (_ : ContDiff ℝ 1 h),
      Continuous fun w : H => ⟪covarianceOperator μ (∇ h w), ∇ h w⟫ := by
    intro h hh
    exact (continuous_inner.comp
      (((covarianceOperator μ).continuous.comp (ContDiff.continuous_gradient hh)).prodMk
        (ContDiff.continuous_gradient hh)))
  have hbound_q : ∀ {h : H → ℝ} {K : ℝ} (_ : ∀ x, ‖fderiv ℝ h x‖ ≤ K) (w : H),
      ‖⟪covarianceOperator μ (∇ h w), ∇ h w⟫‖ ≤ ‖covarianceOperator μ‖ * K ^ 2 := by
    intro h K hK w
    have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0)
    have hnw : ‖∇ h w‖ ≤ K := by rw [norm_gradient]; exact hK w
    calc ‖⟪covarianceOperator μ (∇ h w), ∇ h w⟫‖
        ≤ ‖covarianceOperator μ (∇ h w)‖ * ‖∇ h w‖ := norm_inner_le_norm _ _
      _ ≤ (‖covarianceOperator μ‖ * ‖∇ h w‖) * ‖∇ h w‖ := by
          exact mul_le_mul_of_nonneg_right ((covarianceOperator μ).le_opNorm _) (norm_nonneg _)
      _ ≤ (‖covarianceOperator μ‖ * K) * K := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hnw (norm_nonneg _)) hnw (norm_nonneg _)
            (by positivity)
      _ = ‖covarianceOperator μ‖ * K ^ 2 := by ring
  have hcqf : Continuous qf := hcont_q hf
  have hcqg : Continuous qg := hcont_q hg
  have hiqf : Integrable qf μ :=
    Integrable.mono' (integrable_const (‖covarianceOperator μ‖ * Kf ^ 2))
      hcqf.aestronglyMeasurable (Filter.Eventually.of_forall (hbound_q hKf))
  have hiqg : Integrable qg μ :=
    Integrable.mono' (integrable_const (‖covarianceOperator μ‖ * Kg ^ 2))
      hcqg.aestronglyMeasurable (Filter.Eventually.of_forall (hbound_q hKg))
  -- the two marginal identities
  have hfst : ∀ q : H → ℝ, (∫ p : H × H, q p.1 ∂(μ.prod μ)) = ∫ x : H, q x ∂μ := by
    intro q
    simpa [probReal_univ] using integral_fun_fst (μ := μ) (ν := μ) (f := q)
  have hrot_law : (∫ p : H × H, qf (gaussRot (H := H) (-θ) p) ∂(μ.prod μ))
      = ∫ x : H, qf x ∂μ := by
    have hmap : (μ.prod μ).map (gaussRotMap (H := H) (-θ)) = μ.prod μ :=
      map_gaussRotMap_prod (μ := μ) hmean0 (-θ)
    have hI := integral_map (μ := μ.prod μ) (φ := gaussRotMap (H := H) (-θ))
      (f := fun q : H × H => qf q.1) (by fun_prop)
      (by rw [hmap]; exact (hcqf.comp continuous_fst).aestronglyMeasurable)
    rw [hmap] at hI
    rw [← hfst qf]
    simpa [gaussRotMap_apply] using hI.symm
  -- pointwise Cauchy–Schwarz for the positive operator `C`
  have hptwise : ∀ p : H × H,
      ‖(fderiv ℝ f (gaussRot (H := H) (-θ) p)) (covarianceOperator μ (∇ g p.1))‖
        ≤ (lam * qg p.1 + qf (gaussRot (H := H) (-θ) p) / lam) / 2 := by
    intro p
    have hrepr : (fderiv ℝ f (gaussRot (H := H) (-θ) p)) (covarianceOperator μ (∇ g p.1))
        = ⟪covarianceOperator μ (∇ g p.1), ∇ f (gaussRot (H := H) (-θ) p)⟫ := by
      rw [← inner_gradient_left, real_inner_comm]
    rw [hrepr, Real.norm_eq_abs]
    simpa [hqf, hqg] using LinearMap.IsPositive.abs_inner_le_half_add_smul hpos (∇ g p.1)
      (∇ f (gaussRot (H := H) (-θ) p)) hlam
  have h1 : Integrable (fun p : H × H => qg p.1) (μ.prod μ) := hiqg.comp_fst μ
  have h2 : Integrable (fun p : H × H => qf (gaussRot (H := H) (-θ) p)) (μ.prod μ) :=
    Integrable.mono' (integrable_const (‖covarianceOperator μ‖ * Kf ^ 2))
      ((hcqf.comp (continuous_gaussRot (H := H) (-θ))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => hbound_q hKf _)
  have hintsum : Integrable
      (fun p : H × H => (lam * qg p.1 + qf (gaussRot (H := H) (-θ) p) / lam) / 2) (μ.prod μ) :=
    (((h1.const_mul lam).add (h2.div_const lam)).div_const 2)
  rw [integral_prod_mul_fderiv_gaussRot_eq (μ := μ) hmean0 hf hg hKf hKg θ, abs_mul, abs_neg]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc |∫ p : H × H, (fderiv ℝ f (gaussRot (H := H) (-θ) p))
          (covarianceOperator μ (∇ g p.1)) ∂(μ.prod μ)|
      ≤ ∫ p : H × H, ‖(fderiv ℝ f (gaussRot (H := H) (-θ) p))
          (covarianceOperator μ (∇ g p.1))‖ ∂(μ.prod μ) := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ.prod μ)
          (fun p : H × H => (fderiv ℝ f (gaussRot (H := H) (-θ) p))
            (covarianceOperator μ (∇ g p.1)))
    _ ≤ ∫ p : H × H, (lam * qg p.1 + qf (gaussRot (H := H) (-θ) p) / lam) / 2 ∂(μ.prod μ) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          hintsum (Filter.Eventually.of_forall hptwise)
    _ = (lam * (∫ x : H, qg x ∂μ) + (∫ x : H, qf x ∂μ) / lam) / 2 := by
        rw [integral_div, integral_add (h1.const_mul lam) (h2.div_const lam),
          integral_const_mul, integral_div, hfst qg, hrot_law]

/-! ### From a slice bound to a covariance bound -/

/-- **The rotation argument, packaged.** Any bound `|slice θ| ≤ |sin θ| M` on the rotated integral
gives `|cov[f, g; μ]| ≤ M`, because `cov[f, g; μ]` is minus the integral of the slice over a
quarter turn and `∫₀^{π/2} sin θ dθ = 1`. The two instances used below differ only in how the
slice is bounded: by operator norms, or by the quadratic form of the covariance operator. -/
private lemma abs_covariance_le_of_slice_le
    {f g : H → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    {Kf Kg : ℝ} (hKf : ∀ x, ‖fderiv ℝ f x‖ ≤ Kf) (hKg : ∀ x, ‖fderiv ℝ g x‖ ≤ Kg) {M : ℝ}
    (hslice : ∀ θ : ℝ, |∫ p : H × H,
        f p.1 * (fderiv ℝ g (gaussRot (H := H) θ p)) (gaussRotOrtho (H := H) θ p) ∂(μ.prod μ)|
      ≤ |Real.sin θ| * M) :
    |cov[f, g; μ]| ≤ M := by
  classical
  have hKf0 : 0 ≤ Kf := le_trans (norm_nonneg _) (hKf 0)
  have hKg0 : 0 ≤ Kg := le_trans (norm_nonneg _) (hKg 0)
  set b : ℝ := Real.pi / 2 with hbdef
  have hb0 : (0 : ℝ) ≤ b := by rw [hbdef]; positivity
  set P : Measure (H × H) := μ.prod μ with hP
  set d : ℝ → H × H → ℝ :=
    fun θ p => (fderiv ℝ g (gaussRot (H := H) θ p)) (gaussRotOrtho (H := H) θ p) with hd
  -- `f` and `g` are square-integrable because their derivatives are bounded
  have hfLp : MemLp f 2 μ :=
    MemLp.of_norm_fderiv_le hf.differentiable_one hKf (IsGaussian.memLp_id μ 2 (by simp))
  have hgLp : MemLp g 2 μ :=
    MemLp.of_norm_fderiv_le hg.differentiable_one hKg (IsGaussian.memLp_id μ 2 (by simp))
  -- (1) the covariance is a single integral over `μ ⊗ μ`
  have hff : MemLp (fun p : H × H => f p.1) 2 P := _root_.MeasureTheory.MemLp.comp_fst hfLp μ
  have hgf : MemLp (fun p : H × H => g p.1) 2 P := _root_.MeasureTheory.MemLp.comp_fst hgLp μ
  have hgs : MemLp (fun p : H × H => g p.2) 2 P := _root_.MeasureTheory.MemLp.comp_snd hgLp μ
  have hI11 : Integrable (fun p : H × H => f p.1 * g p.1) P := by
    simpa [Pi.mul_def] using _root_.MeasureTheory.MemLp.integrable_mul hff hgf
  have hI12 : Integrable (fun p : H × H => f p.1 * g p.2) P := by
    simpa [Pi.mul_def] using _root_.MeasureTheory.MemLp.integrable_mul hff hgs
  have hcov : cov[f, g; μ] = ∫ p : H × H, f p.1 * (g p.1 - g p.2) ∂P := by
    rw [covariance_eq_sub hfLp hgLp]
    have e1 : (∫ p : H × H, f p.1 * g p.1 ∂P) = μ[f * g] := by
      have h := integral_fun_fst (μ := μ) (ν := μ) (f := fun x : H => f x * g x)
      simpa [hP, probReal_univ] using h
    have e2 : (∫ p : H × H, f p.1 * g p.2 ∂P) = μ[f] * μ[g] := by
      simpa [hP] using integral_prod_mul (μ := μ) (ν := μ) f g
    rw [← e1, ← e2, ← integral_sub hI11 hI12]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    ring
  -- (2) the fundamental theorem of calculus along the quarter turn
  have hDg : Continuous fun q : H × H => (fderiv ℝ g q.1 : H → ℝ) q.2 :=
    hg.continuous_fderiv_apply (by simp)
  have hcont_d : Continuous fun z : ℝ × (H × H) => d z.1 z.2 := by
    have hpair : Continuous fun z : ℝ × (H × H) =>
        (gaussRot (H := H) z.1 z.2, gaussRotOrtho (H := H) z.1 z.2) := by
      simpa [gaussRot, gaussRotOrtho] using (by fun_prop : Continuous fun z : ℝ × (H × H) =>
        (Real.cos z.1 • z.2.1 + Real.sin z.1 • z.2.2,
          -Real.sin z.1 • z.2.1 + Real.cos z.1 • z.2.2))
    simpa [hd, Function.comp_def] using hDg.comp hpair
  have hcont_dp : ∀ p : H × H, Continuous fun θ : ℝ => d θ p := by
    intro p
    simpa [Function.comp_def] using
      hcont_d.comp (by fun_prop : Continuous fun θ : ℝ => (θ, p))
  have hFTC : ∀ p : H × H, (∫ θ in (0 : ℝ)..b, d θ p) = g p.2 - g p.1 := by
    intro p
    have hgauss : Continuous fun t : ℝ => gaussRot (H := H) t p := by
      simpa [gaussRot] using (by fun_prop : Continuous fun t : ℝ =>
        Real.cos t • p.1 + Real.sin t • p.2)
    have hcont : ContinuousOn (fun θ : ℝ => g (gaussRot (H := H) θ p)) (Set.Icc 0 b) := by
      simpa [Function.comp_def] using (hg.continuous.comp hgauss).continuousOn
    have hder : ∀ θ ∈ Set.Ioo (0 : ℝ) b,
        HasDerivAt (fun t : ℝ => g (gaussRot (H := H) t p)) (d θ p) θ := by
      intro θ _
      simpa [hd] using hasDerivAt_comp_gaussRot (H := H) (f := g) hg θ p
    have hint : IntervalIntegrable (fun θ : ℝ => d θ p) (volume : Measure ℝ) 0 b :=
      (hcont_dp p).intervalIntegrable _ _
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb0 hcont hder hint
    simpa [hbdef, gaussRot, Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two,
      Real.sin_pi_div_two] using h
  -- (3) joint integrability in `(θ, p)`, for the exchange of the two integrals
  have hvol_u : (volume (Set.uIoc (0 : ℝ) b)) < ∞ := by simp [volume_uIoc]
  have : Fact ((volume : Measure ℝ) (Set.uIoc (0 : ℝ) b) < ∞) := ⟨hvol_u⟩
  have hfinite : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) b)) := by infer_instance
  have hIdLp2 : MemLp (id : H → H) 2 μ := IsGaussian.memLp_two_id (μ := μ)
  have hNormLp2 : MemLp (fun x : H => ‖x‖) 2 μ := by
    simpa using _root_.MeasureTheory.MemLp.norm hIdLp2
  have hn1 : MemLp (fun q : H × H => ‖q.1‖) 2 P := _root_.MeasureTheory.MemLp.comp_fst hNormLp2 μ
  have hn2 : MemLp (fun q : H × H => ‖q.2‖) 2 P := _root_.MeasureTheory.MemLp.comp_snd hNormLp2 μ
  have hA : MemLp (fun q : H × H => |f 0| + Kf * ‖q.1‖) 2 P := by
    have h1 : MemLp (fun _ : H × H => |f 0|) 2 P := memLp_const _
    have h2 : MemLp (fun q : H × H => Kf * ‖q.1‖) 2 P :=
      _root_.MeasureTheory.MemLp.const_mul hn1 Kf
    simpa [Pi.add_def] using _root_.MeasureTheory.MemLp.add h1 h2
  have hBsum : MemLp (fun q : H × H => Kg * (‖q.1‖ + ‖q.2‖)) 2 P := by
    have hsum : MemLp (fun q : H × H => ‖q.1‖ + ‖q.2‖) 2 P := by
      simpa [Pi.add_def] using _root_.MeasureTheory.MemLp.add hn1 hn2
    exact _root_.MeasureTheory.MemLp.const_mul hsum Kg
  have hG0 : Integrable
      (fun q : H × H => (|f 0| + Kf * ‖q.1‖) * (Kg * (‖q.1‖ + ‖q.2‖))) P := by
    simpa [Pi.mul_def] using _root_.MeasureTheory.MemLp.integrable_mul hA hBsum
  have hDbound : ∀ (θ : ℝ) (p : H × H),
      ‖f p.1 * d θ p‖ ≤ (|f 0| + Kf * ‖p.1‖) * (Kg * (‖p.1‖ + ‖p.2‖)) := by
    intro θ p
    have h1 : |f p.1| ≤ |f 0| + Kf * ‖p.1‖ := by
      simpa [Real.norm_eq_abs] using
        norm_le_add_mul_norm_of_norm_fderiv_le hf.differentiable_one hKf p.1
    have h2 : |d θ p| ≤ Kg * (‖p.1‖ + ‖p.2‖) := by
      have hle : |d θ p| ≤ ‖fderiv ℝ g (gaussRot (H := H) θ p)‖
          * ‖gaussRotOrtho (H := H) θ p‖ := by
        simpa [hd, Real.norm_eq_abs] using
          ContinuousLinearMap.le_opNorm (fderiv ℝ g (gaussRot (H := H) θ p))
            (gaussRotOrtho (H := H) θ p)
      refine le_trans hle ?_
      exact mul_le_mul (hKg _) (norm_gaussRotOrtho_le (H := H) θ p) (norm_nonneg _) hKg0
    calc ‖f p.1 * d θ p‖ = |f p.1| * |d θ p| := by rw [Real.norm_eq_abs, abs_mul]
      _ ≤ (|f 0| + Kf * ‖p.1‖) * (Kg * (‖p.1‖ + ‖p.2‖)) := by
          refine mul_le_mul h1 h2 (abs_nonneg _) ?_
          have : (0 : ℝ) ≤ Kf * ‖p.1‖ := by positivity
          have h0 : (0 : ℝ) ≤ |f 0| := abs_nonneg _
          linarith
  have hInt_uncurry : Integrable
      (Function.uncurry fun θ : ℝ => fun p : H × H => f p.1 * d θ p)
      ((volume.restrict (Set.uIoc (0 : ℝ) b)).prod P) := by
    refine Integrable.mono' (g := fun z : ℝ × (H × H) =>
      (|f 0| + Kf * ‖z.2.1‖) * (Kg * (‖z.2.1‖ + ‖z.2.2‖))) ?_ ?_
      (Filter.Eventually.of_forall fun z => ?_)
    · exact hG0.comp_snd (volume.restrict (Set.uIoc (0 : ℝ) b))
    · have hcont : Continuous
          (Function.uncurry fun θ : ℝ => fun p : H × H => f p.1 * d θ p) := by
        have : Continuous fun z : ℝ × (H × H) => f z.2.1 * d z.1 z.2 :=
          (hf.continuous.comp (by fun_prop)).mul hcont_d
        simpa [Function.uncurry_def] using this
      exact hcont.aestronglyMeasurable
    · simpa [Function.uncurry_def] using hDbound z.1 z.2
  -- (4) exchange the two integrals and bound each slice
  have hswap : (∫ θ in (0 : ℝ)..b, ∫ p : H × H, f p.1 * d θ p ∂P)
      = ∫ p : H × H, (∫ θ in (0 : ℝ)..b, f p.1 * d θ p) ∂P :=
    intervalIntegral_integral_swap hInt_uncurry
  have hpt : ∀ p : H × H,
      f p.1 * (g p.1 - g p.2) = -(∫ θ in (0 : ℝ)..b, f p.1 * d θ p) := by
    intro p
    rw [intervalIntegral.integral_const_mul, hFTC p]
    ring
  have hcov3 : cov[f, g; μ] = -∫ θ in (0 : ℝ)..b, (∫ p : H × H, f p.1 * d θ p ∂P) := by
    rw [hcov, hswap, ← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hIθ : Integrable (fun θ : ℝ => ∫ p : H × H, f p.1 * d θ p ∂P)
      (volume.restrict (Set.uIoc (0 : ℝ) b)) := hInt_uncurry.integral_prod_left
  have hIIθ : IntervalIntegrable (fun θ : ℝ => ∫ p : H × H, f p.1 * d θ p ∂P)
      (volume : Measure ℝ) 0 b := by
    rw [intervalIntegrable_iff]
    exact hIθ
  have hsinInt : IntervalIntegrable (fun θ : ℝ => Real.sin θ * M)
      (volume : Measure ℝ) 0 b := (Real.continuous_sin.mul continuous_const).intervalIntegrable _ _
  have hsliceIcc : ∀ θ ∈ Set.Icc (0 : ℝ) b,
      |∫ p : H × H, f p.1 * d θ p ∂P| ≤ Real.sin θ * M := by
    intro θ hθ
    have hπ : θ ≤ Real.pi := le_trans hθ.2 (by rw [hbdef]; linarith [Real.pi_pos])
    have hsin : |Real.sin θ| = Real.sin θ :=
      abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hπ)
    have h := hslice θ
    rw [hsin] at h
    simpa [hd, hP] using h
  calc |cov[f, g; μ]| = |∫ θ in (0 : ℝ)..b, (∫ p : H × H, f p.1 * d θ p ∂P)| := by
        rw [hcov3, abs_neg]
    _ ≤ ∫ θ in (0 : ℝ)..b, |∫ p : H × H, f p.1 * d θ p ∂P| :=
        intervalIntegral.abs_integral_le_integral_abs hb0
    _ ≤ ∫ θ in (0 : ℝ)..b, Real.sin θ * M :=
        intervalIntegral.integral_mono_on hb0 hIIθ.abs hsinInt hsliceIcc
    _ = M := by
        rw [intervalIntegral.integral_mul_const, integral_sin, hbdef]
        simp

/-! ### The covariance and Poincaré inequalities -/

/-- **The Gaussian covariance inequality.** For a centered Gaussian measure `μ` on a real Hilbert
space and `C¹` functionals `f`, `g` with `‖Df‖ ≤ Kf` and `‖Dg‖ ≤ Kg`,

`|cov[f, g; μ]| ≤ ‖covarianceOperator μ‖ * (Kf * Kg)`.

The constant is `1`: it is the value of `∫₀^{π/2} sin θ dθ`, the weight produced by the chain rule
along the quarter turn. -/
theorem abs_covariance_le_opNorm_covarianceOperator_mul
    (hmean0 : (∫ x : H, x ∂μ) = 0)
    {f g : H → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    {Kf Kg : ℝ} (hKf : ∀ x, ‖fderiv ℝ f x‖ ≤ Kf) (hKg : ∀ x, ‖fderiv ℝ g x‖ ≤ Kg) :
    |cov[f, g; μ]| ≤ ‖covarianceOperator μ‖ * (Kf * Kg) :=
  abs_covariance_le_of_slice_le (μ := μ) hf hg hKf hKg
    (abs_integral_prod_mul_fderiv_gaussRot_le (μ := μ) hmean0 hf hg hKf hKg)

omit [SecondCountableTopology H] [IsGaussian μ] in
/-- The Dirichlet energy of a function against the covariance operator is nonnegative: the
covariance operator is positive. -/
lemma integral_inner_covarianceOperator_gradient_nonneg (f : H → ℝ) :
    0 ≤ ∫ x : H, ⟪covarianceOperator μ (∇ f x), ∇ f x⟫ ∂μ :=
  integral_nonneg fun x =>
    LinearMap.IsPositive.inner_nonneg_left isPositive_covarianceOperator (∇ f x)

/-- **The Gaussian covariance inequality in weighted quadratic-form shape.** With
`Q h = ∫ ⟪C ∇h, ∇h⟫ dμ` the Dirichlet energy of `h` against the covariance operator, for every
weight `λ > 0`,

`|cov[f, g; μ]| ≤ (λ · Q f + Q g / λ) / 2`.

Optimising the weight gives the Cauchy–Schwarz form
`abs_covariance_le_sqrt_mul_sqrt_integral_inner_covarianceOperator`; the weight-`1` case is
`abs_covariance_le_half_add_integral_inner_covarianceOperator`. -/
theorem abs_covariance_le_half_add_smul_integral_inner_covarianceOperator
    (hmean0 : (∫ x : H, x ∂μ) = 0)
    {f g : H → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    {Kf Kg : ℝ} (hKf : ∀ x, ‖fderiv ℝ f x‖ ≤ Kf) (hKg : ∀ x, ‖fderiv ℝ g x‖ ≤ Kg)
    {lam : ℝ} (hlam : 0 < lam) :
    |cov[f, g; μ]| ≤ (lam * (∫ x : H, ⟪covarianceOperator μ (∇ f x), ∇ f x⟫ ∂μ)
        + (∫ x : H, ⟪covarianceOperator μ (∇ g x), ∇ g x⟫ ∂μ) / lam) / 2 := by
  have h := abs_covariance_le_of_slice_le (μ := μ) hf hg hKf hKg
    (abs_integral_prod_mul_fderiv_gaussRot_le_half_add (μ := μ) hmean0 hf hg hKf hKg
      (lam := lam⁻¹) (by positivity))
  have hrw : (lam⁻¹ * (∫ x : H, ⟪covarianceOperator μ (∇ g x), ∇ g x⟫ ∂μ)
        + (∫ x : H, ⟪covarianceOperator μ (∇ f x), ∇ f x⟫ ∂μ) / lam⁻¹) / 2
      = (lam * (∫ x : H, ⟪covarianceOperator μ (∇ f x), ∇ f x⟫ ∂μ)
        + (∫ x : H, ⟪covarianceOperator μ (∇ g x), ∇ g x⟫ ∂μ) / lam) / 2 := by
    field_simp
    ring
  linarith [h, hrw.ge, hrw.le]

/-- **The Gaussian covariance inequality**, in its sharpest form: with
`Q h = ∫ ⟪C ∇h, ∇h⟫ dμ`,

`|cov[f, g; μ]| ≤ √(Q f) · √(Q g)`.

This is Cauchy–Schwarz for the Dirichlet form of the covariance operator, obtained from the
weighted form by optimising the weight (`Real.le_sqrt_mul_sqrt_of_forall_pos`). It is strictly
sharper than the operator-norm form whenever the gradients are not aligned with the top eigenspace
of `C`: `Q h ≤ ‖C‖ K²`, but for the free energy of a mean-field model `Q h` is a replica overlap,
of order `N`, while `‖C‖` is of the order of the number of configurations. -/
theorem abs_covariance_le_sqrt_mul_sqrt_integral_inner_covarianceOperator
    (hmean0 : (∫ x : H, x ∂μ) = 0)
    {f g : H → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    {Kf Kg : ℝ} (hKf : ∀ x, ‖fderiv ℝ f x‖ ≤ Kf) (hKg : ∀ x, ‖fderiv ℝ g x‖ ≤ Kg) :
    |cov[f, g; μ]|
      ≤ Real.sqrt (∫ x : H, ⟪covarianceOperator μ (∇ f x), ∇ f x⟫ ∂μ)
          * Real.sqrt (∫ x : H, ⟪covarianceOperator μ (∇ g x), ∇ g x⟫ ∂μ) := by
  refine Real.le_sqrt_mul_sqrt_of_forall_pos
    (integral_inner_covarianceOperator_gradient_nonneg (μ := μ) f)
    (integral_inner_covarianceOperator_gradient_nonneg (μ := μ) g) fun lam hlam => ?_
  have := abs_covariance_le_half_add_smul_integral_inner_covarianceOperator
    (μ := μ) hmean0 hf hg hKf hKg hlam
  linarith

/-- The Gaussian covariance inequality in unweighted quadratic-form shape:
`|cov[f, g; μ]| ≤ (Q f + Q g) / 2`, the weight-`1` case. -/
theorem abs_covariance_le_half_add_integral_inner_covarianceOperator
    (hmean0 : (∫ x : H, x ∂μ) = 0)
    {f g : H → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    {Kf Kg : ℝ} (hKf : ∀ x, ‖fderiv ℝ f x‖ ≤ Kf) (hKg : ∀ x, ‖fderiv ℝ g x‖ ≤ Kg) :
    |cov[f, g; μ]| ≤ ((∫ x : H, ⟪covarianceOperator μ (∇ f x), ∇ f x⟫ ∂μ)
        + ∫ x : H, ⟪covarianceOperator μ (∇ g x), ∇ g x⟫ ∂μ) / 2 := by
  simpa using abs_covariance_le_half_add_smul_integral_inner_covarianceOperator
    (μ := μ) hmean0 hf hg hKf hKg (lam := 1) one_pos

/-- **The Gaussian Poincaré inequality**, in its sharp form: if `μ` is a centered Gaussian measure
on a real Hilbert space and `f` is `C¹` with `‖fderiv ℝ f x‖ ≤ K`, then

`Var[f; μ] ≤ ∫ ⟪covarianceOperator μ (∇ f x), ∇ f x⟫ ∂μ`.

The bounded-derivative hypothesis is only used to make the integration by parts legitimate; the
conclusion involves no constant and no norm, only the Dirichlet energy of `f` against the
covariance. It is the diagonal `g = f` of
`abs_covariance_le_sqrt_mul_sqrt_integral_inner_covarianceOperator`. -/
theorem variance_le_integral_inner_covarianceOperator_gradient
    (hmean0 : (∫ x : H, x ∂μ) = 0) {f : H → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hderiv : ∀ x, ‖fderiv ℝ f x‖ ≤ K) :
    Var[f; μ] ≤ ∫ x : H, ⟪covarianceOperator μ (∇ f x), ∇ f x⟫ ∂μ := by
  have hself : cov[f, f; μ] = Var[f; μ] :=
    covariance_self hf.continuous.measurable.aemeasurable
  have h := abs_covariance_le_sqrt_mul_sqrt_integral_inner_covarianceOperator
    (μ := μ) hmean0 hf hf hderiv hderiv
  rw [hself] at h
  have hQ : 0 ≤ ∫ x : H, ⟪covarianceOperator μ (∇ f x), ∇ f x⟫ ∂μ :=
    integral_inner_covarianceOperator_gradient_nonneg (μ := μ) f
  calc Var[f; μ] ≤ |Var[f; μ]| := le_abs_self _
    _ ≤ Real.sqrt (∫ x : H, ⟪covarianceOperator μ (∇ f x), ∇ f x⟫ ∂μ)
          * Real.sqrt (∫ x : H, ⟪covarianceOperator μ (∇ f x), ∇ f x⟫ ∂μ) := h
    _ = ∫ x : H, ⟪covarianceOperator μ (∇ f x), ∇ f x⟫ ∂μ := Real.mul_self_sqrt hQ

/-- The Gaussian Poincaré inequality in operator-norm form:
`Var[f; μ] ≤ ‖covarianceOperator μ‖ * K²`. The diagonal of
`abs_covariance_le_opNorm_covarianceOperator_mul`; weaker than
`variance_le_integral_inner_covarianceOperator_gradient`, but stated in terms of `K` alone. -/
theorem variance_le_opNorm_covarianceOperator_mul_sq
    (hmean0 : (∫ x : H, x ∂μ) = 0) {f : H → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hderiv : ∀ x, ‖fderiv ℝ f x‖ ≤ K) :
    Var[f; μ] ≤ ‖covarianceOperator μ‖ * K ^ 2 := by
  have hself : cov[f, f; μ] = Var[f; μ] :=
    covariance_self hf.continuous.measurable.aemeasurable
  have h := abs_covariance_le_opNorm_covarianceOperator_mul (μ := μ) hmean0 hf hf hderiv hderiv
  rw [hself] at h
  calc Var[f; μ] ≤ |Var[f; μ]| := le_abs_self _
    _ ≤ ‖covarianceOperator μ‖ * (K * K) := h
    _ = ‖covarianceOperator μ‖ * K ^ 2 := by ring

end

end IsGaussian

end ProbabilityTheory
