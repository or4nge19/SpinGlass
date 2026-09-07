/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Common.Mathlib.Analysis.Calculus.FDerivCLMComp

/-!
# Log-sum-exp, softmax, and their Fréchet calculus

For a finite index type `ι`, the **log-sum-exp** function

`logSumExp x = log (∑ i, exp (x i))`

on `EuclideanSpace ℝ ι` is the smooth convex approximation to `max i, x i`; it is the log-partition
function of the finite index set and the convex conjugate of negative entropy. Its gradient is the
**softmax** probability vector

`softmax x i = exp (x i) / ∑ j, exp (x j)`

and its Hessian is the covariance form of `softmax x`:

`D² logSumExp x u v = ∑ i, p i * u i * v i - (∑ i, p i * u i) * (∑ i, p i * v i)`, `p = softmax x`.

Both derivatives are bounded *uniformly in `x`*: `‖D logSumExp‖ ≤ 1` and `‖D² logSumExp‖ ≤ 2`.
Together with the sandwich `max i, x i ≤ logSumExp x ≤ (max i, x i) + log (card ι)` this makes
`λ⁻¹ • logSumExp (λ • ·)` a family of smooth functions of temperate-in-`x` growth converging
uniformly to the maximum, which is what comparison arguments for Gaussian suprema (Slepian,
Sudakov–Fernique) and the free-energy calculus of statistical mechanics both consume.

## Main definitions

- `Real.expSum`, `Real.logSumExp`, `Real.softmax`.

## Main statements

- `Real.contDiff_logSumExp`: `logSumExp` is `C^∞`.
- `Real.fderiv_logSumExp_apply`: the gradient is `softmax`.
- `Real.fderiv_softmax_apply`, `Real.fderiv_fderiv_logSumExp_apply`: the Hessian is the `softmax`
  covariance form.
- `Real.norm_fderiv_logSumExp_le`, `Real.norm_fderiv_fderiv_logSumExp_le`: `≤ 1` and `≤ 2`,
  uniformly.
- `Real.le_logSumExp`, `Real.logSumExp_le_add_log_card`, `Real.abs_logSumExp_le`.
-/

open scoped BigOperators ContDiff

noncomputable section

namespace Real

variable {ι : Type*} [Fintype ι]

/-- The exponential sum `∑ i, exp (x i)`: the partition function of `x`. -/
def expSum (x : EuclideanSpace ℝ ι) : ℝ := ∑ i, Real.exp (x i)

/-- Log-sum-exp: `log (∑ i, exp (x i))`, the smooth approximation to `max i, x i`. -/
def logSumExp (x : EuclideanSpace ℝ ι) : ℝ := Real.log (expSum x)

/-- Softmax: the probability vector `exp (x i) / ∑ j, exp (x j)`, the gradient of `logSumExp`. -/
def softmax (x : EuclideanSpace ℝ ι) (i : ι) : ℝ := Real.exp (x i) / expSum x

variable [Nonempty ι]

lemma expSum_pos (x : EuclideanSpace ℝ ι) : 0 < expSum x :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

lemma expSum_ne_zero (x : EuclideanSpace ℝ ι) : expSum x ≠ 0 := ne_of_gt (expSum_pos x)

lemma softmax_pos (x : EuclideanSpace ℝ ι) (i : ι) : 0 < softmax x i :=
  div_pos (Real.exp_pos _) (expSum_pos x)

lemma softmax_nonneg (x : EuclideanSpace ℝ ι) (i : ι) : 0 ≤ softmax x i :=
  le_of_lt (softmax_pos x i)

lemma sum_softmax (x : EuclideanSpace ℝ ι) : (∑ i, softmax x i) = 1 := by
  have h : (∑ i, softmax x i) = expSum x / expSum x := by
    simp only [softmax, ← Finset.sum_div, expSum]
  rw [h, div_self (expSum_ne_zero x)]

lemma softmax_le_one (x : EuclideanSpace ℝ ι) (i : ι) : softmax x i ≤ 1 := by
  have h := sum_softmax x
  have hle : softmax x i ≤ ∑ j, softmax x j :=
    Finset.single_le_sum (f := fun j => softmax x j)
      (fun j _ => softmax_nonneg x j) (Finset.mem_univ i)
  rwa [h] at hle

omit [Nonempty ι] in
lemma softmax_eq (x : EuclideanSpace ℝ ι) (i : ι) :
    softmax x i = Real.exp (x i) / expSum x := rfl

/-! ### Smoothness -/

/-- Evaluation at a coordinate, as a continuous linear functional. -/
abbrev evalCLM (i : ι) : EuclideanSpace ℝ ι →L[ℝ] ℝ :=
  PiLp.proj (p := (2 : ENNReal)) (fun _ : ι => ℝ) i

omit [Nonempty ι] in
lemma hasFDerivAt_eval (x : EuclideanSpace ℝ ι) (i : ι) :
    HasFDerivAt (fun y : EuclideanSpace ℝ ι => y i) (evalCLM (ι := ι) i) x := by
  simpa [evalCLM] using
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := (2 : ENNReal)) (E := fun _ : ι => ℝ) (f := x) i)

omit [Nonempty ι] in
lemma contDiff_exp_eval (i : ι) :
    ContDiff ℝ (∞) (fun x : EuclideanSpace ℝ ι => Real.exp (x i)) := by
  simpa [Function.comp_def] using (contDiff_exp.comp (evalCLM (ι := ι) i).contDiff)

omit [Nonempty ι] in
/-- The partition function `expSum` is `C^∞`. -/
lemma contDiff_expSum : ContDiff ℝ (∞) (fun x : EuclideanSpace ℝ ι => expSum x) := by
  simpa [expSum] using
    (ContDiff.sum (𝕜 := ℝ) (n := (∞)) (s := (Finset.univ : Finset ι))
      (f := fun i : ι => fun x : EuclideanSpace ℝ ι => Real.exp (x i))
      (fun i _hi => contDiff_exp_eval (ι := ι) i))

/-- Log-sum-exp is `C^∞`. -/
lemma contDiff_logSumExp : ContDiff ℝ (∞) (fun x : EuclideanSpace ℝ ι => logSumExp x) := by
  simpa [logSumExp] using
    (contDiff_expSum (ι := ι)).log (fun x => expSum_ne_zero x)

/-- Softmax is `C^∞`. -/
lemma contDiff_softmax (i : ι) :
    ContDiff ℝ (∞) (fun x : EuclideanSpace ℝ ι => softmax x i) := by
  simpa [softmax] using
    (contDiff_exp_eval (ι := ι) i).fun_div (contDiff_expSum (ι := ι))
      (fun x => expSum_ne_zero x)

/-! ### First derivative: the gradient is `softmax` -/

/-- The gradient of `logSumExp` at `x`, as a continuous linear functional: the `softmax` vector. -/
def gradLogSumExp (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι →L[ℝ] ℝ :=
  ∑ i, softmax x i • evalCLM (ι := ι) i

omit [Nonempty ι] in
@[simp] lemma gradLogSumExp_apply (x v : EuclideanSpace ℝ ι) :
    gradLogSumExp x v = ∑ i, softmax x i * v i := by
  simp [gradLogSumExp, sum_apply, evalCLM, smul_apply, smul_eq_mul]

omit [Nonempty ι] in
lemma hasFDerivAt_expSum (x : EuclideanSpace ℝ ι) :
    HasFDerivAt (fun y : EuclideanSpace ℝ ι => expSum y)
      (∑ i, Real.exp (x i) • evalCLM (ι := ι) i) x := by
  have hterm : ∀ i : ι,
      HasFDerivAt (fun y : EuclideanSpace ℝ ι => Real.exp (y i))
        (Real.exp (x i) • evalCLM (ι := ι) i) x := by
    intro i
    have hexp : HasDerivAt Real.exp (Real.exp (x i)) (x i) := Real.hasDerivAt_exp (x i)
    simpa [Function.comp_def] using
      (HasDerivAt.comp_hasFDerivAt (x := x) hexp (hasFDerivAt_eval (ι := ι) x i))
  simpa [expSum] using
    (HasFDerivAt.fun_sum (u := (Finset.univ : Finset ι))
      (A := fun i : ι => fun y : EuclideanSpace ℝ ι => Real.exp (y i))
      (A' := fun i : ι => Real.exp (x i) • evalCLM (ι := ι) i) (x := x)
      (fun i _hi => hterm i))

lemma hasFDerivAt_logSumExp (x : EuclideanSpace ℝ ι) :
    HasFDerivAt (fun y : EuclideanSpace ℝ ι => logSumExp y) (gradLogSumExp x) x := by
  have hlog := (hasFDerivAt_expSum (ι := ι) x).log (expSum_ne_zero x)
  refine hlog.congr_fderiv ?_
  rw [gradLogSumExp, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, softmax_eq, div_eq_mul_inv, mul_comm]

lemma fderiv_logSumExp_eq (x : EuclideanSpace ℝ ι) :
    fderiv ℝ (fun y : EuclideanSpace ℝ ι => logSumExp y) x = gradLogSumExp x :=
  (hasFDerivAt_logSumExp (ι := ι) x).fderiv

lemma fderiv_logSumExp_apply (x v : EuclideanSpace ℝ ι) :
    fderiv ℝ (fun y : EuclideanSpace ℝ ι => logSumExp y) x v = ∑ i, softmax x i * v i := by
  rw [fderiv_logSumExp_eq, gradLogSumExp_apply]

/-! ### Second derivative: the Hessian is the `softmax` covariance -/

lemma differentiableAt_softmax (x : EuclideanSpace ℝ ι) (i : ι) :
    DifferentiableAt ℝ (fun y : EuclideanSpace ℝ ι => softmax y i) x :=
  ((contDiff_softmax (ι := ι) i).differentiable (by simp)).differentiableAt

omit [Nonempty ι] in
lemma hasFDerivAt_exp_eval (x : EuclideanSpace ℝ ι) (i : ι) :
    HasFDerivAt (fun y : EuclideanSpace ℝ ι => Real.exp (y i))
      (Real.exp (x i) • evalCLM (ι := ι) i) x := by
  have hexp : HasDerivAt Real.exp (Real.exp (x i)) (x i) := Real.hasDerivAt_exp (x i)
  simpa [Function.comp_def] using
    (HasDerivAt.comp_hasFDerivAt (x := x) hexp (hasFDerivAt_eval (ι := ι) x i))

lemma hasFDerivAt_inv_expSum (x : EuclideanSpace ℝ ι) :
    HasFDerivAt (fun y : EuclideanSpace ℝ ι => (expSum y)⁻¹)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-((expSum x) ^ 2)⁻¹)).comp
        (∑ j, Real.exp (x j) • evalCLM (ι := ι) j)) x := by
  have hInv : HasFDerivAt (fun z : ℝ => z⁻¹)
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-((expSum x) ^ 2)⁻¹) : ℝ →L[ℝ] ℝ)
      (expSum x) := hasFDerivAt_inv (𝕜 := ℝ) (expSum_ne_zero x)
  simpa [Function.comp_def] using hInv.comp (x := x) (hasFDerivAt_expSum (ι := ι) x)

/-- `∂_j softmax x i = softmax x i * (δᵢⱼ - softmax x j)`, in directional form. -/
lemma fderiv_softmax_apply (x v : EuclideanSpace ℝ ι) (i : ι) :
    fderiv ℝ (fun y : EuclideanSpace ℝ ι => softmax y i) x v
      = softmax x i * (v i - ∑ j, softmax x j * v j) := by
  have hZ : expSum x ≠ 0 := expSum_ne_zero x
  have hmul := (hasFDerivAt_exp_eval (ι := ι) x i).fun_mul (hasFDerivAt_inv_expSum (ι := ι) x)
  have hs : (fun y : EuclideanSpace ℝ ι => softmax y i)
      = fun y : EuclideanSpace ℝ ι => Real.exp (y i) * (expSum y)⁻¹ := by
    funext y
    rw [softmax_eq, div_eq_mul_inv]
  have hsum : (∑ j, Real.exp (x j) • evalCLM (ι := ι) j) v = ∑ j, Real.exp (x j) * v j := by
    simp [sum_apply, evalCLM, smul_apply, smul_eq_mul]
  have hps : (∑ j, softmax x j * v j) = (expSum x)⁻¹ * ∑ j, Real.exp (x j) * v j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [softmax_eq, div_eq_mul_inv]
      ring
  rw [hs, hmul.fderiv, hps, softmax_eq]
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, smul_eq_mul, hsum,
    evalCLM, PiLp.proj_apply]
  field_simp
  ring

/-- The Hessian form of `logSumExp` at `x`: the covariance bilinear form of `softmax x`. -/
def logSumExpHess (x u v : EuclideanSpace ℝ ι) : ℝ :=
  (∑ i, softmax x i * u i * v i)
    - (∑ i, softmax x i * u i) * (∑ i, softmax x i * v i)

lemma hasFDerivAt_gradLogSumExp (x : EuclideanSpace ℝ ι) :
    HasFDerivAt (fun y : EuclideanSpace ℝ ι => gradLogSumExp y)
      (∑ i, (fderiv ℝ (fun y : EuclideanSpace ℝ ι => softmax y i) x).smulRight
        (evalCLM (ι := ι) i)) x := by
  have hterm : ∀ i : ι,
      HasFDerivAt (fun y : EuclideanSpace ℝ ι => softmax y i • evalCLM (ι := ι) i)
        ((fderiv ℝ (fun y : EuclideanSpace ℝ ι => softmax y i) x).smulRight
          (evalCLM (ι := ι) i)) x :=
    fun i => (differentiableAt_softmax (ι := ι) x i).hasFDerivAt.smul_const (evalCLM (ι := ι) i)
  simpa [gradLogSumExp] using
    (HasFDerivAt.fun_sum (u := (Finset.univ : Finset ι))
      (A := fun i : ι => fun y : EuclideanSpace ℝ ι => softmax y i • evalCLM (ι := ι) i)
      (A' := fun i : ι =>
        (fderiv ℝ (fun y : EuclideanSpace ℝ ι => softmax y i) x).smulRight (evalCLM (ι := ι) i))
      (x := x) (fun i _hi => hterm i))

/-- **The Hessian of log-sum-exp is the covariance form of softmax.** -/
lemma fderiv_fderiv_logSumExp_apply (x u v : EuclideanSpace ℝ ι) :
    ((fderiv ℝ (fderiv ℝ (fun y : EuclideanSpace ℝ ι => logSumExp y)) x) u) v
      = logSumExpHess x u v := by
  have hfun : (fderiv ℝ fun y : EuclideanSpace ℝ ι => logSumExp y)
      = fun y : EuclideanSpace ℝ ι => gradLogSumExp y :=
    funext fun y => fderiv_logSumExp_eq (ι := ι) y
  rw [hfun, (hasFDerivAt_gradLogSumExp (ι := ι) x).fderiv]
  have happ : ((∑ i, (fderiv ℝ (fun y : EuclideanSpace ℝ ι => softmax y i) x).smulRight
        (evalCLM (ι := ι) i)) u) v
      = ∑ i, (fderiv ℝ (fun y : EuclideanSpace ℝ ι => softmax y i) x u) * v i := by
    simp [sum_apply, ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul, evalCLM]
  rw [happ, logSumExpHess]
  have hterm : ∀ i : ι, (fderiv ℝ (fun y : EuclideanSpace ℝ ι => softmax y i) x u) * v i
      = softmax x i * u i * v i - (softmax x i * v i) * (∑ j, softmax x j * u j) := by
    intro i
    rw [fderiv_softmax_apply]
    ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hterm i, Finset.sum_sub_distrib,
    ← Finset.sum_mul]
  ring

/-! ### Uniform bounds on the derivatives -/

omit [Nonempty ι] in
lemma abs_apply_le_norm (x : EuclideanSpace ℝ ι) (i : ι) : |x i| ≤ ‖x‖ := by
  simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le (p := (2 : ENNReal)) (x := x) i)

/-- A `softmax`-average of coordinates is bounded by the norm. -/
lemma abs_sum_softmax_mul_le (x v : EuclideanSpace ℝ ι) :
    |∑ i, softmax x i * v i| ≤ ‖v‖ := by
  have h1 : |∑ i, softmax x i * v i| ≤ ∑ i, |softmax x i * v i| :=
    Finset.abs_sum_le_sum_abs _ _
  have h2 : ∀ i : ι, |softmax x i * v i| ≤ softmax x i * ‖v‖ := by
    intro i
    rw [abs_mul, abs_of_nonneg (softmax_nonneg x i)]
    exact mul_le_mul_of_nonneg_left (abs_apply_le_norm v i) (softmax_nonneg x i)
  calc |∑ i, softmax x i * v i| ≤ ∑ i, |softmax x i * v i| := h1
    _ ≤ ∑ i, softmax x i * ‖v‖ := Finset.sum_le_sum fun i _ => h2 i
    _ = ‖v‖ := by rw [← Finset.sum_mul, sum_softmax, one_mul]

lemma norm_gradLogSumExp_le (x : EuclideanSpace ℝ ι) : ‖gradLogSumExp x‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [gradLogSumExp_apply, Real.norm_eq_abs, one_mul]
  exact abs_sum_softmax_mul_le x v

/-- `‖D logSumExp‖ ≤ 1`, uniformly in `x`: the gradient is a probability vector. -/
lemma norm_fderiv_logSumExp_le (x : EuclideanSpace ℝ ι) :
    ‖fderiv ℝ (fun y : EuclideanSpace ℝ ι => logSumExp y) x‖ ≤ 1 := by
  rw [fderiv_logSumExp_eq]
  exact norm_gradLogSumExp_le x

lemma abs_sum_softmax_mul_mul_le (x u v : EuclideanSpace ℝ ι) :
    |∑ i, softmax x i * u i * v i| ≤ ‖u‖ * ‖v‖ := by
  have h1 : |∑ i, softmax x i * u i * v i| ≤ ∑ i, |softmax x i * u i * v i| :=
    Finset.abs_sum_le_sum_abs _ _
  have h2 : ∀ i : ι, |softmax x i * u i * v i| ≤ softmax x i * (‖u‖ * ‖v‖) := by
    intro i
    have : |softmax x i * u i * v i| = softmax x i * (|u i| * |v i|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (softmax_nonneg x i)]
      ring
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ (softmax_nonneg x i)
    exact mul_le_mul (abs_apply_le_norm u i) (abs_apply_le_norm v i) (abs_nonneg _) (norm_nonneg _)
  calc |∑ i, softmax x i * u i * v i| ≤ ∑ i, |softmax x i * u i * v i| := h1
    _ ≤ ∑ i, softmax x i * (‖u‖ * ‖v‖) := Finset.sum_le_sum fun i _ => h2 i
    _ = ‖u‖ * ‖v‖ := by rw [← Finset.sum_mul, sum_softmax, one_mul]

/-- The Hessian form is bounded by `2 ‖u‖ ‖v‖`, uniformly in `x`. -/
lemma abs_logSumExpHess_le (x u v : EuclideanSpace ℝ ι) :
    |logSumExpHess x u v| ≤ 2 * ‖u‖ * ‖v‖ := by
  rw [logSumExpHess]
  have h1 : |∑ i, softmax x i * u i * v i| ≤ ‖u‖ * ‖v‖ := abs_sum_softmax_mul_mul_le x u v
  have h2 : |(∑ i, softmax x i * u i) * (∑ i, softmax x i * v i)| ≤ ‖u‖ * ‖v‖ := by
    rw [abs_mul]
    exact mul_le_mul (abs_sum_softmax_mul_le x u) (abs_sum_softmax_mul_le x v)
      (abs_nonneg _) (norm_nonneg _)
  calc |(∑ i, softmax x i * u i * v i)
          - (∑ i, softmax x i * u i) * (∑ i, softmax x i * v i)|
      ≤ |∑ i, softmax x i * u i * v i|
          + |(∑ i, softmax x i * u i) * (∑ i, softmax x i * v i)| := abs_sub _ _
    _ ≤ ‖u‖ * ‖v‖ + ‖u‖ * ‖v‖ := add_le_add h1 h2
    _ = 2 * ‖u‖ * ‖v‖ := by ring

/-- `‖D² logSumExp‖ ≤ 2`, uniformly in `x`. -/
lemma norm_fderiv_fderiv_logSumExp_le (x : EuclideanSpace ℝ ι) :
    ‖fderiv ℝ (fderiv ℝ (fun y : EuclideanSpace ℝ ι => logSumExp y)) x‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun u => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [Real.norm_eq_abs, fderiv_fderiv_logSumExp_apply]
  exact abs_logSumExpHess_le x u v

/-! ### The sandwich between the maximum and the maximum plus `log (card ι)` -/

omit [Nonempty ι] in
/-- Every coordinate is at most `logSumExp`. -/
lemma le_logSumExp (x : EuclideanSpace ℝ ι) (i : ι) : x i ≤ logSumExp x := by
  have hle : Real.exp (x i) ≤ expSum x :=
    Finset.single_le_sum (f := fun j => Real.exp (x j))
      (fun j _ => le_of_lt (Real.exp_pos _)) (Finset.mem_univ i)
  have h := Real.log_le_log (Real.exp_pos _) hle
  rwa [Real.log_exp] at h

/-- `logSumExp` exceeds a uniform upper bound on the coordinates by at most `log (card ι)`. -/
lemma logSumExp_le_of_le {x : EuclideanSpace ℝ ι} {M : ℝ} (h : ∀ i, x i ≤ M) :
    logSumExp x ≤ M + Real.log (Fintype.card ι : ℝ) := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hle : expSum x ≤ (Fintype.card ι : ℝ) * Real.exp M := by
    have : expSum x ≤ ∑ _i : ι, Real.exp M :=
      Finset.sum_le_sum fun i _ => Real.exp_le_exp.mpr (h i)
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
  have h1 := Real.log_le_log (expSum_pos x) hle
  rw [Real.log_mul (ne_of_gt hcard) (ne_of_gt (Real.exp_pos M)), Real.log_exp] at h1
  simpa [logSumExp, add_comm] using h1

/-- Polynomial (indeed affine) growth of `logSumExp`. -/
lemma abs_logSumExp_le (x : EuclideanSpace ℝ ι) :
    |logSumExp x| ≤ Real.log (Fintype.card ι : ℝ) + ‖x‖ := by
  have hcard : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hlog : 0 ≤ Real.log (Fintype.card ι : ℝ) := Real.log_nonneg hcard
  have hub : logSumExp x ≤ Real.log (Fintype.card ι : ℝ) + ‖x‖ := by
    have h := logSumExp_le_of_le (x := x) (M := ‖x‖)
      (fun i => le_trans (le_abs_self _) (abs_apply_le_norm x i))
    linarith
  have hlb : -(Real.log (Fintype.card ι : ℝ) + ‖x‖) ≤ logSumExp x := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    have h1 : -‖x‖ ≤ x i := by
      have := abs_apply_le_norm x i
      have h2 : -‖x‖ ≤ x i := by
        rcases abs_le.mp this with ⟨hl, _⟩
        exact hl
      exact h2
    have h2 : x i ≤ logSumExp x := le_logSumExp x i
    linarith
  exact abs_le.mpr ⟨hlb, hub⟩

/-! ### The maximum coordinate and its smooth approximation -/

/-- The largest coordinate of `x`. -/
def maxCoord (x : EuclideanSpace ℝ ι) : ℝ :=
  (Finset.univ : Finset ι).sup' Finset.univ_nonempty (fun i => x i)

lemma le_maxCoord (x : EuclideanSpace ℝ ι) (i : ι) : x i ≤ maxCoord x :=
  Finset.le_sup' (f := fun j : ι => x j) (Finset.mem_univ i)

lemma maxCoord_le {x : EuclideanSpace ℝ ι} {M : ℝ} (h : ∀ i, x i ≤ M) : maxCoord x ≤ M :=
  Finset.sup'_le _ _ fun i _ => h i

lemma continuous_maxCoord : Continuous (maxCoord (ι := ι)) := by
  refine Continuous.finset_sup'_apply (f := fun (i : ι) (x : EuclideanSpace ℝ ι) => x i)
    Finset.univ_nonempty fun i _ => ?_
  exact (evalCLM (ι := ι) i).continuous

lemma abs_maxCoord_le (x : EuclideanSpace ℝ ι) : |maxCoord x| ≤ ‖x‖ := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine abs_le.mpr ⟨?_, maxCoord_le fun j => le_trans (le_abs_self _) (abs_apply_le_norm x j)⟩
  have h1 : -‖x‖ ≤ x i := (abs_le.mp (abs_apply_le_norm x i)).1
  exact le_trans h1 (le_maxCoord x i)

/-- Scaling by `l`, as a continuous linear map. -/
def scaleCLM (l : ℝ) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  l • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι)

omit [Nonempty ι] in
@[simp] lemma scaleCLM_apply (l : ℝ) (x : EuclideanSpace ℝ ι) : scaleCLM l x = l • x := rfl

/-- The **smooth maximum** at scale `l`: `l⁻¹ log ∑ exp (l xᵢ)`. As `l → ∞` it decreases to
`maxCoord`, with the explicit error bound `l⁻¹ log (card ι)`. -/
def smoothMax (l : ℝ) (x : EuclideanSpace ℝ ι) : ℝ := l⁻¹ * logSumExp (l • x)

omit [Nonempty ι] in
lemma smoothMax_eq_comp (l : ℝ) :
    smoothMax (ι := ι) l = fun y : EuclideanSpace ℝ ι => l⁻¹ * logSumExp (scaleCLM l y) := rfl

lemma contDiff_smoothMax (l : ℝ) : ContDiff ℝ (∞) (smoothMax (ι := ι) l) := by
  have hcomp : ContDiff ℝ (∞) (fun y : EuclideanSpace ℝ ι => logSumExp (scaleCLM (ι := ι) l y)) :=
    (contDiff_logSumExp (ι := ι)).comp (scaleCLM (ι := ι) l).contDiff
  simpa [smoothMax_eq_comp, smul_eq_mul] using
    (ContDiff.const_smul (𝕜 := ℝ) (n := (∞)) (R := ℝ) (c := l⁻¹) hcomp)

lemma fderiv_smoothMax_apply {l : ℝ} (hl : l ≠ 0) (x v : EuclideanSpace ℝ ι) :
    fderiv ℝ (smoothMax (ι := ι) l) x v = ∑ i, softmax (l • x) i * v i := by
  have hgd : Differentiable ℝ (fun z : EuclideanSpace ℝ ι => logSumExp z) :=
    (contDiff_logSumExp (ι := ι)).differentiable (by simp)
  have hcomp : Differentiable ℝ (fun y : EuclideanSpace ℝ ι => logSumExp (scaleCLM (ι := ι) l y)) :=
    hgd.comp (scaleCLM (ι := ι) l).differentiable
  have h1 : fderiv ℝ (smoothMax (ι := ι) l) x
      = l⁻¹ • fderiv ℝ (fun y : EuclideanSpace ℝ ι => logSumExp (scaleCLM (ι := ι) l y)) x := by
    rw [smoothMax_eq_comp]
    exact ((hcomp x).hasFDerivAt.const_smul l⁻¹).fderiv
  rw [h1, fderiv_comp_clm hgd (scaleCLM (ι := ι) l) x]
  simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply, scaleCLM_apply,
    smul_eq_mul, fderiv_logSumExp_eq, gradLogSumExp_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (l • v) i = l * v i := rfl
  rw [this]
  field_simp

omit [Nonempty ι] in
lemma logSumExpHess_smul_smul (x u v : EuclideanSpace ℝ ι) (a b : ℝ) :
    logSumExpHess x (a • u) (b • v) = (a * b) * logSumExpHess x u v := by
  have hu : ∀ i : ι, (a • u) i = a * u i := fun _ => rfl
  have hv : ∀ i : ι, (b • v) i = b * v i := fun _ => rfl
  rw [logSumExpHess, logSumExpHess]
  simp only [hu, hv]
  rw [show (∑ i, softmax x i * (a * u i) * (b * v i))
      = (a * b) * ∑ i, softmax x i * u i * v i by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
    show (∑ i, softmax x i * (a * u i)) = a * ∑ i, softmax x i * u i by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
    show (∑ i, softmax x i * (b * v i)) = b * ∑ i, softmax x i * v i by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
  ring

/-- The Hessian of the smooth maximum: `l` times the `softmax` covariance at `l • x`. -/
lemma fderiv_fderiv_smoothMax_apply {l : ℝ} (hl : l ≠ 0) (x u v : EuclideanSpace ℝ ι) :
    ((fderiv ℝ (fderiv ℝ (smoothMax (ι := ι) l)) x) u) v
      = l * logSumExpHess (l • x) u v := by
  have hc2 : ContDiff ℝ 2 (fun y : EuclideanSpace ℝ ι => logSumExp (scaleCLM (ι := ι) l y)) :=
    ((contDiff_logSumExp (ι := ι)).comp (scaleCLM (ι := ι) l).contDiff).of_le (by simp)
  rw [smoothMax_eq_comp, fderiv_fderiv_const_mul_apply hc2 l⁻¹ x u v,
    fderiv_fderiv_comp_clm_apply ((contDiff_logSumExp (ι := ι)).of_le (by simp))
      (scaleCLM (ι := ι) l) x u v,
    fderiv_fderiv_logSumExp_apply, scaleCLM_apply, scaleCLM_apply, scaleCLM_apply,
    logSumExpHess_smul_smul]
  field_simp

lemma norm_fderiv_smoothMax_le {l : ℝ} (hl : l ≠ 0) (x : EuclideanSpace ℝ ι) :
    ‖fderiv ℝ (smoothMax (ι := ι) l) x‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [Real.norm_eq_abs, one_mul, fderiv_smoothMax_apply hl]
  exact abs_sum_softmax_mul_le (l • x) v

lemma norm_fderiv_fderiv_smoothMax_le {l : ℝ} (hl : l ≠ 0) (x : EuclideanSpace ℝ ι) :
    ‖fderiv ℝ (fderiv ℝ (smoothMax (ι := ι) l)) x‖ ≤ 2 * |l| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [Real.norm_eq_abs, fderiv_fderiv_smoothMax_apply hl, abs_mul]
  calc |l| * |logSumExpHess (l • x) u v| ≤ |l| * (2 * ‖u‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (abs_logSumExpHess_le (l • x) u v) (abs_nonneg l)
    _ = 2 * |l| * ‖u‖ * ‖v‖ := by ring

lemma maxCoord_le_smoothMax {l : ℝ} (hl : 0 < l) (x : EuclideanSpace ℝ ι) :
    maxCoord x ≤ smoothMax (ι := ι) l x := by
  refine maxCoord_le fun i => ?_
  have h1 : (l • x) i = l * x i := rfl
  have h2 : (l • x) i ≤ logSumExp (l • x) := le_logSumExp (l • x) i
  rw [smoothMax]
  rw [h1] at h2
  calc x i = l⁻¹ * (l * x i) := by field_simp
    _ ≤ l⁻¹ * logSumExp (l • x) := by
        exact mul_le_mul_of_nonneg_left h2 (le_of_lt (inv_pos.mpr hl))

lemma smoothMax_le_maxCoord_add {l : ℝ} (hl : 0 < l) (x : EuclideanSpace ℝ ι) :
    smoothMax (ι := ι) l x ≤ maxCoord x + l⁻¹ * Real.log (Fintype.card ι : ℝ) := by
  have hbound : ∀ i : ι, (l • x) i ≤ l * maxCoord x := by
    intro i
    have h1 : (l • x) i = l * x i := rfl
    rw [h1]
    exact mul_le_mul_of_nonneg_left (le_maxCoord x i) (le_of_lt hl)
  have h := logSumExp_le_of_le (x := l • x) (M := l * maxCoord x) hbound
  rw [smoothMax]
  calc l⁻¹ * logSumExp (l • x)
      ≤ l⁻¹ * (l * maxCoord x + Real.log (Fintype.card ι : ℝ)) :=
        mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.mpr hl))
    _ = maxCoord x + l⁻¹ * Real.log (Fintype.card ι : ℝ) := by
        field_simp

lemma abs_smoothMax_le {l : ℝ} (hl : 0 < l) (x : EuclideanSpace ℝ ι) :
    |smoothMax (ι := ι) l x| ≤ l⁻¹ * Real.log (Fintype.card ι : ℝ) + ‖x‖ := by
  have hcard : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hlog : 0 ≤ Real.log (Fintype.card ι : ℝ) := Real.log_nonneg hcard
  have hlogpos : 0 ≤ l⁻¹ * Real.log (Fintype.card ι : ℝ) := by positivity
  have hmax := abs_maxCoord_le x
  have hub : smoothMax (ι := ι) l x ≤ l⁻¹ * Real.log (Fintype.card ι : ℝ) + ‖x‖ := by
    have h := smoothMax_le_maxCoord_add hl x
    have h2 : maxCoord x ≤ ‖x‖ := (abs_le.mp hmax).2
    linarith
  have hlb : -(l⁻¹ * Real.log (Fintype.card ι : ℝ) + ‖x‖) ≤ smoothMax (ι := ι) l x := by
    have h := maxCoord_le_smoothMax hl x
    have h2 : -‖x‖ ≤ maxCoord x := (abs_le.mp hmax).1
    linarith
  exact abs_le.mpr ⟨hlb, hub⟩

/-! ### The Hessian in the Dirac basis -/

omit [Nonempty ι] in
@[simp] lemma sum_softmax_mul_basisFun (x : EuclideanSpace ℝ ι) (j : ι) :
    (∑ k, softmax x k * (EuclideanSpace.basisFun ι ℝ j) k) = softmax x j := by
  classical
  simp [EuclideanSpace.basisFun_apply, PiLp.single_apply]

omit [Nonempty ι] in
lemma sum_softmax_mul_basisFun_sq (x : EuclideanSpace ℝ ι) (i : ι) :
    (∑ k, softmax x k * (EuclideanSpace.basisFun ι ℝ i) k
        * (EuclideanSpace.basisFun ι ℝ i) k) = softmax x i := by
  classical
  simp [EuclideanSpace.basisFun_apply, PiLp.single_apply]

omit [Nonempty ι] in
lemma sum_softmax_mul_basisFun_mul_basisFun_of_ne (x : EuclideanSpace ℝ ι) {i j : ι}
    (h : i ≠ j) :
    (∑ k, softmax x k * (EuclideanSpace.basisFun ι ℝ j) k
        * (EuclideanSpace.basisFun ι ℝ i) k) = 0 := by
  classical
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hkj : k = j
  · have hki : k ≠ i := fun hk => h (hk.symm.trans hkj)
    simp [EuclideanSpace.basisFun_apply, PiLp.single_apply, hki]
  · simp [EuclideanSpace.basisFun_apply, PiLp.single_apply, hkj]

omit [Nonempty ι] in
/-- Diagonal Hessian entry of `logSumExp` in the Dirac basis: `pᵢ - pᵢ²`. -/
lemma logSumExpHess_basisFun_self (x : EuclideanSpace ℝ ι) (i : ι) :
    logSumExpHess x (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ i)
      = softmax x i - softmax x i * softmax x i := by
  rw [logSumExpHess, sum_softmax_mul_basisFun_sq, sum_softmax_mul_basisFun]

omit [Nonempty ι] in
/-- Off-diagonal Hessian entry of `logSumExp` in the Dirac basis: `-pᵢpⱼ`. -/
lemma logSumExpHess_basisFun_of_ne (x : EuclideanSpace ℝ ι) {i j : ι} (h : i ≠ j) :
    logSumExpHess x (EuclideanSpace.basisFun ι ℝ j) (EuclideanSpace.basisFun ι ℝ i)
      = -(softmax x j * softmax x i) := by
  rw [logSumExpHess, sum_softmax_mul_basisFun_mul_basisFun_of_ne x h,
    sum_softmax_mul_basisFun, sum_softmax_mul_basisFun, zero_sub]

end Real
