/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# First and second derivatives along a continuous linear precomposition

For `g : F → ℝ` and a continuous linear map `L : E →L[ℝ] F`, the derivatives of `g ∘ L` are the
derivatives of `g` precomposed with `L`:

`D (g ∘ L) x = (D g (L x)) ∘ L`,  `D² (g ∘ L) x u v = D² g (L x) (L u) (L v)`.

The first identity is the chain rule; the second is what an interpolation or rescaling argument
needs, since a change of scale `x ↦ l • x` is such an `L`.

## Main statements

- `fderiv_comp_clm`: the first-order identity.
- `fderiv_fderiv_comp_clm_apply`: the second-order identity.
- `fderiv_fderiv_const_mul_apply`: second-order homogeneity in a scalar factor.
-/

open scoped ContDiff

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Chain rule along a continuous linear map: `D (g ∘ L) x = (D g (L x)) ∘ L`. -/
theorem fderiv_comp_clm {g : F → ℝ} (hg : Differentiable ℝ g) (L : E →L[ℝ] F) (x : E) :
    fderiv ℝ (fun y : E => g (L y)) x = (fderiv ℝ g (L x)).comp L :=
  ((hg (L x)).hasFDerivAt.comp x L.hasFDerivAt).fderiv

/-- Second-order chain rule along a continuous linear map:
`D² (g ∘ L) x u v = D² g (L x) (L u) (L v)`. -/
theorem fderiv_fderiv_comp_clm_apply {g : F → ℝ} (hg : ContDiff ℝ 2 g)
    (L : E →L[ℝ] F) (x u v : E) :
    ((fderiv ℝ (fderiv ℝ (fun y : E => g (L y))) x) u) v
      = ((fderiv ℝ (fderiv ℝ g) (L x)) (L u)) (L v) := by
  -- Precomposition by `L`, as a continuous linear map on the dual.
  set Q : (F →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) := (ContinuousLinearMap.compL ℝ E F ℝ).flip L with hQ
  have hQapply : ∀ M : F →L[ℝ] ℝ, Q M = M.comp L := fun _ => rfl
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hfun : (fderiv ℝ fun y : E => g (L y)) = fun y : E => Q (fderiv ℝ g (L y)) := by
    funext y
    rw [fderiv_comp_clm hgd L y, hQapply]
  have hdg : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hcomp : HasFDerivAt (fun y : E => Q (fderiv ℝ g (L y)))
      ((Q.comp (fderiv ℝ (fderiv ℝ g) (L x))).comp L) x := by
    have h1 : HasFDerivAt (fun z : F => Q (fderiv ℝ g z))
        (Q.comp (fderiv ℝ (fderiv ℝ g) (L x))) (L x) :=
      Q.hasFDerivAt.comp (L x) (hdg (L x)).hasFDerivAt
    exact h1.comp x L.hasFDerivAt
  rw [hfun, hcomp.fderiv]
  simp [hQapply]

/-- Second-order homogeneity in a scalar factor: `D² (a • g) = a • D² g`. -/
theorem fderiv_fderiv_const_mul_apply {g : E → ℝ} (hg : ContDiff ℝ 2 g) (a : ℝ) (x u v : E) :
    ((fderiv ℝ (fderiv ℝ (fun y : E => a * g y)) x) u) v
      = a * ((fderiv ℝ (fderiv ℝ g) x) u) v := by
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hdg : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h1 : (fderiv ℝ fun y : E => a * g y) = fun y : E => a • fderiv ℝ g y := by
    funext y
    exact ((hgd y).hasFDerivAt.const_smul a).fderiv
  rw [h1]
  have h2 : HasFDerivAt (fun y : E => a • fderiv ℝ g y) (a • fderiv ℝ (fderiv ℝ g) x) x :=
    (hdg x).hasFDerivAt.const_smul a
  rw [h2.fderiv]
  simp
