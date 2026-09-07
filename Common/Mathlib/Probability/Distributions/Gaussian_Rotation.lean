/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.Distributions.Gaussian_IBP_HilbertAPI
import Common.Mathlib.Probability.Distributions.Gaussian_Interpolation
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Topology.Algebra.Module.Spaces.CompactConvergenceCLM
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# The Gaussian rotation `(x, y) ↦ (cos θ · x + sin θ · y, -sin θ · x + cos θ · y)`

For a centered Gaussian measure `μ` on a real Hilbert space `H`, the quarter-turn family

`gaussRotMap θ (x, y) = (cos θ • x + sin θ • y, -sin θ • x + cos θ • y)`

is a one-parameter group of orthogonal maps of `H × H` preserving the product Gaussian measure
`μ ⊗ μ` (`map_gaussRotMap_prod`). It carries a pair of independent copies of `μ` to another such
pair while rotating one component into the other, which is what turns a pointwise derivative bound
into a bound on a global fluctuation: `f x - f y` is the integral of `d/dθ f (gaussRot θ (x, y))`
over a quarter turn, and the integrand is measured against a *fresh* independent copy.

`gaussRot` is Talagrand's smart path in its angle parameterization: it is the interpolation
`ProbabilityTheory.gaussianInterp` of `Gaussian_Interpolation` at `cos θ = √t`
(`gaussianInterp_eq_gaussRot`), read on the plain product. The two files develop one interpolation,
not two; the angle makes the orthogonality of the rotation manifest, which is what the variance and
covariance arguments need, while `t` makes the endpoints manifest, which is what the comparison
arguments need.

## Main statements

- `ProbabilityTheory.IsGaussian.map_gaussRotMap_prod`: the rotation preserves `μ ⊗ μ`.
- `ProbabilityTheory.IsGaussian.hasDerivAt_comp_gaussRot`: the derivative along the quarter turn.
- `ProbabilityTheory.IsGaussian.gaussianInterp_eq_gaussRot`: the angle and the time
  parameterizations agree.
-/

open scoped BigOperators ENNReal NNReal ProbabilityTheory RealInnerProductSpace Topology

open MeasureTheory Filter Real

namespace ProbabilityTheory

namespace IsGaussian

noncomputable section

/-! ## The rotation family -/

open scoped Interval

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  {μ : Measure H} [IsGaussian μ]

/-! ### Rotation mixing map -/

/-- The `θ`-dependent Gaussian rotation mix `cos θ • x + sin θ • y`. -/
noncomputable def gaussRot (θ : ℝ) (p : H × H) : H :=
  Real.cos θ • p.1 + Real.sin θ • p.2

/-- The orthogonal companion of `gaussRot`: `-sin θ • x + cos θ • y`. -/
noncomputable def gaussRotOrtho (θ : ℝ) (p : H × H) : H :=
  -Real.sin θ • p.1 + Real.cos θ • p.2

/-! ### Continuous linear maps -/

/-- `gaussRot` as a continuous linear map in the pair variable. -/
noncomputable def gaussRotCLM (θ : ℝ) : (H × H) →L[ℝ] H :=
  (Real.cos θ) • ContinuousLinearMap.fst ℝ H H
    + (Real.sin θ) • ContinuousLinearMap.snd ℝ H H

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
@[simp] lemma gaussRotCLM_apply (θ : ℝ) (p : H × H) :
    gaussRotCLM (H := H) θ p = gaussRot (H := H) θ p := by
  rfl

/-- `gaussRotOrtho` as a continuous linear map in the pair variable. -/
noncomputable def gaussRotOrthoCLM (θ : ℝ) : (H × H) →L[ℝ] H :=
  (-Real.sin θ) • ContinuousLinearMap.fst ℝ H H
    + (Real.cos θ) • ContinuousLinearMap.snd ℝ H H

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
@[simp] lemma gaussRotOrthoCLM_apply (θ : ℝ) (p : H × H) :
    gaussRotOrthoCLM (H := H) θ p = gaussRotOrtho (H := H) θ p := by
  rfl

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
/-- **The rotation and the interpolation are the same smart path**, in two parameterizations:
`gaussianInterp t = gaussRot (arccos √t)`. The angle parameterization makes the orthogonality of
the `2 × 2` matrix manifest (which is what the Poincaré argument needs); the `t` parameterization
makes the endpoints `t = 0, 1` manifest (which is what the comparison arguments need). -/
lemma gaussianInterp_eq_gaussRot {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (p : H × H) :
    ProbabilityTheory.gaussianInterp t (WithLp.toLp 2 p)
      = gaussRot (H := H) (Real.arccos (Real.sqrt t)) p := by
  have h0 : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
  have h1 : Real.sqrt t ≤ 1 := by
    have : Real.sqrt t ≤ Real.sqrt 1 := Real.sqrt_le_sqrt ht.2
    simpa using this
  rw [gaussRot, Real.cos_arccos (by linarith) h1, Real.sin_arccos, Real.sq_sqrt ht.1]
  rfl

/-- The rotation mixing map `(x,y) ↦ (gaussRot θ (x,y), gaussRotOrtho θ (x,y))`. -/
noncomputable def gaussRotMap (θ : ℝ) : (H × H) →L[ℝ] (H × H) :=
  (gaussRotCLM (H := H) θ).prod (gaussRotOrthoCLM (H := H) θ)

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
@[simp] lemma gaussRotMap_apply (θ : ℝ) (p : H × H) :
    gaussRotMap (H := H) θ p = (gaussRot (H := H) θ p, gaussRotOrtho (H := H) θ p) := by
  rfl

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
private lemma gaussRot_gaussRotMap_neg (θ : ℝ) (p : H × H) :
    gaussRot (H := H) θ (gaussRotMap (H := H) (-θ) p) = p.1 := by
  rcases p with ⟨x, y⟩
  simp only [gaussRot, gaussRotMap_apply, cos_neg, sin_neg, neg_smul, gaussRotOrtho, neg_neg,
    add_comm, smul_add, smul_smul, smul_neg, mul_comm, add_left_comm, add_assoc,
    add_neg_cancel_comm_assoc]
  have hcos : Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ = (1 : ℝ) := by
    have : (Real.cos θ) ^ 2 + (Real.sin θ) ^ 2 = (1 : ℝ) := by simp
    simpa [pow_two] using this
  have hcross : -(Real.cos θ * Real.sin θ) + Real.sin θ * Real.cos θ = (0 : ℝ) := by ring
  simp [← add_smul, hcos]

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
private lemma gaussRotOrtho_gaussRotMap_neg (θ : ℝ) (p : H × H) :
    gaussRotOrtho (H := H) θ (gaussRotMap (H := H) (-θ) p) = p.2 := by
  rcases p with ⟨x, y⟩
  simp only [gaussRotOrtho, gaussRotMap_apply, gaussRot, cos_neg, sin_neg, neg_smul, neg_neg,
    add_comm, smul_add, smul_smul, mul_comm, mul_neg, smul_neg, add_assoc,
    add_neg_cancel_comm_assoc]
  have hcos : Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ = (1 : ℝ) := by
    have : (Real.cos θ) ^ 2 + (Real.sin θ) ^ 2 = (1 : ℝ) := by simp
    simpa [pow_two] using this
  have hcross : -(Real.sin θ * Real.cos θ) + Real.cos θ * Real.sin θ = (0 : ℝ) := by ring
  simp [← add_smul, hcos]

private lemma variance_gaussRot_components (θ : ℝ) (L₁ L₂ : StrongDual ℝ H) :
    Var[(Real.cos θ) • L₁ + (Real.sin θ) • L₂; μ]
      + Var[(-Real.sin θ) • L₁ + (Real.cos θ) • L₂; μ]
      = Var[L₁; μ] + Var[L₂; μ] := by
  have hL₁ : MemLp L₁ 2 μ := IsGaussian.memLp_dual μ L₁ 2 (by simp)
  have hL₂ : MemLp L₂ 2 μ := IsGaussian.memLp_dual μ L₂ 2 (by simp)
  have hVar₁ :
      Var[(Real.cos θ) • L₁ + (Real.sin θ) • L₂; μ]
        = Var[(Real.cos θ) • L₁; μ]
          + 2 * cov[(Real.cos θ) • L₁, (Real.sin θ) • L₂; μ]
          + Var[(Real.sin θ) • L₂; μ] :=
    (variance_add (μ := μ) (hL₁.const_smul (Real.cos θ)) (hL₂.const_smul (Real.sin θ)))
  have hVar₂ :
      Var[(-Real.sin θ) • L₁ + (Real.cos θ) • L₂; μ]
        = Var[(-Real.sin θ) • L₁; μ]
          + 2 * cov[(-Real.sin θ) • L₁, (Real.cos θ) • L₂; μ]
          + Var[(Real.cos θ) • L₂; μ] :=
    (variance_add (μ := μ) (hL₁.const_smul (-Real.sin θ)) (hL₂.const_smul (Real.cos θ)))
  have hcos2sin2 : (Real.cos θ) ^ 2 + (Real.sin θ) ^ 2 = 1 := by
    simp
  calc
    Var[(Real.cos θ) • L₁ + (Real.sin θ) • L₂; μ]
        + Var[(-Real.sin θ) • L₁ + (Real.cos θ) • L₂; μ]
        = (Real.cos θ) ^ 2 * Var[L₁; μ]
            + (Real.sin θ) ^ 2 * Var[L₁; μ]
            + (Real.sin θ) ^ 2 * Var[L₂; μ]
            + (Real.cos θ) ^ 2 * Var[L₂; μ] := by
          rw [hVar₁, hVar₂]
          simp [variance_smul, variance_neg,
            covariance_smul_left, covariance_smul_right]
          ring
    _ = ((Real.cos θ) ^ 2 + (Real.sin θ) ^ 2) * Var[L₁; μ]
          + ((Real.cos θ) ^ 2 + (Real.sin θ) ^ 2) * Var[L₂; μ] := by
          ring
    _ = Var[L₁; μ] + Var[L₂; μ] := by
          simp [hcos2sin2]

/-- The rotation map preserves the product Gaussian law (centered case). -/
lemma map_gaussRotMap_prod (hmean0 : (∫ x : H, x ∂μ) = 0) (θ : ℝ) :
    (μ.prod μ).map (gaussRotMap (H := H) θ) = μ.prod μ := by
  let P : Measure (H × H) := μ.prod μ
  let Q : Measure (H × H) := P.map (gaussRotMap (H := H) θ)
  have : IsGaussian P := by infer_instance
  have : IsGaussian Q := by infer_instance
  have hPmean : P[id] = (0 : H × H) := by
    have hInt : Integrable (id : (H × H) → (H × H)) P := IsGaussian.integrable_id (μ := P)
    have hfst :
        (∫ x : H × H, x ∂P).1 = 0 := by
      have hproj :
          (∫ x : H × H, x ∂P).1 = ∫ x : H × H, x.1 ∂P := by
        simpa using
          (ContinuousLinearMap.integral_comp_comm (ContinuousLinearMap.fst ℝ H H) hInt).symm
      have : (∫ x : H × H, x.1 ∂P) = 0 := by
        calc
          (∫ x : H × H, x.1 ∂P)
              = μ.real Set.univ • ∫ x : H, x ∂μ := by
                  simpa [P] using (integral_fun_fst (μ := μ) (ν := μ) (f := (id : H → H)))
          _ = 0 := by simp [probReal_univ, hmean0]
      simpa [hproj] using this
    have hsnd :
        (∫ x : H × H, x ∂P).2 = 0 := by
      have hproj :
          (∫ x : H × H, x ∂P).2 = ∫ x : H × H, x.2 ∂P := by
        simpa using
          (ContinuousLinearMap.integral_comp_comm (ContinuousLinearMap.snd ℝ H H) hInt).symm
      have : (∫ x : H × H, x.2 ∂P) = 0 := by
        calc
          (∫ x : H × H, x.2 ∂P)
              = μ.real Set.univ • ∫ x : H, x ∂μ := by
                  simpa [P] using (integral_fun_snd (μ := μ) (ν := μ) (f := (id : H → H)))
          _ = 0 := by simp [probReal_univ, hmean0]
      simpa [hproj] using this
    ext
    · simpa using hfst
    · simpa using hsnd
  have hQmean : Q[id] = (0 : H × H) := by
    have hInt : Integrable (id : (H × H) → (H × H)) P := IsGaussian.integrable_id (μ := P)
    have hMap : AEMeasurable (gaussRotMap (H := H) θ) P := by fun_prop
    have hId : AEStronglyMeasurable (id : (H × H) → (H × H)) Q := by
      simpa [Q] using (aestronglyMeasurable_id : AEStronglyMeasurable (id : (H × H) → (H × H)) Q)
    have :
        (∫ x : H × H, x ∂Q) = ∫ x : H × H, gaussRotMap (H := H) θ x ∂P := by
      simpa [Q] using (integral_map (μ := P) (φ := gaussRotMap (H := H) θ) (f := (id : (H × H) → (H
        × H)))
        hMap hId)
    have hZero : (∫ x : H × H, gaussRotMap (H := H) θ x ∂P) = 0 := by
      have h :=
        ContinuousLinearMap.integral_comp_comm (gaussRotMap (H := H) θ) hInt
      calc
        (∫ x : H × H, gaussRotMap (H := H) θ x ∂P)
            = ∫ x : H × H, gaussRotMap (H := H) θ (id x) ∂P := by simp [id_eq]
        _ = gaussRotMap (H := H) θ (∫ x : H × H, id x ∂P) := h
        _ = gaussRotMap (H := H) θ 0 := by rw [hPmean]
        _ = 0 := map_zero _
    simpa [this, hZero]
  have hm : P[id] = Q[id] := by
    calc
      P[id] = (0 : H × H) := hPmean
      _ = Q[id] := hQmean.symm
  have hLpP : MemLp (id : (H × H) → (H × H)) 2 P := IsGaussian.memLp_two_id (μ := P)
  have hLpQ : MemLp (id : (H × H) → (H × H)) 2 Q := IsGaussian.memLp_two_id (μ := Q)
  have hv : covarianceBilinDual P = covarianceBilinDual Q := by
    apply (ContinuousLinearMap.toBilinForm_inj (covarianceBilinDual P) (covarianceBilinDual Q)).1
    refine LinearMap.BilinForm.ext_of_isSymm
      (isPosSemidef_covarianceBilinDual.isSymm) (isPosSemidef_covarianceBilinDual.isSymm) ?_
    intro L
    have hdiag :
        covarianceBilinDual P L L = covarianceBilinDual Q L L := by
      simp only [hLpP, covarianceBilinDual_self_eq_variance, hLpQ]
      have hVar : Var[L; Q] = Var[L; P] := by
        have hLQ : AEMeasurable (L : (H × H) → ℝ) Q := by fun_prop
        have hMap : AEMeasurable (gaussRotMap (H := H) θ) P := by fun_prop
        have hVar_map :
            Var[(L : (H × H) → ℝ); Q] = Var[(L : (H × H) → ℝ) ∘ gaussRotMap (H := H) θ; P] := by
          simpa [Q] using (variance_map (μ := P) (X := (L : (H × H) → ℝ))
            (Y := gaussRotMap (H := H) θ) hLQ hMap)
        have hId : MemLp (id : H → H) 2 μ := IsGaussian.memLp_two_id (μ := μ)
        have hVarP : Var[L; P] = Var[L.comp (.inl ℝ H H); μ] + Var[L.comp (.inr ℝ H H); μ] := by
          simpa [P] using (variance_dual_prod (E := H) (F := H) (μ := μ) (ν := μ) (L := L) hId hId)
        have hVarRot :
            Var[(L : (H × H) → ℝ) ∘ gaussRotMap (H := H) θ; P]
              = Var[(L.comp (gaussRotMap (H := H) θ)).comp (.inl ℝ H H); μ]
                + Var[(L.comp (gaussRotMap (H := H) θ)).comp (.inr ℝ H H); μ] := by
          simpa [P, ContinuousLinearMap.coe_comp] using
            (variance_dual_prod (E := H) (F := H) (μ := μ) (ν := μ)
              (L := (L.comp (gaussRotMap (H := H) θ))) hId hId)
        set L₁ : StrongDual ℝ H := L.comp (.inl ℝ H H)
        set L₂ : StrongDual ℝ H := L.comp (.inr ℝ H H)
        have hInl :
            (L.comp (gaussRotMap (H := H) θ)).comp (.inl ℝ H H)
              = (Real.cos (-θ)) • L₁ + (Real.sin (-θ)) • L₂ := by
          ext x
          have hdecomp :
              L (Real.cos θ • x, -(Real.sin θ • x))
                = L₁ (Real.cos θ • x) + L₂ (-(Real.sin θ • x)) := by
            simpa [L₁, L₂] using
              (ContinuousLinearMap.comp_inl_add_comp_inr (L := L) (v := (Real.cos θ • x, -(Real.sin
                θ • x)))).symm
          have hL0 : L (0, -(Real.sin θ • x)) = -(Real.sin θ * L (0, x)) := by
            calc
              L (0, -(Real.sin θ • x)) = L₂ (-(Real.sin θ • x)) := by simp [L₂]
              _ = -(L₂ (Real.sin θ • x)) := by simp
              _ = -(Real.sin θ * L₂ x) := by simp [map_smul, smul_eq_mul]
              _ = -(Real.sin θ * L (0, x)) := by simp [L₂]
          simp [L₁, L₂, gaussRotMap_apply, gaussRot, gaussRotOrtho,
            ContinuousLinearMap.comp_apply, Real.cos_neg, Real.sin_neg, hdecomp, hL0,
            add_comm, smul_eq_mul]
        have hInr :
            (L.comp (gaussRotMap (H := H) θ)).comp (.inr ℝ H H)
              = (-Real.sin (-θ)) • L₁ + (Real.cos (-θ)) • L₂ := by
          ext x
          have hdecomp :
              L (Real.sin θ • x, Real.cos θ • x)
                = L₁ (Real.sin θ • x) + L₂ (Real.cos θ • x) := by
            simpa [L₁, L₂] using
              (ContinuousLinearMap.comp_inl_add_comp_inr (L := L) (v := (Real.sin θ • x, Real.cos θ
                • x))).symm
          simp [L₁, L₂, gaussRotMap_apply, gaussRot, gaussRotOrtho, ContinuousLinearMap.comp_apply,
            Real.cos_neg, Real.sin_neg, hdecomp, add_comm, smul_eq_mul]
        have hRotate :
            Var[(Real.cos (-θ)) • L₁ + (Real.sin (-θ)) • L₂; μ]
              + Var[(-Real.sin (-θ)) • L₁ + (Real.cos (-θ)) • L₂; μ]
              = Var[L₁; μ] + Var[L₂; μ] :=
          variance_gaussRot_components (μ := μ) (H := H) (-θ) L₁ L₂
        have : Var[(L : (H × H) → ℝ) ∘ gaussRotMap (H := H) θ; P] = Var[L; P] := by
          rw [hVarRot, hVarP]
          simpa [hInl, hInr, L₁, L₂] using hRotate
        exact (hVar_map.trans this).trans rfl
      simp [hVar]
    simpa using hdiag
  simpa [P, Q] using (ProbabilityTheory.IsGaussian.ext_covarianceBilinDual (μ := P) (ν := Q) hm
    hv).symm

/-! ## Elementary bounds and the inverse rotation -/

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
@[fun_prop, continuity]
lemma continuous_gaussRot (θ : ℝ) : Continuous fun p : H × H => gaussRot (H := H) θ p := by
  simpa [gaussRot] using (by fun_prop : Continuous fun p : H × H =>
    Real.cos θ • p.1 + Real.sin θ • p.2)

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
@[fun_prop, continuity]
lemma continuous_gaussRotOrtho (θ : ℝ) :
    Continuous fun p : H × H => gaussRotOrtho (H := H) θ p := by
  simpa [gaussRotOrtho] using (by fun_prop : Continuous fun p : H × H =>
    -Real.sin θ • p.1 + Real.cos θ • p.2)


omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
/-- The rotation is a contraction for the `ℓ¹`-type bound on a pair. -/
lemma norm_gaussRot_le (θ : ℝ) (p : H × H) : ‖gaussRot (H := H) θ p‖ ≤ ‖p.1‖ + ‖p.2‖ := by
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_) <;>
    rw [norm_smul, Real.norm_eq_abs] <;>
    [ exact mul_le_of_le_one_left (norm_nonneg _) (abs_cos_le_one θ);
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_sin_le_one θ) ]

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
/-- The orthogonal companion of the rotation obeys the same bound. -/
lemma norm_gaussRotOrtho_le (θ : ℝ) (p : H × H) :
    ‖gaussRotOrtho (H := H) θ p‖ ≤ ‖p.1‖ + ‖p.2‖ := by
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_) <;>
    rw [norm_smul, Real.norm_eq_abs] <;>
    [ exact mul_le_of_le_one_left (norm_nonneg _) (by simpa using abs_sin_le_one θ);
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_cos_le_one θ) ]

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
/-- The rotation is invertible on components: the first coordinate is read back off the rotated
pair by the inverse rotation, `cos θ • (rot p) - sin θ • (rot⊥ p) = p.1`. This is what lets an
integral over `μ ⊗ μ` in the rotated variables be rewritten in the original ones. -/
lemma smul_gaussRot_sub_smul_gaussRotOrtho (θ : ℝ) (p : H × H) :
    Real.cos θ • gaussRot (H := H) θ p - Real.sin θ • gaussRotOrtho (H := H) θ p = p.1 := by
  rcases p with ⟨x, y⟩
  simp only [gaussRot, gaussRotOrtho]
  match_scalars <;> nlinarith [Real.sin_sq_add_cos_sq θ]

/-! ## Differentiating along the quarter turn -/

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
/-- The quarter-turn path `θ ↦ gaussRot θ p` has derivative `gaussRotOrtho θ p`: the rotation
moves at unit speed in the orthogonal direction. -/
lemma hasDerivAt_gaussRot (θ : ℝ) (p : H × H) :
    HasDerivAt (fun t : ℝ => gaussRot (H := H) t p) (gaussRotOrtho (H := H) θ p) θ := by
  simpa [gaussRot, gaussRotOrtho, add_comm, add_left_comm, add_assoc, sub_eq_add_neg, smul_add]
    using
    ((Real.hasDerivAt_cos θ).smul_const p.1).fun_add ((Real.hasDerivAt_sin θ).smul_const p.2)

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
/-- The chain rule along the quarter turn: `d/dθ f (gaussRot θ p) = (Df) (gaussRot θ p)
(gaussRotOrtho θ p)`. -/
lemma hasDerivAt_comp_gaussRot {f : H → ℝ} (hf : ContDiff ℝ 1 f) (θ : ℝ) (p : H × H) :
    HasDerivAt (fun t : ℝ => f (gaussRot (H := H) t p))
      ((fderiv ℝ f (gaussRot (H := H) θ p)) (gaussRotOrtho (H := H) θ p)) θ := by
  have hf' : DifferentiableAt ℝ f (gaussRot (H := H) θ p) :=
    (hf.differentiable (by simp)).differentiableAt
  have hF : HasFDerivAt f (fderiv ℝ f (gaussRot (H := H) θ p)) (gaussRot (H := H) θ p) :=
    hf'.hasFDerivAt
  simpa [Function.comp_def] using (hF.comp_hasDerivAt θ (hasDerivAt_gaussRot (H := H) θ p))

end

end IsGaussian

end ProbabilityTheory
