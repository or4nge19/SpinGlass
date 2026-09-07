/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.Distributions.Gaussian_IBP_Hilbert

/-!
# The Gaussian divergence identity

For a centered Gaussian measure `μ` on a real inner product space `E` with covariance operator
`C = covarianceOperator μ`, and a `C¹` **covector field** `Ψ : E → (E →L[ℝ] ℝ)` of polynomial
growth,

`∫ (Ψ x) x ∂μ = ∑ i, ∫ ((DΨ x) (C bᵢ)) bᵢ ∂μ`

for any orthonormal basis `(bᵢ)`. The right-hand side is the trace of `C ∘ DΨ x`, so the identity
reads `∫ (Ψ x) x = ∫ tr (C ∘ DΨ)`: it is the divergence (Stein) form of Gaussian integration by
parts on a Hilbert space.

Covector fields are the right generality: the vector-field form is the case `Ψ = ⟪V ·, ·⟫` and the
scalar form is the case `Ψ = DF`, which is what every Gaussian interpolation computation needs.
Writing `z_t = √t x + √(1-t) y`, the derivative of `t ↦ 𝔼 F(z_t)` produces terms `𝔼 (DF(z_t)) X`,
and this identity converts each into a covariance-weighted trace of the Hessian — Talagrand
Vol. I, §1.3 (Eq. (1.65)) and Vol. II, §8.2. Slepian's and the Sudakov–Fernique inequalities are
sign consequences of the same trace.

## Main statements

- `IsGaussian.integral_apply_self_eq_sum_integral_fderiv_covarianceOperator`: the divergence
  identity for a covector field (the general theorem).
- `IsGaussian.integral_inner_vectorField_eq_sum_integral_fderiv`: the vector-field form.
- `IsGaussian.integral_fderiv_apply_self_eq_sum_integral_fderiv2`: the scalar `C²` form, giving
  the covariance-weighted Hessian trace.
-/

open scoped Filter BigOperators Topology ProbabilityTheory ENNReal InnerProductSpace NNReal
open MeasureTheory Filter Set

noncomputable section

namespace ProbabilityTheory

section Hilbert

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {μ : Measure E} [IsGaussian μ]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Expansion of a continuous linear functional along an orthonormal basis. -/
private lemma apply_eq_sum_inner_mul (b : OrthonormalBasis ι ℝ E) (L : E →L[ℝ] ℝ) (x : E) :
    L x = ∑ i : ι, ⟪x, b i⟫_ℝ * L (b i) := by
  classical
  calc L x = L (∑ i : ι, ⟪b i, x⟫_ℝ • b i) := by rw [b.sum_repr' x]
    _ = ∑ i : ι, ⟪b i, x⟫_ℝ * L (b i) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    _ = ∑ i : ι, ⟪x, b i⟫_ℝ * L (b i) :=
        Finset.sum_congr rfl fun i _ => by rw [real_inner_comm (b i) x]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Derivative of a coordinate field `x ↦ (Ψ x) v` of a covector field. -/
private lemma hasFDerivAt_covector_coord {Ψ : E → E →L[ℝ] ℝ} {Ψ' : E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hΨ : HasFDerivAt Ψ Ψ' x) (v : E) :
    HasFDerivAt (fun y : E => (Ψ y) v) ((ContinuousLinearMap.apply ℝ ℝ v).comp Ψ') x :=
  (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp x hΨ

namespace IsGaussian

variable (μ)

/-- **Gaussian divergence identity (Stein's identity for covector fields).** For a centered
Gaussian `μ`, an orthonormal basis `b`, and a `C¹` covector field `Ψ` with polynomial growth of
`Ψ` and `DΨ`,

`∫ (Ψ x) x ∂μ = ∑ i, ∫ ((DΨ x) (C bᵢ)) bᵢ ∂μ`,

the right-hand side being the trace of `C ∘ DΨ x`. Talagrand Vol. I, Appendix A.3. -/
theorem integral_apply_self_eq_sum_integral_fderiv_covarianceOperator
    (hmean0 : (∫ x : E, x ∂μ) = 0) (b : OrthonormalBasis ι ℝ E)
    (Ψ : E → E →L[ℝ] ℝ) (hΨ_meas : Measurable Ψ) (hΨ_c1 : ContDiff ℝ 1 Ψ)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hΨ_growth : ∀ x, ‖Ψ x‖ ≤ C * (1 + ‖x‖) ^ m)
    (hΨ'_growth : ∀ x, ‖fderiv ℝ Ψ x‖ ≤ C * (1 + ‖x‖) ^ m) :
    (∫ x : E, (Ψ x) x ∂μ)
      = ∑ i : ι, ∫ x : E,
          ((fderiv ℝ Ψ x) (covarianceOperator μ (b i))) (b i) ∂μ := by
  classical
  have hΨdiff : ∀ x : E, HasFDerivAt Ψ (fderiv ℝ Ψ x) x := fun x =>
    (hΨ_c1.differentiable (by norm_num) x).hasFDerivAt
  have hb_norm : ∀ i : ι, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  -- The scalar coordinate fields of `Ψ`.
  set F : ι → E → ℝ := fun i x => (Ψ x) (b i) with hF
  have hF_meas : ∀ i, Measurable (F i) := fun i =>
    ((ContinuousLinearMap.apply ℝ ℝ (b i)).continuous.measurable).comp hΨ_meas
  have hF_c1 : ∀ i, ContDiff ℝ 1 (F i) := fun i =>
    (ContinuousLinearMap.apply ℝ ℝ (b i)).contDiff.comp hΨ_c1
  have hF_fderiv : ∀ i, ∀ x : E, fderiv ℝ (F i) x
      = (ContinuousLinearMap.apply ℝ ℝ (b i)).comp (fderiv ℝ Ψ x) := fun i x =>
    (hasFDerivAt_covector_coord (hΨdiff x) (b i)).fderiv
  -- Coordinates of a covector inherit its bound, since basis vectors are unit vectors.
  have hF_growth : ∀ i, ∀ x, |F i x| ≤ C * (1 + ‖x‖) ^ m := by
    intro i x
    calc |F i x| = ‖(Ψ x) (b i)‖ := by simp [hF, Real.norm_eq_abs]
      _ ≤ ‖Ψ x‖ * ‖b i‖ := (Ψ x).le_opNorm (b i)
      _ = ‖Ψ x‖ := by rw [hb_norm i, mul_one]
      _ ≤ C * (1 + ‖x‖) ^ m := hΨ_growth x
  have hF'_growth : ∀ i, ∀ x, ‖fderiv ℝ (F i) x‖ ≤ C * (1 + ‖x‖) ^ m := by
    intro i x
    rw [hF_fderiv i x]
    have hop : ‖(ContinuousLinearMap.apply ℝ ℝ (b i)).comp (fderiv ℝ Ψ x)‖
        ≤ ‖fderiv ℝ Ψ x‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (fderiv ℝ Ψ x)) (fun v => ?_)
      calc ‖((ContinuousLinearMap.apply ℝ ℝ (b i)).comp (fderiv ℝ Ψ x)) v‖
          = ‖((fderiv ℝ Ψ x) v) (b i)‖ := by
            simp [ContinuousLinearMap.apply_apply]
        _ ≤ ‖(fderiv ℝ Ψ x) v‖ * ‖b i‖ := ((fderiv ℝ Ψ x) v).le_opNorm (b i)
        _ = ‖(fderiv ℝ Ψ x) v‖ := by rw [hb_norm i, mul_one]
        _ ≤ ‖fderiv ℝ Ψ x‖ * ‖v‖ := (fderiv ℝ Ψ x).le_opNorm v
    exact hop.trans (hΨ'_growth x)
  -- Each coordinate term is integrable, so the finite sum passes through the integral.
  have hInt : ∀ i : ι, Integrable (fun x : E => ⟪x, b i⟫_ℝ * F i x) μ := by
    intro i
    refine integrable_of_abs_le_mul_one_add_norm_pow (μ := μ) ?_
      (C := C) (m := m + 1) hC (fun x => ?_)
    · have hmeas : Measurable fun x : E => ⟪x, b i⟫_ℝ := by
        have h := (innerSL ℝ (b i)).continuous.measurable
        simpa [real_inner_comm] using h
      exact hmeas.mul (hF_meas i)
    · have h1 : |⟪x, b i⟫_ℝ| ≤ 1 + ‖x‖ := by
        calc |⟪x, b i⟫_ℝ| ≤ ‖x‖ * ‖b i‖ := abs_real_inner_le_norm x (b i)
          _ = ‖x‖ := by rw [hb_norm i, mul_one]
          _ ≤ 1 + ‖x‖ := by linarith
      calc |⟪x, b i⟫_ℝ * F i x| = |⟪x, b i⟫_ℝ| * |F i x| := abs_mul _ _
        _ ≤ (1 + ‖x‖) * (C * (1 + ‖x‖) ^ m) :=
            mul_le_mul h1 (hF_growth i x) (abs_nonneg _) (by positivity)
        _ = C * (1 + ‖x‖) ^ (m + 1) := by ring
  calc (∫ x : E, (Ψ x) x ∂μ)
      = ∫ x : E, ∑ i : ι, ⟪x, b i⟫_ℝ * F i x ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun x =>
          apply_eq_sum_inner_mul b (Ψ x) x)
    _ = ∑ i : ι, ∫ x : E, ⟪x, b i⟫_ℝ * F i x ∂μ :=
        integral_finsetSum _ (fun i _ => hInt i)
    _ = ∑ i : ι, ∫ x : E, (fderiv ℝ (F i) x) (covarianceOperator μ (b i)) ∂μ :=
        Finset.sum_congr rfl fun i _ =>
          integral_inner_mul_eq_integral_fderiv_covarianceOperator (μ := μ) hmean0 (b i)
            (F i) (hF_meas i) (hF_c1 i) hC (hF_growth i) (hF'_growth i)
    _ = ∑ i : ι, ∫ x : E,
          ((fderiv ℝ Ψ x) (covarianceOperator μ (b i))) (b i) ∂μ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp [hF_fderiv i x, ContinuousLinearMap.apply_apply]

/-- **Vector-field form of the Gaussian divergence identity.** For a `C¹` vector field `V` with
polynomial growth of `V` and `DV`,
`∫ ⟪x, V x⟫ ∂μ = ∑ i, ∫ ⟪(DV x) (C bᵢ), bᵢ⟫ ∂μ`.
Mathematically this is the covector identity transported along the Riesz isometry; the proof below
runs the same coordinate argument directly on `x ↦ ⟪V x, bᵢ⟫`. -/
theorem integral_inner_vectorField_eq_sum_integral_fderiv
    (hmean0 : (∫ x : E, x ∂μ) = 0) (b : OrthonormalBasis ι ℝ E)
    (V : E → E) (hV_meas : Measurable V) (hV_c1 : ContDiff ℝ 1 V)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hV_growth : ∀ x, ‖V x‖ ≤ C * (1 + ‖x‖) ^ m)
    (hV'_growth : ∀ x, ‖fderiv ℝ V x‖ ≤ C * (1 + ‖x‖) ^ m) :
    (∫ x : E, ⟪x, V x⟫_ℝ ∂μ)
      = ∑ i : ι, ∫ x : E, ⟪(fderiv ℝ V x) (covarianceOperator μ (b i)), b i⟫_ℝ ∂μ := by
  classical
  have hVdiff : ∀ x : E, HasFDerivAt V (fderiv ℝ V x) x := fun x =>
    (hV_c1.differentiable (by norm_num) x).hasFDerivAt
  have hb_norm : ∀ i : ι, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  set F : ι → E → ℝ := fun i x => ⟪V x, b i⟫_ℝ with hF
  have hcoord : ∀ (e : E), (fun x : E => ⟪V x, e⟫_ℝ) = (fun y : E => (innerSL ℝ e) y) ∘ V := by
    intro e; funext x; exact real_inner_comm _ _
  have hF_meas : ∀ i, Measurable (F i) := by
    intro i
    have h := ((innerSL ℝ (b i)).continuous.measurable).comp hV_meas
    simpa [hF, hcoord (b i), Function.comp_def] using h
  have hF_c1 : ∀ i, ContDiff ℝ 1 (F i) := by
    intro i
    simpa [hF, hcoord (b i)] using (innerSL ℝ (b i)).contDiff.comp hV_c1
  have hF_fderiv : ∀ i, ∀ x : E,
      fderiv ℝ (F i) x = (innerSL ℝ (b i)).comp (fderiv ℝ V x) := by
    intro i x
    have h : HasFDerivAt (fun y : E => ⟪V y, b i⟫_ℝ)
        ((innerSL ℝ (b i)).comp (fderiv ℝ V x)) x := by
      rw [hcoord (b i)]
      exact ((innerSL ℝ (b i)).hasFDerivAt.comp x (hVdiff x))
    simpa [hF] using h.fderiv
  have hF_growth : ∀ i, ∀ x, |F i x| ≤ C * (1 + ‖x‖) ^ m := by
    intro i x
    calc |F i x| ≤ ‖V x‖ * ‖b i‖ := by
          simpa [hF] using abs_real_inner_le_norm (V x) (b i)
      _ = ‖V x‖ := by rw [hb_norm i, mul_one]
      _ ≤ C * (1 + ‖x‖) ^ m := hV_growth x
  have hF'_growth : ∀ i, ∀ x, ‖fderiv ℝ (F i) x‖ ≤ C * (1 + ‖x‖) ^ m := by
    intro i x
    rw [hF_fderiv i x]
    have hop : ‖(innerSL ℝ (b i)).comp (fderiv ℝ V x)‖ ≤ ‖fderiv ℝ V x‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (fderiv ℝ V x)) (fun v => ?_)
      calc ‖((innerSL ℝ (b i)).comp (fderiv ℝ V x)) v‖
          = ‖⟪b i, (fderiv ℝ V x) v⟫_ℝ‖ := rfl
        _ ≤ ‖b i‖ * ‖(fderiv ℝ V x) v‖ := by
            simpa [Real.norm_eq_abs] using abs_real_inner_le_norm (b i) ((fderiv ℝ V x) v)
        _ = ‖(fderiv ℝ V x) v‖ := by rw [hb_norm i, one_mul]
        _ ≤ ‖fderiv ℝ V x‖ * ‖v‖ := (fderiv ℝ V x).le_opNorm v
    exact hop.trans (hV'_growth x)
  have hParseval : ∀ x : E, ⟪x, V x⟫_ℝ = ∑ i : ι, ⟪x, b i⟫_ℝ * F i x := by
    intro x
    rw [hF, ← b.sum_inner_mul_inner (𝕜 := ℝ) x (V x)]
    exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm (V x) (b i)]
  have hInt : ∀ i : ι, Integrable (fun x : E => ⟪x, b i⟫_ℝ * F i x) μ := by
    intro i
    refine integrable_of_abs_le_mul_one_add_norm_pow (μ := μ) ?_
      (C := C) (m := m + 1) hC (fun x => ?_)
    · have hmeas : Measurable fun x : E => ⟪x, b i⟫_ℝ := by
        have h := (innerSL ℝ (b i)).continuous.measurable
        simpa [real_inner_comm] using h
      exact hmeas.mul (hF_meas i)
    · have h1 : |⟪x, b i⟫_ℝ| ≤ 1 + ‖x‖ := by
        calc |⟪x, b i⟫_ℝ| ≤ ‖x‖ * ‖b i‖ := abs_real_inner_le_norm x (b i)
          _ = ‖x‖ := by rw [hb_norm i, mul_one]
          _ ≤ 1 + ‖x‖ := by linarith
      calc |⟪x, b i⟫_ℝ * F i x| = |⟪x, b i⟫_ℝ| * |F i x| := abs_mul _ _
        _ ≤ (1 + ‖x‖) * (C * (1 + ‖x‖) ^ m) :=
            mul_le_mul h1 (hF_growth i x) (abs_nonneg _) (by positivity)
        _ = C * (1 + ‖x‖) ^ (m + 1) := by ring
  calc (∫ x : E, ⟪x, V x⟫_ℝ ∂μ)
      = ∫ x : E, ∑ i : ι, ⟪x, b i⟫_ℝ * F i x ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall hParseval)
    _ = ∑ i : ι, ∫ x : E, ⟪x, b i⟫_ℝ * F i x ∂μ :=
        integral_finsetSum _ (fun i _ => hInt i)
    _ = ∑ i : ι, ∫ x : E, (fderiv ℝ (F i) x) (covarianceOperator μ (b i)) ∂μ :=
        Finset.sum_congr rfl fun i _ =>
          integral_inner_mul_eq_integral_fderiv_covarianceOperator (μ := μ) hmean0 (b i)
            (F i) (hF_meas i) (hF_c1 i) hC (hF_growth i) (hF'_growth i)
    _ = ∑ i : ι, ∫ x : E,
          ⟪(fderiv ℝ V x) (covarianceOperator μ (b i)), b i⟫_ℝ ∂μ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [hF_fderiv i x, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
        exact real_inner_comm _ _

/-- **Scalar form: the covariance-weighted Hessian trace.** For `F : E → ℝ` of class `C²` with
polynomial growth of `DF` and `D²F`,
`∫ (DF x) x ∂μ = ∑ i, ∫ (D²F x) (C bᵢ) bᵢ ∂μ`.
This is the identity behind Talagrand's interpolation formula, Vol. I, Eq. (1.65). -/
theorem integral_fderiv_apply_self_eq_sum_integral_fderiv2
    (hmean0 : (∫ x : E, x ∂μ) = 0) (b : OrthonormalBasis ι ℝ E)
    (F : E → ℝ) (hF_c2 : ContDiff ℝ 2 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF'_growth : ∀ x, ‖fderiv ℝ F x‖ ≤ C * (1 + ‖x‖) ^ m)
    (hF''_growth : ∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ C * (1 + ‖x‖) ^ m) :
    (∫ x : E, (fderiv ℝ F x) x ∂μ)
      = ∑ i : ι, ∫ x : E,
          ((fderiv ℝ (fderiv ℝ F) x) (covarianceOperator μ (b i))) (b i) ∂μ := by
  have hDFc1 : ContDiff ℝ 1 (fderiv ℝ F) := hF_c2.fderiv_right (by norm_num)
  exact integral_apply_self_eq_sum_integral_fderiv_covarianceOperator (μ := μ) hmean0 b
    (fderiv ℝ F) hDFc1.continuous.measurable hDFc1 hC hF'_growth hF''_growth

end IsGaussian

/-! ### Linear substitutions

The general statement allows *two* linear maps: the Hamiltonian is `A x + c` and the vector paired
against its gradient is `B x`. Interpolation needs exactly this, because the interpolated
Hamiltonian and its time-derivative are different linear images of the same disorder. -/

section Substitution

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [CompleteSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
/-- `1 + ‖L x + c‖ ≤ (1 + ‖c‖) * (1 + ‖L‖) * (1 + ‖x‖)`. -/
lemma one_add_norm_clm_add_le (L : E →L[ℝ] G) (c : G) (x : E) :
    1 + ‖L x + c‖ ≤ (1 + ‖c‖) * (1 + ‖L‖) * (1 + ‖x‖) := by
  have h1 : ‖L x + c‖ ≤ ‖L‖ * ‖x‖ + ‖c‖ := by
    refine (norm_add_le _ _).trans ?_
    gcongr
    exact L.le_opNorm x
  nlinarith [norm_nonneg x, norm_nonneg c, norm_nonneg L,
    mul_nonneg (norm_nonneg L) (norm_nonneg x), mul_nonneg (norm_nonneg c) (norm_nonneg L),
    mul_nonneg (mul_nonneg (norm_nonneg c) (norm_nonneg L)) (norm_nonneg x)]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [CompleteSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
/-- Polynomial growth transports along an affine map `x ↦ L x + c`. -/
lemma polyGrowth_comp_clm_add {F' : Type*} [NormedAddCommGroup F'] {g : G → F'}
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C) (hg : ∀ z, ‖g z‖ ≤ C * (1 + ‖z‖) ^ m)
    (L : E →L[ℝ] G) (c : G) :
    ∀ x, ‖g (L x + c)‖ ≤ (C * ((1 + ‖c‖) * (1 + ‖L‖)) ^ m) * (1 + ‖x‖) ^ m := by
  intro x
  have hb : (0 : ℝ) ≤ 1 + ‖L x + c‖ := by positivity
  have hmono : (1 + ‖L x + c‖) ^ m ≤ ((1 + ‖c‖) * (1 + ‖L‖) * (1 + ‖x‖)) ^ m :=
    pow_le_pow_left₀ hb (one_add_norm_clm_add_le L c x) m
  calc ‖g (L x + c)‖ ≤ C * (1 + ‖L x + c‖) ^ m := hg _
    _ ≤ C * ((1 + ‖c‖) * (1 + ‖L‖) * (1 + ‖x‖)) ^ m := mul_le_mul_of_nonneg_left hmono hC
    _ = (C * ((1 + ‖c‖) * (1 + ‖L‖)) ^ m) * (1 + ‖x‖) ^ m := by rw [mul_pow]; ring

namespace IsGaussian

omit [CompleteSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
/-- **Two-map Gaussian trace identity.** For a centered Gaussian `μ` on `E`, an orthonormal basis
`b`, continuous linear maps `A B : E →L[ℝ] G`, a shift `c : G`, and `F : G → ℝ` of class `C²` with
polynomially bounded `DF`, `D²F`,

`∫ (DF (A x + c)) (B x) ∂μ = ∑ i, ∫ ((D²F (A x + c)) (A (C bᵢ))) (B bᵢ) ∂μ`.

This is the general theorem behind Gaussian interpolation: `A` is the map producing the
Hamiltonian, `B` the map producing the vector paired against its gradient (for interpolation, the
time-derivative of `A`). Talagrand Vol. I, §1.3, Eq. (1.65); Appendix A.3. -/
theorem integral_fderiv_clm_add_apply_clm_eq_sum
    (hmean0 : (∫ x : E, x ∂μ) = 0) (b : OrthonormalBasis ι ℝ E)
    (A B : E →L[ℝ] G) (c : G)
    (F : G → ℝ) (hF_c2 : ContDiff ℝ 2 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF'_growth : ∀ z, ‖fderiv ℝ F z‖ ≤ C * (1 + ‖z‖) ^ m)
    (hF''_growth : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ C * (1 + ‖z‖) ^ m) :
    (∫ x : E, (fderiv ℝ F (A x + c)) (B x) ∂μ)
      = ∑ i : ι, ∫ x : E,
          ((fderiv ℝ (fderiv ℝ F) (A x + c)) (A (covarianceOperator μ (b i))))
            (B (b i)) ∂μ := by
  classical
  -- Precomposition by `B`, as a continuous linear map on the dual.
  set P : (G →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) := (ContinuousLinearMap.compL ℝ E G ℝ).flip B with hPdef
  have hPapply : ∀ L : G →L[ℝ] ℝ, P L = L.comp B := fun L => rfl
  have hPnorm : ‖P‖ ≤ ‖B‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B) (fun L => ?_)
    rw [hPapply L]
    calc ‖L.comp B‖ ≤ ‖L‖ * ‖B‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖B‖ * ‖L‖ := mul_comm _ _
  have hDF : ContDiff ℝ 1 (fderiv ℝ F) := hF_c2.fderiv_right (by norm_num)
  have hAff : ContDiff ℝ 1 (fun x : E => A x + c) := by fun_prop
  have hΨ_c1 : ContDiff ℝ 1 (fun x : E => P (fderiv ℝ F (A x + c))) :=
    P.contDiff.comp (hDF.comp hAff)
  have hΨ_meas : Measurable (fun x : E => P (fderiv ℝ F (A x + c))) :=
    hΨ_c1.continuous.measurable
  have hΨ_fderiv : ∀ x : E, fderiv ℝ (fun y : E => P (fderiv ℝ F (A y + c))) x
      = P.comp ((fderiv ℝ (fderiv ℝ F) (A x + c)).comp A) := by
    intro x
    have hA : HasFDerivAt (fun y : E => A y + c) A x := (A.hasFDerivAt).add_const c
    have hG : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) (A x + c)) (A x + c) :=
      (hDF.differentiable (by norm_num) (A x + c)).hasFDerivAt
    exact ((P.hasFDerivAt).comp x (hG.comp x hA)).fderiv
  -- One constant for both growth bounds.
  set K : ℝ := (1 + ‖c‖) * (1 + ‖A‖) with hK
  set C' : ℝ := (1 + ‖A‖) * (1 + ‖B‖) * (C * K ^ m) with hC'
  have hKnn : (0 : ℝ) ≤ K := by rw [hK]; positivity
  have hCKnn : (0 : ℝ) ≤ C * K ^ m := by positivity
  have hC'nn : (0 : ℝ) ≤ C' := by rw [hC']; positivity
  have hgrowth1 : ∀ x : E, ‖fderiv ℝ F (A x + c)‖ ≤ (C * K ^ m) * (1 + ‖x‖) ^ m := by
    intro x
    rw [hK]
    exact polyGrowth_comp_clm_add (g := fderiv ℝ F) (C := C) (m := m)
      hC hF'_growth A c x
  have hgrowth2 : ∀ x : E, ‖fderiv ℝ (fderiv ℝ F) (A x + c)‖
      ≤ (C * K ^ m) * (1 + ‖x‖) ^ m := by
    intro x
    rw [hK]
    exact polyGrowth_comp_clm_add (g := fderiv ℝ (fderiv ℝ F)) (C := C) (m := m)
      hC hF''_growth A c x
  have hΨ_growth : ∀ x : E, ‖P (fderiv ℝ F (A x + c))‖ ≤ C' * (1 + ‖x‖) ^ m := by
    intro x
    have h1 : ‖P (fderiv ℝ F (A x + c))‖ ≤ ‖B‖ * ‖fderiv ℝ F (A x + c)‖ := by
      rw [hPapply]
      calc ‖(fderiv ℝ F (A x + c)).comp B‖ ≤ ‖fderiv ℝ F (A x + c)‖ * ‖B‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ = ‖B‖ * ‖fderiv ℝ F (A x + c)‖ := mul_comm _ _
    have h2 : ‖B‖ * ‖fderiv ℝ F (A x + c)‖ ≤ ‖B‖ * ((C * K ^ m) * (1 + ‖x‖) ^ m) :=
      mul_le_mul_of_nonneg_left (hgrowth1 x) (norm_nonneg B)
    refine (h1.trans h2).trans ?_
    rw [hC']
    have hb : ‖B‖ ≤ (1 + ‖A‖) * (1 + ‖B‖) := by
      nlinarith [norm_nonneg A, norm_nonneg B]
    calc ‖B‖ * ((C * K ^ m) * (1 + ‖x‖) ^ m)
        = ‖B‖ * (C * K ^ m) * (1 + ‖x‖) ^ m := by ring
      _ ≤ ((1 + ‖A‖) * (1 + ‖B‖)) * (C * K ^ m) * (1 + ‖x‖) ^ m := by
          have := mul_le_mul_of_nonneg_right hb hCKnn
          exact mul_le_mul_of_nonneg_right this (by positivity)
  have hΨ'_growth : ∀ x : E, ‖fderiv ℝ (fun y : E => P (fderiv ℝ F (A y + c))) x‖
      ≤ C' * (1 + ‖x‖) ^ m := by
    intro x
    rw [hΨ_fderiv x]
    have h1 : ‖P.comp ((fderiv ℝ (fderiv ℝ F) (A x + c)).comp A)‖
        ≤ ‖B‖ * (‖fderiv ℝ (fderiv ℝ F) (A x + c)‖ * ‖A‖) := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      have hAB := ContinuousLinearMap.opNorm_comp_le
        (fderiv ℝ (fderiv ℝ F) (A x + c)) A
      calc ‖P‖ * ‖(fderiv ℝ (fderiv ℝ F) (A x + c)).comp A‖
          ≤ ‖B‖ * ‖(fderiv ℝ (fderiv ℝ F) (A x + c)).comp A‖ :=
            mul_le_mul_of_nonneg_right hPnorm
              (norm_nonneg ((fderiv ℝ (fderiv ℝ F) (A x + c)).comp A))
        _ ≤ ‖B‖ * (‖fderiv ℝ (fderiv ℝ F) (A x + c)‖ * ‖A‖) :=
            mul_le_mul_of_nonneg_left hAB (norm_nonneg B)
    refine h1.trans ?_
    rw [hC']
    have h2 : ‖fderiv ℝ (fderiv ℝ F) (A x + c)‖ * ‖A‖
        ≤ ((C * K ^ m) * (1 + ‖x‖) ^ m) * ‖A‖ :=
      mul_le_mul_of_nonneg_right (hgrowth2 x) (norm_nonneg A)
    have hab : ‖B‖ * ‖A‖ ≤ (1 + ‖A‖) * (1 + ‖B‖) := by
      nlinarith [norm_nonneg A, norm_nonneg B]
    calc ‖B‖ * (‖fderiv ℝ (fderiv ℝ F) (A x + c)‖ * ‖A‖)
        ≤ ‖B‖ * (((C * K ^ m) * (1 + ‖x‖) ^ m) * ‖A‖) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg B)
      _ = (‖B‖ * ‖A‖) * (C * K ^ m) * (1 + ‖x‖) ^ m := by ring
      _ ≤ ((1 + ‖A‖) * (1 + ‖B‖)) * (C * K ^ m) * (1 + ‖x‖) ^ m := by
          have := mul_le_mul_of_nonneg_right hab hCKnn
          exact mul_le_mul_of_nonneg_right this (by positivity)
  have hmain := integral_apply_self_eq_sum_integral_fderiv_covarianceOperator (μ := μ) hmean0 b
    (fun x : E => P (fderiv ℝ F (A x + c))) hΨ_meas hΨ_c1 hC'nn hΨ_growth hΨ'_growth
  have hlhs : (∫ x : E, (P (fderiv ℝ F (A x + c))) x ∂μ)
      = ∫ x : E, (fderiv ℝ F (A x + c)) (B x) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [hPapply]
  rw [← hlhs, hmain]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change ((fderiv ℝ (fun y : E => P (fderiv ℝ F (A y + c))) x)
      (covarianceOperator μ (b i))) (b i)
    = ((fderiv ℝ (fderiv ℝ F) (A x + c)) (A (covarianceOperator μ (b i)))) (B (b i))
  rw [hΨ_fderiv x]
  simp [hPapply]

/-- **Affine Gaussian trace identity**: the case `A = a • id`, `B = id` of
`integral_fderiv_clm_add_apply_clm_eq_sum`.

`∫ (DF (a • x + c)) x ∂μ = a * ∑ i, ∫ ((D²F (a • x + c)) (C bᵢ)) bᵢ ∂μ`.

Talagrand Vol. I, §1.3, Eq. (1.65). -/
theorem integral_fderiv_affine_apply_self_eq_sum
    (hmean0 : (∫ x : E, x ∂μ) = 0) (b : OrthonormalBasis ι ℝ E)
    (F : E → ℝ) (hF_c2 : ContDiff ℝ 2 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF'_growth : ∀ x, ‖fderiv ℝ F x‖ ≤ C * (1 + ‖x‖) ^ m)
    (hF''_growth : ∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ C * (1 + ‖x‖) ^ m)
    (a : ℝ) (c : E) :
    (∫ x : E, (fderiv ℝ F (a • x + c)) x ∂μ)
      = a * ∑ i : ι, ∫ x : E,
          ((fderiv ℝ (fderiv ℝ F) (a • x + c)) (covarianceOperator μ (b i))) (b i) ∂μ := by
  classical
  have h := integral_fderiv_clm_add_apply_clm_eq_sum (μ := μ) hmean0 b
    (a • ContinuousLinearMap.id ℝ E) (ContinuousLinearMap.id ℝ E) c F hF_c2 hC
    hF'_growth hF''_growth
  simp only [smul_apply, ContinuousLinearMap.id_apply] at h
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [map_smul]


end IsGaussian

end Substitution

/-! ### Pushforward covariance -/

section Pushforward

namespace IsGaussian

variable {κ : Type*} [Fintype κ]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

/-- A continuous linear image of a centered measure is centered. -/
lemma integral_id_map_eq_zero (A : E →L[ℝ] G) (hmean0 : (∫ x : E, x ∂μ) = 0) :
    (∫ z : G, z ∂(μ.map A)) = 0 := by
  have hint : Integrable (fun x : E => x) μ :=
    ProbabilityTheory.IsGaussian.integrable_id (μ := μ)
  calc (∫ z : G, z ∂(μ.map A)) = ∫ x : E, A x ∂μ := by
        rw [integral_map A.continuous.measurable.aemeasurable
          (by fun_prop : AEStronglyMeasurable (fun z : G => z) (μ.map A))]
    _ = A (∫ x : E, x ∂μ) := A.integral_comp_comm hint
    _ = 0 := by rw [hmean0, map_zero]

/-- **Gaussian trace identity along a linear substitution**, with explicit growth constants. For a
centered Gaussian `μ` on `E`, a continuous linear `A : E →L[ℝ] G`, a shift `c : G`, an orthonormal
basis `bG` of `G`, and `F : G → ℝ` of class `C²` with polynomially bounded `DF`, `D²F`,

`∫ (DF (A x + c)) (A x) ∂μ = ∑ j, ∫ ((D²F (A x + c)) (C' bⱼ)) bⱼ ∂μ`

where `C' = covarianceOperator (μ.map A)` is the covariance of the *image* `A x`. This is the
form the interpolation method consumes: the Hamiltonian is a linear image of the disorder, and the
Hessian trace is taken against the covariance of that image.
Talagrand Vol. I, §1.3, Eq. (1.65). -/
theorem integral_fderiv_comp_clm_apply_self_eq_sum
    (hmean0 : (∫ x : E, x ∂μ) = 0) (A : E →L[ℝ] G) (c : G) (bG : OrthonormalBasis κ ℝ G)
    (F : G → ℝ) (hF_c2 : ContDiff ℝ 2 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF'_growth : ∀ z, ‖fderiv ℝ F z‖ ≤ C * (1 + ‖z‖) ^ m)
    (hF''_growth : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ C * (1 + ‖z‖) ^ m) :
    (∫ x : E, (fderiv ℝ F (A x + c)) (A x) ∂μ)
      = ∑ j : κ, ∫ x : E,
          ((fderiv ℝ (fderiv ℝ F) (A x + c))
            (covarianceOperator (μ.map A) (bG j))) (bG j) ∂μ := by
  classical
  have hAmeas : AEMeasurable A μ := A.continuous.measurable.aemeasurable
  have hmean' : (∫ z : G, z ∂(μ.map A)) = 0 := integral_id_map_eq_zero (μ := μ) A hmean0
  have hDF : ContDiff ℝ 1 (fderiv ℝ F) := hF_c2.fderiv_right (by norm_num)
  -- The `a = 1` affine identity, on the pushforward Gaussian.
  have hkey := integral_fderiv_affine_apply_self_eq_sum (μ := μ.map A) hmean' bG F hF_c2 hC
    hF'_growth hF''_growth 1 c
  have hDFcont : Continuous fun z : G => fderiv ℝ F ((1 : ℝ) • z + c) :=
    hDF.continuous.comp (by fun_prop)
  have hD2Fcont : Continuous fun z : G => fderiv ℝ (fderiv ℝ F) ((1 : ℝ) • z + c) :=
    (hDF.fderiv_right (m := 0) (by norm_num)).continuous.comp (by fun_prop)
  have hlhs : (∫ z : G, (fderiv ℝ F ((1 : ℝ) • z + c)) z ∂(μ.map A))
      = ∫ x : E, (fderiv ℝ F (A x + c)) (A x) ∂μ := by
    have hm : AEStronglyMeasurable (fun z : G => (fderiv ℝ F ((1 : ℝ) • z + c)) z) (μ.map A) :=
      ((isBoundedBilinearMap_apply.continuous).comp
        (hDFcont.prodMk continuous_id)).aestronglyMeasurable
    rw [integral_map hAmeas hm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp
  have hrhs : ∀ j : κ,
      (∫ z : G, ((fderiv ℝ (fderiv ℝ F) ((1 : ℝ) • z + c))
            (covarianceOperator (μ.map A) (bG j))) (bG j) ∂(μ.map A))
        = ∫ x : E, ((fderiv ℝ (fderiv ℝ F) (A x + c))
            (covarianceOperator (μ.map A) (bG j))) (bG j) ∂μ := by
    intro j
    have hm : AEStronglyMeasurable
        (fun z : G => ((fderiv ℝ (fderiv ℝ F) ((1 : ℝ) • z + c))
          (covarianceOperator (μ.map A) (bG j))) (bG j)) (μ.map A) :=
      (((ContinuousLinearMap.apply ℝ ℝ (bG j)).continuous).comp
        (((ContinuousLinearMap.apply ℝ (G →L[ℝ] ℝ)
          (covarianceOperator (μ.map A) (bG j))).continuous).comp
            hD2Fcont)).aestronglyMeasurable
    rw [integral_map hAmeas hm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp
  rw [← hlhs, hkey, one_mul]
  exact Finset.sum_congr rfl fun j _ => hrhs j

end IsGaussian

end Pushforward

end Hilbert

end ProbabilityTheory
