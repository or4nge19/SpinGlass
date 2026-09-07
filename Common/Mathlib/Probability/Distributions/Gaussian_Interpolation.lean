/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.Distributions.Gaussian_IBP_Temperate

/-!
# The Gaussian interpolation trace identity

Let `P` be a centered Gaussian measure on the `L²`-product `WithLp 2 (E × E)` of a real Hilbert
space with itself, whose covariance operator is **block diagonal** with blocks `u` and `v` read on
an orthonormal basis `b` of `E`. Write

`Z t (x, y) = √t · x + √(1-t) · y`

for the interpolation path and `Ż t` for its time derivative. For a smooth `F : E → ℝ` of temperate
growth and `t ∈ (0,1)`,

`∫ (DF (Z t p + c)) (Ż t p) ∂P = (1/2) ∑ i, [ (D²F (Z t p + c)) (u i) (b i)
                                            - (D²F (Z t p + c)) (v i) (b i) ]`

integrated against `P`. The left-hand side is what differentiating `t ↦ ∫ F (Z t p + c) ∂P`
produces; the right-hand side is a difference of covariance-weighted Hessian traces. This single
identity is the engine of

* Slepian's inequality and the Sudakov–Fernique inequality (the sign of the right-hand side),
* Guerra's replica-symmetric bound (Talagrand, *Mean Field Models for Spin Glasses* I, §1.3),
* the smart-path / interpolation method generally (Talagrand II, §8.2).

It is a corollary of the two-map Gaussian trace identity
`ProbabilityTheory.IsGaussian.integral_fderiv_clm_add_apply_clm_eq_sum`: the interpolation is the
substitution `p ↦ (Z t p + c, Ż t p)` by two *different* continuous linear maps, the product
orthonormal basis `b.prod b` splits the trace into the two blocks, and the scalars collapse
because `√t · (1/(2√t)) = 1/2` and `√(1-t) · (-1/(2√(1-t))) = -1/2`.

## Main definitions

- `ProbabilityTheory.gaussianInterp`: the interpolation `(x, y) ↦ √t · x + √(1-t) · y`, as a
  continuous linear map.
- `ProbabilityTheory.gaussianInterpDeriv`: its derivative in `t`.

## Main statements

- `ProbabilityTheory.hasDerivAt_gaussianInterp`: `Ż t` is indeed the `t`-derivative of `Z t`.
- `ProbabilityTheory.IsGaussian.integral_fderiv_gaussianInterp_apply_deriv_eq_sum`: the
  interpolation trace identity, with explicit polynomial bounds on `DF` and `D²F` (the weakest
  hypotheses).
- `ProbabilityTheory.IsGaussian.integral_fderiv_gaussianInterp_apply_deriv`: the same under the
  single hypothesis `Function.HasTemperateGrowth`.
- `ProbabilityTheory.IsGaussian.hasDerivAt_integral_gaussianInterp` and
  `..._eq_sum`: `s ↦ ∫ F (Z s p + c) ∂P` is differentiable on `(0,1)`, with derivative the trace
  above (differentiation under the integral sign, dominated on compact subintervals).
- `ProbabilityTheory.IsGaussian.continuousOn_integral_gaussianInterp`: it is continuous on `[0,1]`.
- `ProbabilityTheory.IsGaussian.integral_le_integral_of_trace_nonneg` and
  `..._of_fderiv2_trace_nonneg`: **the Gaussian comparison theorem** — a sign condition on the
  trace gives `∫ F (y + c) ∂P ≤ ∫ F (x + c) ∂P` between the two endpoints of the path.
- `ProbabilityTheory.IsGaussian.slepian`: **Slepian's inequality**.
-/

open MeasureTheory Filter Set
open scoped BigOperators ENNReal InnerProductSpace NNReal Topology

noncomputable section

namespace ProbabilityTheory

section Interpolation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Gaussian interpolation map `(x, y) ↦ √t · x + √(1-t) · y` on the `L²`-product, as a
continuous linear map. Talagrand's *smart path*. -/
def gaussianInterp (t : ℝ) : WithLp 2 (E × E) →L[ℝ] E :=
  (Real.sqrt t) • (WithLp.fstL (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (α := E) (β := E))
    + (Real.sqrt (1 - t)) • (WithLp.sndL (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (α := E) (β := E))

/-- The time derivative of the Gaussian interpolation map,
`(x, y) ↦ (1/(2√t)) · x - (1/(2√(1-t))) · y`. -/
def gaussianInterpDeriv (t : ℝ) : WithLp 2 (E × E) →L[ℝ] E :=
  (1 / (2 * Real.sqrt t)) • (WithLp.fstL (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (α := E) (β := E))
    - (1 / (2 * Real.sqrt (1 - t))) • (WithLp.sndL (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (α := E) (β := E))

lemma gaussianInterp_apply (t : ℝ) (p : WithLp 2 (E × E)) :
    gaussianInterp t p
      = Real.sqrt t • (WithLp.ofLp p).1 + Real.sqrt (1 - t) • (WithLp.ofLp p).2 := rfl

lemma gaussianInterpDeriv_apply (t : ℝ) (p : WithLp 2 (E × E)) :
    gaussianInterpDeriv t p
      = (1 / (2 * Real.sqrt t)) • (WithLp.ofLp p).1
        - (1 / (2 * Real.sqrt (1 - t))) • (WithLp.ofLp p).2 := rfl

@[simp] lemma gaussianInterp_toLp_left (t : ℝ) (x : E) :
    gaussianInterp t (WithLp.toLp 2 (x, 0)) = Real.sqrt t • x := by
  simp [gaussianInterp_apply]

@[simp] lemma gaussianInterp_toLp_right (t : ℝ) (y : E) :
    gaussianInterp t (WithLp.toLp 2 (0, y)) = Real.sqrt (1 - t) • y := by
  simp [gaussianInterp_apply]

@[simp] lemma gaussianInterpDeriv_toLp_left (t : ℝ) (x : E) :
    gaussianInterpDeriv t (WithLp.toLp 2 (x, 0)) = (1 / (2 * Real.sqrt t)) • x := by
  simp [gaussianInterpDeriv_apply]

@[simp] lemma gaussianInterpDeriv_toLp_right (t : ℝ) (y : E) :
    gaussianInterpDeriv t (WithLp.toLp 2 (0, y))
      = (-(1 / (2 * Real.sqrt (1 - t)))) • y := by
  simp [gaussianInterpDeriv_apply, neg_smul]

/-- `gaussianInterpDeriv t` is the `t`-derivative of `gaussianInterp t`, for `t ∈ (0, 1)`. -/
lemma hasDerivAt_gaussianInterp {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (p : WithLp 2 (E × E)) :
    HasDerivAt (fun s : ℝ => gaussianInterp s p) (gaussianInterpDeriv t p) t := by
  have ht0 : t ≠ 0 := ne_of_gt ht.1
  have ht1 : (1 : ℝ) - t ≠ 0 := by
    have h := ht.2
    intro hc
    rw [sub_eq_zero] at hc
    exact absurd hc.symm (by linarith)
  have hfst : HasDerivAt (fun s : ℝ => Real.sqrt s • (WithLp.ofLp p).1)
      ((1 / (2 * Real.sqrt t)) • (WithLp.ofLp p).1) t :=
    (Real.hasDerivAt_sqrt ht0).smul_const _
  have hcomp : HasDerivAt (fun s : ℝ => Real.sqrt (1 - s))
      (-(1 / (2 * Real.sqrt (1 - t)))) t := by
    have hin : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub 1
    have h := hin.sqrt (by simpa using ht1)
    rwa [neg_div] at h
  have hsnd : HasDerivAt (fun s : ℝ => Real.sqrt (1 - s) • (WithLp.ofLp p).2)
      ((-(1 / (2 * Real.sqrt (1 - t)))) • (WithLp.ofLp p).2) t :=
    hcomp.smul_const _
  have hEq : gaussianInterpDeriv t p
      = (1 / (2 * Real.sqrt t)) • (WithLp.ofLp p).1
        + (-(1 / (2 * Real.sqrt (1 - t)))) • (WithLp.ofLp p).2 := by
    rw [gaussianInterpDeriv_apply, neg_smul, sub_eq_add_neg]
  have hfun : (fun s : ℝ => gaussianInterp s p)
      = fun s : ℝ =>
          Real.sqrt s • (WithLp.ofLp p).1 + Real.sqrt (1 - s) • (WithLp.ofLp p).2 := by
    funext s
    rw [gaussianInterp_apply]
  rw [hEq, hfun]
  exact hfst.add hsnd

lemma opNorm_gaussianInterp_le (t : ℝ) :
    ‖gaussianInterp (E := E) t‖ ≤ |Real.sqrt t| + |Real.sqrt (1 - t)| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun p => ?_
  have hfst : ‖(WithLp.ofLp p).1‖ ≤ ‖p‖ := by
    simpa using WithLp.norm_fst_le (p := (2 : ℝ≥0∞)) (α := E) (β := E) p
  have hsnd : ‖(WithLp.ofLp p).2‖ ≤ ‖p‖ := by
    simpa using WithLp.norm_snd_le (p := (2 : ℝ≥0∞)) (α := E) (β := E) p
  calc
    ‖gaussianInterp (E := E) t p‖
        ≤ ‖Real.sqrt t • (WithLp.ofLp p).1‖ + ‖Real.sqrt (1 - t) • (WithLp.ofLp p).2‖ := by
          rw [gaussianInterp_apply]
          exact norm_add_le _ _
    _ = |Real.sqrt t| * ‖(WithLp.ofLp p).1‖ + |Real.sqrt (1 - t)| * ‖(WithLp.ofLp p).2‖ := by
          simp [norm_smul]
    _ ≤ |Real.sqrt t| * ‖p‖ + |Real.sqrt (1 - t)| * ‖p‖ := by gcongr
    _ = (|Real.sqrt t| + |Real.sqrt (1 - t)|) * ‖p‖ := by ring

/-- The affine interpolation `p ↦ Z t p + c` has Fréchet derivative `Z t`. -/
lemma hasFDerivAt_gaussianInterp_add_const (t : ℝ) (c : E) (p : WithLp 2 (E × E)) :
    HasFDerivAt (fun z : WithLp 2 (E × E) => gaussianInterp t z + c)
      (gaussianInterp (E := E) t) p := by
  simpa using (gaussianInterp (E := E) t).hasFDerivAt.add_const c


section Bounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- On `[0, 1]` the interpolation map has operator norm at most `2`. -/
lemma opNorm_gaussianInterp_le_two {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖gaussianInterp (E := E) s‖ ≤ 2 := by
  refine (opNorm_gaussianInterp_le (E := E) s).trans ?_
  have h1 : |Real.sqrt s| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg s)]
    simpa using Real.sqrt_le_sqrt hs.2
  have h2 : |Real.sqrt (1 - s)| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have : (1 : ℝ) - s ≤ 1 := by linarith [hs.1]
    simpa using Real.sqrt_le_sqrt this
  linarith

/-- On a compact subinterval `[a, b] ⊆ (0, 1)` the interpolation derivative is uniformly
bounded. -/
lemma norm_gaussianInterpDeriv_le_of_mem_Icc {a b : ℝ} (ha : 0 < a) (hb : b < 1)
    {s : ℝ} (hs : s ∈ Icc a b) (p : WithLp 2 (E × E)) :
    ‖gaussianInterpDeriv s p‖
      ≤ (1 / (2 * Real.sqrt a) + 1 / (2 * Real.sqrt (1 - b))) * ‖p‖ := by
  have has : 0 < s := lt_of_lt_of_le ha hs.1
  have hbs : (0 : ℝ) < 1 - s := by linarith [hs.2]
  have hsa : Real.sqrt a ≤ Real.sqrt s := Real.sqrt_le_sqrt hs.1
  have hsb : Real.sqrt (1 - b) ≤ Real.sqrt (1 - s) := Real.sqrt_le_sqrt (by linarith [hs.2])
  have hsqa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsqb : 0 < Real.sqrt (1 - b) := Real.sqrt_pos.mpr (by linarith)
  have hinv1 : 1 / (2 * Real.sqrt s) ≤ 1 / (2 * Real.sqrt a) := by
    gcongr
  have hinv2 : 1 / (2 * Real.sqrt (1 - s)) ≤ 1 / (2 * Real.sqrt (1 - b)) := by
    gcongr
  have hfst : ‖(WithLp.ofLp p).1‖ ≤ ‖p‖ := by
    simpa using WithLp.norm_fst_le (p := (2 : ℝ≥0∞)) (α := E) (β := E) p
  have hsnd : ‖(WithLp.ofLp p).2‖ ≤ ‖p‖ := by
    simpa using WithLp.norm_snd_le (p := (2 : ℝ≥0∞)) (α := E) (β := E) p
  calc
    ‖gaussianInterpDeriv s p‖
        ≤ ‖(1 / (2 * Real.sqrt s)) • (WithLp.ofLp p).1‖
            + ‖(1 / (2 * Real.sqrt (1 - s))) • (WithLp.ofLp p).2‖ := by
          rw [gaussianInterpDeriv_apply]
          exact norm_sub_le _ _
    _ = (1 / (2 * Real.sqrt s)) * ‖(WithLp.ofLp p).1‖
          + (1 / (2 * Real.sqrt (1 - s))) * ‖(WithLp.ofLp p).2‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (2 * Real.sqrt s)),
            abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (2 * Real.sqrt (1 - s)))]
    _ ≤ (1 / (2 * Real.sqrt a)) * ‖p‖ + (1 / (2 * Real.sqrt (1 - b))) * ‖p‖ := by gcongr
    _ = (1 / (2 * Real.sqrt a) + 1 / (2 * Real.sqrt (1 - b))) * ‖p‖ := by ring

/-- Polynomial growth transports along the smart path, uniformly for `s ∈ [0, 1]`. -/
lemma abs_comp_gaussianInterp_add_le {g : E → ℝ} {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hg : ∀ z, |g z| ≤ C * (1 + ‖z‖) ^ m) (c : E) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (p : WithLp 2 (E × E)) :
    |g (gaussianInterp s p + c)| ≤ (C * ((1 + ‖c‖) * 3) ^ m) * (1 + ‖p‖) ^ m := by
  have h1 : (1 : ℝ) + ‖gaussianInterp s p + c‖ ≤ (1 + ‖c‖) * 3 * (1 + ‖p‖) := by
    refine (one_add_norm_clm_add_le (gaussianInterp (E := E) s) c p).trans ?_
    have h2 : ‖gaussianInterp (E := E) s‖ ≤ 2 := opNorm_gaussianInterp_le_two hs
    have h3 : (1 : ℝ) + ‖gaussianInterp (E := E) s‖ ≤ 3 := by linarith
    have hcn : (0 : ℝ) ≤ 1 + ‖c‖ := by positivity
    have hpn : (0 : ℝ) ≤ 1 + ‖p‖ := by positivity
    gcongr
  have hmono : (1 + ‖gaussianInterp s p + c‖) ^ m ≤ ((1 + ‖c‖) * 3 * (1 + ‖p‖)) ^ m :=
    pow_le_pow_left₀ (by positivity) h1 m
  calc |g (gaussianInterp s p + c)| ≤ C * (1 + ‖gaussianInterp s p + c‖) ^ m := hg _
    _ ≤ C * ((1 + ‖c‖) * 3 * (1 + ‖p‖)) ^ m := by gcongr
    _ = (C * ((1 + ‖c‖) * 3) ^ m) * (1 + ‖p‖) ^ m := by rw [mul_pow]; ring

/-- The smart path is continuous in the interpolation parameter. -/
lemma continuous_gaussianInterp_apply (p : WithLp 2 (E × E)) :
    Continuous fun s : ℝ => gaussianInterp s p := by
  have h : (fun s : ℝ => gaussianInterp s p)
      = fun s : ℝ =>
          Real.sqrt s • (WithLp.ofLp p).1 + Real.sqrt (1 - s) • (WithLp.ofLp p).2 := by
    funext s
    rw [gaussianInterp_apply]
  rw [h]
  exact (Real.continuous_sqrt.smul continuous_const).add
    ((Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).smul continuous_const)

@[simp] lemma gaussianInterp_one (p : WithLp 2 (E × E)) :
    gaussianInterp 1 p = (WithLp.ofLp p).1 := by
  simp [gaussianInterp_apply]

@[simp] lemma gaussianInterp_zero (p : WithLp 2 (E × E)) :
    gaussianInterp 0 p = (WithLp.ofLp p).2 := by
  simp [gaussianInterp_apply]

end Bounds

end Interpolation

section Trace

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Bilinear scaling: `Hs (a • x) (s • y) = (a * s) * Hs x y`. -/
private lemma clm_apply_smul_smul (Hs : E →L[ℝ] E →L[ℝ] ℝ) (a s : ℝ) (x y : E) :
    (Hs (a • x)) (s • y) = (a * s) * (Hs x) y := by
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

namespace IsGaussian

/-- **The Gaussian interpolation trace identity.** Let `P` be a centered Gaussian measure on the
`L²`-product `WithLp 2 (E × E)` whose covariance operator is block diagonal, sending
`(bᵢ, 0) ↦ (uᵢ, 0)` and `(0, bᵢ) ↦ (0, vᵢ)` for an orthonormal basis `b` of `E` — for instance the
law of an independent pair of centered Gaussian vectors, where `u` and `v` are the images of `b`
under the two covariance operators. Then, along the interpolation path `Z t = √t · x + √(1-t) · y`
with the shift `c`,

`∫ (DF (Z t p + c)) (Ż t p) ∂P
  = (1/2) ∑ i, [ ∫ (D²F (Z t p + c)) uᵢ bᵢ ∂P - ∫ (D²F (Z t p + c)) vᵢ bᵢ ∂P ]`.

The left-hand side is the value produced by differentiating `t ↦ ∫ F (Z t p + c) ∂P`; the
right-hand side is the difference of the two covariance-weighted Hessian traces. Sign information
about the right-hand side yields Slepian's inequality, the Sudakov–Fernique inequality and Guerra's
bound; see the module docstring. Talagrand, *Mean Field Models for Spin Glasses* I, §1.3,
Eq. (1.65). -/
theorem integral_fderiv_gaussianInterp_apply_deriv_eq_sum
    {P : Measure (WithLp 2 (E × E))} [IsGaussian P]
    (hmean0 : (∫ p : WithLp 2 (E × E), p ∂P) = 0)
    (b : OrthonormalBasis ι ℝ E) (u v : ι → E)
    (hcovL : ∀ i, covarianceOperator P (WithLp.toLp 2 (b i, 0)) = WithLp.toLp 2 (u i, 0))
    (hcovR : ∀ i, covarianceOperator P (WithLp.toLp 2 (0, b i)) = WithLp.toLp 2 (0, v i))
    (c : E) (F : E → ℝ) (hF_c2 : ContDiff ℝ 2 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF'_growth : ∀ z, ‖fderiv ℝ F z‖ ≤ C * (1 + ‖z‖) ^ m)
    (hF''_growth : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ C * (1 + ‖z‖) ^ m)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∫ p : WithLp 2 (E × E),
        (fderiv ℝ F (gaussianInterp t p + c)) (gaussianInterpDeriv t p) ∂P)
      = ∑ i : ι, (1 / 2 : ℝ) *
          ((∫ p : WithLp 2 (E × E),
                ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (u i)) (b i) ∂P)
            - ∫ p : WithLp 2 (E × E),
                ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (v i)) (b i) ∂P) := by
  classical
  have hst : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht.1
  have hs1t : (0 : ℝ) < Real.sqrt (1 - t) := Real.sqrt_pos.mpr (by linarith [ht.2])
  have h1 : Real.sqrt t * (1 / (2 * Real.sqrt t)) = 1 / 2 := by
    field_simp
  have h2 : Real.sqrt (1 - t) * (-(1 / (2 * Real.sqrt (1 - t)))) = -(1 / 2) := by
    field_simp
  -- The two-map Gaussian trace identity, in the product orthonormal basis.
  rw [integral_fderiv_clm_add_apply_clm_eq_sum (μ := P) hmean0 (b.prod b)
      (gaussianInterp t) (gaussianInterpDeriv t) c F hF_c2 hC hF'_growth hF''_growth,
    Fintype.sum_sum_type]
  -- The `Sum.inl` block: the `u` trace, scaled by `√t · (1/(2√t)) = 1/2`.
  have hleft : ∀ i : ι, (∫ p : WithLp 2 (E × E),
      ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c))
          (gaussianInterp t (covarianceOperator P ((b.prod b) (Sum.inl i)))))
        (gaussianInterpDeriv t ((b.prod b) (Sum.inl i))) ∂P)
        = (1 / 2 : ℝ) * ∫ p : WithLp 2 (E × E),
            ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (u i)) (b i) ∂P := by
    intro i
    have hb : (b.prod b) (Sum.inl i) = WithLp.toLp 2 (b i, 0) := by
      simp [OrthonormalBasis.prod_apply]
    rw [hb, hcovL i, gaussianInterp_toLp_left, gaussianInterpDeriv_toLp_left]
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [clm_apply_smul_smul, h1]
  -- The `Sum.inr` block: the `v` trace, scaled by `√(1-t) · (-1/(2√(1-t))) = -1/2`.
  have hright : ∀ i : ι, (∫ p : WithLp 2 (E × E),
      ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c))
          (gaussianInterp t (covarianceOperator P ((b.prod b) (Sum.inr i)))))
        (gaussianInterpDeriv t ((b.prod b) (Sum.inr i))) ∂P)
        = (-(1 / 2 : ℝ)) * ∫ p : WithLp 2 (E × E),
            ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (v i)) (b i) ∂P := by
    intro i
    have hb : (b.prod b) (Sum.inr i) = WithLp.toLp 2 (0, b i) := by
      simp [OrthonormalBasis.prod_apply]
    rw [hb, hcovR i, gaussianInterp_toLp_right, gaussianInterpDeriv_toLp_right]
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [clm_apply_smul_smul, h2]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hleft i,
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hright i,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The Gaussian interpolation trace identity** under the single hypothesis
`Function.HasTemperateGrowth`. See
`ProbabilityTheory.IsGaussian.integral_fderiv_gaussianInterp_apply_deriv_eq_sum` for the version
with explicit polynomial bounds, which is what functionals with only `C²` control (such as a
free-energy density) satisfy. -/
theorem integral_fderiv_gaussianInterp_apply_deriv
    {P : Measure (WithLp 2 (E × E))} [IsGaussian P]
    (hmean0 : (∫ p : WithLp 2 (E × E), p ∂P) = 0)
    (b : OrthonormalBasis ι ℝ E) (u v : ι → E)
    (hcovL : ∀ i, covarianceOperator P (WithLp.toLp 2 (b i, 0)) = WithLp.toLp 2 (u i, 0))
    (hcovR : ∀ i, covarianceOperator P (WithLp.toLp 2 (0, b i)) = WithLp.toLp 2 (0, v i))
    (c : E) (F : E → ℝ) (hF : Function.HasTemperateGrowth F)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∫ p : WithLp 2 (E × E),
        (fderiv ℝ F (gaussianInterp t p + c)) (gaussianInterpDeriv t p) ∂P)
      = ∑ i : ι, (1 / 2 : ℝ) *
          ((∫ p : WithLp 2 (E × E),
                ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (u i)) (b i) ∂P)
            - ∫ p : WithLp 2 (E × E),
                ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (v i)) (b i) ∂P) := by
  obtain ⟨C, m, hC, _h0, h1, h2⟩ := hF.exists_bound_fderiv_two
  exact integral_fderiv_gaussianInterp_apply_deriv_eq_sum (P := P) hmean0 b u v hcovL hcovR c F
    (hF.1.of_le (by simp)) hC h1 h2 ht


end IsGaussian

end Trace

section Derivative

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Reading a covariance-weighted Hessian trace as a matrix double sum. -/
lemma sum_apply_sum_smul_eq_sum_sum {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (A : ι → ι → ℝ) (Hs : E →L[ℝ] E →L[ℝ] ℝ) :
    (∑ i : ι, (Hs (∑ j : ι, A i j • b j)) (b i))
      = ∑ i : ι, ∑ j : ι, A i j * (Hs (b j)) (b i) := by
  classical
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, sum_apply]
  exact Finset.sum_congr rfl fun j _ => by
    rw [map_smul, smul_apply, smul_eq_mul]

namespace IsGaussian

/-- **Differentiating along Talagrand's smart path.** For a centered Gaussian measure `P` on the
`L²`-product and a `C¹` functional `F` of polynomial growth (together with its derivative), the
interpolated integral `s ↦ ∫ F (Z s p + c) ∂P` is differentiable at every `t ∈ (0,1)`, with
derivative `∫ (DF (Z t p + c)) (Ż t p) ∂P`.

Differentiation under the integral sign is legitimate because on a compact subinterval
`[a, b] ⊆ (0, 1)` the interpolation derivative `Ż s` is uniformly bounded
(`norm_gaussianInterpDeriv_le_of_mem_Icc`) while `‖Z s‖ ≤ 2` (`opNorm_gaussianInterp_le_two`), so
the `s`-derivative of the integrand is dominated by `C' (1 + ‖p‖) ^ (m + 1)`, which a Gaussian
measure integrates (Fernique). -/
theorem hasDerivAt_integral_gaussianInterp
    {P : Measure (WithLp 2 (E × E))} [IsGaussian P]
    (c : E) (F : E → ℝ) (hF_c1 : ContDiff ℝ 1 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ z, |F z| ≤ C * (1 + ‖z‖) ^ m)
    (hF'_growth : ∀ z, ‖fderiv ℝ F z‖ ≤ C * (1 + ‖z‖) ^ m)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s : ℝ => ∫ p : WithLp 2 (E × E), F (gaussianInterp s p + c) ∂P)
      (∫ p : WithLp 2 (E × E),
        (fderiv ℝ F (gaussianInterp t p + c)) (gaussianInterpDeriv t p) ∂P) t := by
  classical
  set a : ℝ := t / 2 with ha_def
  set b : ℝ := (1 + t) / 2 with hb_def
  have ha : 0 < a := by rw [ha_def]; linarith [ht.1]
  have hb : b < 1 := by rw [hb_def]; linarith [ht.2]
  have ht_mem : t ∈ Ioo a b := by
    constructor
    · rw [ha_def]; linarith [ht.1]
    · rw [hb_def]; linarith [ht.2]
  have hab : Ioo a b ⊆ Ioo (0 : ℝ) 1 := fun s hs =>
    ⟨lt_trans ha hs.1, lt_trans hs.2 hb⟩
  have hab' : Ioo a b ⊆ Icc a b := fun _ hs => ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  -- Uniform constants over `[a, b]`.
  set K : ℝ := 1 / (2 * Real.sqrt a) + 1 / (2 * Real.sqrt (1 - b)) with hK_def
  have hK : 0 ≤ K := by
    rw [hK_def]; positivity
  set D : ℝ := C * ((1 + ‖c‖) * 3) ^ m with hD_def
  have hD : 0 ≤ D := by
    rw [hD_def]; positivity
  have hgrow : ∀ (g : E → ℝ), (∀ z, |g z| ≤ C * (1 + ‖z‖) ^ m) →
      ∀ (s : ℝ), s ∈ Icc (0 : ℝ) 1 → ∀ p : WithLp 2 (E × E),
        |g (gaussianInterp s p + c)| ≤ D * (1 + ‖p‖) ^ m :=
    fun g hg s hs p => abs_comp_gaussianInterp_add_le hC hg c hs p
  -- Measurability and integrability of the integrand.
  have hFcont : Continuous F := hF_c1.continuous
  have hF'cont : Continuous (fderiv ℝ F) := hF_c1.continuous_fderiv (by norm_num)
  have hmeas : ∀ s : ℝ, AEStronglyMeasurable
      (fun p : WithLp 2 (E × E) => F (gaussianInterp s p + c)) P :=
    fun s => (hFcont.comp
      ((gaussianInterp (E := E) s).continuous.add continuous_const)).aestronglyMeasurable
  have hint : ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      Integrable (fun p : WithLp 2 (E × E) => F (gaussianInterp s p + c)) P := by
    intro s hs
    exact integrable_of_abs_le_mul_one_add_norm_pow (μ := P)
      (hFcont.comp ((gaussianInterp (E := E) s).continuous.add continuous_const)).measurable
      hD (hgrow F hF_growth s hs)
  -- The `s`-derivative of the integrand and its uniform bound.
  set F' : ℝ → WithLp 2 (E × E) → ℝ := fun s p =>
    (fderiv ℝ F (gaussianInterp s p + c)) (gaussianInterpDeriv s p) with hF'_def
  have hF'meas : AEStronglyMeasurable (F' t) P := by
    refine (Continuous.aestronglyMeasurable ?_)
    exact (hF'cont.comp
      ((gaussianInterp (E := E) t).continuous.add continuous_const)).clm_apply
      (gaussianInterpDeriv (E := E) t).continuous
  have hbound : ∀ᵐ p ∂P, ∀ s ∈ Ioo a b,
      ‖F' s p‖ ≤ (D * K) * (1 + ‖p‖) ^ (m + 1) := by
    refine Filter.Eventually.of_forall fun p => fun s hs => ?_
    have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt (hab hs).1, le_of_lt (hab hs).2⟩
    have h1 : ‖fderiv ℝ F (gaussianInterp s p + c)‖ ≤ D * (1 + ‖p‖) ^ m := by
      simpa [Real.norm_eq_abs] using
        hgrow (fun z => ‖fderiv ℝ F z‖) (fun z => by
          simpa [abs_of_nonneg (norm_nonneg (fderiv ℝ F z))] using hF'_growth z) s hs01 p
    have h2 : ‖gaussianInterpDeriv s p‖ ≤ K * ‖p‖ :=
      norm_gaussianInterpDeriv_le_of_mem_Icc ha hb (hab' hs) p
    have hp1 : ‖p‖ ≤ 1 + ‖p‖ := by linarith [norm_nonneg p]
    calc ‖F' s p‖ ≤ ‖fderiv ℝ F (gaussianInterp s p + c)‖ * ‖gaussianInterpDeriv s p‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (D * (1 + ‖p‖) ^ m) * (K * ‖p‖) := by
          gcongr
      _ ≤ (D * (1 + ‖p‖) ^ m) * (K * (1 + ‖p‖)) := by
          gcongr
      _ = (D * K) * (1 + ‖p‖) ^ (m + 1) := by rw [pow_succ]; ring
  have hbound_int : Integrable (fun p : WithLp 2 (E × E) => (D * K) * (1 + ‖p‖) ^ (m + 1)) P :=
    (ProbabilityTheory.IsGaussian.integrable_one_add_norm_pow (μ := P) (m + 1)).const_mul _
  have hdiff : ∀ᵐ p ∂P, ∀ s ∈ Ioo a b,
      HasDerivAt (fun s : ℝ => F (gaussianInterp s p + c)) (F' s p) s := by
    refine Filter.Eventually.of_forall fun p => fun s hs => ?_
    have hpath : HasDerivAt (fun s : ℝ => gaussianInterp s p + c) (gaussianInterpDeriv s p) s :=
      (hasDerivAt_gaussianInterp (hab hs) p).add_const c
    exact (hF_c1.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt s hpath
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun s p =>
      F (gaussianInterp s p + c)) (bound := fun p => (D * K) * (1 + ‖p‖) ^ (m + 1))
    (Ioo_mem_nhds ht_mem.1 ht_mem.2) (Filter.Eventually.of_forall fun s => hmeas s)
    (hint t ⟨le_of_lt ht.1, le_of_lt ht.2⟩) hF'meas hbound hbound_int hdiff).2

/-- Continuity of the interpolated integral on the closed interval `[0, 1]`. Together with
`hasDerivAt_integral_gaussianInterp` this makes the mean value theorem available on `[0, 1]`,
which is what turns a sign condition on the trace into a comparison of the two endpoint
integrals. -/
theorem continuousOn_integral_gaussianInterp
    {P : Measure (WithLp 2 (E × E))} [IsGaussian P]
    (c : E) (F : E → ℝ) (hF_cont : Continuous F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C) (hF_growth : ∀ z, |F z| ≤ C * (1 + ‖z‖) ^ m) :
    ContinuousOn (fun s : ℝ => ∫ p : WithLp 2 (E × E), F (gaussianInterp s p + c) ∂P)
      (Icc (0 : ℝ) 1) := by
  refine MeasureTheory.continuousOn_of_dominated
    (bound := fun p : WithLp 2 (E × E) => (C * ((1 + ‖c‖) * 3) ^ m) * (1 + ‖p‖) ^ m)
    (fun s _ => (hF_cont.comp
      ((gaussianInterp (E := E) s).continuous.add continuous_const)).aestronglyMeasurable)
    (fun s hs => Filter.Eventually.of_forall fun p => ?_)
    ((ProbabilityTheory.IsGaussian.integrable_one_add_norm_pow (μ := P) m).const_mul _)
    (Filter.Eventually.of_forall fun p =>
      (hF_cont.comp ((continuous_gaussianInterp_apply p).add continuous_const)).continuousOn)
  simpa [Real.norm_eq_abs] using abs_comp_gaussianInterp_add_le hC hF_growth c hs p

/-- **Differentiating along the smart path, in trace form.** Combining
`hasDerivAt_integral_gaussianInterp` with the interpolation trace identity: the derivative of
`s ↦ ∫ F (Z s p + c) ∂P` at `t ∈ (0,1)` is the difference of the two covariance-weighted Hessian
traces. -/
theorem hasDerivAt_integral_gaussianInterp_eq_sum
    {ι : Type*} [Fintype ι]
    {P : Measure (WithLp 2 (E × E))} [IsGaussian P]
    (hmean0 : (∫ p : WithLp 2 (E × E), p ∂P) = 0)
    (b : OrthonormalBasis ι ℝ E) (u v : ι → E)
    (hcovL : ∀ i, covarianceOperator P (WithLp.toLp 2 (b i, 0)) = WithLp.toLp 2 (u i, 0))
    (hcovR : ∀ i, covarianceOperator P (WithLp.toLp 2 (0, b i)) = WithLp.toLp 2 (0, v i))
    (c : E) (F : E → ℝ) (hF_c2 : ContDiff ℝ 2 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ z, |F z| ≤ C * (1 + ‖z‖) ^ m)
    (hF'_growth : ∀ z, ‖fderiv ℝ F z‖ ≤ C * (1 + ‖z‖) ^ m)
    (hF''_growth : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ C * (1 + ‖z‖) ^ m)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s : ℝ => ∫ p : WithLp 2 (E × E), F (gaussianInterp s p + c) ∂P)
      (∑ i : ι, (1 / 2 : ℝ) *
        ((∫ p : WithLp 2 (E × E),
              ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (u i)) (b i) ∂P)
          - ∫ p : WithLp 2 (E × E),
              ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (v i)) (b i) ∂P)) t := by
  rw [← integral_fderiv_gaussianInterp_apply_deriv_eq_sum (P := P) hmean0 b u v hcovL hcovR c F
    hF_c2 hC hF'_growth hF''_growth ht]
  exact hasDerivAt_integral_gaussianInterp c F (hF_c2.of_le (by norm_num)) hC hF_growth
    hF'_growth ht

/-- **The Gaussian comparison theorem** — the engine of Slepian's inequality and of the
Sudakov–Fernique inequality. If, at every `t ∈ (0,1)`, the covariance-weighted Hessian trace of
the first block dominates that of the second, then the first endpoint integral dominates the
second:

`∫ F (y + c) ∂P ≤ ∫ F (x + c) ∂P`

where `x` and `y` are the two coordinates of `p`. Concretely, with `P` the law of an independent
pair `(X, Y)` of centered Gaussian vectors, the conclusion reads `𝔼 F(Y + c) ≤ 𝔼 F(X + c)`, and the
hypothesis is a sign condition on `∑ᵢ [(D²F) (C_X bᵢ) bᵢ - (D²F) (C_Y bᵢ) bᵢ]`. Slepian's
inequality is the case where `F` has nonnegative mixed second derivatives and `C_X - C_Y` has
nonnegative entries. -/
theorem integral_le_integral_of_trace_nonneg
    {ι : Type*} [Fintype ι]
    {P : Measure (WithLp 2 (E × E))} [IsGaussian P]
    (hmean0 : (∫ p : WithLp 2 (E × E), p ∂P) = 0)
    (b : OrthonormalBasis ι ℝ E) (u v : ι → E)
    (hcovL : ∀ i, covarianceOperator P (WithLp.toLp 2 (b i, 0)) = WithLp.toLp 2 (u i, 0))
    (hcovR : ∀ i, covarianceOperator P (WithLp.toLp 2 (0, b i)) = WithLp.toLp 2 (0, v i))
    (c : E) (F : E → ℝ) (hF_c2 : ContDiff ℝ 2 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ z, |F z| ≤ C * (1 + ‖z‖) ^ m)
    (hF'_growth : ∀ z, ‖fderiv ℝ F z‖ ≤ C * (1 + ‖z‖) ^ m)
    (hF''_growth : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ C * (1 + ‖z‖) ^ m)
    (hsign : ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ ∑ i : ι, (1 / 2 : ℝ) *
        ((∫ p : WithLp 2 (E × E),
              ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (u i)) (b i) ∂P)
          - ∫ p : WithLp 2 (E × E),
              ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (v i)) (b i) ∂P)) :
    (∫ p : WithLp 2 (E × E), F ((WithLp.ofLp p).2 + c) ∂P)
      ≤ ∫ p : WithLp 2 (E × E), F ((WithLp.ofLp p).1 + c) ∂P := by
  set φ : ℝ → ℝ := fun s => ∫ p : WithLp 2 (E × E), F (gaussianInterp s p + c) ∂P with hφ_def
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt φ
      (∑ i : ι, (1 / 2 : ℝ) *
        ((∫ p : WithLp 2 (E × E),
              ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (u i)) (b i) ∂P)
          - ∫ p : WithLp 2 (E × E),
              ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (v i)) (b i) ∂P)) t :=
    fun t ht => hasDerivAt_integral_gaussianInterp_eq_sum (P := P) hmean0 b u v hcovL hcovR c F
      hF_c2 hC hF_growth hF'_growth hF''_growth ht
  have hcont : ContinuousOn φ (Icc (0 : ℝ) 1) :=
    continuousOn_integral_gaussianInterp c F (hF_c2.continuous) hC hF_growth
  have hint_eq : interior (Icc (0 : ℝ) 1) = Ioo (0 : ℝ) 1 := interior_Icc
  have hdiffOn : DifferentiableOn ℝ φ (interior (Icc (0 : ℝ) 1)) := by
    rw [hint_eq]
    exact fun t ht => ((hderiv t ht).differentiableAt).differentiableWithinAt
  have hmono : MonotoneOn φ (Icc (0 : ℝ) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hcont hdiffOn fun t ht => ?_
    rw [hint_eq] at ht
    rw [(hderiv t ht).deriv]
    exact hsign t ht
  have h01 : φ 0 ≤ φ 1 := hmono ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simpa [hφ_def] using h01

/-- Each Hessian entry along the smart path is integrable: it is bounded by
`‖D²F‖ ‖w‖ ‖z‖ ≤ C' (1 + ‖p‖) ^ m`, which a Gaussian measure integrates. -/
theorem integrable_fderiv2_gaussianInterp_apply
    {P : Measure (WithLp 2 (E × E))} [IsGaussian P]
    (c : E) (F : E → ℝ) (hF_c2 : ContDiff ℝ 2 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF''_growth : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ C * (1 + ‖z‖) ^ m)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (w z : E) :
    Integrable
      (fun p : WithLp 2 (E × E) => ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) w) z) P := by
  have hF''cont : Continuous (fderiv ℝ (fderiv ℝ F)) :=
    ((hF_c2.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num))
  have hcont : Continuous
      (fun p : WithLp 2 (E × E) => ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) w) z) := by
    refine Continuous.clm_apply ?_ continuous_const
    exact (hF''cont.comp
      ((gaussianInterp (E := E) t).continuous.add continuous_const)).clm_apply continuous_const
  refine integrable_of_abs_le_mul_one_add_norm_pow (μ := P) hcont.measurable
    (C := (C * ‖w‖ * ‖z‖) * ((1 + ‖c‖) * 3) ^ m) (m := m) (by positivity) fun p => ?_
  have hbound : |((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) w) z|
      ≤ ‖fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)‖ * ‖w‖ * ‖z‖ := by
    simpa [Real.norm_eq_abs] using
      ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)).le_opNorm₂ w z)
  have hgrow : ‖fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)‖
      ≤ (C * ((1 + ‖c‖) * 3) ^ m) * (1 + ‖p‖) ^ m := by
    have h := abs_comp_gaussianInterp_add_le (g := fun y => ‖fderiv ℝ (fderiv ℝ F) y‖)
      (C := C) (m := m) hC
      (fun y => by
        rw [abs_of_nonneg (norm_nonneg (fderiv ℝ (fderiv ℝ F) y))]
        exact hF''_growth y) c ht p
    rwa [abs_of_nonneg
      (norm_nonneg (fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)))] at h
  calc |((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) w) z|
      ≤ ‖fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)‖ * ‖w‖ * ‖z‖ := hbound
    _ ≤ ((C * ((1 + ‖c‖) * 3) ^ m) * (1 + ‖p‖) ^ m) * ‖w‖ * ‖z‖ := by
        gcongr
    _ = ((C * ‖w‖ * ‖z‖) * ((1 + ‖c‖) * 3) ^ m) * (1 + ‖p‖) ^ m := by ring

/-- **The Gaussian comparison theorem with a pointwise sign condition.** This is the form Slepian's
inequality takes: if at *every* point the trace of `D²F` against the first block dominates its
trace against the second, then the first endpoint integral dominates the second. -/
theorem integral_le_integral_of_fderiv2_trace_nonneg
    {ι : Type*} [Fintype ι]
    {P : Measure (WithLp 2 (E × E))} [IsGaussian P]
    (hmean0 : (∫ p : WithLp 2 (E × E), p ∂P) = 0)
    (b : OrthonormalBasis ι ℝ E) (u v : ι → E)
    (hcovL : ∀ i, covarianceOperator P (WithLp.toLp 2 (b i, 0)) = WithLp.toLp 2 (u i, 0))
    (hcovR : ∀ i, covarianceOperator P (WithLp.toLp 2 (0, b i)) = WithLp.toLp 2 (0, v i))
    (c : E) (F : E → ℝ) (hF_c2 : ContDiff ℝ 2 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ z, |F z| ≤ C * (1 + ‖z‖) ^ m)
    (hF'_growth : ∀ z, ‖fderiv ℝ F z‖ ≤ C * (1 + ‖z‖) ^ m)
    (hF''_growth : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ C * (1 + ‖z‖) ^ m)
    (hsign : ∀ z : E, 0 ≤ ∑ i : ι,
      (((fderiv ℝ (fderiv ℝ F) z) (u i)) (b i) - ((fderiv ℝ (fderiv ℝ F) z) (v i)) (b i))) :
    (∫ p : WithLp 2 (E × E), F ((WithLp.ofLp p).2 + c) ∂P)
      ≤ ∫ p : WithLp 2 (E × E), F ((WithLp.ofLp p).1 + c) ∂P := by
  classical
  refine integral_le_integral_of_trace_nonneg (P := P) hmean0 b u v hcovL hcovR c F hF_c2 hC
    hF_growth hF'_growth hF''_growth fun t ht => ?_
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hIu : ∀ i : ι, Integrable
      (fun p : WithLp 2 (E × E) =>
        ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (u i)) (b i)) P :=
    fun i => integrable_fderiv2_gaussianInterp_apply c F hF_c2 hC hF''_growth ht' (u i) (b i)
  have hIv : ∀ i : ι, Integrable
      (fun p : WithLp 2 (E × E) =>
        ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (v i)) (b i)) P :=
    fun i => integrable_fderiv2_gaussianInterp_apply c F hF_c2 hC hF''_growth ht' (v i) (b i)
  have hcombine : (∑ i : ι, (1 / 2 : ℝ) *
        ((∫ p : WithLp 2 (E × E),
              ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (u i)) (b i) ∂P)
          - ∫ p : WithLp 2 (E × E),
              ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (v i)) (b i) ∂P))
      = (1 / 2 : ℝ) * ∫ p : WithLp 2 (E × E), (∑ i : ι,
          (((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (u i)) (b i)
            - ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (v i)) (b i))) ∂P := by
    rw [MeasureTheory.integral_finsetSum (s := (Finset.univ : Finset ι))
        (f := fun i p => ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (u i)) (b i)
          - ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (v i)) (b i))
        (fun i _ => (hIu i).sub (hIv i)),
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [MeasureTheory.integral_sub (hIu i) (hIv i)]
  rw [hcombine]
  have hnn : (0 : ℝ) ≤ ∫ p : WithLp 2 (E × E), (∑ i : ι,
      (((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (u i)) (b i)
        - ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (v i)) (b i))) ∂P :=
    MeasureTheory.integral_nonneg fun p => hsign _
  positivity

/-- **Slepian's inequality.** Let `P` be the law of a pair `(X, Y)` of centered Gaussian vectors
on a real Hilbert space `E`, jointly Gaussian and with block-diagonal covariance (for instance an
independent pair), and let `A` and `B` be their covariance matrices in an orthonormal basis `b`:
`A i j = ⟪C_X bᵢ, bⱼ⟫` and `B i j = ⟪C_Y bᵢ, bⱼ⟫`. If

* the variances agree, `A i i = B i i`, and
* `X` is more positively correlated off the diagonal, `B i j ≤ A i j` for `i ≠ j`,

then for every `C²` functional `F` of polynomial growth whose **mixed** second derivatives are
nonnegative,

`𝔼 F (Y + c) ≤ 𝔼 F (X + c)`.

This is the sign consequence of the interpolation trace identity: along Talagrand's smart path the
derivative is `(1/2) ∑_{i,j} (A i j - B i j) · ∂²_{ji} F`, in which the diagonal terms cancel and
every off-diagonal term is a product of two nonnegative factors. -/
theorem slepian {ι : Type*} [Fintype ι]
    {P : Measure (WithLp 2 (E × E))} [IsGaussian P]
    (hmean0 : (∫ p : WithLp 2 (E × E), p ∂P) = 0)
    (b : OrthonormalBasis ι ℝ E) (A B : ι → ι → ℝ)
    (hcovL : ∀ i, covarianceOperator P (WithLp.toLp 2 (b i, 0))
      = WithLp.toLp 2 ((∑ j : ι, A i j • b j), 0))
    (hcovR : ∀ i, covarianceOperator P (WithLp.toLp 2 (0, b i))
      = WithLp.toLp 2 (0, (∑ j : ι, B i j • b j)))
    (c : E) (F : E → ℝ) (hF_c2 : ContDiff ℝ 2 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ z, |F z| ≤ C * (1 + ‖z‖) ^ m)
    (hF'_growth : ∀ z, ‖fderiv ℝ F z‖ ≤ C * (1 + ‖z‖) ^ m)
    (hF''_growth : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ C * (1 + ‖z‖) ^ m)
    (hdiag : ∀ i, A i i = B i i)
    (hoff : ∀ i j, i ≠ j → B i j ≤ A i j)
    (hmixed : ∀ (z : E) (i j : ι), i ≠ j →
      0 ≤ ((fderiv ℝ (fderiv ℝ F) z) (b j)) (b i)) :
    (∫ p : WithLp 2 (E × E), F ((WithLp.ofLp p).2 + c) ∂P)
      ≤ ∫ p : WithLp 2 (E × E), F ((WithLp.ofLp p).1 + c) ∂P := by
  classical
  refine integral_le_integral_of_fderiv2_trace_nonneg (P := P) hmean0 b
    (fun i => ∑ j : ι, A i j • b j) (fun i => ∑ j : ι, B i j • b j) hcovL hcovR c F hF_c2 hC
    hF_growth hF'_growth hF''_growth fun z => ?_
  have hexp : (∑ i : ι,
      (((fderiv ℝ (fderiv ℝ F) z) (∑ j : ι, A i j • b j)) (b i)
        - ((fderiv ℝ (fderiv ℝ F) z) (∑ j : ι, B i j • b j)) (b i)))
      = ∑ i : ι, ∑ j : ι,
          (A i j - B i j) * ((fderiv ℝ (fderiv ℝ F) z) (b j)) (b i) := by
    rw [Finset.sum_sub_distrib,
      sum_apply_sum_smul_eq_sum_sum b A (fderiv ℝ (fderiv ℝ F) z),
      sum_apply_sum_smul_eq_sum_sum b B (fderiv ℝ (fderiv ℝ F) z),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hexp]
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  by_cases hij : i = j
  · subst hij
    rw [hdiag i, sub_self, zero_mul]
  · exact mul_nonneg (by linarith [hoff i j hij]) (hmixed z i j hij)

/-- **The Gaussian comparison theorem, decreasing form.** If the trace is nonpositive throughout
`(0,1)` then the comparison reverses: `∫ F (x + c) ∂P ≤ ∫ F (y + c) ∂P`. -/
theorem integral_le_integral_of_trace_nonpos
    {ι : Type*} [Fintype ι]
    {P : Measure (WithLp 2 (E × E))} [IsGaussian P]
    (hmean0 : (∫ p : WithLp 2 (E × E), p ∂P) = 0)
    (b : OrthonormalBasis ι ℝ E) (u v : ι → E)
    (hcovL : ∀ i, covarianceOperator P (WithLp.toLp 2 (b i, 0)) = WithLp.toLp 2 (u i, 0))
    (hcovR : ∀ i, covarianceOperator P (WithLp.toLp 2 (0, b i)) = WithLp.toLp 2 (0, v i))
    (c : E) (F : E → ℝ) (hF_c2 : ContDiff ℝ 2 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ z, |F z| ≤ C * (1 + ‖z‖) ^ m)
    (hF'_growth : ∀ z, ‖fderiv ℝ F z‖ ≤ C * (1 + ‖z‖) ^ m)
    (hF''_growth : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ C * (1 + ‖z‖) ^ m)
    (hsign : ∀ t ∈ Ioo (0 : ℝ) 1, (∑ i : ι, (1 / 2 : ℝ) *
        ((∫ p : WithLp 2 (E × E),
              ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (u i)) (b i) ∂P)
          - ∫ p : WithLp 2 (E × E),
              ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (v i)) (b i) ∂P)) ≤ 0) :
    (∫ p : WithLp 2 (E × E), F ((WithLp.ofLp p).1 + c) ∂P)
      ≤ ∫ p : WithLp 2 (E × E), F ((WithLp.ofLp p).2 + c) ∂P := by
  set φ : ℝ → ℝ := fun s => ∫ p : WithLp 2 (E × E), F (gaussianInterp s p + c) ∂P with hφ_def
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt φ
      (∑ i : ι, (1 / 2 : ℝ) *
        ((∫ p : WithLp 2 (E × E),
              ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (u i)) (b i) ∂P)
          - ∫ p : WithLp 2 (E × E),
              ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (v i)) (b i) ∂P)) t :=
    fun t ht => hasDerivAt_integral_gaussianInterp_eq_sum (P := P) hmean0 b u v hcovL hcovR c F
      hF_c2 hC hF_growth hF'_growth hF''_growth ht
  have hcont : ContinuousOn φ (Icc (0 : ℝ) 1) :=
    continuousOn_integral_gaussianInterp c F hF_c2.continuous hC hF_growth
  have hint_eq : interior (Icc (0 : ℝ) 1) = Ioo (0 : ℝ) 1 := interior_Icc
  have hdiffOn : DifferentiableOn ℝ φ (interior (Icc (0 : ℝ) 1)) := by
    rw [hint_eq]
    exact fun t ht => ((hderiv t ht).differentiableAt).differentiableWithinAt
  have hanti : AntitoneOn φ (Icc (0 : ℝ) 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hcont hdiffOn fun t ht => ?_
    rw [hint_eq] at ht
    rw [(hderiv t ht).deriv]
    exact hsign t ht
  have h01 : φ 1 ≤ φ 0 := hanti ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simpa [hφ_def] using h01

/-- **The Gaussian comparison theorem, decreasing form, with a pointwise sign condition.** -/
theorem integral_le_integral_of_fderiv2_trace_nonpos
    {ι : Type*} [Fintype ι]
    {P : Measure (WithLp 2 (E × E))} [IsGaussian P]
    (hmean0 : (∫ p : WithLp 2 (E × E), p ∂P) = 0)
    (b : OrthonormalBasis ι ℝ E) (u v : ι → E)
    (hcovL : ∀ i, covarianceOperator P (WithLp.toLp 2 (b i, 0)) = WithLp.toLp 2 (u i, 0))
    (hcovR : ∀ i, covarianceOperator P (WithLp.toLp 2 (0, b i)) = WithLp.toLp 2 (0, v i))
    (c : E) (F : E → ℝ) (hF_c2 : ContDiff ℝ 2 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ z, |F z| ≤ C * (1 + ‖z‖) ^ m)
    (hF'_growth : ∀ z, ‖fderiv ℝ F z‖ ≤ C * (1 + ‖z‖) ^ m)
    (hF''_growth : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ C * (1 + ‖z‖) ^ m)
    (hsign : ∀ z : E, (∑ i : ι,
      (((fderiv ℝ (fderiv ℝ F) z) (u i)) (b i) - ((fderiv ℝ (fderiv ℝ F) z) (v i)) (b i))) ≤ 0) :
    (∫ p : WithLp 2 (E × E), F ((WithLp.ofLp p).1 + c) ∂P)
      ≤ ∫ p : WithLp 2 (E × E), F ((WithLp.ofLp p).2 + c) ∂P := by
  classical
  refine integral_le_integral_of_trace_nonpos (P := P) hmean0 b u v hcovL hcovR c F hF_c2 hC
    hF_growth hF'_growth hF''_growth fun t ht => ?_
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hIu : ∀ i : ι, Integrable
      (fun p : WithLp 2 (E × E) =>
        ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (u i)) (b i)) P :=
    fun i => integrable_fderiv2_gaussianInterp_apply c F hF_c2 hC hF''_growth ht' (u i) (b i)
  have hIv : ∀ i : ι, Integrable
      (fun p : WithLp 2 (E × E) =>
        ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (v i)) (b i)) P :=
    fun i => integrable_fderiv2_gaussianInterp_apply c F hF_c2 hC hF''_growth ht' (v i) (b i)
  have hcombine : (∑ i : ι, (1 / 2 : ℝ) *
        ((∫ p : WithLp 2 (E × E),
              ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (u i)) (b i) ∂P)
          - ∫ p : WithLp 2 (E × E),
              ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (v i)) (b i) ∂P))
      = (1 / 2 : ℝ) * ∫ p : WithLp 2 (E × E), (∑ i : ι,
          (((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (u i)) (b i)
            - ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (v i)) (b i))) ∂P := by
    rw [MeasureTheory.integral_finsetSum (s := (Finset.univ : Finset ι))
        (f := fun i p => ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (u i)) (b i)
          - ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (v i)) (b i))
        (fun i _ => (hIu i).sub (hIv i)),
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [MeasureTheory.integral_sub (hIu i) (hIv i)]
  rw [hcombine]
  have hnn : (∫ p : WithLp 2 (E × E), (∑ i : ι,
      (((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (u i)) (b i)
        - ((fderiv ℝ (fderiv ℝ F) (gaussianInterp t p + c)) (v i)) (b i))) ∂P) ≤ 0 := by
    refine MeasureTheory.integral_nonpos fun p => ?_
    exact hsign _
  nlinarith [hnn]

end IsGaussian

end Derivative

end ProbabilityTheory

end
