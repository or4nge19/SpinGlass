/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.Distributions.Gaussian_SudakovFernique
import Common.Mathlib.Probability.Distributions.Gaussian_ProdCovariance

/-!
# Slepian and Sudakov–Fernique for an independent pair of Gaussian vectors

`Gaussian_Interpolation` and `Gaussian_SudakovFernique` prove the comparison inequalities for a
Gaussian measure on `WithLp 2 (E × E)` whose covariance operator is block diagonal. This file
discharges that hypothesis: by `ProbabilityTheory.covarianceOperator_map_toLp_prodMk` the law of an
independent centered Gaussian pair `(X, Y)` has exactly that structure, with the two second-moment
matrices as its blocks. The comparison inequalities therefore become unconditional statements about
two independent Gaussian vectors on a probability space:

* `ProbabilityTheory.IsGaussian.slepian_of_indepFun` — equal variances and larger correlations for
  `X` give `𝔼 F(Y + c) ≤ 𝔼 F(X + c)` for `F` with nonnegative mixed second derivatives;
* `ProbabilityTheory.IsGaussian.sudakov_fernique_of_indepFun` — smaller increment variances for `X`
  give `𝔼 maxᵢ (Xᵢ + cᵢ) ≤ 𝔼 maxᵢ (Yᵢ + cᵢ)`, with no hypothesis on the variances.

Both are stated with the second moments written out as integrals, `𝔼[Xᵢ Xⱼ]` and `𝔼(Xᵢ - Xⱼ)²`, so
that nothing remains to be checked about covariance operators at the point of use.
-/

open MeasureTheory Filter Set Real
open scoped BigOperators ENNReal InnerProductSpace NNReal Topology

noncomputable section

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {X Y : Ω → EuclideanSpace ℝ ι}

omit [Nonempty ι] in
/-- Square-integrability of a single coordinate of a Gaussian vector. -/
lemma memLp_two_coord [IsGaussian (P.map X)] (hX : Measurable X) (i : ι) :
    MemLp (fun ω => X ω i) 2 P := by
  simpa using memLp_two_inner (X := X) (P := P) hX (EuclideanSpace.basisFun ι ℝ i)

omit [Nonempty ι] in
/-- **The covariance operator on the Dirac basis is the second-moment matrix.** -/
lemma covarianceOperator_basisFun_eq_sum [IsGaussian (P.map X)] (hX : Measurable X) (i : ι) :
    covarianceOperator (P.map X) (EuclideanSpace.basisFun ι ℝ i)
      = ∑ j, (∫ ω, X ω i * X ω j ∂P) • EuclideanSpace.basisFun ι ℝ j := by
  have hentry : ∀ j : ι, ⟪EuclideanSpace.basisFun ι ℝ j,
        covarianceOperator (P.map X) (EuclideanSpace.basisFun ι ℝ i)⟫_ℝ
      = ∫ ω, X ω i * X ω j ∂P := by
    intro j
    rw [real_inner_comm, inner_covarianceOperator_map hX]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp
  calc covarianceOperator (P.map X) (EuclideanSpace.basisFun ι ℝ i)
      = ∑ j, ⟪EuclideanSpace.basisFun ι ℝ j,
          covarianceOperator (P.map X) (EuclideanSpace.basisFun ι ℝ i)⟫_ℝ
            • EuclideanSpace.basisFun ι ℝ j :=
        ((EuclideanSpace.basisFun ι ℝ).sum_repr' _).symm
    _ = ∑ j, (∫ ω, X ω i * X ω j ∂P) • EuclideanSpace.basisFun ι ℝ j :=
        Finset.sum_congr rfl fun j _ => by rw [hentry j]

omit [Nonempty ι] in
/-- Increment variances in terms of second moments: `𝔼(Xᵢ-Xⱼ)² = 𝔼Xᵢ² + 𝔼Xⱼ² - 2𝔼XᵢXⱼ`. -/
lemma integral_sq_sub_eq_second_moments [IsGaussian (P.map X)] (hX : Measurable X) (i j : ι) :
    (∫ ω, (X ω i - X ω j) ^ 2 ∂P)
      = (∫ ω, X ω i * X ω i ∂P) + (∫ ω, X ω j * X ω j ∂P)
        - 2 * ∫ ω, X ω i * X ω j ∂P := by
  have hMi : MemLp (fun ω => X ω i) 2 P := memLp_two_coord hX i
  have hMj : MemLp (fun ω => X ω j) 2 P := memLp_two_coord hX j
  have hii : Integrable (fun ω => X ω i * X ω i) P := hMi.integrable_mul hMi
  have hjj : Integrable (fun ω => X ω j * X ω j) P := hMj.integrable_mul hMj
  have hij : Integrable (fun ω => X ω i * X ω j) P := hMi.integrable_mul hMj
  have hpt : ∀ ω, (X ω i - X ω j) ^ 2
      = (X ω i * X ω i + X ω j * X ω j) - 2 * (X ω i * X ω j) := fun ω => by ring
  have hsum : Integrable (fun ω => X ω i * X ω i + X ω j * X ω j) P := hii.add hjj
  have hdbl : Integrable (fun ω => 2 * (X ω i * X ω j)) P := hij.const_mul 2
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_sub hsum hdbl,
    MeasureTheory.integral_add hii hjj, MeasureTheory.integral_const_mul]

namespace IsGaussian

omit [Nonempty ι] in
/-- The `L²`-joint law of the pair is Gaussian: one of the three inputs of the comparison
theorems. -/
private lemma jointLaw_facts
    [IsGaussian (P.map X)] [IsGaussian (P.map Y)] (hindep : X ⟂ᵢ[P] Y) :
    IsGaussian (P.map fun ω => WithLp.toLp 2 (X ω, Y ω)) := by
  exact isGaussian_map_toLp_prodMk (IsGaussian.hasGaussianLaw (X := X) (P := P))
    (IsGaussian.hasGaussianLaw (X := Y) (P := P)) hindep

omit [Nonempty ι] in
/-- Transport of an integral along the first coordinate of the joint law. -/
private lemma integral_map_fst (hX : Measurable X) (hY : Measurable Y)
    {g : EuclideanSpace ℝ ι → ℝ} (hg : Continuous g)
    (c : EuclideanSpace ℝ ι) :
    (∫ p : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι),
        g ((WithLp.ofLp p).1 + c) ∂(P.map fun ω => WithLp.toLp 2 (X ω, Y ω)))
      = ∫ ω, g (X ω + c) ∂P := by
  have hcont : Continuous
      (fun p : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) => g ((WithLp.ofLp p).1 + c)) :=
    hg.comp ((WithLp.fstL (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (α := EuclideanSpace ℝ ι)
      (β := EuclideanSpace ℝ ι)).continuous.add continuous_const)
  rw [MeasureTheory.integral_map (measurable_toLp_prodMk hX hY).aemeasurable
    hcont.aestronglyMeasurable]

omit [Nonempty ι] in
/-- Transport of an integral along the second coordinate of the joint law. -/
private lemma integral_map_snd (hX : Measurable X) (hY : Measurable Y)
    {g : EuclideanSpace ℝ ι → ℝ} (hg : Continuous g)
    (c : EuclideanSpace ℝ ι) :
    (∫ p : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι),
        g ((WithLp.ofLp p).2 + c) ∂(P.map fun ω => WithLp.toLp 2 (X ω, Y ω)))
      = ∫ ω, g (Y ω + c) ∂P := by
  have hcont : Continuous
      (fun p : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) => g ((WithLp.ofLp p).2 + c)) :=
    hg.comp ((WithLp.sndL (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (α := EuclideanSpace ℝ ι)
      (β := EuclideanSpace ℝ ι)).continuous.add continuous_const)
  rw [MeasureTheory.integral_map (measurable_toLp_prodMk hX hY).aemeasurable
    hcont.aestronglyMeasurable]

section Comparison

variable [IsGaussian (P.map X)] [IsGaussian (P.map Y)]
variable (hX : Measurable X) (hY : Measurable Y) (hindep : X ⟂ᵢ[P] Y)
variable (hX0 : (∫ ω, X ω ∂P) = 0) (hY0 : (∫ ω, Y ω ∂P) = 0)

include hX hY hindep hX0 hY0

/-- **The Sudakov–Fernique inequality for an independent Gaussian pair.** If `X` and `Y` are
independent centered Gaussian vectors indexed by a finite set and the increment variances of `X`
are dominated by those of `Y`,

`𝔼 (Xᵢ - Xⱼ)² ≤ 𝔼 (Yᵢ - Yⱼ)²` for all `i, j`,

then `𝔼 maxᵢ (Xᵢ + cᵢ) ≤ 𝔼 maxᵢ (Yᵢ + cᵢ)`. No hypothesis on the variances is needed. -/
theorem sudakov_fernique_of_indepFun (c : EuclideanSpace ℝ ι)
    (hincr : ∀ i j, (∫ ω, (X ω i - X ω j) ^ 2 ∂P) ≤ ∫ ω, (Y ω i - Y ω j) ^ 2 ∂P) :
    (∫ ω, Real.maxCoord (X ω + c) ∂P) ≤ ∫ ω, Real.maxCoord (Y ω + c) ∂P := by
  have hjoint : IsGaussian (P.map fun ω => WithLp.toLp 2 (X ω, Y ω)) :=
    jointLaw_facts hindep
  have hXi : Integrable X P := (IsGaussian.hasGaussianLaw (X := X) (P := P)).integrable
  have hYi : Integrable Y P := (IsGaussian.hasGaussianLaw (X := Y) (P := P)).integrable
  have hincr' : ∀ i j,
      (∫ ω, X ω i * X ω i ∂P) + (∫ ω, X ω j * X ω j ∂P) - 2 * ∫ ω, X ω i * X ω j ∂P
        ≤ (∫ ω, Y ω i * Y ω i ∂P) + (∫ ω, Y ω j * Y ω j ∂P)
          - 2 * ∫ ω, Y ω i * Y ω j ∂P := by
    intro i j
    rw [← integral_sq_sub_eq_second_moments hX i j,
      ← integral_sq_sub_eq_second_moments hY i j]
    exact hincr i j
  have hmain := sudakov_fernique
    (P := P.map fun ω => WithLp.toLp 2 (X ω, Y ω))
    (integral_id_map_toLp_prodMk_eq_zero hX hY hXi hYi hX0 hY0)
    (fun i j => ∫ ω, X ω i * X ω j ∂P) (fun i j => ∫ ω, Y ω i * Y ω j ∂P)
    (fun i => by
      rw [covarianceOperator_map_toLp_prodMk_left hX hY hindep hX0 hY0,
        covarianceOperator_basisFun_eq_sum hX i])
    (fun i => by
      rw [covarianceOperator_map_toLp_prodMk_right hX hY hindep hX0 hY0,
        covarianceOperator_basisFun_eq_sum hY i])
    c hincr'
  rwa [integral_map_fst hX hY Real.continuous_maxCoord c,
    integral_map_snd hX hY Real.continuous_maxCoord c] at hmain

/-- **Slepian's inequality for an independent Gaussian pair.** If `X` and `Y` are independent
centered Gaussian vectors with equal variances and `X` at least as positively correlated,

`𝔼 Xᵢ² = 𝔼 Yᵢ²` and `𝔼 Yᵢ Yⱼ ≤ 𝔼 Xᵢ Xⱼ` for `i ≠ j`,

then `𝔼 F(Y + c) ≤ 𝔼 F(X + c)` for every `C²` functional `F` of polynomial growth whose mixed
second derivatives are nonnegative. -/
theorem slepian_of_indepFun (c : EuclideanSpace ℝ ι)
    (F : EuclideanSpace ℝ ι → ℝ) (hF_c2 : ContDiff ℝ 2 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ z, |F z| ≤ C * (1 + ‖z‖) ^ m)
    (hF'_growth : ∀ z, ‖fderiv ℝ F z‖ ≤ C * (1 + ‖z‖) ^ m)
    (hF''_growth : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ C * (1 + ‖z‖) ^ m)
    (hvar : ∀ i, (∫ ω, X ω i * X ω i ∂P) = ∫ ω, Y ω i * Y ω i ∂P)
    (hcorr : ∀ i j, i ≠ j → (∫ ω, Y ω i * Y ω j ∂P) ≤ ∫ ω, X ω i * X ω j ∂P)
    (hmixed : ∀ (z : EuclideanSpace ℝ ι) (i j : ι), i ≠ j →
      0 ≤ ((fderiv ℝ (fderiv ℝ F) z) (EuclideanSpace.basisFun ι ℝ j))
        (EuclideanSpace.basisFun ι ℝ i)) :
    (∫ ω, F (Y ω + c) ∂P) ≤ ∫ ω, F (X ω + c) ∂P := by
  have hjoint : IsGaussian (P.map fun ω => WithLp.toLp 2 (X ω, Y ω)) :=
    jointLaw_facts hindep
  have hXi : Integrable X P := (IsGaussian.hasGaussianLaw (X := X) (P := P)).integrable
  have hYi : Integrable Y P := (IsGaussian.hasGaussianLaw (X := Y) (P := P)).integrable
  have hmain := slepian
    (P := P.map fun ω => WithLp.toLp 2 (X ω, Y ω))
    (integral_id_map_toLp_prodMk_eq_zero hX hY hXi hYi hX0 hY0)
    (EuclideanSpace.basisFun ι ℝ)
    (fun i j => ∫ ω, X ω i * X ω j ∂P) (fun i j => ∫ ω, Y ω i * Y ω j ∂P)
    (fun i => by
      rw [covarianceOperator_map_toLp_prodMk_left hX hY hindep hX0 hY0,
        covarianceOperator_basisFun_eq_sum hX i])
    (fun i => by
      rw [covarianceOperator_map_toLp_prodMk_right hX hY hindep hX0 hY0,
        covarianceOperator_basisFun_eq_sum hY i])
    c F hF_c2 hC hF_growth hF'_growth hF''_growth hvar hcorr hmixed
  rwa [integral_map_fst hX hY hF_c2.continuous c,
    integral_map_snd hX hY hF_c2.continuous c] at hmain

end Comparison

end IsGaussian

end ProbabilityTheory
