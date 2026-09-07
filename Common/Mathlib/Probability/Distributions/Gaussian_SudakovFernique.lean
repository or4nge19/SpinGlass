/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.Distributions.Gaussian_Interpolation
import Common.Mathlib.Analysis.SpecialFunctions.LogSumExp

/-!
# The Sudakov–Fernique inequality

If `X` and `Y` are centered jointly Gaussian vectors indexed by a finite set `ι` whose *increment
variances* compare,

`𝔼 (Xᵢ - Xⱼ)² ≤ 𝔼 (Yᵢ - Yⱼ)²` for all `i, j`,

then their expected suprema compare in the same direction:

`𝔼 maxᵢ Xᵢ ≤ 𝔼 maxᵢ Yᵢ`.

Unlike Slepian's inequality this needs no condition on the variances themselves — only on the
canonical distance. The proof is the interpolation trace identity applied to the smooth maximum
`smoothMax l x = l⁻¹ log ∑ᵢ exp (l xᵢ)`: its mixed second derivatives are `-l pᵢpⱼ`, so the trace
reorganizes (`sum_mul_hess_eq_half_sum_incr`) into

`(l/2) ∑_{i,j} [𝔼(Xᵢ-Xⱼ)² - 𝔼(Yᵢ-Yⱼ)²] pᵢ pⱼ ≤ 0`,

whence `𝔼 smoothMax l X ≤ 𝔼 smoothMax l Y` for every `l > 0`. Since
`(⨆ i, xᵢ) ≤ smoothMax l x ≤ (⨆ i, xᵢ) + l⁻¹ log (card ι)` *uniformly*, letting `l → ∞` needs
no limit
interchange: the error term is an explicit constant that tends to `0`.

## Main statements

- `ProbabilityTheory.IsGaussian.integral_smoothMax_le_of_incr_le`: the comparison for the smooth
  maximum, at each scale `l > 0`.
- `ProbabilityTheory.IsGaussian.sudakov_fernique`: the Sudakov–Fernique inequality.
-/

open MeasureTheory Filter Set Real
open scoped BigOperators ENNReal InnerProductSpace NNReal Topology ContDiff

noncomputable section

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
/-- **Reorganizing a covariance-weighted Hessian trace into increment form.** If `H` is the Hessian
of a smooth maximum in the Dirac basis — diagonal `l (pᵢ - pᵢ²)` and off-diagonal `-l pⱼpᵢ` for a
probability vector `p` — then weighting it by any matrix `Δ` gives

`∑_{i,j} Δᵢⱼ Hⱼᵢ = (l/2) ∑_{i,j} (Δᵢᵢ + Δⱼⱼ - 2 Δᵢⱼ) pᵢ pⱼ`,

in which the diagonal of `Δ` no longer appears on its own: only the *increments*
`Δᵢᵢ + Δⱼⱼ - 2Δᵢⱼ` matter. This is the algebraic heart of Sudakov–Fernique. -/
lemma sum_mul_hess_eq_half_sum_incr (p : ι → ℝ) (hp : (∑ i, p i) = 1)
    (Δ : ι → ι → ℝ) (l : ℝ) (H : ι → ι → ℝ)
    (hdiag : ∀ i, H i i = l * (p i - p i * p i))
    (hoff : ∀ i j, i ≠ j → H j i = l * (-(p j * p i))) :
    (∑ i, ∑ j, Δ i j * H j i)
      = (l / 2) * ∑ i, ∑ j, (Δ i i + Δ j j - 2 * Δ i j) * (p i * p j) := by
  classical
  -- Step 1: the inner sum, for each `i`.
  have hinner : ∀ i : ι, (∑ j, Δ i j * H j i)
      = l * (Δ i i * p i - ∑ j, Δ i j * (p j * p i)) := by
    intro i
    have hsplit : (∑ j, Δ i j * H j i)
        = Δ i i * H i i + ∑ j ∈ Finset.univ.erase i, Δ i j * H j i :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
    have hsplit2 : (∑ j, Δ i j * (p j * p i))
        = Δ i i * (p i * p i) + ∑ j ∈ Finset.univ.erase i, Δ i j * (p j * p i) :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
    have hE : (∑ j ∈ Finset.univ.erase i, Δ i j * H j i)
        = -(l * ∑ j ∈ Finset.univ.erase i, Δ i j * (p j * p i)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
      rw [hoff i j hij]
      ring
    rw [hsplit, hsplit2, hdiag i, hE]
    ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hinner i]
  -- Step 2: pull out `l` and split the two double sums.
  have hpull : (∑ i, l * (Δ i i * p i - ∑ j, Δ i j * (p j * p i)))
      = l * ((∑ i, Δ i i * p i) - ∑ i, ∑ j, Δ i j * (p j * p i)) := by
    calc (∑ i, l * (Δ i i * p i - ∑ j, Δ i j * (p j * p i)))
        = ∑ i, (l * (Δ i i * p i) - l * ∑ j, Δ i j * (p j * p i)) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = (∑ i, l * (Δ i i * p i)) - ∑ i, l * ∑ j, Δ i j * (p j * p i) := by
          rw [Finset.sum_sub_distrib]
      _ = l * (∑ i, Δ i i * p i) - l * ∑ i, ∑ j, Δ i j * (p j * p i) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ = l * ((∑ i, Δ i i * p i) - ∑ i, ∑ j, Δ i j * (p j * p i)) := by ring
  rw [hpull]
  -- Step 3: the diagonal sum is half the symmetrized double sum.
  have h1 : (∑ i, ∑ j, Δ i i * (p i * p j)) = ∑ i, Δ i i * p i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    calc (∑ j, Δ i i * (p i * p j)) = ∑ j, (Δ i i * p i) * p j :=
          Finset.sum_congr rfl fun j _ => by ring
      _ = (Δ i i * p i) * ∑ j, p j := (Finset.mul_sum _ _ _).symm
      _ = Δ i i * p i := by rw [hp, mul_one]
  have h2 : (∑ i, ∑ j, Δ j j * (p i * p j)) = ∑ i, Δ i i * p i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    calc (∑ i, Δ j j * (p i * p j)) = ∑ i, (Δ j j * p j) * p i :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = (Δ j j * p j) * ∑ i, p i := (Finset.mul_sum _ _ _).symm
      _ = Δ j j * p j := by rw [hp, mul_one]
  have h3 : (∑ i, ∑ j, Δ i j * (p j * p i)) = ∑ i, ∑ j, Δ i j * (p i * p j) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hrow : ∀ i : ι, (∑ j, (Δ i i + Δ j j - 2 * Δ i j) * (p i * p j))
      = (∑ j, Δ i i * (p i * p j)) + (∑ j, Δ j j * (p i * p j))
        - 2 * ∑ j, Δ i j * (p i * p j) := by
    intro i
    calc (∑ j, (Δ i i + Δ j j - 2 * Δ i j) * (p i * p j))
        = ∑ j, (Δ i i * (p i * p j) + Δ j j * (p i * p j) - 2 * (Δ i j * (p i * p j))) :=
          Finset.sum_congr rfl fun j _ => by ring
      _ = (∑ j, (Δ i i * (p i * p j) + Δ j j * (p i * p j)))
            - ∑ j, 2 * (Δ i j * (p i * p j)) := by rw [Finset.sum_sub_distrib]
      _ = ((∑ j, Δ i i * (p i * p j)) + ∑ j, Δ j j * (p i * p j))
            - 2 * ∑ j, Δ i j * (p i * p j) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hexpand : (∑ i, ∑ j, (Δ i i + Δ j j - 2 * Δ i j) * (p i * p j))
      = (∑ i, ∑ j, Δ i i * (p i * p j)) + (∑ i, ∑ j, Δ j j * (p i * p j))
        - 2 * ∑ i, ∑ j, Δ i j * (p i * p j) := by
    calc (∑ i, ∑ j, (Δ i i + Δ j j - 2 * Δ i j) * (p i * p j))
        = ∑ i, ((∑ j, Δ i i * (p i * p j)) + (∑ j, Δ j j * (p i * p j))
            - 2 * ∑ j, Δ i j * (p i * p j)) := Finset.sum_congr rfl fun i _ => hrow i
      _ = (∑ i, ((∑ j, Δ i i * (p i * p j)) + ∑ j, Δ j j * (p i * p j)))
            - ∑ i, 2 * ∑ j, Δ i j * (p i * p j) := by rw [Finset.sum_sub_distrib]
      _ = ((∑ i, ∑ j, Δ i i * (p i * p j)) + ∑ i, ∑ j, Δ j j * (p i * p j))
            - 2 * ∑ i, ∑ j, Δ i j * (p i * p j) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hexpand, h1, h2, h3]
  ring

namespace IsGaussian

variable {P : Measure (WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι))}

/-- **Sudakov–Fernique for the smooth maximum**, at each scale `l > 0`. The mixed second
derivatives of `smoothMax l` are `-l pᵢpⱼ`, so the interpolation trace collapses to
`(l/2) ∑_{i,j} [incr A - incr B]ᵢⱼ pᵢpⱼ ≤ 0` and the comparison theorem applies. -/
theorem integral_smoothMax_le_of_incr_le [IsGaussian P]
    (hmean0 : (∫ p : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι), p ∂P) = 0)
    (A B : ι → ι → ℝ)
    (hcovL : ∀ i, covarianceOperator P
      (WithLp.toLp 2 (EuclideanSpace.basisFun ι ℝ i, 0))
        = WithLp.toLp 2 ((∑ j, A i j • EuclideanSpace.basisFun ι ℝ j), 0))
    (hcovR : ∀ i, covarianceOperator P
      (WithLp.toLp 2 (0, EuclideanSpace.basisFun ι ℝ i))
        = WithLp.toLp 2 (0, (∑ j, B i j • EuclideanSpace.basisFun ι ℝ j)))
    (c : EuclideanSpace ℝ ι)
    (hincr : ∀ i j, A i i + A j j - 2 * A i j ≤ B i i + B j j - 2 * B i j)
    {l : ℝ} (hl : 0 < l) :
    (∫ p : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι),
        Real.smoothMax l ((WithLp.ofLp p).1 + c) ∂P)
      ≤ ∫ p : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι),
        Real.smoothMax l ((WithLp.ofLp p).2 + c) ∂P := by
  classical
  have hl0 : l ≠ 0 := ne_of_gt hl
  set logc : ℝ := Real.log (Fintype.card ι : ℝ) with hlogc
  have hlogc0 : 0 ≤ logc := by
    rw [hlogc]
    exact Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  set C : ℝ := max (l⁻¹ * logc + 1) (2 * l) with hCdef
  have hC1 : (1 : ℝ) ≤ C := by
    refine le_trans ?_ (le_max_left _ _)
    have : 0 ≤ l⁻¹ * logc := by positivity
    linarith
  have hC : 0 ≤ C := le_trans zero_le_one hC1
  have hFgrowth : ∀ z : EuclideanSpace ℝ ι,
      |Real.smoothMax l z| ≤ C * (1 + ‖z‖) ^ 1 := by
    intro z
    have h1 := Real.abs_smoothMax_le (ι := ι) hl z
    have h2 : l⁻¹ * logc + ‖z‖ ≤ C * (1 + ‖z‖) := by
      have hbase : l⁻¹ * logc + 1 ≤ C := le_max_left _ _
      have hz : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
      nlinarith [hz, hbase]
    simpa using le_trans h1 h2
  have hF'growth : ∀ z : EuclideanSpace ℝ ι,
      ‖fderiv ℝ (Real.smoothMax (ι := ι) l) z‖ ≤ C * (1 + ‖z‖) ^ 1 := by
    intro z
    have h1 := Real.norm_fderiv_smoothMax_le (ι := ι) hl0 z
    have h2 : (1 : ℝ) ≤ C * (1 + ‖z‖) := by
      have hz : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
      nlinarith [hz, hC1]
    simpa using le_trans h1 h2
  have hF''growth : ∀ z : EuclideanSpace ℝ ι,
      ‖fderiv ℝ (fderiv ℝ (Real.smoothMax (ι := ι) l)) z‖ ≤ C * (1 + ‖z‖) ^ 1 := by
    intro z
    have h1 := Real.norm_fderiv_fderiv_smoothMax_le (ι := ι) hl0 z
    have habs : |l| = l := abs_of_pos hl
    have h2 : 2 * |l| ≤ C * (1 + ‖z‖) := by
      have hbase : 2 * l ≤ C := le_max_right _ _
      have hz : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
      rw [habs]
      nlinarith [hz, hC, hbase]
    simpa using le_trans h1 h2
  refine integral_le_integral_of_fderiv2_trace_nonpos (P := P) hmean0
    (EuclideanSpace.basisFun ι ℝ)
    (fun i => ∑ j, A i j • EuclideanSpace.basisFun ι ℝ j)
    (fun i => ∑ j, B i j • EuclideanSpace.basisFun ι ℝ j) hcovL hcovR c
    (Real.smoothMax (ι := ι) l)
    ((Real.contDiff_smoothMax (ι := ι) l).of_le (by simp)) hC hFgrowth hF'growth hF''growth
    fun z => ?_
  -- The pointwise sign condition, via the increment reorganization.
  set p : ι → ℝ := fun i => Real.softmax (l • z) i with hpdef
  set H : ι → ι → ℝ := fun j i =>
    ((fderiv ℝ (fderiv ℝ (Real.smoothMax (ι := ι) l)) z)
      (EuclideanSpace.basisFun ι ℝ j)) (EuclideanSpace.basisFun ι ℝ i) with hHdef
  have hp1 : (∑ i, p i) = 1 := Real.sum_softmax (l • z)
  have hdiag : ∀ i, H i i = l * (p i - p i * p i) := by
    intro i
    rw [hHdef]
    simp only
    rw [Real.fderiv_fderiv_smoothMax_apply hl0, Real.logSumExpHess_basisFun_self]
  have hoff : ∀ i j, i ≠ j → H j i = l * (-(p j * p i)) := by
    intro i j hij
    rw [hHdef]
    simp only
    rw [Real.fderiv_fderiv_smoothMax_apply hl0, Real.logSumExpHess_basisFun_of_ne _ hij]
  have hexp : (∑ i, (((fderiv ℝ (fderiv ℝ (Real.smoothMax (ι := ι) l)) z)
        (∑ j, A i j • EuclideanSpace.basisFun ι ℝ j)) (EuclideanSpace.basisFun ι ℝ i)
      - ((fderiv ℝ (fderiv ℝ (Real.smoothMax (ι := ι) l)) z)
        (∑ j, B i j • EuclideanSpace.basisFun ι ℝ j)) (EuclideanSpace.basisFun ι ℝ i)))
      = ∑ i, ∑ j, (A i j - B i j) * H j i := by
    rw [Finset.sum_sub_distrib,
      sum_apply_sum_smul_eq_sum_sum (EuclideanSpace.basisFun ι ℝ) A
        (fderiv ℝ (fderiv ℝ (Real.smoothMax (ι := ι) l)) z),
      sum_apply_sum_smul_eq_sum_sum (EuclideanSpace.basisFun ι ℝ) B
        (fderiv ℝ (fderiv ℝ (Real.smoothMax (ι := ι) l)) z),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hHdef]; ring
  rw [hexp, sum_mul_hess_eq_half_sum_incr p hp1 (fun i j => A i j - B i j) l H hdiag hoff]
  have hterms : ∀ i j : ι,
      ((A i i - B i i) + (A j j - B j j) - 2 * (A i j - B i j)) * (p i * p j) ≤ 0 := by
    intro i j
    have h1 : (A i i - B i i) + (A j j - B j j) - 2 * (A i j - B i j) ≤ 0 := by
      have := hincr i j
      linarith
    have h2 : 0 ≤ p i * p j :=
      mul_nonneg (Real.softmax_nonneg (l • z) i) (Real.softmax_nonneg (l • z) j)
    exact mul_nonpos_of_nonpos_of_nonneg h1 h2
  have hsum : (∑ i, ∑ j,
      ((A i i - B i i) + (A j j - B j j) - 2 * (A i j - B i j)) * (p i * p j)) ≤ 0 :=
    Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => hterms i j
  have hl2 : 0 ≤ l / 2 := by positivity
  exact mul_nonpos_of_nonneg_of_nonpos hl2 hsum

omit [Nonempty ι] in
/-- Integrability along a coordinate projection, from affine growth. -/
private lemma integrable_comp_fstL [IsGaussian P] (c : EuclideanSpace ℝ ι)
    (g : EuclideanSpace ℝ ι → ℝ) (hg_cont : Continuous g) {K : ℝ} (hK : 0 ≤ K)
    (hg : ∀ z, |g z| ≤ K * (1 + ‖z‖) ^ 1) :
    Integrable
      (fun p : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) =>
        g ((WithLp.ofLp p).1 + c)) P := by
  set L : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) →L[ℝ] EuclideanSpace ℝ ι :=
    WithLp.fstL (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (α := EuclideanSpace ℝ ι)
      (β := EuclideanSpace ℝ ι) with hL
  have hbound := polyGrowth_comp_clm_add (g := g) (C := K) (m := 1) hK
    (fun z => by simpa [Real.norm_eq_abs] using hg z) L c
  exact integrable_of_abs_le_mul_one_add_norm_pow (μ := P)
    (hg_cont.comp (L.continuous.add continuous_const)).measurable
    (C := K * ((1 + ‖c‖) * (1 + ‖L‖)) ^ 1) (m := 1) (by positivity) (fun q => hbound q)

omit [Nonempty ι] in
/-- Integrability along the second coordinate projection. -/
private lemma integrable_comp_sndL [IsGaussian P] (c : EuclideanSpace ℝ ι)
    (g : EuclideanSpace ℝ ι → ℝ) (hg_cont : Continuous g) {K : ℝ} (hK : 0 ≤ K)
    (hg : ∀ z, |g z| ≤ K * (1 + ‖z‖) ^ 1) :
    Integrable
      (fun p : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) =>
        g ((WithLp.ofLp p).2 + c)) P := by
  set L : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) →L[ℝ] EuclideanSpace ℝ ι :=
    WithLp.sndL (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (α := EuclideanSpace ℝ ι)
      (β := EuclideanSpace ℝ ι) with hL
  have hbound := polyGrowth_comp_clm_add (g := g) (C := K) (m := 1) hK
    (fun z => by simpa [Real.norm_eq_abs] using hg z) L c
  exact integrable_of_abs_le_mul_one_add_norm_pow (μ := P)
    (hg_cont.comp (L.continuous.add continuous_const)).measurable
    (C := K * ((1 + ‖c‖) * (1 + ‖L‖)) ^ 1) (m := 1) (by positivity) (fun q => hbound q)

/-- **The Sudakov–Fernique inequality.** Let `P` be the law of a jointly Gaussian, centered pair
`(X, Y)` of `ι`-indexed vectors whose covariance is block diagonal, with covariance matrices `A`
and `B` in the Dirac basis. If the *increment variances* of `X` are dominated by those of `Y`,

`𝔼 (Xᵢ - Xⱼ)² = Aᵢᵢ + Aⱼⱼ - 2Aᵢⱼ ≤ Bᵢᵢ + Bⱼⱼ - 2Bᵢⱼ = 𝔼 (Yᵢ - Yⱼ)²`,

then the expected suprema compare in the same direction:

`𝔼 maxᵢ (Xᵢ + cᵢ) ≤ 𝔼 maxᵢ (Yᵢ + cᵢ)`.

No hypothesis on the variances themselves is needed — only on the canonical distance. -/
theorem sudakov_fernique [IsGaussian P]
    (hmean0 : (∫ p : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι), p ∂P) = 0)
    (A B : ι → ι → ℝ)
    (hcovL : ∀ i, covarianceOperator P
      (WithLp.toLp 2 (EuclideanSpace.basisFun ι ℝ i, 0))
        = WithLp.toLp 2 ((∑ j, A i j • EuclideanSpace.basisFun ι ℝ j), 0))
    (hcovR : ∀ i, covarianceOperator P
      (WithLp.toLp 2 (0, EuclideanSpace.basisFun ι ℝ i))
        = WithLp.toLp 2 (0, (∑ j, B i j • EuclideanSpace.basisFun ι ℝ j)))
    (c : EuclideanSpace ℝ ι)
    (hincr : ∀ i j, A i i + A j j - 2 * A i j ≤ B i i + B j j - 2 * B i j) :
    (∫ p : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι),
        (⨆ i, ((WithLp.ofLp p).1 + c) i) ∂P)
      ≤ ∫ p : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι),
        (⨆ i, ((WithLp.ofLp p).2 + c) i) ∂P := by
  classical
  set logc : ℝ := Real.log (Fintype.card ι : ℝ) with hlogc
  have hlogc0 : 0 ≤ logc := by
    rw [hlogc]
    exact Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  have hmaxbound : ∀ z : EuclideanSpace ℝ ι, |⨆ i, z i| ≤ 1 * (1 + ‖z‖) ^ 1 := by
    intro z
    have := Real.abs_ciSup_coord_le (ι := ι) z
    have hz : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    simpa using by linarith
  have hIm1 := integrable_comp_fstL (P := P) c (fun z : EuclideanSpace ℝ ι => ⨆ i, z i)
    Real.continuous_ciSup_coord zero_le_one hmaxbound
  have hIm2 := integrable_comp_sndL (P := P) c (fun z : EuclideanSpace ℝ ι => ⨆ i, z i)
    Real.continuous_ciSup_coord zero_le_one hmaxbound
  -- For every `l > 0` the smooth comparison gives the maximum comparison up to `l⁻¹ log (card ι)`.
  have key : ∀ l : ℝ, 0 < l →
      (∫ p : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι),
          (⨆ i, ((WithLp.ofLp p).1 + c) i) ∂P)
        ≤ (∫ p : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι),
            (⨆ i, ((WithLp.ofLp p).2 + c) i) ∂P) + l⁻¹ * logc := by
    intro l hl
    have hsmbound : ∀ z : EuclideanSpace ℝ ι,
        |Real.smoothMax (ι := ι) l z| ≤ (l⁻¹ * logc + 1) * (1 + ‖z‖) ^ 1 := by
      intro z
      have h1 := Real.abs_smoothMax_le (ι := ι) hl z
      have hz : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
      have h2 : 0 ≤ l⁻¹ * logc := by positivity
      simpa using by nlinarith [h1, hz, h2]
    have hK : (0 : ℝ) ≤ l⁻¹ * logc + 1 := by positivity
    have hIs1 := integrable_comp_fstL (P := P) c (Real.smoothMax (ι := ι) l)
      (Real.contDiff_smoothMax (ι := ι) l).continuous hK hsmbound
    have hIs2 := integrable_comp_sndL (P := P) c (Real.smoothMax (ι := ι) l)
      (Real.contDiff_smoothMax (ι := ι) l).continuous hK hsmbound
    have step1 : (∫ p, (⨆ i, ((WithLp.ofLp p).1 + c) i) ∂P)
        ≤ ∫ p, Real.smoothMax (ι := ι) l ((WithLp.ofLp p).1 + c) ∂P :=
      MeasureTheory.integral_mono hIm1 hIs1
        (fun q => Real.ciSup_coord_le_smoothMax hl _)
    have step2 := integral_smoothMax_le_of_incr_le (P := P) hmean0 A B hcovL hcovR c hincr hl
    have step3 : (∫ p, Real.smoothMax (ι := ι) l ((WithLp.ofLp p).2 + c) ∂P)
        ≤ (∫ p, (⨆ i, ((WithLp.ofLp p).2 + c) i) ∂P) + l⁻¹ * logc := by
      have hmono : (∫ p, Real.smoothMax (ι := ι) l ((WithLp.ofLp p).2 + c) ∂P)
          ≤ ∫ p, ((⨆ i, ((WithLp.ofLp p).2 + c) i) + l⁻¹ * logc) ∂P :=
        MeasureTheory.integral_mono hIs2 (hIm2.add (integrable_const _))
          (fun q => Real.smoothMax_le_ciSup_coord_add hl _)
      rw [MeasureTheory.integral_add hIm2 (integrable_const _),
        MeasureTheory.integral_const] at hmono
      simpa using hmono
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set l : ℝ := max 1 (logc / ε) with hldef
  have hl1 : (1 : ℝ) ≤ l := le_max_left _ _
  have hl : 0 < l := lt_of_lt_of_le zero_lt_one hl1
  have hle : logc / ε ≤ l := le_max_right _ _
  have hsmall : l⁻¹ * logc ≤ ε := by
    have h1 : logc ≤ l * ε := by
      have := mul_le_mul_of_nonneg_right hle (le_of_lt hε)
      rwa [div_mul_cancel₀ _ (ne_of_gt hε)] at this
    rw [inv_mul_eq_div, div_le_iff₀ hl]
    linarith
  exact le_trans (key l hl) (by linarith [hsmall])

end IsGaussian

end ProbabilityTheory
