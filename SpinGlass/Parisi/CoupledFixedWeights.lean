/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.CoupledBoundLaw
import SpinGlass.Parisi.CascadeLogIntegrable
import SpinGlass.FiniteGibbs.GaussianFieldExpMoment

/-!
# The coupled scheme for the whole cascade, at fixed weights

The two endpoints of the truncated interpolation of §14.6 are truncated cascade sums of branch
functions: at `s = 1` the constrained branch partition functions with the disorder and the external
field (`coupledG … 1`), and at `s = 0`, after the bound (14.140) with the parameter `λ`, the
unconstrained branch functions `∏ᵢ 4 (ch ch ch λ + sh sh sh λ)` (`coupledEndG`,
`wZ_coupledTruncHam_zero_le`). Letting `M → ∞` at fixed weights of positive finite mass gives
Talagrand's (14.139)–(14.145) before the evaluation of `Y₀` by Theorem 14.2.1
(`coupled_fixed_weights`).
-/

open MeasureTheory ProbabilityTheory Finset Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
variable (N : ℕ) {κ : ℕ} {J : Type u} [Fintype J] [DecidableEq J]

/-! ### The endpoint branch functions -/

/-- The unconstrained branch functions with the parameter `λ` of (14.140):
`∏ᵢ 4 (ch A_i ch B_i ch λ + sh A_i sh B_i sh λ) = exp (N log 4 + Y_{κ+1})` for the combined
factors `L + L'`. -/
def coupledEndG (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (L₀ L₀' : Fin 2 → J → ℝ)
    (L L' : Fin κ → Fin 2 → J → ℝ) (θ : Ω × (Fin N × J → ℝ)) (x : Fin κ → Fin N × J → ℝ) :
    ℝ≥0∞ :=
  pairHamG N κ (fun _ => 1) 0 lam a (L₀ + L₀') (fun p => L p + L' p) θ.2 x

omit [MeasurableSpace Ω] [IsProbabilityMeasure Pm] [DecidableEq J] in
lemma coupledEndG_eq (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (L₀ L₀' : Fin 2 → J → ℝ)
    (L L' : Fin κ → Fin 2 → J → ℝ) (θ : Ω × (Fin N × J → ℝ)) (x : Fin κ → Fin N × J → ℝ) :
    coupledEndG N lam a L₀ L₀' L L' θ x
      = ENNReal.ofReal (Real.exp ((N : ℝ) * Real.log 4
          + pairCoshF N κ lam a (L₀ + L₀') (fun p => L p + L' p) θ.2 x)) := by
  unfold coupledEndG pairHamG
  rw [pairBranchZX_one_zero_eq_exp]

/-! ### The endpoints of the truncated interpolation -/

lemma coupledModelField_add_extField (M : ℕ) (ξ : ℝ → ℝ)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (L₀ L₀' : Fin 2 → J → ℝ) (L L' : Fin κ → Fin 2 → J → ℝ)
    (a : Fin N × Fin 2 → ℝ) (ω : Ω × SiteMarksSpace (Fin N × J) κ) :
    (coupledModelField N M ξ G₀ v₀ vs).U ω + coupledExtField N M Pm v₀ vs L₀' L' a ω
      = coupledTruncHam N M 1 ξ G₀ v₀ vs L₀ L₀' L L' a ω := by
  unfold coupledTruncHam
  rw [FiniteGibbs.gaussianInterp_one]
  rfl

lemma coupledTreeField_add_extField (M : ℕ) (ξ : ℝ → ℝ)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (L₀ L₀' : Fin 2 → J → ℝ) (L L' : Fin κ → Fin 2 → J → ℝ)
    (a : Fin N × Fin 2 → ℝ) (ω : Ω × SiteMarksSpace (Fin N × J) κ) :
    (coupledTreeField N M Pm v₀ vs L₀ L).U ω + coupledExtField N M Pm v₀ vs L₀' L' a ω
      = coupledTruncHam N M 0 ξ G₀ v₀ vs L₀ L₀' L L' a ω := by
  unfold coupledTruncHam
  rw [FiniteGibbs.gaussianInterp_zero]
  rfl

/-- **The weighted partition function of the interpolating Hamiltonian is the truncated cascade
sum of the branch functions.** -/
theorem wZ_coupledTruncHam (M : ℕ) (t : ℝ) (ξ : ℝ → ℝ)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (L₀ L₀' : Fin 2 → J → ℝ) (L L' : Fin κ → Fin 2 → J → ℝ)
    (a : Fin N × Fin 2 → ℝ) (w : CascadeWeights κ) (hw : ∀ α, branchWeight κ w α ≠ ∞) (u : ℝ)
    (ω : Ω × SiteMarksSpace (Fin N × J) κ) :
    wZ (coupledWt N M w u) (coupledTruncHam N M t ξ G₀ v₀ vs L₀ L₀' L L' a ω)
      = (truncSum κ M w (coupledG N u a L₀ L₀' L L' ξ G₀ t (ω.1, ω.2.1)) ω.2.2).toReal := by
  unfold coupledWt
  rw [wZ_prod_eq (truncWt κ M w) (constraintR N u),
    toReal_truncSum κ M w hw (Gt := coupledG N u a L₀ L₀' L L' ξ G₀ t (ω.1, ω.2.1))
      (fun _ => ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [wCondZ_coupledTruncHam]
  unfold coupledG pairHamG
  rw [ENNReal.toReal_ofReal (pairBranchZX_nonneg N κ (constraintR_nonneg N u) _ _ _ _ _ _ _)]

omit [DecidableEq J] in
/-- `∑ᵢ σ¹ᵢ σ²ᵢ = N R_{1,2}`. -/
lemma sum_isingSpin_mul_eq_overlap (hN : 0 < N) (σ τ : Config N) :
    ∑ i, isingSpin (σ i) * isingSpin (τ i) = (N : ℝ) * overlap N σ τ := by
  unfold overlap overlapOf spinOf
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- **The bound (14.140) at the endpoint `s = 0`**: for any `λ`, the weighted partition function
of the constrained pairs is at most `e^{-λ N u}` times the truncated cascade sum of the
unconstrained branch functions with the interaction `λ ∑ᵢ σ¹ᵢ σ²ᵢ`. -/
theorem wZ_coupledTruncHam_zero_le (M : ℕ) (hN : 0 < N) (ξ : ℝ → ℝ)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (L₀ L₀' : Fin 2 → J → ℝ) (L L' : Fin κ → Fin 2 → J → ℝ)
    (a : Fin N × Fin 2 → ℝ) (w : CascadeWeights κ) (hw : ∀ α, branchWeight κ w α ≠ ∞) (u lam : ℝ)
    (ω : Ω × SiteMarksSpace (Fin N × J) κ) :
    wZ (coupledWt N M w u) (coupledTruncHam N M 0 ξ G₀ v₀ vs L₀ L₀' L L' a ω)
      ≤ Real.exp (-(lam * ((N : ℝ) * u)))
        * (truncSum κ M w (coupledEndG N lam a L₀ L₀' L L' (ω.1, ω.2.1)) ω.2.2).toReal := by
  have h := wZ_mul_le_exp_mul_wZ_sub (fun p : PairConfig N (TruncBranch κ M) => truncWt κ M w p.2)
    (fun p => constraintR N u p.1) (fun p => truncWt_nonneg κ M w p.2)
    (fun p => constraintR_le_one N u p.1)
    (fun p => ∑ i, isingSpin (p.1 0 i) * isingSpin (p.1 1 i)) (u := (N : ℝ) * u) lam
    (fun p hp => by
      rw [sum_isingSpin_mul_eq_overlap N hN, overlap_eq_of_constraintR_ne_zero N hp])
    (coupledTruncHam N M 0 ξ G₀ v₀ vs L₀ L₀' L L' a ω)
  refine h.trans (le_of_eq ?_)
  congr 1
  have hwt : (fun p : PairConfig N (TruncBranch κ M) => truncWt κ M w p.2)
      = fun p => truncWt κ M w p.2 * (fun _ : Fin 2 → Config N => (1 : ℝ)) p.1 := by
    funext p
    simp
  rw [hwt, wZ_prod_eq (truncWt κ M w) (fun _ : Fin 2 → Config N => (1 : ℝ)),
    toReal_truncSum κ M w hw (Gt := coupledEndG N lam a L₀ L₀' L L' (ω.1, ω.2.1))
      (fun _ => ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun β _ => ?_
  unfold coupledEndG pairHamG
  rw [ENNReal.toReal_ofReal (pairBranchZX_nonneg N κ (fun _ => zero_le_one) _ _ _ _ _ _ _)]
  congr 1
  unfold wCondZ pairBranchZX
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [one_mul]
  congr 1
  rw [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, coupledTruncHam_apply]
  simp only [Real.sqrt_zero, sub_zero, Real.sqrt_one, zero_smul, one_smul]
  unfold pairBranchHamX
  simp only [PiLp.zero_apply]
  ring

/-! ### Talagrand's (14.4) with the disorder: the cascade sums are integrable -/

/-- The joint law of the disorder, the root marks and the cascade marks. -/
abbrev coupledLaw (Pm : Measure Ω) (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) :
    Measure ((Ω × (Fin N × J → ℝ)) × CascadeMarks (Fin N × J → ℝ) κ) :=
  (Pm.prod (rootMarksLaw N v₀)).prod (cascadeMarksLaw κ (siteGaussianMarks (Fin N × J) κ vs))

omit [IsProbabilityMeasure Pm] [DecidableEq J] in
/-- **Talagrand's (14.4) with the disorder**: for branch functions
`pairHamG (c, H(ω), λ, a, K₀, K, z₀)` whose disorder part has finite exponential moments,
`∫∫ G < ∞` over the disorder, the root marks and the marks along a branch. -/
theorem lintegral_lintegral_pairHamG_ne_top {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ)
    (Hf : Ω → EnergySpace N) (hHf : Measurable Hf)
    (hH : ∀ σ : Fin 2 → Config N, ∫⁻ ω, ENNReal.ofReal (Real.exp (-(Hf ω (σ 0) + Hf ω (σ 1))))
      ∂Pm ≠ ∞)
    (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ)
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) :
    ∫⁻ θ, ∫⁻ x, pairHamG N κ c (Hf θ.1) lam a K₀ K θ.2 x
      ∂Measure.pi (siteGaussianMarks (Fin N × J) κ vs) ∂Pm.prod (rootMarksLaw N v₀) ≠ ∞ := by
  -- the Gaussian integral over the marks along the branch
  have hx : ∀ θ : Ω × (Fin N × J → ℝ),
      ∫⁻ x, pairHamG N κ c (Hf θ.1) lam a K₀ K θ.2 x
          ∂Measure.pi (siteGaussianMarks (Fin N × J) κ vs)
        = ∑ σ : Fin 2 → Config N, ENNReal.ofReal (c σ)
            * (ENNReal.ofReal (Real.exp (pairBranchA N (Hf θ.1) lam a K₀ θ.2 σ))
              * ENNReal.ofReal (Real.exp
                  (∑ p, ∑ s, (vs p : ℝ) * pairBranchB N κ K σ p s ^ 2 / 2))) := by
    intro θ
    simp_rw [pairHamG_eq_sum N κ hc0]
    rw [lintegral_finsetSum _ fun σ _ =>
      (measurable_ofReal_exp_add_sum_mul (Fin N × J) κ _ _).const_mul _]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [lintegral_const_mul _ (measurable_ofReal_exp_add_sum_mul (Fin N × J) κ _ _),
      lintegral_ofReal_exp_add_siteGaussianMarks]
  simp_rw [hx]
  -- the integral over the disorder and the root marks, term by term
  have hA : ∀ σ : Fin 2 → Config N, ∀ θ : Ω × (Fin N × J → ℝ),
      ENNReal.ofReal (Real.exp (pairBranchA N (Hf θ.1) lam a K₀ θ.2 σ))
        = ENNReal.ofReal (Real.exp (-(Hf θ.1 (σ 0) + Hf θ.1 (σ 1))))
          * (ENNReal.ofReal (Real.exp (lam * ∑ i, isingSpin (σ 0 i) * isingSpin (σ 1 i)
              - ∑ l : Fin 2, ∑ i, isingSpin (σ l i) * a (i, l)))
            * ENNReal.ofReal (Real.exp (∑ s : Fin N × J,
              (-(∑ l : Fin 2, isingSpin (σ l s.1) * K₀ l s.2)) * θ.2 s))) := by
    intro σ θ
    rw [pairBranchA_eq, Real.exp_add, Real.exp_add, mul_assoc,
      ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hmeasA : ∀ σ : Fin 2 → Config N, Measurable fun θ : Ω × (Fin N × J → ℝ) =>
      ENNReal.ofReal (c σ) * (ENNReal.ofReal (Real.exp (pairBranchA N (Hf θ.1) lam a K₀ θ.2 σ))
        * ENNReal.ofReal (Real.exp (∑ p, ∑ s, (vs p : ℝ) * pairBranchB N κ K σ p s ^ 2 / 2))) := by
    intro σ
    refine Measurable.const_mul (Measurable.mul_const ?_ _) _
    refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
    unfold pairBranchA
    refine Measurable.neg (Measurable.add (Measurable.sub (Measurable.add ?_ ?_) measurable_const)
      (Finset.measurable_sum _ fun l _ => Finset.measurable_sum _ fun i _ =>
        measurable_const.mul (measurable_const.add (Finset.measurable_sum _ fun j _ =>
          measurable_const.mul ((measurable_pi_apply (i, j)).comp measurable_snd)))))
    · exact ((continuous_apply (σ 0)).comp
        (PiLp.continuous_ofLp 2 (fun _ : Config N => ℝ))).measurable.comp (hHf.comp measurable_fst)
    · exact ((continuous_apply (σ 1)).comp
        (PiLp.continuous_ofLp 2 (fun _ : Config N => ℝ))).measurable.comp (hHf.comp measurable_fst)
  rw [lintegral_finsetSum _ fun σ _ => hmeasA σ]
  refine ENNReal.sum_ne_top.2 fun σ _ => ?_
  simp_rw [hA σ]
  -- separate the disorder from the root marks
  have hm1 : Measurable fun ω : Ω => ENNReal.ofReal (Real.exp (-(Hf ω (σ 0) + Hf ω (σ 1)))) := by
    refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Measurable.neg
      (Measurable.add ?_ ?_)))
    · exact ((continuous_apply (σ 0)).comp
        (PiLp.continuous_ofLp 2 (fun _ : Config N => ℝ))).measurable.comp hHf
    · exact ((continuous_apply (σ 1)).comp
        (PiLp.continuous_ofLp 2 (fun _ : Config N => ℝ))).measurable.comp hHf
  have hm2 : Measurable fun z₀ : Fin N × J → ℝ => ENNReal.ofReal (Real.exp (∑ s : Fin N × J,
      (-(∑ l : Fin 2, isingSpin (σ l s.1) * K₀ l s.2)) * z₀ s)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Finset.measurable_sum _ fun s _ =>
      measurable_const.mul (measurable_pi_apply s)))
  have hfun : (fun θ : Ω × (Fin N × J → ℝ) => ENNReal.ofReal (c σ)
      * (ENNReal.ofReal (Real.exp (-(Hf θ.1 (σ 0) + Hf θ.1 (σ 1))))
        * (ENNReal.ofReal (Real.exp (lam * ∑ i, isingSpin (σ 0 i) * isingSpin (σ 1 i)
            - ∑ l : Fin 2, ∑ i, isingSpin (σ l i) * a (i, l)))
          * ENNReal.ofReal (Real.exp (∑ s : Fin N × J,
            (-(∑ l : Fin 2, isingSpin (σ l s.1) * K₀ l s.2)) * θ.2 s)))
        * ENNReal.ofReal (Real.exp (∑ p, ∑ s, (vs p : ℝ) * pairBranchB N κ K σ p s ^ 2 / 2))))
      = fun θ => (ENNReal.ofReal (c σ) * ENNReal.ofReal (Real.exp (lam * ∑ i,
            isingSpin (σ 0 i) * isingSpin (σ 1 i)
            - ∑ l : Fin 2, ∑ i, isingSpin (σ l i) * a (i, l)))
          * ENNReal.ofReal (Real.exp (∑ p, ∑ s, (vs p : ℝ) * pairBranchB N κ K σ p s ^ 2 / 2)))
        * (ENNReal.ofReal (Real.exp (-(Hf θ.1 (σ 0) + Hf θ.1 (σ 1))))
          * ENNReal.ofReal (Real.exp (∑ s : Fin N × J,
            (-(∑ l : Fin 2, isingSpin (σ l s.1) * K₀ l s.2)) * θ.2 s))) := by
    funext θ
    ring
  have hfg : Measurable fun θ : Ω × (Fin N × J → ℝ) =>
      ENNReal.ofReal (Real.exp (-(Hf θ.1 (σ 0) + Hf θ.1 (σ 1))))
        * ENNReal.ofReal (Real.exp (∑ s : Fin N × J,
          (-(∑ l : Fin 2, isingSpin (σ l s.1) * K₀ l s.2)) * θ.2 s)) :=
    (hm1.comp measurable_fst).mul (hm2.comp measurable_snd)
  rw [hfun, lintegral_const_mul _ hfg, lintegral_prod_mul hm1.aemeasurable hm2.aemeasurable]
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top) (ENNReal.mul_ne_top (hH σ) ?_)
  rw [lintegral_ofReal_exp_sum_mul_pi_gaussianReal (fun _ : Fin N × J => v₀)]
  exact ENNReal.ofReal_ne_top

omit [IsProbabilityMeasure Pm] [DecidableEq J] in
/-- **Talagrand's (14.4) with the disorder, for the cascade sum**: the cascade sum of the branch
functions has finite expectation. -/
theorem lintegral_cascadeSum_pairHamG_ne_top {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ)
    (Hf : Ω → EnergySpace N) (hHf : Measurable Hf)
    (hH : ∀ σ : Fin 2 → Config N, ∫⁻ ω, ENNReal.ofReal (Real.exp (-(Hf ω (σ 0) + Hf ω (σ 1))))
      ∂Pm ≠ ∞)
    (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ)
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (w : CascadeWeights κ) (hW : weightSum κ w ≠ ∞) :
    ∫⁻ q, cascadeSum κ (pairHamG N κ c (Hf q.1.1) lam a K₀ K q.1.2) (cascadeZip κ (w, q.2))
      ∂coupledLaw N Pm v₀ vs ≠ ∞ := by
  -- joint measurability of the branch functions in `(θ, x)`
  have hGm := measurable_pairHamG_branchParam N κ c hHf lam a K₀ K
  have hG' := hGm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd :
    Measurable fun q : (ℝ × (Ω × (Fin N × J → ℝ))) × (Fin κ → Fin N × J → ℝ) => (q.1.2, q.2))
  have hG : Measurable fun q : (ℝ × (Ω × (Fin N × J → ℝ))) × (Fin κ → Fin N × J → ℝ) =>
      pairHamG N κ c (Hf q.1.2.1) lam a K₀ K q.1.2.2 q.2 := hG'
  have hSm := measurable_cascadeSum_of κ
    (fun _ (θ : Ω × (Fin N × J → ℝ)) => pairHamG N κ c (Hf θ.1) lam a K₀ K θ.2) hG w 0
  unfold coupledLaw
  rw [lintegral_prod _ hSm.aemeasurable]
  -- the inner integral over the cascade marks
  have hinner : ∀ θ : Ω × (Fin N × J → ℝ),
      ∫⁻ z, cascadeSum κ (pairHamG N κ c (Hf θ.1) lam a K₀ K θ.2) (cascadeZip κ (w, z))
        ∂cascadeMarksLaw κ (siteGaussianMarks (Fin N × J) κ vs)
      = weightSum κ w * ∫⁻ x, pairHamG N κ c (Hf θ.1) lam a K₀ K θ.2 x
          ∂Measure.pi (siteGaussianMarks (Fin N × J) κ vs) := fun θ =>
    lintegral_cascadeSum_cascadeZip κ _ w (measurable_pairHamG' N κ c _ lam a K₀ K _)
  simp_rw [hinner]
  have hmx : Measurable fun θ : Ω × (Fin N × J → ℝ) =>
      ∫⁻ x, pairHamG N κ c (Hf θ.1) lam a K₀ K θ.2 x
        ∂Measure.pi (siteGaussianMarks (Fin N × J) κ vs) :=
    Measurable.lintegral_prod_right' (f := fun p : (Ω × (Fin N × J → ℝ)) × (Fin κ → Fin N × J → ℝ)
      => pairHamG N κ c (Hf p.1.1) lam a K₀ K p.1.2 p.2) hGm
  rw [lintegral_const_mul _ hmx]
  exact ENNReal.mul_ne_top hW
    (lintegral_lintegral_pairHamG_ne_top N hc0 Hf hHf hH lam a K₀ K v₀ vs)

/-! ### An integrable lower bound for the logarithm of the branch functions -/

omit [DecidableEq J] in
/-- Integrability of a coordinate of the root marks under the joint law. -/
lemma integrable_rootMark_coupledLaw (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (s : Fin N × J) :
    Integrable (fun q : (Ω × (Fin N × J → ℝ)) × CascadeMarks (Fin N × J → ℝ) κ => q.1.2 s)
      (coupledLaw N Pm v₀ vs) := by
  have h1 : Integrable (fun z₀ : Fin N × J → ℝ => z₀ s) (rootMarksLaw N v₀) :=
    ((measurePreserving_eval (μ := fun _ : Fin N × J => gaussianReal 0 v₀) s).integrable_comp
      measurable_id.aestronglyMeasurable).2 (integrable_id_gaussianReal 0 v₀)
  have h2 : Integrable (fun θ : Ω × (Fin N × J → ℝ) => θ.2 s) (Pm.prod (rootMarksLaw N v₀)) :=
    ((measurePreserving_snd (μ := Pm) (ν := rootMarksLaw N v₀)).integrable_comp
      (measurable_pi_apply s).aestronglyMeasurable).2 h1
  exact ((measurePreserving_fst (μ := Pm.prod (rootMarksLaw N v₀))
    (ν := cascadeMarksLaw κ (siteGaussianMarks (Fin N × J) κ vs))).integrable_comp
    ((measurable_pi_apply s).comp measurable_snd).aestronglyMeasurable).2 h2

omit [DecidableEq J] in
/-- Integrability of a coordinate of the marks along a branch under the joint law. -/
lemma integrable_branchMark_coupledLaw (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (α₀ : Fin κ → ℕ × ℕ)
    (p : Fin κ) (s : Fin N × J) :
    Integrable (fun q : (Ω × (Fin N × J → ℝ)) × CascadeMarks (Fin N × J → ℝ) κ =>
      branchMarks κ q.2 α₀ p s) (coupledLaw N Pm v₀ vs) := by
  have h1 : Integrable (fun x : Fin N × J → ℝ => x s) (siteGaussianMarks (Fin N × J) κ vs p) :=
    ((measurePreserving_eval (μ := fun _ : Fin N × J => gaussianReal 0 (vs p)) s).integrable_comp
      measurable_id.aestronglyMeasurable).2 (integrable_id_gaussianReal 0 (vs p))
  have h2 : Integrable (fun x : Fin κ → Fin N × J → ℝ => x p s)
      (Measure.pi (siteGaussianMarks (Fin N × J) κ vs)) :=
    ((measurePreserving_eval (μ := siteGaussianMarks (Fin N × J) κ vs) p).integrable_comp
      (measurable_pi_apply s).aestronglyMeasurable).2 h1
  have hbm : MeasurePreserving (fun z => branchMarks κ z α₀)
      (cascadeMarksLaw κ (siteGaussianMarks (Fin N × J) κ vs))
      (Measure.pi (siteGaussianMarks (Fin N × J) κ vs)) :=
    ⟨measurable_branchMarks κ α₀, cascadeMarksLaw_map_branchMarks κ _ α₀⟩
  have hg : Measurable fun x : Fin κ → Fin N × J → ℝ => x p s :=
    (measurable_pi_apply s).comp (measurable_pi_apply p)
  have h3 : Integrable (fun z : CascadeMarks (Fin N × J → ℝ) κ => branchMarks κ z α₀ p s)
      (cascadeMarksLaw κ (siteGaussianMarks (Fin N × J) κ vs)) :=
    (hbm.integrable_comp hg.aestronglyMeasurable).2 h2
  have hg3 : Measurable fun z : CascadeMarks (Fin N × J → ℝ) κ => branchMarks κ z α₀ p s :=
    hg.comp (measurable_branchMarks κ α₀)
  exact ((measurePreserving_snd (μ := Pm.prod (rootMarksLaw N v₀))
    (ν := cascadeMarksLaw κ (siteGaussianMarks (Fin N × J) κ vs))).integrable_comp
    hg3.aestronglyMeasurable).2 h3

omit [IsProbabilityMeasure Pm] [DecidableEq J] in
/-- Integrability of a coordinate of the disorder Hamiltonian under the joint law. -/
lemma integrable_disorder_coupledLaw (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) {Hf : Ω → EnergySpace N}
    (hHf : Measurable Hf) (hHint : ∀ τ, Integrable (fun ω => Hf ω τ) Pm) (τ : Config N) :
    Integrable (fun q : (Ω × (Fin N × J → ℝ)) × CascadeMarks (Fin N × J → ℝ) κ => Hf q.1.1 τ)
      (coupledLaw N Pm v₀ vs) := by
  have hm : Measurable fun ω => Hf ω τ :=
    ((continuous_apply τ).comp (PiLp.continuous_ofLp 2 (fun _ : Config N => ℝ))).measurable.comp
      hHf
  have h2 : Integrable (fun θ : Ω × (Fin N × J → ℝ) => Hf θ.1 τ) (Pm.prod (rootMarksLaw N v₀)) :=
    ((measurePreserving_fst (μ := Pm) (ν := rootMarksLaw N v₀)).integrable_comp
      hm.aestronglyMeasurable).2 (hHint τ)
  exact ((measurePreserving_fst (μ := Pm.prod (rootMarksLaw N v₀))
    (ν := cascadeMarksLaw κ (siteGaussianMarks (Fin N × J) κ vs))).integrable_comp
    (hm.comp measurable_fst).aestronglyMeasurable).2 h2

omit [DecidableEq J] in
/-- **The branch Hamiltonian of a fixed configuration along a fixed branch is integrable** under
the joint law of the disorder and the marks. -/
lemma integrable_pairBranchHamX_coupledLaw (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0)
    {Hf : Ω → EnergySpace N} (hHf : Measurable Hf) (hHint : ∀ τ, Integrable (fun ω => Hf ω τ) Pm)
    (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ)
    (α₀ : Fin κ → ℕ × ℕ) (σ₀ : Fin 2 → Config N) :
    Integrable (fun q : (Ω × (Fin N × J → ℝ)) × CascadeMarks (Fin N × J → ℝ) κ =>
      pairBranchHamX N κ (Hf q.1.1) lam a K₀ K q.1.2 (branchMarks κ q.2 α₀) σ₀)
      (coupledLaw N Pm v₀ vs) := by
  unfold pairBranchHamX pairBranchMark
  refine (((integrable_disorder_coupledLaw N v₀ vs hHf hHint (σ₀ 0)).add
    (integrable_disorder_coupledLaw N v₀ vs hHf hHint (σ₀ 1))).sub (integrable_const _)).add
    (integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun i _ =>
      ((integrable_const _).add ((integrable_finsetSum _ fun j _ =>
        (integrable_rootMark_coupledLaw N v₀ vs (i, j)).const_mul _).add
        (integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun j _ =>
          (integrable_branchMark_coupledLaw N v₀ vs α₀ p (i, j)).const_mul _))).const_mul _)

omit [DecidableEq J] in
/-- **`∫∫ |log G| < ∞`** for the branch functions `pairHamG (c, H(ω), λ, a, K₀, K, z₀)`,
`0 ≤ c ≤ 1` with `c_{σ₀} = 1`, when the disorder is integrable: `|log G| ≤ log |Σ_N²| + ∑_σ |H(σ)|`
and the branch Hamiltonians are integrable. -/
theorem lintegral_lintegral_enorm_log_pairHamG_ne_top {c : (Fin 2 → Config N) → ℝ}
    (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∀ σ, c σ ≤ 1) {σ₀ : Fin 2 → Config N} (hσ₀ : c σ₀ = 1)
    {Hf : Ω → EnergySpace N} (hHf : Measurable Hf) (hHint : ∀ τ, Integrable (fun ω => Hf ω τ) Pm)
    (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ)
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) :
    ∫⁻ θ, ∫⁻ x, ‖Real.log (pairHamG N κ c (Hf θ.1) lam a K₀ K θ.2 x).toReal‖ₑ
      ∂Measure.pi (siteGaussianMarks (Fin N × J) κ vs) ∂Pm.prod (rootMarksLaw N v₀) ≠ ∞ := by
  set F : Ω × (Fin N × J → ℝ) → (Fin κ → Fin N × J → ℝ) → ℝ≥0∞ := fun θ x =>
    ‖Real.log (pairHamG N κ c (Hf θ.1) lam a K₀ K θ.2 x).toReal‖ₑ with hF
  have hFm : Measurable (Function.uncurry F) :=
    (Real.measurable_log.comp (ENNReal.measurable_toReal.comp
      (measurable_pairHamG_branchParam N κ c hHf lam a K₀ K))).enorm
  set α₀ : Fin κ → ℕ × ℕ := fun _ => (0, 0) with hα₀
  rw [lintegral_lintegral_pi_eq κ (Pm.prod (rootMarksLaw N v₀))
    (siteGaussianMarks (Fin N × J) κ vs) F hFm α₀]
  have hbd : Integrable (fun q : (Ω × (Fin N × J → ℝ)) × CascadeMarks (Fin N × J → ℝ) κ =>
      Real.log (Fintype.card (Fin 2 → Config N))
        + ∑ τ, |pairBranchHamX N κ (Hf q.1.1) lam a K₀ K q.1.2 (branchMarks κ q.2 α₀) τ|)
      (coupledLaw N Pm v₀ vs) :=
    (integrable_const _).add (integrable_finsetSum _ fun τ _ =>
      (integrable_pairBranchHamX_coupledLaw N v₀ vs hHf hHint lam a K₀ K α₀ τ).abs)
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun q => ?_) hbd.lintegral_lt_top)
  rw [hF]
  simp only
  rw [Real.enorm_eq_ofReal_abs]
  refine (ENNReal.ofReal_le_ofReal (abs_log_pairHamG_le N κ hc0 hc1 hσ₀ _ _ _ _ _ _ _)).trans ?_
  exact le_rfl

omit [DecidableEq J] in
/-- `-H(σ₀) ≤ log ∑_σ c_σ e^{-H(σ)}` when `c_{σ₀} = 1`. -/
lemma neg_pairBranchHamX_le_log_pairBranchZX {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ)
    {σ₀ : Fin 2 → Config N} (hσ₀ : c σ₀ = 1) (H : EnergySpace N) (lam : ℝ)
    (a : Fin N × Fin 2 → ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin κ → Fin 2 → J → ℝ)
    (z₀ : Fin N × J → ℝ) (x : Fin κ → Fin N × J → ℝ) :
    -pairBranchHamX N κ H lam a K₀ K z₀ x σ₀
      ≤ Real.log (pairHamG N κ c H lam a K₀ K z₀ x).toReal := by
  rw [pairHamG, ENNReal.toReal_ofReal (pairBranchZX_nonneg N κ hc0 _ _ _ _ _ _ _)]
  have hle : Real.exp (-pairBranchHamX N κ H lam a K₀ K z₀ x σ₀)
      ≤ pairBranchZX N κ c H lam a K₀ K z₀ x := by
    unfold pairBranchZX
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum
      (f := fun σ => c σ * Real.exp (-pairBranchHamX N κ H lam a K₀ K z₀ x σ))
      (fun σ _ => mul_nonneg (hc0 σ) (Real.exp_pos _).le) (Finset.mem_univ σ₀))
    rw [hσ₀, one_mul]
  calc -pairBranchHamX N κ H lam a K₀ K z₀ x σ₀
      = Real.log (Real.exp (-pairBranchHamX N κ H lam a K₀ K z₀ x σ₀)) := (Real.log_exp _).symm
    _ ≤ _ := Real.log_le_log (Real.exp_pos _) hle

/-! ### The coupled scheme for the whole cascade, at fixed weights -/

omit [IsProbabilityMeasure Pm] [DecidableEq J] in
lemma integrable_smul_apply_disorder (ξ : ℝ → ℝ)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ)) (s : ℝ)
    (τ : Config N) : Integrable (fun ω => (s • G₀.U ω) τ) Pm := by
  refine (G₀.integrable.norm.const_mul |s|).mono' ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact (((continuous_apply τ).comp
      (PiLp.continuous_ofLp 2 (fun _ : Config N => ℝ))).measurable.comp
        (G₀.measU.const_smul s)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, PiLp.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (by rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le _ _) (abs_nonneg _)

/-- **Talagrand's (14.139)–(14.145) for the whole cascade at fixed weights of positive finite
mass**: with `F₁ = ∑_{R_{1,2}=u} e^{-H_N(σ¹)-H_N(σ²)-H⁰}` and, for any `λ`,
`F₂ = ∏ᵢ 4 (ch A_i ch B_i ch λ + sh A_i sh B_i sh λ)`,

`(1/N) 𝔼 log (∑_α v_α F₁(α) / ∑_α v_α)
  ≤ -λu + (1/N) 𝔼 log (∑_α v_α F₂(α) / ∑_α v_α)
    + ∫₀¹ 𝔼[(1/2) c₀ + (1/2)∑_{ℓ,ℓ'}⟨θ(ρ_{(α,γ)+1})⟩_t] dt`,

`c₀ = pairDiagConst ξ u (ρ_{κ+1})` (`= -2θ(1) - 2θ(u)` under (14.132)). -/
theorem coupled_fixed_weights (hN : 0 < N) (ξ : ℝ → ℝ) (ρ : Fin 2 → Fin 2 → ℕ → ℝ) (u : ℝ)
    (hρ0 : ∀ l l', ρ l l' 0 = 0) {S : Set ℝ} (hρS : ∀ l l' r, ρ l l' r ∈ S)
    (htan : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ q ∈ S, ξ q + (x - q) * deriv ξ q ≤ ξ x) (h0 : deriv ξ 0 = 0)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) {J₁ : Finset J} {L₀ L₀' : Fin 2 → J → ℝ}
    {L L' : Fin κ → Fin 2 → J → ℝ}
    (hC0 : ∀ l l', (v₀ : ℝ) * gram L₀ l l' = deriv ξ (ρ l l' 1) - deriv ξ (ρ l l' 0))
    (hC : ∀ (p : Fin κ) l l', (vs p : ℝ) * gram (L p) l l'
      = deriv ξ (ρ l l' (p.val + 2)) - deriv ξ (ρ l l' (p.val + 1)))
    (hL0 : ∀ l j, j ∉ J₁ → L₀ l j = 0) (hL : ∀ p l j, j ∉ J₁ → L p l j = 0)
    (hL0' : ∀ l j, j ∈ J₁ → L₀' l j = 0) (hL' : ∀ p l j, j ∈ J₁ → L' p l j = 0)
    (a : Fin N × Fin 2 → ℝ) (lam : ℝ) (w : CascadeWeights κ) (hW0 : weightSum κ w ≠ 0)
    (hW : weightSum κ w ≠ ∞) (hu : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    (1 / (N : ℝ)) * (∫ q, Real.log ((cascadeSum κ (coupledG N u a L₀ L₀' L L' ξ G₀ 1 q.1)
          (cascadeZip κ (w, q.2))).toReal
        / (cascadeSum κ (fun _ => 1) (cascadeZip κ (w, q.2))).toReal) ∂coupledLaw N Pm v₀ vs)
      ≤ -(lam * u) + (1 / (N : ℝ)) * (∫ q, Real.log ((cascadeSum κ
            (coupledEndG N lam a L₀ L₀' L L' q.1) (cascadeZip κ (w, q.2))).toReal
          / (cascadeSum κ (fun _ => 1) (cascadeZip κ (w, q.2))).toReal) ∂coupledLaw N Pm v₀ vs)
        + ∫ t in (0 : ℝ)..1, levelBoundLaw κ (Pm.prod (rootMarksLaw N v₀))
            (siteGaussianMarks (Fin N × J) κ vs) (coupledG N u a L₀ L₀' L L' ξ G₀)
            (pairDiagConst ξ u fun l l' => ρ l l' (κ + 1))
            (fun r => ∑ l : Fin 2, ∑ l' : Fin 2, parisiTheta ξ (ρ l l' (r + 1))) w t := by
  classical
  set P : Measure ((Ω × (Fin N × J → ℝ)) × CascadeMarks (Fin N × J → ℝ) κ) :=
    coupledLaw N Pm v₀ vs with hP
  set c₀ := pairDiagConst ξ u fun l l' => ρ l l' (κ + 1) with hc₀
  set θf : ℕ → ℝ := fun r => ∑ l : Fin 2, ∑ l' : Fin 2, parisiTheta ξ (ρ l l' (r + 1)) with hθf
  set G₁ : (Ω × (Fin N × J → ℝ)) → (Fin κ → Fin N × J → ℝ) → ℝ≥0∞ :=
    coupledG N u a L₀ L₀' L L' ξ G₀ 1 with hG₁
  set G₂ : (Ω × (Fin N × J → ℝ)) → (Fin κ → Fin N × J → ℝ) → ℝ≥0∞ :=
    coupledEndG N lam a L₀ L₀' L L' with hG₂
  obtain ⟨σ₀, hσ₀⟩ := hu
  have hcσ₀ : constraintR N u σ₀ = 1 := by
    unfold constraintR
    rw [ite_eq_left hσ₀]
  have hw : ∀ α, branchWeight κ w α ≠ ∞ :=
    fun α => ne_top_of_le_ne_top hW (branchWeight_le_weightSum κ w α)
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  set W : ℝ := (weightSum κ w).toReal with hWdef
  have hWpos : 0 < W := ENNReal.toReal_pos hW0 hW
  obtain ⟨α₀, hα₀, M₀, hM₀⟩ := exists_mem_truncFinset κ w hW0
  obtain ⟨M₁, hM₁⟩ := exists_truncWt_ne_zero κ w hW0 hW
  -- the branch functions at `t = 1`
  have hHf1 : Measurable fun ω => Real.sqrt 1 • G₀.U ω := by
    have h := G₀.measU.const_smul (Real.sqrt 1)
    exact h
  have hGm₁ : Measurable (Function.uncurry G₁) :=
    measurable_pairHamG_branchParam N κ (constraintR N u) hHf1 0 a
      (Real.sqrt (1 - 1) • L₀ + L₀') (fun p => Real.sqrt (1 - 1) • L p + L' p)
  have hGpos₁ : ∀ θ x, 0 < G₁ θ x :=
    fun θ x => coupledG_pos N u ⟨σ₀, hσ₀⟩ a L₀ L₀' L L' ξ G₀ 1 θ x
  have hGfin₁ : ∀ θ x, G₁ θ x ≠ ∞ := fun θ x => ENNReal.ofReal_ne_top
  have hSfin₁ : ∫⁻ q, cascadeSum κ (G₁ q.1) (cascadeZip κ (w, q.2)) ∂P ≠ ∞ :=
    lintegral_cascadeSum_pairHamG_ne_top N (constraintR_nonneg N u) (fun ω => Real.sqrt 1 • G₀.U ω)
      hHf1 (fun σ => G₀.lintegral_ofReal_exp_neg_smul_add_ne_top (Real.sqrt 1) (σ 0) (σ 1)) 0 a
      (Real.sqrt (1 - 1) • L₀ + L₀') (fun p => Real.sqrt (1 - 1) • L p + L' p) v₀ vs w hW
  set ℓ₁ : (Ω × (Fin N × J → ℝ)) × CascadeMarks (Fin N × J → ℝ) κ → ℝ := fun q =>
    -pairBranchHamX N κ (Real.sqrt 1 • G₀.U q.1.1) 0 a (Real.sqrt (1 - 1) • L₀ + L₀')
      (fun p => Real.sqrt (1 - 1) • L p + L' p) q.1.2 (branchMarks κ q.2 α₀) σ₀ with hℓ₁
  have hℓ₁int : Integrable ℓ₁ P :=
    (integrable_pairBranchHamX_coupledLaw N v₀ vs hHf1
      (fun τ => integrable_smul_apply_disorder N ξ G₀ (Real.sqrt 1) τ) 0 a
      (Real.sqrt (1 - 1) • L₀ + L₀') (fun p => Real.sqrt (1 - 1) • L p + L' p) α₀ σ₀).neg
  have hℓ₁le : ∀ q, ℓ₁ q ≤ Real.log (G₁ q.1 (branchMarks κ q.2 α₀)).toReal := fun q =>
    neg_pairBranchHamX_le_log_pairBranchZX N (constraintR_nonneg N u) hcσ₀ _ _ _ _ _ _ _
  -- the branch functions at the endpoint
  have hHf0 : Measurable fun _ : Ω => (0 : EnergySpace N) := measurable_const
  have hGm₂ : Measurable (Function.uncurry G₂) :=
    measurable_pairHamG_branchParam N κ (fun _ => 1) hHf0 lam a (L₀ + L₀') (fun p => L p + L' p)
  have hGpos₂ : ∀ θ x, 0 < G₂ θ x :=
    fun θ x => pairHamG_pos N κ (fun _ => zero_le_one) ⟨σ₀, one_pos⟩ _ _ _ _ _ _ _
  have hGfin₂ : ∀ θ x, G₂ θ x ≠ ∞ := fun θ x => ENNReal.ofReal_ne_top
  have hSfin₂ : ∫⁻ q, cascadeSum κ (G₂ q.1) (cascadeZip κ (w, q.2)) ∂P ≠ ∞ :=
    lintegral_cascadeSum_pairHamG_ne_top N (fun _ => zero_le_one) (fun _ => (0 : EnergySpace N))
      hHf0 (fun σ => by simp) lam a (L₀ + L₀') (fun p => L p + L' p) v₀ vs w hW
  set ℓ₂ : (Ω × (Fin N × J → ℝ)) × CascadeMarks (Fin N × J → ℝ) κ → ℝ := fun q =>
    -pairBranchHamX N κ (0 : EnergySpace N) lam a (L₀ + L₀') (fun p => L p + L' p) q.1.2
      (branchMarks κ q.2 α₀) σ₀ with hℓ₂
  have hℓ₂int : Integrable ℓ₂ P :=
    (integrable_pairBranchHamX_coupledLaw N v₀ vs hHf0
      (fun τ => by simp) lam a (L₀ + L₀') (fun p => L p + L' p) α₀ σ₀).neg
  have hℓ₂le : ∀ q, ℓ₂ q ≤ Real.log (G₂ q.1 (branchMarks κ q.2 α₀)).toReal := fun q =>
    neg_pairBranchHamX_le_log_pairBranchZX N (fun _ => zero_le_one)
      (rfl : (fun _ : Fin 2 → Config N => (1 : ℝ)) σ₀ = 1) _ _ _ _ _ _ _
  -- the limits
  have hlim₁ := tendsto_integral_log_truncSum κ (Pm.prod (rootMarksLaw N v₀))
    (siteGaussianMarks (Fin N × J) κ vs) G₁ hGm₁ hGpos₁ hGfin₁ w hW0 hW hSfin₁ hα₀ hℓ₁int hℓ₁le
  have hlim₂ := tendsto_integral_log_truncSum κ (Pm.prod (rootMarksLaw N v₀))
    (siteGaussianMarks (Fin N × J) κ vs) G₂ hGm₂ hGpos₂ hGfin₂ w hW0 hW hSfin₂ hα₀ hℓ₂int hℓ₂le
  have hlimB := tendsto_integral_truncLevelBoundLaw κ (Pm.prod (rootMarksLaw N v₀))
    (siteGaussianMarks (Fin N × J) κ vs) (coupledG N u a L₀ L₀' L L' ξ G₀)
    (measurable_coupledG N u a L₀ L₀' L L' ξ G₀)
    (fun t θ x => coupledG_pos N u ⟨σ₀, hσ₀⟩ a L₀ L₀' L L' ξ G₀ t θ x)
    (fun t θ => lintegral_coupledG_ne_top N vs u a L₀ L₀' L L' ξ G₀ t θ) c₀ θf w hW0 hW
    (M₀ := M₁) (fun M hM => continuous_truncLevelBoundLaw_coupled N M ξ G₀ v₀ vs L₀ L₀' L L' a
      w hw u (exists_coupledWt_ne_zero N M w u (hM₁ M hM) ⟨σ₀, hσ₀⟩) c₀ θf)
  -- the truncated inequality
  have hassoc : Pm.prod (siteMarksLaw (Fin N × J) κ v₀ vs)
      = ((Pm.prod (rootMarksLaw N v₀)).prod
          (cascadeMarksLaw κ (siteGaussianMarks (Fin N × J) κ vs))).map
            MeasurableEquiv.prodAssoc := prod_siteMarksLaw_eq N v₀ vs
  have hstar : ∀ M, max M₀ M₁ ≤ M →
      (1 / (N : ℝ)) * ∫ q, Real.log (truncSum κ M w (G₁ q.1) q.2).toReal ∂P
        ≤ -(lam * u) + (1 / (N : ℝ)) * ∫ q, Real.log (truncSum κ M w (G₂ q.1) q.2).toReal ∂P
          + ∫ t in (0 : ℝ)..1, truncLevelBoundLaw κ (Pm.prod (rootMarksLaw N v₀))
            (siteGaussianMarks (Fin N × J) κ vs) (coupledG N u a L₀ L₀' L L' ξ G₀) M c₀
            θf w t := by
    intro M hM
    have hM0 : M₀ ≤ M := le_of_max_le_left hM
    have hM1 : M₁ ≤ M := le_of_max_le_right hM
    have hmem := hM₀ M hM0
    have hne : ∃ p, coupledWt N M w u p ≠ 0 :=
      exists_coupledWt_ne_zero N M w u (hM₁ M hM1) ⟨σ₀, hσ₀⟩
    have h := coupled_truncated N M hN ξ ρ u hρ0 hρS htan h0 G₀ v₀ vs hC0 hC hL0 hL hL0'
      hL' a w hW (hM₁ M hM1) ⟨σ₀, hσ₀⟩
    -- the first endpoint
    have hmeas₁ : Measurable fun ω : Ω × SiteMarksSpace (Fin N × J) κ =>
        Real.log (truncSum κ M w (G₁ (ω.1, ω.2.1)) ω.2.2).toReal := by
      have := (measurable_log_truncSum_of κ G₁ hGm₁ M w).comp
        ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
          (measurable_snd.comp measurable_snd) :
          Measurable fun ω : Ω × SiteMarksSpace (Fin N × J) κ => ((ω.1, ω.2.1), ω.2.2))
      exact this
    have hE₁ : (∫ ω, wFreeEnergy (coupledWt N M w u) N ((coupledModelField N M ξ G₀ v₀ vs).U ω
          + coupledExtField N M Pm v₀ vs L₀' L' a ω) ∂Pm.prod (siteMarksLaw (Fin N × J) κ v₀ vs))
        = (1 / (N : ℝ)) * ∫ q, Real.log (truncSum κ M w (G₁ q.1) q.2).toReal ∂P := by
      have e : ∀ ω : Ω × SiteMarksSpace (Fin N × J) κ,
          wFreeEnergy (coupledWt N M w u) N ((coupledModelField N M ξ G₀ v₀ vs).U ω
            + coupledExtField N M Pm v₀ vs L₀' L' a ω)
          = (1 / (N : ℝ)) * Real.log (truncSum κ M w (G₁ (ω.1, ω.2.1)) ω.2.2).toReal := by
        intro ω
        rw [wFreeEnergy, coupledModelField_add_extField,
          wZ_coupledTruncHam N M 1 ξ G₀ v₀ vs L₀ L₀' L L' a w hw u ω]
      simp_rw [e]
      rw [integral_const_mul, hassoc, integral_map MeasurableEquiv.prodAssoc.measurable.aemeasurable
        hmeas₁.aestronglyMeasurable]
      rfl
    -- the second endpoint, with the bound (14.140)
    have hmeas₂ : Measurable fun ω : Ω × SiteMarksSpace (Fin N × J) κ =>
        Real.log (truncSum κ M w (G₂ (ω.1, ω.2.1)) ω.2.2).toReal := by
      have := (measurable_log_truncSum_of κ G₂ hGm₂ M w).comp
        ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
          (measurable_snd.comp measurable_snd) :
          Measurable fun ω : Ω × SiteMarksSpace (Fin N × J) κ => ((ω.1, ω.2.1), ω.2.2))
      exact this
    have hint₂ : Integrable (fun ω : Ω × SiteMarksSpace (Fin N × J) κ =>
        Real.log (truncSum κ M w (G₂ (ω.1, ω.2.1)) ω.2.2).toReal)
        (Pm.prod (siteMarksLaw (Fin N × J) κ v₀ vs)) := by
      rw [hassoc]
      exact (integrable_map_measure hmeas₂.aestronglyMeasurable
        MeasurableEquiv.prodAssoc.measurable.aemeasurable).2
        (integrable_log_truncSum_of κ (Pm.prod (rootMarksLaw N v₀))
          (siteGaussianMarks (Fin N × J) κ vs) G₂ hGm₂ hGpos₂ hGfin₂ w hW hSfin₂ hα₀ hℓ₂int hℓ₂le
          hmem)
    have hE₂ : (∫ ω, wFreeEnergy (coupledWt N M w u) N ((coupledTreeField N M Pm v₀ vs L₀ L).U ω
          + coupledExtField N M Pm v₀ vs L₀' L' a ω) ∂Pm.prod (siteMarksLaw (Fin N × J) κ v₀ vs))
        ≤ -(lam * u) + (1 / (N : ℝ)) * ∫ q, Real.log (truncSum κ M w (G₂ q.1) q.2).toReal ∂P := by
      have hpt : ∀ ω : Ω × SiteMarksSpace (Fin N × J) κ,
          wFreeEnergy (coupledWt N M w u) N ((coupledTreeField N M Pm v₀ vs L₀ L).U ω
            + coupledExtField N M Pm v₀ vs L₀' L' a ω)
          ≤ -(lam * u) + (1 / (N : ℝ))
              * Real.log (truncSum κ M w (G₂ (ω.1, ω.2.1)) ω.2.2).toReal := by
        intro ω
        rw [wFreeEnergy, coupledTreeField_add_extField N M ξ G₀ v₀ vs L₀ L₀' L L' a ω]
        have hle := wZ_coupledTruncHam_zero_le N M hN ξ G₀ v₀ vs L₀ L₀' L L' a w hw u lam ω
        have hZpos := wZ_pos (coupledWt N M w u) (coupledWt_nonneg N M w u) hne
          (coupledTruncHam N M 0 ξ G₀ v₀ vs L₀ L₀' L L' a ω)
        have hTpos : 0 < (truncSum κ M w (G₂ (ω.1, ω.2.1)) ω.2.2).toReal :=
          pos_of_mul_pos_right (hZpos.trans_le hle) (Real.exp_pos _).le
        have h1 := Real.log_le_log hZpos hle
        rw [Real.log_mul (Real.exp_pos _).ne' hTpos.ne', Real.log_exp] at h1
        have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 / N)
        have h3 : (1 / (N : ℝ)) * (-(lam * ((N : ℝ) * u))
            + Real.log (truncSum κ M w (G₂ (ω.1, ω.2.1)) ω.2.2).toReal)
            = -(lam * u) + (1 / (N : ℝ))
              * Real.log (truncSum κ M w (G₂ (ω.1, ω.2.1)) ω.2.2).toReal := by
          field_simp
        exact h2.trans (le_of_eq h3)
      have hintL : Integrable (fun ω : Ω × SiteMarksSpace (Fin N × J) κ =>
          wFreeEnergy (coupledWt N M w u) N ((coupledTreeField N M Pm v₀ vs L₀ L).U ω
            + coupledExtField N M Pm v₀ vs L₀' L' a ω))
          (Pm.prod (siteMarksLaw (Fin N × J) κ v₀ vs)) :=
        integrable_wFreeEnergy_of_integrable_norm _ (coupledWt_nonneg N M w u) hne N
          ((coupledTreeField N M Pm v₀ vs L₀ L).measU.add
            (measurable_coupledExtField N M v₀ vs L₀' L' a))
          ((coupledTreeField N M Pm v₀ vs L₀ L).integrable.add
            (integrable_coupledExtField N M v₀ vs L₀' L' a)).norm
      have hint₃ : Integrable (fun ω : Ω × SiteMarksSpace (Fin N × J) κ => -(lam * u)
          + (1 / (N : ℝ)) * Real.log (truncSum κ M w (G₂ (ω.1, ω.2.1)) ω.2.2).toReal)
          (Pm.prod (siteMarksLaw (Fin N × J) κ v₀ vs)) :=
        (integrable_const _).add (hint₂.const_mul _)
      refine (integral_mono hintL hint₃ hpt).trans (le_of_eq ?_)
      rw [integral_add (integrable_const _) (hint₂.const_mul _), integral_const, probReal_univ,
        one_smul, integral_const_mul, hassoc,
        integral_map MeasurableEquiv.prodAssoc.measurable.aemeasurable hmeas₂.aestronglyMeasurable]
      rfl
    -- combine
    rw [← hE₁]
    exact ((sub_le_iff_le_add.1 h).trans (add_le_add_right hE₂ _)).trans
      (le_of_eq (add_comm _ _))
  -- pass to the limit
  have hlimA : Tendsto (fun M => (1 / (N : ℝ))
      * ∫ q, Real.log (truncSum κ M w (G₁ q.1) q.2).toReal ∂P) atTop
      (𝓝 ((1 / (N : ℝ)) * ∫ q, Real.log (cascadeSum κ (G₁ q.1) (cascadeZip κ (w, q.2))).toReal ∂P))
    := hlim₁.const_mul _
  have hlimB' : Tendsto (fun M => -(lam * u) + (1 / (N : ℝ))
      * ∫ q, Real.log (truncSum κ M w (G₂ q.1) q.2).toReal ∂P
      + ∫ t in (0 : ℝ)..1, truncLevelBoundLaw κ (Pm.prod (rootMarksLaw N v₀))
          (siteGaussianMarks (Fin N × J) κ vs) (coupledG N u a L₀ L₀' L L' ξ G₀) M c₀ θf w t)
      atTop (𝓝 (-(lam * u) + (1 / (N : ℝ))
        * ∫ q, Real.log (cascadeSum κ (G₂ q.1) (cascadeZip κ (w, q.2))).toReal ∂P
        + ∫ t in (0 : ℝ)..1, levelBoundLaw κ (Pm.prod (rootMarksLaw N v₀))
          (siteGaussianMarks (Fin N × J) κ vs) (coupledG N u a L₀ L₀' L L' ξ G₀) c₀ θf w t)) :=
    (tendsto_const_nhds.add (hlim₂.const_mul _)).add hlimB
  have hle := le_of_tendsto_of_tendsto hlimA hlimB' (Filter.eventually_atTop.2 ⟨max M₀ M₁, hstar⟩)
  -- normalization by the total weight
  have hnorm : ∀ (Gt : (Ω × (Fin N × J → ℝ)) → (Fin κ → Fin N × J → ℝ) → ℝ≥0∞)
      (hGm : Measurable (Function.uncurry Gt)) (hGpos : ∀ θ x, 0 < Gt θ x)
      (hGfin : ∀ θ x, Gt θ x ≠ ∞)
      (hSfin : ∫⁻ q, cascadeSum κ (Gt q.1) (cascadeZip κ (w, q.2)) ∂P ≠ ∞)
      (ℓ : (Ω × (Fin N × J → ℝ)) × CascadeMarks (Fin N × J → ℝ) κ → ℝ) (hℓ : Integrable ℓ P)
      (hℓle : ∀ q, ℓ q ≤ Real.log (Gt q.1 (branchMarks κ q.2 α₀)).toReal),
      (∫ q, Real.log ((cascadeSum κ (Gt q.1) (cascadeZip κ (w, q.2))).toReal
          / (cascadeSum κ (fun _ => 1) (cascadeZip κ (w, q.2))).toReal) ∂P)
        = (∫ q, Real.log (cascadeSum κ (Gt q.1) (cascadeZip κ (w, q.2))).toReal ∂P)
          - Real.log W := by
    intro Gt hGm hGpos hGfin hSfin ℓ hℓ hℓle
    have hG : Measurable fun q : (ℝ × (Ω × (Fin N × J → ℝ))) × (Fin κ → Fin N × J → ℝ) =>
        Gt q.1.2 q.2 := hGm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    have hSm := measurable_cascadeSum_of κ (fun _ θ => Gt θ) hG w 0
    have hSlt : ∀ᵐ q ∂P, cascadeSum κ (Gt q.1) (cascadeZip κ (w, q.2)) < ∞ :=
      ae_lt_top hSm hSfin
    have hae : ∀ᵐ q ∂P, Real.log ((cascadeSum κ (Gt q.1) (cascadeZip κ (w, q.2))).toReal
          / (cascadeSum κ (fun _ => 1) (cascadeZip κ (w, q.2))).toReal)
        = Real.log (cascadeSum κ (Gt q.1) (cascadeZip κ (w, q.2))).toReal - Real.log W := by
      filter_upwards [hSlt] with q hq
      have hSpos : 0 < (cascadeSum κ (Gt q.1) (cascadeZip κ (w, q.2))).toReal :=
        ENNReal.toReal_pos (cascadeSum_of_ne_zero κ (fun _ θ => Gt θ) hG (fun _ => hGpos) 0 q.1 w
          hW0 q.2) hq.ne
      rw [cascadeSum_one_cascadeZip, Real.log_div hSpos.ne' hWpos.ne']
    rw [integral_congr_ae hae, integral_sub (integrable_log_cascadeSum_of κ
      (Pm.prod (rootMarksLaw N v₀)) (siteGaussianMarks (Fin N × J) κ vs) Gt hGm hGpos
      hGfin w hW hSfin hα₀ hℓ hℓle) (integrable_const _), integral_const, probReal_univ, one_smul]
  rw [hnorm G₁ hGm₁ hGpos₁ hGfin₁ hSfin₁ ℓ₁ hℓ₁int hℓ₁le,
    hnorm G₂ hGm₂ hGpos₂ hGfin₂ hSfin₂ ℓ₂ hℓ₂int hℓ₂le, mul_sub, mul_sub]
  generalize (1 / (N : ℝ)) = cN at hle ⊢
  have h2 := sub_le_sub_right hle (cN * Real.log W)
  refine h2.trans (le_of_eq ?_)
  ring

end

end SpinGlass
