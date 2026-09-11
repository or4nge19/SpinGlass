/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.TreeCov
import SpinGlass.Parisi.GuerraBound
import SpinGlass.FiniteGibbs.GaussianFieldProd
import SpinGlass.MixedPSpinThermodynamicLimit
import SpinGlass.Hopfield

/-!
# Guerra's broken replica-symmetry bound: the interpolation for a truncated tree

Talagrand, Vol. II, §14.4, Lemma 14.4.1–(14.79) for the tree truncated to indices `< M`, at
fixed weights. On the state space `Σ_N × A`, `A = TruncBranch k M`, the model Hamiltonian
`H_N(σ)` (lifted) and the marks field `H(σ, α)` (Talagrand's (14.73)) are independent centered
Gaussian fields on the product of the model law `N(0, N ξ(R))` with the marks law, and the
weighted comparison bound `wFreeEnergy_sub_le` with the weights `u*_α` of the branches gives
`p_N ≤ 𝔼 (1/N) log ∑_α v_α ∏ᵢ 2cosh(h + z₀ᵢ + ∑ₚ z_{i,p,α}) + ∫₀¹ b(t) dt`,
`b(t) = (1/2)(ξ(1) − ξ'(q_{k+1})) + (1/2) 𝔼⟨θ(q_{(α,γ)})⟩_t` (`guerra_truncated`).

This file provides the two computations of §14.4 behind the endpoints: the weighted partition
function of the lifted model Hamiltonian factorizes off the total weight
(`wZ_pullback_fst`), and that of the marks field is the Ising site factorization (14.80)
(`wZ_treeLin`), together with the continuity of the weighted Gibbs weights in the Hamiltonian.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable {N : ℕ} {A : Type*} [Fintype A]

/-! ### Weighted partition functions on `Σ_N × A` -/

/-- Weights depending only on the branch. -/
def branchWt (w : A → ℝ) : Config N × A → ℝ := fun x => w x.2

/-- The branch weights as weights `u_α · c_σ` on `Σ_N × A` with the trivial constraint `c = 1`. -/
lemma branchWt_eq (w : A → ℝ) :
    branchWt (N := N) w = fun p : Config N × A => w p.2 * (fun _ : Config N => (1 : ℝ)) p.1 := by
  funext p
  simp [branchWt]

/-- The weighted partition function of a Hamiltonian that does not depend on the branch
factorizes: `∑_{σ,α} w_α e^{-H σ} = (∑_α w_α) · Z(H)`. -/
lemma wZ_pullback_fst (w : A → ℝ) (H : EnergySpace N) :
    wZ (branchWt (N := N) w) (pullbackCLM Prod.fst H) = (∑ α, w α) * Z N H := by
  unfold wZ Z branchWt
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  rfl

/-- The weighted partition function of a Hamiltonian of the form `∑ᵢ σᵢ aᵢ(α)`, plus a field
`h`, is the Ising site factorization `∑_α w_α ∏ᵢ 2 cosh(h + aᵢ(α))` (Talagrand's (14.80)). -/
lemma wZ_ising (w : A → ℝ) (a : A → Fin N → ℝ) (h : ℝ) :
    wZ (branchWt (N := N) w)
        (WithLp.toLp 2 (fun x : Config N × A => ∑ i, isingSpin (x.1 i) * a x.2 i)
          + pullbackCLM Prod.fst (H_field N h))
      = ∑ α, w α * ∏ i, (2 * Real.cosh (h + a α i)) := by
  unfold wZ branchWt
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  dsimp only
  rw [← Finset.mul_sum]
  congr 1
  have hval : ∀ σ : Config N, -(((WithLp.toLp 2 (fun x : Config N × A =>
      ∑ i, isingSpin (x.1 i) * a x.2 i) + pullbackCLM Prod.fst (H_field N h) :
        FiniteGibbs.EnergySpace (Config N × A))) (σ, α))
      = ∑ i, (-(h + a α i)) * spin N σ i := by
    intro σ
    change -((∑ i, isingSpin (σ i) * a α i) + h * ∑ i, isingSpin (σ i)) = _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [spin, spinOf]; ring
  simp_rw [hval]
  rw [sum_exp_sum_spin N (fun i => -(h + a α i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [neg_neg, add_comm, exp_add_exp_neg_eq_two_cosh]

/-! ### The interpolation for a truncated tree at fixed weights -/

variable (N k M : ℕ)

/-- The address of a truncated branch. -/
def truncBranchCoe (α : TruncBranch k M) : Fin k → ℕ × ℕ := fun i => ((α i).1, (α i).2)

/-- The weights `u*_α` of the truncated branches, as real numbers. -/
def truncWt (w : CascadeWeights k) : TruncBranch k M → ℝ :=
  fun α => (branchWeight k w (truncBranchCoe k M α)).toReal

omit N in
lemma truncWt_nonneg (w : CascadeWeights k) (α : TruncBranch k M) : 0 ≤ truncWt k M w α :=
  ENNReal.toReal_nonneg

/-- The interpolating Hamiltonian `√t H_N(σ) + √(1-t) H(σ,α)` plus the field, on the product
of the model law with the marks law. -/
def truncHam (t h : ℝ) (ω : EnergySpace N × MarksSpace N k) :
    FiniteGibbs.EnergySpace (Config N × TruncBranch k M) :=
  Real.sqrt t • pullbackCLM Prod.fst ω.1 + Real.sqrt (1 - t) • treeLin N k M (treeCoords N k M ω.2)
    + pullbackCLM Prod.fst (H_field N h)

lemma measurable_truncHam (t h : ℝ) : Measurable (truncHam N k M t h) := by
  have h1 : Measurable fun ω : EnergySpace N × MarksSpace N k =>
      Real.sqrt t • pullbackCLM (Prod.fst : Config N × TruncBranch k M → Config N) ω.1 :=
    (Real.sqrt t • pullbackCLM
      (Prod.fst : Config N × TruncBranch k M → Config N)).continuous.measurable.comp
      measurable_fst
  have h2 : Measurable fun ω : EnergySpace N × MarksSpace N k =>
      Real.sqrt (1 - t) • treeLin N k M (treeCoords N k M ω.2) :=
    (Real.sqrt (1 - t) • treeLin N k M).continuous.measurable.comp
      ((measurable_treeCoords N k M).comp measurable_snd)
  exact (h1.add h2).add measurable_const

/-- The bound (14.79) at time `t` for the weights `w`:
`𝔼 [(1/2)(ξ(1) - ξ'(q_{k+1})) + (1/2) ⟨θ(q_{(α,γ)})⟩_t]`. -/
def guerraTruncBound (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : ℝ) (w : CascadeWeights k)
    (t : ℝ) : ℝ :=
  ∫ ω, treeBoundIntegrand (branchWt (N := N) (truncWt k M w)) (ξ 1 - deriv ξ (qs (Fin.last k)))
      (fun x y => parisiTheta ξ (treeOverlap qs x.2 y.2)) (truncHam N k M t h ω)
    ∂(gaussField N (overlapCovMatrix N ξ)).prod
      (marksLaw N k (parisiVar ξ qs 0) fun p => parisiVar ξ qs (p.val + 1))

/-- The bound of the truncated interpolation is continuous in `t`. -/
lemma continuous_guerraTruncBound (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : ℝ)
    (w : CascadeWeights k) (hne : ∃ α : TruncBranch k M, truncWt k M w α ≠ 0) :
    Continuous (guerraTruncBound N k M ξ qs h w) := by
  set wt : Config N × TruncBranch k M → ℝ := branchWt (N := N) (truncWt k M w) with hwtdef
  have hwt : ∀ x, 0 ≤ wt x := fun x => truncWt_nonneg k M w x.2
  have hne' : ∃ x, wt x ≠ 0 := by
    obtain ⟨α, hα⟩ := hne
    exact ⟨(fun _ => true, α), hα⟩
  set c₀ := ξ 1 - deriv ξ (qs (Fin.last k)) with hc₀
  set θq : Config N × TruncBranch k M → Config N × TruncBranch k M → ℝ :=
    fun x y => parisiTheta ξ (treeOverlap qs x.2 y.2) with hθq
  have hmeasP : ∀ t, AEStronglyMeasurable (fun ω : EnergySpace N × MarksSpace N k =>
      treeBoundIntegrand wt c₀ θq (truncHam N k M t h ω))
      ((gaussField N (overlapCovMatrix N ξ)).prod
        (marksLaw N k (parisiVar ξ qs 0) fun p => parisiVar ξ qs (p.val + 1))) := fun t =>
    ((continuous_treeBoundIntegrand wt hwt hne' c₀ θq).measurable.comp
      (measurable_truncHam N k M t h)).aestronglyMeasurable
  have hbound : ∀ t ω, ‖treeBoundIntegrand wt c₀ θq (truncHam N k M t h ω)‖
      ≤ (1 / 2) * |c₀| + (1 / 2) * ∑ x, ∑ y, |θq x y| := fun t ω => by
    rw [Real.norm_eq_abs]
    exact abs_treeBoundIntegrand_le wt hwt hne' c₀ θq _
  unfold guerraTruncBound
  refine MeasureTheory.continuous_of_dominated (fun t => hmeasP t)
    (bound := fun _ => (1 / 2) * |c₀| + (1 / 2) * ∑ x, ∑ y, |θq x y|)
    (fun t => Filter.Eventually.of_forall fun ω => hbound t ω) (integrable_const _)
    (Filter.Eventually.of_forall fun ω => ?_)
  refine (continuous_treeBoundIntegrand wt hwt hne' c₀ θq).comp ?_
  unfold truncHam
  exact ((Real.continuous_sqrt.smul continuous_const).add
    ((Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).smul continuous_const)).add
    continuous_const

/-- **Guerra's interpolation for the tree truncated to indices `< M`, at fixed weights `w`**
(Talagrand's Lemma 14.4.1 with (14.79) and (14.80), integrated over `t`):
`p_N ≤ 𝔼 (1/N) log ∑_α u*_α ∏ᵢ 2cosh(h + z₀ᵢ + ∑ₚ z_{i,p,α}) − (1/N) log ∑_α u*_α + ∫₀¹ b(t) dt`. -/
theorem guerra_truncated (hN : 0 < N) (ξ : ℝ → ℝ) (hS : (overlapCovMatrix N ξ).PosSemidef)
    (qs : Fin (k + 1) → ℝ) (h0 : deriv ξ 0 = 0)
    (hmono : ∀ r, r ≤ k + 1 → deriv ξ (qExt qs r) ≤ deriv ξ (qExt qs (r + 1)))
    (hq01 : ∀ r, qExt qs r ∈ Set.Icc (0 : ℝ) 1)
    (htan : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ q ∈ Set.Icc (0 : ℝ) 1, ξ q + (x - q) * deriv ξ q ≤ ξ x)
    (h : ℝ) (w : CascadeWeights k) (hne : ∃ α : TruncBranch k M, truncWt k M w α ≠ 0) :
    mixedPSpinFreeEnergy N ξ h
      ≤ (∫ z, (1 / (N : ℝ)) * Real.log (∑ α, truncWt k M w α
            * ∏ i, (2 * Real.cosh (h + treeMark N k M z α i)))
          ∂marksLaw N k (parisiVar ξ qs 0) fun p => parisiVar ξ qs (p.val + 1))
        - (1 / (N : ℝ)) * Real.log (∑ α, truncWt k M w α)
        + ∫ t in (0 : ℝ)..1, guerraTruncBound N k M ξ qs h w t := by
  classical
  set v₀ := parisiVar ξ qs 0 with hv₀
  set vs : Fin k → ℝ≥0 := fun p => parisiVar ξ qs (p.val + 1) with hvs
  set Pm : Measure (EnergySpace N) := gaussField N (overlapCovMatrix N ξ) with hPm
  set Pz := marksLaw N k v₀ vs with hPz
  set wt : Config N × TruncBranch k M → ℝ := branchWt (N := N) (truncWt k M w) with hwtdef
  set c := pullbackCLM (Prod.fst : Config N × TruncBranch k M → Config N) (H_field N h) with hc
  -- the two fields
  let G₁ := ((GaussianField.ofMultivariateGaussian hS).comp
    (Prod.fst : Config N × TruncBranch k M → Config N)).prodLeft Pz
  let G₂ := (treeField N k M v₀ vs).prodRight Pm
  have hindep : G₁.U ⟂ᵢ[Pm.prod Pz] G₂.U := GaussianField.prodLeft_indepFun_prodRight _ _
  have hwt : ∀ x, 0 ≤ wt x := fun x => truncWt_nonneg k M w x.2
  have hne' : ∃ x, wt x ≠ 0 := by
    obtain ⟨α, hα⟩ := hne
    exact ⟨(fun _ => true, α), hα⟩
  have hK₁ : (fun x y : Config N × TruncBranch k M => overlapCovMatrix N ξ x.1 y.1)
      = modelKernel N ξ := by
    funext x y
    rfl
  have hK₂ : treeFieldKernel N k M v₀ vs = treeKernel N ξ (treeOverlap qs) :=
    treeFieldKernel_eq_treeKernel hN ξ qs hmono h0
  -- the integrand bound and its integrability
  set c₀ := ξ 1 - deriv ξ (qs (Fin.last k)) with hc₀
  set θq : Config N × TruncBranch k M → Config N × TruncBranch k M → ℝ :=
    fun x y => parisiTheta ξ (treeOverlap qs x.2 y.2) with hθq
  have hU₁ : ∀ ω : EnergySpace N × MarksSpace N k, G₁.U ω = pullbackCLM Prod.fst ω.1 :=
    fun ω => rfl
  have hU₂ : ∀ ω : EnergySpace N × MarksSpace N k,
      G₂.U ω = treeLin N k M (treeCoords N k M ω.2) := fun ω => rfl
  have hpair : ∀ t ω, gaussianInterp t (pair G₁ G₂ ω) + c = truncHam N k M t h ω := by
    intro t ω
    change gaussianInterp t (WithLp.toLp 2 (G₁.U ω, G₂.U ω)) + c = _
    rw [gaussianInterp_apply, WithLp.ofLp_toLp, hU₁, hU₂]
    rfl
  -- the bound is continuous in `t`
  have hcontb : Continuous (guerraTruncBound N k M ξ qs h w) :=
    continuous_guerraTruncBound N k M ξ qs h w hne
  -- the trace bound
  have hb : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      (∫ p, wGuerraTrace wt (fun x y => overlapCovMatrix N ξ x.1 y.1) (treeFieldKernel N k M v₀ vs)
        N (gaussianInterp t p + c) ∂pairLaw G₁ G₂) ≤ guerraTruncBound N k M ξ qs h w t := by
    intro t _
    have hG := isGaussian_pairLaw G₁ G₂ hindep
    have hcontT := continuous_wGuerraTrace wt hwt hne'
      (fun x y : Config N × TruncBranch k M => overlapCovMatrix N ξ x.1 y.1)
      (treeFieldKernel N k M v₀ vs) N
    have hint1 : Integrable (fun p : PairSpace (Config N × TruncBranch k M) =>
        wGuerraTrace wt (fun x y : Config N × TruncBranch k M => overlapCovMatrix N ξ x.1 y.1)
          (treeFieldKernel N k M v₀ vs) N (gaussianInterp t p + c)) (pairLaw G₁ G₂) := by
      refine Integrable.of_bound ((hcontT.comp
        ((gaussianInterp t).continuous.add continuous_const)).aestronglyMeasurable)
        ((1 / (2 * (N : ℝ)))
          * ((∑ x, |overlapCovMatrix N ξ x.1 x.1 - treeFieldKernel N k M v₀ vs x x|)
          + ∑ x, ∑ y, |overlapCovMatrix N ξ x.1 y.1 - treeFieldKernel N k M v₀ vs x y|))
        (Filter.Eventually.of_forall fun p => ?_)
      rw [Real.norm_eq_abs]
      exact abs_wGuerraTrace_le wt hwt hne' _ _ N _
    have hint2 : Integrable (fun p : PairSpace (Config N × TruncBranch k M) =>
        treeBoundIntegrand wt c₀ θq (gaussianInterp t p + c)) (pairLaw G₁ G₂) := by
      refine Integrable.of_bound (((continuous_treeBoundIntegrand wt hwt hne' c₀ θq).comp
        ((gaussianInterp t).continuous.add continuous_const)).aestronglyMeasurable)
        ((1 / 2) * |c₀| + (1 / 2) * ∑ x, ∑ y, |θq x y|)
        (Filter.Eventually.of_forall fun p => ?_)
      rw [Real.norm_eq_abs]
      exact abs_treeBoundIntegrand_le wt hwt hne' c₀ θq _
    refine (integral_mono hint1 hint2 fun p => ?_).trans (le_of_eq ?_)
    · change wGuerraTrace wt (modelKernel N ξ) (treeFieldKernel N k M v₀ vs) N _ ≤ _
      rw [hK₂]
      exact wGuerraTrace_tree_le hN ξ (treeOverlap qs) (qs (Fin.last k)) (treeOverlap_self qs)
        (fun α γ => hq01 _) htan wt hwt hne' _
    · unfold guerraTruncBound
      change ∫ p, treeBoundIntegrand wt c₀ θq (gaussianInterp t p + c)
        ∂(Pm.prod Pz).map (pair G₁ G₂)
        = _
      have hmeasF : AEStronglyMeasurable (fun p : PairSpace (Config N × TruncBranch k M) =>
          treeBoundIntegrand wt c₀ θq (gaussianInterp t p + c)) ((Pm.prod Pz).map (pair G₁ G₂)) :=
        ((continuous_treeBoundIntegrand wt hwt hne' c₀ θq).comp
          ((gaussianInterp t).continuous.add continuous_const)).aestronglyMeasurable
      rw [integral_map (measurable_pair G₁ G₂).aemeasurable hmeasF]
      simp_rw [hpair]
      rfl
  have hbint : IntervalIntegrable (guerraTruncBound N k M ξ qs h w) volume 0 1 :=
    hcontb.intervalIntegrable 0 1
  -- the comparison bound
  have hmain := wFreeEnergy_sub_le G₁ G₂ hindep wt hwt hne' c N hb hbint
  -- the first endpoint: `(1/N) log ∑ w + p_N`
  have hsum_pos : 0 < ∑ α, truncWt k M w α := by
    obtain ⟨α, hα⟩ := hne
    exact Finset.sum_pos' (fun α _ => truncWt_nonneg k M w α)
      ⟨α, Finset.mem_univ _, lt_of_le_of_ne (truncWt_nonneg k M w α) hα.symm⟩
  have hE1 : ∀ ω : EnergySpace N × MarksSpace N k, wFreeEnergy wt N (G₁.U ω + c)
      = (1 / (N : ℝ)) * Real.log (∑ α, truncWt k M w α)
        + free_energy_density (N := N) (ω.1 + H_field N h) := by
    intro ω
    have hU : G₁.U ω + c = pullbackCLM Prod.fst (ω.1 + H_field N h) := by
      rw [map_add]
      rfl
    rw [wFreeEnergy, hU, hwtdef, wZ_pullback_fst, Real.log_mul hsum_pos.ne' (Z_pos N _).ne',
      mul_add]
    rfl
  have hint_fe : Integrable (fun ω : EnergySpace N × MarksSpace N k =>
      free_energy_density (N := N) (ω.1 + H_field N h)) (Pm.prod Pz) := by
    refine integrable_free_energy_density_of_isGaussian N (Pm.prod Pz)
      (g := fun ω : EnergySpace N × MarksSpace N k => ω.1 + H_field N h)
      (measurable_fst.add_const _) ?_
    have hmap : (Pm.prod Pz).map (fun ω : EnergySpace N × MarksSpace N k => ω.1 + H_field N h)
        = Pm.map (fun H => H + H_field N h) := by
      have hfst : Pm = (Pm.prod Pz).map Prod.fst := by
        rw [Measure.map_fst_prod, measure_univ, one_smul]
      have hadd : Measurable fun H : EnergySpace N => H + H_field N h := measurable_id.add_const _
      conv_rhs => rw [hfst]
      rw [Measure.map_map hadd measurable_fst]
      rfl
    rw [hmap, hPm, gaussField]
    infer_instance
  have hE1' : (∫ ω, wFreeEnergy wt N (G₁.U ω + c) ∂Pm.prod Pz)
      = (1 / (N : ℝ)) * Real.log (∑ α, truncWt k M w α) + mixedPSpinFreeEnergy N ξ h := by
    simp_rw [hE1]
    rw [integral_add (integrable_const _) hint_fe, integral_const, probReal_univ, one_smul]
    congr 1
    change _ = ∫ H, free_energy_density (N := N) (H + H_field N h) ∂Pm
    have hcont : Continuous fun H : EnergySpace N =>
        free_energy_density (N := N) (H + H_field N h) :=
      (contDiff_free_energy_density N).continuous.comp (continuous_id.add continuous_const)
    have hmeasF : AEStronglyMeasurable
        (fun H : EnergySpace N => free_energy_density (N := N) (H + H_field N h))
        ((Pm.prod Pz).map Prod.fst) := hcont.aestronglyMeasurable
    rw [← integral_map measurable_fst.aemeasurable hmeasF, Measure.map_fst_prod, measure_univ,
      one_smul]
  -- the second endpoint: the Ising site factorization (14.80)
  have hE2 : ∀ ω : EnergySpace N × MarksSpace N k, wFreeEnergy wt N (G₂.U ω + c)
      = (1 / (N : ℝ)) * Real.log (∑ α, truncWt k M w α
          * ∏ i, (2 * Real.cosh (h + treeMark N k M ω.2 α i))) := by
    intro ω
    rw [wFreeEnergy, hU₂]
    have hV : treeLin N k M (treeCoords N k M ω.2)
        = WithLp.toLp 2 (fun x : Config N × TruncBranch k M =>
            ∑ i, isingSpin (x.1 i) * treeMark N k M ω.2 x.2 i) := by
      ext x
      exact treeLin_treeCoords_apply N k M ω.2 x
    rw [hV, hwtdef, hc, wZ_ising]
  have hmeasE2 : Measurable fun z : MarksSpace N k => (1 / (N : ℝ)) * Real.log (∑ α, truncWt k M w α
      * ∏ i, (2 * Real.cosh (h + treeMark N k M z α i))) := by
    refine measurable_const.mul (Real.measurable_log.comp (Finset.measurable_sum _ fun α _ =>
      measurable_const.mul (Finset.measurable_prod _ fun i _ => measurable_const.mul
        (Real.continuous_cosh.measurable.comp (measurable_const.add ?_)))))
    unfold treeMark
    exact ((measurable_pi_apply i).comp measurable_fst).add (Finset.measurable_sum _ fun p _ =>
      (measurable_pi_apply i).comp ((measurable_pi_apply (branchNode k M α p)).comp
        ((measurable_truncMarks k M).comp measurable_snd)))
  have hE2' : (∫ ω, wFreeEnergy wt N (G₂.U ω + c) ∂Pm.prod Pz)
      = ∫ z, (1 / (N : ℝ)) * Real.log (∑ α, truncWt k M w α
          * ∏ i, (2 * Real.cosh (h + treeMark N k M z α i))) ∂Pz := by
    simp_rw [hE2]
    have hmeasF : AEStronglyMeasurable (fun z : MarksSpace N k => (1 / (N : ℝ))
        * Real.log (∑ α, truncWt k M w α * ∏ i, (2 * Real.cosh (h + treeMark N k M z α i))))
        ((Pm.prod Pz).map Prod.snd) := hmeasE2.aestronglyMeasurable
    rw [← integral_map measurable_snd.aemeasurable hmeasF, Measure.map_snd_prod, measure_univ,
      one_smul]
  have hmain' : (∫ ω, wFreeEnergy wt N (G₁.U ω + c) ∂Pm.prod Pz)
      - (∫ ω, wFreeEnergy wt N (G₂.U ω + c) ∂Pm.prod Pz)
      ≤ ∫ t in (0 : ℝ)..1, guerraTruncBound N k M ξ qs h w t := hmain
  rw [hE1', hE2'] at hmain'
  linarith

end

end SpinGlass
