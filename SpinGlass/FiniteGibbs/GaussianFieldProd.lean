/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.FiniteGibbs.GaussianFieldPullback

/-!
# Gaussian fields on a product space, and the canonical field of a covariance matrix

Two constructions for Guerra's interpolation on a state space `Σ_N × A`:

* a Gaussian field on `P` and one on `Q` live on `P ⊗ Q` through the projections
  (`GaussianField.prodLeft`, `GaussianField.prodRight`), and they are independent there
  (`GaussianField.prodLeft_indepFun_prodRight`);
* every positive semidefinite matrix `S` is the kernel of the canonical field `id` under the
  multivariate Gaussian `N(0, S)` (`GaussianField.ofMultivariateGaussian`).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace SpinGlass

namespace FiniteGibbs

noncomputable section

variable {α : Type*} [Fintype α]

/-! ### Transport along a measure-preserving map -/

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
  {K : α → α → ℝ}

/-- A Gaussian field on `P` is a Gaussian field on any `P'` mapping onto `P`. -/
def GaussianField.compMeasurable (G : GaussianField (α := α) P K) (f : Ω' → Ω)
    (hf : Measurable f) (hmap : Q.map f = P) : GaussianField (α := α) Q K where
  U := G.U ∘ f
  measU := G.measU.comp hf
  hU := by
    have : IsGaussian (Q.map (G.U ∘ f)) := by
      rw [← Measure.map_map G.measU hf, hmap]
      exact G.isGaussian
    exact IsGaussian.hasGaussianLaw
  mean0 := by
    rw [← Measure.map_map G.measU hf, hmap]
    exact G.mean0
  cov_eq := fun x y => by
    rw [← Measure.map_map G.measU hf, hmap]
    exact G.cov_eq x y

@[simp] lemma GaussianField.compMeasurable_U (G : GaussianField (α := α) P K) (f : Ω' → Ω)
    (hf : Measurable f) (hmap : Q.map f = P) (ω : Ω') :
    (G.compMeasurable f hf hmap).U ω = G.U (f ω) := rfl

/-! ### Fields on a product space -/

variable [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

/-- A field on `P`, as a field on `P ⊗ Q` through the first projection. -/
def GaussianField.prodLeft (G : GaussianField (α := α) P K) (Q : Measure Ω')
    [IsProbabilityMeasure Q] : GaussianField (α := α) (P.prod Q) K :=
  G.compMeasurable Prod.fst measurable_fst (by rw [Measure.map_fst_prod, measure_univ, one_smul])

/-- A field on `Q`, as a field on `P ⊗ Q` through the second projection. -/
def GaussianField.prodRight (P : Measure Ω) [IsProbabilityMeasure P] {K' : α → α → ℝ}
    (G : GaussianField (α := α) Q K') : GaussianField (α := α) (P.prod Q) K' :=
  G.compMeasurable Prod.snd measurable_snd (by rw [Measure.map_snd_prod, measure_univ, one_smul])

omit [IsProbabilityMeasure P] in
@[simp] lemma GaussianField.prodLeft_U (G : GaussianField (α := α) P K) (ω : Ω × Ω') :
    (G.prodLeft Q).U ω = G.U ω.1 := rfl

@[simp] lemma GaussianField.prodRight_U {K' : α → α → ℝ} (G : GaussianField (α := α) Q K')
    (ω : Ω × Ω') : (G.prodRight P).U ω = G.U ω.2 := rfl

/-- The two fields on a product space are independent. -/
lemma GaussianField.prodLeft_indepFun_prodRight (G : GaussianField (α := α) P K)
    {K' : α → α → ℝ} (G' : GaussianField (α := α) Q K') :
    (G.prodLeft Q).U ⟂ᵢ[P.prod Q] (G'.prodRight P).U :=
  indepFun_prod G.measU G'.measU

/-! ### The opposite of a field -/

omit [IsProbabilityMeasure P] [IsProbabilityMeasure Q] in
/-- The opposite `-U` of a centered Gaussian field is a centered Gaussian field with the same
kernel. -/
def GaussianField.neg (G : GaussianField (α := α) P K) : GaussianField (α := α) P K where
  U := fun ω => -G.U ω
  measU := G.measU.neg
  hU := G.hU.fun_neg
  mean0 := by
    have hmap : P.map (fun ω => -G.U ω) = (P.map G.U).map (-ContinuousLinearMap.id ℝ _) := by
      rw [Measure.map_map (-ContinuousLinearMap.id ℝ _).continuous.measurable G.measU]
      rfl
    have hG : IsGaussian (P.map G.U) := G.isGaussian
    have hmem : MemLp (id : EnergySpace α → EnergySpace α) 2 (P.map G.U) :=
      IsGaussian.memLp_two_id
    rw [hmap, integral_map (f := fun x : EnergySpace α => x)
      (-ContinuousLinearMap.id ℝ _).continuous.measurable.aemeasurable
      measurable_id.aestronglyMeasurable,
      ContinuousLinearMap.integral_comp_comm (-ContinuousLinearMap.id ℝ _)
        (φ := fun x : EnergySpace α => x) (hmem.integrable (by norm_num)), G.mean0, map_zero]
  cov_eq := fun x y => by
    have hmap : P.map (fun ω => -G.U ω) = (P.map G.U).map (-ContinuousLinearMap.id ℝ _) := by
      rw [Measure.map_map (-ContinuousLinearMap.id ℝ _).continuous.measurable G.measU]
      rfl
    have hG : IsGaussian (P.map G.U) := G.isGaussian
    have hmem : MemLp (id : EnergySpace α → EnergySpace α) 2 (P.map G.U) :=
      IsGaussian.memLp_two_id
    have hG' : IsGaussian (P.map (fun ω => -G.U ω)) := by rw [hmap]; infer_instance
    have hmem' : MemLp (id : EnergySpace α → EnergySpace α) 2 (P.map (fun ω => -G.U ω)) :=
      IsGaussian.memLp_two_id
    have hmean' : (∫ z : EnergySpace α, z ∂P.map (fun ω => -G.U ω)) = 0 := by
      rw [hmap, integral_map (f := fun x : EnergySpace α => x)
        (-ContinuousLinearMap.id ℝ _).continuous.measurable.aemeasurable
        measurable_id.aestronglyMeasurable,
        ContinuousLinearMap.integral_comp_comm (-ContinuousLinearMap.id ℝ _)
          (φ := fun x : EnergySpace α => x) (hmem.integrable (by norm_num)), G.mean0, map_zero]
    have hadj : ∀ v : EnergySpace α,
        (-ContinuousLinearMap.id ℝ (EnergySpace α)).adjoint v = -v := by
      intro v
      refine ext_inner_right ℝ fun u => ?_
      rw [ContinuousLinearMap.adjoint_inner_left]
      simp
    rw [← covarianceBilin_eq_inner_covarianceOperator hmem' hmean', hmap, covarianceBilin_map hmem,
      hadj, hadj, covarianceBilin_eq_inner_covarianceOperator hmem G.mean0, map_neg, inner_neg_left,
      inner_neg_right, neg_neg]
    exact G.cov_eq x y

@[simp] lemma GaussianField.neg_U (G : GaussianField (α := α) P K) (ω : Ω) :
    G.neg.U ω = -G.U ω := rfl

/-! ### The canonical field of a covariance matrix -/

omit [IsProbabilityMeasure P] [IsProbabilityMeasure Q] in
/-- The bilinear form of a matrix on Dirac vectors is its entry. -/
lemma dotProduct_std_basis_mulVec (S : Matrix α α ℝ) (x y : α) :
    (WithLp.ofLp (std_basis (α := α) x)) ⬝ᵥ S *ᵥ (WithLp.ofLp (std_basis (α := α) y)) = S x y := by
  classical
  simp only [dotProduct, mulVec, std_basis, WithLp.ofLp_toLp]
  rw [Finset.sum_eq_single x]
  · simp only [ite_true, one_mul]
    rw [Finset.sum_eq_single y]
    · simp
    · intro τ _ hτ
      simp [Ne.symm hτ]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro σ _ hσ
    simp [Ne.symm hσ]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The canonical Gaussian field of a positive semidefinite matrix**: the identity on
`EnergySpace α` under `N(0, S)` is a centered Gaussian field with kernel `S`. -/
def GaussianField.ofMultivariateGaussian [DecidableEq α] {S : Matrix α α ℝ} (hS : S.PosSemidef) :
    GaussianField (α := α) (multivariateGaussian (0 : EuclideanSpace ℝ α) S)
      (fun x y => S x y) where
  U := id
  measU := measurable_id
  hU := IsGaussian.hasGaussianLaw_id
  mean0 := by
    rw [Measure.map_id]
    exact integral_id_multivariateGaussian
  cov_eq := fun x y => by
    rw [Measure.map_id, inner_covarianceOperator_multivariateGaussian hS,
      dotProduct_std_basis_mulVec]

end

end FiniteGibbs

end SpinGlass
