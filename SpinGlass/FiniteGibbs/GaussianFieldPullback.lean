/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.FiniteGibbs.GaussianInterpolation
import Common.Mathlib.Probability.Distributions.Gaussian.MultivariateCovariance

/-!
# Pulling back a Gaussian field along a map of state spaces

For a map `f : β → α` of finite state spaces, a Hamiltonian `H` on `α` pulls back to `H ∘ f` on
`β` (`pullbackCLM f`, a continuous linear map of the energy spaces), and a centered Gaussian field
with kernel `K` on `α` pulls back to one with kernel `K (f x) (f y)` on `β`
(`GaussianField.comp`). Two instances matter for Guerra's broken replica-symmetry bound
(Talagrand, Vol. II, §14.4): the lift of the model's Hamiltonian `H_N(σ)` to the state space
`Σ_N × A` of configurations and branches (`f = Prod.fst`), and the restriction of a field to the
support of a family of weights (`f = Subtype.val`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace SpinGlass

namespace FiniteGibbs

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### The pullback of Hamiltonians -/

/-- Pulling back a Hamiltonian along `f : β → α`, as a continuous linear map of energy spaces. -/
def pullbackCLM (f : β → α) : EnergySpace α →L[ℝ] EnergySpace β :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ (β → ℝ)).symm.toLinearMap ∘ₗ LinearMap.funLeft ℝ ℝ f ∘ₗ
      (WithLp.linearEquiv 2 ℝ (α → ℝ)).toLinearMap)

@[simp] lemma pullbackCLM_apply (f : β → α) (H : EnergySpace α) (x : β) :
    pullbackCLM f H x = H (f x) := rfl

lemma pullbackCLM_add_apply (f : β → α) (H c : EnergySpace α) :
    pullbackCLM f (H + c) = pullbackCLM f H + pullbackCLM f c := map_add _ _ _

/-- The adjoint of the pullback sends the Dirac vector `e_x` to `e_{f x}`. -/
lemma adjoint_pullbackCLM_std_basis (f : β → α) (x : β) :
    (pullbackCLM f).adjoint (std_basis (α := β) x) = std_basis (α := α) (f x) := by
  refine ext_inner_right ℝ fun u => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, inner_std_basis_apply, inner_std_basis_apply,
    pullbackCLM_apply]

/-! ### The image of a Gaussian field under a linear map -/

omit [Fintype β] in
/-- Expansion in the Dirac basis: `x = ∑_a x_a e_a`. -/
lemma sum_smul_std_basis (x : EnergySpace α) : ∑ a, x a • std_basis (α := α) a = x := by
  classical
  ext b
  simp [std_basis, Finset.sum_apply]

omit [Fintype β] in
/-- `∑_a (e_c)_a g_a = g_c`. -/
lemma sum_std_basis_apply_mul (c : α) (g : α → ℝ) : ∑ a, std_basis (α := α) c a * g a = g c := by
  classical
  rw [Finset.sum_eq_single c]
  · simp
  · intro a _ ha
    simp [std_basis_apply_of_ne (Ne.symm ha)]
  · intro h
    exact absurd (Finset.mem_univ _) h

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {K : α → α → ℝ}

omit [Fintype β] in
/-- The covariance form of a Gaussian field on arbitrary vectors, from its kernel:
`⟪Cov u, v⟫ = ∑_{a,b} u_a v_b K a b`. -/
lemma GaussianField.inner_covarianceOperator_eq_sum (G : GaussianField (α := α) P K)
    (u v : EnergySpace α) :
    inner ℝ (covarianceOperator (P.map G.U) u) v = ∑ a, ∑ b, u a * v b * K a b := by
  conv_lhs => rw [← sum_smul_std_basis u, ← sum_smul_std_basis v]
  simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, G.cov_eq]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- **The image of a Gaussian field under a continuous linear map** `T` of energy spaces: the
field `ω ↦ T (U ω)`, with kernel `⟪Cov (T† e_x), T† e_y⟫ = ∑_{a,b} (T†e_x)_a (T†e_y)_b K a b`.
Pullbacks (`GaussianField.comp`), fields from independent coordinates
(`GaussianField.ofCoords`) and sums of pullbacks are all instances. -/
def GaussianField.mapCLM (G : GaussianField (α := α) P K)
    (T : EnergySpace α →L[ℝ] EnergySpace β) :
    GaussianField (α := β) P (fun x y => ∑ a, ∑ b,
      T.adjoint (std_basis (α := β) x) a * T.adjoint (std_basis (α := β) y) b * K a b) where
  U := fun ω => T (G.U ω)
  measU := T.continuous.measurable.comp G.measU
  hU := G.hU.map_fun T
  mean0 := by
    have hmeas : Measurable fun ω => T (G.U ω) := T.continuous.measurable.comp G.measU
    rw [integral_map (f := fun x : EnergySpace β => x) hmeas.aemeasurable
      measurable_id.aestronglyMeasurable,
      ContinuousLinearMap.integral_comp_comm _ G.integrable, G.integral_eq_zero, map_zero]
  cov_eq := fun x y => by
    have hG : IsGaussian (P.map G.U) := G.isGaussian
    have hmem : MemLp (id : EnergySpace α → EnergySpace α) 2 (P.map G.U) :=
      IsGaussian.memLp_two_id
    have hmap : P.map (fun ω => T (G.U ω)) = (P.map G.U).map T := by
      rw [Measure.map_map T.continuous.measurable G.measU]
      rfl
    have hG' : IsGaussian (P.map (fun ω => T (G.U ω))) := by
      rw [hmap]; infer_instance
    have hmem' : MemLp (id : EnergySpace β → EnergySpace β) 2
        (P.map (fun ω => T (G.U ω))) := IsGaussian.memLp_two_id
    have hmean' : (∫ z : EnergySpace β, z ∂P.map (fun ω => T (G.U ω))) = 0 := by
      rw [hmap, integral_map (f := fun x : EnergySpace β => x)
        T.continuous.measurable.aemeasurable measurable_id.aestronglyMeasurable,
        ContinuousLinearMap.integral_comp_comm T (φ := fun x : EnergySpace α => x)
          (hmem.integrable (by norm_num)), G.mean0, map_zero]
    rw [← covarianceBilin_eq_inner_covarianceOperator hmem' hmean', hmap,
      covarianceBilin_map hmem, covarianceBilin_eq_inner_covarianceOperator hmem G.mean0,
      G.inner_covarianceOperator_eq_sum]

@[simp] lemma GaussianField.mapCLM_U (G : GaussianField (α := α) P K)
    (T : EnergySpace α →L[ℝ] EnergySpace β) (ω : Ω) : (G.mapCLM T).U ω = T (G.U ω) := rfl

/-- Transporting a Gaussian field along an equality of kernels. -/
def GaussianField.copy (G : GaussianField (α := α) P K) (K' : α → α → ℝ)
    (h : ∀ x y, K' x y = K x y) : GaussianField (α := α) P K' :=
  { G with cov_eq := fun x y => (G.cov_eq x y).trans (h x y).symm }

@[simp] lemma GaussianField.copy_U (G : GaussianField (α := α) P K) (K' : α → α → ℝ)
    (h : ∀ x y, K' x y = K x y) : (G.copy K' h).U = G.U := rfl

omit [Fintype β] in
/-- The kernel of `mapCLM` on a pair of Dirac vectors: `∑_{a,b} (e_c)_a (e_d)_b K a b = K c d`. -/
lemma sum_sum_std_basis_mul_std_basis_mul (c d : α) (K : α → α → ℝ) :
    ∑ a, ∑ b, std_basis (α := α) c a * std_basis (α := α) d b * K a b = K c d :=
  calc ∑ a, ∑ b, std_basis (α := α) c a * std_basis (α := α) d b * K a b
      = ∑ a, std_basis (α := α) c a * ∑ b, std_basis (α := α) d b * K a b := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
    _ = ∑ a, std_basis (α := α) c a * K a d := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [sum_std_basis_apply_mul d (fun b => K a b)]
    _ = K c d := sum_std_basis_apply_mul c (fun a => K a d)

/-! ### The pullback of Gaussian fields -/

/-- **The pullback of a Gaussian field** along `f : β → α`: the field `ω ↦ U ω ∘ f`, with kernel
`K (f x) (f y)` — the image under `pullbackCLM f`, whose adjoint sends `e_x` to `e_{f x}`. -/
def GaussianField.comp (G : GaussianField (α := α) P K) (f : β → α) :
    GaussianField (α := β) P (fun x y => K (f x) (f y)) :=
  (G.mapCLM (pullbackCLM f)).copy _ fun x y => by
    simp only [adjoint_pullbackCLM_std_basis]
    exact (sum_sum_std_basis_mul_std_basis_mul (f x) (f y) K).symm

@[simp] lemma GaussianField.comp_U (G : GaussianField (α := α) P K) (f : β → α) (ω : Ω) (x : β) :
    (G.comp f).U ω x = G.U ω (f x) := rfl

/-- Independence is preserved by pulling back. -/
lemma GaussianField.comp_indepFun {K₁ K₂ : α → α → ℝ} {G₁ : GaussianField (α := α) P K₁}
    {G₂ : GaussianField (α := α) P K₂} (hindep : G₁.U ⟂ᵢ[P] G₂.U) (f g : β → α) :
    (G₁.comp f).U ⟂ᵢ[P] (G₂.comp g).U :=
  hindep.comp (pullbackCLM f).continuous.measurable (pullbackCLM g).continuous.measurable

end

end FiniteGibbs

end SpinGlass
