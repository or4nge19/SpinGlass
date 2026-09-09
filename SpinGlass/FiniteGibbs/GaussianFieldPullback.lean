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

/-! ### The pullback of Gaussian fields -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {K : α → α → ℝ}

/-- **The pullback of a Gaussian field** along `f : β → α`: the field `ω ↦ U ω ∘ f`, with kernel
`K (f x) (f y)`. -/
def GaussianField.comp (G : GaussianField (α := α) P K) (f : β → α) :
    GaussianField (α := β) P (fun x y => K (f x) (f y)) where
  U := fun ω => pullbackCLM f (G.U ω)
  measU := (pullbackCLM f).continuous.measurable.comp G.measU
  hU := G.hU.map_fun (pullbackCLM f)
  mean0 := by
    have hmeas : Measurable fun ω => pullbackCLM f (G.U ω) :=
      (pullbackCLM f).continuous.measurable.comp G.measU
    rw [integral_map (f := fun x : EnergySpace β => x) hmeas.aemeasurable
      measurable_id.aestronglyMeasurable,
      ContinuousLinearMap.integral_comp_comm _ G.integrable, G.integral_eq_zero, map_zero]
  cov_eq := fun x y => by
    have hG : IsGaussian (P.map G.U) := G.isGaussian
    have hmem : MemLp (id : EnergySpace α → EnergySpace α) 2 (P.map G.U) :=
      IsGaussian.memLp_two_id
    have hmap : P.map (fun ω => pullbackCLM f (G.U ω)) = (P.map G.U).map (pullbackCLM f) := by
      rw [Measure.map_map (pullbackCLM f).continuous.measurable G.measU]
      rfl
    have hG' : IsGaussian (P.map (fun ω => pullbackCLM f (G.U ω))) := by
      rw [hmap]; infer_instance
    have hmem' : MemLp (id : EnergySpace β → EnergySpace β) 2
        (P.map (fun ω => pullbackCLM f (G.U ω))) := IsGaussian.memLp_two_id
    have hmean' : (∫ z : EnergySpace β, z ∂P.map (fun ω => pullbackCLM f (G.U ω))) = 0 := by
      rw [hmap, integral_map (f := fun x : EnergySpace β => x)
        (pullbackCLM f).continuous.measurable.aemeasurable measurable_id.aestronglyMeasurable,
        ContinuousLinearMap.integral_comp_comm (pullbackCLM f) (φ := fun x : EnergySpace α => x)
          (hmem.integrable (by norm_num)), G.mean0, map_zero]
    rw [← covarianceBilin_eq_inner_covarianceOperator hmem' hmean', hmap,
      covarianceBilin_map hmem, adjoint_pullbackCLM_std_basis, adjoint_pullbackCLM_std_basis,
      covarianceBilin_eq_inner_covarianceOperator hmem G.mean0]
    exact G.cov_eq (f x) (f y)

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
