import SpinGlass.FiniteGibbs.GibbsMeasure
import Mathlib.Data.Fintype.Prod

/-!
# Finite Gibbs marginalization (Boltzmann machines / RBMs)

This file provides a **finite-volume** lemma to integrate out hidden variables.

For a Gibbs law on a product space `α × β` with energy `H`, the `α`-marginal is again a Gibbs law,
with **effective energy**
\[
  H_{\mathrm{eff}}(a) := -\log \sum_{b} \exp(-H(a,b)).
\]

This is a possibe principled bridge between:

- Boltzmann machines / RBMs (joint Gibbs law on visible+hidden),
- Hopfield-type low-rank energies (visible marginal after Gaussian hidden integration),
- Talagrand’s Vol II viewpoint (kernels / pushforwards).
-/

open MeasureTheory Real BigOperators
open scoped ENNReal NNReal

namespace SpinGlass
namespace FiniteGibbs

noncomputable section

variable {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
variable [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace β] [MeasurableSingletonClass β]

/-! ## Effective energy obtained by summing out `β` -/

/-- The conditional partition function `a ↦ ∑ b, exp (-H (a,b))`. -/
noncomputable def condZ (H : EnergySpace (α × β)) (a : α) : ℝ :=
  ∑ b : β, Real.exp (-H (a, b))

lemma condZ_pos (H : EnergySpace (α × β)) (a : α) : 0 < condZ (α := α) (β := β) H a := by
  classical
  refine Finset.sum_pos ?_ Finset.univ_nonempty
  intro b _hb
  exact Real.exp_pos _

lemma condZ_ne_zero (H : EnergySpace (α × β)) (a : α) : condZ (α := α) (β := β) H a ≠ 0 :=
  (condZ_pos (α := α) (β := β) (H := H) a).ne'

/--
Effective (visible) energy obtained by summing out the `β` variable:

`H_eff a = - log (∑ b, exp (-H (a,b)))`.
-/
noncomputable def marginalEnergy (H : EnergySpace (α × β)) : EnergySpace α :=
  WithLp.toLp 2 (fun a : α => -Real.log (condZ (α := α) (β := β) H a))

lemma exp_neg_marginalEnergy (H : EnergySpace (α × β)) (a : α) :
    Real.exp (-(marginalEnergy (α := α) (β := β) H) a)
      = condZ (α := α) (β := β) H a := by
  have hpos : 0 < condZ (α := α) (β := β) H a :=
    condZ_pos (α := α) (β := β) (H := H) a
  simpa [marginalEnergy, condZ] using (Real.exp_log hpos)

/-! ## Partition function and pmf after marginalization -/

lemma Z_marginalEnergy (H : EnergySpace (α × β)) :
    Z (α := α) (marginalEnergy (α := α) (β := β) H) = Z (α := α × β) H := by
  simp [Z, exp_neg_marginalEnergy, condZ, Fintype.sum_prod_type]

lemma gibbs_pmf_marginalEnergy (H : EnergySpace (α × β)) (a : α) :
    gibbs_pmf (α := α) (marginalEnergy (α := α) (β := β) H) a
      =
      (∑ b : β, Real.exp (-H (a, b))) / Z (α := α × β) H := by
  simp [gibbs_pmf, Z_marginalEnergy, exp_neg_marginalEnergy, condZ]

lemma sum_gibbs_pmf_prod_eq_gibbs_pmf_marginalEnergy (H : EnergySpace (α × β)) (a : α) :
    (∑ b : β, gibbs_pmf (α := α × β) H (a, b))
      = gibbs_pmf (α := α) (marginalEnergy (α := α) (β := β) H) a := by
  have hZ : Z (α := α × β) H ≠ 0 := Z_ne_zero (α := α × β) (H := H)
  calc
    (∑ b : β, gibbs_pmf (α := α × β) H (a, b))
        = (∑ b : β, Real.exp (-H (a, b)) / Z (α := α × β) H) := by
            simp [gibbs_pmf]
    _ = (∑ b : β, Real.exp (-H (a, b)) * (Z (α := α × β) H)⁻¹) := by
          simp [div_eq_mul_inv]
    _ = (∑ b : β, Real.exp (-H (a, b))) * (Z (α := α × β) H)⁻¹ := by
          classical
          simpa [Finset.sum_mul] using
            (Finset.sum_mul (s := (Finset.univ : Finset β))
              (f := fun b : β => Real.exp (-H (a, b))) (a := (Z (α := α × β) H)⁻¹)).symm
    _ = (∑ b : β, Real.exp (-H (a, b))) / Z (α := α × β) H := by
          simp [div_eq_mul_inv, hZ]
    _ = gibbs_pmf (α := α) (marginalEnergy (α := α) (β := β) H) a := by
          simpa [gibbs_pmf_marginalEnergy]

/-! ## Measure-level marginalization lemma -/

/--
Marginalizing the Gibbs measure on `α × β` along `Prod.fst` yields the Gibbs measure on `α`
with the effective energy `marginalEnergy`.

This is the finite-volume “RBM visible marginal = Gibbs of log-sum-exp energy” statement.
-/
theorem map_fst_gibbsMeasure_eq_gibbsMeasure_marginalEnergy (H : EnergySpace (α × β)) :
    (gibbsMeasure (α := α × β) H).map Prod.fst
      =
      gibbsMeasure (α := α) (marginalEnergy (α := α) (β := β) H) := by
  classical
  refine Measure.ext (fun s hs => ?_)
  have hLHS :
      (gibbsMeasure (α := α × β) H).map Prod.fst s
        =
        ∑ a : α,
          (if a ∈ s then
              ∑ b : β, ENNReal.ofReal (gibbs_pmf (α := α × β) H (a, b))
            else 0) := by
    rw [Measure.map_apply measurable_fst hs]
    simp [FiniteGibbs.gibbsMeasure, hs, gibbsWeightNNReal_coe_ennreal, Fintype.sum_prod_type,
      Set.indicator, Pi.one_apply]
  have hRHS :
      gibbsMeasure (α := α) (marginalEnergy (α := α) (β := β) H) s
        =
        ∑ a : α, (if a ∈ s then ENNReal.ofReal
          (gibbs_pmf (α := α) (marginalEnergy (α := α) (β := β) H) a) else 0) := by
    simp [FiniteGibbs.gibbsMeasure, hs, gibbsWeightNNReal_coe_ennreal, Set.indicator, Pi.one_apply]
  have hsum_ofReal (a : α) :
      (∑ b : β, ENNReal.ofReal (gibbs_pmf (α := α × β) H (a, b)))
        =
        ENNReal.ofReal (gibbs_pmf (α := α) (marginalEnergy (α := α) (β := β) H) a) := by
    have hnonneg : ∀ b : β, 0 ≤ gibbs_pmf (α := α × β) H (a, b) := fun b =>
      gibbs_pmf_nonneg (α := α × β) (H := H) (a, b)
    rw [← ENNReal.ofReal_sum_of_nonneg (s := (Finset.univ : Finset β))
      (f := fun b : β => gibbs_pmf (α := α × β) H (a, b)) (by intro b _; exact hnonneg b)]
    simpa [sum_gibbs_pmf_prod_eq_gibbs_pmf_marginalEnergy (α := α) (β := β) (H := H) a]
  simp [hLHS, hRHS, hsum_ofReal]

end

end FiniteGibbs
end SpinGlass
