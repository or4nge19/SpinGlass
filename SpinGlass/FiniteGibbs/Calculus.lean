import SpinGlass.FiniteGibbs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Finite Gibbs calculus: smoothness

`C^∞` regularity of `Z`, `gibbs_pmf`, and `free_energy_density`; chain rule along `t ↦ H t`;
uniform bound on the directional derivative.
-/

open Real BigOperators Filter Topology
open scoped ContDiff

namespace SpinGlass

namespace FiniteGibbs

noncomputable section

variable {α : Type*} [Fintype α] [Nonempty α]

omit [Nonempty α] in
lemma abs_apply_le_norm (H : EnergySpace α) (σ : α) : |H σ| ≤ ‖H‖ :=
  Real.abs_apply_le_norm (ι := α) H σ

omit [Nonempty α] in
/-- `Z` is smooth (`C^∞`): it is `Real.expSum` precomposed with the negation. -/
lemma contDiff_Z : ContDiff ℝ (∞) (fun H : EnergySpace α => Z (α := α) H) :=
  (Real.contDiff_expSum (ι := α)).comp (negCLM (α := α)).contDiff

/-- `gibbs_pmf` is smooth (`C^∞`): it is `Real.softmax` precomposed with the negation. -/
lemma contDiff_gibbs_pmf (σ : α) :
    ContDiff ℝ (∞) (fun H : EnergySpace α => gibbs_pmf (α := α) H σ) :=
  (Real.contDiff_softmax (ι := α) σ).comp (negCLM (α := α)).contDiff

/-- The free energy density is smooth: it is `Real.logSumExp` precomposed with the negation,
rescaled. -/
lemma contDiff_free_energy_density (n : ℕ) :
    ContDiff ℝ (∞) (fun H : EnergySpace α => free_energy_density (α := α) n H) := by
  have hcomp : ContDiff ℝ (∞) (fun H : EnergySpace α => Real.logSumExp (-H)) :=
    (Real.contDiff_logSumExp (ι := α)).comp (negCLM (α := α)).contDiff
  simpa [free_energy_density_eq_logSumExp, smul_eq_mul] using
    (ContDiff.const_smul (𝕜 := ℝ) (n := (∞)) (R := ℝ) (c := (1 / (n : ℝ))) hcomp)

/-- Chain rule for `t ↦ free_energy_density n (H t)`. -/
lemma hasDerivAt_free_energy_density_comp
    (n : ℕ) {H : ℝ → EnergySpace α} {H' : EnergySpace α} {t : ℝ}
    (hH : HasDerivAt H H' t) :
    HasDerivAt (fun s => free_energy_density (α := α) n (H s))
      (fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H) (H t) H') t := by
  have hF : HasFDerivAt (fun H : EnergySpace α => free_energy_density (α := α) n H)
      (fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H) (H t)) (H t) :=
    (((contDiff_free_energy_density (α := α) (n := n)).differentiable (by simp)) (H t)).hasFDerivAt
  simpa [Function.comp_def] using (HasFDerivAt.comp_hasDerivAt (x := t) hF hH)

/-- `|D F_n(H)[v]| ≤ (1/n) ‖v‖`: the gradient is `1/n` times a probability average. -/
lemma abs_fderiv_free_energy_density_apply_le (n : ℕ) (H v : EnergySpace α) :
    |fderiv ℝ (fun H' : EnergySpace α => free_energy_density (α := α) n H') H v|
      ≤ (1 / (n : ℝ)) * ‖v‖ := by
  rw [fderiv_free_energy_density_apply, abs_mul, abs_neg,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))]
  gcongr
  simpa [gibbs_pmf_eq_softmax] using Real.abs_sum_softmax_mul_le (-H) v

lemma norm_fderiv_free_energy_density_le (n : ℕ) (H : EnergySpace α) :
    ‖fderiv ℝ (fun H' : EnergySpace α => free_energy_density (α := α) n H') H‖
      ≤ (1 / (n : ℝ)) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  simpa [Real.norm_eq_abs] using
    abs_fderiv_free_energy_density_apply_le (α := α) (n := n) (H := H) (v := v)

/-! ### Growth bound -/

lemma log_card_nonneg : 0 ≤ Real.log (Fintype.card α : ℝ) :=
  Real.log_nonneg (by exact_mod_cast Fintype.card_pos)

/-- `|F_n(H)| ≤ (log (card α) + 1) (1 + ‖H‖)`: affine growth of the free-energy density, from
the sandwich `max ≤ logSumExp ≤ max + log (card α)`. -/
lemma abs_free_energy_density_le (n : ℕ) (H : EnergySpace α) :
    |free_energy_density (α := α) n H|
      ≤ (Real.log (Fintype.card α) + 1) * (1 + ‖H‖) := by
  have hlog : 0 ≤ Real.log (Fintype.card α : ℝ) := log_card_nonneg (α := α)
  have hbase : |Real.logSumExp (-H)| ≤ Real.log (Fintype.card α : ℝ) + ‖H‖ := by
    simpa using Real.abs_logSumExp_le (-H)
  have hone_div_le : (1 / (n : ℝ)) ≤ 1 := by
    cases n with
    | zero => simp
    | succ m =>
        rw [div_le_one (by positivity)]
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero m)
  have hnn : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have hH : (0 : ℝ) ≤ ‖H‖ := norm_nonneg H
  calc |free_energy_density (α := α) n H|
      = (1 / (n : ℝ)) * |Real.logSumExp (-H)| := by
        rw [free_energy_density_eq_logSumExp, abs_mul, abs_of_nonneg hnn]
    _ ≤ 1 * (Real.log (Fintype.card α : ℝ) + ‖H‖) := by
        gcongr
    _ ≤ (Real.log (Fintype.card α) + 1) * (1 + ‖H‖) := by nlinarith

/-- `|F_n(H₂) - F_n(H₁)| ≤ (1/n) ‖H₂ - H₁‖`. -/
lemma abs_free_energy_density_sub_le (n : ℕ) (H₁ H₂ : EnergySpace α) :
    |free_energy_density (α := α) n H₂ - free_energy_density (α := α) n H₁|
      ≤ (1 / (n : ℝ)) * ‖H₂ - H₁‖ := by
  have hdiff : Differentiable ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H) :=
    (contDiff_free_energy_density (α := α) n).differentiable (by simp)
  have hbound : ∀ H : EnergySpace α,
      ‖fderiv ℝ (fun H' : EnergySpace α => free_energy_density (α := α) n H') H‖
        ≤ (1 / (n : ℝ)) := fun H => norm_fderiv_free_energy_density_le (α := α) n H
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := fun H : EnergySpace α =>
      free_energy_density (α := α) n H) (fun H _ => hdiff H)
    (fun H _ => by simpa using hbound H) (convex_univ) (Set.mem_univ H₁) (Set.mem_univ H₂)
  simpa [Real.norm_eq_abs, abs_sub_comm] using this

/-! ## Uniform bounds on the free-energy Hessian -/

/-- **Uniform bound on the free-energy Hessian as a bilinear form**: `|D²F_n(H)[h,k]| ≤ (2/n)
‖h‖ ‖k‖`, from the corresponding bound on the `softmax` covariance form. -/
lemma abs_hessian_free_energy_le (n : ℕ) (H : EnergySpace α) (h k : EnergySpace α) :
    |hessian_free_energy (α := α) n H h k| ≤ (2 / (n : ℝ)) * ‖h‖ * ‖k‖ := by
  rw [hessian_free_energy_eq_logSumExpHess, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))]
  have hb := Real.abs_logSumExpHess_le (-H) h k
  calc (1 / (n : ℝ)) * |Real.logSumExpHess (-H) h k|
      ≤ (1 / (n : ℝ)) * (2 * ‖h‖ * ‖k‖) := by
        gcongr
    _ = (2 / (n : ℝ)) * ‖h‖ * ‖k‖ := by ring

/-- **Uniform operator-norm bound on the second derivative of the free-energy density**:
`‖D²F_n(H)‖ ≤ 2/n`, uniformly in `H`. Together with `norm_fderiv_free_energy_density_le` this
supplies the polynomial-growth hypotheses (of degree `0`) needed by the second-order Gaussian
integration-by-parts formulae. -/
lemma norm_fderiv_fderiv_free_energy_density_le (n : ℕ) (H : EnergySpace α) :
    ‖fderiv ℝ (fderiv ℝ (fun H' : EnergySpace α => free_energy_density (α := α) n H')) H‖
      ≤ 2 / (n : ℝ) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun k => ?_
  rw [Real.norm_eq_abs,
    show ((fderiv ℝ (fderiv ℝ (fun H' : EnergySpace α =>
        free_energy_density (α := α) n H')) H) h) k
      = hessian_free_energy (α := α) n H h k from
      hessian_free_energy_fderiv_eq_hessian_free_energy (α := α) n H h k]
  simpa [mul_assoc] using abs_hessian_free_energy_le (α := α) n H h k

end

end FiniteGibbs

end SpinGlass
