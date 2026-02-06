import SpinGlass.FiniteGibbs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Calculus for `SpinGlass.FiniteGibbs`

This file adds the **smoothness / chain rule / derivative bounds** needed to use the generic
finite-volume Gibbs calculus (`SpinGlass.FiniteGibbs`) as a backend for Talagrand-style
interpolation arguments.

In particular we provide:

- `C^∞` regularity of `Z`, `gibbs_pmf`, and `free_energy_density`;
- a convenient chain rule lemma for `t ↦ free_energy_density n (H t)`;
- a uniform bound on the directional derivative of `free_energy_density`.
-/

open Real BigOperators Filter Topology
open scoped ContDiff

namespace SpinGlass

namespace FiniteGibbs

noncomputable section

variable {α : Type*} [Fintype α] [Nonempty α]

omit [Nonempty α] in
lemma abs_apply_le_norm (H : EnergySpace α) (σ : α) : |H σ| ≤ ‖H‖ := by
  simpa [Real.norm_eq_abs] using
    (PiLp.norm_apply_le (p := (2 : ENNReal)) (x := H) σ)

omit [Nonempty α] in
/-- `Z` is smooth (`C^∞`) as a finite sum of exponentials of linear forms. -/
lemma contDiff_Z : ContDiff ℝ (∞) (fun H : EnergySpace α => Z (α := α) H) := by
  have hterm :
      ∀ σ : α, ContDiff ℝ (∞) (fun H : EnergySpace α => Real.exp (-H σ)) := by
    intro σ
    simpa using (contDiff_exp.comp (contDiff_neg.comp (evalCLM (α := α) σ).contDiff))
  simpa [Z] using
    (ContDiff.sum (𝕜 := ℝ) (n := (∞)) (s := (Finset.univ : Finset α))
      (f := fun σ : α => fun H : EnergySpace α => Real.exp (-H σ))
      (fun σ _hσ => hterm σ))

/-- `gibbs_pmf` is smooth (`C^∞`) as a quotient of smooth functions, since `Z(H) ≠ 0`. -/
lemma contDiff_gibbs_pmf (σ : α) :
    ContDiff ℝ (∞) (fun H : EnergySpace α => gibbs_pmf (α := α) H σ) := by
  have hnum :
      ContDiff ℝ (∞) (fun H : EnergySpace α => Real.exp (-H σ)) := by
    simpa using (contDiff_exp.comp (contDiff_neg.comp (evalCLM (α := α) σ).contDiff))
  have hZ : ContDiff ℝ (∞) (fun H : EnergySpace α => Z (α := α) H) :=
    contDiff_Z (α := α)
  have hZne : ∀ H : EnergySpace α, Z (α := α) H ≠ 0 := fun H =>
    (Z_pos (α := α) (H := H)).ne'
  simpa [gibbs_pmf] using hnum.div hZ hZne

/-- The free energy density `H ↦ (1/n) * log (Z H)` is smooth. -/
lemma contDiff_free_energy_density (n : ℕ) :
    ContDiff ℝ (∞) (fun H : EnergySpace α => free_energy_density (α := α) n H) := by
  have hZ : ContDiff ℝ (∞) (fun H : EnergySpace α => Z (α := α) H) :=
    contDiff_Z (α := α)
  have hlog : ContDiff ℝ (∞) (fun H : EnergySpace α => Real.log (Z (α := α) H)) :=
    (hZ.log (fun H => (Z_ne_zero (α := α) (H := H))))
  simpa [free_energy_density, smul_eq_mul, mul_assoc] using
    (ContDiff.const_smul (𝕜 := ℝ) (n := (∞)) (R := ℝ) (c := (1 / (n : ℝ))) hlog)

/--
Chain rule for the free energy density along a one-dimensional path `H : ℝ → EnergySpace α`.

This is the basic analytic input for Talagrand’s interpolation: differentiation of
`fun t ↦ free_energy_density n (H t)`.
-/
lemma hasDerivAt_free_energy_density_comp
    (n : ℕ) {H : ℝ → EnergySpace α} {H' : EnergySpace α} {t : ℝ}
    (hH : HasDerivAt H H' t) :
    HasDerivAt (fun s => free_energy_density (α := α) n (H s))
      (fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H) (H t) H') t := by
  have hdiff :
      DifferentiableAt ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H) (H t) := by
    have hdiff' :
        Differentiable ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H) :=
      (contDiff_free_energy_density (α := α) (n := n)).differentiable (by simp)
    exact hdiff' (H t)
  have hF :
      HasFDerivAt (fun H : EnergySpace α => free_energy_density (α := α) n H)
        (fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H) (H t)) (H t) :=
    hdiff.hasFDerivAt
  simpa using
    (HasFDerivAt.comp_hasDerivAt (x := t) (f := H)
      (l := fun H : EnergySpace α => free_energy_density (α := α) n H)
      (l' := fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H) (H t)) hF hH)

/--
Uniform bound on the directional derivative of the free energy density:
\[
|D F_n(H)[v]| \le \frac{1}{n} \|v\|.
\]

This is used as a dominated differentiation hypothesis in interpolation arguments.
-/
lemma abs_fderiv_free_energy_density_apply_le (n : ℕ) (H v : EnergySpace α) :
    |fderiv ℝ (fun H' : EnergySpace α => free_energy_density (α := α) n H') H v|
      ≤ (1 / (n : ℝ)) * ‖v‖ := by
  have hsum1 : (∑ σ : α, gibbs_pmf (α := α) H σ) = 1 :=
    sum_gibbs_pmf (α := α) (H := H)
  have hv_point : ∀ σ : α, |v σ| ≤ ‖v‖ := fun σ =>
    (abs_apply_le_norm (α := α) v σ)
  have hmain :
      |∑ σ : α, gibbs_pmf (α := α) H σ * v σ| ≤ ‖v‖ := by

    calc
      |∑ σ : α, gibbs_pmf (α := α) H σ * v σ|
          ≤ ∑ σ : α, |gibbs_pmf (α := α) H σ * v σ| := by
              simpa using
                (Finset.abs_sum_le_sum_abs
                  (f := fun σ : α => gibbs_pmf (α := α) H σ * v σ)
                  (s := (Finset.univ : Finset α)))
      _ = ∑ σ : α, gibbs_pmf (α := α) H σ * |v σ| := by
            refine Finset.sum_congr rfl (fun σ _hσ => ?_)
            have hp : 0 ≤ gibbs_pmf (α := α) H σ :=
              gibbs_pmf_nonneg (α := α) (H := H) (σ := σ)
            simp [abs_mul, abs_of_nonneg hp, mul_assoc]
      _ ≤ ∑ σ : α, gibbs_pmf (α := α) H σ * ‖v‖ := by
            refine Finset.sum_le_sum (fun σ _hσ => ?_)
            have hp : 0 ≤ gibbs_pmf (α := α) H σ :=
              gibbs_pmf_nonneg (α := α) (H := H) (σ := σ)
            exact mul_le_mul_of_nonneg_left (hv_point σ) hp
      _ = (∑ σ : α, gibbs_pmf (α := α) H σ) * ‖v‖ := by
            simpa using
              (Finset.sum_mul (s := (Finset.univ : Finset α))
                (f := fun σ : α => gibbs_pmf (α := α) H σ) (a := ‖v‖)).symm
      _ = ‖v‖ := by simp [hsum1]
  have hfderiv :
      fderiv ℝ (fun H' : EnergySpace α => free_energy_density (α := α) n H') H v
        = -(1 / (n : ℝ)) * ∑ σ : α, (gibbs_pmf (α := α) H σ) * v σ :=
    fderiv_free_energy_density_apply (α := α) (n := n) (H := H) (h := v)
  calc
    |fderiv ℝ (fun H' : EnergySpace α => free_energy_density (α := α) n H') H v|
        = |-(1 / (n : ℝ)) * ∑ σ : α, (gibbs_pmf (α := α) H σ) * v σ| := by
            simpa [hfderiv]
    _ = (1 / (n : ℝ)) * |∑ σ : α, (gibbs_pmf (α := α) H σ) * v σ| := by
            simp [abs_mul]
    _ ≤ (1 / (n : ℝ)) * ‖v‖ := by
            exact mul_le_mul_of_nonneg_left hmain (by positivity)

lemma norm_fderiv_free_energy_density_le (n : ℕ) (H : EnergySpace α) :
    ‖fderiv ℝ (fun H' : EnergySpace α => free_energy_density (α := α) n H') H‖ ≤ (1 / (n : ℝ)) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  have habs :=
    abs_fderiv_free_energy_density_apply_le (α := α) (n := n) (H := H) (v := v)
  simpa [Real.norm_eq_abs] using habs

/--
Global Lipschitz bound for the free energy density:
\[
|F_n(H₂) - F_n(H₁)| \le \frac{1}{n}\,\|H₂ - H₁\|.
\]

This is the key regularity input for Gaussian concentration (and a useful shortcut in analytic
interpolation arguments).
-/
lemma abs_free_energy_density_sub_le (n : ℕ) (H₁ H₂ : EnergySpace α) :
    |free_energy_density (α := α) n H₂ - free_energy_density (α := α) n H₁|
      ≤ (1 / (n : ℝ)) * ‖H₂ - H₁‖ := by
  have hdiff :
      ∀ x : EnergySpace α,
        DifferentiableAt ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H) x := by
    intro x
    have : Differentiable ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H) :=
      (contDiff_free_energy_density (α := α) (n := n)).differentiable (by simp)
    exact this x
  have hbound :
      ∀ x : EnergySpace α, ‖fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H) x‖ ≤
        (1 / (n : ℝ)) := fun x => norm_fderiv_free_energy_density_le (α := α) (n := n) x
  have hmv :=
    (Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (f := fun H : EnergySpace α => free_energy_density (α := α) n H)
      (s := (Set.univ : Set (EnergySpace α))) (x := H₁) (y := H₂)
      (hf := fun x _hx => hdiff x)
      (bound := fun x _hx => hbound x) (hs := convex_univ) (xs := by trivial) (ys := by trivial))
  simpa [Real.norm_eq_abs] using hmv

/-! ### Growth bounds for `Z` and `free_energy_density` -/

omit [Nonempty α] in
lemma Z_le_card_mul_exp_norm (H : EnergySpace α) :
    Z (α := α) H ≤ (Fintype.card α : ℝ) * Real.exp (‖H‖) := by
  have hterm : ∀ σ : α, Real.exp (-H σ) ≤ Real.exp (‖H‖) := by
    intro σ
    have hlin : -H σ ≤ ‖H‖ :=
      (neg_le_abs (H σ)).trans (abs_apply_le_norm (α := α) H σ)
    simpa using (Real.exp_le_exp.2 hlin)
  simpa [Z] using
    (calc
      (∑ σ : α, Real.exp (-H σ)) ≤ ∑ σ : α, Real.exp (‖H‖) := by
        simpa using (Finset.sum_le_sum (s := (Finset.univ : Finset α)) (fun σ _hσ => hterm σ))
      _ = (Fintype.card α : ℝ) * Real.exp (‖H‖) := by
        simp)

lemma Z_ge_exp_neg_norm (H : EnergySpace α) :
    Real.exp (-‖H‖) ≤ Z (α := α) H := by
  let σ₀ : α := Classical.choice (‹Nonempty α›)
  have hlin0 : H σ₀ ≤ ‖H‖ :=
    (le_abs_self (H σ₀)).trans (abs_apply_le_norm (α := α) H σ₀)
  have hlin : -‖H‖ ≤ -H σ₀ := by simpa using (neg_le_neg hlin0)
  have hexp : Real.exp (-‖H‖) ≤ Real.exp (-H σ₀) := by
    simpa using (Real.exp_le_exp.2 hlin)
  have hterm_le_Z : Real.exp (-H σ₀) ≤ Z (α := α) H := by
    have hnonneg : ∀ σ : α, 0 ≤ Real.exp (-H σ) := fun σ => (Real.exp_pos _).le
    have :
        Real.exp (-H σ₀) ≤
          ∑ σ ∈ (Finset.univ : Finset α), Real.exp (-H σ) := by
      exact Finset.single_le_sum (fun σ _hσ => hnonneg σ) (Finset.mem_univ σ₀)
    simpa [Z] using this
  exact le_trans hexp hterm_le_Z

lemma log_card_nonneg : 0 ≤ Real.log (Fintype.card α : ℝ) := by
  have hcard_pos : 0 < Fintype.card α := Fintype.card_pos
  have h1le : (1 : ℝ) ≤ (Fintype.card α : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.2 hcard_pos)
  exact Real.log_nonneg h1le

lemma logZ_le_log_card_add_norm (H : EnergySpace α) :
    Real.log (Z (α := α) H) ≤ Real.log (Fintype.card α : ℝ) + ‖H‖ := by
  have hZpos : 0 < Z (α := α) H := Z_pos (α := α) (H := H)
  have hZ_le : Z (α := α) H ≤ (Fintype.card α : ℝ) * Real.exp (‖H‖) :=
    Z_le_card_mul_exp_norm (α := α) H
  have hlog_le :
      Real.log (Z (α := α) H) ≤ Real.log ((Fintype.card α : ℝ) * Real.exp (‖H‖)) :=
    Real.log_le_log hZpos hZ_le
  have hcard_ne : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos (α := α)))
  have hexp_ne : Real.exp (‖H‖) ≠ 0 := Real.exp_ne_zero _
  simpa [Real.log_mul hcard_ne hexp_ne, Real.log_exp] using hlog_le

lemma logZ_ge_neg_log_card_add_norm (H : EnergySpace α) :
    -(Real.log (Fintype.card α : ℝ) + ‖H‖) ≤ Real.log (Z (α := α) H) := by
  have h1 : -‖H‖ ≤ Real.log (Z (α := α) H) := by
    have hexp_pos : 0 < Real.exp (-‖H‖) := Real.exp_pos _
    have hZpos : 0 < Z (α := α) H := Z_pos (α := α) (H := H)
    have hlog_le : Real.log (Real.exp (-‖H‖)) ≤ Real.log (Z (α := α) H) :=
      Real.log_le_log hexp_pos (le_trans (Z_ge_exp_neg_norm (α := α) (H := H)) (le_rfl))
    simpa using hlog_le
  have h2 : -(Real.log (Fintype.card α : ℝ) + ‖H‖) ≤ -‖H‖ := by
    nlinarith [log_card_nonneg (α := α)]
  exact le_trans h2 h1

lemma abs_logZ_le_log_card_add_norm (H : EnergySpace α) :
    |Real.log (Z (α := α) H)| ≤ Real.log (Fintype.card α : ℝ) + ‖H‖ :=
  (abs_le.2 ⟨logZ_ge_neg_log_card_add_norm (α := α) (H := H),
    logZ_le_log_card_add_norm (α := α) (H := H)⟩)

lemma abs_free_energy_density_le (n : ℕ) (H : EnergySpace α) :
    |free_energy_density (α := α) n H|
      ≤ (Real.log (Fintype.card α) + 1) * (1 + ‖H‖) := by
  let C : ℝ := Real.log (Fintype.card α) + 1
  have hone_div_le : (1 / (n : ℝ)) ≤ 1 := by
    cases n with
    | zero => simp
    | succ m =>
        have : (1 : ℝ) ≤ (Nat.succ m : ℝ) := by exact_mod_cast (Nat.succ_pos m)
        simpa [one_div] using (one_div_le_one_div_of_le (by linarith) this)
  have habs_log : |Real.log (Z (α := α) H)| ≤ Real.log (Fintype.card α : ℝ) + ‖H‖ :=
    abs_logZ_le_log_card_add_norm (α := α) (H := H)
  have hscale :
      |free_energy_density (α := α) n H|
        ≤ (1 / (n : ℝ)) * (Real.log (Fintype.card α : ℝ) + ‖H‖) := by
    calc
      |free_energy_density (α := α) n H|
          = |(1 / (n : ℝ)) * Real.log (Z (α := α) H)| := by
              simp [free_energy_density]
      _ = (1 / (n : ℝ)) * |Real.log (Z (α := α) H)| := by
            simp [abs_mul]
      _ ≤ (1 / (n : ℝ)) * (Real.log (Fintype.card α : ℝ) + ‖H‖) := by
            exact mul_le_mul_of_nonneg_left habs_log (by positivity)
  have hpoly :
      (1 / (n : ℝ)) * (Real.log (Fintype.card α : ℝ) + ‖H‖) ≤ C * (1 + ‖H‖) := by
    have : (1 / (n : ℝ)) * (Real.log (Fintype.card α : ℝ) + ‖H‖)
          ≤ 1 * (Real.log (Fintype.card α : ℝ) + ‖H‖) := by
          gcongr
    have : (1 / (n : ℝ)) * (Real.log (Fintype.card α : ℝ) + ‖H‖)
          ≤ (Real.log (Fintype.card α : ℝ) + ‖H‖) := by simpa using this
    have haux : (Real.log (Fintype.card α : ℝ) + ‖H‖) ≤ C * (1 + ‖H‖) := by
      have ha : 0 ≤ Real.log (Fintype.card α : ℝ) := log_card_nonneg (α := α)
      have hx : 0 ≤ ‖H‖ := norm_nonneg H
      have : Real.log (Fintype.card α : ℝ) + ‖H‖ ≤ (Real.log (Fintype.card α : ℝ) + 1) * (1 + ‖H‖) := by
        nlinarith [ha, hx]
      simpa [C, add_assoc, add_left_comm, add_comm] using this
    exact le_trans this haux
  exact le_trans hscale hpoly

end

end FiniteGibbs

end SpinGlass
