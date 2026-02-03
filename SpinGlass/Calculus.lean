import SpinGlass.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Common.Mathlib.Probability.Distributions.Gaussian.IntegrationByParts

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology

open scoped ContDiff
open scoped ProbabilityTheory

namespace SpinGlass

variable {N : ℕ}

/-!
## Calculus bridge for the free energy (Talagrand)

This file packages the **calculus layer** needed to connect:

- the *abstract* Fréchet-derivative API used by the Gaussian IBP library; and
- the *explicit* Gibbs-average / covariance formulas used in the SK algebra.

The key statement is `hessian_free_energy_eq_variance`, asserting that the (abstract)
Hessian of the free energy density is exactly the Gibbs covariance bilinear form.

### References
- M. Talagrand, *Mean Field Models for Spin Glasses*, Vol. I, Ch. 1, §1.3 (differentiation of
  \(\log Z\) and the Gibbs covariance/Hessian identity used in the Guerra interpolation).
-/

section Derivatives

/-!
### Smoothness of the partition function and free energy

These are the (finite-dimensional) smoothness facts used to justify the Fréchet derivatives.
They correspond to standard computations in Talagrand’s Appendix on differentiation of
the free energy functional.
-/

/--
`Z` is smooth (`C^∞`) as a finite sum of exponentials of linear forms.

This is the finite-volume regularity input behind Talagrand’s differentiation of the free energy
functional (Vol. I, Ch. 1, §1.3).
-/
lemma contDiff_Z (N : ℕ) : ContDiff ℝ (∞) (fun H : EnergySpace N => Z N H) := by
  classical
  -- `Z(H) = ∑σ exp(-H σ)`. Each summand is smooth and the index set is finite.
  have hterm :
      ∀ σ : Config N, ContDiff ℝ (∞) (fun H : EnergySpace N => Real.exp (-H σ)) := by
    intro σ
    -- `H ↦ H σ` is smooth (continuous linear), so `H ↦ exp(-H σ)` is smooth by composition.
    simpa using (contDiff_exp.comp (contDiff_neg.comp (evalCLM (N := N) σ).contDiff))
  simpa [Z] using
    (ContDiff.sum (𝕜 := ℝ) (n := (∞))
      (s := (Finset.univ : Finset (Config N)))
      (f := fun σ : Config N => fun H : EnergySpace N => Real.exp (-H σ))
      (fun σ hσ => hterm σ))

/--
`gibbs_pmf` is smooth (`C^∞`) as a quotient of smooth functions, since `Z(H) ≠ 0`.
-/
lemma contDiff_gibbs_pmf (N : ℕ) (σ : Config N) :
    ContDiff ℝ (∞) (fun H : EnergySpace N => gibbs_pmf N H σ) := by
  classical
  have hnum :
      ContDiff ℝ (∞) (fun H : EnergySpace N => Real.exp (-H σ)) := by
    simpa using (contDiff_exp.comp (contDiff_neg.comp (evalCLM (N := N) σ).contDiff))
  have hZ : ContDiff ℝ (∞) (fun H : EnergySpace N => Z N H) := contDiff_Z (N := N)
  have hZne : ∀ H : EnergySpace N, Z N H ≠ 0 := fun H =>
    (Z_pos (N := N) (H := H)).ne'
  simpa [gibbs_pmf] using hnum.div hZ hZne

/--
`Z(H) > 0` for every Hamiltonian `H`.

This is the positivity condition needed to differentiate `log (Z H)` (as in Talagrand, Vol. I,
Ch. 1, §1.3).
-/
lemma Z_pos_everywhere (H : EnergySpace N) : 0 < Z N H :=
  Z_pos (N := N) (H := H)

/--
The free energy density `H ↦ (1/N) log Z(H)` is smooth.

Reference: Talagrand, Vol. I, Ch. 1, §1.3 (differentiation of the free energy).
-/
lemma contDiff_free_energy_density (N : ℕ) :
    ContDiff ℝ (∞) (fun H : EnergySpace N => free_energy_density (N := N) H) := by
  classical
  have hZ : ContDiff ℝ (∞) (fun H : EnergySpace N => Z N H) := contDiff_Z (N := N)
  have hlog : ContDiff ℝ (∞) (fun H : EnergySpace N => Real.log (Z N H)) :=
    (hZ.log (fun H => (Z_pos_everywhere (N := N) (H := H)).ne'))
  simpa [free_energy_density, smul_eq_mul, mul_assoc] using
    (ContDiff.const_smul (𝕜 := ℝ) (n := (∞)) (R := ℝ) (c := (1 / (N : ℝ))) hlog)

/-!
### First and second Fréchet derivatives (Talagrand: Gibbs averages and covariances)

These are the formal counterparts of the standard identities:

* \(D(\log Z)(h) = -\langle h \rangle\),
* \(D^2(\log Z)(h,k) = \langle hk \rangle - \langle h \rangle \langle k \rangle\).
-/

/--
**First derivative of the free energy density.**

This is Talagrand’s “\(D\log Z = -\langle \cdot\rangle\)” identity for the Gibbs measure,
with the extra \(1/N\) normalization of the free energy density.

Reference: Talagrand, Vol. I, Ch. 1, §1.3 (first derivative of \(\log Z\)).
-/
lemma fderiv_free_energy_apply (H h : EnergySpace N) :
    fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H) H h =
      -(1 / (N : ℝ)) * ∑ σ : Config N, (gibbs_pmf N H σ) * h σ :=
  fderiv_free_energy_density_apply (N := N) (H := H) (h := h)

/--
**Second derivative / Hessian equals Gibbs covariance** (Talagrand).

This is the main “bridge” identity: the abstract Hessian (Fréchet second derivative)
agrees with the explicit Gibbs covariance formula.

In Talagrand’s notation, this is the identification of \(D^2 \log Z\) with the Gibbs
variance/covariance (used implicitly throughout the Guerra interpolation).

Reference: Talagrand, Vol. I, Ch. 1, §1.3 (second derivative of \(\log Z\) as a covariance).
-/
lemma hessian_free_energy_eq_variance (H h k : EnergySpace N) :
    (hessian_logZ (N := N) H) h k
      = (1 / (N : ℝ)) *
          ((∑ σ : Config N, gibbs_pmf N H σ * h σ * k σ) -
            (∑ σ : Config N, gibbs_pmf N H σ * h σ) * (∑ τ : Config N, gibbs_pmf N H τ * k τ)) := by
  simpa [gibbs_covariance, hessian_free_energy] using
    (hessian_eq_covariance (N := N) (H := H) (h := h) (k := k))

end Derivatives

/-!
### Moderate growth / integrability package (for Gaussian IBP)

For Gaussian inputs, we only need explicit polynomial-growth bounds on `free_energy_density` and
its Fréchet derivative. This is the Mathlib-idiomatic formulation used by the Cameron–Martin IBP.
-/

section GaussianIntegrability

open scoped BigOperators

variable (N)

lemma abs_apply_le_norm (H : EnergySpace N) (σ : Config N) : |H σ| ≤ ‖H‖ := by
  simpa [Real.norm_eq_abs] using
    (PiLp.norm_apply_le (p := (2 : ENNReal)) (x := H) σ)

lemma Z_le_card_mul_exp_norm (H : EnergySpace N) :
    Z N H ≤ (Fintype.card (Config N) : ℝ) * Real.exp (‖H‖) := by
  classical
  have hterm : ∀ σ : Config N, Real.exp (-H σ) ≤ Real.exp (‖H‖) := by
    intro σ
    have hlin : -H σ ≤ ‖H‖ :=
      (neg_le_abs (H σ)).trans (abs_apply_le_norm (N := N) H σ)
    simpa using (Real.exp_le_exp.2 hlin)
  simpa [Z] using
    (calc
      (∑ σ : Config N, Real.exp (-H σ))
          ≤ ∑ σ : Config N, Real.exp (‖H‖) := by
              simpa using
                (Finset.sum_le_sum (s := (Finset.univ : Finset (Config N)))
                  (fun σ _hσ => hterm σ))
      _ = (Fintype.card (Config N) : ℝ) * Real.exp (‖H‖) := by
            simp)

lemma Z_ge_exp_neg_norm (H : EnergySpace N) :
    Real.exp (-‖H‖) ≤ Z N H := by
  classical
  let σ₀ : Config N := fun _ => false
  have hlin0 : H σ₀ ≤ ‖H‖ :=
    (le_abs_self (H σ₀)).trans (abs_apply_le_norm (N := N) H σ₀)
  have hlin : -‖H‖ ≤ -H σ₀ := by
    simpa using (neg_le_neg hlin0)
  have hexp : Real.exp (-‖H‖) ≤ Real.exp (-H σ₀) := by
    simpa using (Real.exp_le_exp.2 hlin)
  have hterm_le_Z : Real.exp (-H σ₀) ≤ Z N H := by
    have hnonneg : ∀ σ : Config N, 0 ≤ Real.exp (-H σ) := fun σ => (Real.exp_pos _).le
    have :
        Real.exp (-H σ₀) ≤
          ∑ σ ∈ (Finset.univ : Finset (Config N)), Real.exp (-H σ) := by
      exact Finset.single_le_sum (fun σ _hσ => hnonneg σ) (Finset.mem_univ σ₀)
    simpa [Z] using this
  exact le_trans hexp hterm_le_Z

lemma abs_free_energy_density_le
    (H : EnergySpace N) :
    |free_energy_density (N := N) H|
      ≤ (Real.log (Fintype.card (Config N)) + 1) * (1 + ‖H‖) := by
  classical
  let C : ℝ := Real.log (Fintype.card (Config N)) + 1
  have hcard_pos : 0 < Fintype.card (Config N) := by
    classical
    have : Nonempty (Config N) := ⟨fun _ => false⟩
    exact Fintype.card_pos
  have hlog_nonneg : 0 ≤ Real.log (Fintype.card (Config N) : ℝ) := by
    have h1le : (1 : ℝ) ≤ (Fintype.card (Config N) : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.2 hcard_pos)
    exact Real.log_nonneg h1le
  have hZpos : 0 < Z N H := Z_pos (N := N) (H := H)
  have hZ_le := Z_le_card_mul_exp_norm (N := N) H
  have hZ_ge := Z_ge_exp_neg_norm (N := N) H
  have hlog_upper :
      Real.log (Z N H) ≤ Real.log (Fintype.card (Config N) : ℝ) + ‖H‖ := by
    have hlog_le :
        Real.log (Z N H) ≤ Real.log ((Fintype.card (Config N) : ℝ) * Real.exp (‖H‖)) :=
      Real.log_le_log hZpos hZ_le
    have hcard_ne : (Fintype.card (Config N) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hcard_pos)
    have : Real.log ((Fintype.card (Config N) : ℝ) * Real.exp (‖H‖))
          = Real.log (Fintype.card (Config N) : ℝ) + ‖H‖ := by
      have hexp_ne : Real.exp (‖H‖) ≠ 0 := Real.exp_ne_zero _
      calc
        Real.log ((Fintype.card (Config N) : ℝ) * Real.exp (‖H‖))
            = Real.log (Fintype.card (Config N) : ℝ) + Real.log (Real.exp (‖H‖)) := by
                simpa using (Real.log_mul hcard_ne hexp_ne)
        _ = Real.log (Fintype.card (Config N) : ℝ) + ‖H‖ := by
                rw [Real.log_exp]
    rw [this] at hlog_le
    exact hlog_le
  have hlog_lower : -(Real.log (Fintype.card (Config N) : ℝ) + ‖H‖) ≤ Real.log (Z N H) := by
    have h1 : -‖H‖ ≤ Real.log (Z N H) := by
      have hlog_le : Real.log (Real.exp (-‖H‖)) ≤ Real.log (Z N H) := by
        have hexp_pos : 0 < Real.exp (-‖H‖) := Real.exp_pos _
        exact Real.log_le_log hexp_pos hZ_ge
      simpa using hlog_le
    have h2 : -(Real.log (Fintype.card (Config N) : ℝ) + ‖H‖) ≤ -‖H‖ := by
      nlinarith [hlog_nonneg]
    exact le_trans h2 h1
  have habs_log :
      |Real.log (Z N H)| ≤ Real.log (Fintype.card (Config N) : ℝ) + ‖H‖ :=
    (abs_le.2 ⟨hlog_lower, hlog_upper⟩)
  have hone_div_le : (1 / (N : ℝ)) ≤ 1 := by
    cases N with
    | zero => simp
    | succ n =>
        have : (1 : ℝ) ≤ (Nat.succ n : ℝ) := by exact_mod_cast (Nat.succ_pos n)
        simpa [one_div] using (one_div_le_one_div_of_le (by linarith) this)
  have hscale :
      |free_energy_density (N := N) H|
        ≤ (1 / (N : ℝ)) * (Real.log (Fintype.card (Config N) : ℝ) + ‖H‖) := by
    have : |free_energy_density (N := N) H|
          = |(1 / (N : ℝ)) * Real.log (Z N H)| := by
              simp [free_energy_density]
    calc
      |free_energy_density (N := N) H|
          = |(1 / (N : ℝ)) * Real.log (Z N H)| := this
      _ = |(1 / (N : ℝ))| * |Real.log (Z N H)| := by simp [abs_mul]
      _ = (1 / (N : ℝ)) * |Real.log (Z N H)| := by simp
      _ ≤ (1 / (N : ℝ)) * (Real.log (Fintype.card (Config N) : ℝ) + ‖H‖) := by
            exact mul_le_mul_of_nonneg_left habs_log (by positivity)
  have hpoly :
      (1 / (N : ℝ)) * (Real.log (Fintype.card (Config N) : ℝ) + ‖H‖)
        ≤ C * (1 + ‖H‖) := by
    have h1 :
        (1 / (N : ℝ)) * (Real.log (Fintype.card (Config N) : ℝ) + ‖H‖)
          ≤ (Real.log (Fintype.card (Config N) : ℝ) + ‖H‖) := by
      have hnonneg : 0 ≤ (Real.log (Fintype.card (Config N) : ℝ) + ‖H‖) := by
        nlinarith [hlog_nonneg, norm_nonneg H]
      exact (mul_le_mul_of_nonneg_right hone_div_le hnonneg).trans_eq (by simp)
    have h2 :
        (Real.log (Fintype.card (Config N) : ℝ) + ‖H‖) ≤ C * (1 + ‖H‖) := by
      dsimp [C]
      nlinarith [hlog_nonneg, norm_nonneg H]
    exact le_trans h1 h2
  simpa [C] using le_trans hscale hpoly

/-! A convenient integrability corollary for Gaussian disorder. -/
lemma integrable_free_energy_density_of_isGaussian
    {Ω : Type*} [MeasureSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {g : Ω → EnergySpace N} (hg_meas : Measurable g)
    (hg_gauss : ProbabilityTheory.IsGaussian (P.map g)) :
    Integrable (fun w : Ω => free_energy_density (N := N) (g w)) P := by
  classical
  let μ : Measure (EnergySpace N) := P.map g
  haveI : ProbabilityTheory.IsGaussian μ := hg_gauss
  -- Integrability on the pushforward measure.
  have hInt_on_μ : Integrable (fun x : EnergySpace N => free_energy_density (N := N) x) μ := by
    -- linear growth bound + Gaussian moment finiteness
    let C : ℝ := Real.log (Fintype.card (Config N)) + 1
    have hbound : ∀ x, |free_energy_density (N := N) x| ≤ C * (1 + ‖x‖) := by
      intro x
      simpa [C] using (abs_free_energy_density_le (N := N) (H := x))
    have hpoly : Integrable (fun x : EnergySpace N => (1 + ‖x‖) ^ (1 : ℕ)) μ :=
      ProbabilityTheory.IsGaussian.integrable_one_add_norm_pow (μ := μ) 1
    have hdom : Integrable (fun x : EnergySpace N => C * (1 + ‖x‖) ^ (1 : ℕ)) μ :=
      hpoly.const_mul C
    refine hdom.mono' (by
      have : Measurable (fun x : EnergySpace N => free_energy_density (N := N) x) :=
        (contDiff_free_energy_density (N := N)).continuous.measurable
      exact this.aestronglyMeasurable)
      (ae_of_all _ (fun x => ?_))
    have hx := hbound x
    have hnonneg : 0 ≤ (C * (1 + ‖x‖) ^ (1 : ℕ)) := by positivity
    have : ‖free_energy_density (N := N) x‖ ≤ C * (1 + ‖x‖) ^ (1 : ℕ) := by
      simpa [Real.norm_eq_abs] using hx
    exact this
  -- Pull back along `g`.
  have hmeas : AEMeasurable g P := hg_meas.aemeasurable
  have hpull :=
    (integrable_map_measure (μ := P)
    (f := g) (g := fun x : EnergySpace N => free_energy_density (N := N) x)
    (by
      have : Measurable (fun x : EnergySpace N => free_energy_density (N := N) x) :=
        (contDiff_free_energy_density (N := N)).continuous.measurable
      exact this.aestronglyMeasurable)
    hmeas).1 hInt_on_μ
  simpa [Function.comp] using hpull

end GaussianIntegrability

end SpinGlass
