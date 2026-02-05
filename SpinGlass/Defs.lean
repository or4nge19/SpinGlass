import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Notation
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv


open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology

namespace SpinGlass

variable (N : ℕ) (β : ℝ)

/-! ### Basic Definitions -/

/-!
### Vol II–style abstraction boundary

Most of the “thermodynamic” objects used throughout Talagrand Vol I/II (partition function,
Gibbs weights, free energy, covariance/Hessian identities) only depend on a **finite configuration
space** `Σ` and an energy function `H : Σ → ℝ`.

In this repo, concrete models fix `Σ := Config N := Fin N → Bool`, and we keep that specialization
for compatibility. But we also expose a configuration-agnostic API so that Vol I models become
instances of the Vol II general framework (Gaussian processes indexed by `Σ`).
-/

/-- A generic finite configuration space. Concrete models will take `Σ := Config N`. -/
abbrev Conf := Type*

/--
Generic partition function on a finite configuration space `Σ`.

This is the canonical `log-sum-exp` object of Vol II (Ch. 8–9, Appendix A): any Gaussian
interpolation/comparison statement is ultimately applied to `H ↦ log (∑ σ, exp (-H σ))`.
-/
noncomputable def Z' {α : Type*} [Fintype α] (H : α → ℝ) : ℝ :=
  ∑ σ : α, Real.exp (- H σ)

/-- Generic Gibbs weight on `Σ` (a probability mass function when normalized by `Z'`). -/
noncomputable def gibbs_pmf' {α : Type*} [Fintype α] (H : α → ℝ) (σ : α) : ℝ :=
  Real.exp (- H σ) / Z' H

/-- Generic free energy density with an explicit scaling parameter `N` (system size). -/
noncomputable def free_energy_density' {α : Type*} [Fintype α] (N : ℕ) (H : α → ℝ) : ℝ :=
  (1 / (N : ℝ)) * Real.log (Z' H)

abbrev Config := Fin N → Bool

def spin (σ : Config N) (i : Fin N) : ℝ := if σ i then 1 else -1

abbrev EnergySpace := PiLp 2 (fun _ : Config N => ℝ)

/-- Magnetization of a configuration: \( \sum_{i=1}^N \sigma_i \) (with `σ_i ∈ {±1}`). -/
def magnetization (σ : Config N) : ℝ :=
  ∑ i : Fin N, spin N σ i

/--
External field energy term:
\[
H_{\text{field}}(\sigma) = h \sum_{i=1}^N \sigma_i.
\]

This is the physically correct “magnetic field” contribution (it depends on `σ`).
-/
def magnetic_field_vector (h : ℝ) : EnergySpace N :=
  WithLp.toLp 2 (fun σ : Config N => h * magnetization N σ)

noncomputable instance : InnerProductSpace ℝ (EnergySpace N) :=
  PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Config N => ℝ)

noncomputable instance : FiniteDimensional ℝ (EnergySpace N) := by
  classical
  -- `EnergySpace N` is a type synonym of the finite product `∀ σ : Config N, ℝ`.
  infer_instance

def std_basis (σ : Config N) : EnergySpace N :=
  WithLp.toLp 2 (fun τ => if σ = τ then 1 else 0)

lemma inner_std_basis_apply (σ : Config N) (H : EnergySpace N) :
    inner ℝ (std_basis N σ) H = H σ := by
  classical
  -- Expand the `PiLp 2` inner product and use the `if`-Kronecker delta.
  simp [std_basis, PiLp.inner_apply]

noncomputable section

def overlap (σ τ : Config N) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, (spin N σ i) * (spin N τ i)

/-! ### Covariance Kernels -/

def sk_cov_kernel (σ τ : Config N) : ℝ :=
  (N * β^2 / 2) * (overlap N σ τ)^2

def simple_cov_kernel (xi : ℝ → ℝ) (σ τ : Config N) : ℝ :=
  N * β^2 * xi (overlap N σ τ)

/-! ### Thermodynamic Quantities -/

def Z (H : EnergySpace N) : ℝ := ∑ σ, Real.exp (- H σ)

def gibbs_pmf (H : EnergySpace N) (σ : Config N) : ℝ :=
  Real.exp (- H σ) / Z N H

/-! #### Vol II bridge lemmas (`Config N` specialization) -/

/-- `Z` is the specialization of the Vol II partition function `Z'` to `Σ := Config N`. -/
lemma Z_eq_Z' (H : EnergySpace N) :
    Z (N := N) H = Z' (α := Config N) (fun σ : Config N => H σ) := by
  rfl

/-- `gibbs_pmf` is the specialization of the Vol II Gibbs weight `gibbs_pmf'` to `Σ := Config N`. -/
lemma gibbs_pmf_eq_gibbs_pmf' (H : EnergySpace N) (σ : Config N) :
    gibbs_pmf (N := N) H σ = gibbs_pmf' (α := Config N) (fun τ : Config N => H τ) σ := by
  rfl

/-- Gibbs average \(\langle f \rangle_H\) under the Gibbs weights `gibbs_pmf`. -/
noncomputable def gibbs_average (H : EnergySpace N) (f : Config N → ℝ) : ℝ :=
  ∑ σ, gibbs_pmf N H σ * f σ

/-! ### Free energy density and its abstract (Fréchet) Hessian -/

/--
Free energy density \(F_N(H) := \frac1N \log Z_N(H)\).

Reference: Talagrand, *Mean Field Models for Spin Glasses*, Vol. I, Ch. 1, §1.3
(definition and basic properties of the finite-volume free energy).
-/
noncomputable def free_energy_density (H : EnergySpace N) : ℝ :=
  (1 / (N : ℝ)) * Real.log (Z N H)

/-- `free_energy_density` is the specialization of the Vol II free energy `free_energy_density'`. -/
lemma free_energy_density_eq_free_energy_density' (H : EnergySpace N) :
    free_energy_density (N := N) H =
      free_energy_density' (α := Config N) N (fun σ : Config N => H σ) := by
  rfl

/--
The Hessian of the free energy density, defined abstractly as the second Fréchet derivative
`fderiv ℝ (fun H' => fderiv ℝ (free_energy_density N) H') H`.

This is the object that interfaces directly with Gaussian IBP statements.

Reference: Talagrand, Vol. I, Ch. 1, §1.3 (identification of the second derivative of \(\log Z\)
with a Gibbs covariance; this is the abstract Fréchet form needed for Gaussian IBP).
-/
noncomputable def hessian_free_energy_fderiv (H : EnergySpace N) :
    EnergySpace N →L[ℝ] EnergySpace N →L[ℝ] ℝ :=
  fderiv ℝ (fun H' => fderiv ℝ (free_energy_density (N := N)) H') H

lemma Z_pos (H : EnergySpace N) : 0 < Z N H := by
  classical
  have : 0 < ∑ σ : Config N, Real.exp (- H σ) := by
    refine Finset.sum_pos ?_ Finset.univ_nonempty
    intro σ _hσ
    exact Real.exp_pos _
  simpa [Z] using this

lemma Z_ne_zero (H : EnergySpace N) : Z N H ≠ 0 :=
  (ne_of_gt (Z_pos (N := N) (H := H)))

lemma gibbs_pmf_pos (H : EnergySpace N) (σ : Config N) : 0 < gibbs_pmf N H σ := by
  have hZ : 0 < Z N H := Z_pos (N := N) (H := H)
  simpa [gibbs_pmf] using (div_pos (Real.exp_pos _) hZ)

lemma gibbs_pmf_nonneg (H : EnergySpace N) (σ : Config N) : 0 ≤ gibbs_pmf N H σ :=
  le_of_lt (gibbs_pmf_pos (N := N) (H := H) σ)

lemma gibbs_pmf_le_one (H : EnergySpace N) (σ : Config N) : gibbs_pmf N H σ ≤ 1 := by
  classical
  have hZpos : 0 < Z N H := Z_pos (N := N) (H := H)
  have hterm_le :
      Real.exp (-H σ) ≤ Z N H := by
    -- A single term is bounded by the full sum `Z`.
    simpa [Z] using
      (Finset.single_le_sum (s := (Finset.univ : Finset (Config N)))
        (f := fun τ => Real.exp (-H τ))
        (hf := fun τ _hτ => (Real.exp_pos _).le)
        (a := σ) (h := Finset.mem_univ σ))
  have := (div_le_one hZpos).2 hterm_le
  simpa [gibbs_pmf] using this

lemma sum_gibbs_pmf (H : EnergySpace N) : (∑ σ, gibbs_pmf N H σ) = 1 := by
  classical
  have hZ : Z N H ≠ 0 := Z_ne_zero (N := N) (H := H)
  calc
    (∑ σ, gibbs_pmf N H σ) = ∑ σ, Real.exp (- H σ) / Z N H := by rfl
    _ = ∑ σ, Real.exp (- H σ) * (Z N H)⁻¹ := by
      simp [div_eq_mul_inv]
    _ = (∑ σ, Real.exp (- H σ)) * (Z N H)⁻¹ := by
      -- factor the constant `(Z N H)⁻¹` out of the sum
      simpa using
        (Finset.sum_mul (s := (Finset.univ : Finset (Config N)))
          (f := fun σ => Real.exp (- H σ)) (a := (Z N H)⁻¹)).symm
    _ = (Z N H) * (Z N H)⁻¹ := by
      simp [Z]
    _ = 1 := by simp [hZ]

/-! ### Differentiation formulas (Fréchet derivatives) -/

noncomputable abbrev evalCLM (σ : Config N) : EnergySpace N →L[ℝ] ℝ :=
  PiLp.proj (p := (2 : ENNReal)) (fun _ : Config N => ℝ) σ

noncomputable def grad_free_energy_density (H : EnergySpace N) : EnergySpace N →L[ℝ] ℝ :=
  (-(1 / (N : ℝ))) • ∑ σ : Config N, (gibbs_pmf N H σ) • evalCLM (N := N) σ

lemma hasFDerivAt_exp_neg_eval (H : EnergySpace N) (σ : Config N) :
    HasFDerivAt (fun H : EnergySpace N => Real.exp (-H σ))
      ((-(Real.exp (-H σ))) • evalCLM (N := N) σ) H := by
  classical
  have heval :
      HasFDerivAt (fun H : EnergySpace N => H σ) (evalCLM (N := N) σ) H := by
    simpa [evalCLM] using
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := (2 : ENNReal))
        (E := fun _ : Config N => ℝ) (f := H) σ)
  have hneg :
      HasFDerivAt (fun H : EnergySpace N => -(H σ)) (-(evalCLM (N := N) σ)) H := by
    simpa using heval.neg
  have hexp : HasDerivAt Real.exp (Real.exp (-H σ)) (-H σ) :=
    Real.hasDerivAt_exp (-H σ)
  have hcomp :
      HasFDerivAt (fun H : EnergySpace N => Real.exp (-(H σ)))
        ((Real.exp (-H σ)) • (-(evalCLM (N := N) σ))) H := by
    simpa [Function.comp] using
      (HasDerivAt.comp_hasFDerivAt (x := H) hexp hneg)
  simpa [smul_neg, neg_smul] using hcomp

lemma hasFDerivAt_Z (H : EnergySpace N) :
    HasFDerivAt (fun H : EnergySpace N => Z N H)
      (∑ σ : Config N, (-(Real.exp (-H σ))) • evalCLM (N := N) σ) H := by
  classical
  have hterm :
      ∀ σ : Config N,
        HasFDerivAt (fun H : EnergySpace N => Real.exp (-H σ))
          ((-(Real.exp (-H σ))) • evalCLM (N := N) σ) H := by
    intro σ
    simpa using hasFDerivAt_exp_neg_eval (N := N) (H := H) σ
  simpa [Z] using
    (HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Config N)))
      (A := fun σ : Config N => fun H : EnergySpace N => Real.exp (-H σ))
      (A' := fun σ : Config N => (-(Real.exp (-H σ))) • evalCLM (N := N) σ)
      (x := H)
      (fun σ _hσ => hterm σ))

lemma hasFDerivAt_inv_Z (H : EnergySpace N) :
    HasFDerivAt (fun H : EnergySpace N => (Z N H)⁻¹)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-(Z N H ^ 2)⁻¹)).comp
        (∑ σ : Config N, (-(Real.exp (-H σ))) • evalCLM (N := N) σ)) H := by
  classical
  have hInv :
      HasFDerivAt (fun x : ℝ => x⁻¹)
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-(Z N H ^ 2)⁻¹) : ℝ →L[ℝ] ℝ)
        (Z N H) :=
    hasFDerivAt_inv (𝕜 := ℝ) (x := Z N H) (Z_ne_zero (N := N) (H := H))
  simpa [Function.comp] using hInv.comp (x := H) (hasFDerivAt_Z (N := N) (H := H))

lemma hasFDerivAt_gibbs_pmf (H : EnergySpace N) (σ : Config N) :
    HasFDerivAt (fun H : EnergySpace N => gibbs_pmf N H σ)
      ((Z N H)⁻¹ • ((-(Real.exp (-H σ))) • evalCLM (N := N) σ) +
          (Real.exp (-H σ)) •
            ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-(Z N H ^ 2)⁻¹)).comp
              (∑ τ : Config N, (-(Real.exp (-H τ))) • evalCLM (N := N) τ))) H := by
  classical
  have hnum :
      HasFDerivAt (fun H : EnergySpace N => Real.exp (-H σ))
        ((-(Real.exp (-H σ))) • evalCLM (N := N) σ) H :=
    hasFDerivAt_exp_neg_eval (N := N) (H := H) σ
  have hden :
      HasFDerivAt (fun H : EnergySpace N => (Z N H)⁻¹)
        ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-(Z N H ^ 2)⁻¹)).comp
          (∑ τ : Config N, (-(Real.exp (-H τ))) • evalCLM (N := N) τ)) H :=
    hasFDerivAt_inv_Z (N := N) (H := H)
  have hmul :
      HasFDerivAt (fun H : EnergySpace N => Real.exp (-H σ) * (Z N H)⁻¹)
        ((Real.exp (-H σ)) •
            ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-(Z N H ^ 2)⁻¹)).comp
              (∑ τ : Config N, (-(Real.exp (-H τ))) • evalCLM (N := N) τ))
          + (Z N H)⁻¹ • ((-(Real.exp (-H σ))) • evalCLM (N := N) σ)) H :=
    (hnum.mul hden)
  simpa [gibbs_pmf, div_eq_mul_inv, add_comm, add_left_comm, add_assoc] using hmul

lemma differentiableAt_gibbs_pmf (H : EnergySpace N) (σ : Config N) :
    DifferentiableAt ℝ (fun H' => gibbs_pmf N H' σ) H :=
  (hasFDerivAt_gibbs_pmf (N := N) (H := H) σ).differentiableAt

lemma differentiable_gibbs_pmf (σ : Config N) :
    Differentiable ℝ (fun H' => gibbs_pmf N H' σ) := by
  intro H
  exact differentiableAt_gibbs_pmf (N := N) (H := H) σ

lemma fderiv_gibbs_pmf_apply (H h : EnergySpace N) (σ : Config N) :
    fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H σ) H h =
      (gibbs_pmf N H σ) *
        ((∑ τ : Config N, (gibbs_pmf N H τ) * h τ) - h σ) := by
  classical
  have h' := (hasFDerivAt_gibbs_pmf (N := N) (H := H) σ).fderiv
  have h_eval :
      fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H σ) H h =
        (Z N H)⁻¹ * (-(Real.exp (-H σ)) * h σ) +
          (Real.exp (-H σ)) *
            (-(Z N H ^ 2)⁻¹ *
              (∑ τ : Config N, (-(Real.exp (-H τ))) * h τ)) := by
    have hsum_const :
        (∑ x : Config N, h x * (Real.exp (-H x) * (Z N H ^ 2)⁻¹))
          = (Z N H ^ 2)⁻¹ * ∑ x : Config N, h x * Real.exp (-H x) := by
      classical
      calc
        (∑ x : Config N, h x * (Real.exp (-H x) * (Z N H ^ 2)⁻¹))
            = ∑ x : Config N, (h x * Real.exp (-H x)) * (Z N H ^ 2)⁻¹ := by
                refine Finset.sum_congr rfl ?_
                intro x _hx
                ring
        _ = (∑ x : Config N, h x * Real.exp (-H x)) * (Z N H ^ 2)⁻¹ := by
              simp [Finset.sum_mul]
        _ = (Z N H ^ 2)⁻¹ * ∑ x : Config N, h x * Real.exp (-H x) := by
              simp [mul_comm]
    simp [h', evalCLM, ContinuousLinearMap.smul_apply, smul_eq_mul, mul_comm]
    exact Eq.symm (Finset.mul_sum Finset.univ (fun i ↦ rexp (-H.ofLp i) * h.ofLp i) (Z N H ^ 2)⁻¹)
  have hZ : Z N H ≠ 0 := Z_ne_zero (N := N) (H := H)
  have hsum :
      (∑ τ : Config N, (-(Real.exp (-H τ))) * h τ) =
        -(Z N H) * (∑ τ : Config N, (gibbs_pmf N H τ) * h τ) := by
    simp [gibbs_pmf, div_eq_mul_inv, mul_comm, Finset.mul_sum]
    field_simp
  calc
    fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H σ) H h
        = (Z N H)⁻¹ * (-(Real.exp (-H σ)) * h σ) +
            (Real.exp (-H σ)) *
              (-(Z N H ^ 2)⁻¹ * (∑ τ : Config N, (-(Real.exp (-H τ))) * h τ)) := h_eval
    _ = (Real.exp (-H σ) / Z N H) * ((∑ τ : Config N, (Real.exp (-H τ) / Z N H) * h τ) - h σ) := by
          have hsum' :
              (∑ τ : Config N, (-(Real.exp (-H τ))) * h τ) =
                -∑ τ : Config N, (Real.exp (-H τ) * h τ) := by
            simp [Finset.sum_neg_distrib]
          have hexp_sum :
              (∑ τ : Config N, (Real.exp (-H τ) / Z N H) * h τ) =
                (Z N H)⁻¹ * ∑ τ : Config N, (Real.exp (-H τ) * h τ) := by
            simp [div_eq_mul_inv, mul_assoc, mul_comm, Finset.mul_sum]
          have : (Z N H ^ 2)⁻¹ * (Z N H) = (Z N H)⁻¹ := by
            field_simp [hZ, pow_two, mul_assoc, mul_left_comm, mul_comm]
          have hpull :
              (∑ x : Config N, h x * (Real.exp (-H x) * (Z N H)⁻¹)) =
                (Z N H)⁻¹ * ∑ x : Config N, h x * Real.exp (-H x) := by
            simp [mul_assoc, mul_comm, Finset.mul_sum]
          simp only [div_eq_mul_inv, pow_two, hsum']
          ring_nf
          have hsum_pullZ :
              (∑ x : Config N, (Z N H)⁻¹ * rexp (-H.ofLp x) * h.ofLp x) =
                (Z N H)⁻¹ * ∑ x : Config N, rexp (-H.ofLp x) * h.ofLp x := by
            -- `Finset.mul_sum` is `a * (∑ f) = ∑ (a * f)`; we use it backwards.
            simpa [mul_assoc] using
              (Eq.symm
                (Finset.mul_sum (Finset.univ : Finset (Config N))
                  (fun x : Config N => rexp (-H.ofLp x) * h.ofLp x) (Z N H)⁻¹))
          rw [hsum_pullZ]
          ring_nf
    _ = (gibbs_pmf N H σ) * ((∑ τ : Config N, (gibbs_pmf N H τ) * h τ) - h σ) := by
          simp [gibbs_pmf]

lemma hasFDerivAt_grad_free_energy_density (H : EnergySpace N) :
    HasFDerivAt (fun H : EnergySpace N => grad_free_energy_density (N := N) H)
      (-((1 / (N : ℝ)) •
          ∑ σ : Config N,
            (fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H σ) H).smulRight
              (evalCLM (N := N) σ))) H := by
  classical
  have hterm :
      ∀ σ : Config N,
        HasFDerivAt (fun H : EnergySpace N => (gibbs_pmf N H σ) • evalCLM (N := N) σ)
          ((fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H σ) H).smulRight (evalCLM (N := N) σ)) H := by
    intro σ
    have hg := hasFDerivAt_gibbs_pmf (N := N) (H := H) σ
    simpa [hg.fderiv] using hg.smul_const (evalCLM (N := N) σ)
  have hsum :
      HasFDerivAt (fun H : EnergySpace N => ∑ σ : Config N, (gibbs_pmf N H σ) • evalCLM (N := N) σ)
        (∑ σ : Config N,
          (fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H σ) H).smulRight (evalCLM (N := N) σ)) H := by
    simpa using
      (HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Config N)))
        (A := fun σ : Config N => fun H : EnergySpace N => (gibbs_pmf N H σ) • evalCLM (N := N) σ)
        (A' := fun σ : Config N =>
          (fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H σ) H).smulRight (evalCLM (N := N) σ))
        (x := H)
        (fun σ _hσ => hterm σ))
  simpa [grad_free_energy_density] using
    (hsum.fun_const_smul (c := (-(1 / (N : ℝ)))))

lemma fderiv_Z_apply (H h : EnergySpace N) :
    fderiv ℝ (fun H : EnergySpace N => Z N H) H h =
      - ∑ σ : Config N, Real.exp (-H σ) * h σ := by
  classical
  have hZ' := (hasFDerivAt_Z (N := N) (H := H)).fderiv
  simp [hZ', evalCLM, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]

lemma fderiv_free_energy_density_apply (H h : EnergySpace N) :
    fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H) H h =
      -(1 / (N : ℝ)) * ∑ σ : Config N, (gibbs_pmf N H σ) * h σ := by
  classical
  have hZ : HasFDerivAt (fun H : EnergySpace N => Z N H)
      (∑ σ : Config N, (-(Real.exp (-H σ))) • evalCLM (N := N) σ) H :=
    hasFDerivAt_Z (N := N) (H := H)
  have hlog :
      HasFDerivAt (fun H : EnergySpace N => Real.log (Z N H))
        ((Z N H)⁻¹ • (∑ σ : Config N, (-(Real.exp (-H σ))) • evalCLM (N := N) σ)) H :=
    (hZ.log (Z_ne_zero (N := N) (H := H)))
  have hF :
      HasFDerivAt (fun H : EnergySpace N => free_energy_density (N := N) H)
        ((1 / (N : ℝ)) • ((Z N H)⁻¹ • (∑ σ : Config N, (-(Real.exp (-H σ))) • evalCLM (N := N) σ))) H := by
    simpa [free_energy_density, smul_eq_mul, mul_assoc] using (hlog.const_smul (c := (1 / (N : ℝ))))
  have hF' := hF.fderiv
  have : fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H) H h =
        (1 / (N : ℝ)) * ((Z N H)⁻¹ * (-∑ σ : Config N, Real.exp (-H σ) * h σ)) := by
    simp [hF', evalCLM, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  calc
    fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H) H h
        = (1 / (N : ℝ)) * ((Z N H)⁻¹ * (-∑ σ : Config N, Real.exp (-H σ) * h σ)) := this
    _ = -(1 / (N : ℝ)) * ∑ σ : Config N, (Real.exp (-H σ) / Z N H) * h σ := by
          simp [div_eq_mul_inv, mul_assoc, mul_comm,
            Finset.mul_sum, Finset.sum_neg_distrib]
    _ = -(1 / (N : ℝ)) * ∑ σ : Config N, (gibbs_pmf N H σ) * h σ := by
          simp [gibbs_pmf]

lemma fderiv_free_energy_density_eq (H : EnergySpace N) :
    fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H) H =
      grad_free_energy_density (N := N) H := by
  classical
  ext h
  simp [grad_free_energy_density, fderiv_free_energy_density_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

def hessian_free_energy (H : EnergySpace N) (h k : EnergySpace N) : ℝ :=
  (1 / (N : ℝ)) * (
    (∑ σ, gibbs_pmf N H σ * h σ * k σ) -
    (∑ σ, gibbs_pmf N H σ * h σ) * (∑ τ, gibbs_pmf N H τ * k τ)
  )

lemma hessian_free_energy_fderiv_eq_hessian_free_energy
    (H h k : EnergySpace N) :
    (hessian_free_energy_fderiv (N := N) H) h k = hessian_free_energy N H h k := by
  classical
  have hgrad :
      (fun H' : EnergySpace N =>
          fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H) H') =
        fun H' : EnergySpace N => grad_free_energy_density (N := N) H' := by
    funext H'
    exact fderiv_free_energy_density_eq (N := N) (H := H')

  have hfderiv_grad :
      fderiv ℝ (fun H' : EnergySpace N => grad_free_energy_density (N := N) H') H =
        -((1 / (N : ℝ)) •
            ∑ σ : Config N,
              (fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H σ) H).smulRight
                (evalCLM (N := N) σ)) := by
    simpa using (hasFDerivAt_grad_free_energy_density (N := N) (H := H)).fderiv
  let g : Config N → ℝ := fun σ => gibbs_pmf N H σ
  let Eh : ℝ := ∑ τ : Config N, g τ * h τ
  calc
    (hessian_free_energy_fderiv (N := N) H) h k
        = ((fderiv ℝ (fun H' : EnergySpace N => grad_free_energy_density (N := N) H') H) h) k := by
            simp [hessian_free_energy_fderiv, hgrad]
    _ = (1 / (N : ℝ)) *
          (∑ σ : Config N, g σ * h σ * k σ -
            (∑ τ : Config N, g τ * h τ) * (∑ σ : Config N, g σ * k σ)) := by
          have h1 :
              ((fderiv ℝ (fun H' : EnergySpace N => grad_free_energy_density (N := N) H') H) h) k
                = -(1 / (N : ℝ)) * ∑ σ : Config N,
                    (fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H σ) H h) * k σ := by
            simp [hfderiv_grad, evalCLM, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
              ContinuousLinearMap.neg_apply, smul_eq_mul, mul_comm]
          have h2 :
              -(1 / (N : ℝ)) * ∑ σ : Config N,
                  (fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H σ) H h) * k σ
                = (1 / (N : ℝ)) *
                    (∑ σ : Config N, g σ * h σ * k σ -
                      (∑ τ : Config N, g τ * h τ) * (∑ σ : Config N, g σ * k σ)) := by
            have hsum_fderiv :
                ∑ σ : Config N,
                    (fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H σ) H h) * k σ
                  = (∑ σ : Config N, g σ * k σ) * (∑ τ : Config N, g τ * h τ) -
                      ∑ σ : Config N, g σ * h σ * k σ := by
              have hterm :
                  ∀ σ : Config N,
                    (fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H σ) H h) * k σ
                      = (g σ * k σ) * (∑ τ : Config N, g τ * h τ) - g σ * h σ * k σ := by
                intro σ
                simp [fderiv_gibbs_pmf_apply, g, mul_assoc, mul_left_comm, mul_comm, mul_sub]
              calc
                ∑ σ : Config N,
                    (fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H σ) H h) * k σ
                    = ∑ σ : Config N, ((g σ * k σ) * (∑ τ : Config N, g τ * h τ) - g σ * h σ * k σ) := by
                        refine Finset.sum_congr rfl ?_
                        intro σ _hσ
                        exact hterm σ
                _ = (∑ σ : Config N, (g σ * k σ) * (∑ τ : Config N, g τ * h τ)) -
                      ∑ σ : Config N, g σ * h σ * k σ := by
                        simp [Finset.sum_sub_distrib]
                _ = (∑ σ : Config N, g σ * k σ) * (∑ τ : Config N, g τ * h τ) -
                      ∑ σ : Config N, g σ * h σ * k σ := by
                        simpa [mul_assoc, mul_left_comm, mul_comm] using
                          (Finset.sum_mul (s := (Finset.univ : Finset (Config N)))
                            (f := fun σ : Config N => g σ * k σ)
                            (a := ∑ τ : Config N, g τ * h τ)).symm
            calc
              -(1 / (N : ℝ)) * ∑ σ : Config N,
                    (fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H σ) H h) * k σ
                  = -(1 / (N : ℝ)) *
                      ((∑ σ : Config N, g σ * k σ) * (∑ τ : Config N, g τ * h τ) -
                        ∑ σ : Config N, g σ * h σ * k σ) := by
                        simp [hsum_fderiv]
              _ = (1 / (N : ℝ)) *
                    (∑ σ : Config N, g σ * h σ * k σ -
                      (∑ τ : Config N, g τ * h τ) * (∑ σ : Config N, g σ * k σ)) := by
                        ring
          calc
            ((fderiv ℝ (fun H' : EnergySpace N => grad_free_energy_density (N := N) H') H) h) k
                = -(1 / (N : ℝ)) * ∑ σ : Config N,
                    (fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H σ) H h) * k σ := h1
            _ = (1 / (N : ℝ)) *
                    (∑ σ : Config N, g σ * h σ * k σ -
                      (∑ τ : Config N, g τ * h τ) * (∑ σ : Config N, g σ * k σ)) := h2
    _ = hessian_free_energy N H h k := by
          simp [hessian_free_energy, g, sub_eq_add_neg, add_comm]

/-! ### Compatibility aliases (for Gaussian IBP / calculus API) -/

/-- An alias for the abstract Fréchet Hessian of the free energy density. -/
noncomputable abbrev hessian_logZ (H : EnergySpace N) :
    EnergySpace N →L[ℝ] EnergySpace N →L[ℝ] ℝ :=
  hessian_free_energy_fderiv (N := N) H

/-- An alias for the explicit Gibbs covariance bilinear form. -/
def gibbs_covariance (H : EnergySpace N) (h k : EnergySpace N) : ℝ :=
  hessian_free_energy N H h k

/--
The abstract (Fréchet) Hessian agrees with the explicit Gibbs covariance formula.

Reference: Talagrand, Vol. I, Ch. 1, §1.3 (second derivative of \(\log Z\) as a Gibbs covariance),
formalized here as an equality between an `fderiv`-based Hessian and a finite-sum covariance.
-/
lemma hessian_eq_covariance (H h k : EnergySpace N) :
    (hessian_logZ (N := N) H) h k = gibbs_covariance (N := N) H h k := by
  simpa [hessian_logZ, gibbs_covariance] using
    (hessian_free_energy_fderiv_eq_hessian_free_energy (N := N) (H := H) (h := h) (k := k))

/-! ### Trace Formulae and Proofs -/

/--
The trace of the product of a covariance operator `Cov` and the Hessian of the free energy.
Algebraically reduces to variance-like terms of the Gibbs measure.

Reference: Talagrand, Vol. I, Ch. 1, §1.3 (trace/Hessian rewriting used in the Guerra
interpolation after applying Gaussian integration by parts).
-/
theorem trace_formula (H : EnergySpace N) (Cov : Config N → Config N → ℝ) :
    (∑ σ, ∑ τ, Cov σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ)) =
    (1 / (N : ℝ)) * (
      (∑ σ, (gibbs_pmf N H σ) * Cov σ σ) -
      (∑ σ, ∑ τ, (gibbs_pmf N H σ) * (gibbs_pmf N H τ) * Cov σ τ)
    ) := by
  classical
  let g : Config N → ℝ := fun σ => gibbs_pmf N H σ
  have hb : ∀ σ, (∑ ρ, g ρ * std_basis N σ ρ) = g σ := by
    intro σ
    simp [g, std_basis]
  have hc :
      ∀ σ τ, (∑ ρ, g ρ * std_basis N σ ρ * std_basis N τ ρ) = if σ = τ then g σ else 0 := by
    intro σ τ
    by_cases hστ : σ = τ
    · subst hστ
      simp [g, std_basis]
    · simp [g, std_basis, hστ]
  have hHess :
      ∀ σ τ,
        hessian_free_energy N H (std_basis N σ) (std_basis N τ)
        = (1 / (N : ℝ)) * ((if σ = τ then g σ else 0) - g σ * g τ) := by
    intro σ τ
    simp [hessian_free_energy, hb, hc, g]
  have h_diag :
      (∑ σ, ∑ τ, Cov σ τ * (if σ = τ then g σ else 0))
        = ∑ σ, (gibbs_pmf N H σ) * Cov σ σ := by
    classical
    refine Finset.sum_congr rfl ?_
    intro σ _hσ
    rw [Finset.sum_eq_single σ]
    · simp [g, mul_comm]
    · intro τ _hτ hτσ
      have hστ : σ ≠ τ := by simpa [eq_comm] using hτσ
      simp [g, hστ]
    · intro hmem
      exfalso
      exact hmem (Finset.mem_univ σ)
  have h_prod :
      (∑ σ, ∑ τ, Cov σ τ * (g σ * g τ))
        = ∑ σ, ∑ τ, (gibbs_pmf N H σ) * (gibbs_pmf N H τ) * Cov σ τ := by
    classical
    simp [g, mul_comm]
  calc
    (∑ σ, ∑ τ, Cov σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ))
        = ∑ σ, ∑ τ, Cov σ τ * ((1 / (N : ℝ)) * ((if σ = τ then g σ else 0) - g σ * g τ)) := by
            simp [hHess]
    _ = ∑ σ, ∑ τ, (1 / (N : ℝ)) * (Cov σ τ * ((if σ = τ then g σ else 0) - g σ * g τ)) := by
            refine Finset.sum_congr rfl ?_
            intro σ _hσ
            refine Finset.sum_congr rfl ?_
            intro τ _hτ
            simp [mul_left_comm]
    _ = (1 / (N : ℝ)) * ∑ σ, ∑ τ, Cov σ τ * ((if σ = τ then g σ else 0) - g σ * g τ) := by
            simp [Finset.mul_sum]
    _ = (1 / (N : ℝ)) * (
          (∑ σ, (gibbs_pmf N H σ) * Cov σ σ) -
          (∑ σ, ∑ τ, (gibbs_pmf N H σ) * (gibbs_pmf N H τ) * Cov σ τ)
        ) := by
            have hsplit :
                (∑ σ, ∑ τ, Cov σ τ * ((if σ = τ then g σ else 0) - g σ * g τ))
                  =
                (∑ σ, ∑ τ, Cov σ τ * (if σ = τ then g σ else 0))
                  -
                (∑ σ, ∑ τ, Cov σ τ * (g σ * g τ)) := by
              simp [mul_sub, Finset.sum_sub_distrib]
            simp [hsplit, h_prod, g, mul_comm]

/--
Self-overlap is always 1.
-/
theorem overlap_self (hN : 0 < N) (σ : Config N) : overlap N σ σ = 1 := by
  classical
  unfold overlap
  have hterm : ∀ i : Fin N, spin N σ i * spin N σ i = (1 : ℝ) := by
    intro i
    cases hσ : σ i <;> simp [spin, hσ]
  have hsum : (∑ i : Fin N, spin N σ i * spin N σ i) = (N : ℝ) := by
    calc
      (∑ i : Fin N, spin N σ i * spin N σ i)
          = ∑ _i : Fin N, (1 : ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              exact hterm i
      _ = (N : ℝ) := by simp
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  -- `(1 / (N : ℝ)) * N = 1` for `N ≠ 0`
  simp [hsum, hN0, div_eq_mul_inv]

/--
Trace calculation for the SK model covariance.
Result: (β²/2) * (1 - ⟨R₁₂²⟩ - 1/N + 1/N) = (β²/2) * (1 - ⟨R₁₂²⟩)

Reference: Talagrand, Vol. I, Ch. 1, §1.3 (the SK trace term in the derivative formula
leading to Eq. (1.65)).
-/
theorem trace_sk (hN : 0 < N) (H : EnergySpace N) :
    (∑ σ, ∑ τ, sk_cov_kernel N β σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ)) =
    (β^2 / 2) * (1 - ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ)^2) := by
  classical
  let E_R2 : ℝ :=
    ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ)^2
  have hs1 : (∑ σ, gibbs_pmf N H σ) = 1 := sum_gibbs_pmf (N := N) (H := H)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [trace_formula (N := N) (H := H) (Cov := sk_cov_kernel N β)]
  have hdiag :
      (∑ σ, gibbs_pmf N H σ * sk_cov_kernel N β σ σ)
        = (N * β^2 / 2) := by
    have hover : ∀ σ : Config N, (overlap N σ σ)^2 = (1 : ℝ) := by
      intro σ
      simp [overlap_self (N := N) (hN := hN) σ]
    calc
      (∑ σ, gibbs_pmf N H σ * sk_cov_kernel N β σ σ)
          = ∑ σ, gibbs_pmf N H σ * (N * β^2 / 2) := by
              refine Finset.sum_congr rfl ?_
              intro σ _hσ
              simp [sk_cov_kernel, hover, mul_comm]
      _ = (∑ σ, gibbs_pmf N H σ) * (N * β^2 / 2) := by
              simpa using
                (Finset.sum_mul (s := (Finset.univ : Finset (Config N)))
                  (f := fun σ => gibbs_pmf N H σ) (a := (N * β^2 / 2))).symm
      _ = (N * β^2 / 2) := by simp [hs1]
  have hoff :
      (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * sk_cov_kernel N β σ τ)
        = (N * β^2 / 2) * E_R2 := by
    simp [sk_cov_kernel, E_R2, Finset.mul_sum, mul_assoc, mul_left_comm]
  have hcancel : (1 / (N : ℝ)) * (N * β^2 / 2) = (β^2 / 2) := by
    field_simp [hN0]
  calc
    (1 / (N : ℝ)) *
        ((∑ σ, gibbs_pmf N H σ * sk_cov_kernel N β σ σ) -
          (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * sk_cov_kernel N β σ τ))
        = (1 / (N : ℝ)) * ((N * β^2 / 2) - ((N * β^2 / 2) * E_R2)) := by
            simp [hdiag, hoff]
    _ = (1 / (N : ℝ)) * ((N * β^2 / 2) * (1 - E_R2)) := by ring
    _ = ((1 / (N : ℝ)) * (N * β^2 / 2)) * (1 - E_R2) := by
            simp [mul_assoc]
    _ = (β^2 / 2) * (1 - E_R2) := by
            simpa [mul_assoc] using congrArg (fun z => z * (1 - E_R2)) hcancel
    _ = (β^2 / 2) * (1 - ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ)^2) := by
            simp [E_R2]

/--
Trace calculation for Simple Model.
Result: β² q (1 - ⟨R₁₂⟩)

Reference: Talagrand, Vol. I, Ch. 1, §1.3 (generalized for RSB).
-/
theorem trace_simple (hN : 0 < N) (H : EnergySpace N) (xi : ℝ → ℝ) :
    (∑ σ, ∑ τ, simple_cov_kernel N β xi σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ)) =
    (β^2) * (xi 1 - ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * xi (overlap N σ τ)) := by
  classical
  let E_xi : ℝ :=
    ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * xi (overlap N σ τ)
  have hs1 : (∑ σ, gibbs_pmf N H σ) = 1 := sum_gibbs_pmf (N := N) (H := H)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [trace_formula (N := N) (H := H) (Cov := simple_cov_kernel N β xi)]
  have hdiag :
      (∑ σ, gibbs_pmf N H σ * simple_cov_kernel N β xi σ σ) = N * β^2 * xi 1 := by
    have hover : ∀ σ : Config N, overlap N σ σ = 1 := by
      intro σ
      simpa using overlap_self (N := N) (hN := hN) σ
    calc
      (∑ σ, gibbs_pmf N H σ * simple_cov_kernel N β xi σ σ)
          = ∑ σ, gibbs_pmf N H σ * (N * β^2 * xi 1) := by
              simp [simple_cov_kernel, hover, mul_assoc, mul_comm]
      _ = (∑ σ, gibbs_pmf N H σ) * (N * β^2 * xi 1) := by
              simpa using
                (Finset.sum_mul (s := (Finset.univ : Finset (Config N)))
                  (f := fun σ => gibbs_pmf N H σ) (a := (N * β^2 * xi 1))).symm
      _ = N * β^2 * xi 1 := by simp [hs1]
  have hoff :
      (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * simple_cov_kernel N β xi σ τ)
        = (N * β^2) * E_xi := by
    simp [simple_cov_kernel, E_xi, Finset.mul_sum, mul_assoc, mul_left_comm]
  have hcancel : (1 / (N : ℝ)) * (N * β^2) = (β^2) := by
    field_simp [hN0]
  calc
    (1 / (N : ℝ)) *
        ((∑ σ, gibbs_pmf N H σ * simple_cov_kernel N β xi σ σ) -
          (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * simple_cov_kernel N β xi σ τ))
        = (1 / (N : ℝ)) * ((N * β^2 * xi 1) - ((N * β^2) * E_xi)) := by
            simp [hdiag, hoff]
    _ = (1 / (N : ℝ)) * ((N * β^2) * (xi 1 - E_xi)) := by ring
    _ = ((1 / (N : ℝ)) * (N * β^2)) * (xi 1 - E_xi) := by
            simp [mul_assoc]
    _ = (β^2) * (xi 1 - E_xi) := by
            simpa [mul_assoc] using congrArg (fun z => z * (xi 1 - E_xi)) hcancel
    _ = (β^2) * (xi 1 - ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * xi (overlap N σ τ)) := by
            simp [E_xi]

/--
**Proof of Guerra's Derivative Bound**

Combinations of the trace formulas imply:
φ'(t) = (β²/2) * ( (1/2 - ξ(1)) - ⟨R²/2 - ξ(R)⟩ )

Reference: Talagrand, Vol. I, Ch. 1, §1.3, Eq. (1.65) (generalized).
-/
theorem guerra_derivative_bound_algebra
    (hN : 0 < N) (H : EnergySpace N) (xi : ℝ → ℝ) :
    let term_sk := (∑ σ, ∑ τ, sk_cov_kernel N β σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ))
    let term_simple := (∑ σ, ∑ τ, simple_cov_kernel N β xi σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ))
    (1 / 2) * (term_sk - term_simple) = (β^2 / 2) * ((1/2 - xi 1) - ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * ((overlap N σ τ)^2 / 2 - xi (overlap N σ τ))) := by
  dsimp
  rw [trace_sk (N := N) (β := β) (hN := hN) (H := H),
      trace_simple (N := N) (β := β) (xi := xi) (hN := hN) (H := H)]
  let E_xi := ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * xi (overlap N σ τ)
  let E_R2 := ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ)^2
  have h_main : (1 / 2) * ((β^2 / 2) * (1 - E_R2) - (β^2) * (xi 1 - E_xi)) =
                (β^2 / 2) * ((1/2 - xi 1) - (1/2 * E_R2 - E_xi)) := by
    ring
  rw [h_main]
  congr 1
  congr 1
  classical
  simp [E_R2, E_xi]
  have hhalf :
      (2⁻¹ : ℝ) *
          (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ) ^ 2)
        =
          ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * ((overlap N σ τ) ^ 2 / 2) := by
    classical
    simp [div_eq_mul_inv]
    calc
      (2⁻¹ : ℝ) *
          (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ) ^ 2)
          =
          ∑ σ, (2⁻¹ : ℝ) *
            (∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ) ^ 2) := by
            simpa using
              (Finset.mul_sum (s := (Finset.univ : Finset (Config N)))
                (f := fun σ =>
                  ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ) ^ 2)
                (a := (2⁻¹ : ℝ)))
      _ =
          ∑ σ, ∑ τ, (2⁻¹ : ℝ) *
            (gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro σ _hσ
            simpa using
              (Finset.mul_sum (s := (Finset.univ : Finset (Config N)))
                (f := fun τ =>
                  gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ) ^ 2)
                (a := (2⁻¹ : ℝ)))
      _ =
          ∑ σ, ∑ τ,
            gibbs_pmf N H σ * gibbs_pmf N H τ * ((overlap N σ τ) ^ 2 * (2⁻¹ : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro σ _hσ
            refine Finset.sum_congr rfl ?_
            intro τ _hτ
            ring
  rw [hhalf]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro τ _
  ring

end
end SpinGlass
