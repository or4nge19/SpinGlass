import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite Gibbs calculus (Vol II abstraction boundary)

This file develops the **model-agnostic finite-volume calculus** for the free energy functional

`H ↦ (1/n) * log (∑ σ, exp (- H σ))`

on a finite configuration space `α`.

The point is to make Talagrand Vol I/II arguments reusable: once a model is packaged as a random
Hamiltonian taking values in the Hilbert space `PiLp 2 (fun _ : α => ℝ)`, the analytic layer
(Fréchet derivatives, Hessian = Gibbs covariance, trace formulae) becomes uniform and does not
depend on the specific structure of `α` (`Config N`, cascades, …).
-/

open Real BigOperators Filter Topology

namespace SpinGlass

namespace FiniteGibbs

/-! ## Basic objects: partition function, Gibbs weights, free energy -/

noncomputable section

variable {α : Type*} [Fintype α] [Nonempty α]

/-- Energy Hilbert space on a finite configuration space `α`. -/
abbrev EnergySpace (α : Type*) : Type _ :=
  PiLp 2 (fun _ : α => ℝ)

noncomputable instance : InnerProductSpace ℝ (EnergySpace α) :=
  PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : α => ℝ)

noncomputable instance : FiniteDimensional ℝ (EnergySpace α) := by
  infer_instance

/-- Dirac basis vector `e_σ` in `EnergySpace α`. -/
noncomputable def std_basis (σ : α) : EnergySpace α := by
    classical
    exact WithLp.toLp 2 (fun τ => if σ = τ then 1 else 0)

omit [Nonempty α] in
lemma inner_std_basis_apply (σ : α) (H : EnergySpace α) :
    inner ℝ (std_basis (α := α) σ) H = H σ := by
  classical
  simp [std_basis, PiLp.inner_apply]

/-- Partition function `Z(H) = ∑_σ exp(-H σ)`. -/
noncomputable def Z (H : EnergySpace α) : ℝ :=
  ∑ σ : α, Real.exp (-H σ)

/-- Gibbs weight (probability mass function after normalization). -/
noncomputable def gibbs_pmf (H : EnergySpace α) (σ : α) : ℝ :=
  Real.exp (-H σ) / Z (α := α) H

/-- Free energy density with explicit scaling parameter `n` (system size). -/
noncomputable def free_energy_density (n : ℕ) (H : EnergySpace α) : ℝ :=
  (1 / (n : ℝ)) * Real.log (Z (α := α) H)

lemma Z_pos (H : EnergySpace α) : 0 < Z (α := α) H := by

  refine Finset.sum_pos ?_ Finset.univ_nonempty
  intro σ _hσ
  exact Real.exp_pos _

lemma Z_ne_zero (H : EnergySpace α) : Z (α := α) H ≠ 0 :=
  (ne_of_gt (Z_pos (α := α) (H := H)))

lemma gibbs_pmf_pos (H : EnergySpace α) (σ : α) : 0 < gibbs_pmf (α := α) H σ := by
  have hZ : 0 < Z (α := α) H := Z_pos (α := α) (H := H)
  simpa [gibbs_pmf] using (div_pos (Real.exp_pos _) hZ)

lemma gibbs_pmf_nonneg (H : EnergySpace α) (σ : α) : 0 ≤ gibbs_pmf (α := α) H σ :=
  le_of_lt (gibbs_pmf_pos (α := α) (H := H) σ)

lemma gibbs_pmf_le_one (H : EnergySpace α) (σ : α) : gibbs_pmf (α := α) H σ ≤ 1 := by
  have hZpos : 0 < Z (α := α) H := Z_pos (α := α) (H := H)
  have hterm_le : Real.exp (-H σ) ≤ Z (α := α) H := by
    simpa [Z] using
      (Finset.single_le_sum (s := (Finset.univ : Finset α))
        (f := fun τ => Real.exp (-H τ))
        (hf := fun τ _hτ => (Real.exp_pos _).le)
        (a := σ) (h := Finset.mem_univ σ))
  have := (div_le_one hZpos).2 hterm_le
  simpa [gibbs_pmf] using this

lemma sum_gibbs_pmf (H : EnergySpace α) : (∑ σ, gibbs_pmf (α := α) H σ) = 1 := by
  have hZ : Z (α := α) H ≠ 0 := Z_ne_zero (α := α) (H := H)
  calc
    (∑ σ, gibbs_pmf (α := α) H σ) = ∑ σ, Real.exp (-H σ) / Z (α := α) H := by rfl
    _ = ∑ σ, Real.exp (-H σ) * (Z (α := α) H)⁻¹ := by
      simp [div_eq_mul_inv]
    _ = (∑ σ, Real.exp (-H σ)) * (Z (α := α) H)⁻¹ := by
      simpa using
        (Finset.sum_mul (s := (Finset.univ : Finset α))
          (f := fun σ => Real.exp (-H σ)) (a := (Z (α := α) H)⁻¹)).symm
    _ = (Z (α := α) H) * (Z (α := α) H)⁻¹ := by
      simp [Z]
    _ = 1 := by simp [hZ]

/-! ## Fréchet calculus: derivatives and Hessian identities -/

noncomputable abbrev evalCLM (σ : α) : EnergySpace α →L[ℝ] ℝ :=
  PiLp.proj (p := (2 : ENNReal)) (fun _ : α => ℝ) σ

noncomputable def grad_free_energy_density (n : ℕ) (H : EnergySpace α) : EnergySpace α →L[ℝ] ℝ :=
  (-(1 / (n : ℝ))) • ∑ σ : α, (gibbs_pmf (α := α) H σ) • evalCLM (α := α) σ

omit [Nonempty α] in
lemma hasFDerivAt_exp_neg_eval (H : EnergySpace α) (σ : α) :
    HasFDerivAt (fun H : EnergySpace α => Real.exp (-H σ))
      ((-(Real.exp (-H σ))) • evalCLM (α := α) σ) H := by
  have heval :
      HasFDerivAt (fun H : EnergySpace α => H σ) (evalCLM (α := α) σ) H := by
    simpa [evalCLM] using
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := (2 : ENNReal))
        (E := fun _ : α => ℝ) (f := H) σ)
  have hneg :
      HasFDerivAt (fun H : EnergySpace α => -(H σ)) (-(evalCLM (α := α) σ)) H := by
    simpa using heval.neg
  have hexp : HasDerivAt Real.exp (Real.exp (-H σ)) (-H σ) :=
    Real.hasDerivAt_exp (-H σ)
  have hcomp :
      HasFDerivAt (fun H : EnergySpace α => Real.exp (-(H σ)))
        ((Real.exp (-H σ)) • (-(evalCLM (α := α) σ))) H := by
    simpa [Function.comp] using
      (HasDerivAt.comp_hasFDerivAt (x := H) hexp hneg)
  simpa [smul_neg, neg_smul] using hcomp

omit [Nonempty α] in
lemma hasFDerivAt_Z (H : EnergySpace α) :
    HasFDerivAt (fun H : EnergySpace α => Z (α := α) H)
      (∑ σ : α, (-(Real.exp (-H σ))) • evalCLM (α := α) σ) H := by

  have hterm :
      ∀ σ : α,
        HasFDerivAt (fun H : EnergySpace α => Real.exp (-H σ))
          ((-(Real.exp (-H σ))) • evalCLM (α := α) σ) H := by
    intro σ
    simpa using hasFDerivAt_exp_neg_eval (α := α) (H := H) σ
  simpa [Z] using
    (HasFDerivAt.fun_sum (u := (Finset.univ : Finset α))
      (A := fun σ : α => fun H : EnergySpace α => Real.exp (-H σ))
      (A' := fun σ : α => (-(Real.exp (-H σ))) • evalCLM (α := α) σ)
      (x := H)
      (fun σ _hσ => hterm σ))

lemma hasFDerivAt_inv_Z (H : EnergySpace α) :
    HasFDerivAt (fun H : EnergySpace α => (Z (α := α) H)⁻¹)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-(Z (α := α) H ^ 2)⁻¹)).comp
        (∑ σ : α, (-(Real.exp (-H σ))) • evalCLM (α := α) σ)) H := by
  have hInv :
      HasFDerivAt (fun x : ℝ => x⁻¹)
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-(Z (α := α) H ^ 2)⁻¹) : ℝ →L[ℝ] ℝ)
        (Z (α := α) H) :=
    hasFDerivAt_inv (𝕜 := ℝ) (x := Z (α := α) H) (Z_ne_zero (α := α) (H := H))
  simpa [Function.comp] using hInv.comp (x := H) (hasFDerivAt_Z (α := α) (H := H))

lemma hasFDerivAt_gibbs_pmf (H : EnergySpace α) (σ : α) :
    HasFDerivAt (fun H : EnergySpace α => gibbs_pmf (α := α) H σ)
      ((Z (α := α) H)⁻¹ • ((-(Real.exp (-H σ))) • evalCLM (α := α) σ) +
          (Real.exp (-H σ)) •
            ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-(Z (α := α) H ^ 2)⁻¹)).comp
              (∑ τ : α, (-(Real.exp (-H τ))) • evalCLM (α := α) τ))) H := by
  have hnum :
      HasFDerivAt (fun H : EnergySpace α => Real.exp (-H σ))
        ((-(Real.exp (-H σ))) • evalCLM (α := α) σ) H :=
    hasFDerivAt_exp_neg_eval (α := α) (H := H) σ
  have hden :
      HasFDerivAt (fun H : EnergySpace α => (Z (α := α) H)⁻¹)
        ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-(Z (α := α) H ^ 2)⁻¹)).comp
          (∑ τ : α, (-(Real.exp (-H τ))) • evalCLM (α := α) τ)) H :=
    hasFDerivAt_inv_Z (α := α) (H := H)
  have hmul :
      HasFDerivAt (fun H : EnergySpace α => Real.exp (-H σ) * (Z (α := α) H)⁻¹)
        ((Real.exp (-H σ)) •
            ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-(Z (α := α) H ^ 2)⁻¹)).comp
              (∑ τ : α, (-(Real.exp (-H τ))) • evalCLM (α := α) τ))
          + (Z (α := α) H)⁻¹ • ((-(Real.exp (-H σ))) • evalCLM (α := α) σ)) H :=
    (hnum.mul hden)
  simpa [gibbs_pmf, div_eq_mul_inv, add_comm, add_left_comm, add_assoc] using hmul

lemma fderiv_gibbs_pmf_apply (H h : EnergySpace α) (σ : α) :
    fderiv ℝ (fun H : EnergySpace α => gibbs_pmf (α := α) H σ) H h =
      (gibbs_pmf (α := α) H σ) *
        ((∑ τ : α, (gibbs_pmf (α := α) H τ) * h τ) - h σ) := by
  have h' := (hasFDerivAt_gibbs_pmf (α := α) (H := H) σ).fderiv
  have h_eval :
      fderiv ℝ (fun H : EnergySpace α => gibbs_pmf (α := α) H σ) H h =
        (Z (α := α) H)⁻¹ * (-(Real.exp (-H σ)) * h σ) +
          (Real.exp (-H σ)) *
            (-(Z (α := α) H ^ 2)⁻¹ *
              (∑ τ : α, (-(Real.exp (-H τ))) * h τ)) := by
    -- Evaluate the Fréchet derivative on `h`.
    simp [h', evalCLM, ContinuousLinearMap.smul_apply, smul_eq_mul, mul_comm]
    -- Remaining goal: pull the scalar factor `(Z H ^ 2)⁻¹` out of the finite sum.
    simpa [mul_assoc] using
      (Finset.mul_sum (Finset.univ : Finset α)
        (fun i : α => Real.exp (-H i) * h i) (Z (α := α) H ^ 2)⁻¹).symm
  have hZ : Z (α := α) H ≠ 0 := Z_ne_zero (α := α) (H := H)
  have hsum' : (∑ τ : α, (-(Real.exp (-H τ))) * h τ) = -∑ τ : α, (Real.exp (-H τ) * h τ) := by
    simp [Finset.sum_neg_distrib]
  have hexp_sum :
      (∑ τ : α, (Real.exp (-H τ) / Z (α := α) H) * h τ) =
        (Z (α := α) H)⁻¹ * ∑ τ : α, (Real.exp (-H τ) * h τ) := by
    simp [div_eq_mul_inv, mul_assoc, mul_comm, Finset.mul_sum]
  have hZ2 : (Z (α := α) H ^ 2)⁻¹ * (Z (α := α) H) = (Z (α := α) H)⁻¹ := by
    field_simp [hZ, pow_two, mul_assoc, mul_left_comm, mul_comm]
  calc
    fderiv ℝ (fun H : EnergySpace α => gibbs_pmf (α := α) H σ) H h
        = (Z (α := α) H)⁻¹ * (-(Real.exp (-H σ)) * h σ) +
            (Real.exp (-H σ)) *
              (-(Z (α := α) H ^ 2)⁻¹ * (∑ τ : α, (-(Real.exp (-H τ))) * h τ)) := h_eval
    _ = (Real.exp (-H σ) / Z (α := α) H) *
          ((∑ τ : α, (Real.exp (-H τ) / Z (α := α) H) * h τ) - h σ) := by
          simp only [div_eq_mul_inv, pow_two, hsum']
          ring_nf
          have hsum_pullZ :
              (∑ x : α, (Z (α := α) H)⁻¹ * Real.exp (-H.ofLp x) * h.ofLp x) =
                (Z (α := α) H)⁻¹ * ∑ x : α, Real.exp (-H.ofLp x) * h.ofLp x := by
            simpa [mul_assoc] using
              (Eq.symm
                (Finset.mul_sum (Finset.univ : Finset α)
                  (fun x : α => Real.exp (-H.ofLp x) * h.ofLp x) (Z (α := α) H)⁻¹))
          rw [hsum_pullZ]
          ring_nf
    _ = (gibbs_pmf (α := α) H σ) *
          ((∑ τ : α, (gibbs_pmf (α := α) H τ) * h τ) - h σ) := by
          simp [gibbs_pmf, hexp_sum]

noncomputable def hessian_free_energy_fderiv (n : ℕ) (H : EnergySpace α) :
    EnergySpace α →L[ℝ] EnergySpace α →L[ℝ] ℝ :=
  fderiv ℝ (fun H' => fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H) H') H

/-- The explicit Gibbs covariance bilinear form (Talagrand). -/
def hessian_free_energy (n : ℕ) (H : EnergySpace α) (h k : EnergySpace α) : ℝ :=
  (1 / (n : ℝ)) * (
    (∑ σ, gibbs_pmf (α := α) H σ * h σ * k σ) -
    (∑ σ, gibbs_pmf (α := α) H σ * h σ) * (∑ τ, gibbs_pmf (α := α) H τ * k τ)
  )

lemma fderiv_free_energy_density_apply (n : ℕ) (H h : EnergySpace α) :
    fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H) H h =
      -(1 / (n : ℝ)) * ∑ σ : α, (gibbs_pmf (α := α) H σ) * h σ := by
  have hZ : HasFDerivAt (fun H : EnergySpace α => Z (α := α) H)
      (∑ σ : α, (-(Real.exp (-H σ))) • evalCLM (α := α) σ) H :=
    hasFDerivAt_Z (α := α) (H := H)
  have hlog :
      HasFDerivAt (fun H : EnergySpace α => Real.log (Z (α := α) H))
        ((Z (α := α) H)⁻¹ • (∑ σ : α, (-(Real.exp (-H σ))) • evalCLM (α := α) σ)) H :=
    (hZ.log (Z_ne_zero (α := α) (H := H)))
  have hF :
      HasFDerivAt (fun H : EnergySpace α => free_energy_density (α := α) n H)
        ((1 / (n : ℝ)) • ((Z (α := α) H)⁻¹ • (∑ σ : α, (-(Real.exp (-H σ))) • evalCLM (α := α) σ))) H := by
    simpa [free_energy_density, smul_eq_mul, mul_assoc] using (hlog.const_smul (c := (1 / (n : ℝ))))
  have hF' := hF.fderiv
  have :
      fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H) H h =
        (1 / (n : ℝ)) * ((Z (α := α) H)⁻¹ * (-∑ σ : α, Real.exp (-H σ) * h σ)) := by
    simp [hF', evalCLM, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  calc
    fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H) H h
        = (1 / (n : ℝ)) * ((Z (α := α) H)⁻¹ * (-∑ σ : α, Real.exp (-H σ) * h σ)) := this
    _ = -(1 / (n : ℝ)) * ∑ σ : α, (Real.exp (-H σ) / Z (α := α) H) * h σ := by
          simp [div_eq_mul_inv, mul_assoc, mul_comm, Finset.mul_sum, Finset.sum_neg_distrib]
    _ = -(1 / (n : ℝ)) * ∑ σ : α, (gibbs_pmf (α := α) H σ) * h σ := by
          simp [gibbs_pmf]

lemma hasFDerivAt_grad_free_energy_density (n : ℕ) (H : EnergySpace α) :
    HasFDerivAt (fun H : EnergySpace α => grad_free_energy_density (α := α) n H)
      (-((1 / (n : ℝ)) •
          ∑ σ : α,
            (fderiv ℝ (fun H : EnergySpace α => gibbs_pmf (α := α) H σ) H).smulRight
              (evalCLM (α := α) σ))) H := by
  have hterm :
      ∀ σ : α,
        HasFDerivAt (fun H : EnergySpace α => (gibbs_pmf (α := α) H σ) • evalCLM (α := α) σ)
          ((fderiv ℝ (fun H : EnergySpace α => gibbs_pmf (α := α) H σ) H).smulRight
            (evalCLM (α := α) σ)) H := by
    intro σ
    have hg := hasFDerivAt_gibbs_pmf (α := α) (H := H) σ
    simpa [hg.fderiv] using hg.smul_const (evalCLM (α := α) σ)
  have hsum :
      HasFDerivAt (fun H : EnergySpace α => ∑ σ : α, (gibbs_pmf (α := α) H σ) • evalCLM (α := α) σ)
        (∑ σ : α,
          (fderiv ℝ (fun H : EnergySpace α => gibbs_pmf (α := α) H σ) H).smulRight
            (evalCLM (α := α) σ)) H := by
    simpa using
      (HasFDerivAt.fun_sum (u := (Finset.univ : Finset α))
        (A := fun σ : α => fun H : EnergySpace α => (gibbs_pmf (α := α) H σ) • evalCLM (α := α) σ)
        (A' := fun σ : α =>
          (fderiv ℝ (fun H : EnergySpace α => gibbs_pmf (α := α) H σ) H).smulRight (evalCLM (α := α) σ))
        (x := H)
        (fun σ _hσ => hterm σ))
  simpa [grad_free_energy_density] using (hsum.fun_const_smul (c := (-(1 / (n : ℝ)))))

lemma fderiv_free_energy_density_eq (n : ℕ) (H : EnergySpace α) :
    fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H) H =
      grad_free_energy_density (α := α) n H := by

  ext h
  simp [grad_free_energy_density, fderiv_free_energy_density_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

lemma hessian_free_energy_fderiv_eq_hessian_free_energy (n : ℕ) (H h k : EnergySpace α) :
    (hessian_free_energy_fderiv (α := α) n H) h k = hessian_free_energy (α := α) n H h k := by
  have hgrad :
      (fun H' : EnergySpace α =>
          fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H) H') =
        fun H' : EnergySpace α => grad_free_energy_density (α := α) n H' := by
    funext H'
    exact fderiv_free_energy_density_eq (α := α) (n := n) (H := H')
  have hfderiv_grad :
      fderiv ℝ (fun H' : EnergySpace α => grad_free_energy_density (α := α) n H') H =
        -((1 / (n : ℝ)) •
            ∑ σ : α,
              (fderiv ℝ (fun H : EnergySpace α => gibbs_pmf (α := α) H σ) H).smulRight
                (evalCLM (α := α) σ)) := by
    simpa using (hasFDerivAt_grad_free_energy_density (α := α) (n := n) (H := H)).fderiv
  let g : α → ℝ := fun σ => gibbs_pmf (α := α) H σ
  calc
    (hessian_free_energy_fderiv (α := α) n H) h k
        = ((fderiv ℝ (fun H' : EnergySpace α => grad_free_energy_density (α := α) n H') H) h) k := by
            simp [hessian_free_energy_fderiv, hgrad]
    _ = (1 / (n : ℝ)) *
          (∑ σ : α, g σ * h σ * k σ -
            (∑ τ : α, g τ * h τ) * (∑ σ : α, g σ * k σ)) := by
          have h1 :
              ((fderiv ℝ (fun H' : EnergySpace α => grad_free_energy_density (α := α) n H') H) h) k
                = -(1 / (n : ℝ)) * ∑ σ : α,
                    (fderiv ℝ (fun H : EnergySpace α => gibbs_pmf (α := α) H σ) H h) * k σ := by
            simp [hfderiv_grad, evalCLM, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
              ContinuousLinearMap.neg_apply, smul_eq_mul, mul_comm]
          have h2 :
              -(1 / (n : ℝ)) * ∑ σ : α,
                  (fderiv ℝ (fun H : EnergySpace α => gibbs_pmf (α := α) H σ) H h) * k σ
                = (1 / (n : ℝ)) *
                    (∑ σ : α, g σ * h σ * k σ -
                      (∑ τ : α, g τ * h τ) * (∑ σ : α, g σ * k σ)) := by
            have hsum_fderiv :
                ∑ σ : α,
                    (fderiv ℝ (fun H : EnergySpace α => gibbs_pmf (α := α) H σ) H h) * k σ
                  = (∑ σ : α, g σ * k σ) * (∑ τ : α, g τ * h τ) -
                      ∑ σ : α, g σ * h σ * k σ := by
              have hterm :
                  ∀ σ : α,
                    (fderiv ℝ (fun H : EnergySpace α => gibbs_pmf (α := α) H σ) H h) * k σ
                      = (g σ * k σ) * (∑ τ : α, g τ * h τ) - g σ * h σ * k σ := by
                intro σ
                simp [fderiv_gibbs_pmf_apply, g, mul_assoc, mul_left_comm, mul_comm, mul_sub]
              calc
                ∑ σ : α,
                    (fderiv ℝ (fun H : EnergySpace α => gibbs_pmf (α := α) H σ) H h) * k σ
                    = ∑ σ : α, ((g σ * k σ) * (∑ τ : α, g τ * h τ) - g σ * h σ * k σ) := by
                        refine Finset.sum_congr rfl ?_
                        intro σ _hσ
                        exact hterm σ
                _ = (∑ σ : α, (g σ * k σ) * (∑ τ : α, g τ * h τ)) -
                      ∑ σ : α, g σ * h σ * k σ := by
                        simp [Finset.sum_sub_distrib]
                _ = (∑ σ : α, g σ * k σ) * (∑ τ : α, g τ * h τ) -
                      ∑ σ : α, g σ * h σ * k σ := by
                        simpa [mul_assoc, mul_left_comm, mul_comm] using
                          (Finset.sum_mul (s := (Finset.univ : Finset α))
                            (f := fun σ : α => g σ * k σ) (a := ∑ τ : α, g τ * h τ)).symm
            calc
              -(1 / (n : ℝ)) * ∑ σ : α,
                    (fderiv ℝ (fun H : EnergySpace α => gibbs_pmf (α := α) H σ) H h) * k σ
                  = -(1 / (n : ℝ)) *
                      ((∑ σ : α, g σ * k σ) * (∑ τ : α, g τ * h τ) -
                        ∑ σ : α, g σ * h σ * k σ) := by
                        simp [hsum_fderiv]
              _ = (1 / (n : ℝ)) *
                    (∑ σ : α, g σ * h σ * k σ -
                      (∑ τ : α, g τ * h τ) * (∑ σ : α, g σ * k σ)) := by
                        ring
          calc
            ((fderiv ℝ (fun H' : EnergySpace α => grad_free_energy_density (α := α) n H') H) h) k
                = -(1 / (n : ℝ)) * ∑ σ : α,
                    (fderiv ℝ (fun H : EnergySpace α => gibbs_pmf (α := α) H σ) H h) * k σ := h1
            _ = (1 / (n : ℝ)) *
                    (∑ σ : α, g σ * h σ * k σ -
                      (∑ τ : α, g τ * h τ) * (∑ σ : α, g σ * k σ)) := h2
    _ = hessian_free_energy (α := α) n H h k := by
          simp [hessian_free_energy, g, sub_eq_add_neg, add_comm]

/-- An alias for the abstract Fréchet Hessian of the free energy density. -/
noncomputable abbrev hessian_logZ (n : ℕ) (H : EnergySpace α) :
    EnergySpace α →L[ℝ] EnergySpace α →L[ℝ] ℝ :=
  hessian_free_energy_fderiv (α := α) n H

/-- An alias for the explicit Gibbs covariance bilinear form. -/
def gibbs_covariance (n : ℕ) (H : EnergySpace α) (h k : EnergySpace α) : ℝ :=
  hessian_free_energy (α := α) n H h k

lemma hessian_eq_covariance (n : ℕ) (H h k : EnergySpace α) :
    (hessian_logZ (α := α) n H) h k = gibbs_covariance (α := α) n H h k := by
  simpa [hessian_logZ, gibbs_covariance] using
    (hessian_free_energy_fderiv_eq_hessian_free_energy (α := α) (n := n) (H := H) (h := h) (k := k))

/-! ## Trace formulae (finite sums) -/
omit [Nonempty α] in
theorem trace_formula (n : ℕ) (H : EnergySpace α) (Cov : α → α → ℝ) :
    (∑ σ, ∑ τ, Cov σ τ * hessian_free_energy (α := α) n H
        (std_basis (α := α) σ) (std_basis (α := α) τ)) =
    (1 / (n : ℝ)) * (
      (∑ σ, (gibbs_pmf (α := α) H σ) * Cov σ σ) -
      (∑ σ, ∑ τ, (gibbs_pmf (α := α) H σ) * (gibbs_pmf (α := α) H τ) * Cov σ τ)
    ) := by
  classical
  let g : α → ℝ := fun σ => gibbs_pmf (α := α) H σ
  have hb : ∀ σ, (∑ ρ : α, g ρ * std_basis (α := α) σ ρ) = g σ := by
    intro σ
    simp [g, std_basis]
  have hc :
      ∀ σ τ, (∑ ρ : α, g ρ * std_basis (α := α) σ ρ * std_basis (α := α) τ ρ) =
        if σ = τ then g σ else 0 := by
    intro σ τ
    by_cases hστ : σ = τ
    · subst hστ
      simp [g, std_basis]
    · simp [g, std_basis, hστ]
  have hHess :
      ∀ σ τ,
        hessian_free_energy (α := α) n H (std_basis (α := α) σ) (std_basis (α := α) τ)
        = (1 / (n : ℝ)) * ((if σ = τ then g σ else 0) - g σ * g τ) := by
    intro σ τ
    simp [hessian_free_energy, hb, hc, g]
  have h_diag :
      (∑ σ, ∑ τ, Cov σ τ * (if σ = τ then g σ else 0))
        = ∑ σ, (gibbs_pmf (α := α) H σ) * Cov σ σ := by

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
  calc
    (∑ σ, ∑ τ, Cov σ τ * hessian_free_energy (α := α) n H
        (std_basis (α := α) σ) (std_basis (α := α) τ))
        = ∑ σ, ∑ τ, Cov σ τ * ((1 / (n : ℝ)) * ((if σ = τ then g σ else 0) - g σ * g τ)) := by
              refine Finset.sum_congr rfl ?_
              intro σ _hσ
              refine Finset.sum_congr rfl ?_
              intro τ _hτ
              simp [hHess σ τ]
    _ = (1 / (n : ℝ)) *
          ((∑ σ, ∑ τ, Cov σ τ * (if σ = τ then g σ else 0)) -
            (∑ σ, ∑ τ, Cov σ τ * (g σ * g τ))) := by
          -- pull out the constant `(1/n)` and distribute over subtraction
          -- (we do this by rewriting the summand, then using `sum_mul`/`sum_add_distrib`/`sum_sub_distrib`)
          have :
              (∑ σ, ∑ τ, Cov σ τ * ((1 / (n : ℝ)) * ((if σ = τ then g σ else 0) - g σ * g τ)))
                =
              (1 / (n : ℝ)) *
                (∑ σ, ∑ τ, Cov σ τ * ((if σ = τ then g σ else 0) - g σ * g τ)) := by
            -- factor the constant out of the double sum
            simp [mul_left_comm, Finset.mul_sum]
          -- now distribute the inner subtraction
          calc
            (∑ σ, ∑ τ, Cov σ τ * ((1 / (n : ℝ)) * ((if σ = τ then g σ else 0) - g σ * g τ)))
                = (1 / (n : ℝ)) *
                    (∑ σ, ∑ τ, Cov σ τ * ((if σ = τ then g σ else 0) - g σ * g τ)) := this
            _ = (1 / (n : ℝ)) *
                    ((∑ σ, ∑ τ, Cov σ τ * (if σ = τ then g σ else 0)) -
                      (∑ σ, ∑ τ, Cov σ τ * (g σ * g τ))) := by
                  -- avoid `simp` cancellation of the common factor `(1/n)`; prove the inner sum identity first
                  have hinner :
                      (∑ σ, ∑ τ, Cov σ τ * ((if σ = τ then g σ else 0) - g σ * g τ))
                        =
                      (∑ σ, ∑ τ, Cov σ τ * (if σ = τ then g σ else 0)) -
                        (∑ σ, ∑ τ, Cov σ τ * (g σ * g τ)) := by
                    -- distribute `*` over subtraction inside the finite sums
                    simp [mul_sub, Finset.sum_sub_distrib, mul_assoc, mul_left_comm, mul_comm]
                  -- now multiply both sides by the constant `(1/n)`
                  simpa using congrArg (fun t : ℝ => (1 / (n : ℝ)) * t) hinner
    _ = (1 / (n : ℝ)) *
          ((∑ σ, (gibbs_pmf (α := α) H σ) * Cov σ σ) -
            (∑ σ, ∑ τ, (gibbs_pmf (α := α) H σ) * (gibbs_pmf (α := α) H τ) * Cov σ τ)) := by
          -- Avoid cancelling the common prefactor `(1/n)` via simp (`mul_eq_mul_left_iff`).
          refine congrArg (fun t : ℝ => (1 / (n : ℝ)) * t) ?_
          have hdiag' :
              (∑ σ, ∑ τ, Cov σ τ * (if σ = τ then g σ else 0))
                = ∑ σ, (gibbs_pmf (α := α) H σ) * Cov σ σ := by
            exact h_diag
          have hprod' :
              (∑ σ, ∑ τ, Cov σ τ * (g σ * g τ))
                =
              ∑ σ, ∑ τ, (gibbs_pmf (α := α) H σ) * (gibbs_pmf (α := α) H τ) * Cov σ τ := by
            simp [g, mul_assoc, mul_left_comm, mul_comm]
          rw [hdiag', hprod']

end

end FiniteGibbs

end SpinGlass
