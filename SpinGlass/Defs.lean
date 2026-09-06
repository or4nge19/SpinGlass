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
import SpinGlass.FiniteGibbs


open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology

namespace SpinGlass

variable (N : ℕ) (β : ℝ)

/-!
# Finite-volume SK objects

Configuration space `Config N`, energy Hilbert space `EnergySpace`, partition function `Z`,
Gibbs weights, free energy density, covariance kernels, and Guerra trace identities.
Talagrand Vol. I, Ch. 1.
-/

/-! ### Configuration-agnostic partition function -/

/-- A generic finite configuration space. Concrete models will take `Σ := Config N`. -/
abbrev Conf := Type*

/-- Partition function `∑ σ, exp(-H σ)` on a finite configuration space. -/
noncomputable def Z' {α : Type*} [Fintype α] (H : α → ℝ) : ℝ :=
  ∑ σ : α, Real.exp (- H σ)

/-- Generic Gibbs weight on `Σ` (a probability mass function when normalized by `Z'`). -/
noncomputable def gibbs_pmf' {α : Type*} [Fintype α] (H : α → ℝ) (σ : α) : ℝ :=
  Real.exp (- H σ) / Z' H

/-- Generic free energy density with an explicit scaling parameter `N` (system size). -/
noncomputable def free_energy_density' {α : Type*} [Fintype α] (N : ℕ) (H : α → ℝ) : ℝ :=
  (1 / (N : ℝ)) * Real.log (Z' H)

/-! ### Configuration space and single-site spins -/

/-- Configuration space on `N` sites with single-site space `S` (default: `Bool`). -/
abbrev Config (N : ℕ) (S : Type := Bool) : Type := Fin N → S

/-- The standard Ising single-site map `Bool → ℝ`, sending `true ↦ 1` and `false ↦ -1`. -/
def isingSpin : Bool → ℝ := fun b => if b then 1 else -1

/-- `isingSpin true = 1`. -/
@[simp] lemma isingSpin_true : isingSpin true = (1 : ℝ) := by
  simp [isingSpin]

/-- `isingSpin false = -1`. -/
@[simp] lemma isingSpin_false : isingSpin false = (-1 : ℝ) := by
  simp [isingSpin]

/-- `|isingSpin b| = 1` for all `b : Bool`. -/
lemma abs_isingSpin_eq_one (b : Bool) : |isingSpin b| = (1 : ℝ) := by
  cases b <;> simp [isingSpin]

/-- `isingSpin b * isingSpin b = 1` for all `b : Bool`. -/
lemma isingSpin_mul_self (b : Bool) : isingSpin b * isingSpin b = (1 : ℝ) := by
  cases b <;> simp [isingSpin]

/-- Spin at site `i` induced by a single-site observable `spin : S → ℝ`. -/
def spinOf {S : Type} (spin : S → ℝ) (σ : Config N S) (i : Fin N) : ℝ :=
  spin (σ i)

/-- Unfolding lemma for `spinOf`. -/
@[simp] lemma spinOf_apply {S : Type} (s : S → ℝ) (σ : Config N S) (i : Fin N) :
    spinOf (N := N) s σ i = s (σ i) := by
  rfl

/-- The Ising spin at site `i` (specialization of `spinOf` to `isingSpin`). -/
def spin (σ : Config N) (i : Fin N) : ℝ :=
  spinOf (N := N) isingSpin σ i

/-- `spin` is `spinOf` specialized to `isingSpin`. -/
lemma spin_eq_spinOf (σ : Config N) (i : Fin N) :
    spin N σ i = spinOf (N := N) isingSpin σ i := by
  rfl

/-- Ising spins satisfy `|spin N σ i| = 1`. -/
lemma abs_spin_eq_one (σ : Config N) (i : Fin N) : |spin N σ i| = (1 : ℝ) := by
  simpa [spin, spinOf] using abs_isingSpin_eq_one (σ i)

/-- Ising spins satisfy `spin N σ i * spin N σ i = 1`. -/
lemma spin_mul_self (σ : Config N) (i : Fin N) : spin N σ i * spin N σ i = (1 : ℝ) := by
  simpa [spin, spinOf] using isingSpin_mul_self (σ i)

/-- Energy Hilbert space `PiLp 2 (fun _ : Config N ↦ ℝ)` (`ℓ²` on `ℝ^{2^N}`). -/
abbrev EnergySpace := PiLp 2 (fun _ : Config N => ℝ)

/-! #### Magnetization and overlap -/

/-- Magnetization induced by a single-site observable `spin : S → ℝ`. -/
def magnetizationOf {S : Type} (spin : S → ℝ) (σ : Config N S) : ℝ :=
  ∑ i : Fin N, spinOf (N := N) spin σ i

/-- Magnetization of an Ising configuration: \( \sum_{i=1}^N \sigma_i \) (with `σ_i ∈ {±1}`). -/
def magnetization (σ : Config N) : ℝ :=
  magnetizationOf (N := N) isingSpin σ

/-- `magnetization` is `magnetizationOf` specialized to `isingSpin`. -/
lemma magnetization_eq_magnetizationOf (σ : Config N) :
    magnetization N σ = magnetizationOf (N := N) isingSpin σ := by
  rfl

/-- External field energy `H_field(σ) = h ∑_i σ_i`. -/
def magnetic_field_vector (h : ℝ) : EnergySpace N :=
  WithLp.toLp 2 (fun σ : Config N => h * magnetization N σ)

noncomputable instance : InnerProductSpace ℝ (EnergySpace N) :=
  PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Config N => ℝ)

noncomputable instance : FiniteDimensional ℝ (EnergySpace N) := by
  -- `EnergySpace N` is a type synonym of the finite product `∀ σ : Config N, ℝ`.
  infer_instance

/-! ### Basis vector `std_basis` -/

noncomputable def std_basis (σ : Config N) : EnergySpace N :=
  FiniteGibbs.std_basis (α := Config N) σ

lemma inner_std_basis_apply (σ : Config N) (H : EnergySpace N) :
    inner ℝ (std_basis N σ) H = H σ := by
  simpa [std_basis] using (FiniteGibbs.inner_std_basis_apply (α := Config N) σ H)

noncomputable section

/-- Overlap induced by a single-site observable `spin : S → ℝ`. -/
def overlapOf {S : Type} (spin : S → ℝ) (σ τ : Config N S) : ℝ :=
  (1 / (N : ℝ)) * ∑ i : Fin N, (spinOf (N := N) spin σ i) * (spinOf (N := N) spin τ i)

/-- The Ising overlap (specialization of `overlapOf` to `isingSpin`). -/
def overlap (σ τ : Config N) : ℝ :=
  overlapOf (N := N) isingSpin σ τ

/-- `overlap` is `overlapOf` specialized to `isingSpin`. -/
lemma overlap_eq_overlapOf (σ τ : Config N) :
    overlap N σ τ = overlapOf (N := N) isingSpin σ τ := by
  rfl

/-- The overlap is symmetric in its two configuration arguments. -/
lemma overlapOf_comm {S : Type} (spin : S → ℝ) (σ τ : Config N S) :
    overlapOf (N := N) spin σ τ = overlapOf (N := N) spin τ σ := by
  simp [overlapOf, mul_comm]

/-- The Ising overlap is symmetric. -/
lemma overlap_comm (σ τ : Config N) : overlap N σ τ = overlap N τ σ := by
  simpa [overlap] using overlapOf_comm (N := N) (spin := isingSpin) σ τ

/-! ### Covariance Kernels -/

/-- SK covariance kernel induced by a single-site observable `spin : S → ℝ`. -/
def sk_cov_kernelOf {S : Type} (spin : S → ℝ) (σ τ : Config N S) : ℝ :=
  (N * β^2 / 2) * (overlapOf (N := N) spin σ τ)^2

/-- The SK covariance kernel induced by `spin` is symmetric. -/
lemma sk_cov_kernelOf_comm {S : Type} (spin : S → ℝ) (σ τ : Config N S) :
    sk_cov_kernelOf (N := N) (β := β) spin σ τ
      = sk_cov_kernelOf (N := N) (β := β) spin τ σ := by
  simp [sk_cov_kernelOf, overlapOf_comm]

/-- The Ising SK covariance kernel (specialization of `sk_cov_kernelOf` to `isingSpin`). -/
def sk_cov_kernel (σ τ : Config N) : ℝ :=
  (N * β^2 / 2) * (overlap N σ τ)^2

/-- `sk_cov_kernel` is `sk_cov_kernelOf` specialized to `isingSpin`. -/
lemma sk_cov_kernel_eq_sk_cov_kernelOf (σ τ : Config N) :
    sk_cov_kernel N β σ τ = sk_cov_kernelOf (N := N) (β := β) isingSpin σ τ := by
  rfl

/-- The Ising SK covariance kernel is symmetric. -/
lemma sk_cov_kernel_comm (σ τ : Config N) :
    sk_cov_kernel N β σ τ = sk_cov_kernel N β τ σ := by
  simp [sk_cov_kernel, overlap_comm]

/-- “Reference” covariance kernel induced by a single-site observable `spin : S → ℝ`. -/
def simple_cov_kernelOf {S : Type} (xi : ℝ → ℝ) (spin : S → ℝ) (σ τ : Config N S) : ℝ :=
  N * β^2 * xi (overlapOf (N := N) spin σ τ)

/-- The reference covariance kernel induced by `spin` is symmetric. -/
lemma simple_cov_kernelOf_comm {S : Type} (xi : ℝ → ℝ) (spin : S → ℝ) (σ τ : Config N S) :
    simple_cov_kernelOf (N := N) (β := β) xi spin σ τ
      = simple_cov_kernelOf (N := N) (β := β) xi spin τ σ := by
  simp [simple_cov_kernelOf, overlapOf_comm]

/-- The Ising reference covariance kernel (specialization of `simple_cov_kernelOf` to `isingSpin`). -/
def simple_cov_kernel (xi : ℝ → ℝ) (σ τ : Config N) : ℝ :=
  N * β^2 * xi (overlap N σ τ)

/-- `simple_cov_kernel` is `simple_cov_kernelOf` specialized to `isingSpin`. -/
lemma simple_cov_kernel_eq_simple_cov_kernelOf (xi : ℝ → ℝ) (σ τ : Config N) :
    simple_cov_kernel N β xi σ τ
      = simple_cov_kernelOf (N := N) (β := β) xi isingSpin σ τ := by
  rfl

/-- The Ising reference covariance kernel is symmetric. -/
lemma simple_cov_kernel_comm (xi : ℝ → ℝ) (σ τ : Config N) :
    simple_cov_kernel N β xi σ τ = simple_cov_kernel N β xi τ σ := by
  simp [simple_cov_kernel, overlap_comm]

/-! ### Thermodynamic Quantities -/

def Z (H : EnergySpace N) : ℝ := ∑ σ, Real.exp (- H σ)

def gibbs_pmf (H : EnergySpace N) (σ : Config N) : ℝ :=
  Real.exp (- H σ) / Z N H

/-! #### Bridge lemmas to the model-agnostic `FiniteGibbs` layer -/

/-- `Z` is definitionally `FiniteGibbs.Z` specialized to `α := Config N`. -/
lemma Z_eq_FiniteGibbs_Z (H : EnergySpace N) :
    Z (N := N) H = FiniteGibbs.Z (α := Config N) H := by
  rfl

/-- `gibbs_pmf` is definitionally `FiniteGibbs.gibbs_pmf` specialized to `α := Config N`. -/
lemma gibbs_pmf_eq_FiniteGibbs_gibbs_pmf (H : EnergySpace N) (σ : Config N) :
    gibbs_pmf (N := N) H σ = FiniteGibbs.gibbs_pmf (α := Config N) H σ := by
  rfl

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

/-- Free energy density `F_N(H) := (1/N) log Z_N(H)`. Talagrand Vol. I, §1.3. -/
noncomputable def free_energy_density (H : EnergySpace N) : ℝ :=
  (1 / (N : ℝ)) * Real.log (Z N H)

/-- `free_energy_density` is the specialization of the Vol II free energy `free_energy_density'`. -/
lemma free_energy_density_eq_free_energy_density' (H : EnergySpace N) :
    free_energy_density (N := N) H =
      free_energy_density' (α := Config N) N (fun σ : Config N => H σ) := by
  rfl

/-- Hessian of `free_energy_density` as a second Fréchet derivative. Talagrand Vol. I, §1.3. -/
noncomputable def hessian_free_energy_fderiv (H : EnergySpace N) :
    EnergySpace N →L[ℝ] EnergySpace N →L[ℝ] ℝ :=
  fderiv ℝ (fun H' => fderiv ℝ (free_energy_density (N := N)) H') H

lemma Z_pos (H : EnergySpace N) : 0 < Z N H := by
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
  have hZpos : 0 < Z N H := Z_pos (N := N) (H := H)
  have hterm_le :
      Real.exp (-H σ) ≤ Z N H := by
    simpa [Z] using
      (Finset.single_le_sum (s := (Finset.univ : Finset (Config N)))
        (f := fun τ => Real.exp (-H τ))
        (hf := fun τ _hτ => (Real.exp_pos _).le)
        (a := σ) (h := Finset.mem_univ σ))
  have := (div_le_one hZpos).2 hterm_le
  simpa [gibbs_pmf] using this

lemma sum_gibbs_pmf (H : EnergySpace N) : (∑ σ, gibbs_pmf N H σ) = 1 := by
  have hZ : Z N H ≠ 0 := Z_ne_zero (N := N) (H := H)
  calc
    (∑ σ, gibbs_pmf N H σ) = ∑ σ, Real.exp (- H σ) / Z N H := by rfl
    _ = ∑ σ, Real.exp (- H σ) * (Z N H)⁻¹ := by
      simp [div_eq_mul_inv]
    _ = (∑ σ, Real.exp (- H σ)) * (Z N H)⁻¹ := by
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
  simpa [gibbs_pmf_eq_FiniteGibbs_gibbs_pmf] using
    (FiniteGibbs.fderiv_gibbs_pmf_apply (α := Config N) (H := H) (h := h) σ)

lemma hasFDerivAt_grad_free_energy_density (H : EnergySpace N) :
    HasFDerivAt (fun H : EnergySpace N => grad_free_energy_density (N := N) H)
      (-((1 / (N : ℝ)) •
          ∑ σ : Config N,
            (fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H σ) H).smulRight
              (evalCLM (N := N) σ))) H := by
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
  have hZ' := (hasFDerivAt_Z (N := N) (H := H)).fderiv
  simp [hZ', evalCLM, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]

lemma fderiv_free_energy_density_apply (H h : EnergySpace N) :
    fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H) H h =
      -(1 / (N : ℝ)) * ∑ σ : Config N, (gibbs_pmf N H σ) * h σ := by
  simpa [free_energy_density, FiniteGibbs.free_energy_density, Z_eq_FiniteGibbs_Z,
    gibbs_pmf_eq_FiniteGibbs_gibbs_pmf] using
    (FiniteGibbs.fderiv_free_energy_density_apply (α := Config N) (n := N) (H := H) (h := h))

lemma fderiv_free_energy_density_eq (H : EnergySpace N) :
    fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H) H =
      grad_free_energy_density (N := N) H := by
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
  have hFE :
      (free_energy_density (N := N)) =
        fun H : EnergySpace N => (1 / (N : ℝ)) * Real.log (Z N H) := by
    rfl
  simpa [hFE, hessian_free_energy_fderiv, hessian_free_energy, Z, gibbs_pmf,
    FiniteGibbs.hessian_free_energy_fderiv, FiniteGibbs.hessian_free_energy,
    FiniteGibbs.free_energy_density, FiniteGibbs.Z, FiniteGibbs.gibbs_pmf] using
    (FiniteGibbs.hessian_free_energy_fderiv_eq_hessian_free_energy
      (α := Config N) (n := N) (H := H) (h := h) (k := k))

/-! ### Compatibility aliases -/

/-- Alias of `hessian_free_energy_fderiv`. -/
noncomputable abbrev hessian_logZ (H : EnergySpace N) :
    EnergySpace N →L[ℝ] EnergySpace N →L[ℝ] ℝ :=
  hessian_free_energy_fderiv (N := N) H

/-- Alias of the Gibbs covariance bilinear form. -/
def gibbs_covariance (H : EnergySpace N) (h k : EnergySpace N) : ℝ :=
  hessian_free_energy N H h k

/-- Fréchet Hessian of `free_energy_density` equals Gibbs covariance. Talagrand Vol. I, §1.3. -/
lemma hessian_eq_covariance (H h k : EnergySpace N) :
    (hessian_logZ (N := N) H) h k = gibbs_covariance (N := N) H h k := by
  simpa [hessian_logZ, gibbs_covariance] using
    (hessian_free_energy_fderiv_eq_hessian_free_energy (N := N) (H := H) (h := h) (k := k))

/-! ### Trace Formulae and Proofs -/

/-- Trace of `Cov` against the free-energy Hessian. Talagrand Vol. I, §1.3. -/
theorem trace_formula (H : EnergySpace N) (Cov : Config N → Config N → ℝ) :
    (∑ σ, ∑ τ, Cov σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ)) =
    (1 / (N : ℝ)) * (
      (∑ σ, (gibbs_pmf N H σ) * Cov σ σ) -
      (∑ σ, ∑ τ, (gibbs_pmf N H σ) * (gibbs_pmf N H τ) * Cov σ τ)
    ) := by
  simpa [hessian_free_energy, FiniteGibbs.hessian_free_energy, std_basis, FiniteGibbs.std_basis,
    gibbs_pmf_eq_FiniteGibbs_gibbs_pmf] using
    (FiniteGibbs.trace_formula (α := Config N) (n := N) (H := H) (Cov := Cov))

/-- Self-overlap is `1`. -/
theorem overlap_self (hN : 0 < N) (σ : Config N) : overlap N σ σ = 1 := by
  unfold overlap overlapOf
  have hsum : (∑ i : Fin N, isingSpin (σ i) * isingSpin (σ i)) = (N : ℝ) := by
    calc
      (∑ i : Fin N, isingSpin (σ i) * isingSpin (σ i))
          = ∑ _i : Fin N, (1 : ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              simpa using isingSpin_mul_self (σ i)
      _ = (N : ℝ) := by simp
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp [spinOf, hsum, hN0, div_eq_mul_inv]

/-- SK trace: `(β²/2) * (1 - ⟨R₁₂²⟩)`. Talagrand Vol. I, §1.3, Eq. (1.65). -/
theorem trace_sk (hN : 0 < N) (H : EnergySpace N) :
    (∑ σ, ∑ τ, sk_cov_kernel N β σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ)) =
    (β^2 / 2) * (1 - ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ)^2) := by
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

/-- Simple-model trace: `β² q (1 - ⟨R₁₂⟩)`. Talagrand Vol. I, §1.3. -/
theorem trace_simple (hN : 0 < N) (H : EnergySpace N) (xi : ℝ → ℝ) :
    (∑ σ, ∑ τ, simple_cov_kernel N β xi σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ)) =
    (β^2) * (xi 1 - ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * xi (overlap N σ τ)) := by
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

/-- Guerra derivative: `φ'(t) = (β²/2) * ((1/2 - ξ(1)) - ⟨R²/2 - ξ(R)⟩)`. Talagrand Vol. I, Eq. (1.65). -/
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
  simp [E_R2, E_xi]
  have hhalf :
      (2⁻¹ : ℝ) *
          (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ) ^ 2)
        =
          ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * ((overlap N σ τ) ^ 2 / 2) := by

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
