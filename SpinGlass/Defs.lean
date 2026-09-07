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

/-- The Dirac basis vector `e_σ` of `EnergySpace N`; the `Config N` instance of
`FiniteGibbs.std_basis`. -/
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

/-! ### Covariance kernels

A mean-field Hamiltonian on `N` sites whose covariance depends only on the overlap has
`𝔼[H_N(σ) H_N(τ)] = N · ξ(R_{σ,τ})` for a single function `ξ` (Talagrand Vol. II, Eq. (14.57);
for the mixed `p`-spin model `ξ x = ∑ₚ βₚ² xᵖ`). This is the only covariance kernel in the
development: `skCovXi` and `refCovXi` below are the two choices of `ξ` used in Vol. I, §1.3.
-/

/-- Overlap-driven covariance kernel `N · ξ(R_{σ,τ})` for a single-site observable `spin`.
Talagrand Vol. II, Eq. (14.57). -/
def overlapCovKernelOf {S : Type} (spin : S → ℝ) (xi : ℝ → ℝ) (σ τ : Config N S) : ℝ :=
  (N : ℝ) * xi (overlapOf (N := N) spin σ τ)

/-- Overlap-driven covariance kernel on Ising configurations. -/
abbrev overlapCovKernel (xi : ℝ → ℝ) (σ τ : Config N) : ℝ :=
  overlapCovKernelOf (N := N) isingSpin xi σ τ

/-- Unfolding lemma for `overlapCovKernel` in terms of the Ising `overlap`. -/
@[simp] lemma overlapCovKernel_apply (xi : ℝ → ℝ) (σ τ : Config N) :
    overlapCovKernel (N := N) xi σ τ = (N : ℝ) * xi (overlap N σ τ) := rfl

/-- An overlap-driven covariance kernel is symmetric. -/
lemma overlapCovKernelOf_comm {S : Type} (spin : S → ℝ) (xi : ℝ → ℝ) (σ τ : Config N S) :
    overlapCovKernelOf (N := N) spin xi σ τ = overlapCovKernelOf (N := N) spin xi τ σ := by
  simp [overlapCovKernelOf, overlapOf_comm]

/-- The SK choice of `ξ`: `ξ_SK x = β² x² / 2`. Talagrand Vol. I, §1.3. -/
def skCovXi (β : ℝ) : ℝ → ℝ := fun x => β ^ 2 * x ^ 2 / 2

/-- Guerra's replica-symmetric reference choice of `ξ`, built from a profile `xi`:
`ξ_ref x = β² · xi x`. Talagrand Vol. I, §1.3. -/
def refCovXi (β : ℝ) (xi : ℝ → ℝ) : ℝ → ℝ := fun x => β ^ 2 * xi x

/-- The SK covariance kernel `N β² R²/2`, i.e. `overlapCovKernel` at `skCovXi`. Kept
semireducible so that `simp` and `whnf` do not unfold it in the Guerra computations. -/
def sk_cov_kernel (σ τ : Config N) : ℝ :=
  overlapCovKernel (N := N) (skCovXi β) σ τ

/-- Guerra's reference covariance kernel `N β² xi(R)`, i.e. `overlapCovKernel` at `refCovXi`. -/
def simple_cov_kernel (xi : ℝ → ℝ) (σ τ : Config N) : ℝ :=
  overlapCovKernel (N := N) (refCovXi β xi) σ τ

/-- `sk_cov_kernel` is `overlapCovKernel` at `skCovXi`. -/
lemma sk_cov_kernel_def (σ τ : Config N) :
    sk_cov_kernel N β σ τ = overlapCovKernel (N := N) (skCovXi β) σ τ := rfl

/-- `simple_cov_kernel` is `overlapCovKernel` at `refCovXi`. -/
lemma simple_cov_kernel_def (xi : ℝ → ℝ) (σ τ : Config N) :
    simple_cov_kernel N β xi σ τ = overlapCovKernel (N := N) (refCovXi β xi) σ τ := rfl

/-- `sk_cov_kernel` in closed form. -/
lemma sk_cov_kernel_eq (σ τ : Config N) :
    sk_cov_kernel N β σ τ = (N * β ^ 2 / 2) * (overlap N σ τ) ^ 2 := by
  simp only [sk_cov_kernel_def, overlapCovKernel_apply, skCovXi]; ring

/-- `simple_cov_kernel` in closed form. -/
lemma simple_cov_kernel_eq (xi : ℝ → ℝ) (σ τ : Config N) :
    simple_cov_kernel N β xi σ τ = N * β ^ 2 * xi (overlap N σ τ) := by
  simp only [simple_cov_kernel_def, overlapCovKernel_apply, refCovXi]; ring

/-- The SK covariance kernel is symmetric. -/
lemma sk_cov_kernel_comm (σ τ : Config N) :
    sk_cov_kernel N β σ τ = sk_cov_kernel N β τ σ :=
  overlapCovKernelOf_comm (N := N) isingSpin (skCovXi β) σ τ

/-- The reference covariance kernel is symmetric. -/
lemma simple_cov_kernel_comm (xi : ℝ → ℝ) (σ τ : Config N) :
    simple_cov_kernel N β xi σ τ = simple_cov_kernel N β xi τ σ :=
  overlapCovKernelOf_comm (N := N) isingSpin (refCovXi β xi) σ τ

/-! ### Thermodynamic Quantities -/

/-- Partition function `Z(H) = ∑_σ exp(-H σ)`. Talagrand Vol. I, §1.1. -/
def Z (H : EnergySpace N) : ℝ := ∑ σ, Real.exp (- H σ)

/-- Gibbs probability mass function `p_H(σ) = exp(-H σ) / Z(H)`. Talagrand Vol. I, §1.1. -/
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

/-- Gibbs average \(\langle f \rangle_H\) under the Gibbs weights `gibbs_pmf`. -/
noncomputable def gibbs_average (H : EnergySpace N) (f : Config N → ℝ) : ℝ :=
  ∑ σ, gibbs_pmf N H σ * f σ

/-! #### The two-replica bracket

Talagrand writes \(\langle f \rangle\) for the average of a function of several replicas under
independent copies of the Gibbs measure (Vol. I, §1.1). Two replicas is the case that carries the
overlap `R₁₂`, and hence the whole Guerra/Parisi algebra. -/

/-- The two-replica Gibbs bracket \(\langle f \rangle_H = \sum_{σ,τ} p_H(σ)\,p_H(τ)\,f(σ,τ)\).
Talagrand Vol. I, §1.1. -/
noncomputable def gibbs_average₂ (H : EnergySpace N) (f : Config N → Config N → ℝ) : ℝ :=
  ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * f σ τ

/-! ### Free energy density and its abstract (Fréchet) Hessian -/

/-- Free energy density `F_N(H) := (1/N) log Z_N(H)`. Talagrand Vol. I, §1.3. -/
noncomputable def free_energy_density (H : EnergySpace N) : ℝ :=
  (1 / (N : ℝ)) * Real.log (Z N H)

/-- Hessian of `free_energy_density` as a second Fréchet derivative. Talagrand Vol. I, §1.3. -/
noncomputable def hessian_free_energy_fderiv (H : EnergySpace N) :
    EnergySpace N →L[ℝ] EnergySpace N →L[ℝ] ℝ :=
  fderiv ℝ (fun H' => fderiv ℝ (free_energy_density (N := N)) H') H

lemma Z_pos (H : EnergySpace N) : 0 < Z N H := FiniteGibbs.Z_pos (α := Config N) H

lemma Z_ne_zero (H : EnergySpace N) : Z N H ≠ 0 := FiniteGibbs.Z_ne_zero (α := Config N) H

lemma gibbs_pmf_pos (H : EnergySpace N) (σ : Config N) : 0 < gibbs_pmf N H σ :=
  FiniteGibbs.gibbs_pmf_pos (α := Config N) H σ

lemma gibbs_pmf_nonneg (H : EnergySpace N) (σ : Config N) : 0 ≤ gibbs_pmf N H σ :=
  FiniteGibbs.gibbs_pmf_nonneg (α := Config N) H σ

lemma gibbs_pmf_le_one (H : EnergySpace N) (σ : Config N) : gibbs_pmf N H σ ≤ 1 :=
  FiniteGibbs.gibbs_pmf_le_one (α := Config N) H σ

lemma sum_gibbs_pmf (H : EnergySpace N) : (∑ σ, gibbs_pmf N H σ) = 1 :=
  FiniteGibbs.sum_gibbs_pmf (α := Config N) H

/-! #### Two-replica bracket API -/

/-- The two-replica bracket of a constant is that constant. -/
@[simp] lemma gibbs_average₂_const (H : EnergySpace N) (c : ℝ) :
    gibbs_average₂ (N := N) H (fun _ _ => c) = c := by
  have hs1 : (∑ σ, gibbs_pmf N H σ) = 1 := sum_gibbs_pmf (N := N) (H := H)
  have hinner : ∀ σ : Config N,
      (∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * c) = gibbs_pmf N H σ * c := by
    intro σ
    calc
      (∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * c)
          = (∑ τ, gibbs_pmf N H τ) * (gibbs_pmf N H σ * c) := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun τ _ => by ring
      _ = gibbs_pmf N H σ * c := by rw [hs1, one_mul]
  calc
    gibbs_average₂ (N := N) H (fun _ _ => c)
        = ∑ σ, gibbs_pmf N H σ * c := Finset.sum_congr rfl fun σ _ => hinner σ
    _ = (∑ σ, gibbs_pmf N H σ) * c := (Finset.sum_mul ..).symm
    _ = c := by rw [hs1, one_mul]

/-- Scalars pull out of the two-replica bracket. -/
lemma gibbs_average₂_const_mul (H : EnergySpace N) (c : ℝ) (f : Config N → Config N → ℝ) :
    gibbs_average₂ (N := N) H (fun σ τ => c * f σ τ) = c * gibbs_average₂ (N := N) H f := by
  rw [gibbs_average₂, gibbs_average₂, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun τ _ => by ring

/-- The two-replica bracket commutes with subtraction. -/
lemma gibbs_average₂_sub (H : EnergySpace N) (f g : Config N → Config N → ℝ) :
    gibbs_average₂ (N := N) H (fun σ τ => f σ τ - g σ τ)
      = gibbs_average₂ (N := N) H f - gibbs_average₂ (N := N) H g := by
  rw [gibbs_average₂, gibbs_average₂, gibbs_average₂, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun τ _ => by ring

/-- The two-replica bracket preserves nonnegativity. -/
lemma gibbs_average₂_nonneg (H : EnergySpace N) {f : Config N → Config N → ℝ}
    (hf : ∀ σ τ, 0 ≤ f σ τ) : 0 ≤ gibbs_average₂ (N := N) H f :=
  Finset.sum_nonneg fun σ _ => Finset.sum_nonneg fun τ _ =>
    mul_nonneg (mul_nonneg (gibbs_pmf_nonneg (N := N) (H := H) σ)
      (gibbs_pmf_nonneg (N := N) (H := H) τ)) (hf σ τ)

/-! ### Differentiation formulas (Fréchet derivatives)

All of these are the model-agnostic `FiniteGibbs` calculus at `α := Config N`, which is in turn
the general log-sum-exp calculus of `Common.Mathlib.Analysis.SpecialFunctions.LogSumExp`. -/

/-- Evaluation at a configuration, as a continuous linear functional on `EnergySpace N`. -/
noncomputable abbrev evalCLM (σ : Config N) : EnergySpace N →L[ℝ] ℝ :=
  FiniteGibbs.evalCLM (α := Config N) σ

lemma differentiableAt_gibbs_pmf (H : EnergySpace N) (σ : Config N) :
    DifferentiableAt ℝ (fun H' => gibbs_pmf N H' σ) H :=
  FiniteGibbs.differentiableAt_gibbs_pmf (α := Config N) H σ

lemma differentiable_gibbs_pmf (σ : Config N) :
    Differentiable ℝ (fun H' => gibbs_pmf N H' σ) :=
  fun H => differentiableAt_gibbs_pmf (N := N) (H := H) σ

lemma hasFDerivAt_gibbs_pmf (H : EnergySpace N) (σ : Config N) :
    HasFDerivAt (fun H' : EnergySpace N => gibbs_pmf N H' σ)
      (fderiv ℝ (fun H' : EnergySpace N => gibbs_pmf N H' σ) H) H :=
  (differentiableAt_gibbs_pmf (N := N) (H := H) σ).hasFDerivAt

lemma fderiv_gibbs_pmf_apply (H h : EnergySpace N) (σ : Config N) :
    fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H σ) H h =
      (gibbs_pmf N H σ) *
        ((∑ τ : Config N, (gibbs_pmf N H τ) * h τ) - h σ) :=
  FiniteGibbs.fderiv_gibbs_pmf_apply (α := Config N) H h σ

lemma fderiv_free_energy_density_apply (H h : EnergySpace N) :
    fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H) H h =
      -(1 / (N : ℝ)) * ∑ σ : Config N, (gibbs_pmf N H σ) * h σ :=
  FiniteGibbs.fderiv_free_energy_density_apply (α := Config N) N H h

/-- The Gibbs covariance bilinear form at system size `N`: the Hessian of the free-energy
density, written out. -/
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

/-- **Overlap-driven trace identity.** For a covariance kernel `N · ξ(R_{σ,τ})` the trace against
the free-energy Hessian collapses to `ξ 1 - ⟨ξ(R₁₂)⟩`. This is the single trace identity of the
development; the SK and replica-symmetric traces are the two instances of `ξ`.
Talagrand Vol. I, §1.3, Eq. (1.65). -/
theorem trace_overlapCovKernel (hN : 0 < N) (H : EnergySpace N) (xi : ℝ → ℝ) :
    (∑ σ, ∑ τ, overlapCovKernel (N := N) xi σ τ *
        hessian_free_energy N H (std_basis N σ) (std_basis N τ))
      = xi 1 - gibbs_average₂ (N := N) H (fun σ τ => xi (overlap N σ τ)) := by
  simp only [gibbs_average₂]
  have hs1 : (∑ σ, gibbs_pmf N H σ) = 1 := sum_gibbs_pmf (N := N) (H := H)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [trace_formula (N := N) (H := H) (Cov := overlapCovKernel (N := N) xi)]
  -- Diagonal: `R_{σ,σ} = 1`, so the diagonal sum is `N · ξ 1`.
  have hdiag :
      (∑ σ, gibbs_pmf N H σ * overlapCovKernel (N := N) xi σ σ) = (N : ℝ) * xi 1 := by
    have hover : ∀ σ : Config N, overlapCovKernel (N := N) xi σ σ = (N : ℝ) * xi 1 := by
      intro σ
      simp only [overlapCovKernel_apply, overlap_self (N := N) (hN := hN) σ]
    calc
      (∑ σ, gibbs_pmf N H σ * overlapCovKernel (N := N) xi σ σ)
          = ∑ σ, gibbs_pmf N H σ * ((N : ℝ) * xi 1) := by
              exact Finset.sum_congr rfl fun σ _ => by rw [hover σ]
      _ = (∑ σ, gibbs_pmf N H σ) * ((N : ℝ) * xi 1) := (Finset.sum_mul ..).symm
      _ = (N : ℝ) * xi 1 := by rw [hs1, one_mul]
  -- Off-diagonal: the `N` factors out of the double sum.
  have hoff :
      (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * overlapCovKernel (N := N) xi σ τ)
        = (N : ℝ) * ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * xi (overlap N σ τ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [overlapCovKernel_apply]
    ring
  rw [hdiag, hoff]
  field_simp

/-- **Guerra's interpolation identity, algebraic core.** For two overlap-driven covariance kernels
the half-difference of the Hessian traces is governed by `ξ₁ - ξ₂` alone. Specializing
`ξ₁ = skCovXi β` and `ξ₂ = refCovXi β xi` gives Talagrand Vol. I, Eq. (1.65). -/
theorem half_trace_sub_overlapCovKernel (hN : 0 < N) (H : EnergySpace N) (xi₁ xi₂ : ℝ → ℝ) :
    (1 / 2 : ℝ) *
        ((∑ σ, ∑ τ, overlapCovKernel (N := N) xi₁ σ τ *
              hessian_free_energy N H (std_basis N σ) (std_basis N τ))
          - (∑ σ, ∑ τ, overlapCovKernel (N := N) xi₂ σ τ *
              hessian_free_energy N H (std_basis N σ) (std_basis N τ)))
      = (1 / 2 : ℝ) *
          ((xi₁ 1 - xi₂ 1)
            - gibbs_average₂ (N := N) H
                (fun σ τ => xi₁ (overlap N σ τ) - xi₂ (overlap N σ τ))) := by
  rw [trace_overlapCovKernel (N := N) (hN := hN) (H := H) (xi := xi₁),
      trace_overlapCovKernel (N := N) (hN := hN) (H := H) (xi := xi₂),
      gibbs_average₂_sub (N := N) (H := H)
        (f := fun σ τ => xi₁ (overlap N σ τ)) (g := fun σ τ => xi₂ (overlap N σ τ))]
  ring

end
end SpinGlass
