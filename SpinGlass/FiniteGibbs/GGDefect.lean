/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.FiniteGibbs.Cavity

/-!
# The Ghirlanda–Guerra defect is the energy–observable covariance

The Ghirlanda–Guerra identities are not exact at finite volume. This file identifies *exactly*
what the defect is: for a centered Gaussian Hamiltonian whose covariance kernel has constant
diagonal `c σ σ = d` — the case of every mixed `p`-spin model, where `c σ τ = N ξ(R_{στ})` and so
`c σ σ = N ξ(1)` — the failure of the Ghirlanda–Guerra identity for a test function `f` of `n`
replicas equals

`𝔼⟨H_{σⁱ} f⟩ - 𝔼⟨f⟩ · 𝔼⟨H⟩`,

the covariance between the Hamiltonian evaluated at a replica and the observable. In particular
the identities hold exactly precisely when the energy decorrelates from every observable, which is
what self-averaging of the Hamiltonian provides asymptotically.

The proof is the cavity identity `integral_gibbs_average_n_det_energy_mul` used twice: once at
`(n, f)` to expand `𝔼⟨f · c(σⁱ, ·)⟩`, and once at `(1, 1)` to evaluate `𝔼⟨c(σ¹,σ²)⟩`. Splitting
off the diagonal term `l = i` is where the constant-diagonal hypothesis enters, and it is the only
place it is used.

## Main statements

- `FiniteGibbs.integrable_gibbs_average_n_det`: replica averages are integrable.
- `FiniteGibbs.gibbs_average_one`: the one-replica average is the Gibbs average.
- `FiniteGibbs.ghirlandaGuerra_defect`: **the defect identity**.
-/

open MeasureTheory ProbabilityTheory BigOperators
open scoped InnerProductSpace ContDiff

namespace SpinGlass

namespace FiniteGibbs

noncomputable section

variable {α : Type*} [Fintype α] [Nonempty α]

omit [Nonempty α] in
/-- The Dirac basis vectors are unit vectors. -/
lemma norm_std_basis (ρ : α) : ‖std_basis (α := α) ρ‖ = 1 := by
  classical
  rw [std_basis_eq_single ρ]
  simp

omit [Nonempty α] in
/-- The one-replica Gibbs average is the ordinary Gibbs average. -/
lemma gibbs_average_one (H : EnergySpace α) (g : ReplicaFun (α := α) 1) :
    gibbs_average_n_det (α := α) (n := 1) H g
      = ∑ τ : α, g (fun _ => τ) * gibbs_pmf (α := α) H τ := by
  classical
  rw [gibbs_average_n_det, ← Equiv.sum_comp (Equiv.funUnique (Fin 1) α).symm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have huniq : ((Equiv.funUnique (Fin 1) α).symm τ) = (fun _ : Fin 1 => τ) := funext fun _ => rfl
  rw [huniq]
  simp

@[simp] lemma gibbs_average_one_const (H : EnergySpace α) :
    gibbs_average_n_det (α := α) (n := 1) H (fun _ => (1 : ℝ)) = 1 := by
  rw [gibbs_average_one]
  simpa using sum_gibbs_pmf (α := α) H

variable {μ : Measure (EnergySpace α)} [IsGaussian μ]

omit [Nonempty α] [IsGaussian μ] in
/-- The covariance kernel of a Gaussian Hamiltonian law, in the Dirac basis. Every entry is
bounded by the operator norm of the covariance operator, because the Dirac vectors are unit
vectors. -/
lemma abs_covarianceOperator_std_basis_apply_le (ρ τ : α) :
    |(covarianceOperator μ (std_basis (α := α) ρ)) τ| ≤ ‖covarianceOperator μ‖ := by
  refine le_trans (abs_apply_le_norm (α := α) _ τ) ?_
  calc ‖covarianceOperator μ (std_basis (α := α) ρ)‖
      ≤ ‖covarianceOperator μ‖ * ‖std_basis (α := α) ρ‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖covarianceOperator μ‖ := by rw [norm_std_basis, mul_one]

/-- A replica average of an `H`-dependent observable is integrable as soon as the observable is
continuous in `H` and uniformly bounded. -/
lemma integrable_gibbs_average_n_det_of_bounded (m : ℕ)
    (g : EnergySpace α → ReplicaFun (α := α) m)
    (hg : Continuous fun H : EnergySpace α => gibbs_average_n_det (α := α) (n := m) H (g H))
    {B : ℝ} (hB : ∀ H σs, ‖g H σs‖ ≤ B) :
    Integrable (fun H : EnergySpace α => gibbs_average_n_det (α := α) (n := m) H (g H)) μ := by
  classical
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (fun _ => Classical.arbitrary α))
  have hbound : ∀ H : EnergySpace α,
      |gibbs_average_n_det (α := α) (n := m) H (g H)|
        ≤ (Fintype.card (ReplicaSpace (α := α) m) : ℝ) * B := by
    intro H
    refine le_trans (abs_gibbs_average_n_det_le_sum_abs (α := α) m H (g H)) ?_
    calc (∑ σs : ReplicaSpace (α := α) m, ‖g H σs‖)
        ≤ ∑ _σs : ReplicaSpace (α := α) m, B := Finset.sum_le_sum fun σs _ => hB H σs
      _ = (Fintype.card (ReplicaSpace (α := α) m) : ℝ) * B := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact ProbabilityTheory.IsGaussian.integrable_of_abs_le_mul_one_add_norm_pow (μ := μ)
    hg.measurable (C := (Fintype.card (ReplicaSpace (α := α) m) : ℝ) * B) (m := 0)
    (by positivity) (fun H => by simpa using hbound H)


/-! ### Splitting the diagonal term out of the cavity identity -/

/-- **The Gibbs average of a kernel against a fresh replica**: `⟨c ρ ·⟩ = ∑_τ G_τ c(ρ, τ)`.

This is Talagrand's `⟨c(ρ, σ^{n+1})⟩`: the kernel evaluated at `ρ` and an independent extra draw
from the Gibbs measure. It involves no Gaussian structure at all — only the Gibbs weights and the
kernel — and it is (obviously) linear in the kernel, which is what lets the Ghirlanda–Guerra
combination of a *sum* of kernels be split into the combinations of the summands. -/
def freshKernelAvg (H : EnergySpace α) (c : α → α → ℝ) (ρ : α) : ℝ :=
  ∑ τ : α, gibbs_pmf (α := α) H τ * c ρ τ

/-- **The covariance kernel of a Gaussian Hamiltonian law along a family of directions**:
`c_w(σ, τ) = Cov(⟪H, w σ⟫, H τ)`.

Taking `w = e_·` gives the Hamiltonian's own covariance kernel `Cov(H σ, H τ)`. Taking
`w σ = Wᵀ e_σ` for a continuous linear `W` gives the *cross* kernel between the component `W H` of
the disorder and the Hamiltonian — which is what isolates a single `p`-spin term of a mixed model,
and which is in general **not symmetric**. -/
def covKernel (μ : Measure (EnergySpace α)) (w : α → EnergySpace α) (σ τ : α) : ℝ :=
  (covarianceOperator μ (w σ)) τ

omit [Nonempty α] in
@[simp] lemma covKernel_apply (μ : Measure (EnergySpace α)) (w : α → EnergySpace α) (σ τ : α) :
    covKernel μ w σ τ = (covarianceOperator μ (w σ)) τ := rfl

/-- **The component field of the disorder in a family of directions**: the vector whose value at
`σ` is `⟪x, w σ⟫`.

The disorder `x` lives in an arbitrary real inner-product space. For `Ω = EnergySpace α` and
`w σ = Wᵀ e_σ` with `W` a continuous linear map this is `W H`, the corresponding linear component
of the disorder; for `w = e_·` it is `H` itself; for `Ω = E × E` and `w σ = (0, e_σ)` it is the
second summand of a Hamiltonian built from two independent pieces. Packaging it as a vector of
`EnergySpace α` is what lets the whole finite-volume calculus — written for the energy — be reused
verbatim for a component. -/
def componentField {Ω : Type*} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω]
    (w : α → Ω) (x : Ω) : EnergySpace α :=
  WithLp.toLp 2 fun σ => ⟪x, w σ⟫_ℝ

omit [Fintype α] [Nonempty α] in
@[simp] lemma componentField_apply {Ω : Type*} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω]
    (w : α → Ω) (x : Ω) (σ : α) :
    (componentField (α := α) w x) σ = ⟪x, w σ⟫_ℝ := rfl

omit [Nonempty α] in
/-- The component field in the coordinate directions is the disorder itself. -/
@[simp] lemma componentField_std_basis (H : EnergySpace α) :
    componentField (α := α) (fun σ => std_basis (α := α) σ) H = H := by
  refine WithLp.ofLp_injective (p := 2) (funext fun σ => ?_)
  rw [componentField_apply, real_inner_comm]
  exact inner_std_basis_apply (α := α) σ H

omit [Nonempty α] [IsGaussian μ] in
/-- `freshKernelAvg` is additive in the kernel. -/
lemma freshKernelAvg_add (H : EnergySpace α) (c c' : α → α → ℝ) (ρ : α) :
    freshKernelAvg (α := α) H (c + c') ρ
      = freshKernelAvg (α := α) H c ρ + freshKernelAvg (α := α) H c' ρ := by
  simp only [freshKernelAvg, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun τ _ => by ring

omit [Nonempty α] [IsGaussian μ] in
/-- `freshKernelAvg` is homogeneous in the kernel. -/
lemma freshKernelAvg_smul (H : EnergySpace α) (r : ℝ) (c : α → α → ℝ) (ρ : α) :
    freshKernelAvg (α := α) H (r • c) ρ = r * freshKernelAvg (α := α) H c ρ := by
  simp only [freshKernelAvg, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun τ _ => by ring

omit [IsGaussian μ] in
lemma continuous_freshKernelAvg (c : α → α → ℝ) (ρ : α) :
    Continuous fun H : EnergySpace α => freshKernelAvg (α := α) H c ρ :=
  continuous_finsetSum _ fun τ _ =>
    ((contDiff_gibbs_pmf (α := α) τ).continuous).mul continuous_const

omit [IsGaussian μ] in
/-- The fresh-replica average of a kernel is bounded by the kernel: the Gibbs weights sum to one. -/
lemma abs_freshKernelAvg_le {c : α → α → ℝ} {M : ℝ} (hc : ∀ σ τ : α, |c σ τ| ≤ M)
    (H : EnergySpace α) (ρ : α) : |freshKernelAvg (α := α) H c ρ| ≤ M := by
  classical
  have h1 : |freshKernelAvg (α := α) H c ρ| ≤ ∑ τ : α, gibbs_pmf (α := α) H τ * |c ρ τ| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq (Finset.sum_congr rfl fun τ _ => ?_))
    rw [abs_mul, abs_of_nonneg (gibbs_pmf_nonneg (α := α) H τ)]
  refine h1.trans ?_
  calc (∑ τ : α, gibbs_pmf (α := α) H τ * |c ρ τ|)
      ≤ ∑ τ : α, gibbs_pmf (α := α) H τ * M :=
        Finset.sum_le_sum fun τ _ =>
          mul_le_mul_of_nonneg_left (hc ρ τ) (gibbs_pmf_nonneg (α := α) H τ)
    _ = M := by rw [← Finset.sum_mul, sum_gibbs_pmf, one_mul]

omit [Nonempty α] [IsGaussian μ] in
/-- Every entry of a cross-covariance kernel is bounded by the operator norm times the size of the
direction. -/
lemma abs_covKernel_le {w : α → EnergySpace α} {Mw : ℝ} (hw : ∀ σ : α, ‖w σ‖ ≤ Mw) (σ τ : α) :
    |covKernel μ w σ τ| ≤ ‖covarianceOperator μ‖ * Mw := by
  calc |covKernel μ w σ τ| ≤ ‖covarianceOperator μ (w σ)‖ :=
        abs_apply_le_norm (α := α) (covarianceOperator μ (w σ)) τ
    _ ≤ ‖covarianceOperator μ‖ * ‖w σ‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖covarianceOperator μ‖ * Mw := mul_le_mul_of_nonneg_left (hw σ) (norm_nonneg _)

/-- The Gibbs average of the Hamiltonian's own covariance against a fresh replica: `⟨c ρ ·⟩`. -/
noncomputable def freshCov (μ : Measure (EnergySpace α)) (H : EnergySpace α) (ρ : α) : ℝ :=
  freshKernelAvg (α := α) H (covKernel μ (std_basis (α := α))) ρ

omit [Nonempty α] [IsGaussian μ] in
lemma freshCov_apply (H : EnergySpace α) (ρ : α) :
    freshCov μ H ρ
      = ∑ τ : α, gibbs_pmf (α := α) H τ * (covarianceOperator μ (std_basis (α := α) ρ)) τ := rfl

omit [IsGaussian μ] in
lemma continuous_freshCov (ρ : α) :
    Continuous fun H : EnergySpace α => freshCov μ H ρ :=
  continuous_finsetSum _ fun τ _ =>
    ((contDiff_gibbs_pmf (α := α) τ).continuous).mul continuous_const

omit [IsGaussian μ] in
lemma abs_freshCov_le (H : EnergySpace α) (ρ : α) :
    |freshCov μ H ρ| ≤ ‖covarianceOperator μ‖ := by
  have h := Real.abs_sum_softmax_mul_le (-H) (covarianceOperator μ (std_basis (α := α) ρ))
  refine le_trans (by simpa [freshCov_apply, gibbs_pmf_eq_softmax] using h) ?_
  calc ‖covarianceOperator μ (std_basis (α := α) ρ)‖
      ≤ ‖covarianceOperator μ‖ * ‖std_basis (α := α) ρ‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖covarianceOperator μ‖ := by rw [norm_std_basis, mul_one]

/-! ### Splitting the diagonal term out of the cavity identity -/

/-- **The cavity identity with the diagonal term separated, in an arbitrary direction family.**
When the cross-covariance kernel `c_w(σ,τ) = Cov(⟪H, w σ⟫, H τ)` has constant diagonal
`c_w σ σ = d`, the `l = i` summand of the cavity identity is `d ⟨f⟩`, and the rest of the sum runs
over `l ≠ i`. -/
theorem integral_gibbs_average_n_det_inner_mul_erase
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0) (w : α → EnergySpace α) {d : ℝ}
    (hdiag : ∀ σ : α, (covarianceOperator μ (w σ)) σ = d)
    (m : ℕ) (f : ReplicaFun (α := α) m) (i : Fin m) :
    (∫ H : EnergySpace α,
        gibbs_average_n_det (α := α) (n := m) H (fun σs => ⟪H, w (σs i)⟫_ℝ * f σs) ∂μ)
      = ∫ H : EnergySpace α,
          ((m : ℝ) * gibbs_average_n_det (α := α) (n := m) H
                (fun σs => f σs * freshKernelAvg (α := α) H (covKernel μ w) (σs i))
            - d * gibbs_average_n_det (α := α) (n := m) H f
            - ∑ l ∈ Finset.univ.erase i, gibbs_average_n_det (α := α) (n := m) H
                (fun σs => f σs * covKernel μ w (σs i) (σs l))) ∂μ := by
  classical
  rw [integral_gibbs_average_n_det_inner_mul (μ := μ) hmean0 w m f i]
  refine integral_congr_ae (Filter.Eventually.of_forall fun H => ?_)
  have hsplit : (∑ l : Fin m, gibbs_average_n_det (α := α) (n := m) H
        (fun σs => f σs * (covarianceOperator μ (w (σs i))) (σs l)))
      = gibbs_average_n_det (α := α) (n := m) H
          (fun σs => f σs * (covarianceOperator μ (w (σs i))) (σs i))
        + ∑ l ∈ Finset.univ.erase i, gibbs_average_n_det (α := α) (n := m) H
            (fun σs => f σs * (covarianceOperator μ (w (σs i))) (σs l)) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have hdiagAvg : gibbs_average_n_det (α := α) (n := m) H
      (fun σs => f σs * (covarianceOperator μ (w (σs i))) (σs i))
      = d * gibbs_average_n_det (α := α) (n := m) H f := by
    rw [gibbs_average_n_det, gibbs_average_n_det, Finset.mul_sum]
    exact Finset.sum_congr rfl fun σs _ => by rw [hdiag (σs i)]; ring
  simp only [freshKernelAvg, covKernel_apply]
  rw [hsplit, hdiagAvg]
  ring

/-- **The cavity identity with the diagonal term separated.** The coordinate case `w = e_·` of
`SpinGlass.FiniteGibbs.integral_gibbs_average_n_det_inner_mul_erase`. -/
theorem integral_gibbs_average_n_det_energy_mul_erase
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0) {d : ℝ}
    (hdiag : ∀ σ : α, (covarianceOperator μ (std_basis (α := α) σ)) σ = d)
    (m : ℕ) (f : ReplicaFun (α := α) m) (i : Fin m) :
    (∫ H : EnergySpace α,
        gibbs_average_n_det (α := α) (n := m) H (fun σs => H (σs i) * f σs) ∂μ)
      = ∫ H : EnergySpace α,
          ((m : ℝ) * gibbs_average_n_det (α := α) (n := m) H
                (fun σs => f σs * freshCov μ H (σs i))
            - d * gibbs_average_n_det (α := α) (n := m) H f
            - ∑ l ∈ Finset.univ.erase i, gibbs_average_n_det (α := α) (n := m) H
                (fun σs => f σs
                  * (covarianceOperator μ (std_basis (α := α) (σs i))) (σs l))) ∂μ := by
  have hco : ∀ (H : EnergySpace α) (σ : α), ⟪H, std_basis (α := α) σ⟫_ℝ = H σ := fun H σ => by
    rw [real_inner_comm]; exact inner_std_basis_apply (α := α) σ H
  have h := integral_gibbs_average_n_det_inner_mul_erase (μ := μ) hmean0
    (fun σ => std_basis (α := α) σ) hdiag m f i
  rw [show (∫ H : EnergySpace α, gibbs_average_n_det (α := α) (n := m) H
        (fun σs => ⟪H, std_basis (α := α) (σs i)⟫_ℝ * f σs) ∂μ)
      = ∫ H : EnergySpace α, gibbs_average_n_det (α := α) (n := m) H
        (fun σs => H (σs i) * f σs) ∂μ from
    integral_congr_ae (Filter.Eventually.of_forall fun H =>
      congrArg (gibbs_average_n_det (α := α) (n := m) H)
        (funext fun σs => by rw [hco]))] at h
  exact h

/-! ### The mean field -/

/-- **The mean of a component field is its mean cross-covariance with a fresh replica, minus the
diagonal**: `𝔼⟨⟪H, w ·⟫⟩ = 𝔼⟨c_w(σ¹, σ²)⟩ - d`. This is
`integral_gibbs_average_n_det_inner_mul_erase` at one replica and the constant test function. -/
theorem integral_gibbs_average_one_inner
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0) {w : α → EnergySpace α} {Mw : ℝ}
    (hw : ∀ σ : α, ‖w σ‖ ≤ Mw) {d : ℝ}
    (hdiag : ∀ σ : α, (covarianceOperator μ (w σ)) σ = d) :
    (∫ H : EnergySpace α,
        gibbs_average_n_det (α := α) (n := 1) H (fun τs => ⟪H, w (τs 0)⟫_ℝ) ∂μ)
      = (∫ H : EnergySpace α, gibbs_average_n_det (α := α) (n := 1) H
          (fun τs => freshKernelAvg (α := α) H (covKernel μ w) (τs 0)) ∂μ) - d := by
  classical
  have hone := integral_gibbs_average_n_det_inner_mul_erase (μ := μ) hmean0 w hdiag 1
    (fun _ => (1 : ℝ)) 0
  have herase : (Finset.univ.erase (0 : Fin 1)) = ∅ := by
    ext l
    simp [Subsingleton.elim l 0]
  have hbd := abs_freshKernelAvg_le (abs_covKernel_le (μ := μ) hw)
  have hI1' : Integrable
      (fun H : EnergySpace α => gibbs_average_n_det (α := α) (n := 1) H
        (fun τs => freshKernelAvg (α := α) H (covKernel μ w) (τs 0))) μ := by
    refine integrable_gibbs_average_n_det_of_bounded (μ := μ) 1
      (fun H τs => freshKernelAvg (α := α) H (covKernel μ w) (τs 0)) ?_
      (B := ‖covarianceOperator μ‖ * Mw) fun H τs => ?_
    · simp only [gibbs_average_n_det]
      exact continuous_finsetSum _ fun τs _ =>
        ((continuous_freshKernelAvg (α := α) (covKernel μ w) (τs 0)).mul
          (continuous_finsetProd _ fun l _ => (contDiff_gibbs_pmf (α := α) (τs l)).continuous))
    · simpa [Real.norm_eq_abs] using hbd H (τs 0)
  rw [show (fun H : EnergySpace α => gibbs_average_n_det (α := α) (n := 1) H
        (fun τs => ⟪H, w (τs 0)⟫_ℝ)) = fun H : EnergySpace α =>
      gibbs_average_n_det (α := α) (n := 1) H (fun τs => ⟪H, w (τs 0)⟫_ℝ * (1 : ℝ)) from by
    funext H; simp]
  rw [hone, herase]
  simp only [Finset.sum_empty, sub_zero, Nat.cast_one, one_mul, gibbs_average_one_const,
    mul_one, one_mul]
  rw [MeasureTheory.integral_sub hI1' (integrable_const d), MeasureTheory.integral_const]
  simp

/-- **The mean energy is the mean two-replica covariance, minus the diagonal**:
`𝔼⟨H⟩ = 𝔼⟨c(σ¹, σ²)⟩ - d`. The coordinate case `w = e_·` of
`SpinGlass.FiniteGibbs.integral_gibbs_average_one_inner`. -/
theorem integral_gibbs_average_one_energy
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0) {d : ℝ}
    (hdiag : ∀ σ : α, (covarianceOperator μ (std_basis (α := α) σ)) σ = d) :
    (∫ H : EnergySpace α,
        gibbs_average_n_det (α := α) (n := 1) H (fun τs => H (τs 0)) ∂μ)
      = (∫ H : EnergySpace α,
          gibbs_average_n_det (α := α) (n := 1) H (fun τs => freshCov μ H (τs 0)) ∂μ) - d := by
  have hco : ∀ (H : EnergySpace α) (σ : α), ⟪H, std_basis (α := α) σ⟫_ℝ = H σ := fun H σ => by
    rw [real_inner_comm]; exact inner_std_basis_apply (α := α) σ H
  have h := integral_gibbs_average_one_inner (μ := μ) hmean0
    (w := fun σ => std_basis (α := α) σ) (Mw := 1)
    (fun σ => le_of_eq (norm_std_basis (α := α) σ)) hdiag
  rw [show (∫ H : EnergySpace α, gibbs_average_n_det (α := α) (n := 1) H
        (fun τs => ⟪H, std_basis (α := α) (τs 0)⟫_ℝ) ∂μ)
      = ∫ H : EnergySpace α, gibbs_average_n_det (α := α) (n := 1) H
        (fun τs => H (τs 0)) ∂μ from
    integral_congr_ae (Filter.Eventually.of_forall fun H =>
      congrArg (gibbs_average_n_det (α := α) (n := 1) H)
        (funext fun τs => hco H (τs 0)))] at h
  exact h

/-! ### The component cavity identity for a linear-image Hamiltonian -/

section LinearImage

variable {Ω : Type*} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω] [CompleteSpace Ω]
variable [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω]
variable {P : Measure Ω} [IsGaussian P]

/-- **The cross-covariance kernel of a component of the disorder against a linear-image
Hamiltonian**: `c_{A,w}(σ, τ) = Cov(⟪x, w σ⟫, (A x) τ)`.

With `Ω = E × E`, `A (x, y) = x + t y` and `w σ = (0, e_σ)` this is `t` times the covariance of the
second summand — the kernel of a single `p`-spin term of a mixed Hamiltonian. -/
def crossKernel (P : Measure Ω) (A : Ω →L[ℝ] EnergySpace α) (w : α → Ω) (σ τ : α) : ℝ :=
  (A (covarianceOperator P (w σ))) τ

omit [Fintype α] [Nonempty α] [SecondCountableTopology Ω] in
@[simp] lemma crossKernel_apply (P : Measure Ω) (A : Ω →L[ℝ] EnergySpace α) (w : α → Ω)
    (σ τ : α) : crossKernel P A w σ τ = (A (covarianceOperator P (w σ))) τ := rfl

omit [Nonempty α] [SecondCountableTopology Ω] [IsGaussian P] in
/-- Every entry of a cross-covariance kernel is bounded. -/
lemma abs_crossKernel_le (A : Ω →L[ℝ] EnergySpace α) {w : α → Ω} {Mw : ℝ}
    (hw : ∀ σ : α, ‖w σ‖ ≤ Mw) (σ τ : α) :
    |crossKernel P A w σ τ| ≤ ‖A‖ * (‖covarianceOperator P‖ * Mw) := by
  calc |crossKernel P A w σ τ| ≤ ‖A (covarianceOperator P (w σ))‖ :=
        abs_apply_le_norm (α := α) (A (covarianceOperator P (w σ))) τ
    _ ≤ ‖A‖ * ‖covarianceOperator P (w σ)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖A‖ * (‖covarianceOperator P‖ * ‖w σ‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg A)
    _ ≤ ‖A‖ * (‖covarianceOperator P‖ * Mw) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hw σ) (norm_nonneg _)) (norm_nonneg A)

omit [Nonempty α] in
/-- **The Hamiltonian's own covariance kernel is the cross kernel at the adjoint directions.**

If `w σ` represents the `σ`-th coordinate of the Hamiltonian, in the sense that
`⟪p, w σ⟫ = (A p) σ` for every disorder `p` — that is, `w = Aᵀ e_·` — then the covariance kernel of
the *law of the Hamiltonian* is the cross kernel of `w`:

`Cov((A x) σ, (A x) τ) = (A (C_P (w σ))) τ`.

No adjoint is needed in the statement or the proof: the defining property of `w` is used twice,
once on each side. -/
theorem covarianceOperator_map_std_basis_eq_crossKernel
    (A : Ω →L[ℝ] EnergySpace α) {w : α → Ω}
    (hw : ∀ (p : Ω) (σ : α), ⟪p, w σ⟫_ℝ = (A p) σ) (σ τ : α) :
    (covarianceOperator (P.map A) (std_basis (α := α) σ)) τ = crossKernel P A w σ τ := by
  classical
  have hmemP : MemLp (id : Ω → Ω) 2 P := ProbabilityTheory.IsGaussian.memLp_two_id
  have hgauss : ProbabilityTheory.IsGaussian (P.map A) :=
    ProbabilityTheory.isGaussian_map (μ := P) A
  have hmemA : MemLp (id : EnergySpace α → EnergySpace α) 2 (P.map A) :=
    ProbabilityTheory.IsGaussian.memLp_two_id
  -- the left-hand side, as an uncentered second moment
  have hL : (covarianceOperator (P.map A) (std_basis (α := α) σ)) τ
      = ∫ z : EnergySpace α, ⟪std_basis (α := α) σ, z⟫_ℝ * ⟪std_basis (α := α) τ, z⟫_ℝ
          ∂(P.map A) := by
    rw [show (covarianceOperator (P.map A) (std_basis (α := α) σ)) τ
        = inner ℝ (covarianceOperator (P.map A) (std_basis (α := α) σ))
            (std_basis (α := α) τ) from by
      rw [real_inner_comm, inner_std_basis_apply]]
    exact ProbabilityTheory.covarianceOperator_inner hmemA _ _
  have hLmap : (∫ z : EnergySpace α, ⟪std_basis (α := α) σ, z⟫_ℝ
        * ⟪std_basis (α := α) τ, z⟫_ℝ ∂(P.map A))
      = ∫ p : Ω, (A p) σ * (A p) τ ∂P := by
    rw [MeasureTheory.integral_map (μ := P) (φ := A)
      (f := fun z : EnergySpace α => ⟪std_basis (α := α) σ, z⟫_ℝ
        * ⟪std_basis (α := α) τ, z⟫_ℝ)
      A.continuous.measurable.aemeasurable
      (((continuous_const.inner continuous_id).mul
        (continuous_const.inner continuous_id)).aestronglyMeasurable)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => by
      simp only [inner_std_basis_apply])
  -- the right-hand side, likewise
  have hR : crossKernel P A w σ τ = ∫ p : Ω, (A p) σ * (A p) τ ∂P := by
    rw [crossKernel, ← hw (covarianceOperator P (w σ)) τ,
      ProbabilityTheory.covarianceOperator_inner hmemP]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    change ⟪w σ, p⟫_ℝ * ⟪w τ, p⟫_ℝ = (A p) σ * (A p) τ
    rw [real_inner_comm p (w σ), real_inner_comm p (w τ), hw p σ, hw p τ]
  rw [hL, hLmap, hR]

/-- **The component cavity identity with the diagonal term separated.** When the cross kernel has
constant diagonal `c_{A,w} σ σ = d`, the `l = i` summand is `d ⟨f⟩` and the rest of the sum runs
over `l ≠ i`. -/
theorem integral_gibbs_average_n_det_inner_mul_comp_erase
    (hmean0 : (∫ x : Ω, x ∂P) = 0) (A : Ω →L[ℝ] EnergySpace α) (c₀ : EnergySpace α)
    (w : α → Ω) {d : ℝ} (hdiag : ∀ σ : α, crossKernel P A w σ σ = d)
    (m : ℕ) (f : ReplicaFun (α := α) m) (i : Fin m) :
    (∫ x : Ω, gibbs_average_n_det (α := α) (n := m) (A x + c₀)
        (fun σs => ⟪x, w (σs i)⟫_ℝ * f σs) ∂P)
      = ∫ x : Ω,
          ((m : ℝ) * gibbs_average_n_det (α := α) (n := m) (A x + c₀)
                (fun σs => f σs
                  * freshKernelAvg (α := α) (A x + c₀) (crossKernel P A w) (σs i))
            - d * gibbs_average_n_det (α := α) (n := m) (A x + c₀) f
            - ∑ l ∈ Finset.univ.erase i, gibbs_average_n_det (α := α) (n := m) (A x + c₀)
                (fun σs => f σs * crossKernel P A w (σs i) (σs l))) ∂P := by
  classical
  rw [integral_gibbs_average_n_det_inner_mul_comp (P := P) hmean0 A c₀ w m f i]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hsplit : (∑ l : Fin m, gibbs_average_n_det (α := α) (n := m) (A x + c₀)
        (fun σs => f σs * (A (covarianceOperator P (w (σs i)))) (σs l)))
      = gibbs_average_n_det (α := α) (n := m) (A x + c₀)
          (fun σs => f σs * (A (covarianceOperator P (w (σs i)))) (σs i))
        + ∑ l ∈ Finset.univ.erase i, gibbs_average_n_det (α := α) (n := m) (A x + c₀)
            (fun σs => f σs * (A (covarianceOperator P (w (σs i)))) (σs l)) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have hdiagAvg : gibbs_average_n_det (α := α) (n := m) (A x + c₀)
      (fun σs => f σs * (A (covarianceOperator P (w (σs i)))) (σs i))
      = d * gibbs_average_n_det (α := α) (n := m) (A x + c₀) f := by
    rw [gibbs_average_n_det, gibbs_average_n_det, Finset.mul_sum]
    exact Finset.sum_congr rfl fun σs _ => by
      have := hdiag (σs i)
      rw [crossKernel_apply] at this
      rw [this]; ring
  simp only [freshKernelAvg, crossKernel_apply]
  rw [hsplit, hdiagAvg]
  ring

/-- **The mean of a component field is its mean cross kernel against a fresh replica, minus the
diagonal**: `𝔼⟨⟪x, w ·⟫⟩ = 𝔼⟨c_{A,w}(σ¹, σ²)⟩ - d`. -/
theorem integral_gibbs_average_one_inner_comp
    (hmean0 : (∫ x : Ω, x ∂P) = 0) (A : Ω →L[ℝ] EnergySpace α) (c₀ : EnergySpace α)
    {w : α → Ω} {Mw : ℝ} (hw : ∀ σ : α, ‖w σ‖ ≤ Mw) {d : ℝ}
    (hdiag : ∀ σ : α, crossKernel P A w σ σ = d) :
    (∫ x : Ω, gibbs_average_n_det (α := α) (n := 1) (A x + c₀)
        (fun τs => ⟪x, w (τs 0)⟫_ℝ) ∂P)
      = (∫ x : Ω, gibbs_average_n_det (α := α) (n := 1) (A x + c₀)
          (fun τs => freshKernelAvg (α := α) (A x + c₀) (crossKernel P A w) (τs 0)) ∂P) - d := by
  classical
  have hone := integral_gibbs_average_n_det_inner_mul_comp_erase (P := P) hmean0 A c₀ w hdiag 1
    (fun _ => (1 : ℝ)) 0
  have herase : (Finset.univ.erase (0 : Fin 1)) = ∅ := by
    ext l
    simp [Subsingleton.elim l 0]
  have hker := abs_crossKernel_le (P := P) A hw
  have hbd := abs_freshKernelAvg_le (α := α) hker
  have hI1' : Integrable
      (fun x : Ω => gibbs_average_n_det (α := α) (n := 1) (A x + c₀)
        (fun τs => freshKernelAvg (α := α) (A x + c₀) (crossKernel P A w) (τs 0))) P := by
    have hcont : Continuous fun x : Ω => gibbs_average_n_det (α := α) (n := 1) (A x + c₀)
        (fun τs => freshKernelAvg (α := α) (A x + c₀) (crossKernel P A w) (τs 0)) := by
      simp only [gibbs_average_n_det]
      exact continuous_finsetSum _ fun τs _ =>
        (((continuous_freshKernelAvg (α := α) (crossKernel P A w) (τs 0)).comp
            (A.continuous.add continuous_const)).mul
          (continuous_finsetProd _ fun l _ =>
            ((contDiff_gibbs_pmf (α := α) (τs l)).continuous).comp
              (A.continuous.add continuous_const)))
    have hM0 : (0 : ℝ) ≤ ‖A‖ * (‖covarianceOperator P‖ * Mw) :=
      le_trans (abs_nonneg _) (hker (Classical.arbitrary α) (Classical.arbitrary α))
    refine ProbabilityTheory.IsGaussian.integrable_of_abs_le_mul_one_add_norm_pow (μ := P)
      hcont.measurable (C := ‖A‖ * (‖covarianceOperator P‖ * Mw)) (m := 0) hM0 fun x => ?_
    rw [gibbs_average_one]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ τ : α,
        |freshKernelAvg (α := α) (A x + c₀) (crossKernel P A w) τ
            * gibbs_pmf (α := α) (A x + c₀) τ|
          ≤ (‖A‖ * (‖covarianceOperator P‖ * Mw)) * gibbs_pmf (α := α) (A x + c₀) τ := by
      intro τ
      rw [abs_mul, abs_of_nonneg (gibbs_pmf_nonneg (α := α) (A x + c₀) τ)]
      exact mul_le_mul_of_nonneg_right (hbd (A x + c₀) τ)
        (gibbs_pmf_nonneg (α := α) (A x + c₀) τ)
    calc (∑ τ : α, |freshKernelAvg (α := α) (A x + c₀) (crossKernel P A w) τ
            * gibbs_pmf (α := α) (A x + c₀) τ|)
        ≤ ∑ τ : α, (‖A‖ * (‖covarianceOperator P‖ * Mw))
            * gibbs_pmf (α := α) (A x + c₀) τ := Finset.sum_le_sum fun τ _ => hterm τ
      _ = ‖A‖ * (‖covarianceOperator P‖ * Mw) := by
          rw [← Finset.mul_sum, sum_gibbs_pmf, mul_one]
      _ ≤ ‖A‖ * (‖covarianceOperator P‖ * Mw) * (1 + ‖x‖) ^ 0 := by simp
  rw [show (fun x : Ω => gibbs_average_n_det (α := α) (n := 1) (A x + c₀)
        (fun τs => ⟪x, w (τs 0)⟫_ℝ)) = fun x : Ω =>
      gibbs_average_n_det (α := α) (n := 1) (A x + c₀)
        (fun τs => ⟪x, w (τs 0)⟫_ℝ * (1 : ℝ)) from by
    funext x; simp]
  rw [hone, herase]
  simp only [Finset.sum_empty, sub_zero, Nat.cast_one, one_mul, gibbs_average_one_const,
    mul_one, one_mul]
  rw [MeasureTheory.integral_sub hI1' (integrable_const d), MeasureTheory.integral_const]
  simp

/-- A replica average along a linear-image Hamiltonian is integrable as soon as the observable is
continuous in the disorder and uniformly bounded. -/
lemma integrable_gibbs_average_n_det_comp_of_bounded (A : Ω →L[ℝ] EnergySpace α)
    (c₀ : EnergySpace α) (m : ℕ) (g : Ω → ReplicaFun (α := α) m)
    (hg : Continuous fun x : Ω => gibbs_average_n_det (α := α) (n := m) (A x + c₀) (g x))
    {B : ℝ} (hB : ∀ x σs, ‖g x σs‖ ≤ B) :
    Integrable (fun x : Ω => gibbs_average_n_det (α := α) (n := m) (A x + c₀) (g x)) P := by
  classical
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (fun _ => Classical.arbitrary α))
  have hbound : ∀ x : Ω,
      |gibbs_average_n_det (α := α) (n := m) (A x + c₀) (g x)|
        ≤ (Fintype.card (ReplicaSpace (α := α) m) : ℝ) * B := by
    intro x
    refine le_trans (abs_gibbs_average_n_det_le_sum_abs (α := α) m (A x + c₀) (g x)) ?_
    calc (∑ σs : ReplicaSpace (α := α) m, ‖g x σs‖)
        ≤ ∑ _σs : ReplicaSpace (α := α) m, B := Finset.sum_le_sum fun σs _ => hB x σs
      _ = (Fintype.card (ReplicaSpace (α := α) m) : ℝ) * B := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact ProbabilityTheory.IsGaussian.integrable_of_abs_le_mul_one_add_norm_pow (μ := P)
    hg.measurable (C := (Fintype.card (ReplicaSpace (α := α) m) : ℝ) * B) (m := 0)
    (by positivity) (fun x => by simpa using hbound x)

/-- The replica bracket of a component field along a linear-image Hamiltonian is integrable. -/
lemma integrable_gibbs_average_n_det_inner_mul_comp (A : Ω →L[ℝ] EnergySpace α)
    (c₀ : EnergySpace α) {w : α → Ω} {Mw : ℝ} (hw : ∀ σ : α, ‖w σ‖ ≤ Mw)
    (m : ℕ) (f : ReplicaFun (α := α) m) (i : Fin m) :
    Integrable (fun x : Ω => gibbs_average_n_det (α := α) (n := m) (A x + c₀)
      (fun σs => ⟪x, w (σs i)⟫_ℝ * f σs)) P := by
  classical
  have hMw0 : (0 : ℝ) ≤ Mw := le_trans (norm_nonneg _) (hw (Classical.arbitrary α))
  set Bf : ℝ := ∑ σs : ReplicaSpace (α := α) m, ‖f σs‖ with hBf
  have hBf0 : 0 ≤ Bf := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hfle : ∀ σs : ReplicaSpace (α := α) m, ‖f σs‖ ≤ Bf :=
    fun σs => Finset.single_le_sum (f := fun σs' => ‖f σs'‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ σs)
  have hcont : Continuous fun x : Ω =>
      gibbs_average_n_det (α := α) (n := m) (A x + c₀)
        (fun σs => ⟪x, w (σs i)⟫_ℝ * f σs) := by
    simp only [gibbs_average_n_det]
    exact continuous_finsetSum _ fun σs _ =>
      (((continuous_id.inner continuous_const).mul continuous_const).mul
        (continuous_finsetProd _ fun l _ =>
          ((contDiff_gibbs_pmf (α := α) (σs l)).continuous).comp
            (A.continuous.add continuous_const)))
  refine ProbabilityTheory.IsGaussian.integrable_of_abs_le_mul_one_add_norm_pow (μ := P)
    hcont.measurable (C := Bf * Mw) (m := 1) (mul_nonneg hBf0 hMw0) fun x => ?_
  refine le_trans (abs_gibbs_average_n_det_le_sum_abs (α := α) m (A x + c₀) _) ?_
  calc (∑ σs : ReplicaSpace (α := α) m, ‖⟪x, w (σs i)⟫_ℝ * f σs‖)
      ≤ ∑ σs : ReplicaSpace (α := α) m, (‖x‖ * Mw) * ‖f σs‖ := by
        refine Finset.sum_le_sum fun σs _ => ?_
        rw [Real.norm_eq_abs, abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        calc |⟪x, w (σs i)⟫_ℝ| ≤ ‖x‖ * ‖w (σs i)‖ := abs_real_inner_le_norm x (w (σs i))
          _ ≤ ‖x‖ * Mw := mul_le_mul_of_nonneg_left (hw (σs i)) (norm_nonneg x)
    _ = (‖x‖ * Mw) * Bf := by rw [← Finset.mul_sum]
    _ ≤ (Bf * Mw) * (1 + ‖x‖) ^ 1 := by
        have hn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
        have hpow : (1 + ‖x‖) ^ 1 = 1 + ‖x‖ := pow_one _
        rw [hpow]
        nlinarith [hBf0, hMw0, hn]

/-- The mean absolute deviation of a component field along a linear-image Hamiltonian is
integrable. -/
lemma integrable_sum_gibbs_pmf_mul_abs_inner_sub_comp (A : Ω →L[ℝ] EnergySpace α)
    (c₀ : EnergySpace α) {w : α → Ω} {Mw : ℝ} (hw : ∀ σ : α, ‖w σ‖ ≤ Mw) (a : ℝ) :
    Integrable (fun x : Ω =>
      ∑ σ : α, gibbs_pmf (α := α) (A x + c₀) σ * |⟪x, w σ⟫_ℝ - a|) P := by
  classical
  have hMw0 : (0 : ℝ) ≤ Mw := le_trans (norm_nonneg _) (hw (Classical.arbitrary α))
  have hcont : Continuous fun x : Ω =>
      ∑ σ : α, gibbs_pmf (α := α) (A x + c₀) σ * |⟪x, w σ⟫_ℝ - a| :=
    continuous_finsetSum _ fun σ _ =>
      (((contDiff_gibbs_pmf (α := α) σ).continuous).comp
        (A.continuous.add continuous_const)).mul
        (((continuous_id.inner continuous_const).sub continuous_const).abs)
  have hnn : ∀ x : Ω,
      0 ≤ ∑ σ : α, gibbs_pmf (α := α) (A x + c₀) σ * |⟪x, w σ⟫_ℝ - a| :=
    fun x => Finset.sum_nonneg fun σ _ =>
      mul_nonneg (gibbs_pmf_nonneg (α := α) (A x + c₀) σ) (abs_nonneg _)
  have hbd : ∀ x : Ω,
      (∑ σ : α, gibbs_pmf (α := α) (A x + c₀) σ * |⟪x, w σ⟫_ℝ - a|) ≤ Mw * ‖x‖ + |a| := by
    intro x
    calc (∑ σ : α, gibbs_pmf (α := α) (A x + c₀) σ * |⟪x, w σ⟫_ℝ - a|)
        ≤ ∑ _σ : α, gibbs_pmf (α := α) (A x + c₀) _σ * (Mw * ‖x‖ + |a|) := by
          refine Finset.sum_le_sum fun σ _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (gibbs_pmf_nonneg (α := α) (A x + c₀) σ)
          have hb : |⟪x, w σ⟫_ℝ| ≤ Mw * ‖x‖ := by
            calc |⟪x, w σ⟫_ℝ| ≤ ‖x‖ * ‖w σ‖ := abs_real_inner_le_norm x (w σ)
              _ ≤ ‖x‖ * Mw := mul_le_mul_of_nonneg_left (hw σ) (norm_nonneg x)
              _ = Mw * ‖x‖ := mul_comm _ _
          calc |⟪x, w σ⟫_ℝ - a| ≤ |⟪x, w σ⟫_ℝ| + |a| := abs_sub _ _
            _ ≤ Mw * ‖x‖ + |a| := by linarith
      _ = Mw * ‖x‖ + |a| := by rw [← Finset.sum_mul, sum_gibbs_pmf, one_mul]
  refine ProbabilityTheory.IsGaussian.integrable_of_abs_le_mul_one_add_norm_pow (μ := P)
    hcont.measurable (C := Mw + |a|) (m := 1) (by linarith [abs_nonneg a]) fun x => ?_
  rw [abs_of_nonneg (hnn x), pow_one]
  have h := hbd x
  nlinarith [norm_nonneg x, abs_nonneg a, hMw0]

/-- **Talagrand, Vol. II, Lemma 12.1.4, for a component of the disorder.** The mean of the
component field is at most twice the size of its cross kernel — hence *uniform in the volume*
whenever the kernel is, which for a `p`-spin term of a mixed model (`aₚ N Rᵖ`) it is after dividing
by `N`. -/
theorem abs_integral_gibbs_average_one_inner_comp_le
    (hmean0 : (∫ x : Ω, x ∂P) = 0) (A : Ω →L[ℝ] EnergySpace α) (c₀ : EnergySpace α)
    {w : α → Ω} {Mw : ℝ} (hw : ∀ σ : α, ‖w σ‖ ≤ Mw) {d : ℝ}
    (hdiag : ∀ σ : α, crossKernel P A w σ σ = d) {M : ℝ}
    (hker : ∀ σ τ : α, |crossKernel P A w σ τ| ≤ M) :
    |∫ x : Ω, gibbs_average_n_det (α := α) (n := 1) (A x + c₀)
        (fun τs => ⟪x, w (τs 0)⟫_ℝ) ∂P| ≤ 2 * M := by
  classical
  have hbd := abs_freshKernelAvg_le (α := α) hker
  have hd : |d| ≤ M := by rw [← hdiag (Classical.arbitrary α)]; exact hker _ _
  have hptwise : ∀ x : Ω,
      |gibbs_average_n_det (α := α) (n := 1) (A x + c₀)
        (fun τs => freshKernelAvg (α := α) (A x + c₀) (crossKernel P A w) (τs 0))| ≤ M := by
    intro x
    rw [gibbs_average_one]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc (∑ τ : α, |freshKernelAvg (α := α) (A x + c₀) (crossKernel P A w) τ
            * gibbs_pmf (α := α) (A x + c₀) τ|)
        ≤ ∑ τ : α, M * gibbs_pmf (α := α) (A x + c₀) τ := by
          refine Finset.sum_le_sum fun τ _ => ?_
          rw [abs_mul, abs_of_nonneg (gibbs_pmf_nonneg (α := α) (A x + c₀) τ)]
          exact mul_le_mul_of_nonneg_right (hbd (A x + c₀) τ)
            (gibbs_pmf_nonneg (α := α) (A x + c₀) τ)
      _ = M := by rw [← Finset.mul_sum, sum_gibbs_pmf, mul_one]
  have hint : |∫ x : Ω, gibbs_average_n_det (α := α) (n := 1) (A x + c₀)
      (fun τs => freshKernelAvg (α := α) (A x + c₀) (crossKernel P A w) (τs 0)) ∂P| ≤ M := by
    have h := MeasureTheory.norm_integral_le_of_norm_le_const (μ := P)
      (f := fun x : Ω => gibbs_average_n_det (α := α) (n := 1) (A x + c₀)
        (fun τs => freshKernelAvg (α := α) (A x + c₀) (crossKernel P A w) (τs 0)))
      (C := M) (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hptwise x)
    simpa [Real.norm_eq_abs, measure_univ] using h
  rw [integral_gibbs_average_one_inner_comp (P := P) hmean0 A c₀ hw hdiag]
  calc |(∫ x : Ω, gibbs_average_n_det (α := α) (n := 1) (A x + c₀)
          (fun τs => freshKernelAvg (α := α) (A x + c₀) (crossKernel P A w) (τs 0)) ∂P) - d|
      ≤ |∫ x : Ω, gibbs_average_n_det (α := α) (n := 1) (A x + c₀)
          (fun τs => freshKernelAvg (α := α) (A x + c₀) (crossKernel P A w) (τs 0)) ∂P| + |d| :=
        abs_sub _ _
    _ ≤ M + M := add_le_add hint hd
    _ = 2 * M := by ring

end LinearImage

/-! ### The Ghirlanda–Guerra combination -/

/-- **The Ghirlanda–Guerra combination of a kernel.**

For an arbitrary kernel `c` on configurations, a test function `f` of `m` replicas and an index
`i`, this is

`m 𝔼⟨f · c(σⁱ, σ^{m+1})⟩ - 𝔼⟨f⟩ · 𝔼⟨c(σ¹, σ²)⟩ - ∑_{l ≠ i} 𝔼⟨f · c(σⁱ, σˡ)⟩`,

where the first term averages the kernel against a *fresh* replica (`freshCov`) and the last sum
runs over the replicas already present. The **Ghirlanda–Guerra identities** are the statement that
this quantity vanishes, for every `m`, `f` and `i`.

The kernel is a *parameter*, not `μ`'s own covariance: the combination is then **linear in `c`**
(`ghirlandaGuerraCombinationOf_add`, `ghirlandaGuerraCombinationOf_smul`), so the combination of a
mixed `p`-spin kernel `∑ₚ aₚ N Rᵖ` splits into the combinations of its individual `p`-spin terms.
The Hamiltonian's own case is `ghirlandaGuerraCombination`.

Talagrand, *Mean Field Models for Spin Glasses*, Vol. II, Definition 15.3.4 and Eq. (15.40);
Panchenko, *The Parisi ultrametricity conjecture*, Eq. (1.1). -/
def ghirlandaGuerraCombinationOf (μ : Measure (EnergySpace α)) (c : α → α → ℝ) (m : ℕ)
    (f : ReplicaFun (α := α) m) (i : Fin m) : ℝ :=
  (m : ℝ) * (∫ H : EnergySpace α,
        gibbs_average_n_det (α := α) (n := m) H
          (fun σs => f σs * freshKernelAvg (α := α) H c (σs i)) ∂μ)
      - (∫ H : EnergySpace α, gibbs_average_n_det (α := α) (n := m) H f ∂μ)
          * (∫ H : EnergySpace α,
              gibbs_average_n_det (α := α) (n := 1) H
                (fun τs => freshKernelAvg (α := α) H c (τs 0)) ∂μ)
      - ∑ l ∈ Finset.univ.erase i, ∫ H : EnergySpace α,
          gibbs_average_n_det (α := α) (n := m) H (fun σs => f σs * c (σs i) (σs l)) ∂μ

/-- **The Ghirlanda–Guerra combination of the Hamiltonian's own covariance kernel**: the case
`c = Cov(H σ, H τ)` of `SpinGlass.FiniteGibbs.ghirlandaGuerraCombinationOf`. This is the
combination Talagrand's Definition 15.3.4 asserts to vanish. -/
def ghirlandaGuerraCombination (μ : Measure (EnergySpace α)) (m : ℕ)
    (f : ReplicaFun (α := α) m) (i : Fin m) : ℝ :=
  ghirlandaGuerraCombinationOf μ (covKernel μ (std_basis (α := α))) m f i

omit [Nonempty α] [IsGaussian μ] in
lemma ghirlandaGuerraCombination_eq (m : ℕ) (f : ReplicaFun (α := α) m) (i : Fin m) :
    ghirlandaGuerraCombination μ m f i
      = (m : ℝ) * (∫ H : EnergySpace α,
            gibbs_average_n_det (α := α) (n := m) H
              (fun σs => f σs * freshCov μ H (σs i)) ∂μ)
          - (∫ H : EnergySpace α, gibbs_average_n_det (α := α) (n := m) H f ∂μ)
              * (∫ H : EnergySpace α,
                  gibbs_average_n_det (α := α) (n := 1) H (fun τs => freshCov μ H (τs 0)) ∂μ)
          - ∑ l ∈ Finset.univ.erase i, ∫ H : EnergySpace α,
              gibbs_average_n_det (α := α) (n := m) H
                (fun σs => f σs
                  * (covarianceOperator μ (std_basis (α := α) (σs i))) (σs l)) ∂μ := rfl

/-- The replica bracket of a component field against a bounded observable is integrable. -/
lemma integrable_gibbs_average_n_det_inner_mul {w : α → EnergySpace α} {Mw : ℝ}
    (hw : ∀ σ : α, ‖w σ‖ ≤ Mw) (m : ℕ) (f : ReplicaFun (α := α) m) (i : Fin m) :
    Integrable (fun H : EnergySpace α => gibbs_average_n_det (α := α) (n := m) H
      (fun σs => ⟪H, w (σs i)⟫_ℝ * f σs)) μ := by
  classical
  have hMw0 : (0 : ℝ) ≤ Mw := le_trans (norm_nonneg _) (hw (Classical.arbitrary α))
  set Bf : ℝ := ∑ σs : ReplicaSpace (α := α) m, ‖f σs‖ with hBf
  have hBf0 : 0 ≤ Bf := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hfle : ∀ σs : ReplicaSpace (α := α) m, ‖f σs‖ ≤ Bf :=
    fun σs => Finset.single_le_sum (f := fun σs' => ‖f σs'‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ σs)
  have hcont : Continuous fun H : EnergySpace α =>
      gibbs_average_n_det (α := α) (n := m) H (fun σs => ⟪H, w (σs i)⟫_ℝ * f σs) := by
    simp only [gibbs_average_n_det]
    exact continuous_finsetSum _ fun σs _ =>
      (((continuous_id.inner continuous_const).mul continuous_const).mul
        (continuous_finsetProd _ fun l _ => (contDiff_gibbs_pmf (α := α) (σs l)).continuous))
  refine ProbabilityTheory.IsGaussian.integrable_of_abs_le_mul_one_add_norm_pow (μ := μ)
    hcont.measurable (C := Bf * Mw) (m := 1) (mul_nonneg hBf0 hMw0) fun H => ?_
  refine le_trans (abs_gibbs_average_n_det_le_sum_abs (α := α) m H _) ?_
  calc (∑ σs : ReplicaSpace (α := α) m, ‖⟪H, w (σs i)⟫_ℝ * f σs‖)
      ≤ ∑ σs : ReplicaSpace (α := α) m, (‖H‖ * Mw) * ‖f σs‖ := by
        refine Finset.sum_le_sum fun σs _ => ?_
        rw [Real.norm_eq_abs, abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        calc |⟪H, w (σs i)⟫_ℝ| ≤ ‖H‖ * ‖w (σs i)‖ := abs_real_inner_le_norm H (w (σs i))
          _ ≤ ‖H‖ * Mw := mul_le_mul_of_nonneg_left (hw (σs i)) (norm_nonneg H)
    _ = (‖H‖ * Mw) * Bf := by rw [← Finset.mul_sum]
    _ ≤ (Bf * Mw) * (1 + ‖H‖) ^ 1 := by
        have hn : (0 : ℝ) ≤ ‖H‖ := norm_nonneg H
        have hpow : (1 + ‖H‖) ^ 1 = 1 + ‖H‖ := pow_one _
        rw [hpow]
        nlinarith [hBf0, hMw0, hn]

/-! ### The defect identity -/

/-- **The Ghirlanda–Guerra defect of a component of the disorder is its covariance with the
observable.**

Let `w` be a family of directions and `c_w(σ,τ) = Cov(⟪H, w σ⟫, H τ)` the corresponding
cross-covariance kernel, with constant diagonal `c_w σ σ = d`. Then the Ghirlanda–Guerra
combination of `c_w` is exactly

`𝔼⟨⟪H, w(σⁱ)⟫ f⟩ - 𝔼⟨f⟩ · 𝔼⟨⟪H, w(·)⟫⟩`,

the covariance between the *component field* `σ ↦ ⟪H, w σ⟫` evaluated at the `i`-th replica and the
observable. Taking `w = e_·` gives the Hamiltonian itself; taking `w σ = Wᵀ e_σ` for a linear map
`W` gives the component `W H` — for a mixed `p`-spin model, a single `p`-spin term, whose kernel is
a single monomial `aₚ N Rᵖ`. That is what turns the identities at the model's own profile `ξ` into
the identities at *each* monomial test function.

Talagrand, *Mean Field Models for Spin Glasses*, Vol. II, §12.2. -/
theorem ghirlandaGuerra_defect_of
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0) {w : α → EnergySpace α} {Mw : ℝ}
    (hw : ∀ σ : α, ‖w σ‖ ≤ Mw) {d : ℝ}
    (hdiag : ∀ σ : α, (covarianceOperator μ (w σ)) σ = d)
    (m : ℕ) (f : ReplicaFun (α := α) m) (i : Fin m) :
    ghirlandaGuerraCombinationOf μ (covKernel μ w) m f i
      = (∫ H : EnergySpace α,
            gibbs_average_n_det (α := α) (n := m) H (fun σs => ⟪H, w (σs i)⟫_ℝ * f σs) ∂μ)
        - (∫ H : EnergySpace α, gibbs_average_n_det (α := α) (n := m) H f ∂μ)
            * (∫ H : EnergySpace α,
                gibbs_average_n_det (α := α) (n := 1) H (fun τs => ⟪H, w (τs 0)⟫_ℝ) ∂μ) := by
  classical
  rw [ghirlandaGuerraCombinationOf]
  have hK0 : (0 : ℝ) ≤ ‖covarianceOperator μ‖ := norm_nonneg _
  have hker : ∀ σ τ : α, |covKernel μ w σ τ| ≤ ‖covarianceOperator μ‖ * Mw :=
    abs_covKernel_le (μ := μ) hw
  have hfresh := abs_freshKernelAvg_le hker
  set Bf : ℝ := ∑ σs : ReplicaSpace (α := α) m, ‖f σs‖ with hBf
  have hBf0 : 0 ≤ Bf := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hfle : ∀ σs : ReplicaSpace (α := α) m, ‖f σs‖ ≤ Bf :=
    fun σs => Finset.single_le_sum (f := fun σs' => ‖f σs'‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ σs)
  have hcontAvg : ∀ (g : ReplicaFun (α := α) m),
      Continuous fun H : EnergySpace α => gibbs_average_n_det (α := α) (n := m) H g :=
    fun g => (contDiff_gibbs_average_n_det (α := α) m g).continuous
  -- the four integrability facts
  have hI2 : Integrable
      (fun H : EnergySpace α => gibbs_average_n_det (α := α) (n := m) H f) μ :=
    integrable_gibbs_average_n_det_of_bounded (μ := μ) m (fun _ => f) (hcontAvg f)
      (B := Bf) (fun _ σs => hfle σs)
  have hI1 : Integrable
      (fun H : EnergySpace α => gibbs_average_n_det (α := α) (n := m) H
        (fun σs => f σs * freshKernelAvg (α := α) H (covKernel μ w) (σs i))) μ := by
    refine integrable_gibbs_average_n_det_of_bounded (μ := μ) m
      (fun H σs => f σs * freshKernelAvg (α := α) H (covKernel μ w) (σs i)) ?_
      (B := Bf * (‖covarianceOperator μ‖ * Mw)) fun H σs => ?_
    · simp only [gibbs_average_n_det]
      exact continuous_finsetSum _ fun σs _ =>
        ((continuous_const.mul (continuous_freshKernelAvg (α := α) (covKernel μ w) (σs i))).mul
          (continuous_finsetProd _ fun l _ => (contDiff_gibbs_pmf (α := α) (σs l)).continuous))
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (by simpa [Real.norm_eq_abs] using hfle σs)
        (hfresh H (σs i)) (abs_nonneg _) hBf0
  have hI3 : ∀ l : Fin m, Integrable
      (fun H : EnergySpace α => gibbs_average_n_det (α := α) (n := m) H
        (fun σs => f σs * covKernel μ w (σs i) (σs l))) μ := by
    intro l
    refine integrable_gibbs_average_n_det_of_bounded (μ := μ) m
      (fun _ σs => f σs * covKernel μ w (σs i) (σs l))
      (hcontAvg _) (B := Bf * (‖covarianceOperator μ‖ * Mw)) fun H σs => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (by simpa [Real.norm_eq_abs] using hfle σs)
      (hker (σs i) (σs l)) (abs_nonneg _) hBf0
  -- (★) the cavity identity with the diagonal separated, split into separate integrals
  have hstar := integral_gibbs_average_n_det_inner_mul_erase (μ := μ) hmean0 w hdiag m f i
  have hIsum : Integrable (fun H : EnergySpace α =>
      ∑ l ∈ Finset.univ.erase i, gibbs_average_n_det (α := α) (n := m) H
        (fun σs => f σs * covKernel μ w (σs i) (σs l))) μ :=
    integrable_finsetSum _ fun l _ => hI3 l
  have hIa : Integrable (fun H : EnergySpace α => (m : ℝ) *
      gibbs_average_n_det (α := α) (n := m) H
        (fun σs => f σs * freshKernelAvg (α := α) H (covKernel μ w) (σs i))) μ := hI1.const_mul _
  have hIb : Integrable (fun H : EnergySpace α => d *
      gibbs_average_n_det (α := α) (n := m) H f) μ := hI2.const_mul _
  have hIdiff : Integrable (fun H : EnergySpace α =>
      (m : ℝ) * gibbs_average_n_det (α := α) (n := m) H
          (fun σs => f σs * freshKernelAvg (α := α) H (covKernel μ w) (σs i))
        - d * gibbs_average_n_det (α := α) (n := m) H f) μ := hIa.sub hIb
  rw [MeasureTheory.integral_sub hIdiff hIsum,
    MeasureTheory.integral_sub hIa hIb,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finsetSum _ fun l (_ : l ∈ Finset.univ.erase i) => hI3 l] at hstar
  -- (★★) the mean component field, from the same identity at one replica
  rw [integral_gibbs_average_one_inner (μ := μ) hmean0 hw hdiag]
  linarith [hstar]

/-- **The Ghirlanda–Guerra defect is the energy–observable covariance.**

For a centered Gaussian Hamiltonian law whose covariance kernel has constant diagonal `c σ σ = d`
— the case of every mixed `p`-spin model, where `c σ τ = N ξ(R_{στ})` — the failure of the
Ghirlanda–Guerra identity for a test function `f` of `m` replicas is exactly

`𝔼⟨H_{σⁱ} f⟩ - 𝔼⟨f⟩ · 𝔼⟨H⟩`,

the covariance between the Hamiltonian evaluated at the `i`-th replica and the observable. In
particular the identity holds **exactly** iff the energy decorrelates from `f`; asymptotic
self-averaging of the Hamiltonian is what makes this vanish in the limit, and this identity is
what converts a bound on that covariance into a bound on the Ghirlanda–Guerra error.

The coordinate case `w = e_·` of `SpinGlass.FiniteGibbs.ghirlandaGuerra_defect_of`.

Talagrand, *Mean Field Models for Spin Glasses*, Vol. II, §12.2. -/
theorem ghirlandaGuerra_defect
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0) {d : ℝ}
    (hdiag : ∀ σ : α, (covarianceOperator μ (std_basis (α := α) σ)) σ = d)
    (m : ℕ) (f : ReplicaFun (α := α) m) (i : Fin m) :
    ghirlandaGuerraCombination μ m f i
      = (∫ H : EnergySpace α,
            gibbs_average_n_det (α := α) (n := m) H (fun σs => H (σs i) * f σs) ∂μ)
        - (∫ H : EnergySpace α, gibbs_average_n_det (α := α) (n := m) H f ∂μ)
            * (∫ H : EnergySpace α,
                gibbs_average_n_det (α := α) (n := 1) H (fun τs => H (τs 0)) ∂μ) := by
  have hco : ∀ (H : EnergySpace α) (σ : α), ⟪H, std_basis (α := α) σ⟫_ℝ = H σ := fun H σ => by
    rw [real_inner_comm]; exact inner_std_basis_apply (α := α) σ H
  have h := ghirlandaGuerra_defect_of (μ := μ) hmean0
    (w := fun σ => std_basis (α := α) σ) (Mw := 1)
    (fun σ => le_of_eq (norm_std_basis (α := α) σ)) hdiag m f i
  rw [show (∫ H : EnergySpace α, gibbs_average_n_det (α := α) (n := m) H
          (fun σs => ⟪H, std_basis (α := α) (σs i)⟫_ℝ * f σs) ∂μ)
        = ∫ H : EnergySpace α, gibbs_average_n_det (α := α) (n := m) H
          (fun σs => H (σs i) * f σs) ∂μ from
      integral_congr_ae (Filter.Eventually.of_forall fun H =>
        congrArg (gibbs_average_n_det (α := α) (n := m) H)
          (funext fun σs => by rw [hco])),
    show (∫ H : EnergySpace α, gibbs_average_n_det (α := α) (n := 1) H
          (fun τs => ⟪H, std_basis (α := α) (τs 0)⟫_ℝ) ∂μ)
        = ∫ H : EnergySpace α, gibbs_average_n_det (α := α) (n := 1) H
          (fun τs => H (τs 0)) ∂μ from
      integral_congr_ae (Filter.Eventually.of_forall fun H =>
        congrArg (gibbs_average_n_det (α := α) (n := 1) H)
          (funext fun τs => hco H (τs 0)))] at h
  exact h

/-! ### The Ghirlanda–Guerra defect and error of a component -/

section LinearImageDefect

variable {Ω : Type*} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω] [CompleteSpace Ω]
variable [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω]
variable {P : Measure Ω} [IsGaussian P]

omit [Nonempty α] [CompleteSpace Ω] [SecondCountableTopology Ω] [IsGaussian P] in
/-- Change of variables along an affine linear image of the disorder. -/
lemma integral_map_clm_add_const (A : Ω →L[ℝ] EnergySpace α) (c₀ : EnergySpace α)
    {g : EnergySpace α → ℝ} (hg : Continuous g) :
    (∫ H : EnergySpace α, g H ∂(P.map (fun x : Ω => A x + c₀))) = ∫ x : Ω, g (A x + c₀) ∂P :=
  MeasureTheory.integral_map
    (A.continuous.add continuous_const).measurable.aemeasurable hg.aestronglyMeasurable

/-- **The Ghirlanda–Guerra defect of a component, for a linear-image Hamiltonian.**

The law of the Hamiltonian is `P.map (A · + c₀)`; the Ghirlanda–Guerra combination of the *cross*
kernel of a component is the covariance between that component's field at the `i`-th replica and
the observable. Taking `Ω = E × E`, `A (x,y) = x + t y` and `w σ = (0, e_σ)` this is the defect of
a single summand of the Hamiltonian. -/
theorem ghirlandaGuerra_defect_of_comp
    (hmean0 : (∫ x : Ω, x ∂P) = 0) (A : Ω →L[ℝ] EnergySpace α) (c₀ : EnergySpace α)
    {w : α → Ω} {Mw : ℝ} (hw : ∀ σ : α, ‖w σ‖ ≤ Mw) {d : ℝ}
    (hdiag : ∀ σ : α, crossKernel P A w σ σ = d)
    (m : ℕ) (f : ReplicaFun (α := α) m) (i : Fin m) :
    ghirlandaGuerraCombinationOf (P.map (fun x : Ω => A x + c₀)) (crossKernel P A w) m f i
      = (∫ x : Ω, gibbs_average_n_det (α := α) (n := m) (A x + c₀)
            (fun σs => ⟪x, w (σs i)⟫_ℝ * f σs) ∂P)
        - (∫ x : Ω, gibbs_average_n_det (α := α) (n := m) (A x + c₀) f ∂P)
            * (∫ x : Ω, gibbs_average_n_det (α := α) (n := 1) (A x + c₀)
                (fun τs => ⟪x, w (τs 0)⟫_ℝ) ∂P) := by
  classical
  set c : α → α → ℝ := crossKernel P A w with hc
  have hkerbd := abs_crossKernel_le (P := P) A hw
  have hM0 : (0 : ℝ) ≤ ‖A‖ * (‖covarianceOperator P‖ * Mw) :=
    le_trans (abs_nonneg _) (hkerbd (Classical.arbitrary α) (Classical.arbitrary α))
  -- the four change-of-variables steps
  have hcA : Continuous fun H : EnergySpace α => gibbs_average_n_det (α := α) (n := m) H
      (fun σs => f σs * freshKernelAvg (α := α) H c (σs i)) := by
    simp only [gibbs_average_n_det]
    exact continuous_finsetSum _ fun σs _ =>
      ((continuous_const.mul (continuous_freshKernelAvg (α := α) c (σs i))).mul
        (continuous_finsetProd _ fun l _ => (contDiff_gibbs_pmf (α := α) (σs l)).continuous))
  have hcB : Continuous fun H : EnergySpace α =>
      gibbs_average_n_det (α := α) (n := m) H f :=
    (contDiff_gibbs_average_n_det (α := α) m f).continuous
  have hcC : Continuous fun H : EnergySpace α => gibbs_average_n_det (α := α) (n := 1) H
      (fun τs => freshKernelAvg (α := α) H c (τs 0)) := by
    simp only [gibbs_average_n_det]
    exact continuous_finsetSum _ fun τs _ =>
      ((continuous_freshKernelAvg (α := α) c (τs 0)).mul
        (continuous_finsetProd _ fun l _ => (contDiff_gibbs_pmf (α := α) (τs l)).continuous))
  have hcD : ∀ l : Fin m, Continuous fun H : EnergySpace α =>
      gibbs_average_n_det (α := α) (n := m) H (fun σs => f σs * c (σs i) (σs l)) :=
    fun l => (contDiff_gibbs_average_n_det (α := α) m _).continuous
  rw [ghirlandaGuerraCombinationOf,
    integral_map_clm_add_const (P := P) A c₀ hcA,
    integral_map_clm_add_const (P := P) A c₀ hcB,
    integral_map_clm_add_const (P := P) A c₀ hcC,
    Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ.erase i) =>
      integral_map_clm_add_const (P := P) A c₀ (hcD l)]
  -- now the two cavity identities
  set Bf : ℝ := ∑ σs : ReplicaSpace (α := α) m, ‖f σs‖ with hBf
  have hBf0 : 0 ≤ Bf := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hfle : ∀ σs : ReplicaSpace (α := α) m, ‖f σs‖ ≤ Bf :=
    fun σs => Finset.single_le_sum (f := fun σs' => ‖f σs'‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ σs)
  have hI2 : Integrable
      (fun x : Ω => gibbs_average_n_det (α := α) (n := m) (A x + c₀) f) P :=
    integrable_gibbs_average_n_det_comp_of_bounded (P := P) A c₀ m (fun _ => f)
      (hcB.comp (A.continuous.add continuous_const)) (B := Bf) (fun _ σs => hfle σs)
  have hI1 : Integrable
      (fun x : Ω => gibbs_average_n_det (α := α) (n := m) (A x + c₀)
        (fun σs => f σs * freshKernelAvg (α := α) (A x + c₀) c (σs i))) P := by
    refine integrable_gibbs_average_n_det_comp_of_bounded (P := P) A c₀ m
      (fun x σs => f σs * freshKernelAvg (α := α) (A x + c₀) c (σs i))
      (hcA.comp (A.continuous.add continuous_const))
      (B := Bf * (‖A‖ * (‖covarianceOperator P‖ * Mw))) fun x σs => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (by simpa [Real.norm_eq_abs] using hfle σs)
      (abs_freshKernelAvg_le (α := α) hkerbd (A x + c₀) (σs i)) (abs_nonneg _) hBf0
  have hI3 : ∀ l : Fin m, Integrable
      (fun x : Ω => gibbs_average_n_det (α := α) (n := m) (A x + c₀)
        (fun σs => f σs * c (σs i) (σs l))) P := by
    intro l
    refine integrable_gibbs_average_n_det_comp_of_bounded (P := P) A c₀ m
      (fun _ σs => f σs * c (σs i) (σs l))
      ((hcD l).comp (A.continuous.add continuous_const))
      (B := Bf * (‖A‖ * (‖covarianceOperator P‖ * Mw))) fun x σs => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (by simpa [Real.norm_eq_abs] using hfle σs)
      (hkerbd (σs i) (σs l)) (abs_nonneg _) hBf0
  have hI4 : Integrable
      (fun x : Ω => gibbs_average_n_det (α := α) (n := m) (A x + c₀)
        (fun σs => ⟪x, w (σs i)⟫_ℝ * f σs)) P :=
    integrable_gibbs_average_n_det_inner_mul_comp (P := P) A c₀ hw m f i
  have hstar := integral_gibbs_average_n_det_inner_mul_comp_erase (P := P) hmean0 A c₀ w hdiag
    m f i
  have hIsum : Integrable (fun x : Ω =>
      ∑ l ∈ Finset.univ.erase i, gibbs_average_n_det (α := α) (n := m) (A x + c₀)
        (fun σs => f σs * c (σs i) (σs l))) P :=
    integrable_finsetSum _ fun l _ => hI3 l
  have hIa : Integrable (fun x : Ω => (m : ℝ) *
      gibbs_average_n_det (α := α) (n := m) (A x + c₀)
        (fun σs => f σs * freshKernelAvg (α := α) (A x + c₀) c (σs i))) P := hI1.const_mul _
  have hIb : Integrable (fun x : Ω => d *
      gibbs_average_n_det (α := α) (n := m) (A x + c₀) f) P := hI2.const_mul _
  have hIdiff : Integrable (fun x : Ω =>
      (m : ℝ) * gibbs_average_n_det (α := α) (n := m) (A x + c₀)
          (fun σs => f σs * freshKernelAvg (α := α) (A x + c₀) c (σs i))
        - d * gibbs_average_n_det (α := α) (n := m) (A x + c₀) f) P := hIa.sub hIb
  rw [MeasureTheory.integral_sub hIdiff hIsum,
    MeasureTheory.integral_sub hIa hIb,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finsetSum _ fun l (_ : l ∈ Finset.univ.erase i) => hI3 l] at hstar
  rw [integral_gibbs_average_one_inner_comp (P := P) hmean0 A c₀ hw hdiag]
  linarith [hstar]

end LinearImageDefect

end

end FiniteGibbs


end SpinGlass
