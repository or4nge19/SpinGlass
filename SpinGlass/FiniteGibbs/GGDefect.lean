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

/-- The Gibbs average of the covariance against a fresh replica: `⟨c ρ ·⟩`. -/
noncomputable def freshCov (μ : Measure (EnergySpace α)) (H : EnergySpace α) (ρ : α) : ℝ :=
  ∑ τ : α, gibbs_pmf (α := α) H τ * (covarianceOperator μ (std_basis (α := α) ρ)) τ

omit [IsGaussian μ] in
lemma continuous_freshCov (ρ : α) :
    Continuous fun H : EnergySpace α => freshCov μ H ρ :=
  continuous_finsetSum _ fun τ _ =>
    ((contDiff_gibbs_pmf (α := α) τ).continuous).mul continuous_const

omit [IsGaussian μ] in
lemma abs_freshCov_le (H : EnergySpace α) (ρ : α) :
    |freshCov μ H ρ| ≤ ‖covarianceOperator μ‖ := by
  have h := Real.abs_sum_softmax_mul_le (-H) (covarianceOperator μ (std_basis (α := α) ρ))
  refine le_trans (by simpa [freshCov, gibbs_pmf_eq_softmax] using h) ?_
  calc ‖covarianceOperator μ (std_basis (α := α) ρ)‖
      ≤ ‖covarianceOperator μ‖ * ‖std_basis (α := α) ρ‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖covarianceOperator μ‖ := by rw [norm_std_basis, mul_one]

/-- **The cavity identity with the diagonal term separated.** When the covariance kernel has
constant diagonal `c σ σ = d`, the `l = i` summand of the cavity identity is `d ⟨f⟩`, and the rest
of the sum runs over `l ≠ i`. -/
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
  classical
  rw [integral_gibbs_average_n_det_energy_mul (μ := μ) hmean0 m f i]
  refine integral_congr_ae (Filter.Eventually.of_forall fun H => ?_)
  have hsplit : (∑ l : Fin m, gibbs_average_n_det (α := α) (n := m) H
        (fun σs => f σs * (covarianceOperator μ (std_basis (α := α) (σs i))) (σs l)))
      = gibbs_average_n_det (α := α) (n := m) H
          (fun σs => f σs * (covarianceOperator μ (std_basis (α := α) (σs i))) (σs i))
        + ∑ l ∈ Finset.univ.erase i, gibbs_average_n_det (α := α) (n := m) H
            (fun σs => f σs
              * (covarianceOperator μ (std_basis (α := α) (σs i))) (σs l)) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have hdiagAvg : gibbs_average_n_det (α := α) (n := m) H
      (fun σs => f σs * (covarianceOperator μ (std_basis (α := α) (σs i))) (σs i))
      = d * gibbs_average_n_det (α := α) (n := m) H f := by
    rw [gibbs_average_n_det, gibbs_average_n_det, Finset.mul_sum]
    exact Finset.sum_congr rfl fun σs _ => by rw [hdiag (σs i)]; ring
  simp only [freshCov]
  rw [hsplit, hdiagAvg]
  ring


/-! ### The mean energy -/

/-- **The mean energy is the mean two-replica covariance, minus the diagonal**:
`𝔼⟨H⟩ = 𝔼⟨c(σ¹, σ²)⟩ - d`. This is the cavity identity at one replica and the constant test
function; it is the `m = 1` shadow of `integral_gibbs_average_n_det_energy_mul_erase`. -/
theorem integral_gibbs_average_one_energy
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0) {d : ℝ}
    (hdiag : ∀ σ : α, (covarianceOperator μ (std_basis (α := α) σ)) σ = d) :
    (∫ H : EnergySpace α,
        gibbs_average_n_det (α := α) (n := 1) H (fun τs => H (τs 0)) ∂μ)
      = (∫ H : EnergySpace α,
          gibbs_average_n_det (α := α) (n := 1) H (fun τs => freshCov μ H (τs 0)) ∂μ) - d := by
  classical
  set K : ℝ := ‖covarianceOperator μ‖ with hK
  have hone := integral_gibbs_average_n_det_energy_mul_erase (μ := μ) hmean0 hdiag 1
    (fun _ => (1 : ℝ)) 0
  have herase : (Finset.univ.erase (0 : Fin 1)) = ∅ := by
    ext l
    simp [Subsingleton.elim l 0]
  have hI1' : Integrable
      (fun H : EnergySpace α => gibbs_average_n_det (α := α) (n := 1) H
        (fun τs => freshCov μ H (τs 0))) μ := by
    refine integrable_gibbs_average_n_det_of_bounded (μ := μ) 1
      (fun H τs => freshCov μ H (τs 0)) ?_ (B := K) fun H τs => ?_
    · simp only [gibbs_average_n_det]
      exact continuous_finsetSum _ fun τs _ =>
        ((continuous_freshCov (μ := μ) (τs 0)).mul
          (continuous_finsetProd _ fun l _ => (contDiff_gibbs_pmf (α := α) (τs l)).continuous))
    · simpa [Real.norm_eq_abs] using abs_freshCov_le (μ := μ) H (τs 0)
  rw [show (fun H : EnergySpace α => gibbs_average_n_det (α := α) (n := 1) H
        (fun τs => H (τs 0))) = fun H : EnergySpace α =>
      gibbs_average_n_det (α := α) (n := 1) H (fun τs => H (τs 0) * (1 : ℝ)) from by
    funext H; simp]
  rw [hone, herase]
  simp only [Finset.sum_empty, sub_zero, Nat.cast_one, one_mul, gibbs_average_one_const,
    mul_one, one_mul]
  rw [MeasureTheory.integral_sub hI1' (integrable_const d), MeasureTheory.integral_const]
  simp

/-! ### The defect identity -/

/-- **The Ghirlanda–Guerra defect is the energy–observable covariance.**

For a centered Gaussian Hamiltonian law whose covariance kernel has constant diagonal `c σ σ = d`
— the case of every mixed `p`-spin model, where `c σ τ = N ξ(R_{στ})` — the failure of the
Ghirlanda–Guerra identity for a test function `f` of `m` replicas is exactly

`𝔼⟨H_{σⁱ} f⟩ - 𝔼⟨f⟩ · 𝔼⟨H⟩`,

the covariance between the Hamiltonian evaluated at the `i`-th replica and the observable. In
particular the identity holds **exactly** iff the energy decorrelates from `f`; asymptotic
self-averaging of the Hamiltonian is what makes this vanish in the limit, and this identity is
what converts a bound on that covariance into a bound on the Ghirlanda–Guerra error.

Talagrand, *Mean Field Models for Spin Glasses*, Vol. II, §12.2. -/
theorem ghirlandaGuerra_defect
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0) {d : ℝ}
    (hdiag : ∀ σ : α, (covarianceOperator μ (std_basis (α := α) σ)) σ = d)
    (m : ℕ) (f : ReplicaFun (α := α) m) (i : Fin m) :
    ((m : ℝ) * (∫ H : EnergySpace α,
          gibbs_average_n_det (α := α) (n := m) H
            (fun σs => f σs * freshCov μ H (σs i)) ∂μ)
        - (∫ H : EnergySpace α, gibbs_average_n_det (α := α) (n := m) H f ∂μ)
            * (∫ H : EnergySpace α,
                gibbs_average_n_det (α := α) (n := 1) H (fun τs => freshCov μ H (τs 0)) ∂μ)
        - ∑ l ∈ Finset.univ.erase i, ∫ H : EnergySpace α,
            gibbs_average_n_det (α := α) (n := m) H
              (fun σs => f σs
                * (covarianceOperator μ (std_basis (α := α) (σs i))) (σs l)) ∂μ)
      = (∫ H : EnergySpace α,
            gibbs_average_n_det (α := α) (n := m) H (fun σs => H (σs i) * f σs) ∂μ)
        - (∫ H : EnergySpace α, gibbs_average_n_det (α := α) (n := m) H f ∂μ)
            * (∫ H : EnergySpace α,
                gibbs_average_n_det (α := α) (n := 1) H (fun τs => H (τs 0)) ∂μ) := by
  classical
  set K : ℝ := ‖covarianceOperator μ‖ with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
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
        (fun σs => f σs * freshCov μ H (σs i))) μ := by
    refine integrable_gibbs_average_n_det_of_bounded (μ := μ) m
      (fun H σs => f σs * freshCov μ H (σs i)) ?_ (B := Bf * K) fun H σs => ?_
    · simp only [gibbs_average_n_det]
      exact continuous_finsetSum _ fun σs _ =>
        ((continuous_const.mul (continuous_freshCov (μ := μ) (σs i))).mul
          (continuous_finsetProd _ fun l _ => (contDiff_gibbs_pmf (α := α) (σs l)).continuous))
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (by simpa [Real.norm_eq_abs] using hfle σs)
        (abs_freshCov_le (μ := μ) H (σs i)) (abs_nonneg _) hBf0
  have hI3 : ∀ l : Fin m, Integrable
      (fun H : EnergySpace α => gibbs_average_n_det (α := α) (n := m) H
        (fun σs => f σs * (covarianceOperator μ (std_basis (α := α) (σs i))) (σs l))) μ := by
    intro l
    refine integrable_gibbs_average_n_det_of_bounded (μ := μ) m
      (fun _ σs => f σs * (covarianceOperator μ (std_basis (α := α) (σs i))) (σs l))
      (hcontAvg _) (B := Bf * K) fun H σs => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (by simpa [Real.norm_eq_abs] using hfle σs)
      (abs_covarianceOperator_std_basis_apply_le (μ := μ) (σs i) (σs l)) (abs_nonneg _) hBf0
  have hI4 : Integrable
      (fun H : EnergySpace α => gibbs_average_n_det (α := α) (n := m) H
        (fun σs => H (σs i) * f σs)) μ := by
    have hcont : Continuous fun H : EnergySpace α =>
        gibbs_average_n_det (α := α) (n := m) H (fun σs => H (σs i) * f σs) := by
      simp only [gibbs_average_n_det]
      exact continuous_finsetSum _ fun σs _ =>
        (((evalCLM (α := α) (σs i)).continuous.mul continuous_const).mul
          (continuous_finsetProd _ fun l _ => (contDiff_gibbs_pmf (α := α) (σs l)).continuous))
    refine ProbabilityTheory.IsGaussian.integrable_of_abs_le_mul_one_add_norm_pow (μ := μ)
      hcont.measurable (C := Bf) (m := 1) hBf0 fun H => ?_
    refine le_trans (abs_gibbs_average_n_det_le_sum_abs (α := α) m H _) ?_
    calc (∑ σs : ReplicaSpace (α := α) m, ‖H (σs i) * f σs‖)
        ≤ ∑ σs : ReplicaSpace (α := α) m, ‖H‖ * ‖f σs‖ := by
          refine Finset.sum_le_sum fun σs _ => ?_
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right (abs_apply_le_norm (α := α) H (σs i))
            (abs_nonneg _)
      _ = ‖H‖ * Bf := by rw [← Finset.mul_sum]
      _ ≤ Bf * (1 + ‖H‖) ^ 1 := by
          have := norm_nonneg H
          nlinarith [hBf0]
  -- (★) the cavity identity with the diagonal separated, split into separate integrals
  have hstar := integral_gibbs_average_n_det_energy_mul_erase (μ := μ) hmean0 hdiag m f i
  have hIsum : Integrable (fun H : EnergySpace α =>
      ∑ l ∈ Finset.univ.erase i, gibbs_average_n_det (α := α) (n := m) H
        (fun σs => f σs
          * (covarianceOperator μ (std_basis (α := α) (σs i))) (σs l))) μ :=
    integrable_finsetSum _ fun l _ => hI3 l
  have hIa : Integrable (fun H : EnergySpace α => (m : ℝ) *
      gibbs_average_n_det (α := α) (n := m) H
        (fun σs => f σs * freshCov μ H (σs i))) μ := hI1.const_mul _
  have hIb : Integrable (fun H : EnergySpace α => d *
      gibbs_average_n_det (α := α) (n := m) H f) μ := hI2.const_mul _
  have hIdiff : Integrable (fun H : EnergySpace α =>
      (m : ℝ) * gibbs_average_n_det (α := α) (n := m) H
          (fun σs => f σs * freshCov μ H (σs i))
        - d * gibbs_average_n_det (α := α) (n := m) H f) μ := hIa.sub hIb
  rw [MeasureTheory.integral_sub hIdiff hIsum,
    MeasureTheory.integral_sub hIa hIb,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finsetSum _ fun l (_ : l ∈ Finset.univ.erase i) => hI3 l] at hstar
  -- (★★) the mean energy, from the same identity at one replica
  rw [integral_gibbs_average_one_energy (μ := μ) hmean0 hdiag]
  linarith [hstar]

end

end FiniteGibbs

end SpinGlass
