/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.FiniteGibbs.ReplicaCalculus
import Common.Mathlib.Probability.Distributions.Gaussian_IBP_Hilbert

/-!
# The cavity identity for Gibbs averages of a Gaussian Hamiltonian

Let `H` be a centered Gaussian Hamiltonian on a finite configuration space `α`, with covariance
kernel `c ρ τ = ⟪C e_ρ, e_τ⟫` in the Dirac basis, and let `⟨·⟩` denote the `n`-replica Gibbs
average `gibbs_average_n_det`. Gaussian integration by parts, applied to the Gibbs average as a
functional of the Hamiltonian, gives the **exact** identity

`𝔼[H_ρ ⟨f⟩] = n · 𝔼[⟨f⟩ · ⟨c ρ ·⟩] - ∑_{l<n} 𝔼⟨f · c ρ σˡ⟩`,

valid at every finite volume and for every bounded `f` of `n` replicas. Summing over `ρ` against a
replica turns the left-hand side into `𝔼⟨H_{σ¹} f⟩` and the first term into an average over a
*fresh* replica `σⁿ⁺¹`, which is the form used in the cavity method.

This identity is the exact finite-volume statement underlying the Ghirlanda–Guerra identities.
The Ghirlanda–Guerra identities themselves are *not* exact at finite volume — they are what remains
after replacing `H_{σ¹}` by its mean, which is legitimate only up to the fluctuation of the
Hamiltonian — so the cavity identity, not GG, is what can be proved here without a limit.

Everything is model-agnostic: `α` is an arbitrary finite nonempty type and `μ` an arbitrary
centered Gaussian law on `EnergySpace α`.

## Main statements

- `FiniteGibbs.contDiff_gibbs_average_n_det`: the replica average is smooth in the Hamiltonian.
- `FiniteGibbs.fderiv_gibbs_average_n_det_apply_eq`: its derivative in the direction `v`,
  reorganized as `n ⟨f⟩ ⟨v⟩ - ∑_l ⟨f v(σˡ)⟩`.
- `FiniteGibbs.integral_apply_mul_gibbs_average_n_det`: **the cavity identity**.
-/

open MeasureTheory ProbabilityTheory BigOperators
open scoped InnerProductSpace ContDiff

namespace SpinGlass

namespace FiniteGibbs

noncomputable section

variable {α : Type*} [Fintype α] [Nonempty α]

/-- The replica Gibbs average is smooth in the Hamiltonian. -/
lemma contDiff_gibbs_average_n_det (n : ℕ) (f : ReplicaFun (α := α) n) :
    ContDiff ℝ (∞) (fun H : EnergySpace α => gibbs_average_n_det (α := α) (n := n) H f) := by
  classical
  refine ContDiff.sum (𝕜 := ℝ) (n := (∞)) (s := (Finset.univ : Finset (ReplicaSpace (α := α) n)))
    (f := fun σs H => f σs * ∏ l : Fin n, gibbs_pmf (α := α) H (σs l)) fun σs _ => ?_
  exact contDiff_const.mul (contDiff_prod fun l _ => contDiff_gibbs_pmf (α := α) (σs l))

/-- The derivative of the replica Gibbs average, reorganized: differentiating the `n` Gibbs
factors produces `n` copies of the Gibbs average of the direction, minus one evaluation of the
direction at each replica. -/
lemma fderiv_gibbs_average_n_det_apply_eq (n : ℕ) (H v : EnergySpace α)
    (f : ReplicaFun (α := α) n) :
    fderiv ℝ (fun H' => gibbs_average_n_det (α := α) (n := n) H' f) H v
      = (n : ℝ) * gibbs_average_n_det (α := α) (n := n) H f
            * (∑ τ : α, gibbs_pmf (α := α) H τ * v τ)
        - ∑ l : Fin n, gibbs_average_n_det (α := α) (n := n) H (fun σs => f σs * v (σs l)) := by
  classical
  rw [fderiv_gibbs_average_n_det_apply]
  set A : ℝ := ∑ τ : α, gibbs_pmf (α := α) H τ * v τ with hA
  -- Expand each summand and separate the two contributions.
  have hsum : ∀ σs : ReplicaSpace (α := α) n,
      (∑ _l : Fin n, (A - v (σs _l))) = (n : ℝ) * A - ∑ l : Fin n, v (σs l) := by
    intro σs
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have hterm : ∀ σs : ReplicaSpace (α := α) n,
      f σs * (∏ l : Fin n, gibbs_pmf (α := α) H (σs l)) * ∑ _l : Fin n, (A - v (σs _l))
        = (n : ℝ) * A * (f σs * ∏ l : Fin n, gibbs_pmf (α := α) H (σs l))
          - ∑ l : Fin n, (f σs * v (σs l)) * ∏ k : Fin n, gibbs_pmf (α := α) H (σs k) := by
    intro σs
    have hdist : f σs * (∏ l : Fin n, gibbs_pmf (α := α) H (σs l)) * ∑ l : Fin n, v (σs l)
        = ∑ l : Fin n, (f σs * v (σs l)) * ∏ k : Fin n, gibbs_pmf (α := α) H (σs k) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [hsum σs, mul_sub, hdist]
    ring
  rw [Finset.sum_congr rfl fun σs _ => hterm σs, Finset.sum_sub_distrib]
  congr 1
  · rw [show (∑ σs : ReplicaSpace (α := α) n,
          (n : ℝ) * A * (f σs * ∏ l : Fin n, gibbs_pmf (α := α) H (σs l)))
        = ((n : ℝ) * A) * ∑ σs : ReplicaSpace (α := α) n,
            f σs * ∏ l : Fin n, gibbs_pmf (α := α) H (σs l) from (Finset.mul_sum _ _ _).symm,
      gibbs_average_n_det, hA]
    ring
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => by rw [gibbs_average_n_det]

variable {μ : Measure (EnergySpace α)} [IsGaussian μ]

/-- **The cavity identity.** For a centered Gaussian Hamiltonian law `μ` with covariance operator
`C`, every `ρ : α` and every function `f` of `n` replicas,

`∫ H_ρ ⟨f⟩ dμ = ∫ ( n ⟨f⟩ ⟨C e_ρ⟩ - ∑_{l<n} ⟨f · (C e_ρ)(σˡ)⟩ ) dμ`.

This is Gaussian integration by parts applied to the Gibbs average as a functional of the
Hamiltonian; it is exact at every finite volume. Talagrand, *Mean Field Models for Spin Glasses*,
Vol. I, §1.7 and Vol. II, §12.2. -/
theorem integral_apply_mul_gibbs_average_n_det
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0)
    (n : ℕ) (f : ReplicaFun (α := α) n) (ρ : α) :
    (∫ H : EnergySpace α, H ρ * gibbs_average_n_det (α := α) (n := n) H f ∂μ)
      = ∫ H : EnergySpace α,
          ((n : ℝ) * gibbs_average_n_det (α := α) (n := n) H f
              * (∑ τ : α, gibbs_pmf (α := α) H τ
                  * (covarianceOperator μ (std_basis (α := α) ρ)) τ)
            - ∑ l : Fin n, gibbs_average_n_det (α := α) (n := n) H
                (fun σs => f σs * (covarianceOperator μ (std_basis (α := α) ρ)) (σs l))) ∂μ := by
  classical
  set S : ℝ := ∑ σs : ReplicaSpace (α := α) n, ‖f σs‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set C : ℝ := (1 + 2 * (n : ℝ)) * S with hC
  have hC0 : 0 ≤ C := by positivity
  have hc1 : ContDiff ℝ 1
      (fun H : EnergySpace α => gibbs_average_n_det (α := α) (n := n) H f) :=
    (contDiff_gibbs_average_n_det (α := α) n f).of_le (by simp)
  have hmeas : Measurable
      (fun H : EnergySpace α => gibbs_average_n_det (α := α) (n := n) H f) :=
    hc1.continuous.measurable
  have hgrowth : ∀ H : EnergySpace α,
      |gibbs_average_n_det (α := α) (n := n) H f| ≤ C * (1 + ‖H‖) ^ 0 := by
    intro H
    have h := abs_gibbs_average_n_det_le_sum_abs (α := α) n H f
    have hSC : S ≤ C := by nlinarith [hS0, Nat.cast_nonneg (α := ℝ) n]
    simpa [Real.norm_eq_abs] using h.trans hSC
  have hgrowth' : ∀ H : EnergySpace α,
      ‖fderiv ℝ (fun H' => gibbs_average_n_det (α := α) (n := n) H' f) H‖
        ≤ C * (1 + ‖H‖) ^ 0 := by
    intro H
    have h := norm_fderiv_gibbs_average_n_det_le (α := α) n H f
    have hSC : (2 * (n : ℝ)) * S ≤ C := by nlinarith [hS0]
    simpa [Real.norm_eq_abs] using h.trans hSC
  have hIBP := ProbabilityTheory.IsGaussian.integral_inner_mul_eq_integral_fderiv_covarianceOperator
    (μ := μ) hmean0 (std_basis (α := α) ρ)
    (fun H : EnergySpace α => gibbs_average_n_det (α := α) (n := n) H f)
    hmeas hc1 hC0 hgrowth hgrowth'
  have hcoord : ∀ H : EnergySpace α, ⟪H, std_basis (α := α) ρ⟫_ℝ = H ρ := by
    intro H
    rw [real_inner_comm]
    exact inner_std_basis_apply (α := α) ρ H
  calc (∫ H : EnergySpace α, H ρ * gibbs_average_n_det (α := α) (n := n) H f ∂μ)
      = ∫ H : EnergySpace α,
          ⟪H, std_basis (α := α) ρ⟫_ℝ * gibbs_average_n_det (α := α) (n := n) H f ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun H => by simp only [hcoord])
    _ = ∫ H : EnergySpace α,
          (fderiv ℝ (fun H' => gibbs_average_n_det (α := α) (n := n) H' f) H)
            (covarianceOperator μ (std_basis (α := α) ρ)) ∂μ := hIBP
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun H => by
        simp only []
        rw [fderiv_gibbs_average_n_det_apply_eq])

/-! ### The cavity identity with the energy inside the bracket -/

omit [Nonempty α] in
/-- Collapsing an indicator on the `i`-th replica against a weight. -/
private lemma sum_gibbs_average_indicator_mul [DecidableEq α]
    (m : ℕ) (H : EnergySpace α) (f : ReplicaFun (α := α) m) (i : Fin m) (A : α → ℝ) :
    (∑ ρ : α, gibbs_average_n_det (α := α) (n := m) H
        (fun σs => (if σs i = ρ then (1 : ℝ) else 0) * f σs) * A ρ)
      = gibbs_average_n_det (α := α) (n := m) H (fun σs => f σs * A (σs i)) := by
  classical
  simp only [gibbs_average_n_det, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σs _ => ?_
  rw [show (∑ ρ : α, (if σs i = ρ then (1 : ℝ) else 0) * f σs
        * (∏ l : Fin m, gibbs_pmf (α := α) H (σs l)) * A ρ)
      = ∑ ρ : α, (if σs i = ρ then
          f σs * (∏ l : Fin m, gibbs_pmf (α := α) H (σs l)) * A ρ else 0) from
    Finset.sum_congr rfl fun ρ _ => by
      by_cases hρ : σs i = ρ <;> simp [hρ]]
  rw [Finset.sum_ite_eq Finset.univ (σs i)]
  simp
  ring

omit [Nonempty α] in
/-- Collapsing an indicator on the `i`-th replica against an arbitrary weight inside the
bracket. -/
private lemma sum_gibbs_average_indicator_weight [DecidableEq α]
    (m : ℕ) (H : EnergySpace α) (f : ReplicaFun (α := α) m) (i : Fin m)
    (W : α → ReplicaSpace (α := α) m → ℝ) :
    (∑ ρ : α, gibbs_average_n_det (α := α) (n := m) H
        (fun σs => (if σs i = ρ then (1 : ℝ) else 0) * f σs * W ρ σs))
      = gibbs_average_n_det (α := α) (n := m) H (fun σs => f σs * W (σs i) σs) := by
  classical
  simp only [gibbs_average_n_det]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σs _ => ?_
  rw [show (∑ ρ : α, (if σs i = ρ then (1 : ℝ) else 0) * f σs * W ρ σs
        * ∏ l : Fin m, gibbs_pmf (α := α) H (σs l))
      = ∑ ρ : α, (if σs i = ρ then
          f σs * W ρ σs * ∏ l : Fin m, gibbs_pmf (α := α) H (σs l) else 0) from
    Finset.sum_congr rfl fun ρ _ => by
      by_cases hρ : σs i = ρ <;> simp [hρ]]
  rw [Finset.sum_ite_eq Finset.univ (σs i)]
  simp

omit [Nonempty α] in
/-- The energy of the `i`-th replica, expanded over the value of that replica. -/
private lemma sum_apply_mul_gibbs_average_indicator [DecidableEq α]
    (m : ℕ) (H : EnergySpace α) (f : ReplicaFun (α := α) m) (i : Fin m) :
    (∑ ρ : α, H ρ * gibbs_average_n_det (α := α) (n := m) H
        (fun σs => (if σs i = ρ then (1 : ℝ) else 0) * f σs))
      = gibbs_average_n_det (α := α) (n := m) H (fun σs => H (σs i) * f σs) := by
  classical
  simp only [gibbs_average_n_det, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σs _ => ?_
  rw [show (∑ ρ : α, H ρ * ((if σs i = ρ then (1 : ℝ) else 0) * f σs
        * ∏ l : Fin m, gibbs_pmf (α := α) H (σs l)))
      = ∑ ρ : α, (if σs i = ρ then
          H ρ * (f σs * ∏ l : Fin m, gibbs_pmf (α := α) H (σs l)) else 0) from
    Finset.sum_congr rfl fun ρ _ => by
      by_cases hρ : σs i = ρ <;> simp [hρ]]
  rw [Finset.sum_ite_eq Finset.univ (σs i)]
  simp
  ring


variable {μ : Measure (EnergySpace α)} [IsGaussian μ]

omit [Nonempty α] in
/-- Every bounded continuous functional of the Hamiltonian is integrable under a Gaussian law. -/
private lemma integrable_of_bounded {g : EnergySpace α → ℝ} (hg : Continuous g)
    {C : ℝ} (hC : ∀ H, |g H| ≤ C) : Integrable g μ := by
  have h0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  exact ProbabilityTheory.IsGaussian.integrable_of_abs_le_mul_one_add_norm_pow (μ := μ)
    hg.measurable (C := C) (m := 0) h0
    (fun H => by simp [hC H])

/-- **The cavity identity, with the energy inside the bracket.** For a centered Gaussian
Hamiltonian law `μ` with covariance operator `C`, any `m` replicas, any `i < m` and any `f`,

`𝔼⟨H_{σⁱ} f⟩ = 𝔼[ m ⟨f · ⟨C e_{σⁱ}⟩⟩ - ∑_{l<m} ⟨f · (C e_{σⁱ})(σˡ)⟩ ]`,

where the inner `⟨C e_{σⁱ}⟩ = ∑_τ G_τ (C e_{σⁱ})(τ)` is the Gibbs average over a *fresh* replica.
This is the form of the cavity identity used in the cavity method: the Hamiltonian evaluated at a
replica is traded for covariances between that replica and the others, plus one fresh replica.
Exact at every finite volume. Talagrand, Vol. I, §1.7; Vol. II, §12.2. -/
theorem integral_gibbs_average_n_det_energy_mul
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0)
    (m : ℕ) (f : ReplicaFun (α := α) m) (i : Fin m) :
    (∫ H : EnergySpace α,
        gibbs_average_n_det (α := α) (n := m) H (fun σs => H (σs i) * f σs) ∂μ)
      = ∫ H : EnergySpace α,
          ((m : ℝ) * gibbs_average_n_det (α := α) (n := m) H
              (fun σs => f σs * (∑ τ : α, gibbs_pmf (α := α) H τ
                  * (covarianceOperator μ (std_basis (α := α) (σs i))) τ))
            - ∑ l : Fin m, gibbs_average_n_det (α := α) (n := m) H
                (fun σs => f σs
                  * (covarianceOperator μ (std_basis (α := α) (σs i))) (σs l))) ∂μ := by
  classical
  set S : ℝ := ∑ σs : ReplicaSpace (α := α) m, ‖f σs‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  -- the indicator-restricted test functions
  set fρ : α → ReplicaFun (α := α) m :=
    fun ρ σs => (if σs i = ρ then (1 : ℝ) else 0) * f σs with hfρ
  have hfρ_bdd : ∀ ρ, (∑ σs : ReplicaSpace (α := α) m, ‖fρ ρ σs‖) ≤ S := by
    intro ρ
    refine Finset.sum_le_sum fun σs _ => ?_
    rw [hfρ]
    by_cases hρ : σs i = ρ <;> simp [hρ]
  -- apply the cavity identity for each value `ρ` of the `i`-th replica, and sum
  have hcav : ∀ ρ : α, (∫ H : EnergySpace α,
        H ρ * gibbs_average_n_det (α := α) (n := m) H (fρ ρ) ∂μ)
      = ∫ H : EnergySpace α,
          ((m : ℝ) * gibbs_average_n_det (α := α) (n := m) H (fρ ρ)
              * (∑ τ : α, gibbs_pmf (α := α) H τ
                  * (covarianceOperator μ (std_basis (α := α) ρ)) τ)
            - ∑ l : Fin m, gibbs_average_n_det (α := α) (n := m) H
                (fun σs => fρ ρ σs
                  * (covarianceOperator μ (std_basis (α := α) ρ)) (σs l))) ∂μ :=
    fun ρ => integral_apply_mul_gibbs_average_n_det (μ := μ) hmean0 m (fρ ρ) ρ
  -- integrability of every piece
  have hcontAvg : ∀ (g : ReplicaFun (α := α) m),
      Continuous fun H : EnergySpace α => gibbs_average_n_det (α := α) (n := m) H g :=
    fun g => (contDiff_gibbs_average_n_det (α := α) m g).continuous
  have hIntL : ∀ ρ : α, Integrable
      (fun H : EnergySpace α => H ρ * gibbs_average_n_det (α := α) (n := m) H (fρ ρ)) μ := by
    intro ρ
    refine ProbabilityTheory.IsGaussian.integrable_of_abs_le_mul_one_add_norm_pow (μ := μ)
      (((evalCLM (α := α) ρ).continuous.mul (hcontAvg (fρ ρ))).measurable)
      (C := S) (m := 1) hS0 fun H => ?_
    have h1 : |H ρ| ≤ ‖H‖ := abs_apply_le_norm (α := α) H ρ
    have h2 : |gibbs_average_n_det (α := α) (n := m) H (fρ ρ)| ≤ S :=
      le_trans (abs_gibbs_average_n_det_le_sum_abs (α := α) m H (fρ ρ)) (hfρ_bdd ρ)
    have h3 : |H ρ * gibbs_average_n_det (α := α) (n := m) H (fρ ρ)| ≤ ‖H‖ * S := by
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    refine h3.trans ?_
    have : ‖H‖ ≤ (1 + ‖H‖) ^ 1 := by simp [le_of_lt (lt_one_add ‖H‖)]
    nlinarith [norm_nonneg H, hS0]
  set v : α → EnergySpace α :=
    fun ρ => covarianceOperator μ (std_basis (α := α) ρ) with hv
  have hIntR : ∀ ρ : α, Integrable
      (fun H : EnergySpace α =>
        (m : ℝ) * gibbs_average_n_det (α := α) (n := m) H (fρ ρ)
            * (∑ τ : α, gibbs_pmf (α := α) H τ * (v ρ) τ)
          - ∑ l : Fin m, gibbs_average_n_det (α := α) (n := m) H
              (fun σs => fρ ρ σs * (v ρ) (σs l))) μ := by
    intro ρ
    refine integrable_of_bounded (μ := μ) ?_ (C := (m : ℝ) * (S * ‖v ρ‖)
        + (m : ℝ) * (S * ‖v ρ‖)) fun H => ?_
    · refine ((continuous_const.mul (hcontAvg (fρ ρ))).mul ?_).sub ?_
      · exact continuous_finsetSum _ fun τ _ =>
          ((contDiff_gibbs_pmf (α := α) τ).continuous).mul continuous_const
      · exact continuous_finsetSum _ fun l _ => hcontAvg _
    · have hA : |gibbs_average_n_det (α := α) (n := m) H (fρ ρ)| ≤ S :=
        le_trans (abs_gibbs_average_n_det_le_sum_abs (α := α) m H (fρ ρ)) (hfρ_bdd ρ)
      have hB : |∑ τ : α, gibbs_pmf (α := α) H τ * (v ρ) τ| ≤ ‖v ρ‖ := by
        simpa [gibbs_pmf_eq_softmax] using Real.abs_sum_softmax_mul_le (-H) (v ρ)
      have h1 : |(m : ℝ) * gibbs_average_n_det (α := α) (n := m) H (fρ ρ)
          * (∑ τ : α, gibbs_pmf (α := α) H τ * (v ρ) τ)| ≤ (m : ℝ) * (S * ‖v ρ‖) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg m), mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hA hB (abs_nonneg _) hS0) (Nat.cast_nonneg m)
      have h2 : |∑ l : Fin m, gibbs_average_n_det (α := α) (n := m) H
          (fun σs => fρ ρ σs * (v ρ) (σs l))| ≤ (m : ℝ) * (S * ‖v ρ‖) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        have hterm : ∀ l : Fin m, |gibbs_average_n_det (α := α) (n := m) H
            (fun σs => fρ ρ σs * (v ρ) (σs l))| ≤ S * ‖v ρ‖ := by
          intro l
          refine le_trans (abs_gibbs_average_n_det_le_sum_abs (α := α) m H _) ?_
          calc (∑ σs : ReplicaSpace (α := α) m, ‖fρ ρ σs * (v ρ) (σs l)‖)
              ≤ ∑ σs : ReplicaSpace (α := α) m, ‖fρ ρ σs‖ * ‖v ρ‖ := by
                refine Finset.sum_le_sum fun σs _ => ?_
                rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
                exact mul_le_mul_of_nonneg_left (abs_apply_le_norm (α := α) (v ρ) (σs l))
                  (abs_nonneg _)
            _ = (∑ σs : ReplicaSpace (α := α) m, ‖fρ ρ σs‖) * ‖v ρ‖ := (Finset.sum_mul _ _ _).symm
            _ ≤ S * ‖v ρ‖ := mul_le_mul_of_nonneg_right (hfρ_bdd ρ) (norm_nonneg _)
        calc (∑ l : Fin m, |gibbs_average_n_det (α := α) (n := m) H
              (fun σs => fρ ρ σs * (v ρ) (σs l))|)
            ≤ ∑ _l : Fin m, S * ‖v ρ‖ := Finset.sum_le_sum fun l _ => hterm l
          _ = (m : ℝ) * (S * ‖v ρ‖) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact le_trans (abs_sub _ _) (add_le_add h1 h2)
  -- sum the per-`ρ` cavity identities and collapse the indicators
  have hsum : (∑ ρ : α, ∫ H : EnergySpace α,
        H ρ * gibbs_average_n_det (α := α) (n := m) H (fρ ρ) ∂μ)
      = ∑ ρ : α, ∫ H : EnergySpace α,
          ((m : ℝ) * gibbs_average_n_det (α := α) (n := m) H (fρ ρ)
              * (∑ τ : α, gibbs_pmf (α := α) H τ * (v ρ) τ)
            - ∑ l : Fin m, gibbs_average_n_det (α := α) (n := m) H
                (fun σs => fρ ρ σs * (v ρ) (σs l))) ∂μ :=
    Finset.sum_congr rfl fun ρ _ => hcav ρ
  rw [← MeasureTheory.integral_finsetSum _ fun ρ (_ : ρ ∈ Finset.univ) => hIntL ρ,
    ← MeasureTheory.integral_finsetSum _ fun ρ (_ : ρ ∈ Finset.univ) => hIntR ρ] at hsum
  calc (∫ H : EnergySpace α,
        gibbs_average_n_det (α := α) (n := m) H (fun σs => H (σs i) * f σs) ∂μ)
      = ∫ H : EnergySpace α, (∑ ρ : α,
          H ρ * gibbs_average_n_det (α := α) (n := m) H (fρ ρ)) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun H =>
          (sum_apply_mul_gibbs_average_indicator (α := α) m H f i).symm)
    _ = ∫ H : EnergySpace α, (∑ ρ : α,
          ((m : ℝ) * gibbs_average_n_det (α := α) (n := m) H (fρ ρ)
              * (∑ τ : α, gibbs_pmf (α := α) H τ * (v ρ) τ)
            - ∑ l : Fin m, gibbs_average_n_det (α := α) (n := m) H
                (fun σs => fρ ρ σs * (v ρ) (σs l)))) ∂μ := hsum
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun H => ?_)
  -- the pointwise collapse of the indicators
  simp only []
  rw [Finset.sum_sub_distrib, hv]
  congr 1
  · rw [show (∑ ρ : α, (m : ℝ) * gibbs_average_n_det (α := α) (n := m) H (fρ ρ)
          * (∑ τ : α, gibbs_pmf (α := α) H τ * (v ρ) τ))
        = (m : ℝ) * ∑ ρ : α, gibbs_average_n_det (α := α) (n := m) H (fρ ρ)
            * (∑ τ : α, gibbs_pmf (α := α) H τ * (v ρ) τ) from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun ρ _ => by ring,
      sum_gibbs_average_indicator_mul (α := α) m H f i
        (fun ρ => ∑ τ : α, gibbs_pmf (α := α) H τ * (v ρ) τ)]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    exact sum_gibbs_average_indicator_weight (α := α) m H f i (fun ρ σs => (v ρ) (σs l))

end

end FiniteGibbs

end SpinGlass
