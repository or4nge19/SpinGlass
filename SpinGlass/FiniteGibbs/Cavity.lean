/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Common.Mathlib.Probability.Distributions.Gaussian_IBP_LinearImage
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
- `FiniteGibbs.integral_inner_mul_gibbs_average_n_det`: **the cavity identity**, in an arbitrary
  direction; `integral_apply_mul_gibbs_average_n_det` is its coordinate case.
- `FiniteGibbs.integral_gibbs_average_n_det_inner_mul`: the cavity identity with an arbitrary
  *field* `σ ↦ ⟪H, w σ⟫` inside the bracket — a component of the disorder, for instance;
  `integral_gibbs_average_n_det_energy_mul` is its coordinate case, the energy itself.
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

/-- The derivative of the replica bracket along a *shifted* Hamiltonian is the derivative at the
shifted point: the shift is affine with derivative the identity. -/
lemma fderiv_gibbs_average_n_det_add_const (n : ℕ) (c K : EnergySpace α)
    (f : ReplicaFun (α := α) n) :
    fderiv ℝ (fun K' : EnergySpace α => gibbs_average_n_det (α := α) (n := n) (K' + c) f) K
      = fderiv ℝ (fun K' : EnergySpace α => gibbs_average_n_det (α := α) (n := n) K' f)
          (K + c) := by
  have hd : DifferentiableAt ℝ
      (fun K' : EnergySpace α => gibbs_average_n_det (α := α) (n := n) K' f) (K + c) :=
    ((contDiff_gibbs_average_n_det (α := α) n f).differentiable (by simp)) _
  have h1 : HasFDerivAt (fun K' : EnergySpace α => K' + c)
      (ContinuousLinearMap.id ℝ (EnergySpace α)) K := (hasFDerivAt_id K).add_const c
  have h2 := hd.hasFDerivAt.comp K h1
  have h3 : HasFDerivAt
      (fun K' : EnergySpace α => gibbs_average_n_det (α := α) (n := n) (K' + c) f)
      (fderiv ℝ (fun K' : EnergySpace α => gibbs_average_n_det (α := α) (n := n) K' f) (K + c)) K
        := by
    simpa [Function.comp_def] using h2
  exact h3.fderiv

/-! ### The cavity identity for a Hamiltonian that is a linear image of the disorder -/

section LinearImage

variable {Ω : Type*} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω] [CompleteSpace Ω]
variable [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω]
variable {P : Measure Ω} [IsGaussian P]

/-- **The cavity identity for a Hamiltonian that is a linear image of the disorder.**

The disorder is an abstract centered Gaussian vector `x` on a Hilbert space `Ω`, and the
Hamiltonian is a continuous linear image `A x`. Then for every direction `h` in `Ω`,

`∫ ⟪x, h⟫ ⟨f⟩_{A x} ∂P = ∫ ( n ⟨f⟩ ⟨v⟩ - ∑_{l<n} ⟨f · v(σˡ)⟩ ) ∂P`, where `v = A (C_P h)`

is the **cross-covariance** between the tested direction and the Hamiltonian.

This is the form the cavity method needs when the Hamiltonian is a *sum* of independent pieces and
one differentiates with respect to a single piece: taking `Ω = E × E`, `A (x, y) = x + t y` and
`h = (0, k)` isolates the `y`-component, whose cross kernel is `t` times the `y`-covariance. The
case `Ω = EnergySpace α`, `A = id` is
`SpinGlass.FiniteGibbs.integral_inner_mul_gibbs_average_n_det`.

Talagrand, *Mean Field Models for Spin Glasses*, Vol. I, §1.7 and Vol. II, §12.2. -/
theorem integral_inner_mul_gibbs_average_n_det_comp
    (hmean0 : (∫ x : Ω, x ∂P) = 0) (A : Ω →L[ℝ] EnergySpace α) (c : EnergySpace α)
    (n : ℕ) (f : ReplicaFun (α := α) n) (h : Ω) :
    (∫ x : Ω, ⟪x, h⟫_ℝ * gibbs_average_n_det (α := α) (n := n) (A x + c) f ∂P)
      = ∫ x : Ω,
          ((n : ℝ) * gibbs_average_n_det (α := α) (n := n) (A x + c) f
              * (∑ τ : α, gibbs_pmf (α := α) (A x + c) τ
                  * (A (covarianceOperator P h)) τ)
            - ∑ l : Fin n, gibbs_average_n_det (α := α) (n := n) (A x + c)
                (fun σs => f σs * (A (covarianceOperator P h)) (σs l))) ∂P := by
  classical
  set S : ℝ := ∑ σs : ReplicaSpace (α := α) n, ‖f σs‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set C : ℝ := (1 + 2 * (n : ℝ)) * S with hC
  have hC0 : 0 ≤ C := by positivity
  have hc1 : ContDiff ℝ 1
      (fun K : EnergySpace α => gibbs_average_n_det (α := α) (n := n) (K + c) f) :=
    ((contDiff_gibbs_average_n_det (α := α) n f).of_le (by simp)).comp
      (contDiff_id.add contDiff_const)
  have hgrowth : ∀ K : EnergySpace α,
      |gibbs_average_n_det (α := α) (n := n) (K + c) f| ≤ C * (1 + ‖K‖) ^ 0 := by
    intro K
    have hb := abs_gibbs_average_n_det_le_sum_abs (α := α) n (K + c) f
    have hSC : S ≤ C := by nlinarith [hS0, Nat.cast_nonneg (α := ℝ) n]
    simpa [Real.norm_eq_abs] using hb.trans hSC
  have hgrowth' : ∀ K : EnergySpace α,
      ‖fderiv ℝ (fun K' => gibbs_average_n_det (α := α) (n := n) (K' + c) f) K‖
        ≤ C * (1 + ‖K‖) ^ 0 := by
    intro K
    rw [fderiv_gibbs_average_n_det_add_const (α := α) n c K f]
    have hb := norm_fderiv_gibbs_average_n_det_le (α := α) n (K + c) f
    have hSC : (2 * (n : ℝ)) * S ≤ C := by nlinarith [hS0]
    simpa [Real.norm_eq_abs] using hb.trans hSC
  have hIBP := ProbabilityTheory.IsGaussian.integral_inner_mul_comp_clm P hmean0 A h
    (fun K : EnergySpace α => gibbs_average_n_det (α := α) (n := n) (K + c) f) hc1 hC0
    hgrowth hgrowth'
  rw [hIBP]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [fderiv_gibbs_average_n_det_add_const, fderiv_gibbs_average_n_det_apply_eq]

end LinearImage

variable {μ : Measure (EnergySpace α)} [IsGaussian μ]

/-- **The cavity identity, in an arbitrary direction.** For a centered Gaussian Hamiltonian law
`μ` with covariance operator `C`, every direction `w` and every function `f` of `n` replicas,

`∫ ⟪H, w⟫ ⟨f⟩ dμ = ∫ ( n ⟨f⟩ ⟨C w⟩ - ∑_{l<n} ⟨f · (C w)(σˡ)⟩ ) dμ`.

This is Gaussian integration by parts applied to the Gibbs average as a functional of the
Hamiltonian; it is exact at every finite volume. The generality in `w` is what allows a *component*
of the disorder — say the `p`-spin part of a mixed Hamiltonian, which is a linear image `W H` of it,
so that `(W H) σ = ⟪H, Wᵀ e_σ⟫` — to be treated on the same footing as the energy itself; taking
`w = e_ρ` recovers Talagrand's form. Talagrand, *Mean Field Models for Spin Glasses*, Vol. I, §1.7
and Vol. II, §12.2. -/
theorem integral_inner_mul_gibbs_average_n_det
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0)
    (n : ℕ) (f : ReplicaFun (α := α) n) (w : EnergySpace α) :
    (∫ H : EnergySpace α, ⟪H, w⟫_ℝ * gibbs_average_n_det (α := α) (n := n) H f ∂μ)
      = ∫ H : EnergySpace α,
          ((n : ℝ) * gibbs_average_n_det (α := α) (n := n) H f
              * (∑ τ : α, gibbs_pmf (α := α) H τ * (covarianceOperator μ w) τ)
            - ∑ l : Fin n, gibbs_average_n_det (α := α) (n := n) H
                (fun σs => f σs * (covarianceOperator μ w) (σs l))) ∂μ := by
  have h := integral_inner_mul_gibbs_average_n_det_comp (P := μ) hmean0
    (ContinuousLinearMap.id ℝ (EnergySpace α)) 0 n f w
  simpa using h

/-- **The cavity identity at a coordinate direction.** The case `w = e_ρ` of
`SpinGlass.FiniteGibbs.integral_inner_mul_gibbs_average_n_det`: since `⟪H, e_ρ⟫ = H ρ`, this is
Talagrand's cavity identity for the energy at a single configuration. -/
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
  have hcoord : ∀ H : EnergySpace α, ⟪H, std_basis (α := α) ρ⟫_ℝ = H ρ := fun H => by
    rw [real_inner_comm]; exact inner_std_basis_apply (α := α) ρ H
  rw [← integral_inner_mul_gibbs_average_n_det (μ := μ) hmean0 n f (std_basis (α := α) ρ)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun H => by simp only [hcoord])

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
/-- A field evaluated at the `i`-th replica, expanded over the value of that replica. -/
private lemma sum_apply_mul_gibbs_average_indicator [DecidableEq α]
    (m : ℕ) (H : EnergySpace α) (f : ReplicaFun (α := α) m) (i : Fin m) (u : α → ℝ) :
    (∑ ρ : α, u ρ * gibbs_average_n_det (α := α) (n := m) H
        (fun σs => (if σs i = ρ then (1 : ℝ) else 0) * f σs))
      = gibbs_average_n_det (α := α) (n := m) H (fun σs => u (σs i) * f σs) := by
  classical
  simp only [gibbs_average_n_det, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σs _ => ?_
  rw [show (∑ ρ : α, u ρ * ((if σs i = ρ then (1 : ℝ) else 0) * f σs
        * ∏ l : Fin m, gibbs_pmf (α := α) H (σs l)))
      = ∑ ρ : α, (if σs i = ρ then
          u ρ * (f σs * ∏ l : Fin m, gibbs_pmf (α := α) H (σs l)) else 0) from
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
theorem integral_gibbs_average_n_det_inner_mul
    (hmean0 : (∫ x : EnergySpace α, x ∂μ) = 0) (w : α → EnergySpace α)
    (m : ℕ) (f : ReplicaFun (α := α) m) (i : Fin m) :
    (∫ H : EnergySpace α,
        gibbs_average_n_det (α := α) (n := m) H (fun σs => ⟪H, w (σs i)⟫_ℝ * f σs) ∂μ)
      = ∫ H : EnergySpace α,
          ((m : ℝ) * gibbs_average_n_det (α := α) (n := m) H
              (fun σs => f σs * (∑ τ : α, gibbs_pmf (α := α) H τ
                  * (covarianceOperator μ (w (σs i))) τ))
            - ∑ l : Fin m, gibbs_average_n_det (α := α) (n := m) H
                (fun σs => f σs * (covarianceOperator μ (w (σs i))) (σs l))) ∂μ := by
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
        ⟪H, w ρ⟫_ℝ * gibbs_average_n_det (α := α) (n := m) H (fρ ρ) ∂μ)
      = ∫ H : EnergySpace α,
          ((m : ℝ) * gibbs_average_n_det (α := α) (n := m) H (fρ ρ)
              * (∑ τ : α, gibbs_pmf (α := α) H τ * (covarianceOperator μ (w ρ)) τ)
            - ∑ l : Fin m, gibbs_average_n_det (α := α) (n := m) H
                (fun σs => fρ ρ σs * (covarianceOperator μ (w ρ)) (σs l))) ∂μ :=
    fun ρ => integral_inner_mul_gibbs_average_n_det (μ := μ) hmean0 m (fρ ρ) (w ρ)
  -- integrability of every piece
  have hcontAvg : ∀ (g : ReplicaFun (α := α) m),
      Continuous fun H : EnergySpace α => gibbs_average_n_det (α := α) (n := m) H g :=
    fun g => (contDiff_gibbs_average_n_det (α := α) m g).continuous
  have hIntL : ∀ ρ : α, Integrable
      (fun H : EnergySpace α => ⟪H, w ρ⟫_ℝ * gibbs_average_n_det (α := α) (n := m) H (fρ ρ)) μ := by
    intro ρ
    have hcontIn : Continuous fun H : EnergySpace α => ⟪H, w ρ⟫_ℝ :=
      continuous_id.inner continuous_const
    refine ProbabilityTheory.IsGaussian.integrable_of_abs_le_mul_one_add_norm_pow (μ := μ)
      ((hcontIn.mul (hcontAvg (fρ ρ))).measurable)
      (C := S * ‖w ρ‖) (m := 1) (mul_nonneg hS0 (norm_nonneg _)) fun H => ?_
    have h1 : |⟪H, w ρ⟫_ℝ| ≤ ‖H‖ * ‖w ρ‖ := abs_real_inner_le_norm H (w ρ)
    have h2 : |gibbs_average_n_det (α := α) (n := m) H (fρ ρ)| ≤ S :=
      le_trans (abs_gibbs_average_n_det_le_sum_abs (α := α) m H (fρ ρ)) (hfρ_bdd ρ)
    have h3 : |⟪H, w ρ⟫_ℝ * gibbs_average_n_det (α := α) (n := m) H (fρ ρ)|
        ≤ (‖H‖ * ‖w ρ‖) * S := by
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    refine h3.trans ?_
    have hn : (0 : ℝ) ≤ ‖H‖ := norm_nonneg H
    have hw : (0 : ℝ) ≤ ‖w ρ‖ := norm_nonneg (w ρ)
    have hpow : (1 + ‖H‖) ^ 1 = 1 + ‖H‖ := pow_one _
    rw [hpow]
    nlinarith [hS0, hn, hw]
  set v : α → EnergySpace α := fun ρ => covarianceOperator μ (w ρ) with hv
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
        ⟪H, w ρ⟫_ℝ * gibbs_average_n_det (α := α) (n := m) H (fρ ρ) ∂μ)
      = ∑ ρ : α, ∫ H : EnergySpace α,
          ((m : ℝ) * gibbs_average_n_det (α := α) (n := m) H (fρ ρ)
              * (∑ τ : α, gibbs_pmf (α := α) H τ * (v ρ) τ)
            - ∑ l : Fin m, gibbs_average_n_det (α := α) (n := m) H
                (fun σs => fρ ρ σs * (v ρ) (σs l))) ∂μ :=
    Finset.sum_congr rfl fun ρ _ => hcav ρ
  rw [← MeasureTheory.integral_finsetSum _ fun ρ (_ : ρ ∈ Finset.univ) => hIntL ρ,
    ← MeasureTheory.integral_finsetSum _ fun ρ (_ : ρ ∈ Finset.univ) => hIntR ρ] at hsum
  calc (∫ H : EnergySpace α,
        gibbs_average_n_det (α := α) (n := m) H (fun σs => ⟪H, w (σs i)⟫_ℝ * f σs) ∂μ)
      = ∫ H : EnergySpace α, (∑ ρ : α,
          ⟪H, w ρ⟫_ℝ * gibbs_average_n_det (α := α) (n := m) H (fρ ρ)) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun H =>
          (sum_apply_mul_gibbs_average_indicator (α := α) m H f i
            (fun ρ => ⟪H, w ρ⟫_ℝ)).symm)
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

/-- **The cavity identity with the energy inside the bracket.** The coordinate case `w = e_·` of
`SpinGlass.FiniteGibbs.integral_gibbs_average_n_det_inner_mul`:

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
  rw [← integral_gibbs_average_n_det_inner_mul (μ := μ) hmean0
    (fun ρ => std_basis (α := α) ρ) m f i]
  refine integral_congr_ae (Filter.Eventually.of_forall fun H => ?_)
  exact congrArg (gibbs_average_n_det (α := α) (n := m) H) (funext fun σs => by
    rw [real_inner_comm, inner_std_basis_apply (α := α) (σs i) H])

/-! ### The field cavity identity for a linear-image Hamiltonian -/

section LinearImageField

variable {Ω : Type*} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω] [CompleteSpace Ω]
variable [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω]
variable {P : Measure Ω} [IsGaussian P]

private lemma integrable_of_bounded_gaussian {g : Ω → ℝ} (hg : Continuous g)
    {C : ℝ} (hC : ∀ x, |g x| ≤ C) : Integrable g P := by
  have h0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  exact ProbabilityTheory.IsGaussian.integrable_of_abs_le_mul_one_add_norm_pow (μ := P)
    hg.measurable (C := C) (m := 0) h0 (fun x => by simp [hC x])

/-- **The cavity identity with a component field inside the bracket, for a Hamiltonian that is a
linear image of the disorder.**

The disorder is an abstract centered Gaussian vector `x`, the Hamiltonian is `A x`, and the field
tested inside the bracket is `σ ↦ ⟪x, w σ⟫` for a family of directions `w` in the *disorder*
space. The kernel that appears is the cross-covariance `c(σ, τ) = (A (C_P (w σ))) τ`, which is
`Cov(⟪x, w σ⟫, (A x) τ)`.

Taking `Ω = EnergySpace α`, `A = id` and `w = e_·` recovers
`SpinGlass.FiniteGibbs.integral_gibbs_average_n_det_energy_mul`. Taking `Ω = E × E`,
`A (x, y) = x + t y` and `w σ = (0, e_σ)` isolates the second summand of the Hamiltonian: the
kernel becomes `t` times the second block's covariance. Talagrand, Vol. I, §1.7; Vol. II, §12.2. -/
theorem integral_gibbs_average_n_det_inner_mul_comp
    (hmean0 : (∫ x : Ω, x ∂P) = 0) (A : Ω →L[ℝ] EnergySpace α) (c : EnergySpace α) (w : α → Ω)
    (m : ℕ) (f : ReplicaFun (α := α) m) (i : Fin m) :
    (∫ x : Ω, gibbs_average_n_det (α := α) (n := m) (A x + c)
        (fun σs => ⟪x, w (σs i)⟫_ℝ * f σs) ∂P)
      = ∫ x : Ω,
          ((m : ℝ) * gibbs_average_n_det (α := α) (n := m) (A x + c)
              (fun σs => f σs * (∑ τ : α, gibbs_pmf (α := α) (A x + c) τ
                  * (A (covarianceOperator P (w (σs i)))) τ))
            - ∑ l : Fin m, gibbs_average_n_det (α := α) (n := m) (A x + c)
                (fun σs => f σs * (A (covarianceOperator P (w (σs i)))) (σs l))) ∂P := by
  classical
  set S : ℝ := ∑ σs : ReplicaSpace (α := α) m, ‖f σs‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set fρ : α → ReplicaFun (α := α) m :=
    fun ρ σs => (if σs i = ρ then (1 : ℝ) else 0) * f σs with hfρ
  have hfρ_bdd : ∀ ρ, (∑ σs : ReplicaSpace (α := α) m, ‖fρ ρ σs‖) ≤ S := by
    intro ρ
    refine Finset.sum_le_sum fun σs _ => ?_
    rw [hfρ]
    by_cases hρ : σs i = ρ <;> simp [hρ]
  -- the per-direction cavity identity
  set v : α → EnergySpace α := fun ρ => A (covarianceOperator P (w ρ)) with hv
  have hcav : ∀ ρ : α, (∫ x : Ω,
        ⟪x, w ρ⟫_ℝ * gibbs_average_n_det (α := α) (n := m) (A x + c) (fρ ρ) ∂P)
      = ∫ x : Ω,
          ((m : ℝ) * gibbs_average_n_det (α := α) (n := m) (A x + c) (fρ ρ)
              * (∑ τ : α, gibbs_pmf (α := α) (A x + c) τ * (v ρ) τ)
            - ∑ l : Fin m, gibbs_average_n_det (α := α) (n := m) (A x + c)
                (fun σs => fρ ρ σs * (v ρ) (σs l))) ∂P :=
    fun ρ => integral_inner_mul_gibbs_average_n_det_comp (P := P) hmean0 A c m (fρ ρ) (w ρ)
  have hcontAvg : ∀ (g : ReplicaFun (α := α) m),
      Continuous fun x : Ω => gibbs_average_n_det (α := α) (n := m) (A x + c) g :=
    fun g => (contDiff_gibbs_average_n_det (α := α) m g).continuous.comp
      (A.continuous.add continuous_const)
  have hIntL : ∀ ρ : α, Integrable
      (fun x : Ω => ⟪x, w ρ⟫_ℝ * gibbs_average_n_det (α := α) (n := m) (A x + c) (fρ ρ)) P := by
    intro ρ
    have hcontIn : Continuous fun x : Ω => ⟪x, w ρ⟫_ℝ :=
      continuous_id.inner continuous_const
    refine ProbabilityTheory.IsGaussian.integrable_of_abs_le_mul_one_add_norm_pow (μ := P)
      ((hcontIn.mul (hcontAvg (fρ ρ))).measurable)
      (C := S * ‖w ρ‖) (m := 1) (mul_nonneg hS0 (norm_nonneg _)) fun x => ?_
    have h1 : |⟪x, w ρ⟫_ℝ| ≤ ‖x‖ * ‖w ρ‖ := abs_real_inner_le_norm x (w ρ)
    have h2 : |gibbs_average_n_det (α := α) (n := m) (A x + c) (fρ ρ)| ≤ S :=
      le_trans (abs_gibbs_average_n_det_le_sum_abs (α := α) m (A x + c) (fρ ρ)) (hfρ_bdd ρ)
    have h3 : |⟪x, w ρ⟫_ℝ * gibbs_average_n_det (α := α) (n := m) (A x + c) (fρ ρ)|
        ≤ (‖x‖ * ‖w ρ‖) * S := by
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    refine h3.trans ?_
    have hn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
    have hwn : (0 : ℝ) ≤ ‖w ρ‖ := norm_nonneg (w ρ)
    have hpow : (1 + ‖x‖) ^ 1 = 1 + ‖x‖ := pow_one _
    rw [hpow]
    nlinarith [hS0, hn, hwn]
  have hIntR : ∀ ρ : α, Integrable
      (fun x : Ω =>
        (m : ℝ) * gibbs_average_n_det (α := α) (n := m) (A x + c) (fρ ρ)
            * (∑ τ : α, gibbs_pmf (α := α) (A x + c) τ * (v ρ) τ)
          - ∑ l : Fin m, gibbs_average_n_det (α := α) (n := m) (A x + c)
              (fun σs => fρ ρ σs * (v ρ) (σs l))) P := by
    intro ρ
    refine integrable_of_bounded_gaussian (P := P) ?_ (C := (m : ℝ) * (S * ‖v ρ‖)
        + (m : ℝ) * (S * ‖v ρ‖)) fun x => ?_
    · refine ((continuous_const.mul (hcontAvg (fρ ρ))).mul ?_).sub ?_
      · exact (continuous_finsetSum _ fun τ _ =>
          ((contDiff_gibbs_pmf (α := α) τ).continuous).mul continuous_const).comp
            (A.continuous.add continuous_const)
      · exact continuous_finsetSum _ fun l _ => hcontAvg _
    · have hA : |gibbs_average_n_det (α := α) (n := m) (A x + c) (fρ ρ)| ≤ S :=
        le_trans (abs_gibbs_average_n_det_le_sum_abs (α := α) m (A x + c) (fρ ρ)) (hfρ_bdd ρ)
      have hB : |∑ τ : α, gibbs_pmf (α := α) (A x + c) τ * (v ρ) τ| ≤ ‖v ρ‖ := by
        simpa [gibbs_pmf_eq_softmax] using Real.abs_sum_softmax_mul_le (-(A x + c)) (v ρ)
      have h1 : |(m : ℝ) * gibbs_average_n_det (α := α) (n := m) (A x + c) (fρ ρ)
          * (∑ τ : α, gibbs_pmf (α := α) (A x + c) τ * (v ρ) τ)| ≤ (m : ℝ) * (S * ‖v ρ‖) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg m), mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hA hB (abs_nonneg _) hS0) (Nat.cast_nonneg m)
      have h2 : |∑ l : Fin m, gibbs_average_n_det (α := α) (n := m) (A x + c)
          (fun σs => fρ ρ σs * (v ρ) (σs l))| ≤ (m : ℝ) * (S * ‖v ρ‖) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        have hterm : ∀ l : Fin m, |gibbs_average_n_det (α := α) (n := m) (A x + c)
            (fun σs => fρ ρ σs * (v ρ) (σs l))| ≤ S * ‖v ρ‖ := by
          intro l
          refine le_trans (abs_gibbs_average_n_det_le_sum_abs (α := α) m (A x + c) _) ?_
          calc (∑ σs : ReplicaSpace (α := α) m, ‖fρ ρ σs * (v ρ) (σs l)‖)
              ≤ ∑ σs : ReplicaSpace (α := α) m, ‖fρ ρ σs‖ * ‖v ρ‖ := by
                refine Finset.sum_le_sum fun σs _ => ?_
                rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
                exact mul_le_mul_of_nonneg_left (abs_apply_le_norm (α := α) (v ρ) (σs l))
                  (abs_nonneg _)
            _ = (∑ σs : ReplicaSpace (α := α) m, ‖fρ ρ σs‖) * ‖v ρ‖ := (Finset.sum_mul _ _ _).symm
            _ ≤ S * ‖v ρ‖ := mul_le_mul_of_nonneg_right (hfρ_bdd ρ) (norm_nonneg _)
        calc (∑ l : Fin m, |gibbs_average_n_det (α := α) (n := m) (A x + c)
              (fun σs => fρ ρ σs * (v ρ) (σs l))|)
            ≤ ∑ _l : Fin m, S * ‖v ρ‖ := Finset.sum_le_sum fun l _ => hterm l
          _ = (m : ℝ) * (S * ‖v ρ‖) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact le_trans (abs_sub _ _) (add_le_add h1 h2)
  have hsum : (∑ ρ : α, ∫ x : Ω,
        ⟪x, w ρ⟫_ℝ * gibbs_average_n_det (α := α) (n := m) (A x + c) (fρ ρ) ∂P)
      = ∑ ρ : α, ∫ x : Ω,
          ((m : ℝ) * gibbs_average_n_det (α := α) (n := m) (A x + c) (fρ ρ)
              * (∑ τ : α, gibbs_pmf (α := α) (A x + c) τ * (v ρ) τ)
            - ∑ l : Fin m, gibbs_average_n_det (α := α) (n := m) (A x + c)
                (fun σs => fρ ρ σs * (v ρ) (σs l))) ∂P :=
    Finset.sum_congr rfl fun ρ _ => hcav ρ
  rw [← MeasureTheory.integral_finsetSum _ fun ρ (_ : ρ ∈ Finset.univ) => hIntL ρ,
    ← MeasureTheory.integral_finsetSum _ fun ρ (_ : ρ ∈ Finset.univ) => hIntR ρ] at hsum
  calc (∫ x : Ω, gibbs_average_n_det (α := α) (n := m) (A x + c)
        (fun σs => ⟪x, w (σs i)⟫_ℝ * f σs) ∂P)
      = ∫ x : Ω, (∑ ρ : α,
          ⟪x, w ρ⟫_ℝ * gibbs_average_n_det (α := α) (n := m) (A x + c) (fρ ρ)) ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall fun x =>
          (sum_apply_mul_gibbs_average_indicator (α := α) m (A x + c) f i
            (fun ρ => ⟪x, w ρ⟫_ℝ)).symm)
    _ = ∫ x : Ω, (∑ ρ : α,
          ((m : ℝ) * gibbs_average_n_det (α := α) (n := m) (A x + c) (fρ ρ)
              * (∑ τ : α, gibbs_pmf (α := α) (A x + c) τ * (v ρ) τ)
            - ∑ l : Fin m, gibbs_average_n_det (α := α) (n := m) (A x + c)
                (fun σs => fρ ρ σs * (v ρ) (σs l)))) ∂P := hsum
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only []
  rw [Finset.sum_sub_distrib, hv]
  congr 1
  · rw [show (∑ ρ : α, (m : ℝ) * gibbs_average_n_det (α := α) (n := m) (A x + c) (fρ ρ)
          * (∑ τ : α, gibbs_pmf (α := α) (A x + c) τ * (v ρ) τ))
        = (m : ℝ) * ∑ ρ : α, gibbs_average_n_det (α := α) (n := m) (A x + c) (fρ ρ)
            * (∑ τ : α, gibbs_pmf (α := α) (A x + c) τ * (v ρ) τ) from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun ρ _ => by ring,
      sum_gibbs_average_indicator_mul (α := α) m (A x + c) f i
        (fun ρ => ∑ τ : α, gibbs_pmf (α := α) (A x + c) τ * (v ρ) τ)]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    exact sum_gibbs_average_indicator_weight (α := α) m (A x + c) f i (fun ρ σs => (v ρ) (σs l))

end LinearImageField

end

end FiniteGibbs

end SpinGlass
