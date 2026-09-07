import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Common.Mathlib.Analysis.SpecialFunctions.LogSumExp

/-!
# Finite Gibbs calculus

Model-agnostic finite-volume free energy `H ↦ (1/n) log (∑ σ, exp(-H σ))` on a finite type `α`.
Fréchet derivatives, Hessian = Gibbs covariance, trace formulae. Talagrand Vol. I–II.

These objects **are** the general log-sum-exp objects of
`Common.Mathlib.Analysis.SpecialFunctions.LogSumExp` evaluated at the negated Hamiltonian —
`Z_eq_expSum`, `gibbs_pmf_eq_softmax`, `free_energy_density_eq_logSumExp` and
`hessian_free_energy_eq_logSumExpHess` all hold by `rfl` — so every result below is derived from
the general theory rather than reproved. The negation `H ↦ -H` is the continuous linear map
`negCLM`, and the calculus transports along it by `fderiv_comp_clm` and
`fderiv_fderiv_comp_clm_apply`.
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

omit [Fintype α] [Nonempty α] in
/-- `std_basis σ` has coordinate `1` at `σ`. -/
@[simp] lemma std_basis_self_apply (σ : α) : (std_basis (α := α) σ) σ = 1 := by
  classical
  simp [std_basis]

omit [Fintype α] [Nonempty α] in
/-- `std_basis σ` has coordinate `0` away from `σ`. -/
@[simp] lemma std_basis_apply_of_ne {σ τ : α} (h : σ ≠ τ) :
    (std_basis (α := α) σ) τ = 0 := by
  classical
  simp [std_basis, h]

omit [Fintype α] [Nonempty α] in
/-- `std_basis` is Mathlib's `PiLp.single`/`EuclideanSpace.single`, since `EnergySpace α` is
`EuclideanSpace ℝ α`. This is the bridge to Mathlib's orthonormal-basis API. -/
lemma std_basis_eq_single [DecidableEq α] (σ : α) :
    std_basis (α := α) σ = EuclideanSpace.single σ (1 : ℝ) := by
  classical
  refine WithLp.ofLp_injective (p := 2) (funext fun τ => ?_)
  by_cases h : σ = τ
  · subst h; simp
  · simp [h, Ne.symm h]

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

/-! ### Identification with the general log-sum-exp objects

All four identities hold by definition: the finite-volume Gibbs objects are the general
log-sum-exp objects at the negated Hamiltonian. -/

omit [Nonempty α] in
lemma Z_eq_expSum (H : EnergySpace α) : Z (α := α) H = Real.expSum (-H) := rfl

omit [Nonempty α] in
lemma gibbs_pmf_eq_softmax (H : EnergySpace α) (σ : α) :
    gibbs_pmf (α := α) H σ = Real.softmax (-H) σ := rfl

omit [Nonempty α] in
lemma free_energy_density_eq_logSumExp (n : ℕ) (H : EnergySpace α) :
    free_energy_density (α := α) n H = (1 / (n : ℝ)) * Real.logSumExp (-H) := rfl

lemma Z_pos (H : EnergySpace α) : 0 < Z (α := α) H := Real.expSum_pos (-H)

lemma Z_ne_zero (H : EnergySpace α) : Z (α := α) H ≠ 0 := Real.expSum_ne_zero (-H)

lemma gibbs_pmf_pos (H : EnergySpace α) (σ : α) : 0 < gibbs_pmf (α := α) H σ :=
  Real.softmax_pos (-H) σ

lemma gibbs_pmf_nonneg (H : EnergySpace α) (σ : α) : 0 ≤ gibbs_pmf (α := α) H σ :=
  Real.softmax_nonneg (-H) σ

lemma gibbs_pmf_le_one (H : EnergySpace α) (σ : α) : gibbs_pmf (α := α) H σ ≤ 1 :=
  Real.softmax_le_one (-H) σ

lemma sum_gibbs_pmf (H : EnergySpace α) : (∑ σ, gibbs_pmf (α := α) H σ) = 1 :=
  Real.sum_softmax (-H)

/-! ## Fréchet calculus: derivatives and Hessian identities

Everything here is the log-sum-exp calculus of `Common.Mathlib.Analysis.SpecialFunctions.LogSumExp`
transported along the negation `H ↦ -H`, which is the continuous linear map `negCLM`. -/

/-- Evaluation at a configuration, as a continuous linear functional on `EnergySpace α`: it is
Mathlib's `PiLp.proj`, not a new object. -/
noncomputable abbrev evalCLM (σ : α) : EnergySpace α →L[ℝ] ℝ :=
  PiLp.proj (p := (2 : ENNReal)) (fun _ : α => ℝ) σ

/-- Negation of the Hamiltonian, as a continuous linear map. The Gibbs calculus is the
log-sum-exp calculus precomposed with it. -/
noncomputable def negCLM : EnergySpace α →L[ℝ] EnergySpace α :=
  -ContinuousLinearMap.id ℝ (EnergySpace α)

omit [Nonempty α] in
@[simp] lemma negCLM_apply (H : EnergySpace α) : negCLM (α := α) H = -H := rfl

lemma differentiable_logSumExp_neg :
    Differentiable ℝ (fun H : EnergySpace α => Real.logSumExp (-H)) :=
  ((Real.contDiff_logSumExp (ι := α)).differentiable (by simp)).comp
    (negCLM (α := α)).differentiable

lemma contDiff_two_logSumExp_neg :
    ContDiff ℝ 2 (fun H : EnergySpace α => Real.logSumExp (-H)) :=
  ((Real.contDiff_logSumExp (ι := α)).comp (negCLM (α := α)).contDiff).of_le (by simp)

/-- The directional derivative of the Gibbs weights: the softmax derivative, with the sign of the
negation. -/
lemma fderiv_gibbs_pmf_apply (H h : EnergySpace α) (σ : α) :
    fderiv ℝ (fun H : EnergySpace α => gibbs_pmf (α := α) H σ) H h =
      (gibbs_pmf (α := α) H σ) *
        ((∑ τ : α, (gibbs_pmf (α := α) H τ) * h τ) - h σ) := by
  have hd : Differentiable ℝ (fun y : EnergySpace α => Real.softmax y σ) :=
    (Real.contDiff_softmax (ι := α) σ).differentiable (by simp)
  have hchain : fderiv ℝ (fun H : EnergySpace α => Real.softmax (-H) σ) H
      = (fderiv ℝ (fun y : EnergySpace α => Real.softmax y σ) (-H)).comp (negCLM (α := α)) :=
    fderiv_comp_clm hd (negCLM (α := α)) H
  have : fderiv ℝ (fun H : EnergySpace α => gibbs_pmf (α := α) H σ) H h
      = fderiv ℝ (fun y : EnergySpace α => Real.softmax y σ) (-H) (-h) := by
    rw [show (fun H : EnergySpace α => gibbs_pmf (α := α) H σ)
        = fun H : EnergySpace α => Real.softmax (-H) σ from rfl, hchain]
    rfl
  rw [this, Real.fderiv_softmax_apply]
  have hneg : ∀ τ : α, (-h) τ = -(h τ) := fun _ => rfl
  simp only [hneg, gibbs_pmf_eq_softmax]
  rw [show (∑ τ : α, Real.softmax (-H) τ * -h τ)
      = -∑ τ : α, Real.softmax (-H) τ * h τ by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun τ _ => by ring]
  ring

lemma differentiableAt_gibbs_pmf (H : EnergySpace α) (σ : α) :
    DifferentiableAt ℝ (fun H : EnergySpace α => gibbs_pmf (α := α) H σ) H :=
  (((Real.contDiff_softmax (ι := α) σ).differentiable (by simp)).comp
    (negCLM (α := α)).differentiable).differentiableAt

lemma hasFDerivAt_gibbs_pmf (H : EnergySpace α) (σ : α) :
    HasFDerivAt (fun H : EnergySpace α => gibbs_pmf (α := α) H σ)
      (fderiv ℝ (fun H : EnergySpace α => gibbs_pmf (α := α) H σ) H) H :=
  (differentiableAt_gibbs_pmf (α := α) H σ).hasFDerivAt

omit [Nonempty α] in
lemma sum_gibbs_pmf_mul_std_basis (H : EnergySpace α) (τ : α) :
    (∑ ρ : α, (gibbs_pmf (α := α) H ρ) * (std_basis (α := α) τ ρ)) =
      gibbs_pmf (α := α) H τ := by
  classical
  simp [std_basis]

lemma fderiv_gibbs_pmf_apply_std_basis (H : EnergySpace α) (σ τ : α) :
    fderiv ℝ (fun H : EnergySpace α => gibbs_pmf (α := α) H σ) H (std_basis (α := α) τ)
      = (gibbs_pmf (α := α) H σ) *
          ((gibbs_pmf (α := α) H τ) - (std_basis (α := α) τ σ)) := by
  rw [fderiv_gibbs_pmf_apply, sum_gibbs_pmf_mul_std_basis]

/-- The second Fréchet derivative of the free-energy density, as a bilinear map. -/
noncomputable def hessian_free_energy_fderiv (n : ℕ) (H : EnergySpace α) :
    EnergySpace α →L[ℝ] EnergySpace α →L[ℝ] ℝ :=
  fderiv ℝ (fun H' => fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H) H') H

/-- The explicit Gibbs covariance bilinear form (Talagrand). -/
def hessian_free_energy (n : ℕ) (H : EnergySpace α) (h k : EnergySpace α) : ℝ :=
  (1 / (n : ℝ)) * (
    (∑ σ, gibbs_pmf (α := α) H σ * h σ * k σ) -
    (∑ σ, gibbs_pmf (α := α) H σ * h σ) * (∑ τ, gibbs_pmf (α := α) H τ * k τ)
  )

omit [Nonempty α] in
/-- The Gibbs covariance form is the `softmax` covariance form of the general theory, at `-H`. -/
lemma hessian_free_energy_eq_logSumExpHess (n : ℕ) (H h k : EnergySpace α) :
    hessian_free_energy (α := α) n H h k
      = (1 / (n : ℝ)) * Real.logSumExpHess (-H) h k := rfl

omit [Nonempty α] in
lemma hessian_free_energy_std_basis_eq (n : ℕ) (H : EnergySpace α) (σ τ : α) :
    hessian_free_energy (α := α) n H (std_basis (α := α) σ) (std_basis (α := α) τ)
      =
      (1 / (n : ℝ)) *
        ((gibbs_pmf (α := α) H σ) * (std_basis (α := α) τ σ) -
          (gibbs_pmf (α := α) H σ) * (gibbs_pmf (α := α) H τ)) := by
  classical
  refine congrArg (fun t : ℝ => (1 / (n : ℝ)) * t) ?_
  have hb : ∀ ρ : α, (∑ ν : α, gibbs_pmf (α := α) H ν * std_basis (α := α) ρ ν)
      = gibbs_pmf (α := α) H ρ := by
    intro ρ
    simp [std_basis]
  have hc : (∑ ν : α, gibbs_pmf (α := α) H ν
        * std_basis (α := α) σ ν * std_basis (α := α) τ ν)
      = gibbs_pmf (α := α) H σ * std_basis (α := α) τ σ := by
    simpa [mul_assoc, std_basis] using
      (Finset.sum_eq_single_of_mem (s := (Finset.univ : Finset α)) (a := σ)
        (f := fun ν : α => gibbs_pmf (α := α) H ν
          * (std_basis (α := α) σ ν * std_basis (α := α) τ ν))
        (by simp)
        (fun ν _hν hne => by
          have hne' : σ ≠ ν := Ne.symm hne
          simp [std_basis, hne']))
  rw [hc, hb σ, hb τ]

/-- Hessian `std_basis` entries equal `-(1/n)` times `fderiv gibbs_pmf` on `std_basis`. -/
lemma neg_one_div_n_mul_fderiv_gibbs_pmf_apply_std_basis_eq
    (n : ℕ) (H : EnergySpace α) (σ τ : α) :
    (-(1 / (n : ℝ))) *
        fderiv ℝ (fun H : EnergySpace α => gibbs_pmf (α := α) H σ) H (std_basis (α := α) τ)
      =
      hessian_free_energy (α := α) n H (std_basis (α := α) σ) (std_basis (α := α) τ) := by
  classical
  rw [fderiv_gibbs_pmf_apply_std_basis, hessian_free_energy_std_basis_eq]
  ring

/-- The gradient of the free-energy density: minus `1/n` times the Gibbs average. -/
lemma fderiv_free_energy_density_apply (n : ℕ) (H h : EnergySpace α) :
    fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H) H h =
      -(1 / (n : ℝ)) * ∑ σ : α, (gibbs_pmf (α := α) H σ) * h σ := by
  have hchain : fderiv ℝ (fun H : EnergySpace α => Real.logSumExp (-H)) H
      = (fderiv ℝ (fun y : EnergySpace α => Real.logSumExp y) (-H)).comp (negCLM (α := α)) :=
    fderiv_comp_clm ((Real.contDiff_logSumExp (ι := α)).differentiable (by simp))
      (negCLM (α := α)) H
  have hscal : fderiv ℝ (fun H : EnergySpace α => free_energy_density (α := α) n H) H
      = (1 / (n : ℝ)) • fderiv ℝ (fun H : EnergySpace α => Real.logSumExp (-H)) H := by
    rw [show (fun H : EnergySpace α => free_energy_density (α := α) n H)
        = fun H : EnergySpace α => (1 / (n : ℝ)) * Real.logSumExp (-H) from rfl]
    exact (((differentiable_logSumExp_neg (α := α)) H).hasFDerivAt.const_smul (1 / (n : ℝ))).fderiv
  rw [hscal, smul_apply, hchain]
  have happ : ((fderiv ℝ (fun y : EnergySpace α => Real.logSumExp y) (-H)).comp
      (negCLM (α := α))) h
      = ∑ σ : α, Real.softmax (-H) σ * (-h) σ := by
    rw [ContinuousLinearMap.coe_comp, Function.comp_apply, negCLM_apply,
      Real.fderiv_logSumExp_apply]
  rw [happ]
  have hneg : ∀ τ : α, (-h) τ = -(h τ) := fun _ => rfl
  simp only [hneg, ← gibbs_pmf_eq_softmax, smul_eq_mul]
  rw [show (∑ τ : α, gibbs_pmf (α := α) H τ * -h τ)
      = -∑ τ : α, gibbs_pmf (α := α) H τ * h τ by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun τ _ => by ring]
  ring

/-- **The Hessian of the free-energy density is the Gibbs covariance form.** This is the general
identity `Real.fderiv_fderiv_logSumExp_apply` transported along the negation, whose two sign
changes cancel. -/
lemma hessian_free_energy_fderiv_eq_hessian_free_energy (n : ℕ) (H h k : EnergySpace α) :
    (hessian_free_energy_fderiv (α := α) n H) h k = hessian_free_energy (α := α) n H h k := by
  have hfun : (fun H : EnergySpace α => free_energy_density (α := α) n H)
      = fun H : EnergySpace α => (1 / (n : ℝ)) * Real.logSumExp (-H) := rfl
  have hL : ((fderiv ℝ (fderiv ℝ (fun H : EnergySpace α =>
        (1 / (n : ℝ)) * Real.logSumExp (-H))) H) h) k
      = (1 / (n : ℝ)) * ((fderiv ℝ (fderiv ℝ
          (fun H : EnergySpace α => Real.logSumExp (-H))) H) h) k :=
    fderiv_fderiv_const_mul_apply (contDiff_two_logSumExp_neg (α := α)) (1 / (n : ℝ)) H h k
  have hR : ((fderiv ℝ (fderiv ℝ (fun H : EnergySpace α => Real.logSumExp (-H))) H) h) k
      = Real.logSumExpHess (-H) h k := by
    have hfe : (fun H : EnergySpace α => Real.logSumExp (-H))
        = fun H : EnergySpace α => Real.logSumExp (negCLM (α := α) H) := rfl
    rw [hfe, fderiv_fderiv_comp_clm_apply ((Real.contDiff_logSumExp (ι := α)).of_le (by simp))
      (negCLM (α := α)) H h k, Real.fderiv_fderiv_logSumExp_apply, negCLM_apply,
      show (negCLM (α := α)) h = (-1 : ℝ) • h by rw [negCLM_apply, neg_one_smul],
      show (negCLM (α := α)) k = (-1 : ℝ) • k by rw [negCLM_apply, neg_one_smul],
      Real.logSumExpHess_smul_smul]
    norm_num
  rw [hessian_free_energy_fderiv, hfun, hL, hR, hessian_free_energy_eq_logSumExpHess]


/-- Alias of `hessian_free_energy_fderiv`. -/
noncomputable abbrev hessian_logZ (n : ℕ) (H : EnergySpace α) :
    EnergySpace α →L[ℝ] EnergySpace α →L[ℝ] ℝ :=
  hessian_free_energy_fderiv (α := α) n H

/-- Alias of the Gibbs covariance bilinear form. -/
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
          -- (we do this by rewriting the summand, then using
          -- `sum_mul`/`sum_add_distrib`/`sum_sub_distrib`)
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
                  -- avoid `simp` cancellation of the common factor `(1/n)`; prove the inner sum
                  -- identity first
                  have hinner :
                      (∑ σ, ∑ τ, Cov σ τ * ((if σ = τ then g σ else 0) - g σ * g τ))
                        =
                      (∑ σ, ∑ τ, Cov σ τ * (if σ = τ then g σ else 0)) -
                        (∑ σ, ∑ τ, Cov σ τ * (g σ * g τ)) := by
                    -- distribute `*` over subtraction inside the finite sums
                    simp [mul_sub, Finset.sum_sub_distrib]
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
            simp [g, mul_comm]
          rw [hdiag', hprod']

end

end FiniteGibbs

end SpinGlass
