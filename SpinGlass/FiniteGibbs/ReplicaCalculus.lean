import SpinGlass.FiniteGibbs
import SpinGlass.FiniteGibbs.Calculus
import SpinGlass.FiniteGibbs.ReplicaMeasure
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Replica calculus for `SpinGlass.FiniteGibbs`

This file provides **model-agnostic** Fréchet-derivative formulas and uniform bounds for
deterministic objects built from sampling `n` independent replicas from a finite-volume Gibbs law.

The results are used as the finite-volume backend for Talagrand’s interpolation / smart-path
method (Vol. I, §1.4), where one differentiates Gibbs averages of functions of replicas and then
applies Gaussian integration by parts on the disorder.

## Main results

- `abs_gibbs_average_n_det_le_sum_abs`: a crude bound on the deterministic Gibbs average.
- `fderiv_prod_gibbs_pmf_apply`: derivative of the product Gibbs weight on `n` replicas.
- `norm_fderiv_prod_gibbs_pmf_le`: a uniform bound on the derivative of the product Gibbs weight.
- `fderiv_gibbs_average_n_det_apply`: derivative of the deterministic Gibbs average.
- `norm_fderiv_gibbs_pmf_le_two`: a uniform bound on the derivative of `gibbs_pmf`.
- `norm_fderiv_gibbs_average_n_det_le`: a uniform bound on the derivative of `gibbs_average_n_det`.
-/

open Real BigOperators

namespace SpinGlass
namespace FiniteGibbs

noncomputable section

variable {α : Type*} [Fintype α] [Nonempty α]

/-! ## Elementary bounds for Gibbs weights -/

lemma prod_gibbs_pmf_nonneg (n : ℕ) (H : EnergySpace α) (σs : ReplicaSpace (α := α) n) :
    0 ≤ ∏ l : Fin n, gibbs_pmf (α := α) H (σs l) := by
  classical
  refine Finset.prod_nonneg ?_
  intro l _hl
  exact gibbs_pmf_nonneg (α := α) (H := H) (σ := σs l)

lemma prod_gibbs_pmf_le_one (n : ℕ) (H : EnergySpace α) (σs : ReplicaSpace (α := α) n) :
    (∏ l : Fin n, gibbs_pmf (α := α) H (σs l)) ≤ (1 : ℝ) := by
  classical
  refine
    Finset.prod_le_one (s := (Finset.univ : Finset (Fin n)))
      (f := fun l => gibbs_pmf (α := α) H (σs l)) ?_ ?_
  · intro l _hl
    exact gibbs_pmf_nonneg (α := α) (H := H) (σ := σs l)
  · intro l _hl
    exact gibbs_pmf_le_one (α := α) (H := H) (σ := σs l)

/-! ## A crude bound on the deterministic Gibbs average -/

/-- The deterministic Gibbs average is bounded by the sum of absolute values of `f`. -/
lemma abs_gibbs_average_n_det_le_sum_abs (n : ℕ) (H : EnergySpace α) (f : ReplicaFun (α := α) n) :
    |gibbs_average_n_det (α := α) (n := n) H f| ≤ ∑ σs : ReplicaSpace (α := α) n, |f σs| := by
  classical
  have hprod_abs_le_one (σs : ReplicaSpace (α := α) n) :
      |∏ l : Fin n, gibbs_pmf (α := α) H (σs l)| ≤ (1 : ℝ) := by
    have hnonneg :
        0 ≤ ∏ l : Fin n, gibbs_pmf (α := α) H (σs l) :=
      prod_gibbs_pmf_nonneg (α := α) (n := n) (H := H) σs
    have hle1 :
        (∏ l : Fin n, gibbs_pmf (α := α) H (σs l)) ≤ (1 : ℝ) :=
      prod_gibbs_pmf_le_one (α := α) (n := n) (H := H) σs
    simpa [abs_of_nonneg hnonneg] using hle1
  calc
    |gibbs_average_n_det (α := α) (n := n) H f|
        = |∑ σs : ReplicaSpace (α := α) n,
            f σs * ∏ l : Fin n, gibbs_pmf (α := α) H (σs l)| := by
            rfl
    _ ≤ ∑ σs : ReplicaSpace (α := α) n,
          |f σs * ∏ l : Fin n, gibbs_pmf (α := α) H (σs l)| := by
          simpa using
            (Finset.abs_sum_le_sum_abs
              (f := fun σs : ReplicaSpace (α := α) n =>
                f σs * ∏ l : Fin n, gibbs_pmf (α := α) H (σs l))
              (s := (Finset.univ : Finset (ReplicaSpace (α := α) n))))
    _ = ∑ σs : ReplicaSpace (α := α) n,
          |f σs| * |∏ l : Fin n, gibbs_pmf (α := α) H (σs l)| := by
          refine Finset.sum_congr rfl (fun σs _hσs => ?_)
          simp [abs_mul]
    _ ≤ ∑ σs : ReplicaSpace (α := α) n, |f σs| := by
          refine Finset.sum_le_sum ?_
          intro σs _hσs
          have := mul_le_mul_of_nonneg_left (hprod_abs_le_one σs) (abs_nonneg (f σs))
          simpa using this

/-! ## Bounds for the derivative of `gibbs_pmf` -/

lemma abs_sum_gibbs_pmf_mul_apply_le_norm (H v : EnergySpace α) :
    |∑ τ : α, gibbs_pmf (α := α) H τ * v τ| ≤ ‖v‖ := by
  classical
  have hsum1 : (∑ τ : α, gibbs_pmf (α := α) H τ) = 1 :=
    sum_gibbs_pmf (α := α) (H := H)
  calc
    |∑ τ : α, gibbs_pmf (α := α) H τ * v τ|
        ≤ ∑ τ : α, |gibbs_pmf (α := α) H τ * v τ| := by
            simpa using
              (Finset.abs_sum_le_sum_abs
                (f := fun τ : α => gibbs_pmf (α := α) H τ * v τ)
                (s := (Finset.univ : Finset α)))
    _ = ∑ τ : α, gibbs_pmf (α := α) H τ * |v τ| := by
          refine Finset.sum_congr rfl (fun τ _hτ => ?_)
          have hp : 0 ≤ gibbs_pmf (α := α) H τ :=
            gibbs_pmf_nonneg (α := α) (H := H) (σ := τ)
          simp [abs_mul, abs_of_nonneg hp]
    _ ≤ ∑ τ : α, gibbs_pmf (α := α) H τ * ‖v‖ := by
          refine Finset.sum_le_sum (fun τ _hτ => ?_)
          have hp : 0 ≤ gibbs_pmf (α := α) H τ :=
            gibbs_pmf_nonneg (α := α) (H := H) (σ := τ)
          have hvτ : |v τ| ≤ ‖v‖ := by
            simpa [Real.norm_eq_abs] using abs_apply_le_norm (α := α) v τ
          exact mul_le_mul_of_nonneg_left hvτ hp
    _ = (∑ τ : α, gibbs_pmf (α := α) H τ) * ‖v‖ := by
          simpa using
            (Finset.sum_mul (s := (Finset.univ : Finset α))
              (f := fun τ : α => gibbs_pmf (α := α) H τ) (a := ‖v‖)).symm
    _ = ‖v‖ := by simp [hsum1]

lemma abs_sum_gibbs_pmf_mul_apply_sub_apply_le_two_norm (H v : EnergySpace α) (σ : α) :
    |(∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v σ| ≤ 2 * ‖v‖ := by
  have hE : |∑ τ : α, gibbs_pmf (α := α) H τ * v τ| ≤ ‖v‖ :=
    abs_sum_gibbs_pmf_mul_apply_le_norm (α := α) (H := H) v
  have hvσ : |v σ| ≤ ‖v‖ := by
    simpa [Real.norm_eq_abs] using abs_apply_le_norm (α := α) v σ
  have htri :
      |(∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v σ|
        ≤ |∑ τ : α, gibbs_pmf (α := α) H τ * v τ| + |v σ| := by
    simpa using (abs_sub _ _)
  calc
    |(∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v σ|
        ≤ |∑ τ : α, gibbs_pmf (α := α) H τ * v τ| + |v σ| := htri
    _ ≤ ‖v‖ + ‖v‖ := by gcongr
    _ = 2 * ‖v‖ := by ring

/-- Uniform bound on the Fréchet derivative of `H ↦ gibbs_pmf H σ`. -/
lemma norm_fderiv_gibbs_pmf_le_two (H : EnergySpace α) (σ : α) :
    ‖fderiv ℝ (fun H' : EnergySpace α => gibbs_pmf (α := α) H' σ) H‖ ≤ 2 := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  have hformula :
      fderiv ℝ (fun H' : EnergySpace α => gibbs_pmf (α := α) H' σ) H v =
        gibbs_pmf (α := α) H σ * ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v σ) := by
    simpa using (fderiv_gibbs_pmf_apply (α := α) (H := H) (h := v) σ)
  have hdiff :
      |(∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v σ| ≤ 2 * ‖v‖ :=
    abs_sum_gibbs_pmf_mul_apply_sub_apply_le_two_norm (α := α) (H := H) v σ
  have hp : 0 ≤ gibbs_pmf (α := α) H σ :=
    gibbs_pmf_nonneg (α := α) (H := H) (σ := σ)
  have hp1 : gibbs_pmf (α := α) H σ ≤ 1 :=
    gibbs_pmf_le_one (α := α) (H := H) (σ := σ)
  have hmain : |fderiv ℝ (fun H' : EnergySpace α => gibbs_pmf (α := α) H' σ) H v| ≤ 2 * ‖v‖ := by
    calc
      |fderiv ℝ (fun H' : EnergySpace α => gibbs_pmf (α := α) H' σ) H v|
          = |gibbs_pmf (α := α) H σ * ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v σ)| := by
              simp [hformula]
      _ = gibbs_pmf (α := α) H σ *
            |(∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v σ| := by
            simp [abs_mul, abs_of_nonneg hp]
      _ ≤ gibbs_pmf (α := α) H σ * (2 * ‖v‖) := by gcongr
      _ ≤ 1 * (2 * ‖v‖) := by gcongr
      _ = 2 * ‖v‖ := by ring
  simpa [Real.norm_eq_abs] using hmain

/-! ## Derivatives for products over replicas and deterministic Gibbs averages -/

/--
The derivative of the product Gibbs weight
`H ↦ ∏ l, gibbs_pmf H (σs l)` in direction `v`.
-/
lemma fderiv_prod_gibbs_pmf_apply (n : ℕ) (H v : EnergySpace α) (σs : ReplicaSpace (α := α) n) :
    fderiv ℝ (fun H' => ∏ l : Fin n, gibbs_pmf (α := α) H' (σs l)) H v =
      (∏ l : Fin n, gibbs_pmf (α := α) H (σs l)) *
        ∑ l : Fin n, ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l)) := by
  classical
  have hdiff :
      ∀ l : Fin n,
        DifferentiableAt ℝ (fun H' => gibbs_pmf (α := α) H' (σs l)) H := by
    intro l
    exact (hasFDerivAt_gibbs_pmf (α := α) (H := H) (σ := σs l)).differentiableAt
  have h_fderiv_prod :=
    fderiv_finset_prod
      (𝕜 := ℝ) (E := EnergySpace α) (𝔸' := ℝ) (u := (Finset.univ : Finset (Fin n)))
      (g := fun l H' => gibbs_pmf (α := α) H' (σs l))
      (fun l _hl => hdiff l)
  rw [h_fderiv_prod]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  have hterm :
      ∀ l : Fin n,
        (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l, gibbs_pmf (α := α) H (σs j)) *
            fderiv ℝ (fun H' => gibbs_pmf (α := α) H' (σs l)) H v
          =
          (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l, gibbs_pmf (α := α) H (σs j)) *
            (gibbs_pmf (α := α) H (σs l) *
              ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l))) := by
    intro l
    simp [fderiv_gibbs_pmf_apply]
  calc
    ∑ l ∈ (Finset.univ : Finset (Fin n)),
        (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l, gibbs_pmf (α := α) H (σs j)) *
          fderiv ℝ (fun H' => gibbs_pmf (α := α) H' (σs l)) H v
      =
      ∑ l ∈ (Finset.univ : Finset (Fin n)),
        (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l, gibbs_pmf (α := α) H (σs j)) *
          (gibbs_pmf (α := α) H (σs l) *
            ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l))) := by
        refine Finset.sum_congr rfl (fun l _hl => ?_)
        simpa using hterm l
    _ =
      ∑ l ∈ (Finset.univ : Finset (Fin n)),
        (∏ j : Fin n, gibbs_pmf (α := α) H (σs j)) *
          ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l)) := by
        refine Finset.sum_congr rfl (fun l _hl => ?_)
        have herase :
            (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l, gibbs_pmf (α := α) H (σs j)) *
                gibbs_pmf (α := α) H (σs l)
              =
              ∏ j : Fin n, gibbs_pmf (α := α) H (σs j) := by
          classical
          simpa using
            (Finset.prod_erase_mul (s := (Finset.univ : Finset (Fin n)))
              (f := fun j => gibbs_pmf (α := α) H (σs j)) (a := l) (Finset.mem_univ l))
        have :=
          congrArg (fun a => a * ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l))) herase
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
    _ =
      (∏ j : Fin n, gibbs_pmf (α := α) H (σs j)) *
        ∑ l : Fin n, ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l)) := by
        simpa using
          (Finset.mul_sum (s := (Finset.univ : Finset (Fin n)))
            (f := fun l => (∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l))
            (a := (∏ j : Fin n, gibbs_pmf (α := α) H (σs j)))).symm

/-- Uniform bound on the Fréchet derivative of the product Gibbs weight on `n` replicas. -/
lemma norm_fderiv_prod_gibbs_pmf_le (n : ℕ) (H : EnergySpace α) (σs : ReplicaSpace (α := α) n) :
    ‖fderiv ℝ (fun H' : EnergySpace α => ∏ l : Fin n, gibbs_pmf (α := α) H' (σs l)) H‖
      ≤ 2 * (n : ℝ) := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  have hformula :
      fderiv ℝ (fun H' : EnergySpace α => ∏ l : Fin n, gibbs_pmf (α := α) H' (σs l)) H v =
        (∏ l : Fin n, gibbs_pmf (α := α) H (σs l)) *
          ∑ l : Fin n, ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l)) := by
    simpa using fderiv_prod_gibbs_pmf_apply (α := α) (n := n) (H := H) (v := v) σs
  have hprod_abs_le_one :
      |∏ l : Fin n, gibbs_pmf (α := α) H (σs l)| ≤ (1 : ℝ) := by
    have hnonneg :
        0 ≤ ∏ l : Fin n, gibbs_pmf (α := α) H (σs l) :=
      prod_gibbs_pmf_nonneg (α := α) (n := n) (H := H) σs
    have hle1 :
        (∏ l : Fin n, gibbs_pmf (α := α) H (σs l)) ≤ (1 : ℝ) :=
      prod_gibbs_pmf_le_one (α := α) (n := n) (H := H) σs
    simpa [abs_of_nonneg hnonneg] using hle1
  have hsum_abs :
      |∑ l : Fin n, ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l))|
        ≤ 2 * (n : ℝ) * ‖v‖ := by
    have h₁ :
        |∑ l : Fin n, ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l))|
          ≤ ∑ l : Fin n, |(∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l)| := by
      simpa using
        (Finset.abs_sum_le_sum_abs
          (s := (Finset.univ : Finset (Fin n)))
          (f := fun l : Fin n => (∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l)))
    have h₂ :
        (∑ l : Fin n, |(∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l)|)
          ≤ (n : ℝ) * (2 * ‖v‖) := by
      -- Bound termwise, then evaluate the constant sum.
      have h' :
          (Finset.univ.sum fun l : Fin n =>
              |(∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l)|)
            ≤ Finset.univ.sum fun _l : Fin n => 2 * ‖v‖ := by
        classical
        refine Finset.sum_le_sum ?_
        intro l _hl
        simpa using
          (abs_sum_gibbs_pmf_mul_apply_sub_apply_le_two_norm
            (α := α) (H := H) (v := v) (σ := σs l))
      -- Rewrite back to `Fintype` sums and evaluate the constant sum.
      simpa using h'
    have h := le_trans h₁ h₂
    -- evaluate the constant sum on the right
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hmain : ‖fderiv ℝ (fun H' : EnergySpace α => ∏ l : Fin n, gibbs_pmf (α := α) H' (σs l)) H v‖
      ≤ (2 * (n : ℝ)) * ‖v‖ := by
    calc
      ‖fderiv ℝ (fun H' : EnergySpace α => ∏ l : Fin n, gibbs_pmf (α := α) H' (σs l)) H v‖
          = |fderiv ℝ (fun H' : EnergySpace α => ∏ l : Fin n, gibbs_pmf (α := α) H' (σs l)) H v| := by
              simp [Real.norm_eq_abs]
      _ = |(∏ l : Fin n, gibbs_pmf (α := α) H (σs l)) *
            ∑ l : Fin n, ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l))| := by
            simp [hformula]
      _ = |∏ l : Fin n, gibbs_pmf (α := α) H (σs l)| *
            |∑ l : Fin n, ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l))| := by
            simp [abs_mul]
      _ ≤ 1 * (2 * (n : ℝ) * ‖v‖) := by
            gcongr
      _ = (2 * (n : ℝ)) * ‖v‖ := by ring
  simpa [mul_assoc] using hmain

/-- Differentiability of the product Gibbs weight as a function of the Hamiltonian. -/
lemma differentiableAt_prod_gibbs_pmf (n : ℕ) (H : EnergySpace α) (σs : ReplicaSpace (α := α) n) :
    DifferentiableAt ℝ (fun H' => ∏ l : Fin n, gibbs_pmf (α := α) H' (σs l)) H := by
  classical
  have hg :
      ∀ l ∈ (Finset.univ : Finset (Fin n)),
        HasFDerivAt (fun H' => gibbs_pmf (α := α) H' (σs l))
          (fderiv ℝ (fun H' => gibbs_pmf (α := α) H' (σs l)) H) H := by
    intro l _hl
    exact (hasFDerivAt_gibbs_pmf (α := α) (H := H) (σ := σs l)).differentiableAt.hasFDerivAt
  have hHas :=
    (HasFDerivAt.finset_prod (u := (Finset.univ : Finset (Fin n)))
      (g := fun l H' => gibbs_pmf (α := α) H' (σs l))
      (g' := fun l => fderiv ℝ (fun H' => gibbs_pmf (α := α) H' (σs l)) H)
      (x := H) hg).differentiableAt
  simpa using hHas

/-- Directional derivative of `gibbs_average_n_det` with respect to the Hamiltonian. -/
lemma fderiv_gibbs_average_n_det_apply (n : ℕ) (H v : EnergySpace α) (f : ReplicaFun (α := α) n) :
    fderiv ℝ (fun H' => gibbs_average_n_det (α := α) (n := n) H' f) H v =
      ∑ σs : ReplicaSpace (α := α) n,
        f σs * (∏ l : Fin n, gibbs_pmf (α := α) H (σs l)) *
          ∑ l : Fin n, ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l)) := by
  classical
  let u : Finset (ReplicaSpace (α := α) n) := Finset.univ
  let A : ReplicaSpace (α := α) n → EnergySpace α → ℝ :=
    fun σs H' => f σs * ∏ l : Fin n, gibbs_pmf (α := α) H' (σs l)
  have hA_diff : ∀ σs ∈ u, DifferentiableAt ℝ (A σs) H := by
    intro σs _hσs
    have hprod :
        DifferentiableAt ℝ (fun H' => ∏ l : Fin n, gibbs_pmf (α := α) H' (σs l)) H :=
      differentiableAt_prod_gibbs_pmf (α := α) (n := n) (H := H) σs
    simpa [A] using (DifferentiableAt.const_mul hprod (f σs))
  have hfderiv_sum :
      fderiv ℝ (fun H' : EnergySpace α => ∑ σs ∈ u, A σs H') H = ∑ σs ∈ u, fderiv ℝ (A σs) H := by
    simpa using (fderiv_fun_sum (u := u) (A := A) (x := H) hA_diff)
  have hrewrite :
      (fun H' : EnergySpace α => gibbs_average_n_det (α := α) (n := n) H' f) =
        fun H' : EnergySpace α => ∑ σs ∈ u, A σs H' := by
    funext H'
    simp [gibbs_average_n_det, u, A]
  rw [hrewrite]
  have : fderiv ℝ (fun H' : EnergySpace α => ∑ σs ∈ u, A σs H') H v =
      (∑ σs ∈ u, fderiv ℝ (A σs) H) v := by
    simp [hfderiv_sum]
  simp [this, u, A, fderiv_const_mul, differentiableAt_prod_gibbs_pmf,
    fderiv_prod_gibbs_pmf_apply, mul_assoc, mul_left_comm, mul_comm, mul_add, sub_eq_add_neg,
    Finset.mul_sum]

/-- Differentiability of `H ↦ gibbs_average_n_det H f`. -/
lemma differentiableAt_gibbs_average_n_det (n : ℕ) (H : EnergySpace α) (f : ReplicaFun (α := α) n) :
    DifferentiableAt ℝ (fun H' => gibbs_average_n_det (α := α) (n := n) H' f) H := by
  classical
  have hterm :
      ∀ σs : ReplicaSpace (α := α) n,
        DifferentiableAt ℝ (fun H' => f σs * ∏ l : Fin n, gibbs_pmf (α := α) H' (σs l)) H := by
    intro σs
    have hprod :
        DifferentiableAt ℝ (fun H' => ∏ l : Fin n, gibbs_pmf (α := α) H' (σs l)) H :=
      differentiableAt_prod_gibbs_pmf (α := α) (n := n) (H := H) σs
    simpa using (DifferentiableAt.const_mul hprod (f σs))
  have hsum :
      DifferentiableAt ℝ
        (fun H' =>
          ∑ σs ∈ (Finset.univ : Finset (ReplicaSpace (α := α) n)),
            f σs * ∏ l : Fin n, gibbs_pmf (α := α) H' (σs l)) H := by
    refine
      (DifferentiableAt.fun_sum (𝕜 := ℝ) (E := EnergySpace α) (F := ℝ)
        (u := (Finset.univ : Finset (ReplicaSpace (α := α) n)))
        (A := fun σs : ReplicaSpace (α := α) n => fun H' : EnergySpace α =>
          f σs * ∏ l : Fin n, gibbs_pmf (α := α) H' (σs l))
        (x := H) ?_)
    intro σs _hσs
    simpa using hterm σs
  simpa [gibbs_average_n_det] using hsum

/-- Uniform bound on the derivative of `gibbs_average_n_det` (operator norm). -/
lemma norm_fderiv_gibbs_average_n_det_le (n : ℕ) (H : EnergySpace α) (f : ReplicaFun (α := α) n) :
    ‖fderiv ℝ (fun H' => gibbs_average_n_det (α := α) (n := n) H' f) H‖
      ≤ (2 * (n : ℝ)) * (∑ σs : ReplicaSpace (α := α) n, ‖f σs‖) := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ (fun v => ?_)
  · have : 0 ≤ (2 : ℝ) * (n : ℝ) := by positivity
    exact mul_nonneg this (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  · have hv_formula :
        fderiv ℝ (fun H' => gibbs_average_n_det (α := α) (n := n) H' f) H v =
          ∑ σs : ReplicaSpace (α := α) n,
            f σs * (∏ l : Fin n, gibbs_pmf (α := α) H (σs l)) *
              ∑ l : Fin n, ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l)) := by
      simpa using fderiv_gibbs_average_n_det_apply (α := α) (n := n) (H := H) (v := v) f
    have hprod_abs_le_one (σs : ReplicaSpace (α := α) n) :
        |∏ l : Fin n, gibbs_pmf (α := α) H (σs l)| ≤ (1 : ℝ) := by
      have hnonneg :
          0 ≤ ∏ l : Fin n, gibbs_pmf (α := α) H (σs l) :=
        prod_gibbs_pmf_nonneg (α := α) (n := n) (H := H) σs
      have hle1 :
          (∏ l : Fin n, gibbs_pmf (α := α) H (σs l)) ≤ (1 : ℝ) :=
        prod_gibbs_pmf_le_one (α := α) (n := n) (H := H) σs
      simpa [abs_of_nonneg hnonneg] using hle1
    have hsum_abs (σs : ReplicaSpace (α := α) n) :
        |∑ l : Fin n, ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l))|
          ≤ (2 * (n : ℝ)) * ‖v‖ := by
      classical
      have hdiff_le : ∀ l : Fin n,
          |(∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l)| ≤ 2 * ‖v‖ := by
        intro l
        simpa using
          abs_sum_gibbs_pmf_mul_apply_sub_apply_le_two_norm (α := α) (H := H) v (σs l)
      calc
        |∑ l : Fin n, ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l))|
            ≤ ∑ l : Fin n, |(∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l)| := by
                simpa using
                  (Finset.abs_sum_le_sum_abs
                    (f := fun l : Fin n =>
                      (∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l))
                    (s := (Finset.univ : Finset (Fin n))))
        _ ≤ ∑ l : Fin n, (2 * ‖v‖) := by
              refine Finset.sum_le_sum (fun l _hl => ?_)
              exact hdiff_le l
        _ = (2 * ‖v‖) * (n : ℝ) := by
              simp [Finset.card_univ, mul_comm]
        _ = (2 * (n : ℝ)) * ‖v‖ := by ring
    rw [hv_formula]
    -- Reduce the operator norm bound to a pointwise absolute-value estimate.
    have hmain :
        |∑ σs : ReplicaSpace (α := α) n,
            f σs * (∏ l : Fin n, gibbs_pmf (α := α) H (σs l)) *
              ∑ l : Fin n, ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l))|
          ≤ ((2 * (n : ℝ)) * (∑ σs : ReplicaSpace (α := α) n, ‖f σs‖)) * ‖v‖ := by
      classical
      calc
        |∑ σs : ReplicaSpace (α := α) n,
            f σs * (∏ l : Fin n, gibbs_pmf (α := α) H (σs l)) *
              ∑ l : Fin n, ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l))|
            ≤ ∑ σs : ReplicaSpace (α := α) n,
                |f σs * (∏ l : Fin n, gibbs_pmf (α := α) H (σs l)) *
                  ∑ l : Fin n, ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l))| := by
                simpa using
                  (Finset.abs_sum_le_sum_abs
                    (f := fun σs : ReplicaSpace (α := α) n =>
                      f σs * (∏ l : Fin n, gibbs_pmf (α := α) H (σs l)) *
                        ∑ l : Fin n, ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l)))
                    (s := (Finset.univ : Finset (ReplicaSpace (α := α) n))))
        _ = ∑ σs : ReplicaSpace (α := α) n,
              (‖f σs‖ * |∏ l : Fin n, gibbs_pmf (α := α) H (σs l)| *
                |∑ l : Fin n, ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l))|) := by
              refine Finset.sum_congr rfl (fun σs _hσs => ?_)
              simp [abs_mul, Real.norm_eq_abs, mul_assoc]
        _ ≤ ∑ σs : ReplicaSpace (α := α) n,
              (‖f σs‖ * (1 : ℝ) * ((2 * (n : ℝ)) * ‖v‖)) := by
              refine Finset.sum_le_sum (fun σs _hσs => ?_)
              have h1 : |∏ l : Fin n, gibbs_pmf (α := α) H (σs l)| ≤ (1 : ℝ) :=
                hprod_abs_le_one σs
              have h2 :
                  |∑ l : Fin n, ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l))|
                    ≤ (2 * (n : ℝ)) * ‖v‖ :=
                hsum_abs σs
              have h0 : 0 ≤ ‖f σs‖ := norm_nonneg _
              have hsum_nonneg :
                  0 ≤
                    |∑ l : Fin n, ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l))| :=
                abs_nonneg _
              have hfp :
                  ‖f σs‖ * |∏ l : Fin n, gibbs_pmf (α := α) H (σs l)| ≤ ‖f σs‖ * (1 : ℝ) :=
                mul_le_mul_of_nonneg_left h1 h0
              have hmul1 :
                  ‖f σs‖ * |∏ l : Fin n, gibbs_pmf (α := α) H (σs l)| *
                      |∑ l : Fin n, ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l))|
                    ≤ ‖f σs‖ * (1 : ℝ) *
                        |∑ l : Fin n, ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l))| := by
                -- multiply `hfp` by a nonnegative factor
                simpa [mul_assoc] using mul_le_mul_of_nonneg_right hfp hsum_nonneg
              have hmul2 :
                  ‖f σs‖ * (1 : ℝ) *
                      |∑ l : Fin n, ((∑ τ : α, gibbs_pmf (α := α) H τ * v τ) - v (σs l))|
                    ≤ ‖f σs‖ * (1 : ℝ) * ((2 * (n : ℝ)) * ‖v‖) := by
                have hf1 : 0 ≤ ‖f σs‖ * (1 : ℝ) := by simp
                exact mul_le_mul_of_nonneg_left h2 hf1
              exact le_trans hmul1 hmul2
        _ = ((2 * (n : ℝ)) * ‖v‖) * (∑ σs : ReplicaSpace (α := α) n, ‖f σs‖) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun σs _hσs => ?_)
              ring
        _ = ((2 * (n : ℝ)) * (∑ σs : ReplicaSpace (α := α) n, ‖f σs‖)) * ‖v‖ := by
              ring
    simpa [Real.norm_eq_abs] using hmain

end

end FiniteGibbs
end SpinGlass

