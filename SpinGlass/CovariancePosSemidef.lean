import SpinGlass.Defs
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Realizability of overlap-driven covariance kernels

A symmetric kernel is the covariance of a centered Gaussian family exactly when it is positive
semidefinite. This file proves that criterion for Talagrand's mixed `p`-spin kernels
`N · ξ(R_{σ,τ})`: if `ξ` is a polynomial with nonnegative coefficients — Talagrand's condition
`ξ(x) = ∑ₚ βₚ² xᵖ` (Vol. II, Eq. (14.57)) — then the kernel is positive semidefinite.

The proof is the Schur product theorem applied to the overlap Gram matrix: `R` is `1/N` times a
Gram matrix, hence positive semidefinite, and Hadamard powers of positive semidefinite matrices
are positive semidefinite.

## Main statements

- `Matrix.posSemidef_hadamardPow`: Hadamard powers preserve positive semidefiniteness.
- `posSemidef_overlapMatrix`: the overlap matrix `R_{σ,τ}` is positive semidefinite.
- `posSemidef_overlapPolyMatrix`: **the mixed `p`-spin criterion** — `N · ∑ₚ aₚ Rᵖ` is positive
  semidefinite whenever every `aₚ ≥ 0`.
- `posSemidef_skCovMatrix`, `posSemidef_refCovMatrix`: the SK and replica-symmetric kernels of
  Vol. I, §1.3 are positive semidefinite (the latter for `0 ≤ q`).
-/

open BigOperators Matrix

namespace Matrix

variable {ι : Type*}

/-- The all-ones matrix is positive semidefinite: it is the Gram matrix of the all-ones vector. -/
lemma posSemidef_ones_of : (Matrix.of fun _ _ : ι => (1 : ℝ)).PosSemidef := by
  refine ⟨?_, fun x => ?_⟩
  · ext i j; simp
  · have hkey : (x.sum fun i xi =>
          x.sum fun j xj => star xi * (Matrix.of fun _ _ : ι => (1 : ℝ)) i j * xj)
        = (∑ i ∈ x.support, x i) * ∑ j ∈ x.support, x j := by
      simp only [Matrix.of_apply, star_trivial, mul_one, Finsupp.sum]
      exact (Finset.sum_mul_sum _ _ _ _).symm
    rw [hkey]
    exact mul_self_nonneg _

/-- A nonnegative scalar multiple of a positive semidefinite matrix is positive semidefinite. -/
protected lemma PosSemidef.smul_of_nonneg {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    {c : ℝ} (hc : 0 ≤ c) : (c • A).PosSemidef := by
  refine ⟨hA.1.smul (IsSelfAdjoint.all c), fun x => ?_⟩
  have hkey : (x.sum fun i xi => x.sum fun j xj => star xi * (c • A) i j * xj)
      = c * x.sum fun i xi => x.sum fun j xj => star xi * A i j * xj := by
    simp only [Matrix.smul_apply, smul_eq_mul, Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hkey]
  exact mul_nonneg hc (hA.2 x)

/-- Entrywise (Hadamard) power of a matrix: `hadamardPow A p` has entries `(A i j) ^ p`. -/
def hadamardPow (A : Matrix ι ι ℝ) : ℕ → Matrix ι ι ℝ
  | 0 => Matrix.of fun _ _ => 1
  | p + 1 => A ⊙ hadamardPow A p

@[simp] lemma hadamardPow_zero (A : Matrix ι ι ℝ) :
    hadamardPow A 0 = Matrix.of fun _ _ => 1 := rfl

@[simp] lemma hadamardPow_succ (A : Matrix ι ι ℝ) (p : ℕ) :
    hadamardPow A (p + 1) = A ⊙ hadamardPow A p := rfl

/-- `hadamardPow A p` has entries the `p`-th powers of the entries of `A`. -/
@[simp] lemma hadamardPow_apply (A : Matrix ι ι ℝ) (p : ℕ) (i j : ι) :
    hadamardPow A p i j = (A i j) ^ p := by
  induction p with
  | zero => simp
  | succ p ih => simp [Matrix.hadamard_apply, ih, pow_succ, mul_comm]

/-- **Hadamard powers preserve positive semidefiniteness** (iterated Schur product theorem). -/
lemma posSemidef_hadamardPow [Finite ι] {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (p : ℕ) : (hadamardPow A p).PosSemidef := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  induction p with
  | zero => simpa using posSemidef_ones_of (ι := ι)
  | succ p ih => exact hA.hadamard ih

end Matrix

namespace SpinGlass

variable {N : ℕ}

/-- The matrix of Ising spins, `spinMatrix N σ i = σᵢ ∈ {±1}`. -/
def spinMatrix (N : ℕ) : Matrix (Config N) (Fin N) ℝ :=
  Matrix.of fun σ i => spin N σ i

/-- The overlap matrix `R_{σ,τ}`. -/
noncomputable def overlapMatrix (N : ℕ) : Matrix (Config N) (Config N) ℝ :=
  Matrix.of fun σ τ => overlap N σ τ

/-- The overlap matrix is `1/N` times the Gram matrix of the spin vectors. -/
lemma overlapMatrix_eq_smul_gram (N : ℕ) :
    overlapMatrix N = (1 / (N : ℝ)) • (spinMatrix N * (spinMatrix N)ᴴ) := by
  ext σ τ
  simp [overlapMatrix, spinMatrix, overlap, overlapOf, Matrix.mul_apply, spinOf, spin,
    Finset.mul_sum]

/-- **The overlap matrix is positive semidefinite.** -/
lemma posSemidef_overlapMatrix (N : ℕ) : (overlapMatrix N).PosSemidef := by
  rw [overlapMatrix_eq_smul_gram]
  exact (Matrix.posSemidef_self_mul_conjTranspose (spinMatrix N)).smul_of_nonneg
    (by positivity)

/-- **Talagrand's realizability criterion for mixed `p`-spin covariances.** If every coefficient
`a p` is nonnegative, the overlap-driven kernel `N · ∑ₚ a p · Rᵖ` is positive semidefinite, hence
is the covariance kernel of a centered Gaussian Hamiltonian. Talagrand Vol. II, Eq. (14.57). -/
lemma posSemidef_overlapPolyMatrix (N : ℕ) (a : ℕ → ℝ) (ha : ∀ p, 0 ≤ a p) (s : Finset ℕ) :
    (Matrix.of fun σ τ : Config N =>
      (N : ℝ) * ∑ p ∈ s, a p * (overlap N σ τ) ^ p).PosSemidef := by
  classical
  have hsum : (Matrix.of fun σ τ : Config N => (N : ℝ) * ∑ p ∈ s, a p * (overlap N σ τ) ^ p)
      = (N : ℝ) • ∑ p ∈ s, a p • Matrix.hadamardPow (overlapMatrix N) p := by
    ext σ τ
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.sum_apply,
      Matrix.hadamardPow_apply, overlapMatrix, Finset.mul_sum, smul_eq_mul]
  rw [hsum]
  refine Matrix.PosSemidef.smul_of_nonneg ?_ (by positivity)
  refine Matrix.posSemidef_sum s (fun p _ => ?_)
  exact (Matrix.posSemidef_hadamardPow (posSemidef_overlapMatrix N) p).smul_of_nonneg (ha p)

/-- The SK covariance kernel is positive semidefinite: it is `N · (β²/2) R²`. -/
lemma posSemidef_skCovMatrix (N : ℕ) (β : ℝ) :
    (Matrix.of fun σ τ : Config N => sk_cov_kernel N β σ τ).PosSemidef := by
  classical
  have hEq : (Matrix.of fun σ τ : Config N => sk_cov_kernel N β σ τ)
      = Matrix.of fun σ τ : Config N =>
          (N : ℝ) * ∑ p ∈ ({2} : Finset ℕ),
            (if p = 2 then β ^ 2 / 2 else 0) * (overlap N σ τ) ^ p := by
    ext σ τ
    simp [sk_cov_kernel_eq]
    ring
  rw [hEq]
  exact posSemidef_overlapPolyMatrix N
    (fun p => if p = 2 then β ^ 2 / 2 else 0) (fun p => by positivity) {2}

/-- Guerra's replica-symmetric reference kernel is positive semidefinite for `0 ≤ q`:
it is `N · (β² q) R`. -/
lemma posSemidef_refCovMatrix (N : ℕ) (β q : ℝ) (hq : 0 ≤ q) :
    (Matrix.of fun σ τ : Config N =>
      simple_cov_kernel N β (fun r => q * r) σ τ).PosSemidef := by
  classical
  have hEq : (Matrix.of fun σ τ : Config N =>
        simple_cov_kernel N β (fun r => q * r) σ τ)
      = Matrix.of fun σ τ : Config N =>
          (N : ℝ) * ∑ p ∈ ({1} : Finset ℕ),
            (if p = 1 then β ^ 2 * q else 0) * (overlap N σ τ) ^ p := by
    ext σ τ
    simp [simple_cov_kernel_eq]
    ring
  rw [hEq]
  exact posSemidef_overlapPolyMatrix N
    (fun p => if p = 1 then β ^ 2 * q else 0) (fun p => by positivity) {1}

end SpinGlass
