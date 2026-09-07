/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Hadamard powers preserve positive semidefiniteness

Mathlib has the Schur product theorem `Matrix.PosSemidef.hadamard`: the entrywise product of two
positive semidefinite matrices is positive semidefinite. This file iterates it to the entrywise
(Hadamard) powers `A ∘ⁿ`, whose base case `n = 0` is the all-ones matrix, and records the two
auxiliary facts that the iteration needs: the all-ones matrix is positive semidefinite, and
positive semidefiniteness is preserved by scaling with a nonnegative real.

Hadamard powers are what turn a polynomial with nonnegative coefficients applied entrywise to a
positive semidefinite matrix into a positive semidefinite matrix — the classical criterion behind
mixed `p`-spin covariance kernels.

## Main statements

- `Matrix.posSemidef_ones_of`: the all-ones matrix is positive semidefinite.
- `Matrix.PosSemidef.smul_of_nonneg`: nonnegative scaling preserves positive semidefiniteness.
- `Matrix.hadamardPow`: the entrywise power.
- `Matrix.posSemidef_hadamardPow`: it preserves positive semidefiniteness.
-/

open BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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
