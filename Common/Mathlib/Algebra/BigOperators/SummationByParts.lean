/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Summation by parts in telescoped form

The discrete Leibniz rule `Δ(fg) = f(·+1) Δg + (Δf) g` sums to

`∑_{i < n} (f (i+1) * (g (i+1) - g i) + (f (i+1) - f i) * g i) = f n * g n - f 0 * g 0`

(`Finset.sum_range_mul_sub_add_sub_mul`), valid in any ring: the two halves of the product rule
are arranged so that no commutativity is needed. This is the telescoped form of summation by
parts; Mathlib's `Finset.sum_range_by_parts` is the form in which one of the two sums has been
replaced by the partial sums of `g`.
-/

namespace Finset

variable {R : Type*} [Ring R]

/-- **Summation by parts, telescoped**: the discrete Leibniz rule summed over `range n`. -/
theorem sum_range_mul_sub_add_sub_mul (f g : ℕ → R) (n : ℕ) :
    ∑ i ∈ range n, (f (i + 1) * (g (i + 1) - g i) + (f (i + 1) - f i) * g i)
      = f n * g n - f 0 * g 0 := by
  have h : ∀ i : ℕ, f (i + 1) * (g (i + 1) - g i) + (f (i + 1) - f i) * g i
      = (fun j => f j * g j) (i + 1) - (fun j => f j * g j) i := by
    intro i
    simp only
    rw [mul_sub, sub_mul]
    exact sub_add_sub_cancel _ _ _
  simp_rw [h]
  exact sum_range_sub (fun j => f j * g j) n

/-- The commutative form, with the second half written as `g i * (f (i+1) - f i)`. -/
theorem sum_range_mul_sub_add_mul_sub {R : Type*} [CommRing R] (f g : ℕ → R) (n : ℕ) :
    ∑ i ∈ range n, (f (i + 1) * (g (i + 1) - g i) + g i * (f (i + 1) - f i))
      = f n * g n - f 0 * g 0 := by
  simpa [mul_comm] using sum_range_mul_sub_add_sub_mul f g n

end Finset
