/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Data.Fin.Tuple.Basic

/-!
# `Fin.insertNth` as an update

`Fin.insertNth p x q` inserts `x` at position `p` of the tuple `q`. Changing the inserted value
is updating the `p`-th coordinate: `insertNth p x q = update (insertNth p x₀ q) p x` for any `x₀`.
This is the bridge between the product decomposition `MeasurableEquiv.piFinSuccAbove` (whose
inverse is `insertNth`) and statements phrased with `Function.update`.
-/

namespace Fin

variable {n : ℕ} {α : Type*}

/-- Inserting `x` at `p` is updating the `p`-th coordinate of any insertion at `p`. -/
theorem insertNth_eq_update (p : Fin (n + 1)) (x x₀ : α) (q : Fin n → α) :
    (insertNth p x q : Fin (n + 1) → α) = Function.update (insertNth p x₀ q) p x := by
  ext i
  refine p.succAboveCases ?_ ?_ i
  · simp
  · intro j
    rw [insertNth_apply_succAbove, Function.update_of_ne (succAbove_ne p j),
      insertNth_apply_succAbove]

end Fin
