/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Subadditive

/-!
# Fekete's lemma, superadditive form

Mathlib's `Subadditive` records `u (m + n) ≤ u m + u n` and Fekete's lemma in the form
`u n / n → sInf (range (u · / ·))`. Statistical mechanics uses the mirror statement: a
*super*additive sequence has `u n / n → sSup (range (u · / ·))`. That is the shape of the
thermodynamic limit — `N ↦ N p_N` is superadditive by Guerra–Toninelli interpolation, and the free
energy per site converges to its supremum.

This file records the superadditive form, obtained from the subadditive one by negation.

## Main statements

- `Superadditive`: the definition.
- `Superadditive.tendsto_lim`: Fekete's lemma.
- `Superadditive.div_le_lim`: every term is below the limit.
-/

open Filter Set

/-- A real sequence is superadditive if `u m + u n ≤ u (m + n)`. -/
def Superadditive (u : ℕ → ℝ) : Prop :=
  ∀ m n, u m + u n ≤ u (m + n)

namespace Superadditive

variable {u : ℕ → ℝ}

/-- Negating a superadditive sequence gives a subadditive one. -/
theorem subadditive_neg (h : Superadditive u) : Subadditive (fun n => -u n) := by
  intro m n
  have := h m n
  simp only []
  linarith

/-- The limit of `u n / n` for a superadditive sequence: the supremum of the sequence of averages,
defined as minus the infimum for the negated sequence. -/
noncomputable def lim (h : Superadditive u) : ℝ := -(h.subadditive_neg).lim

private lemma bddBelow_neg_of_bddAbove (hbdd : BddAbove (range fun n : ℕ => u n / n)) :
    BddBelow (range fun n : ℕ => (fun m : ℕ => -u m) n / n) := by
  obtain ⟨C, hC⟩ := hbdd
  refine ⟨-C, ?_⟩
  rintro y ⟨n, rfl⟩
  have : u n / n ≤ C := hC ⟨n, rfl⟩
  simp only [neg_div]
  linarith

/-- **Fekete's lemma, superadditive form**: if `u` is superadditive and the averages `u n / n` are
bounded above, then they converge to `Superadditive.lim`. -/
theorem tendsto_lim (h : Superadditive u) (hbdd : BddAbove (range fun n : ℕ => u n / n)) :
    Tendsto (fun n : ℕ => u n / n) atTop (nhds h.lim) := by
  have hsub := (h.subadditive_neg).tendsto_lim (bddBelow_neg_of_bddAbove hbdd)
  have hneg : Tendsto (fun n : ℕ => -((fun m : ℕ => -u m) n / n)) atTop
      (nhds (-(h.subadditive_neg).lim)) := hsub.neg
  refine hneg.congr fun n => ?_
  simp [neg_div]

/-- Every average is below the limit: `Superadditive.lim` is the supremum. -/
theorem div_le_lim (h : Superadditive u) (hbdd : BddAbove (range fun n : ℕ => u n / n))
    {n : ℕ} (hn : n ≠ 0) : u n / n ≤ h.lim := by
  have hle := (h.subadditive_neg).lim_le_div (bddBelow_neg_of_bddAbove hbdd) hn
  have : (h.subadditive_neg).lim ≤ -(u n / n) := by
    simpa [neg_div] using hle
  simp only [lim]
  linarith

end Superadditive
