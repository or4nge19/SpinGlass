import SpinGlass.Papers.Triviality4D.RandomCurrentRepresentation
import Mathlib.Data.Nat.Choose.Basic

/-!
# Random current switching lemma (finite volume)

This file formalizes the **switching lemma** from `4D_triviality_June_2021_final.tex`, Lemma 1.5
("Definition and switching lemma" subsection).

We work in finite volume `Λ` with currents `n : Edge Λ → ℕ` and the real-valued current weights
`weightReal` introduced in `RandomCurrentRepresentation.lean`.
-/

open scoped BigOperators

namespace SpinGlass.Papers.Triviality4D

namespace RandomCurrent

universe u

variable {V : Type u} [DecidableEq V]
variable {Λ : Finset V}

/-! ## The event `ℱ_B`: existence of a subcurrent with sources `B` -/

/-- `HasSubCurrent n B` means: there exists a subcurrent `m ≤ n` with `sources m = B`. -/
def HasSubCurrent (n : Current (V := V) Λ) (B : Finset (↥Λ)) : Prop :=
  ∃ m : Current (V := V) Λ, CurrentLE (V := V) m n ∧ sources (V := V) m = B

/-! ## A finite type of edge-copy assignments for a fixed total current -/

/--
For a fixed total current `n`, an **assignment** chooses, for each edge `e`, a subset of the
`n e` edge-copies that will be attributed to the *first* current in a splitting `n = n₁ + n₂`.

We represent edge-copies of `e` by `Fin (n e)`.
-/
abbrev EdgeAssign (n : Current (V := V) Λ) : Type u :=
  ∀ e : Edge (V := V) Λ, Finset (Fin (n e))

noncomputable def currentOfEdgeAssign (n : Current (V := V) Λ) (S : EdgeAssign (V := V) (Λ := Λ) n) :
    Current (V := V) Λ :=
  fun e => (S e).card

noncomputable def currentOfEdgeAssignCompl (n : Current (V := V) Λ) (S : EdgeAssign (V := V) (Λ := Λ) n) :
    Current (V := V) Λ :=
  fun e => n e - (S e).card

lemma currentOfEdgeAssign_add_currentOfEdgeAssignCompl (n : Current (V := V) Λ)
    (S : EdgeAssign (V := V) (Λ := Λ) n) :
    currentOfEdgeAssign (V := V) (Λ := Λ) n S + currentOfEdgeAssignCompl (V := V) (Λ := Λ) n S = n := by
  funext e
  have hle : (S e).card ≤ n e := by
    simpa using (Finset.card_le_univ (s := S e))
  simpa [currentOfEdgeAssign, currentOfEdgeAssignCompl, Nat.add_sub_of_le hle]

end RandomCurrent

end SpinGlass.Papers.Triviality4D

