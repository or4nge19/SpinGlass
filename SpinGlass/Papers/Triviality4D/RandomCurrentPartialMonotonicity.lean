import SpinGlass.Papers.Triviality4D.RandomCurrentConsequences

/-!
# Partial monotonicity tools for random currents (finite volume)

This file develops basic infrastructure for the paper's Appendix Lemma `lem:a`:
we introduce a **cut coupling** which deletes (sets to zero) the couplings across a vertex set.

The key point is that, for a current that carries **no** flow across the cut, the random-current
weight `weightReal` is unchanged when we replace `J` by the cut coupling.
-/

open scoped BigOperators

namespace SpinGlass.Papers.Triviality4D

namespace RandomCurrent

universe u

variable {V : Type u} [DecidableEq V]
variable {Λ : Finset V}

/-! ## Cut couplings across a vertex set -/

/-- An edge crosses a vertex cut `S` if its endpoints lie on opposite sides. -/
def EdgeCross (S : Finset (↥Λ)) (e : Edge (V := V) Λ) : Prop :=
  (e.1.out.1 ∈ S ∧ e.1.out.2 ∉ S) ∨ (e.1.out.1 ∉ S ∧ e.1.out.2 ∈ S)

instance (S : Finset (↥Λ)) (e : Edge (V := V) Λ) :
    Decidable (EdgeCross (V := V) (Λ := Λ) S e) := by
  dsimp [EdgeCross]
  infer_instance

lemma EdgeCross.symm (S : Finset (↥Λ)) (e : Edge (V := V) Λ) :
    EdgeCross (V := V) (Λ := Λ) S e ↔
      ((e.1.out.2 ∈ S ∧ e.1.out.1 ∉ S) ∨ (e.1.out.2 ∉ S ∧ e.1.out.1 ∈ S)) := by
  constructor <;> intro h <;> rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [EdgeCross, h1, h2]

/--
The coupling obtained from `J` by deleting all couplings across the cut `S`.

Equivalently, we set `J e = 0` for every edge `e` that crosses `S`.
-/
noncomputable def cutCoupling (J : Edge (V := V) Λ → ℝ) (S : Finset (↥Λ)) : Edge (V := V) Λ → ℝ :=
  fun e => if EdgeCross (V := V) (Λ := Λ) S e then 0 else J e

@[simp] lemma cutCoupling_of_cross
    (J : Edge (V := V) Λ → ℝ) (S : Finset (↥Λ)) {e : Edge (V := V) Λ}
    (he : EdgeCross (V := V) (Λ := Λ) S e) :
    cutCoupling (V := V) (Λ := Λ) J S e = 0 := by
  simp [cutCoupling, he]

@[simp] lemma cutCoupling_of_not_cross
    (J : Edge (V := V) Λ → ℝ) (S : Finset (↥Λ)) {e : Edge (V := V) Λ}
    (he : ¬ EdgeCross (V := V) (Λ := Λ) S e) :
    cutCoupling (V := V) (Λ := Λ) J S e = J e := by
  simp [cutCoupling, he]

/-! ## `weightReal` invariance when there is no current across the cut -/

lemma weightReal_cutCoupling_eq_weightReal
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (S : Finset (↥Λ)) (n : Current (V := V) Λ)
    (hzero : ∀ e : Edge (V := V) Λ, EdgeCross (V := V) (Λ := Λ) S e → n e = 0) :
    weightReal (V := V) (Λ := Λ) β (cutCoupling (V := V) (Λ := Λ) J S) n
      =
      weightReal (V := V) (Λ := Λ) β J n := by
  classical
  unfold weightReal cutCoupling
  -- rewrite the `Fintype` products as `Finset.univ` products
  simp [Fintype.prod]
  refine Finset.prod_congr rfl ?_
  intro e _he
  by_cases hcross : EdgeCross (V := V) (Λ := Λ) S e
  · have hn : n e = 0 := hzero e hcross
    simp [hcross, hn]
  · simp [hcross]

lemma weightReal_cutCoupling_eq_zero_of_exists_cross_pos
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (S : Finset (↥Λ)) (n : Current (V := V) Λ)
    (hex : ∃ e : Edge (V := V) Λ, EdgeCross (V := V) (Λ := Λ) S e ∧ 0 < n e) :
    weightReal (V := V) (Λ := Λ) β (cutCoupling (V := V) (Λ := Λ) J S) n = 0 := by
  classical
  rcases hex with ⟨e, hecross, hpos⟩
  unfold weightReal cutCoupling
  -- rewrite the `Fintype` product as a `Finset.univ` product
  simp [Fintype.prod]
  -- isolate the vanishing factor at the crossing edge `e`
  have hfac :
      (β * (if EdgeCross (V := V) (Λ := Λ) S e then 0 else J e)) ^ (n e) / (n e).factorial = 0 := by
    have hn : 0 < n e := hpos
    have hn0 : n e ≠ 0 := Nat.ne_of_gt hn
    simp [hecross, hn0]
  -- the full product is zero because one factor is zero
  refine (Finset.prod_eq_zero_iff.2 ?_)
  refine ⟨e, ?_⟩
  simp [hfac]

end RandomCurrent

end SpinGlass.Papers.Triviality4D

