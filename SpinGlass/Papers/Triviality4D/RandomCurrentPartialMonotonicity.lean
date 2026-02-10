import SpinGlass.Papers.Triviality4D.RandomCurrentConsequences

/-!
# Partial monotonicity tools for random currents (finite volume)

This file develops basic infrastructure for the paper's Appendix Lemma `lem:a`:
we introduce a **cut coupling** which deletes (sets to zero) the couplings across a vertex set.

For a current that carries **no** flow across the cut, the random-current
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

noncomputable instance (S : Finset (↥Λ)) (e : Edge (V := V) Λ) :
    Decidable (EdgeCross (V := V) (Λ := Λ) S e) := by
  classical
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
  -- work directly with `Fintype` products via pointwise congruence
  refine Fintype.prod_congr (f := fun e : Edge (V := V) Λ =>
      (β * (if EdgeCross (V := V) (Λ := Λ) S e then 0 else J e)) ^ (n e) / (n e).factorial)
    (g := fun e : Edge (V := V) Λ => (β * J e) ^ (n e) / (n e).factorial) ?_
  intro e
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
  have hfac :
      (β * (if EdgeCross (V := V) (Λ := Λ) S e then 0 else J e)) ^ (n e) / (n e).factorial = 0 := by
    have hn0 : n e ≠ 0 := Nat.ne_of_gt hpos
    simp [hecross, hn0]
  have heUniv : e ∈ (Finset.univ : Finset (Edge (V := V) Λ)) := by simp
  exact
    (Finset.prod_eq_zero (s := (Finset.univ : Finset (Edge (V := V) Λ)))
      (f := fun e' : Edge (V := V) Λ =>
        (β * (if EdgeCross (V := V) (Λ := Λ) S e' then 0 else J e')) ^ (n e') / (n e').factorial)
      (i := e) heUniv hfac)

/-! ## Cluster cuts (no current crosses a cluster boundary) -/

lemma current_eq_zero_of_edgeCross_clusterFinset
    (n : Current (V := V) Λ) (x : ↥Λ) (e : Edge (V := V) Λ)
    (he : EdgeCross (V := V) (Λ := Λ) (clusterFinset (V := V) (Λ := Λ) n x) e) :
    n e = 0 := by
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact
      edge_zero_of_boundary_clusterFinset (V := V) (Λ := Λ) n (x := x) (e := e) h1 h2
  · exact
      edge_zero_of_boundary_clusterFinset_rev (V := V) (Λ := Λ) n (x := x) (e := e) h2 h1

lemma current_eq_zero_of_edgeCross_clusterFinset_add
    (n₁ n₂ : Current (V := V) Λ) (x : ↥Λ) (e : Edge (V := V) Λ)
    (he : EdgeCross (V := V) (Λ := Λ) (clusterFinset (V := V) (Λ := Λ) (n₁ + n₂) x) e) :
    n₁ e = 0 ∧ n₂ e = 0 := by
  have h0 : (n₁ + n₂) e = 0 :=
    current_eq_zero_of_edgeCross_clusterFinset (V := V) (Λ := Λ) (n := (n₁ + n₂)) x e he
  have hsum : n₁ e + n₂ e = 0 := by
    simpa using h0
  exact (Nat.add_eq_zero_iff.mp hsum)

lemma weightReal_cutCoupling_clusterFinset_eq_weightReal_left
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (n₁ n₂ : Current (V := V) Λ) (x : ↥Λ) :
    weightReal (V := V) (Λ := Λ) β
          (cutCoupling (V := V) (Λ := Λ) J (clusterFinset (V := V) (Λ := Λ) (n₁ + n₂) x)) n₁
      =
      weightReal (V := V) (Λ := Λ) β J n₁ := by
  refine weightReal_cutCoupling_eq_weightReal (V := V) (Λ := Λ) (β := β) (J := J)
    (S := clusterFinset (V := V) (Λ := Λ) (n₁ + n₂) x) (n := n₁) ?_
  intro e he
  exact (current_eq_zero_of_edgeCross_clusterFinset_add (V := V) (Λ := Λ) (n₁ := n₁) (n₂ := n₂) x e he).1

lemma weightReal_cutCoupling_clusterFinset_eq_weightReal_right
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (n₁ n₂ : Current (V := V) Λ) (x : ↥Λ) :
    weightReal (V := V) (Λ := Λ) β
          (cutCoupling (V := V) (Λ := Λ) J (clusterFinset (V := V) (Λ := Λ) (n₁ + n₂) x)) n₂
      =
      weightReal (V := V) (Λ := Λ) β J n₂ := by
  refine weightReal_cutCoupling_eq_weightReal (V := V) (Λ := Λ) (β := β) (J := J)
    (S := clusterFinset (V := V) (Λ := Λ) (n₁ + n₂) x) (n := n₂) ?_
  intro e he
  exact (current_eq_zero_of_edgeCross_clusterFinset_add (V := V) (Λ := Λ) (n₁ := n₁) (n₂ := n₂) x e he).2

end RandomCurrent

end SpinGlass.Papers.Triviality4D
