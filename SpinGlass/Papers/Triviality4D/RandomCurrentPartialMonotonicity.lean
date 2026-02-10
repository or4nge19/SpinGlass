import SpinGlass.Papers.Triviality4D.RandomCurrentConsequences

/-!
# Partial monotonicity for random currents (finite volume)

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

/-!
## Pair-current expectations

For Appendix Lemma `lem:a` we need to take expectations of *functions* of a pair of currents
under the source-conditioned two-current law. `PPairReal` is tailored to *events of the total*
current; the corresponding expectation functional on pairs is provided by `EPairReal` in
`SpinGlass.Papers.Triviality4D.RandomCurrentConsequences` (imported above).
-/

/-! ## Cut couplings across a vertex set -/

/-- An edge crosses a vertex cut `S` if its endpoints lie on opposite sides. -/
def EdgeCross (S : Finset (↥Λ)) (e : Edge (V := V) Λ) : Prop :=
  (e.1.out.1 ∈ S ∧ e.1.out.2 ∉ S) ∨ (e.1.out.1 ∉ S ∧ e.1.out.2 ∈ S)

/-! A current carries no flow across `S` if it vanishes on every crossing edge. -/
def NoCross (S : Finset (↥Λ)) (n : Current (V := V) Λ) : Prop :=
  ∀ e : Edge (V := V) Λ, EdgeCross (V := V) (Λ := Λ) S e → n e = 0

noncomputable instance (S : Finset (↥Λ)) (n : Current (V := V) Λ) :
    Decidable (NoCross (V := V) (Λ := Λ) S n) := by
  classical
  dsimp [NoCross]
  infer_instance

noncomputable instance (S : Finset (↥Λ)) (e : Edge (V := V) Λ) :
    Decidable (EdgeCross (V := V) (Λ := Λ) S e) := by
  classical
  dsimp [EdgeCross]
  infer_instance

omit [DecidableEq V] in
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

@[simp]
lemma cutCoupling_of_cross
    (J : Edge (V := V) Λ → ℝ) (S : Finset (↥Λ)) {e : Edge (V := V) Λ}
    (he : EdgeCross (V := V) (Λ := Λ) S e) :
    cutCoupling (V := V) (Λ := Λ) J S e = 0 := by
  simp [cutCoupling, he]

@[simp]
lemma cutCoupling_of_not_cross
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
  unfold weightReal cutCoupling
  refine Fintype.prod_congr (f := fun e : Edge (V := V) Λ =>
      (β * (if EdgeCross (V := V) (Λ := Λ) S e then 0 else J e)) ^ (n e) / (n e).factorial)
    (g := fun e : Edge (V := V) Λ => (β * J e) ^ (n e) / (n e).factorial) ?_
  intro e
  by_cases hcross : EdgeCross (V := V) (Λ := Λ) S e
  · have hn : n e = 0 := hzero e hcross
    simp [hcross, hn]
  · simp [hcross]

/-- The part of a current supported on edges with both endpoints in `S`. -/
noncomputable def restrictInside (S : Finset (↥Λ)) (n : Current (V := V) Λ) : Current (V := V) Λ :=
  fun e => if (e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S) then n e else 0

/-- The part of a current supported on edges with both endpoints in `Sᶜ`. -/
noncomputable def restrictOutside (S : Finset (↥Λ)) (n : Current (V := V) Λ) : Current (V := V) Λ :=
  fun e => if (e.1.out.1 ∉ S ∧ e.1.out.2 ∉ S) then n e else 0

lemma weightReal_eq_mul_weightReal_restrictInside_restrictOutside
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (S : Finset (↥Λ)) (n : Current (V := V) Λ)
    (hzero : ∀ e : Edge (V := V) Λ, EdgeCross (V := V) (Λ := Λ) S e → n e = 0) :
    weightReal (V := V) (Λ := Λ) β J n
      =
      weightReal (V := V) (Λ := Λ) β J (restrictInside (V := V) (Λ := Λ) S n) *
        weightReal (V := V) (Λ := Λ) β J (restrictOutside (V := V) (Λ := Λ) S n) := by
  classical
  unfold weightReal restrictInside restrictOutside
  -- pointwise factorization, then `Fintype.prod_mul_distrib`
  have hpoint :
      (fun e : Edge (V := V) Λ => (β * J e) ^ (n e) / (n e).factorial)
        =
        (fun e : Edge (V := V) Λ =>
          ((β * J e) ^ (if e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S then n e else 0) /
                (if e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S then n e else 0).factorial) *
            ((β * J e) ^ (if e.1.out.1 ∉ S ∧ e.1.out.2 ∉ S then n e else 0) /
                (if e.1.out.1 ∉ S ∧ e.1.out.2 ∉ S then n e else 0).factorial)) := by
    funext e
    by_cases h1 : e.1.out.1 ∈ S <;> by_cases h2 : e.1.out.2 ∈ S
    · -- inside
      simp [h1, h2]
    · -- crossing (out.1 in, out.2 out)
      have hz : n e = 0 := hzero e (Or.inl ⟨h1, h2⟩)
      simp [h1, h2, hz]
    · -- crossing (out.1 out, out.2 in)
      have hz : n e = 0 := hzero e (Or.inr ⟨h1, h2⟩)
      simp [h1, h2, hz]
    · -- outside
      simp [h1, h2]
  calc
    (∏ e : Edge (V := V) Λ, (β * J e) ^ (n e) / (n e).factorial)
        =
        ∏ e : Edge (V := V) Λ,
          ((β * J e) ^ (if e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S then n e else 0) /
                (if e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S then n e else 0).factorial) *
            ((β * J e) ^ (if e.1.out.1 ∉ S ∧ e.1.out.2 ∉ S then n e else 0) /
                (if e.1.out.1 ∉ S ∧ e.1.out.2 ∉ S then n e else 0).factorial) := by
          simp [hpoint]
    _ =
        (∏ e : Edge (V := V) Λ,
            (β * J e) ^ (if e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S then n e else 0) /
              (if e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S then n e else 0).factorial) *
          (∏ e : Edge (V := V) Λ,
            (β * J e) ^ (if e.1.out.1 ∉ S ∧ e.1.out.2 ∉ S then n e else 0) /
              (if e.1.out.1 ∉ S ∧ e.1.out.2 ∉ S then n e else 0).factorial) := by
          -- rewrite the `Fintype` products as `Finset.univ` products, then use `Finset.prod_mul_distrib`
          simpa using
            (Finset.prod_mul_distrib (s := (Finset.univ : Finset (Edge (V := V) Λ)))
              (f := fun e : Edge (V := V) Λ =>
                (β * J e) ^ (if e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S then n e else 0) /
                  (if e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S then n e else 0).factorial)
              (g := fun e : Edge (V := V) Λ =>
                (β * J e) ^ (if e.1.out.1 ∉ S ∧ e.1.out.2 ∉ S then n e else 0) /
                  (if e.1.out.1 ∉ S ∧ e.1.out.2 ∉ S then n e else 0).factorial))

lemma weightReal_cutCoupling_eq_zero_of_exists_cross_pos
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (S : Finset (↥Λ)) (n : Current (V := V) Λ)
    (hex : ∃ e : Edge (V := V) Λ, EdgeCross (V := V) (Λ := Λ) S e ∧ 0 < n e) :
    weightReal (V := V) (Λ := Λ) β (cutCoupling (V := V) (Λ := Λ) J S) n = 0 := by
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

lemma weightReal_cutCoupling_eq_ite_noCross
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (S : Finset (↥Λ)) (n : Current (V := V) Λ) :
    weightReal (V := V) (Λ := Λ) β (cutCoupling (V := V) (Λ := Λ) J S) n
      =
      if NoCross (V := V) (Λ := Λ) S n then weightReal (V := V) (Λ := Λ) β J n else 0 := by
  classical
  by_cases hNC : NoCross (V := V) (Λ := Λ) S n
  · simpa [hNC] using
      (weightReal_cutCoupling_eq_weightReal (V := V) (Λ := Λ) (β := β) (J := J) (S := S) (n := n)
        hNC)
  · have hex : ∃ e : Edge (V := V) Λ, EdgeCross (V := V) (Λ := Λ) S e ∧ 0 < n e := by
      dsimp [NoCross] at hNC
      push_neg at hNC
      rcases hNC with ⟨e, hecross, hne0⟩
      exact ⟨e, hecross, Nat.pos_of_ne_zero hne0⟩
    have hz :
        weightReal (V := V) (Λ := Λ) β (cutCoupling (V := V) (Λ := Λ) J S) n = 0 :=
      weightReal_cutCoupling_eq_zero_of_exists_cross_pos (V := V) (Λ := Λ) (β := β) (J := J) (S := S)
        (n := n) hex
    simpa [hNC] using hz

lemma ZReal_cutCoupling_eq_tsum_ite_noCross
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (S : Finset (↥Λ)) (B : Finset (↥Λ)) :
    ZReal (V := V) (Λ := Λ) β (cutCoupling (V := V) (Λ := Λ) J S) B
      =
      ∑' n : Current (V := V) Λ,
        if sources (V := V) n = B then
          (if NoCross (V := V) (Λ := Λ) S n then weightReal (V := V) (Λ := Λ) β J n else 0)
        else 0 := by
  unfold ZReal
  refine tsum_congr ?_
  intro n
  by_cases hsrc : sources (V := V) n = B
  · simp [hsrc, weightReal_cutCoupling_eq_ite_noCross (V := V) (Λ := Λ) (β := β) (J := J) (S := S)
      (n := n)]
  · simp [hsrc]

/-! ## Cluster cuts (no current crosses a cluster boundary) -/

/-- The union of trace clusters of all vertices in a finite set `S`. -/
noncomputable def clusterFinsetSet (n : Current (V := V) Λ) (S : Finset (↥Λ)) : Finset (↥Λ) := by
  classical
  exact (Finset.univ.filter fun y => ∃ x ∈ S, Connected (V := V) (Λ := Λ) n x y)

omit [DecidableEq V] in
lemma mem_clusterFinsetSet_iff (n : Current (V := V) Λ) (S : Finset (↥Λ)) (y : ↥Λ) :
    y ∈ clusterFinsetSet (V := V) (Λ := Λ) n S ↔ ∃ x ∈ S, Connected (V := V) (Λ := Λ) n x y := by
  simp [clusterFinsetSet]

omit [DecidableEq V] in
lemma clusterFinsetSet_closed_of_adj
    (n : Current (V := V) Λ) (S : Finset (↥Λ)) {u v : ↥Λ}
    (hu : u ∈ clusterFinsetSet (V := V) (Λ := Λ) n S) (h : Adj (V := V) (Λ := Λ) n u v) :
    v ∈ clusterFinsetSet (V := V) (Λ := Λ) n S := by
  rcases (mem_clusterFinsetSet_iff (V := V) (Λ := Λ) n S u).1 hu with ⟨y, hyS, hyu⟩
  have huv : Connected (V := V) (Λ := Λ) n u v := Relation.ReflTransGen.single h
  have hyv : Connected (V := V) (Λ := Λ) n y v :=
    Connected.trans (V := V) (Λ := Λ) n hyu huv
  exact (mem_clusterFinsetSet_iff (V := V) (Λ := Λ) n S v).2 ⟨y, hyS, hyv⟩

omit [DecidableEq V] in
lemma current_eq_zero_of_edgeCross_clusterFinsetSet
    (n : Current (V := V) Λ) (S : Finset (↥Λ)) (e : Edge (V := V) Λ)
    (he : EdgeCross (V := V) (Λ := Λ) (clusterFinsetSet (V := V) (Λ := Λ) n S) e) :
    n e = 0 := by
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · by_contra hne0
    have hpos : 0 < n e := Nat.pos_of_ne_zero hne0
    have hne : (e.1.out.1 : ↥Λ) ≠ e.1.out.2 := by
      intro hEq
      have : Sym2.IsDiag (s(e.1.out.1, e.1.out.2) : Sym2 (↥Λ)) :=
        (Sym2.mk_isDiag_iff (x := e.1.out.1) (y := e.1.out.2)).2 hEq
      have : Sym2.IsDiag (e.1 : Sym2 (↥Λ)) := by
        simpa [Sym2.mk, e.1.out_eq] using this
      exact e.2 this
    have hadj : Adj (V := V) (Λ := Λ) n e.1.out.1 e.1.out.2 := by
      refine ⟨hne, ?_⟩
      have heq : edge (V := V) (Λ := Λ) e.1.out.1 e.1.out.2 hne = e := by
        apply Subtype.ext
        simp [edge, Sym2.mk, e.1.out_eq]
      simpa [heq] using hpos
    have hmem :
        e.1.out.2 ∈ clusterFinsetSet (V := V) (Λ := Λ) n S :=
      clusterFinsetSet_closed_of_adj (V := V) (Λ := Λ) n S (u := e.1.out.1) (v := e.1.out.2) h1 hadj
    exact h2 hmem
  · by_contra hne0
    have hpos : 0 < n e := Nat.pos_of_ne_zero hne0
    have hne : (e.1.out.1 : ↥Λ) ≠ e.1.out.2 := by
      intro hEq
      have : Sym2.IsDiag (s(e.1.out.1, e.1.out.2) : Sym2 (↥Λ)) :=
        (Sym2.mk_isDiag_iff (x := e.1.out.1) (y := e.1.out.2)).2 hEq
      have : Sym2.IsDiag (e.1 : Sym2 (↥Λ)) := by
        simpa [Sym2.mk, e.1.out_eq] using this
      exact e.2 this
    have hadj12 : Adj (V := V) (Λ := Λ) n e.1.out.1 e.1.out.2 := by
      refine ⟨hne, ?_⟩
      have heq : edge (V := V) (Λ := Λ) e.1.out.1 e.1.out.2 hne = e := by
        apply Subtype.ext
        simp [edge, Sym2.mk, e.1.out_eq]
      simpa [heq] using hpos
    have hadj21 : Adj (V := V) (Λ := Λ) n e.1.out.2 e.1.out.1 :=
      (Adj_comm (V := V) (Λ := Λ) n (x := e.1.out.1) (y := e.1.out.2)).1 hadj12
    have hmem :
        e.1.out.1 ∈ clusterFinsetSet (V := V) (Λ := Λ) n S :=
      clusterFinsetSet_closed_of_adj (V := V) (Λ := Λ) n S (u := e.1.out.2) (v := e.1.out.1) h2 hadj21
    exact h1 hmem

omit [DecidableEq V] in
lemma current_eq_zero_of_edgeCross_clusterFinsetSet_add
    (n₁ n₂ : Current (V := V) Λ) (S : Finset (↥Λ)) (e : Edge (V := V) Λ)
    (he : EdgeCross (V := V) (Λ := Λ) (clusterFinsetSet (V := V) (Λ := Λ) (n₁ + n₂) S) e) :
    n₁ e = 0 ∧ n₂ e = 0 := by
  have h0 : (n₁ + n₂) e = 0 :=
    current_eq_zero_of_edgeCross_clusterFinsetSet (V := V) (Λ := Λ) (n := (n₁ + n₂)) S e he
  have hsum : n₁ e + n₂ e = 0 := by
    simpa using h0
  exact Nat.add_eq_zero_iff.mp hsum

omit [DecidableEq V] in
lemma current_eq_zero_of_edgeCross_clusterFinset
    (n : Current (V := V) Λ) (x : ↥Λ) (e : Edge (V := V) Λ)
    (he : EdgeCross (V := V) (Λ := Λ) (clusterFinset (V := V) (Λ := Λ) n x) e) :
    n e = 0 := by
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact
      edge_zero_of_boundary_clusterFinset (V := V) (Λ := Λ) n (x := x) (e := e) h1 h2
  · exact
      edge_zero_of_boundary_clusterFinset_rev (V := V) (Λ := Λ) n (x := x) (e := e) h2 h1

omit [DecidableEq V] in
lemma current_eq_zero_of_edgeCross_clusterFinset_add
    (n₁ n₂ : Current (V := V) Λ) (x : ↥Λ) (e : Edge (V := V) Λ)
    (he : EdgeCross (V := V) (Λ := Λ) (clusterFinset (V := V) (Λ := Λ) (n₁ + n₂) x) e) :
    n₁ e = 0 ∧ n₂ e = 0 := by
  have h0 : (n₁ + n₂) e = 0 :=
    current_eq_zero_of_edgeCross_clusterFinset (V := V) (Λ := Λ) (n := (n₁ + n₂)) x e he
  have hsum : n₁ e + n₂ e = 0 := by
    simpa using h0
  exact (Nat.add_eq_zero_iff.mp hsum)

lemma weightReal_cutCoupling_clusterFinsetSet_eq_weightReal_left
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (n₁ n₂ : Current (V := V) Λ) (S : Finset (↥Λ)) :
    weightReal (V := V) (Λ := Λ) β
          (cutCoupling (V := V) (Λ := Λ) J (clusterFinsetSet (V := V) (Λ := Λ) (n₁ + n₂) S)) n₁
      =
      weightReal (V := V) (Λ := Λ) β J n₁ := by
  refine weightReal_cutCoupling_eq_weightReal (V := V) (Λ := Λ) (β := β) (J := J)
    (S := clusterFinsetSet (V := V) (Λ := Λ) (n₁ + n₂) S) (n := n₁) ?_
  intro e he
  exact
    (current_eq_zero_of_edgeCross_clusterFinsetSet_add (V := V) (Λ := Λ) (n₁ := n₁) (n₂ := n₂)
      (S := S) e he).1

lemma weightReal_cutCoupling_clusterFinsetSet_eq_weightReal_right
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (n₁ n₂ : Current (V := V) Λ) (S : Finset (↥Λ)) :
    weightReal (V := V) (Λ := Λ) β
          (cutCoupling (V := V) (Λ := Λ) J (clusterFinsetSet (V := V) (Λ := Λ) (n₁ + n₂) S)) n₂
      =
      weightReal (V := V) (Λ := Λ) β J n₂ := by
  refine weightReal_cutCoupling_eq_weightReal (V := V) (Λ := Λ) (β := β) (J := J)
    (S := clusterFinsetSet (V := V) (Λ := Λ) (n₁ + n₂) S) (n := n₂) ?_
  intro e he
  exact
    (current_eq_zero_of_edgeCross_clusterFinsetSet_add (V := V) (Λ := Λ) (n₁ := n₁) (n₂ := n₂)
      (S := S) e he).2

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
