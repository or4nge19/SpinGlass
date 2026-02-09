import SpinGlass.Papers.Triviality4D.RandomCurrentRepresentation
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.Normed.Group.Indicator

/-!
# Random current switching lemma (finite volume)

This file formalizes the **switching lemma** from `4D_triviality_June_2021_final.tex`, Lemma 1.5
("Definition and switching lemma" subsection).

We work in finite volume `Λ` with currents `n : Edge Λ → ℕ` and the real-valued current weights
`weightReal` introduced in `RandomCurrentRepresentation.lean`.
-/

open scoped BigOperators Topology

namespace SpinGlass.Papers.Triviality4D

namespace RandomCurrent

universe u

variable {V : Type u} [DecidableEq V]
variable {Λ : Finset V}

/-! ## A finite type of edge-copy assignments for a fixed total current -/

/--
For a fixed total current `n`, an **assignment** chooses, for each edge `e`, a subset of the
`n e` edge-copies that will be attributed to the *first* current in a splitting `n = n₁ + n₂`.

We represent edge-copies of `e` by `Fin (n e)`.
-/
abbrev EdgeAssign (n : Current (V := V) Λ) : Type u :=
  ∀ e : Edge (V := V) Λ, Finset (Fin (n e))

/-- The first subcurrent `n₁` encoded by an edge assignment `S` for a total current `n`.

By definition, `n₁ e` is the number of edge-copies of `e` assigned to the first current. -/
noncomputable def currentOfEdgeAssign (n : Current (V := V) Λ) (S : EdgeAssign (V := V) (Λ := Λ) n) :
    Current (V := V) Λ :=
  fun e => (S e).card

/-- The complementary subcurrent `n₂` encoded by an edge assignment `S` for a total current `n`.

By definition, `n₂ e = n e - n₁ e`. -/
noncomputable def currentOfEdgeAssignCompl (n : Current (V := V) Λ) (S : EdgeAssign (V := V) (Λ := Λ) n) :
    Current (V := V) Λ :=
  fun e => n e - (S e).card

omit [DecidableEq V] in
lemma currentOfEdgeAssign_le (n : Current (V := V) Λ) (S : EdgeAssign (V := V) (Λ := Λ) n) :
    CurrentLE (V := V) (currentOfEdgeAssign (V := V) (Λ := Λ) n S) n := by
  intro e
  have hle : (S e).card ≤ n e := by
    simpa using (Finset.card_le_univ (s := S e))
  simpa [currentOfEdgeAssign] using hle

/-! ## Counting edge assignments with prescribed multiplicities -/

/-- Fiber of edge assignments inducing a given subcurrent `n₁`. -/
abbrev EdgeAssignFiber (n n1 : Current (V := V) Λ) : Type u :=
  {S : EdgeAssign (V := V) (Λ := Λ) n // currentOfEdgeAssign (V := V) (Λ := Λ) n S = n1}

/-- Reindex `EdgeAssignFiber n n₁` edgewise as families of fixed-cardinality subsets. -/
noncomputable def edgeAssignFiberEquiv
    (n n1 : Current (V := V) Λ) :
    EdgeAssignFiber (V := V) (Λ := Λ) n n1 ≃
      (∀ e : Edge (V := V) Λ, {s : Finset (Fin (n e)) // s.card = n1 e}) := by
  refine
    { toFun := fun S => fun e => ⟨S.1 e, ?_⟩
      invFun := fun T => ⟨fun e => (T e).1, by
        funext e
        simpa [currentOfEdgeAssign] using (T e).2⟩
      left_inv := ?_
      right_inv := ?_ }
  · have h := congrArg (fun m : Current (V := V) Λ => m e) S.2
    simpa [currentOfEdgeAssign] using h
  · intro S
    ext e
    rfl
  · intro T
    funext e
    apply Subtype.ext
    rfl

lemma card_edgeAssignFiber (n n1 : Current (V := V) Λ) :
    Fintype.card (EdgeAssignFiber (V := V) (Λ := Λ) n n1) =
      ∏ e : Edge (V := V) Λ, (n e).choose (n1 e) := by
  calc
    Fintype.card (EdgeAssignFiber (V := V) (Λ := Λ) n n1)
        = Fintype.card (∀ e : Edge (V := V) Λ, {s : Finset (Fin (n e)) // s.card = n1 e}) := by
            simpa using Fintype.card_congr (edgeAssignFiberEquiv (V := V) (Λ := Λ) n n1)
    _ = ∏ e : Edge (V := V) Λ, Fintype.card {s : Finset (Fin (n e)) // s.card = n1 e} := by
          simp
    _ = ∏ e : Edge (V := V) Λ, (n e).choose (n1 e) := by
          simp [Fintype.card_finset_len]

/-! ## Canonical edge assignments representing subcurrents -/

/-- The canonical subset of `Fin n` of cardinality `k` (using `Fin.castLE`). -/
noncomputable def canonEdgeSet (n k : ℕ) (hk : k ≤ n) : Finset (Fin n) :=
  (Finset.univ.image (Fin.castLE hk))

lemma card_canonEdgeSet (n k : ℕ) (hk : k ≤ n) :
    (canonEdgeSet n k hk).card = k := by
  simpa [canonEdgeSet] using
    (Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin k)))
      (Fin.castLE_injective hk))

/-- The canonical edge assignment representing a subcurrent `m ≤ n`.

For each edge `e`, we take the canonical subset of `Fin (n e)` of size `m e`. -/
noncomputable def canonEdgeAssign (n m : Current (V := V) Λ) (hm : CurrentLE (V := V) m n) :
    EdgeAssign (V := V) (Λ := Λ) n :=
  fun e => canonEdgeSet (n e) (m e) (hm e)

omit [DecidableEq V] in
lemma currentOfEdgeAssign_canonEdgeAssign (n m : Current (V := V) Λ) (hm : CurrentLE (V := V) m n) :
    currentOfEdgeAssign (V := V) (Λ := Λ) n (canonEdgeAssign (V := V) (Λ := Λ) n m hm) = m := by
  funext e
  simp [canonEdgeAssign, currentOfEdgeAssign, card_canonEdgeSet]

lemma exists_edgeAssign_sources_of_hasSubCurrent (n : Current (V := V) Λ) (B : Finset (↥Λ)) :
    HasSubCurrent (V := V) (Λ := Λ) n B →
      ∃ M : EdgeAssign (V := V) (Λ := Λ) n,
        sources (V := V) (currentOfEdgeAssign (V := V) (Λ := Λ) n M) = B := by
  rintro ⟨m, hmle, hsrc⟩
  refine ⟨canonEdgeAssign (V := V) (Λ := Λ) n m hmle, ?_⟩
  simpa [currentOfEdgeAssign_canonEdgeAssign (V := V) (Λ := Λ) (n := n) (m := m) hmle] using hsrc

omit [DecidableEq V] in
lemma currentOfEdgeAssign_add_currentOfEdgeAssignCompl (n : Current (V := V) Λ)
    (S : EdgeAssign (V := V) (Λ := Λ) n) :
    currentOfEdgeAssign (V := V) (Λ := Λ) n S + currentOfEdgeAssignCompl (V := V) (Λ := Λ) n S = n := by
  funext e
  have hle : (S e).card ≤ n e := by
    simpa [currentOfEdgeAssign] using (currentOfEdgeAssign_le (V := V) (Λ := Λ) (n := n) S e)
  simp [currentOfEdgeAssign, currentOfEdgeAssignCompl, Nat.add_sub_of_le hle]

/-! ## Real weight algebra for splittings -/

lemma edgeFactor_mul (a : ℝ) (k l : ℕ) :
    (a ^ k / (k.factorial : ℝ)) * (a ^ l / (l.factorial : ℝ)) =
      (a ^ (k + l) / ((k + l).factorial : ℝ)) * ((Nat.choose (k + l) k) : ℝ) := by
  have hk0 : (k.factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero k)
  have hl0 : (l.factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero l)
  have hkl0 : ((k + l).factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero (k + l))
  field_simp [hk0, hl0, hkl0]
  rw [← pow_add]
  have hk : k ≤ k + l := Nat.le_add_right k l
  have hnat : (Nat.choose (k + l) k) * k.factorial * l.factorial = (k + l).factorial := by
    simpa [Nat.add_sub_cancel_left k l, mul_assoc, mul_left_comm, mul_comm] using
      (Nat.choose_mul_factorial_mul_factorial (n := k + l) (k := k) hk)
  have hreal :
      ((Nat.choose (k + l) k : ℕ) : ℝ) * (k.factorial : ℝ) * (l.factorial : ℝ) =
        ((k + l).factorial : ℝ) := by
    exact_mod_cast hnat
  calc
    a ^ (k + l) * ((k + l).factorial : ℝ)
        = a ^ (k + l) * (((Nat.choose (k + l) k : ℕ) : ℝ) * (k.factorial : ℝ) * (l.factorial : ℝ)) := by
            simp [hreal]
    _ = (k.factorial : ℝ) * (l.factorial : ℝ) * a ^ (k + l) * ((Nat.choose (k + l) k : ℕ) : ℝ) := by
            ring_nf

lemma weightReal_mul_eq (β : ℝ) (J : Edge (V := V) Λ → ℝ)
    (n1 n2 : Current (V := V) Λ) :
    weightReal (V := V) (Λ := Λ) β J n1 * weightReal (V := V) (Λ := Λ) β J n2 =
      weightReal (V := V) (Λ := Λ) β J (n1 + n2) *
        (∏ e : Edge (V := V) Λ, ((Nat.choose (n1 e + n2 e) (n1 e)) : ℝ)) := by
  calc
    weightReal (V := V) (Λ := Λ) β J n1 * weightReal (V := V) (Λ := Λ) β J n2
        = ∏ e : Edge (V := V) Λ,
            ((β * J e) ^ (n1 e) / (n1 e).factorial) *
              ((β * J e) ^ (n2 e) / (n2 e).factorial) := by
          simpa [weightReal] using
            (Finset.prod_mul_distrib (s := (Finset.univ : Finset (Edge (V := V) Λ)))
              (f := fun e => (β * J e) ^ (n1 e) / (n1 e).factorial)
              (g := fun e => (β * J e) ^ (n2 e) / (n2 e).factorial)).symm
    _ = ∏ e : Edge (V := V) Λ,
          ((β * J e) ^ (n1 e + n2 e) / (n1 e + n2 e).factorial) *
            ((Nat.choose (n1 e + n2 e) (n1 e)) : ℝ) := by
          refine Finset.prod_congr rfl ?_
          intro e _
          simpa using
            (edgeFactor_mul (a := β * J e) (k := n1 e) (l := n2 e))
    _ = (∏ e : Edge (V := V) Λ, (β * J e) ^ (n1 e + n2 e) / (n1 e + n2 e).factorial) *
          (∏ e : Edge (V := V) Λ, ((Nat.choose (n1 e + n2 e) (n1 e)) : ℝ)) := by
          simpa using
            (Finset.prod_mul_distrib (s := (Finset.univ : Finset (Edge (V := V) Λ)))
              (f := fun e => (β * J e) ^ (n1 e + n2 e) / (n1 e + n2 e).factorial)
              (g := fun e => ((Nat.choose (n1 e + n2 e) (n1 e)) : ℝ)))
    _ = weightReal (V := V) (Λ := Λ) β J (n1 + n2) *
          (∏ e : Edge (V := V) Λ, ((Nat.choose (n1 e + n2 e) (n1 e)) : ℝ)) := by
          simp [weightReal]

/-! ## Finite splittings of a fixed total current -/

/--
For a fixed total current `n`, a `SplitCurrent n` is the choice of an integer `n₁(e) ∈ {0,…,n(e)}`
for every edge `e`. This parametrizes all current splittings `n = n₁ + n₂` by setting
`n₂(e) = n(e) - n₁(e)`.
-/
abbrev SplitCurrent (n : Current (V := V) Λ) : Type u :=
  ∀ e : Edge (V := V) Λ, Fin (n e + 1)

/-- The first current `n₁` associated to a split parameter `s : SplitCurrent n`. -/
noncomputable def splitCurrentToCurrent (n : Current (V := V) Λ) (s : SplitCurrent (V := V) (Λ := Λ) n) :
    Current (V := V) Λ :=
  fun e => (s e).val

/-- The complementary current `n₂ = n - n₁` associated to a split parameter `s : SplitCurrent n`. -/
noncomputable def splitCurrentToCurrentCompl (n : Current (V := V) Λ) (s : SplitCurrent (V := V) (Λ := Λ) n) :
    Current (V := V) Λ :=
  fun e => n e - (s e).val

omit [DecidableEq V] in
lemma splitCurrent_add (n : Current (V := V) Λ) (s : SplitCurrent (V := V) (Λ := Λ) n) :
    splitCurrentToCurrent (V := V) (Λ := Λ) n s +
        splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s = n := by
  funext e
  have hle : (s e).val ≤ n e := Nat.le_of_lt_succ (s e).isLt
  simp [splitCurrentToCurrent, splitCurrentToCurrentCompl, Nat.add_sub_of_le hle]

lemma weightReal_mul_eq_splitCurrent (β : ℝ) (J : Edge (V := V) Λ → ℝ)
    (n : Current (V := V) Λ) (s : SplitCurrent (V := V) (Λ := Λ) n) :
    weightReal (V := V) (Λ := Λ) β J (splitCurrentToCurrent (V := V) (Λ := Λ) n s) *
        weightReal (V := V) (Λ := Λ) β J (splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s)
      =
      weightReal (V := V) (Λ := Λ) β J n *
        (∏ e : Edge (V := V) Λ,
          ((Nat.choose (n e) ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e)) : ℝ)) := by
  classical
  have hsum :
      splitCurrentToCurrent (V := V) (Λ := Λ) n s +
          splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s = n := by
    simpa using (splitCurrent_add (V := V) (Λ := Λ) n s)
  have he :
      ∀ e : Edge (V := V) Λ,
        (splitCurrentToCurrent (V := V) (Λ := Λ) n s) e +
            (splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s) e = n e := by
    intro e
    have := congrArg (fun m : Current (V := V) Λ => m e) hsum
    simpa using this
  simpa [hsum, he] using
    (weightReal_mul_eq (V := V) (Λ := Λ) (β := β) (J := J)
      (n1 := splitCurrentToCurrent (V := V) (Λ := Λ) n s)
      (n2 := splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s))

/-- Forget an edge assignment to its split parameter, by taking edgewise cardinalities. -/
noncomputable def edgeAssignToSplitCurrent (n : Current (V := V) Λ) :
    EdgeAssign (V := V) (Λ := Λ) n → SplitCurrent (V := V) (Λ := Λ) n :=
  fun S e =>
    ⟨(S e).card, Nat.lt_succ_of_le (by
      simpa using (Finset.card_le_univ (s := S e)))⟩

/-- Fiber of edge assignments inducing a fixed split parameter `s : SplitCurrent n`. -/
abbrev EdgeAssignSplitFiber (n : Current (V := V) Λ) (s : SplitCurrent (V := V) (Λ := Λ) n) : Type u :=
  {S : EdgeAssign (V := V) (Λ := Λ) n // edgeAssignToSplitCurrent (V := V) (Λ := Λ) n S = s}

/-- Identify `EdgeAssignSplitFiber n s` with `EdgeAssignFiber n n₁` for `n₁ = splitCurrentToCurrent n s`. -/
noncomputable def edgeAssignSplitFiberEquiv (n : Current (V := V) Λ) (s : SplitCurrent (V := V) (Λ := Λ) n) :
    EdgeAssignSplitFiber (V := V) (Λ := Λ) n s ≃
      EdgeAssignFiber (V := V) (Λ := Λ) n (splitCurrentToCurrent (V := V) (Λ := Λ) n s) := by
  refine
    { toFun := fun S => ⟨S.1, ?_⟩
      invFun := fun S => ⟨S.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · funext e
    have h := congrArg (fun t : SplitCurrent (V := V) (Λ := Λ) n => (t e).val) S.2
    simpa [edgeAssignToSplitCurrent, currentOfEdgeAssign, splitCurrentToCurrent] using h
  · funext e
    apply Fin.ext
    have h := congrArg (fun m : Current (V := V) Λ => m e) S.2
    simpa [edgeAssignToSplitCurrent, currentOfEdgeAssign, splitCurrentToCurrent] using h
  · intro S
    apply Subtype.ext
    rfl
  · intro S
    apply Subtype.ext
    rfl

/-! ## Toggling an assignment and its effect on sources -/

noncomputable def toggleEdgeAssign (n : Current (V := V) Λ)
    (M S : EdgeAssign (V := V) (Λ := Λ) n) : EdgeAssign (V := V) (Λ := Λ) n :=
  fun e => symmDiff (S e) (M e)

omit [DecidableEq V] in
lemma toggleEdgeAssign_involutive (n : Current (V := V) Λ)
    (M : EdgeAssign (V := V) (Λ := Λ) n) :
    Function.Involutive (toggleEdgeAssign (V := V) (Λ := Λ) n M) := by
  intro S
  funext e
  calc
    toggleEdgeAssign (V := V) (Λ := Λ) n M (toggleEdgeAssign (V := V) (Λ := Λ) n M S) e
        = symmDiff (symmDiff (S e) (M e)) (M e) := by
            simp [toggleEdgeAssign]
    _ = symmDiff (S e) (symmDiff (M e) (M e)) := by
          simpa using (symmDiff_assoc (S e) (M e) (M e))
    _ = symmDiff (S e) (⊥ : Finset (Fin (n e))) := by
          simp [symmDiff_self]
    _ = S e := by
          simp

lemma card_symmDiff_add_two_inter {α : Type} [DecidableEq α] (s t : Finset α) :
    (symmDiff s t).card + 2 * (s ∩ t).card = s.card + t.card := by
  have hdisj : Disjoint (s \ t) (t \ s) := by
    refine Finset.disjoint_left.2 ?_
    intro a ha hb
    have hna : a ∉ t := (Finset.mem_sdiff.1 ha).2
    exact hna (Finset.mem_sdiff.1 hb).1
  have hcard : (symmDiff s t).card = (s \ t).card + (t \ s).card := by
    simp [symmDiff, Finset.card_union_of_disjoint hdisj]
  have hst : (s \ t).card = s.card - (s ∩ t).card := by
    simpa [Finset.inter_comm, Finset.inter_left_comm, Finset.inter_assoc] using
      (Finset.card_sdiff (s := t) (t := s))
  have hts : (t \ s).card = t.card - (s ∩ t).card := by
    simpa using (Finset.card_sdiff (s := s) (t := t))
  have hleS : (s ∩ t).card ≤ s.card :=
    Finset.card_le_card (Finset.inter_subset_left (s₁ := s) (s₂ := t))
  have hleT : (s ∩ t).card ≤ t.card :=
    Finset.card_le_card (Finset.inter_subset_right (s₁ := s) (s₂ := t))
  calc
    (symmDiff s t).card + 2 * (s ∩ t).card
        = ((s \ t).card + (t \ s).card) + 2 * (s ∩ t).card := by
            simp [hcard, add_assoc]
    _ = ((s.card - (s ∩ t).card) + (t.card - (s ∩ t).card)) + 2 * (s ∩ t).card := by
            simp [hst, hts]
    _ = (s.card - (s ∩ t).card) + (s ∩ t).card + ((t.card - (s ∩ t).card) + (s ∩ t).card) := by
            ring_nf
    _ = s.card + t.card := by
            simp [Nat.sub_add_cancel hleS, Nat.sub_add_cancel hleT]

noncomputable def interDegree (n : Current (V := V) Λ)
    (S M : EdgeAssign (V := V) (Λ := Λ) n) (x : ↥Λ) : ℕ :=
  ∑ e : Edge (V := V) Λ, if x ∈ (e.1 : Sym2 (↥Λ)) then ((S e) ∩ (M e)).card else 0

lemma degree_toggle_add_two_inter (n : Current (V := V) Λ)
    (S M : EdgeAssign (V := V) (Λ := Λ) n) (x : ↥Λ) :
    degree (V := V) (currentOfEdgeAssign (V := V) (Λ := Λ) n S) x +
        degree (V := V) (currentOfEdgeAssign (V := V) (Λ := Λ) n M) x
      =
      degree (V := V)
          (currentOfEdgeAssign (V := V) (Λ := Λ) n (toggleEdgeAssign (V := V) (Λ := Λ) n M S)) x
        + 2 * interDegree (V := V) (Λ := Λ) n S M x := by
  simp [degree, currentOfEdgeAssign, toggleEdgeAssign, interDegree]
  rw [← Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro e _
  by_cases hx : x ∈ (e.1 : Sym2 (↥Λ))
  · simp [hx, card_symmDiff_add_two_inter (s := S e) (t := M e)]
  · simp [hx]

lemma sources_toggleEdgeAssign (n : Current (V := V) Λ)
    (S M : EdgeAssign (V := V) (Λ := Λ) n) :
    sources (V := V)
        (currentOfEdgeAssign (V := V) (Λ := Λ) n (toggleEdgeAssign (V := V) (Λ := Λ) n M S)) =
      symmDiff (sources (V := V) (currentOfEdgeAssign (V := V) (Λ := Λ) n S))
        (sources (V := V) (currentOfEdgeAssign (V := V) (Λ := Λ) n M)) := by
  ext x
  have hdeg :=
    degree_toggle_add_two_inter (V := V) (Λ := Λ) (n := n) (S := S) (M := M) x
  have heven : Even (2 * interDegree (V := V) (Λ := Λ) n S M x) := by
    simp
  have hiff : ∀ p q : Prop, (p ↔ ¬ q) ↔ (p ∧ ¬ q) ∨ (q ∧ ¬ p) := by
    intro p q
    by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]
  set dS : ℕ :=
    degree (V := V) (currentOfEdgeAssign (V := V) (Λ := Λ) n S) x
  set dM : ℕ :=
    degree (V := V) (currentOfEdgeAssign (V := V) (Λ := Λ) n M) x
  set dT : ℕ :=
    degree (V := V)
        (currentOfEdgeAssign (V := V) (Λ := Λ) n (toggleEdgeAssign (V := V) (Λ := Λ) n M S)) x
  have hoddT : Odd dT ↔ Odd (dS + dM) := by
    have : dS + dM = dT + 2 * interDegree (V := V) (Λ := Λ) n S M x := by
      simpa [dS, dM, dT] using hdeg
    have hremove : Odd (dT + 2 * interDegree (V := V) (Λ := Λ) n S M x) ↔ Odd dT := by
      simpa [heven] using (Nat.odd_add (m := dT) (n := 2 * interDegree (V := V) (Λ := Λ) n S M x))
    exact (by
      simpa [this] using hremove.symm)
  have : (Odd dT) ↔ (Odd dS ∧ ¬ Odd dM) ∨ (Odd dM ∧ ¬ Odd dS) := by
    have hadd : Odd (dS + dM) ↔ (Odd dS ↔ Even dM) := by
      simpa [dS, dM] using (Nat.odd_add (m := dS) (n := dM))
    have : Odd (dS + dM) ↔ (Odd dS ↔ ¬ Odd dM) := by
      simpa [Nat.not_odd_iff_even] using hadd
    exact (hoddT.trans (this.trans (hiff (Odd dS) (Odd dM))))
  simpa [mem_sources_iff, IsSource, dS, dM, dT, Finset.mem_symmDiff] using this

/-! ## Source switching on edge assignments (bijection level) -/

noncomputable def toggleEdgeAssignEquiv (n : Current (V := V) Λ)
    (M : EdgeAssign (V := V) (Λ := Λ) n) :
    EdgeAssign (V := V) (Λ := Λ) n ≃ EdgeAssign (V := V) (Λ := Λ) n :=
  { toFun := toggleEdgeAssign (V := V) (Λ := Λ) n M
    invFun := toggleEdgeAssign (V := V) (Λ := Λ) n M
    left_inv := toggleEdgeAssign_involutive (V := V) (Λ := Λ) n M
    right_inv := toggleEdgeAssign_involutive (V := V) (Λ := Λ) n M }

noncomputable def toggleEdgeAssignEquiv_sources (n : Current (V := V) Λ)
    (A B : Finset (↥Λ)) (M : EdgeAssign (V := V) (Λ := Λ) n)
    (hM : sources (V := V) (currentOfEdgeAssign (V := V) (Λ := Λ) n M) = B) :
    {S : EdgeAssign (V := V) (Λ := Λ) n //
        sources (V := V) (currentOfEdgeAssign (V := V) (Λ := Λ) n S) = symmDiff A B} ≃
      {S : EdgeAssign (V := V) (Λ := Λ) n //
        sources (V := V) (currentOfEdgeAssign (V := V) (Λ := Λ) n S) = A} := by
  refine
    { toFun := fun S =>
        ⟨toggleEdgeAssign (V := V) (Λ := Λ) n M S.1, ?_⟩
      invFun := fun S =>
        ⟨toggleEdgeAssign (V := V) (Λ := Λ) n M S.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hsrc := sources_toggleEdgeAssign (V := V) (Λ := Λ) (n := n) (S := S.1) (M := M)
    simpa [S.2, hM, symmDiff_assoc, symmDiff_self, symmDiff_bot] using hsrc
  · have hsrc := sources_toggleEdgeAssign (V := V) (Λ := Λ) (n := n) (S := S.1) (M := M)
    simpa [S.2, hM] using hsrc
  · intro S
    apply Subtype.ext
    simpa using (toggleEdgeAssign_involutive (V := V) (Λ := Λ) n M S.1)
  · intro S
    apply Subtype.ext
    simpa using (toggleEdgeAssign_involutive (V := V) (Λ := Λ) n M S.1)

/-! ## Counting splittings via edge assignments -/

omit [DecidableEq V] in
lemma splitCurrentToCurrent_edgeAssignToSplitCurrent (n : Current (V := V) Λ)
    (S : EdgeAssign (V := V) (Λ := Λ) n) :
    splitCurrentToCurrent (V := V) (Λ := Λ) n (edgeAssignToSplitCurrent (V := V) (Λ := Λ) n S) =
      currentOfEdgeAssign (V := V) (Λ := Λ) n S := by
  funext e
  rfl

omit [DecidableEq V] in
lemma splitCurrentToCurrentCompl_edgeAssignToSplitCurrent (n : Current (V := V) Λ)
    (S : EdgeAssign (V := V) (Λ := Λ) n) :
    splitCurrentToCurrentCompl (V := V) (Λ := Λ) n (edgeAssignToSplitCurrent (V := V) (Λ := Λ) n S) =
      currentOfEdgeAssignCompl (V := V) (Λ := Λ) n S := by
  funext e
  rfl

lemma card_edgeAssignSplitFiber (n : Current (V := V) Λ) (s : SplitCurrent (V := V) (Λ := Λ) n) :
    Fintype.card (EdgeAssignSplitFiber (V := V) (Λ := Λ) n s) =
      ∏ e : Edge (V := V) Λ, (n e).choose ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e) := by
  calc
    Fintype.card (EdgeAssignSplitFiber (V := V) (Λ := Λ) n s)
        =
        Fintype.card
          (EdgeAssignFiber (V := V) (Λ := Λ) n (splitCurrentToCurrent (V := V) (Λ := Λ) n s)) := by
          simpa using Fintype.card_congr (edgeAssignSplitFiberEquiv (V := V) (Λ := Λ) n s)
    _ = ∏ e : Edge (V := V) Λ, (n e).choose ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e) := by
          simpa using
            (card_edgeAssignFiber (V := V) (Λ := Λ) (n := n)
              (n1 := splitCurrentToCurrent (V := V) (Λ := Λ) n s))

/-!
Summing over a subtype `{x // P x}` equals summing over all `x` with an
indicator.
-/
lemma sum_subtype_eq_sum_if {α : Type*} {M : Type*} [Fintype α] [AddCommMonoid M]
    (P : α → Prop) [DecidablePred P] (f : α → M) :
    (∑ x : {a // P a}, f x.1) = ∑ a : α, (if P a then f a else 0) := by
  classical
  have hinj :
      Set.InjOn (fun x : {a // P a} => (x.1 : α)) (↑(Finset.univ : Finset {a // P a})) := by
    intro x _ y _ h
    exact Subtype.ext (by simpa using h)
  have himage :
      Finset.image (fun x : {a // P a} => (x.1 : α)) (Finset.univ : Finset {a // P a})
        = (Finset.univ.filter P : Finset α) := by
    ext a
    simp [Finset.mem_filter]
  have hsub :
      (∑ x : {a // P a}, f x.1) =
        ∑ a ∈ (Finset.univ.filter P : Finset α), f a := by
    have h :=
      (Finset.sum_image (f := f) (s := (Finset.univ : Finset {a // P a}))
        (g := fun x : {a // P a} => (x.1 : α)) hinj)
    simpa [himage] using h.symm
  calc
    (∑ x : {a // P a}, f x.1)
        = ∑ a ∈ (Finset.univ.filter P : Finset α), f a := hsub
    _ = ∑ a : α, (if P a then f a else 0) := by
          simpa using
            (Finset.sum_filter (s := (Finset.univ : Finset α)) (p := P) (f := f))

/-- Edge assignments whose induced first current has sources `A`. -/
abbrev AssignSources (n : Current (V := V) Λ) (A : Finset (↥Λ)) : Type u :=
  {S : EdgeAssign (V := V) (Λ := Λ) n //
      sources (V := V) (currentOfEdgeAssign (V := V) (Λ := Λ) n S) = A}

noncomputable def assignSourcesEquivSigma (n : Current (V := V) Λ) (A : Finset (↥Λ)) :
    AssignSources (V := V) (Λ := Λ) n A ≃
      (s : {s : SplitCurrent (V := V) (Λ := Λ) n //
        sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A}) ×
        EdgeAssignSplitFiber (V := V) (Λ := Λ) n s.1 := by
  let toFun :
      AssignSources (V := V) (Λ := Λ) n A →
        (s : {s : SplitCurrent (V := V) (Λ := Λ) n //
          sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A}) ×
          EdgeAssignSplitFiber (V := V) (Λ := Λ) n s.1 :=
    fun S =>
      let s : SplitCurrent (V := V) (Λ := Λ) n :=
        edgeAssignToSplitCurrent (V := V) (Λ := Λ) n S.1
      have hs : sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A := by
        simpa [s, splitCurrentToCurrent_edgeAssignToSplitCurrent] using S.2
      ⟨⟨s, hs⟩, ⟨S.1, rfl⟩⟩
  let invFun :
      (s : {s : SplitCurrent (V := V) (Λ := Λ) n //
        sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A}) ×
        EdgeAssignSplitFiber (V := V) (Λ := Λ) n s.1 →
        AssignSources (V := V) (Λ := Λ) n A :=
    fun T =>
      let s : SplitCurrent (V := V) (Λ := Λ) n := T.1.1
      let hs : sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A := T.1.2
      let S : EdgeAssign (V := V) (Λ := Λ) n := T.2.1
      have hsplit :
          edgeAssignToSplitCurrent (V := V) (Λ := Λ) n S = s := by
        simpa using T.2.2
      have hcurr :
          currentOfEdgeAssign (V := V) (Λ := Λ) n S =
            splitCurrentToCurrent (V := V) (Λ := Λ) n s := by
        funext e
        have hval :=
          congrArg (fun t : SplitCurrent (V := V) (Λ := Λ) n => (t e).val) hsplit
        simpa [edgeAssignToSplitCurrent, currentOfEdgeAssign, splitCurrentToCurrent] using hval
      ⟨S, by simpa [hcurr] using hs⟩
  refine
    { toFun := toFun
      invFun := invFun
      left_inv := ?_
      right_inv := ?_ }
  · intro S
    apply Subtype.ext
    simp [toFun, invFun]
  · intro T
    rcases T with ⟨s, Sf⟩
    cases s with
    | mk s hs =>
      cases Sf with
      | mk S hS =>
        cases hS
        simp [toFun, invFun]
        funext e
        apply Fin.ext
        rfl

lemma card_assignSources (n : Current (V := V) Λ) (A : Finset (↥Λ)) :
    Fintype.card (AssignSources (V := V) (Λ := Λ) n A) =
      ∑ s : SplitCurrent (V := V) (Λ := Λ) n,
        if sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A then
          Fintype.card (EdgeAssignSplitFiber (V := V) (Λ := Λ) n s)
        else 0 := by
  let P : SplitCurrent (V := V) (Λ := Λ) n → Prop :=
    fun s => sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A
  have hdecomp :
      Fintype.card (AssignSources (V := V) (Λ := Λ) n A) =
        ∑ s : {s : SplitCurrent (V := V) (Λ := Λ) n // P s},
          Fintype.card (EdgeAssignSplitFiber (V := V) (Λ := Λ) n s.1) := by
    calc
      Fintype.card (AssignSources (V := V) (Λ := Λ) n A)
          = Fintype.card ((s : {s : SplitCurrent (V := V) (Λ := Λ) n // P s}) ×
              EdgeAssignSplitFiber (V := V) (Λ := Λ) n s.1) := by
              simpa [P] using
                (Fintype.card_congr (assignSourcesEquivSigma (V := V) (Λ := Λ) (n := n) A))
      _ = ∑ s : {s : SplitCurrent (V := V) (Λ := Λ) n // P s},
            Fintype.card (EdgeAssignSplitFiber (V := V) (Λ := Λ) n s.1) := by
            simp
  have hsum :
      (∑ s : {s : SplitCurrent (V := V) (Λ := Λ) n // P s},
          Fintype.card (EdgeAssignSplitFiber (V := V) (Λ := Λ) n s.1))
        =
        ∑ s : SplitCurrent (V := V) (Λ := Λ) n,
          if P s then Fintype.card (EdgeAssignSplitFiber (V := V) (Λ := Λ) n s) else 0 := by
    simpa [P] using
      (sum_subtype_eq_sum_if (α := SplitCurrent (V := V) (Λ := Λ) n) (M := ℕ) (P := P)
        (f := fun s => Fintype.card (EdgeAssignSplitFiber (V := V) (Λ := Λ) n s)))
  simpa [P] using hdecomp.trans hsum

/-! ## Switching lemma: reindexing over a fixed total current -/

lemma hasSubCurrent_of_exists_edgeAssign_sources (n : Current (V := V) Λ) (B : Finset (↥Λ)) :
    (∃ M : EdgeAssign (V := V) (Λ := Λ) n,
        sources (V := V) (currentOfEdgeAssign (V := V) (Λ := Λ) n M) = B) →
      HasSubCurrent (V := V) (Λ := Λ) n B := by
  rintro ⟨M, hM⟩
  refine ⟨currentOfEdgeAssign (V := V) (Λ := Λ) n M, currentOfEdgeAssign_le (V := V) (Λ := Λ) (n := n) M, hM⟩

lemma hasSubCurrent_iff_exists_edgeAssign_sources (n : Current (V := V) Λ) (B : Finset (↥Λ)) :
    HasSubCurrent (V := V) (Λ := Λ) n B ↔
      ∃ M : EdgeAssign (V := V) (Λ := Λ) n,
        sources (V := V) (currentOfEdgeAssign (V := V) (Λ := Λ) n M) = B := by
  constructor
  · exact exists_edgeAssign_sources_of_hasSubCurrent (V := V) (Λ := Λ) (n := n) (B := B)
  · exact hasSubCurrent_of_exists_edgeAssign_sources (V := V) (Λ := Λ) (n := n) (B := B)

/-- Pairs of currents whose sum is a fixed total current `n`. -/
abbrev AddFiber (n : Current (V := V) Λ) : Type u :=
  {p : Current (V := V) Λ × Current (V := V) Λ // p.1 + p.2 = n}

/--
Equivalence between split parameters `s : SplitCurrent n` and pairs `(n₁,n₂)` with `n₁+n₂=n`.
-/
noncomputable def splitCurrentEquivAddFiber (n : Current (V := V) Λ) :
    SplitCurrent (V := V) (Λ := Λ) n ≃ AddFiber (V := V) (Λ := Λ) n := by
  refine
    { toFun := fun s =>
        ⟨⟨splitCurrentToCurrent (V := V) (Λ := Λ) n s,
            splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s⟩,
          splitCurrent_add (V := V) (Λ := Λ) n s⟩
      invFun := fun p =>
        let n1 : Current (V := V) Λ := p.1.1
        let n2 : Current (V := V) Λ := p.1.2
        fun e =>
          ⟨n1 e,
            Nat.lt_succ_of_le
              (Nat.le.intro (k := n2 e) (by
                have h := congrArg (fun m : Current (V := V) Λ => m e) p.2
                simpa using h))⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro s
    funext e
    apply Fin.ext
    rfl
  · intro p
    apply Subtype.ext
    ext e
    · rfl
    · have h := congrArg (fun m : Current (V := V) Λ => m e) p.2
      have h' : p.1.1 e + p.1.2 e = n e := by
        simpa using h
      have hn : n e = p.1.1 e + p.1.2 e := h'.symm
      simp [splitCurrentToCurrentCompl, hn]

/-! ## Summability of the absolute current weights -/

lemma summable_norm_weightReal (β : ℝ) (J : Edge (V := V) Λ → ℝ) :
    Summable (fun n : Current (V := V) Λ => ‖weightReal (V := V) (Λ := Λ) β J n‖) := by
  let f : Edge (V := V) Λ → ℕ → ℝ := fun e k => (β * J e) ^ k / (k.factorial : ℝ)
  have hf : ∀ e, Summable fun k : ℕ => ‖f e k‖ := by
    intro e
    simpa [f] using summable_norm_pow_div_factorial (x := β * J e)
  have hsum : Summable (fun n : Current (V := V) Λ => ‖currTerm (E := Edge (V := V) Λ) f n‖) :=
    (tsum_pi_currTerm_eq_prod_tsum (E := Edge (V := V) Λ) f hf).1
  refine Summable.congr hsum ?_
  intro n
  simp [currTerm, weightReal, f]

/-! ## Per-total-current switching identity (combinatorial core) -/

lemma hasSubCurrent_of_assignSources
    (n : Current (V := V) Λ) (A B : Finset (↥Λ)) (hn : sources (V := V) n = symmDiff A B) :
    AssignSources (V := V) (Λ := Λ) n A → HasSubCurrent (V := V) (Λ := Λ) n B := by
  intro S
  let n1 : Current (V := V) Λ :=
    currentOfEdgeAssign (V := V) (Λ := Λ) n S.1
  let n2 : Current (V := V) Λ :=
    currentOfEdgeAssignCompl (V := V) (Λ := Λ) n S.1
  have hsum : n1 + n2 = n := by
    simpa [n1, n2] using
      (currentOfEdgeAssign_add_currentOfEdgeAssignCompl (V := V) (Λ := Λ) (n := n) S.1)
  have hadd :
      sources (V := V) n = symmDiff (sources (V := V) n1) (sources (V := V) n2) := by
    simpa [hsum] using (sources_add (V := V) (Λ := Λ) (n1 := n1) (n2 := n2))
  have hsrc1 : sources (V := V) n1 = A := by
    simpa [n1] using S.2
  have hsolve :
      symmDiff (sources (V := V) n1) (sources (V := V) n) = sources (V := V) n2 := by
    have := congrArg (fun t => symmDiff (sources (V := V) n1) t) hadd
    simpa [symmDiff_symmDiff_cancel_left] using this
  have hsrc2 : sources (V := V) n2 = B := by
    calc
      sources (V := V) n2
          = symmDiff (sources (V := V) n1) (sources (V := V) n) := by
              simpa using hsolve.symm
      _ = symmDiff A (symmDiff A B) := by
              simp [hsrc1, hn]
      _ = B := by
              simp
  have hle : CurrentLE (V := V) n2 n := by
    intro e
    simp [n2, currentOfEdgeAssignCompl]
  exact ⟨n2, hle, hsrc2⟩

lemma card_assignSources_eq_of_hasSubCurrent
    (n : Current (V := V) Λ) (A B : Finset (↥Λ)) (hsub : HasSubCurrent (V := V) (Λ := Λ) n B) :
    (Fintype.card (AssignSources (V := V) (Λ := Λ) n A) : ℝ) =
      (Fintype.card (AssignSources (V := V) (Λ := Λ) n (symmDiff A B)) : ℝ) := by
  rcases (exists_edgeAssign_sources_of_hasSubCurrent (V := V) (Λ := Λ) (n := n) (B := B) hsub) with ⟨M, hM⟩
  have hcard :
      Fintype.card (AssignSources (V := V) (Λ := Λ) n (symmDiff A B)) =
        Fintype.card (AssignSources (V := V) (Λ := Λ) n A) := by
    simpa [AssignSources] using
      (Fintype.card_congr
        (toggleEdgeAssignEquiv_sources (V := V) (Λ := Λ) (n := n) (A := A) (B := B) (M := M) hM))
  exact_mod_cast hcard.symm

lemma card_assignSources_eq_zero_of_not_hasSubCurrent
    (n : Current (V := V) Λ) (A B : Finset (↥Λ)) (hn : sources (V := V) n = symmDiff A B)
    (hsub : ¬ HasSubCurrent (V := V) (Λ := Λ) n B) :
    (Fintype.card (AssignSources (V := V) (Λ := Λ) n A) : ℝ) = 0 := by
  have hempty : IsEmpty (AssignSources (V := V) (Λ := Λ) n A) := by
    refine ⟨fun S => hsub (hasSubCurrent_of_assignSources (V := V) (Λ := Λ) (n := n) (A := A) (B := B) hn S)⟩
  have : Fintype.card (AssignSources (V := V) (Λ := Λ) n A) = 0 := by
    letI : IsEmpty (AssignSources (V := V) (Λ := Λ) n A) := hempty
    exact Fintype.card_eq_zero
  exact_mod_cast this

lemma sum_choose_eq_card_assignSources (n : Current (V := V) Λ) (A : Finset (↥Λ)) :
    (∑ s : SplitCurrent (V := V) (Λ := Λ) n,
        if sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A then
          (∏ e : Edge (V := V) Λ,
              ((n e).choose ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e) : ℝ))
        else 0)
      =
      (Fintype.card (AssignSources (V := V) (Λ := Λ) n A) : ℝ) := by
  have hcard :
      (Fintype.card (AssignSources (V := V) (Λ := Λ) n A) : ℝ)
        =
        ∑ s : SplitCurrent (V := V) (Λ := Λ) n,
          if sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A then
            (Fintype.card (EdgeAssignSplitFiber (V := V) (Λ := Λ) n s) : ℝ)
          else 0 := by
    have h := card_assignSources (V := V) (Λ := Λ) n A
    have h' :
        (Fintype.card (AssignSources (V := V) (Λ := Λ) n A) : ℝ)
          =
          (∑ s : SplitCurrent (V := V) (Λ := Λ) n,
              if sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A then
                Fintype.card (EdgeAssignSplitFiber (V := V) (Λ := Λ) n s)
              else 0 : ℕ) := by
      exact_mod_cast h
    simpa using h'
  have hfiber :
      ∀ s : SplitCurrent (V := V) (Λ := Λ) n,
        (Fintype.card (EdgeAssignSplitFiber (V := V) (Λ := Λ) n s) : ℝ)
          =
          ∏ e : Edge (V := V) Λ,
            ((n e).choose ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e) : ℝ) := by
    intro s
    have h := card_edgeAssignSplitFiber (V := V) (Λ := Λ) n s
    have h' :
        (Fintype.card (EdgeAssignSplitFiber (V := V) (Λ := Λ) n s) : ℝ)
          =
          (∏ e : Edge (V := V) Λ,
              (n e).choose ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e) : ℕ) := by
      exact_mod_cast h
    simpa using h'
  have hsum :
      (∑ s : SplitCurrent (V := V) (Λ := Λ) n,
          if sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A then
            (∏ e : Edge (V := V) Λ,
                ((n e).choose ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e) : ℝ))
          else 0)
        =
        ∑ s : SplitCurrent (V := V) (Λ := Λ) n,
          if sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A then
            (Fintype.card (EdgeAssignSplitFiber (V := V) (Λ := Λ) n s) : ℝ)
          else 0 := by
    refine Fintype.sum_congr _ _ ?_
    intro s
    by_cases hs :
        sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A
    · simp [hs, hfiber (s := s)]
    · simp [hs]
  simpa [hsum] using hcard.symm

lemma sum_choose_sources_eq_card_assignSources
    (n : Current (V := V) Λ) (A B : Finset (↥Λ)) :
    (∑ s : SplitCurrent (V := V) (Λ := Λ) n,
        if sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A ∧
            sources (V := V) (splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s) = B then
          (∏ e : Edge (V := V) Λ,
              ((n e).choose ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e) : ℝ))
        else 0)
      =
      if sources (V := V) n = symmDiff A B then
        (Fintype.card (AssignSources (V := V) (Λ := Λ) n A) : ℝ)
      else 0 := by
  by_cases hn : sources (V := V) n = symmDiff A B
  · have hforce :
        ∀ s : SplitCurrent (V := V) (Λ := Λ) n,
          sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A →
            sources (V := V) (splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s) = B := by
      intro s hA
      let n1 : Current (V := V) Λ := splitCurrentToCurrent (V := V) (Λ := Λ) n s
      let n2 : Current (V := V) Λ := splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s
      have hsum : n1 + n2 = n := by
        simpa [n1, n2] using (splitCurrent_add (V := V) (Λ := Λ) n s)
      have hadd :
          sources (V := V) n = symmDiff (sources (V := V) n1) (sources (V := V) n2) := by
        simpa [hsum] using (sources_add (V := V) (Λ := Λ) (n1 := n1) (n2 := n2))
      have hsolve :
          symmDiff (sources (V := V) n1) (sources (V := V) n) = sources (V := V) n2 := by
        have := congrArg (fun t => symmDiff (sources (V := V) n1) t) hadd
        simpa [symmDiff_symmDiff_cancel_left] using this
      calc
        sources (V := V) n2
            = symmDiff (sources (V := V) n1) (sources (V := V) n) := by
                simpa using hsolve.symm
        _ = symmDiff A (symmDiff A B) := by
                simp [n1, hA, hn]
        _ = B := by
                simp
    have hterm :
        ∀ s : SplitCurrent (V := V) (Λ := Λ) n,
          (if sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A ∧
                sources (V := V) (splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s) = B then
              (∏ e : Edge (V := V) Λ,
                  ((n e).choose ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e) : ℝ))
            else 0)
            =
            (if sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A then
              (∏ e : Edge (V := V) Λ,
                  ((n e).choose ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e) : ℝ))
            else 0) := by
      intro s
      by_cases hA :
          sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A
      · have hB := hforce (s := s) hA
        simp [hA, hB]
      · simp [hA]
    have hsum :
        (∑ s : SplitCurrent (V := V) (Λ := Λ) n,
            if sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A ∧
                  sources (V := V) (splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s) = B then
                (∏ e : Edge (V := V) Λ,
                    ((n e).choose ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e) : ℝ))
              else 0)
          =
          ∑ s : SplitCurrent (V := V) (Λ := Λ) n,
            if sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A then
              (∏ e : Edge (V := V) Λ,
                  ((n e).choose ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e) : ℝ))
            else 0 := by
      exact Fintype.sum_congr _ _ hterm
    simp [hn, hsum, sum_choose_eq_card_assignSources (V := V) (Λ := Λ) (n := n) (A := A)]
  · have hz :
        (∑ s : SplitCurrent (V := V) (Λ := Λ) n,
            if sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A ∧
                  sources (V := V) (splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s) = B then
                (∏ e : Edge (V := V) Λ,
                    ((n e).choose ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e) : ℝ))
              else 0)
          = 0 := by
      refine Fintype.sum_eq_zero _ ?_
      intro s
      by_cases hAB :
          sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A ∧
            sources (V := V) (splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s) = B
      · let n1 : Current (V := V) Λ := splitCurrentToCurrent (V := V) (Λ := Λ) n s
        let n2 : Current (V := V) Λ := splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s
        have hsum : n1 + n2 = n := by
          simpa [n1, n2] using (splitCurrent_add (V := V) (Λ := Λ) n s)
        have hadd :
            sources (V := V) n = symmDiff (sources (V := V) n1) (sources (V := V) n2) := by
          simpa [hsum] using (sources_add (V := V) (Λ := Λ) (n1 := n1) (n2 := n2))
        have : sources (V := V) n = symmDiff A B := by
          simpa [n1, n2, hAB.1, hAB.2] using hadd
        exact (hn this).elim
      · simp [hAB]
    simp [hn, hz]

lemma sum_choose_sources_symmDiff_empty_eq_card_assignSources
    (n : Current (V := V) Λ) (A B : Finset (↥Λ)) :
    (∑ s : SplitCurrent (V := V) (Λ := Λ) n,
        if sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = symmDiff A B ∧
            sources (V := V) (splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s) = (∅ : Finset (↥Λ)) then
          (∏ e : Edge (V := V) Λ,
              ((n e).choose ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e) : ℝ))
        else 0)
      =
      if sources (V := V) n = symmDiff A B then
        (Fintype.card (AssignSources (V := V) (Λ := Λ) n (symmDiff A B)) : ℝ)
      else 0 := by
  by_cases hn : sources (V := V) n = symmDiff A B
  · have hforce :
        ∀ s : SplitCurrent (V := V) (Λ := Λ) n,
          sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = symmDiff A B →
            sources (V := V) (splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s) = (∅ : Finset (↥Λ)) := by
      intro s hsrc
      let n1 : Current (V := V) Λ := splitCurrentToCurrent (V := V) (Λ := Λ) n s
      let n2 : Current (V := V) Λ := splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s
      have hsum : n1 + n2 = n := by
        simpa [n1, n2] using (splitCurrent_add (V := V) (Λ := Λ) n s)
      have hadd :
          sources (V := V) n = symmDiff (sources (V := V) n1) (sources (V := V) n2) := by
        simpa [hsum] using (sources_add (V := V) (Λ := Λ) (n1 := n1) (n2 := n2))
      have hEq : symmDiff (sources (V := V) n1) (sources (V := V) n2) = sources (V := V) n1 := by
        simpa [n1, hn, hsrc] using hadd.symm
      have hb : sources (V := V) n2 = (⊥ : Finset (↥Λ)) := (symmDiff_eq_left).1 hEq
      simpa using hb
    have hterm :
        ∀ s : SplitCurrent (V := V) (Λ := Λ) n,
          (if sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = symmDiff A B ∧
                sources (V := V) (splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s) = (∅ : Finset (↥Λ)) then
              (∏ e : Edge (V := V) Λ,
                  ((n e).choose ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e) : ℝ))
            else 0)
            =
            (if sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = symmDiff A B then
              (∏ e : Edge (V := V) Λ,
                  ((n e).choose ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e) : ℝ))
            else 0) := by
      intro s
      by_cases hsrc :
          sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = symmDiff A B
      · have hemp := hforce (s := s) hsrc
        simp [hsrc, hemp]
      · simp [hsrc]
    have hsum :
        (∑ s : SplitCurrent (V := V) (Λ := Λ) n,
            if sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = symmDiff A B ∧
                  sources (V := V) (splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s) = (∅ : Finset (↥Λ)) then
                (∏ e : Edge (V := V) Λ,
                    ((n e).choose ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e) : ℝ))
              else 0)
          =
          ∑ s : SplitCurrent (V := V) (Λ := Λ) n,
            if sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = symmDiff A B then
              (∏ e : Edge (V := V) Λ,
                  ((n e).choose ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e) : ℝ))
            else 0 := by
      exact Fintype.sum_congr _ _ hterm
    simp [hn, hsum, sum_choose_eq_card_assignSources (V := V) (Λ := Λ) (n := n) (A := symmDiff A B)]
  · have hz :
        (∑ s : SplitCurrent (V := V) (Λ := Λ) n,
            if sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = symmDiff A B ∧
                  sources (V := V) (splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s) = (∅ : Finset (↥Λ)) then
                (∏ e : Edge (V := V) Λ,
                    ((n e).choose ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e) : ℝ))
              else 0)
          = 0 := by
      refine Fintype.sum_eq_zero _ ?_
      intro s
      by_cases hAB :
          sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = symmDiff A B ∧
            sources (V := V) (splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s) = (∅ : Finset (↥Λ))
      · let n1 : Current (V := V) Λ := splitCurrentToCurrent (V := V) (Λ := Λ) n s
        let n2 : Current (V := V) Λ := splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s
        have hsum : n1 + n2 = n := by
          simpa [n1, n2] using (splitCurrent_add (V := V) (Λ := Λ) n s)
        have hadd :
            sources (V := V) n = symmDiff (sources (V := V) n1) (sources (V := V) n2) := by
          simpa [hsum] using (sources_add (V := V) (Λ := Λ) (n1 := n1) (n2 := n2))
        have h' : sources (V := V) n = symmDiff (symmDiff A B) (∅ : Finset (↥Λ)) := by
          simpa [n1, n2, hAB.1, hAB.2] using hadd
        have hbot : symmDiff (symmDiff A B) (∅ : Finset (↥Λ)) = symmDiff A B := by simp
        have : sources (V := V) n = symmDiff A B := by
          simpa [hbot] using h'
        exact (hn this).elim
      · simp [hAB]
    simp [hn, hz]

/-! ## Fiberwise decomposition of `tsum` over total current -/

omit [DecidableEq V] in
lemma tsum_by_totalCurrent
    (f : (Current (V := V) Λ × Current (V := V) Λ) → ℝ) (hf : Summable f) :
    (∑' p, f p)
      =
      ∑' n : Current (V := V) Λ,
        ∑' p : AddFiber (V := V) (Λ := Λ) n, f p.1 := by
  let g :
      (Current (V := V) Λ × Current (V := V) Λ) → Current (V := V) Λ := fun p => p.1 + p.2
  have ha : HasSum f (∑' p, f p) := hf.hasSum
  have ha' :
      HasSum
        (fun n : Current (V := V) Λ =>
          ∑' p : {p : (Current (V := V) Λ × Current (V := V) Λ) // g p = n}, f p.1)
        (∑' p, f p) :=
    ha.tsum_fiberwise g
  have ha'' :
      HasSum
        (fun n : Current (V := V) Λ =>
          ∑' p : AddFiber (V := V) (Λ := Λ) n, f p.1)
        (∑' p, f p) := by
    simpa [g, AddFiber] using ha'
  exact ha''.tsum_eq.symm

lemma tsum_addFiber_eq_sum_splitCurrent
    (n : Current (V := V) Λ) (g : (Current (V := V) Λ × Current (V := V) Λ) → ℝ) :
    (∑' p : AddFiber (V := V) (Λ := Λ) n, g p.1)
      =
      ∑ s : SplitCurrent (V := V) (Λ := Λ) n,
        g ⟨splitCurrentToCurrent (V := V) (Λ := Λ) n s,
          splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s⟩ := by
  have :=
    (Equiv.tsum_eq (splitCurrentEquivAddFiber (V := V) (Λ := Λ) n) (fun p => g p.1))
  simpa [tsum_fintype, splitCurrentEquivAddFiber] using this.symm

/-! ## Switching lemma (paper Lemma 1.5), as an identity of absolutely convergent series -/

lemma summable_norm_weightReal_mul_norm_weightReal (β : ℝ) (J : Edge (V := V) Λ → ℝ) :
    Summable (fun p : Current (V := V) Λ × Current (V := V) Λ =>
      ‖weightReal (V := V) (Λ := Λ) β J p.1‖ * ‖weightReal (V := V) (Λ := Λ) β J p.2‖) := by
  let w : Current (V := V) Λ → ℝ := weightReal (V := V) (Λ := Λ) β J
  have hs : Summable fun n : Current (V := V) Λ => ‖w n‖ := summable_norm_weightReal (V := V) (Λ := Λ) (β := β) J
  have hnonneg : 0 ≤ (fun n : Current (V := V) Λ => ‖w n‖) := by
    intro n
    exact norm_nonneg (w n)
  simpa [w] using (Summable.mul_of_nonneg hs hs hnonneg hnonneg)

/-! ### Summability helpers for switching-series -/

lemma nonneg_const_of_norm_le {α : Type*} [Inhabited α]
    (F : α → ℝ) (C : ℝ) (hF : ∀ a, ‖F a‖ ≤ C) : 0 ≤ C := by
  have h := hF default
  exact (norm_nonneg (F default)).trans h

lemma norm_F_mul_weightReal_mul_weightReal_le (β : ℝ) (J : Edge (V := V) Λ → ℝ)
    (F : Current (V := V) Λ → ℝ) (C : ℝ) (hF : ∀ n, ‖F n‖ ≤ C) :
    ∀ p : Current (V := V) Λ × Current (V := V) Λ,
      ‖F (p.1 + p.2) *
            weightReal (V := V) (Λ := Λ) β J p.1 *
          weightReal (V := V) (Λ := Λ) β J p.2‖
        ≤
        C *
          (‖weightReal (V := V) (Λ := Λ) β J p.1‖ *
            ‖weightReal (V := V) (Λ := Λ) β J p.2‖) := by
  intro p
  have hFn : ‖F (p.1 + p.2)‖ ≤ C := hF (p.1 + p.2)
  have hmul₁ :
      ‖F (p.1 + p.2) *
            weightReal (V := V) (Λ := Λ) β J p.1 *
          weightReal (V := V) (Λ := Λ) β J p.2‖
        ≤
        ‖F (p.1 + p.2) * weightReal (V := V) (Λ := Λ) β J p.1‖ *
          ‖weightReal (V := V) (Λ := Λ) β J p.2‖ :=
    norm_mul_le (F (p.1 + p.2) * weightReal (V := V) (Λ := Λ) β J p.1)
      (weightReal (V := V) (Λ := Λ) β J p.2)
  have hmul₂ :
      ‖F (p.1 + p.2) * weightReal (V := V) (Λ := Λ) β J p.1‖
        ≤
        ‖F (p.1 + p.2)‖ * ‖weightReal (V := V) (Λ := Λ) β J p.1‖ :=
    norm_mul_le (F (p.1 + p.2)) (weightReal (V := V) (Λ := Λ) β J p.1)
  have hmul₃ :
      ‖F (p.1 + p.2) * weightReal (V := V) (Λ := Λ) β J p.1‖ *
          ‖weightReal (V := V) (Λ := Λ) β J p.2‖
        ≤
        (‖F (p.1 + p.2)‖ * ‖weightReal (V := V) (Λ := Λ) β J p.1‖) *
          ‖weightReal (V := V) (Λ := Λ) β J p.2‖ :=
    mul_le_mul_of_nonneg_right hmul₂ (norm_nonneg _)
  have hmul :
      ‖F (p.1 + p.2) *
            weightReal (V := V) (Λ := Λ) β J p.1 *
          weightReal (V := V) (Λ := Λ) β J p.2‖
        ≤
        ‖F (p.1 + p.2)‖ *
          (‖weightReal (V := V) (Λ := Λ) β J p.1‖ *
            ‖weightReal (V := V) (Λ := Λ) β J p.2‖) := by
    have := (le_trans hmul₁ hmul₃)
    simp [mul_assoc]
  have hnonneg :
      0 ≤
        ‖weightReal (V := V) (Λ := Λ) β J p.1‖ *
          ‖weightReal (V := V) (Λ := Λ) β J p.2‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  exact hmul.trans (mul_le_mul_of_nonneg_right hFn hnonneg)

lemma summable_of_norm_le_mul_weightReal (β : ℝ) (J : Edge (V := V) Λ → ℝ) (C : ℝ)
    (f : (Current (V := V) Λ × Current (V := V) Λ) → ℝ)
    (hf :
      ∀ p : Current (V := V) Λ × Current (V := V) Λ,
        ‖f p‖ ≤
          C *
            (‖weightReal (V := V) (Λ := Λ) β J p.1‖ *
              ‖weightReal (V := V) (Λ := Λ) β J p.2‖)) :
    Summable f := by
  have hs_prod :
      Summable (fun p : Current (V := V) Λ × Current (V := V) Λ =>
        ‖weightReal (V := V) (Λ := Λ) β J p.1‖ *
          ‖weightReal (V := V) (Λ := Λ) β J p.2‖) := by
    simpa using (summable_norm_weightReal_mul_norm_weightReal (V := V) (Λ := Λ) (β := β) J)
  have hs_bound :
      Summable (fun p : Current (V := V) Λ × Current (V := V) Λ =>
        C *
          (‖weightReal (V := V) (Λ := Λ) β J p.1‖ *
            ‖weightReal (V := V) (Λ := Λ) β J p.2‖)) :=
    hs_prod.mul_left C
  exact Summable.of_norm_bounded hs_bound hf

lemma summable_switchingSummandL (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A B : Finset (↥Λ))
    (F : Current (V := V) Λ → ℝ) (C : ℝ) (hF : ∀ n, ‖F n‖ ≤ C) :
    Summable (fun p : Current (V := V) Λ × Current (V := V) Λ =>
      if sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B then
        F (p.1 + p.2) *
            weightReal (V := V) (Λ := Λ) β J p.1 *
          weightReal (V := V) (Λ := Λ) β J p.2
      else 0) := by
  classical
  have hC : 0 ≤ C := nonneg_const_of_norm_le (F := F) (C := C) hF
  refine
    summable_of_norm_le_mul_weightReal (V := V) (Λ := Λ) (β := β) (J := J) (C := C)
      (f := fun p =>
        if sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B then
          F (p.1 + p.2) *
              weightReal (V := V) (Λ := Λ) β J p.1 *
            weightReal (V := V) (Λ := Λ) β J p.2
        else 0) ?_
  intro p
  by_cases hsrc : sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B
  · simpa [hsrc] using
      (norm_F_mul_weightReal_mul_weightReal_le (V := V) (Λ := Λ) (β := β) (J := J) (F := F) (C := C) hF p)
  · have hnonneg :
        0 ≤
          C *
            (‖weightReal (V := V) (Λ := Λ) β J p.1‖ *
              ‖weightReal (V := V) (Λ := Λ) β J p.2‖) :=
      mul_nonneg hC (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    simpa [hsrc] using hnonneg

lemma summable_switchingSummandR (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A B : Finset (↥Λ))
    (F : Current (V := V) Λ → ℝ) (C : ℝ) (hF : ∀ n, ‖F n‖ ≤ C) :
    Summable (fun p : Current (V := V) Λ × Current (V := V) Λ =>
      if sources (V := V) p.1 = symmDiff A B ∧ sources (V := V) p.2 = (∅ : Finset (↥Λ)) then
        ({n : Current (V := V) Λ | HasSubCurrent (V := V) (Λ := Λ) n B}).indicator
          (fun n =>
            F n *
                weightReal (V := V) (Λ := Λ) β J p.1 *
              weightReal (V := V) (Λ := Λ) β J p.2)
          (p.1 + p.2)
      else 0) := by
  let SB : Set (Current (V := V) Λ) := {n | HasSubCurrent (V := V) (Λ := Λ) n B}
  have hC : 0 ≤ C := nonneg_const_of_norm_le (F := F) (C := C) hF
  refine
    summable_of_norm_le_mul_weightReal (V := V) (Λ := Λ) (β := β) (J := J) (C := C)
      (f := fun p =>
        if sources (V := V) p.1 = symmDiff A B ∧ sources (V := V) p.2 = (∅ : Finset (↥Λ)) then
          SB.indicator
            (fun n =>
              F n *
                  weightReal (V := V) (Λ := Λ) β J p.1 *
                weightReal (V := V) (Λ := Λ) β J p.2)
            (p.1 + p.2)
        else 0) ?_
  intro p
  by_cases hsrc :
      sources (V := V) p.1 = symmDiff A B ∧ sources (V := V) p.2 = (∅ : Finset (↥Λ))
  · have hind :
        ‖SB.indicator
              (fun n =>
                F n *
                    weightReal (V := V) (Λ := Λ) β J p.1 *
                  weightReal (V := V) (Λ := Λ) β J p.2)
              (p.1 + p.2)‖
          ≤
          ‖F (p.1 + p.2) *
                weightReal (V := V) (Λ := Λ) β J p.1 *
              weightReal (V := V) (Λ := Λ) β J p.2‖ := by
      simpa [SB] using
        (norm_indicator_le_norm_self (s := SB)
          (f := fun n =>
            F n *
                weightReal (V := V) (Λ := Λ) β J p.1 *
              weightReal (V := V) (Λ := Λ) β J p.2)
          (a := p.1 + p.2))
    have hcore :
        ‖F (p.1 + p.2) *
              weightReal (V := V) (Λ := Λ) β J p.1 *
            weightReal (V := V) (Λ := Λ) β J p.2‖
          ≤
          C *
            (‖weightReal (V := V) (Λ := Λ) β J p.1‖ *
              ‖weightReal (V := V) (Λ := Λ) β J p.2‖) :=
      norm_F_mul_weightReal_mul_weightReal_le (V := V) (Λ := Λ) (β := β) (J := J) (F := F) (C := C) hF p
    have : ‖SB.indicator
          (fun n =>
            F n *
                weightReal (V := V) (Λ := Λ) β J p.1 *
              weightReal (V := V) (Λ := Λ) β J p.2)
          (p.1 + p.2)‖
        ≤
        C *
          (‖weightReal (V := V) (Λ := Λ) β J p.1‖ *
            ‖weightReal (V := V) (Λ := Λ) β J p.2‖) :=
      hind.trans hcore
    simpa [hsrc, SB] using this
  · have hnonneg :
        0 ≤
          C *
            (‖weightReal (V := V) (Λ := Λ) β J p.1‖ *
              ‖weightReal (V := V) (Λ := Λ) β J p.2‖) :=
      mul_nonneg hC (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    simpa [hsrc] using hnonneg


/--
Switching lemma (Lemma 1.5 in `4D_triviality_June_2021_final.tex`) for the real current weights
`weightReal`.

We assume `F` is bounded in norm, so both sides are absolutely summable in `ℝ`.
-/
theorem switchingLemma
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A B : Finset (↥Λ))
    (F : Current (V := V) Λ → ℝ) (C : ℝ) (hF : ∀ n, ‖F n‖ ≤ C) :
    (∑' p : Current (V := V) Λ × Current (V := V) Λ,
        if sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B then
          F (p.1 + p.2) *
              weightReal (V := V) (Λ := Λ) β J p.1 *
            weightReal (V := V) (Λ := Λ) β J p.2
        else 0)
      =
      (∑' p : Current (V := V) Λ × Current (V := V) Λ,
        if sources (V := V) p.1 = symmDiff A B ∧ sources (V := V) p.2 = (∅ : Finset (↥Λ)) then
          ({n : Current (V := V) Λ | HasSubCurrent (V := V) (Λ := Λ) n B}).indicator
            (fun n =>
              F n *
                  weightReal (V := V) (Λ := Λ) β J p.1 *
                weightReal (V := V) (Λ := Λ) β J p.2)
            (p.1 + p.2)
        else 0) := by
  let w : Current (V := V) Λ → ℝ := weightReal (V := V) (Λ := Λ) β J
  let SB : Set (Current (V := V) Λ) := {n | HasSubCurrent (V := V) (Λ := Λ) n B}
  let fL : (Current (V := V) Λ × Current (V := V) Λ) → ℝ := fun p =>
    if sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B then
      F (p.1 + p.2) * w p.1 * w p.2
    else 0
  let fR : (Current (V := V) Λ × Current (V := V) Λ) → ℝ := fun p =>
    if sources (V := V) p.1 = symmDiff A B ∧ sources (V := V) p.2 = (∅ : Finset (↥Λ)) then
      SB.indicator (fun n => F n * w p.1 * w p.2) (p.1 + p.2)
    else 0
  have hsL : Summable fL := by
    simpa [fL, w] using
      (summable_switchingSummandL (V := V) (Λ := Λ) (β := β) (J := J) (A := A) (B := B)
        (F := F) (C := C) hF)
  have hsR : Summable fR := by
    simpa [fR, w, SB] using
      (summable_switchingSummandR (V := V) (Λ := Λ) (β := β) (J := J) (A := A) (B := B)
        (F := F) (C := C) hF)
  have hdecompL := tsum_by_totalCurrent (V := V) (Λ := Λ) (f := fL) hsL
  have hdecompR := tsum_by_totalCurrent (V := V) (Λ := Λ) (f := fR) hsR
  have hinter :
      ∀ n : Current (V := V) Λ,
        (∑' p : AddFiber (V := V) (Λ := Λ) n, fL p.1)
          =
          (∑' p : AddFiber (V := V) (Λ := Λ) n, fR p.1) := by
    intro n
    rw [tsum_addFiber_eq_sum_splitCurrent (V := V) (Λ := Λ) (n := n) (g := fL),
      tsum_addFiber_eq_sum_splitCurrent (V := V) (Λ := Λ) (n := n) (g := fR)]
    let c : ℝ := F n * w n
    have hL :
        (∑ s : SplitCurrent (V := V) (Λ := Λ) n,
            fL ⟨splitCurrentToCurrent (V := V) (Λ := Λ) n s,
              splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s⟩)
          =
          c *
            (if sources (V := V) n = symmDiff A B then
              (Fintype.card (AssignSources (V := V) (Λ := Λ) n A) : ℝ)
            else 0) := by
      have hterm :
          ∀ s : SplitCurrent (V := V) (Λ := Λ) n,
            fL ⟨splitCurrentToCurrent (V := V) (Λ := Λ) n s,
                splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s⟩
              =
              c *
                (if sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A ∧
                      sources (V := V)
                          (splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s) = B then
                    (∏ e : Edge (V := V) Λ,
                        ((Nat.choose (n e)
                            ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e)) : ℝ))
                  else 0) := by
        intro s
        let n1 : Current (V := V) Λ := splitCurrentToCurrent (V := V) (Λ := Λ) n s
        let n2 : Current (V := V) Λ := splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s
        have hsum : n1 + n2 = n := by
          simpa [n1, n2] using (splitCurrent_add (V := V) (Λ := Λ) n s)
        have hmul :
            w n1 * w n2
              =
              w n * (∏ e : Edge (V := V) Λ,
                ((Nat.choose (n e) (n1 e)) : ℝ)) := by
          simpa [w, n1, n2] using
            (weightReal_mul_eq_splitCurrent (V := V) (Λ := Λ) (β := β) (J := J) (n := n) s)
        by_cases hAB : sources (V := V) n1 = A ∧ sources (V := V) n2 = B
        · simp [fL, w, c, n1, n2, hAB, hsum, hmul, mul_assoc]
        · simp [fL, w, c, n1, n2, hAB]
      calc
        (∑ s : SplitCurrent (V := V) (Λ := Λ) n,
            fL ⟨splitCurrentToCurrent (V := V) (Λ := Λ) n s,
              splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s⟩)
            = ∑ s : SplitCurrent (V := V) (Λ := Λ) n,
                c *
                  (if sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A ∧
                        sources (V := V)
                            (splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s) = B then
                      (∏ e : Edge (V := V) Λ,
                          ((Nat.choose (n e)
                              ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e)) : ℝ))
                    else 0) := by
                exact Fintype.sum_congr _ _ hterm
        _ = c *
              (∑ s : SplitCurrent (V := V) (Λ := Λ) n,
                if sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A ∧
                    sources (V := V)
                        (splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s) = B then
                  (∏ e : Edge (V := V) Λ,
                      ((Nat.choose (n e)
                          ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e)) : ℝ))
                else 0) := by
              simpa using
                (Finset.mul_sum (s := (Finset.univ : Finset (SplitCurrent (V := V) (Λ := Λ) n)))
                    (f := fun s =>
                      if sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = A ∧
                          sources (V := V)
                              (splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s) = B then
                        (∏ e : Edge (V := V) Λ,
                            ((Nat.choose (n e)
                                ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e)) : ℝ))
                      else 0) c).symm
        _ = c *
              (if sources (V := V) n = symmDiff A B then
                (Fintype.card (AssignSources (V := V) (Λ := Λ) n A) : ℝ)
              else 0) := by
              simp [sum_choose_sources_eq_card_assignSources (V := V) (Λ := Λ) (n := n) (A := A) (B := B)]
    by_cases hsub : HasSubCurrent (V := V) (Λ := Λ) n B
    · have hR :
          (∑ s : SplitCurrent (V := V) (Λ := Λ) n,
              fR ⟨splitCurrentToCurrent (V := V) (Λ := Λ) n s,
                splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s⟩)
            =
            c *
              (if sources (V := V) n = symmDiff A B then
                (Fintype.card (AssignSources (V := V) (Λ := Λ) n (symmDiff A B)) : ℝ)
              else 0) := by
        have hterm :
            ∀ s : SplitCurrent (V := V) (Λ := Λ) n,
              fR ⟨splitCurrentToCurrent (V := V) (Λ := Λ) n s,
                  splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s⟩
                =
                c *
                  (if sources (V := V)
                        (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = symmDiff A B ∧
                      sources (V := V)
                          (splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s) = (∅ : Finset (↥Λ)) then
                      (∏ e : Edge (V := V) Λ,
                          ((Nat.choose (n e)
                              ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e)) : ℝ))
                    else 0) := by
          intro s
          let n1 : Current (V := V) Λ := splitCurrentToCurrent (V := V) (Λ := Λ) n s
          let n2 : Current (V := V) Λ := splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s
          have hsum : n1 + n2 = n := by
            simpa [n1, n2] using (splitCurrent_add (V := V) (Λ := Λ) n s)
          have hmul :
              w n1 * w n2
                =
                w n * (∏ e : Edge (V := V) Λ,
                  ((Nat.choose (n e) (n1 e)) : ℝ)) := by
            simpa [w, n1, n2] using
              (weightReal_mul_eq_splitCurrent (V := V) (Λ := Λ) (β := β) (J := J) (n := n) s)
          by_cases hsrc :
              sources (V := V) n1 = symmDiff A B ∧
                sources (V := V) n2 = (∅ : Finset (↥Λ))
          · have hmem : n ∈ SB := by simpa [SB] using hsub
            simp [fR, SB, w, c, n1, n2, hsrc, hsum, hmul, Set.indicator_of_mem hmem, mul_assoc]
          · simp [fR, w, c, n1, n2, hsrc]
        calc
          (∑ s : SplitCurrent (V := V) (Λ := Λ) n,
              fR ⟨splitCurrentToCurrent (V := V) (Λ := Λ) n s,
                splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s⟩)
              = ∑ s : SplitCurrent (V := V) (Λ := Λ) n,
                  c *
                    (if sources (V := V)
                          (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = symmDiff A B ∧
                        sources (V := V)
                            (splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s) = (∅ : Finset (↥Λ)) then
                        (∏ e : Edge (V := V) Λ,
                            ((Nat.choose (n e)
                                ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e)) : ℝ))
                      else 0) := by
                  exact Fintype.sum_congr _ _ hterm
          _ = c *
                (∑ s : SplitCurrent (V := V) (Λ := Λ) n,
                  if sources (V := V)
                        (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = symmDiff A B ∧
                      sources (V := V)
                          (splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s) = (∅ : Finset (↥Λ)) then
                    (∏ e : Edge (V := V) Λ,
                        ((Nat.choose (n e)
                            ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e)) : ℝ))
                  else 0) := by
                simpa using
                  (Finset.mul_sum (s := (Finset.univ : Finset (SplitCurrent (V := V) (Λ := Λ) n)))
                      (f := fun s =>
                        if sources (V := V)
                              (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = symmDiff A B ∧
                            sources (V := V)
                                (splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s) =
                                  (∅ : Finset (↥Λ)) then
                          (∏ e : Edge (V := V) Λ,
                              ((Nat.choose (n e)
                                  ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e)) : ℝ))
                        else 0) c).symm
          _ = c *
                (if sources (V := V) n = symmDiff A B then
                  (Fintype.card (AssignSources (V := V) (Λ := Λ) n (symmDiff A B)) : ℝ)
                else 0) := by
                simp [sum_choose_sources_symmDiff_empty_eq_card_assignSources (V := V) (Λ := Λ) (n := n)
                  (A := A) (B := B)]
      have hcard :
          (Fintype.card (AssignSources (V := V) (Λ := Λ) n A) : ℝ)
            =
            (Fintype.card (AssignSources (V := V) (Λ := Λ) n (symmDiff A B)) : ℝ) :=
        card_assignSources_eq_of_hasSubCurrent (V := V) (Λ := Λ) (n := n) (A := A) (B := B) hsub
      by_cases hsrc : sources (V := V) n = symmDiff A B
      · simp [hL, hR, hsrc, hcard]
      · simp [hL, hR, hsrc]
    · have hR0 :
          (∑ s : SplitCurrent (V := V) (Λ := Λ) n,
              fR ⟨splitCurrentToCurrent (V := V) (Λ := Λ) n s,
                splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s⟩)
            = 0 := by
        refine Fintype.sum_eq_zero _ ?_
        intro s
        have hnot :
            splitCurrentToCurrent (V := V) (Λ := Λ) n s +
                splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s ∉ SB := by
          simpa [SB, splitCurrent_add (V := V) (Λ := Λ) (n := n) s] using hsub
        by_cases hsrc :
            sources (V := V) (splitCurrentToCurrent (V := V) (Λ := Λ) n s) = symmDiff A B ∧
              sources (V := V)
                  (splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s) = (∅ : Finset (↥Λ))
        · simp [fR, hsrc, SB, Set.indicator_of_notMem hnot]
        · simp [fR, hsrc]
      by_cases hsrc : sources (V := V) n = symmDiff A B
      · have hcard0 :
            (Fintype.card (AssignSources (V := V) (Λ := Λ) n A) : ℝ) = 0 :=
          card_assignSources_eq_zero_of_not_hasSubCurrent (V := V) (Λ := Λ) (n := n)
            (A := A) (B := B) hsrc hsub
        simp [hL, hR0, hsrc, hcard0]
      · simp [hL, hR0, hsrc]
  calc
    (∑' p : Current (V := V) Λ × Current (V := V) Λ, fL p)
        = ∑' n : Current (V := V) Λ, ∑' p : AddFiber (V := V) (Λ := Λ) n, fL p.1 := hdecompL
    _ = ∑' n : Current (V := V) Λ, ∑' p : AddFiber (V := V) (Λ := Λ) n, fR p.1 := by
          refine tsum_congr ?_
          intro n
          simpa using hinter n
    _ = (∑' p : Current (V := V) Λ × Current (V := V) Λ, fR p) := hdecompR.symm

theorem switchingLemma_bounded
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A B : Finset (↥Λ))
    (F : Current (V := V) Λ → ℝ) (hF : ∃ C : ℝ, ∀ n, ‖F n‖ ≤ C) :
    (∑' p : Current (V := V) Λ × Current (V := V) Λ,
        if sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B then
          F (p.1 + p.2) *
              weightReal (V := V) (Λ := Λ) β J p.1 *
            weightReal (V := V) (Λ := Λ) β J p.2
        else 0)
      =
      (∑' p : Current (V := V) Λ × Current (V := V) Λ,
        if sources (V := V) p.1 = symmDiff A B ∧ sources (V := V) p.2 = (∅ : Finset (↥Λ)) then
          ({n : Current (V := V) Λ | HasSubCurrent (V := V) (Λ := Λ) n B}).indicator
            (fun n =>
              F n *
                  weightReal (V := V) (Λ := Λ) β J p.1 *
                weightReal (V := V) (Λ := Λ) β J p.2)
            (p.1 + p.2)
        else 0) := by
  rcases hF with ⟨C, hC⟩
  exact switchingLemma (V := V) (Λ := Λ) (β := β) (J := J) (A := A) (B := B) (F := F) (C := C) hC

/-! ## Switching lemma with `F ≡ 1` -/

theorem switchingLemma_one
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A B : Finset (↥Λ)) :
    (∑' p : Current (V := V) Λ × Current (V := V) Λ,
        if sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B then
          weightReal (V := V) (Λ := Λ) β J p.1 *
            weightReal (V := V) (Λ := Λ) β J p.2
        else 0)
      =
      (∑' p : Current (V := V) Λ × Current (V := V) Λ,
        if sources (V := V) p.1 = symmDiff A B ∧ sources (V := V) p.2 = (∅ : Finset (↥Λ)) then
          ({n : Current (V := V) Λ | HasSubCurrent (V := V) (Λ := Λ) n B}).indicator
            (fun _n =>
              weightReal (V := V) (Λ := Λ) β J p.1 *
                weightReal (V := V) (Λ := Λ) β J p.2)
            (p.1 + p.2)
        else 0) := by
  have hF : ∀ n : Current (V := V) Λ, ‖(1 : ℝ)‖ ≤ (1 : ℝ) := by
    intro _n
    simp
  simpa [mul_assoc] using
    (switchingLemma (V := V) (Λ := Λ) (β := β) (J := J) (A := A) (B := B)
      (F := fun _n : Current (V := V) Λ => (1 : ℝ)) (C := (1 : ℝ)) hF)

/-! ## Source-constrained sums as products of `ZReal` -/

lemma summable_norm_sources_weightReal (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A : Finset (↥Λ)) :
    Summable (fun n : Current (V := V) Λ =>
      ‖if sources (V := V) n = A then weightReal (V := V) (Λ := Λ) β J n else 0‖) := by
  have hs :
      Summable (fun n : Current (V := V) Λ => ‖weightReal (V := V) (Λ := Λ) β J n‖) :=
    summable_norm_weightReal (V := V) (Λ := Λ) (β := β) J
  refine Summable.of_nonneg_of_le (f := fun n => ‖weightReal (V := V) (Λ := Λ) β J n‖)
    (g := fun n => ‖if sources (V := V) n = A then weightReal (V := V) (Λ := Λ) β J n else 0‖)
    (fun _n => norm_nonneg _) ?_ hs
  intro n
  by_cases h : sources (V := V) n = A <;> simp [h]

lemma ZReal_mul_ZReal_eq_tsum_pair
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A B : Finset (↥Λ)) :
    ZReal (V := V) (Λ := Λ) β J A * ZReal (V := V) (Λ := Λ) β J B
      =
      (∑' p : Current (V := V) Λ × Current (V := V) Λ,
        if sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B then
          weightReal (V := V) (Λ := Λ) β J p.1 *
            weightReal (V := V) (Λ := Λ) β J p.2
        else 0) := by
  classical
  let f : Current (V := V) Λ → ℝ :=
    fun n => if sources (V := V) n = A then weightReal (V := V) (Λ := Λ) β J n else 0
  let g : Current (V := V) Λ → ℝ :=
    fun n => if sources (V := V) n = B then weightReal (V := V) (Λ := Λ) β J n else 0
  have hf :
      Summable (fun n : Current (V := V) Λ => ‖f n‖) := by
    simpa [f] using summable_norm_sources_weightReal (V := V) (Λ := Λ) (β := β) (J := J) (A := A)
  have hg :
      Summable (fun n : Current (V := V) Λ => ‖g n‖) := by
    simpa [g] using summable_norm_sources_weightReal (V := V) (Λ := Λ) (β := β) (J := J) (A := B)
  have hmul :
      ((∑' n : Current (V := V) Λ, f n) * (∑' n : Current (V := V) Λ, g n)) =
        ∑' p : Current (V := V) Λ × Current (V := V) Λ, f p.1 * g p.2 := by
    simpa using (tsum_mul_tsum_of_summable_norm (f := f) (g := g) hf hg)
  -- unfold `ZReal`, then rewrite the nested `if`s into a single conjunction
  have hmul' :
      ZReal (V := V) (Λ := Λ) β J A * ZReal (V := V) (Λ := Λ) β J B
        =
        ∑' p : Current (V := V) Λ × Current (V := V) Λ,
          if sources (V := V) p.2 = B then
            if sources (V := V) p.1 = A then
              weightReal (V := V) (Λ := Λ) β J p.1 *
                weightReal (V := V) (Λ := Λ) β J p.2
            else 0
          else 0 := by
    simpa [ZReal, f, g] using hmul
  refine hmul'.trans ?_
  refine tsum_congr ?_
  intro p
  by_cases h1 : sources (V := V) p.1 = A <;> by_cases h2 : sources (V := V) p.2 = B <;> simp [h1, h2]

theorem switchingLemma_ZReal_mul
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A B : Finset (↥Λ)) :
    ZReal (V := V) (Λ := Λ) β J A * ZReal (V := V) (Λ := Λ) β J B
      =
      (∑' p : Current (V := V) Λ × Current (V := V) Λ,
        if sources (V := V) p.1 = symmDiff A B ∧ sources (V := V) p.2 = (∅ : Finset (↥Λ)) then
          ({n : Current (V := V) Λ | HasSubCurrent (V := V) (Λ := Λ) n B}).indicator
            (fun _n =>
              weightReal (V := V) (Λ := Λ) β J p.1 *
                weightReal (V := V) (Λ := Λ) β J p.2)
            (p.1 + p.2)
        else 0) := by
  calc
    ZReal (V := V) (Λ := Λ) β J A * ZReal (V := V) (Λ := Λ) β J B
        =
        (∑' p : Current (V := V) Λ × Current (V := V) Λ,
          if sources (V := V) p.1 = A ∧ sources (V := V) p.2 = B then
            weightReal (V := V) (Λ := Λ) β J p.1 *
              weightReal (V := V) (Λ := Λ) β J p.2
          else 0) := ZReal_mul_ZReal_eq_tsum_pair (V := V) (Λ := Λ) (β := β) (J := J) (A := A) (B := B)
    _ = _ := switchingLemma_one (V := V) (Λ := Λ) (β := β) (J := J) (A := A) (B := B)


end RandomCurrent

end SpinGlass.Papers.Triviality4D
