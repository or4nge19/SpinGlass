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

/-! ## Counting edge assignments with prescribed multiplicities -/

abbrev EdgeAssignFiber (n n1 : Current (V := V) Λ) : Type u :=
  {S : EdgeAssign (V := V) (Λ := Λ) n // currentOfEdgeAssign (V := V) (Λ := Λ) n S = n1}

noncomputable def edgeAssignFiberEquiv
    (n n1 : Current (V := V) Λ) :
    EdgeAssignFiber (V := V) (Λ := Λ) n n1 ≃
      (∀ e : Edge (V := V) Λ, {s : Finset (Fin (n e)) // s.card = n1 e}) :=
by
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

noncomputable def canonEdgeSet (n k : ℕ) (hk : k ≤ n) : Finset (Fin n) :=
  (Finset.univ.image (Fin.castLE hk))

lemma card_canonEdgeSet (n k : ℕ) (hk : k ≤ n) :
    (canonEdgeSet n k hk).card = k := by
  simpa [canonEdgeSet] using
    (Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin k)))
      (Fin.castLE_injective hk))

noncomputable def canonEdgeAssign (n m : Current (V := V) Λ) (hm : CurrentLE (V := V) m n) :
    EdgeAssign (V := V) (Λ := Λ) n :=
  fun e => canonEdgeSet (n e) (m e) (hm e)

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

lemma currentOfEdgeAssign_add_currentOfEdgeAssignCompl (n : Current (V := V) Λ)
    (S : EdgeAssign (V := V) (Λ := Λ) n) :
    currentOfEdgeAssign (V := V) (Λ := Λ) n S + currentOfEdgeAssignCompl (V := V) (Λ := Λ) n S = n := by
  funext e
  have hle : (S e).card ≤ n e := by
    simpa using (Finset.card_le_univ (s := S e))
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

/-! ## Sources under current addition -/

lemma degree_add (n1 n2 : Current (V := V) Λ) (x : ↥Λ) :
    degree (V := V) (n1 + n2) x = degree (V := V) n1 x + degree (V := V) n2 x := by
  simp [degree]
  have hintegrand :
      (fun e : Edge (V := V) Λ => if x ∈ (e.1 : Sym2 (↥Λ)) then n1 e + n2 e else 0) =
        (fun e : Edge (V := V) Λ =>
          (if x ∈ (e.1 : Sym2 (↥Λ)) then n1 e else 0) +
            (if x ∈ (e.1 : Sym2 (↥Λ)) then n2 e else 0)) := by
    funext e
    by_cases hx : x ∈ (e.1 : Sym2 (↥Λ))
    · simp [hx]
    · simp [hx]
  simpa [hintegrand] using
    (Finset.sum_add_distrib (s := (Finset.univ : Finset (Edge (V := V) Λ)))
      (f := fun e : Edge (V := V) Λ => if x ∈ (e.1 : Sym2 (↥Λ)) then n1 e else 0)
      (g := fun e : Edge (V := V) Λ => if x ∈ (e.1 : Sym2 (↥Λ)) then n2 e else 0))

lemma sources_add (n1 n2 : Current (V := V) Λ) :
    sources (V := V) (n1 + n2) =
      symmDiff (sources (V := V) n1) (sources (V := V) n2) := by
  ext x
  simp [mem_sources_iff, IsSource, degree_add, Finset.mem_symmDiff]
  have hiff : ∀ p q : Prop, (p ↔ ¬ q) ↔ (p ∧ ¬ q) ∨ (q ∧ ¬ p) := by
    intro p q
    by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]
  have hadd :
      Odd (degree (V := V) n1 x + degree (V := V) n2 x) ↔
        (Odd (degree (V := V) n1 x) ↔ Even (degree (V := V) n2 x)) := by
    simpa using (Nat.odd_add (m := degree (V := V) n1 x) (n := degree (V := V) n2 x))
  have : (Odd (degree (V := V) n1 x) ↔ Even (degree (V := V) n2 x)) ↔
      (Odd (degree (V := V) n1 x) ∧ Even (degree (V := V) n2 x)) ∨
        (Odd (degree (V := V) n2 x) ∧ Even (degree (V := V) n1 x)) := by
    simpa [Nat.not_odd_iff_even, and_left_comm, and_assoc, and_comm] using
      (hiff (Odd (degree (V := V) n1 x)) (Odd (degree (V := V) n2 x)))
  exact hadd.trans this

/-! ## Finite splittings of a fixed total current -/

/--
For a fixed total current `n`, a `SplitCurrent n` is the choice of an integer `n₁(e) ∈ {0,…,n(e)}`
for every edge `e`. This parametrizes all current splittings `n = n₁ + n₂` by setting
`n₂(e) = n(e) - n₁(e)`.
-/
abbrev SplitCurrent (n : Current (V := V) Λ) : Type u :=
  ∀ e : Edge (V := V) Λ, Fin (n e + 1)

noncomputable def splitCurrentToCurrent (n : Current (V := V) Λ) (s : SplitCurrent (V := V) (Λ := Λ) n) :
    Current (V := V) Λ :=
  fun e => (s e).val

noncomputable def splitCurrentToCurrentCompl (n : Current (V := V) Λ) (s : SplitCurrent (V := V) (Λ := Λ) n) :
    Current (V := V) Λ :=
  fun e => n e - (s e).val

lemma splitCurrent_add (n : Current (V := V) Λ) (s : SplitCurrent (V := V) (Λ := Λ) n) :
    splitCurrentToCurrent (V := V) (Λ := Λ) n s +
        splitCurrentToCurrentCompl (V := V) (Λ := Λ) n s = n := by
  funext e
  have hle : (s e).val ≤ n e := Nat.le_of_lt_succ (s e).isLt
  simp [splitCurrentToCurrent, splitCurrentToCurrentCompl, Nat.add_sub_of_le hle]

noncomputable def edgeAssignToSplitCurrent (n : Current (V := V) Λ) :
    EdgeAssign (V := V) (Λ := Λ) n → SplitCurrent (V := V) (Λ := Λ) n :=
  fun S e =>
    ⟨(S e).card, Nat.lt_succ_of_le (by
      simpa using (Finset.card_le_univ (s := S e)))⟩

abbrev EdgeAssignSplitFiber (n : Current (V := V) Λ) (s : SplitCurrent (V := V) (Λ := Λ) n) : Type u :=
  {S : EdgeAssign (V := V) (Λ := Λ) n // edgeAssignToSplitCurrent (V := V) (Λ := Λ) n S = s}

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
  · simp [hx, card_symmDiff_add_two_inter (s := S e) (t := M e), add_assoc, add_left_comm, add_comm]
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
        sources (V := V) (currentOfEdgeAssign (V := V) (Λ := Λ) n S) = A} :=
by
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

lemma splitCurrentToCurrent_edgeAssignToSplitCurrent (n : Current (V := V) Λ)
    (S : EdgeAssign (V := V) (Λ := Λ) n) :
    splitCurrentToCurrent (V := V) (Λ := Λ) n (edgeAssignToSplitCurrent (V := V) (Λ := Λ) n S) =
      currentOfEdgeAssign (V := V) (Λ := Λ) n S := by
  funext e
  rfl

lemma splitCurrentToCurrentCompl_edgeAssignToSplitCurrent (n : Current (V := V) Λ)
    (S : EdgeAssign (V := V) (Λ := Λ) n) :
    splitCurrentToCurrentCompl (V := V) (Λ := Λ) n (edgeAssignToSplitCurrent (V := V) (Λ := Λ) n S) =
      currentOfEdgeAssignCompl (V := V) (Λ := Λ) n S := by
  funext e
  rfl

lemma card_edgeAssignSplitFiber (n : Current (V := V) Λ) (s : SplitCurrent (V := V) (Λ := Λ) n) :
    Fintype.card (EdgeAssignSplitFiber (V := V) (Λ := Λ) n s) =
      ∏ e : Edge (V := V) Λ, (n e).choose ((splitCurrentToCurrent (V := V) (Λ := Λ) n s) e) := by
  classical
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
A small bookkeeping lemma: summing over a subtype `{x // P x}` equals summing over all `x` with an
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
        EdgeAssignSplitFiber (V := V) (Λ := Λ) n s.1 :=
by
  classical
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
  classical
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
            simpa using
              (Fintype.card_sigma (ι := {s : SplitCurrent (V := V) (Λ := Λ) n // P s})
                (α := fun s => EdgeAssignSplitFiber (V := V) (Λ := Λ) n s.1))
  -- rewrite the sum over the subtype as a sum over all `s` with an indicator
  have hsum :
      (∑ s : {s : SplitCurrent (V := V) (Λ := Λ) n // P s},
          Fintype.card (EdgeAssignSplitFiber (V := V) (Λ := Λ) n s.1))
        =
        ∑ s : SplitCurrent (V := V) (Λ := Λ) n,
          if P s then Fintype.card (EdgeAssignSplitFiber (V := V) (Λ := Λ) n s) else 0 := by
    -- apply the general lemma with `f s = card (fiber s)`
    simpa [P] using
      (sum_subtype_eq_sum_if (α := SplitCurrent (V := V) (Λ := Λ) n) (M := ℕ) (P := P)
        (f := fun s => Fintype.card (EdgeAssignSplitFiber (V := V) (Λ := Λ) n s)))
  simpa [P] using hdecomp.trans hsum

end RandomCurrent

end SpinGlass.Papers.Triviality4D
