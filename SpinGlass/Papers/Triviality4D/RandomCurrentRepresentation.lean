import SpinGlass.Papers.Triviality4D.RandomCurrent
import SpinGlass.Defs
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

/-!
# Random current representation (finite volume): partition function and correlation expansion

This file proves the finite-volume random-current representation identities used in
`4D_triviality_June_2021_final.tex`, Section 1.5:

- expansion of the finite-volume Ising partition function into a sum over currents,
- expansion of spin correlations as ratios of source-constrained current sums.

The switching lemma is proved in a separate file.
-/

open scoped BigOperators Topology

namespace SpinGlass.Papers.Triviality4D

namespace RandomCurrent

universe u

/-! ## Algebraic tools: products of series and sums over Boolean functions -/

/-- Product term associated to `n : E → ℕ` for an edgewise weight family `f : E → ℕ → ℝ`. -/
noncomputable def currTerm {E : Type*} [Fintype E] (f : E → ℕ → ℝ) (n : E → ℕ) : ℝ :=
  ∏ e : E, f e (n e)

/-- Finite product of absolutely convergent series factorizes into a `tsum` over functions `E → ℕ`. -/
theorem tsum_pi_currTerm_eq_prod_tsum
    {E : Type*} [Fintype E]
    (f : E → ℕ → ℝ) (hf : ∀ e, Summable fun k : ℕ => ‖f e k‖) :
    (Summable (fun n : E → ℕ => ‖currTerm (E := E) f n‖)) ∧
      (∑' n : E → ℕ, currTerm (E := E) f n) = ∏ e : E, (∑' k : ℕ, f e k) := by
  refine (Fintype.induction_empty_option
    (P := fun E _ =>
      ∀ (f : E → ℕ → ℝ), (∀ e, Summable fun k : ℕ => ‖f e k‖) →
        (Summable (fun n : E → ℕ => ‖currTerm (E := E) f n‖)) ∧
          (∑' n : E → ℕ, currTerm (E := E) f n) = ∏ e : E, (∑' k : ℕ, f e k))
    (of_equiv := ?_) (h_empty := ?_) (h_option := ?_) E) f hf
  · intro α β hβ e hα f hf
    letI : Fintype α := Fintype.ofEquiv β e.symm
    let fα : α → ℕ → ℝ := fun a k => f (e a) k
    have hfα : ∀ a : α, Summable fun k : ℕ => ‖fα a k‖ := fun a => hf (e a)
    have h := hα fα hfα
    let ec : (α → ℕ) ≃ (β → ℕ) := Equiv.arrowCongr e (Equiv.refl ℕ)
    have hterm : ∀ n : α → ℕ, currTerm (E := β) f (ec n) = currTerm (E := α) fα n := by
      intro n
      have hreindex :
          (∏ a : α, f (e a) (n a)) = ∏ b : β, f b (n (e.symm b)) := by
        refine (Fintype.prod_equiv e
          (f := fun a : α => f (e a) (n a))
          (g := fun b : β => f b (n (e.symm b))) ?_)
        intro a
        simp
      simpa [currTerm, fα, ec] using hreindex.symm
    have hsum : Summable (fun nb : β → ℕ => ‖currTerm (E := β) f nb‖) := by
      have : Summable (fun n : α → ℕ => ‖currTerm (E := β) f (ec n)‖) := by
        refine Summable.congr h.1 ?_
        intro n
        have := congrArg (fun x : ℝ => ‖x‖) (hterm n)
        simpa using this.symm
      exact
        (Equiv.summable_iff (e := ec) (f := fun nb : β → ℕ => ‖currTerm (E := β) f nb‖)).1 this
    have htsum :
        (∑' nb : β → ℕ, currTerm (E := β) f nb) = ∑' n : α → ℕ, currTerm (E := α) fα n := by
      have :
          (∑' nb : β → ℕ, currTerm (E := β) f nb) = ∑' n : α → ℕ, currTerm (E := β) f (ec n) := by
        simpa using (Equiv.tsum_eq ec (fun nb : β → ℕ => currTerm (E := β) f nb)).symm
      calc
        (∑' nb : β → ℕ, currTerm (E := β) f nb)
            = ∑' n : α → ℕ, currTerm (E := β) f (ec n) := this
        _ = ∑' n : α → ℕ, currTerm (E := α) fα n := by
              refine tsum_congr ?_
              intro n
              simp [hterm n]
    have hprod : (∏ b : β, (∑' k : ℕ, f b k)) = ∏ a : α, (∑' k : ℕ, fα a k) := by
      have :=
        (Fintype.prod_equiv e
          (f := fun a : α => (∑' k : ℕ, fα a k))
          (g := fun b : β => (∑' k : ℕ, f b k))
          (by intro a; simp [fα]))
      simpa using this.symm
    refine ⟨hsum, ?_⟩
    calc
      (∑' nb : β → ℕ, currTerm (E := β) f nb)
          = ∑' n : α → ℕ, currTerm (E := α) fα n := htsum
      _ = ∏ a : α, (∑' k : ℕ, fα a k) := h.2
      _ = ∏ b : β, (∑' k : ℕ, f b k) := by simp [hprod]
  · intro f _hf
    have hsum : Summable (fun n : (PEmpty → ℕ) => ‖currTerm (E := PEmpty) f n‖) := by
      simpa using (Summable.of_finite (f := fun n : (PEmpty → ℕ) => ‖currTerm (E := PEmpty) f n‖))
    refine ⟨hsum, ?_⟩
    simp [currTerm]
  · intro α _ hα  f hf
    let fα : α → ℕ → ℝ := fun a k => f (some a) k
    have hfα : ∀ a : α, Summable fun k : ℕ => ‖fα a k‖ := fun a => hf (some a)
    have ih := hα fα hfα
    let rest : (α → ℕ) → ℝ := fun n => currTerm (E := α) fα n
    have hrest_summ : Summable (fun n : α → ℕ => ‖rest n‖) := ih.1
    have hrest_eq : (∑' n : α → ℕ, rest n) = ∏ a : α, (∑' k : ℕ, fα a k) := ih.2
    let ecur : (ℕ × (α → ℕ)) ≃ (Option α → ℕ) :=
      (Equiv.piOptionEquivProd (β := fun _ : Option α => ℕ)).symm
    have hsum : Summable (fun n : Option α → ℕ => ‖currTerm (E := Option α) f n‖) := by
      have : Summable (fun p : ℕ × (α → ℕ) => ‖currTerm (E := Option α) f (ecur p)‖) := by
        have hf0 : Summable (fun n0 : ℕ => ‖f none n0‖) := hf none
        have hsumR : Summable (fun p : ℕ × (α → ℕ) => ‖f none p.1‖ * ‖rest p.2‖) := by
          have hf0' : 0 ≤ fun n0 : ℕ => ‖f none n0‖ := fun _ => by simp
          have hrest' : 0 ≤ fun n' : α → ℕ => ‖rest n'‖ := fun _ => by simp
          simpa using
            (Summable.mul_of_nonneg (f := fun n0 : ℕ => ‖f none n0‖)
              (g := fun n' : α → ℕ => ‖rest n'‖) hf0 hrest_summ hf0' hrest')
        refine (hsumR.of_nonneg_of_le (fun _ => by simp) ?_)
        intro p
        have :
            ‖currTerm (E := Option α) f (ecur p)‖
              ≤ ‖f none p.1‖ * ‖rest p.2‖ := by
          simp [currTerm, rest, fα, ecur, Fintype.prod_option]
        simpa using this
      exact
        (Equiv.summable_iff (e := ecur)
          (f := fun n : Option α → ℕ => ‖currTerm (E := Option α) f n‖)).1 this
    have heq : (∑' n : Option α → ℕ, currTerm (E := Option α) f n)
        = ∏ o : Option α, (∑' k : ℕ, f o k) := by
      have htsum : (∑' n : Option α → ℕ, currTerm (E := Option α) f n)
            = ∑' p : ℕ × (α → ℕ), currTerm (E := Option α) f (ecur p) := by
        simpa using
          (Equiv.tsum_eq ecur (fun n : Option α → ℕ => currTerm (E := Option α) f n)).symm
      have hmul :
          (∑' n0 : ℕ, f none n0) * (∑' n' : α → ℕ, rest n')
            = ∑' p : ℕ × (α → ℕ), f none p.1 * rest p.2 := by
        have hf0 : Summable (fun n0 : ℕ => ‖f none n0‖) := hf none
        simpa using
          (tsum_mul_tsum_of_summable_norm (f := fun n0 : ℕ => f none n0)
            (g := fun n' : α → ℕ => rest n') hf0 hrest_summ)
      calc
        (∑' n : Option α → ℕ, currTerm (E := Option α) f n)
            = ∑' p : ℕ × (α → ℕ), currTerm (E := Option α) f (ecur p) := htsum
        _ = ∑' p : ℕ × (α → ℕ), f none p.1 * rest p.2 := by
              refine tsum_congr ?_
              intro p
              simp [currTerm, rest, fα, ecur, Fintype.prod_option]
        _ = (∑' n0 : ℕ, f none n0) * (∑' n' : α → ℕ, rest n') := by
              simp [hmul]
        _ = (∑' n0 : ℕ, f none n0) * (∏ a : α, (∑' k : ℕ, fα a k)) := by
              simp [hrest_eq]
        _ = ∏ o : Option α, (∑' k : ℕ, f o k) := by
              simp [fα, Fintype.prod_option]

    exact ⟨hsum, heq⟩


section BoolFunctionSum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (h : ι → Bool → ℝ)

/-- Finite sum over all functions `ι → Bool` factorizes into a product of single-site sums. -/
lemma sum_all_bool_functions_prod :
    (∑ σ : (ι → Bool), ∏ i : ι, h i (σ i)) = ∏ i : ι, (∑ b : Bool, h i b) := by
  have hR :
      (∏ i : ι, (∑ b : Bool, h i b))
        = ∏ i ∈ (Finset.univ : Finset ι), ∑ b ∈ (Finset.univ : Finset Bool), h i b := by
    simp
  let t : ι → Finset Bool := fun _ => (Finset.univ : Finset Bool)
  have hprod_sum :
      (∏ i ∈ (Finset.univ : Finset ι), ∑ b ∈ (Finset.univ : Finset Bool), h i b)
        = ∑ σ ∈ (Fintype.piFinset t), ∏ i : ι, h i (σ i) := by
    have hs :
        (∏ i ∈ (Finset.univ : Finset ι), ∑ b ∈ t i, h i b)
          = ∑ p ∈ (Finset.univ : Finset ι).pi t,
              ∏ x ∈ (Finset.univ : Finset ι).attach,
                h (↑x) (p (↑x) (by simp)) := by
      simpa [t, Finset.prod_attach] using
        (Finset.prod_sum (s := (Finset.univ : Finset ι)) (t := t) (f := fun i b => h i b))
    have hs' :
        (∑ p ∈ (Finset.univ : Finset ι).pi t,
            ∏ x ∈ (Finset.univ : Finset ι).attach,
              h (↑x) (p (↑x) (by simp)))
          = ∑ σ ∈ Fintype.piFinset t,
              ∏ x ∈ (Finset.univ : Finset ι).attach,
                h (↑x) ((fun a _ => σ a) (↑x) (by simpa using x.2)) := by
      simpa [t] using
        (Finset.sum_univ_pi (ι := ι) (β := ℝ) (t := t)
          (f := fun p =>
            ∏ x ∈ (Finset.univ : Finset ι).attach,
              h (↑x) (p (↑x) (by simp))))
    have hs'' :
        (∑ σ ∈ Fintype.piFinset t,
            ∏ x ∈ (Finset.univ : Finset ι).attach,
              h (↑x) ((fun a _ => σ a) (↑x) (by simpa using x.2)))
          = ∑ σ ∈ Fintype.piFinset t, ∏ i : ι, h i (σ i) := by
      simp
    calc
      (∏ i ∈ (Finset.univ : Finset ι), ∑ b ∈ (Finset.univ : Finset Bool), h i b)
          = ∑ p ∈ (Finset.univ : Finset ι).pi t,
              ∏ x ∈ (Finset.univ : Finset ι).attach,
                h (↑x) (p (↑x) (by simp)) := by
              simpa [t] using hs
      _ = ∑ σ ∈ Fintype.piFinset t,
              ∏ x ∈ (Finset.univ : Finset ι).attach,
                h (↑x) ((fun a _ => σ a) (↑x) (by simpa using x.2)) := hs'
      _ = ∑ σ ∈ Fintype.piFinset t, ∏ i : ι, h i (σ i) := hs''
  have ht : (Fintype.piFinset t) = (Finset.univ : Finset (ι → Bool)) := by
    simpa [t] using (Fintype.piFinset_univ (α := ι) (β := fun _ : ι => Bool))
  calc
    (∑ σ : (ι → Bool), ∏ i : ι, h i (σ i))
        = ∑ σ ∈ (Finset.univ : Finset (ι → Bool)), ∏ i : ι, h i (σ i) := by simp
    _ = ∑ σ ∈ Fintype.piFinset t, ∏ i : ι, h i (σ i) := by simp [ht]
    _ = ∏ i ∈ (Finset.univ : Finset ι), ∑ b ∈ (Finset.univ : Finset Bool), h i b := by
          simpa [hprod_sum] using hprod_sum.symm
    _ = ∏ i : ι, (∑ b : Bool, h i b) := by simp

end BoolFunctionSum

/-! ## Edge-monomials vs vertex-monomials -/

variable {V : Type u} [DecidableEq V]
variable {Λ : Finset V}

/-- Spin value in `ℝ` associated to a Boolean Ising spin `σ x`. -/
noncomputable def spinVal (σ : ↥Λ → Bool) (x : ↥Λ) : ℝ :=
  SpinGlass.isingSpin (σ x)

/-- Edge spin product \(σ_x σ_y\) for an unordered edge `e = {x,y}`. -/
noncomputable def edgeSpin (σ : ↥Λ → Bool) (e : Edge (V := V) Λ) : ℝ :=
  (e.1.lift
    ⟨fun x y => spinVal (Λ := Λ) σ x * spinVal (Λ := Λ) σ y, by
      intro x y
      simp [spinVal, mul_comm]⟩)

/-- Edge monomial \(\prod_e (σ_e)^{n(e)}\) associated to a current `n`. -/
noncomputable def edgeMonomial (σ : ↥Λ → Bool) (n : Current (V := V) Λ) : ℝ :=
  ∏ e : Edge (V := V) Λ, (edgeSpin (V := V) (Λ := Λ) σ e) ^ (n e)

/-- Vertex monomial \(\prod_x (σ_x)^{\deg_n(x)}\) associated to a current `n`. -/
noncomputable def vertexMonomial (σ : ↥Λ → Bool) (n : Current (V := V) Λ) : ℝ :=
  ∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x)

section ProdIndicatorTwo

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Equivalence between the two-point subset `{x // x = a ∨ x = b}` and `Bool`. -/
noncomputable def orEqEquivBool (a b : α) (hab : a ≠ b) : {x : α // x = a ∨ x = b} ≃ Bool := by
  have hba : b ≠ a := by
    intro h
    exact hab h.symm
  refine
    { toFun := fun x => if x.1 = a then true else false
      invFun := fun t => if t then ⟨a, Or.inl rfl⟩ else ⟨b, Or.inr rfl⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    by_cases hx : x.1 = a
    · apply Subtype.ext
      simp [hx]
    · have hx' : x.1 = b := by
        rcases x.2 with hxa | hxb
        · exfalso; exact hx hxa
        · exact hxb
      apply Subtype.ext
      simp [hx', hba]
  · intro t
    cases t <;> simp [hba]

variable {M : Type*} [CommMonoid M]

lemma prod_indicator_two (s : α → M) (a b : α) (hab : a ≠ b) (k : ℕ) :
    (∏ x : α, (s x) ^ (if x = a ∨ x = b then k else 0)) = (s a) ^ k * (s b) ^ k := by
  have hprod :
      (∏ x : α, (s x) ^ (if x = a ∨ x = b then k else 0))
        = ∏ x : α, dite (x = a ∨ x = b) (fun _ => (s x) ^ k) (fun _ => (1 : M)) := by
    refine Fintype.prod_congr
      (f := fun x : α => (s x) ^ (if x = a ∨ x = b then k else 0))
      (g := fun x : α => dite (x = a ∨ x = b) (fun _ => (s x) ^ k) (fun _ => (1 : M))) ?_
    intro x
    by_cases hx : x = a ∨ x = b <;> simp [hx]
  have hsplit :=
    (Fintype.prod_dite (α := α) (β := M) (p := fun x : α => x = a ∨ x = b)
      (f := fun x _ => (s x) ^ k) (g := fun _ _ => (1 : M)))
  have hsub : (∏ x : {x : α // x = a ∨ x = b}, (s x.1) ^ k) = (s a) ^ k * (s b) ^ k := by
    have hba : b ≠ a := by
      intro h
      exact hab h.symm
    have hEq : (∏ x : {x : α // x = a ∨ x = b}, (s x.1) ^ k)
        = ∏ t : Bool, (if t then (s a) ^ k else (s b) ^ k) := by
      refine (Fintype.prod_equiv (orEqEquivBool (α := α) a b hab)
        (fun x => (s x.1) ^ k)
        (fun t => if t then (s a) ^ k else (s b) ^ k) ?_)
      intro x
      by_cases hx : x.1 = a
      · simp [orEqEquivBool, hx]
      · have hx' : x.1 = b := by
          rcases x.2 with hxa | hxb
          · exfalso; exact hx hxa
          · exact hxb
        simp [orEqEquivBool, hx', hba]
    simp [hEq]
  calc
    (∏ x : α, (s x) ^ (if x = a ∨ x = b then k else 0))
        = ∏ x : α, dite (x = a ∨ x = b) (fun _ => (s x) ^ k) (fun _ => (1 : M)) := hprod
    _ = (∏ x : {x : α // x = a ∨ x = b}, (s x.1) ^ k) *
          ∏ x : {x : α // ¬ (x = a ∨ x = b)}, (1 : M) := by
          simpa using hsplit
    _ = (∏ x : {x : α // x = a ∨ x = b}, (s x.1) ^ k) := by simp
    _ = (s a) ^ k * (s b) ^ k := hsub

/-- Rewrite a product over a finset as a product over all indices with an indicator exponent. -/
lemma prod_mem_eq_prod_pow_indicator (A : Finset α) (s : α → M) :
    (∏ x ∈ A, s x) = ∏ x : α, (s x) ^ (if x ∈ A then (1 : ℕ) else 0) := by
  have hpow :
      (∏ x : α, (s x) ^ (if x ∈ A then (1 : ℕ) else 0)) = ∏ x : α, (if x ∈ A then s x else (1 : M)) := by
    refine Fintype.prod_congr
      (f := fun x : α => (s x) ^ (if x ∈ A then (1 : ℕ) else 0))
      (g := fun x : α => if x ∈ A then s x else (1 : M)) ?_
    intro x
    by_cases hx : x ∈ A <;> simp [hx]
  have hfilter :
      (∏ x : α, if x ∈ A then s x else (1 : M)) = ∏ x ∈ A, s x := by
    classical
    simp
  calc
    (∏ x ∈ A, s x)
        = ∏ x : α, if x ∈ A then s x else (1 : M) := by
            simp [hfilter]
    _ = ∏ x : α, (s x) ^ (if x ∈ A then (1 : ℕ) else 0) := by
            simp

end ProdIndicatorTwo

lemma edge_factor_eq_vertex_prod (σ : ↥Λ → Bool) (n : Current (V := V) Λ) (e : Edge (V := V) Λ) :
    (edgeSpin (V := V) (Λ := Λ) σ e) ^ (n e)
      = ∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (if x ∈ (e.1 : Sym2 (↥Λ)) then n e else 0) := by
  rcases e with ⟨m, hm⟩
  have hP :
      ∀ m : Sym2 (↥Λ),
        ∀ hm : ¬ Sym2.IsDiag m,
          (edgeSpin (V := V) (Λ := Λ) σ ⟨m, hm⟩) ^ (n ⟨m, hm⟩)
            = ∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (if x ∈ (m : Sym2 (↥Λ)) then n ⟨m, hm⟩ else 0) := by
    intro m
    refine Sym2.ind ?_ m
    intro a b hm
    have hab : a ≠ b := by
      simpa [Sym2.mk_isDiag_iff] using hm
    have hprod :=
      prod_indicator_two (α := ↥Λ) (M := ℝ) (s := fun x => spinVal (Λ := Λ) σ x) a b hab
        (k := n ⟨s(a, b), hm⟩)
    have hedge :
        edgeSpin (V := V) (Λ := Λ) σ ⟨s(a, b), hm⟩
          = spinVal (Λ := Λ) σ a * spinVal (Λ := Λ) σ b := by
      simp [edgeSpin, Sym2.lift_mk]
    calc
      (edgeSpin (V := V) (Λ := Λ) σ ⟨s(a, b), hm⟩) ^ (n ⟨s(a, b), hm⟩)
          = (spinVal (Λ := Λ) σ a) ^ (n ⟨s(a, b), hm⟩) *
              (spinVal (Λ := Λ) σ b) ^ (n ⟨s(a, b), hm⟩) := by
                simp [hedge, mul_pow]
      _ = ∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (if x = a ∨ x = b then n ⟨s(a, b), hm⟩ else 0) := by
            exact hprod.symm
      _ = ∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (if x ∈ (s(a, b) : Sym2 (↥Λ)) then n ⟨s(a, b), hm⟩ else 0) := by
            simp [Sym2.mem_iff]
  simpa using hP m hm

lemma edgeMonomial_eq_vertexMonomial (σ : ↥Λ → Bool) (n : Current (V := V) Λ) :
    edgeMonomial (V := V) (Λ := Λ) σ n = vertexMonomial (V := V) (Λ := Λ) σ n := by
  have h1 :
      (∏ e : Edge (V := V) Λ, (edgeSpin (V := V) (Λ := Λ) σ e) ^ (n e))
        =
        ∏ e : Edge (V := V) Λ,
          ∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (if x ∈ (e.1 : Sym2 (↥Λ)) then n e else 0) := by
    refine Fintype.prod_congr
      (f := fun e : Edge (V := V) Λ => (edgeSpin (V := V) (Λ := Λ) σ e) ^ (n e))
      (g := fun e : Edge (V := V) Λ =>
        ∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (if x ∈ (e.1 : Sym2 (↥Λ)) then n e else 0)) ?_
    intro e
    simpa using edge_factor_eq_vertex_prod (V := V) (Λ := Λ) (σ := σ) (n := n) e
  have hswap :
      (∏ e : Edge (V := V) Λ, ∏ x : ↥Λ,
          (spinVal (Λ := Λ) σ x) ^ (if x ∈ (e.1 : Sym2 (↥Λ)) then n e else 0))
        =
        ∏ x : ↥Λ, ∏ e : Edge (V := V) Λ,
          (spinVal (Λ := Λ) σ x) ^ (if x ∈ (e.1 : Sym2 (↥Λ)) then n e else 0) := by
    simpa using
      (Finset.prod_comm
        (s := (Finset.univ : Finset (Edge (V := V) Λ)))
        (t := (Finset.univ : Finset (↥Λ)))
        (f := fun e x =>
          (spinVal (Λ := Λ) σ x) ^ (if x ∈ (e.1 : Sym2 (↥Λ)) then n e else 0)))
  have hdeg :
      ∀ x : ↥Λ,
        (∏ e : Edge (V := V) Λ,
            (spinVal (Λ := Λ) σ x) ^ (if x ∈ (e.1 : Sym2 (↥Λ)) then n e else 0))
          =
          (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x) := by
    intro x
    simpa [degree] using
      (Finset.prod_pow_eq_pow_sum
        (s := (Finset.univ : Finset (Edge (V := V) Λ)))
        (f := fun e : Edge (V := V) Λ =>
          if x ∈ (e.1 : Sym2 (↥Λ)) then n e else 0)
        (a := spinVal (Λ := Λ) σ x))
  unfold edgeMonomial vertexMonomial
  calc
    (∏ e : Edge (V := V) Λ, (edgeSpin (V := V) (Λ := Λ) σ e) ^ (n e))
        = ∏ e : Edge (V := V) Λ,
            ∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (if x ∈ (e.1 : Sym2 (↥Λ)) then n e else 0) := h1
    _ = ∏ x : ↥Λ, ∏ e : Edge (V := V) Λ,
            (spinVal (Λ := Λ) σ x) ^ (if x ∈ (e.1 : Sym2 (↥Λ)) then n e else 0) := hswap
    _ = ∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x) := by
          refine Fintype.prod_congr (f := fun x => ∏ e : Edge (V := V) Λ,
            (spinVal (Λ := Λ) σ x) ^ (if x ∈ (e.1 : Sym2 (↥Λ)) then n e else 0))
            (g := fun x => (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x)) ?_
          intro x
          simpa using hdeg x


/-! ## Ising partition function as a current sum -/

/-- Boltzmann weight for a spin configuration `σ` in finite volume `Λ`. -/
noncomputable def isingBoltzmann (β : ℝ) (J : Edge (V := V) Λ → ℝ) (σ : ↥Λ → Bool) : ℝ :=
  ∏ e : Edge (V := V) Λ, Real.exp (β * J e * edgeSpin (V := V) (Λ := Λ) σ e)

/-- Finite-volume Ising partition function `Z_Λ(β)` (in Boolean-spin encoding). -/
noncomputable def isingZ (β : ℝ) (J : Edge (V := V) Λ → ℝ) : ℝ :=
  ∑ σ : (↥Λ → Bool), isingBoltzmann (V := V) (Λ := Λ) β J σ

/-- The Boltzmann weight is strictly positive. -/
lemma isingBoltzmann_pos (β : ℝ) (J : Edge (V := V) Λ → ℝ) (σ : ↥Λ → Bool) :
    0 < isingBoltzmann (V := V) (Λ := Λ) β J σ := by
  classical
  unfold isingBoltzmann
  simpa using
    (Finset.prod_pos (s := (Finset.univ : Finset (Edge (V := V) Λ)))
      (f := fun e : Edge (V := V) Λ =>
        Real.exp (β * J e * edgeSpin (V := V) (Λ := Λ) σ e))
      (by
        intro e _he
        simpa using (Real.exp_pos (β * J e * edgeSpin (V := V) (Λ := Λ) σ e))))

/-- The finite-volume partition function is strictly positive, hence nonzero. -/
lemma isingZ_pos (β : ℝ) (J : Edge (V := V) Λ → ℝ) :
    0 < isingZ (V := V) (Λ := Λ) β J := by
  classical
  unfold isingZ
  refine Finset.sum_pos (fun σ _hσ => isingBoltzmann_pos (V := V) (Λ := Λ) (β := β) (J := J) σ)
    (s := (Finset.univ : Finset (↥Λ → Bool))) Finset.univ_nonempty

lemma isingZ_ne_zero (β : ℝ) (J : Edge (V := V) Λ → ℝ) :
    isingZ (V := V) (Λ := Λ) β J ≠ 0 :=
  ne_of_gt (isingZ_pos (V := V) (Λ := Λ) (β := β) (J := J))

/-- Spin-inserted partition sum `∑_σ (∏_{x∈A} σ_x) e^{β H(σ)}`. -/
noncomputable def isingZWithSpin (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A : Finset (↥Λ)) : ℝ :=
  ∑ σ : (↥Λ → Bool),
    (∏ x ∈ A, spinVal (Λ := Λ) σ x) * isingBoltzmann (V := V) (Λ := Λ) β J σ

/-- The current weight `w(n) = ∏_e (β J_e)^{n(e)} / n(e)!` (real-valued). -/
noncomputable def weightReal (β : ℝ) (J : Edge (V := V) Λ → ℝ) (n : Current (V := V) Λ) : ℝ :=
  ∏ e : Edge (V := V) Λ, (β * J e) ^ (n e) / (n e).factorial

/-- Source-constrained current partition sum `Z_B = ∑_{∂n = B} w(n)` (real-valued). -/
noncomputable def ZReal (β : ℝ) (J : Edge (V := V) Λ → ℝ) (B : Finset (↥Λ)) : ℝ :=
  ∑' n : Current (V := V) Λ, if sources (V := V) n = B then weightReal (V := V) (Λ := Λ) β J n else 0

/-! ### Parity: `ZReal B = 0` when `B` has odd cardinality -/

lemma sources_ne_of_odd_card (n : Current (V := V) Λ) {B : Finset (↥Λ)} (hB : Odd B.card) :
    sources (V := V) n ≠ B := by
  intro hsrc
  have hEven : Even B.card := by
    simpa [hsrc] using (even_card_sources (V := V) (Λ := Λ) n)
  exact (Nat.not_even_iff_odd.2 hB) hEven

theorem ZReal_eq_zero_of_odd_card
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) {B : Finset (↥Λ)} (hB : Odd B.card) :
    ZReal (V := V) (Λ := Λ) β J B = 0 := by
  classical
  unfold ZReal
  have hsrc : ∀ n : Current (V := V) Λ, sources (V := V) n ≠ B := by
    intro n
    exact sources_ne_of_odd_card (V := V) (Λ := Λ) n hB
  simp [hsrc]

lemma real_exp_eq_tsum_pow_div_factorial (x : ℝ) :
    Real.exp x = ∑' n : ℕ, x ^ n / (n.factorial : ℝ) := by
  have hx :
      (NormedSpace.exp : ℝ → ℝ) x = ∑' n : ℕ, x ^ n / (n.factorial : ℝ) := by
    simpa using congrArg (fun f : ℝ → ℝ => f x) (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ))
  simpa [Real.exp_eq_exp_ℝ] using hx

lemma summable_norm_pow_div_factorial (x : ℝ) :
    Summable (fun n : ℕ => ‖x ^ n / (n.factorial : ℝ)‖) := by
  have : (fun n : ℕ => ‖x ^ n / (n.factorial : ℝ)‖) = fun n : ℕ => (|x| : ℝ) ^ n / (n.factorial : ℝ) := by
    funext n
    simp [Real.norm_eq_abs]
  simpa [this] using (Real.summable_pow_div_factorial (x := |x|))

lemma isingBoltzmann_eq_tsum_current (β : ℝ) (J : Edge (V := V) Λ → ℝ) (σ : ↥Λ → Bool) :
    isingBoltzmann (V := V) (Λ := Λ) β J σ
      =
      ∑' n : Current (V := V) Λ,
        weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n := by
  let f : Edge (V := V) Λ → ℕ → ℝ :=
    fun e k => (β * J e * edgeSpin (V := V) (Λ := Λ) σ e) ^ k / (k.factorial : ℝ)
  have hf : ∀ e, Summable fun k : ℕ => ‖f e k‖ := by
    intro e
    simpa [f] using summable_norm_pow_div_factorial (x := β * J e * edgeSpin (V := V) (Λ := Λ) σ e)
  have hprod := (tsum_pi_currTerm_eq_prod_tsum (E := Edge (V := V) Λ) f hf).2
  have hexp :
      ∏ e : Edge (V := V) Λ, Real.exp (β * J e * edgeSpin (V := V) (Λ := Λ) σ e)
        =
        ∏ e : Edge (V := V) Λ, (∑' k : ℕ, f e k) := by
    refine Fintype.prod_congr (f := fun e => Real.exp (β * J e * edgeSpin (V := V) (Λ := Λ) σ e))
      (g := fun e => (∑' k : ℕ, f e k)) ?_
    intro e
    simp [f, real_exp_eq_tsum_pow_div_factorial]
  have hterm :
      ∀ n : Current (V := V) Λ,
        currTerm (E := Edge (V := V) Λ) f n
          = weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n := by
    intro n
    have hfactor :
        (∏ e : Edge (V := V) Λ, f e (n e))
          =
          (∏ e : Edge (V := V) Λ,
              ((β * J e) ^ (n e) / (n e).factorial) *
                (edgeSpin (V := V) (Λ := Λ) σ e) ^ (n e)) := by
      refine Fintype.prod_congr
        (f := fun e : Edge (V := V) Λ => f e (n e))
        (g := fun e : Edge (V := V) Λ =>
          ((β * J e) ^ (n e) / (n e).factorial) *
            (edgeSpin (V := V) (Λ := Λ) σ e) ^ (n e)) ?_
      intro e
      simp [f, mul_pow, mul_div_right_comm, mul_assoc, mul_left_comm, mul_comm]
    have hsplit :
        (∏ e : Edge (V := V) Λ,
              ((β * J e) ^ (n e) / (n e).factorial) *
                (edgeSpin (V := V) (Λ := Λ) σ e) ^ (n e))
          =
          (∏ e : Edge (V := V) Λ, (β * J e) ^ (n e) / (n e).factorial) *
            ∏ e : Edge (V := V) Λ, (edgeSpin (V := V) (Λ := Λ) σ e) ^ (n e) := by
      simpa using
        (Finset.prod_mul_distrib
          (s := (Finset.univ : Finset (Edge (V := V) Λ)))
          (f := fun e : Edge (V := V) Λ => (β * J e) ^ (n e) / (n e).factorial)
          (g := fun e : Edge (V := V) Λ => (edgeSpin (V := V) (Λ := Λ) σ e) ^ (n e)))
    calc
      currTerm (E := Edge (V := V) Λ) f n
          = ∏ e : Edge (V := V) Λ, f e (n e) := by rfl
      _ = ∏ e : Edge (V := V) Λ,
              ((β * J e) ^ (n e) / (n e).factorial) *
                (edgeSpin (V := V) (Λ := Λ) σ e) ^ (n e) := hfactor
      _ = (∏ e : Edge (V := V) Λ, (β * J e) ^ (n e) / (n e).factorial) *
            ∏ e : Edge (V := V) Λ, (edgeSpin (V := V) (Λ := Λ) σ e) ^ (n e) := hsplit
      _ = weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n := by
            simp [weightReal, edgeMonomial]
  unfold isingBoltzmann
  calc
    (∏ e : Edge (V := V) Λ, Real.exp (β * J e * edgeSpin (V := V) (Λ := Λ) σ e))
        = ∏ e : Edge (V := V) Λ, (∑' k : ℕ, f e k) := hexp
    _ = ∑' n : Current (V := V) Λ, currTerm (E := Edge (V := V) Λ) f n := by
          exact hprod.symm
    _ = ∑' n : Current (V := V) Λ,
          weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n := by
          refine tsum_congr ?_
          intro n
          exact hterm n

lemma sum_bool_isingSpin_pow (m : ℕ) :
    (∑ b : Bool, SpinGlass.isingSpin b ^ m) = if Even m then (2 : ℝ) else 0 := by
  by_cases h : Even m
  · simp [SpinGlass.isingSpin, h, one_add_one_eq_two]
  · have h' : ¬ Even m := h
    simp [SpinGlass.isingSpin, h', neg_one_pow_eq_ite]

lemma sum_sigma_vertexMonomial_withSpin
    (n : Current (V := V) Λ) (A : Finset (↥Λ)) :
    (∑ σ : (↥Λ → Bool), (∏ x ∈ A, spinVal (Λ := Λ) σ x) * vertexMonomial (V := V) (Λ := Λ) σ n)
      =
      if sources (V := V) n = A then (2 : ℝ) ^ Λ.card else 0 := by
  have hintegrand :
      (fun σ : (↥Λ → Bool) =>
          (∏ x ∈ A, spinVal (Λ := Λ) σ x) * vertexMonomial (V := V) (Λ := Λ) σ n)
        =
        fun σ : (↥Λ → Bool) =>
          ∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^
            (degree (V := V) n x + if x ∈ A then 1 else 0) := by
    funext σ
    have hA :
        (∏ x ∈ A, spinVal (Λ := Λ) σ x)
          =
          ∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (if x ∈ A then 1 else 0) := by
      simpa using
        (prod_mem_eq_prod_pow_indicator (α := ↥Λ) (M := ℝ) (A := A)
          (s := fun x => spinVal (Λ := Λ) σ x))
    have hmul :
        (∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (if x ∈ A then 1 else 0)) *
            (∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x))
          =
          ∏ x : ↥Λ,
            (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x) *
              (spinVal (Λ := Λ) σ x) ^ (if x ∈ A then 1 else 0) := by
      have hswap :
          (∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (if x ∈ A then 1 else 0)) *
              (∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x))
            =
            (∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x)) *
              (∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (if x ∈ A then 1 else 0)) := by
        simp [mul_comm]
      have hcomb :
          (∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x)) *
              (∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (if x ∈ A then 1 else 0))
            =
            ∏ x : ↥Λ,
              (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x) *
                (spinVal (Λ := Λ) σ x) ^ (if x ∈ A then 1 else 0) := by
        change
          (Finset.univ.prod fun x : ↥Λ => (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x)) *
              (Finset.univ.prod fun x : ↥Λ => (spinVal (Λ := Λ) σ x) ^ (if x ∈ A then 1 else 0))
            =
            Finset.univ.prod fun x : ↥Λ =>
              (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x) *
                (spinVal (Λ := Λ) σ x) ^ (if x ∈ A then 1 else 0)
        exact
          (Finset.prod_mul_distrib
            (s := (Finset.univ : Finset (↥Λ)))
            (f := fun x : ↥Λ => (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x))
            (g := fun x : ↥Λ => (spinVal (Λ := Λ) σ x) ^ (if x ∈ A then 1 else 0))).symm
      exact hswap.trans hcomb
    calc
      (∏ x ∈ A, spinVal (Λ := Λ) σ x) * vertexMonomial (V := V) (Λ := Λ) σ n
          = (∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (if x ∈ A then 1 else 0)) *
              (∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x)) := by
                simp [vertexMonomial, hA]
      _ = ∏ x : ↥Λ,
            (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x) *
              (spinVal (Λ := Λ) σ x) ^ (if x ∈ A then 1 else 0) := hmul
      _ = ∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^
            (degree (V := V) n x + if x ∈ A then 1 else 0) := by
            refine Fintype.prod_congr
              (f := fun x : ↥Λ =>
                (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x) *
                  (spinVal (Λ := Λ) σ x) ^ (if x ∈ A then 1 else 0))
              (g := fun x : ↥Λ =>
                (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x + if x ∈ A then 1 else 0)) ?_
            intro x
            simpa using
              (pow_add (spinVal (Λ := Λ) σ x) (degree (V := V) n x) (if x ∈ A then 1 else 0)).symm
  have hfactor :
      (∑ σ : (↥Λ → Bool),
          ∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x + if x ∈ A then 1 else 0))
        =
        ∏ x : ↥Λ, (∑ b : Bool,
          SpinGlass.isingSpin b ^ (degree (V := V) n x + if x ∈ A then 1 else 0)) := by
    simpa [spinVal] using
      (sum_all_bool_functions_prod (ι := ↥Λ)
        (h := fun x b => SpinGlass.isingSpin b ^ (degree (V := V) n x + if x ∈ A then 1 else 0)))
  have hsingle :
      (∏ x : ↥Λ, (∑ b : Bool,
          SpinGlass.isingSpin b ^ (degree (V := V) n x + if x ∈ A then 1 else 0)))
        =
        if sources (V := V) n = A then (2 : ℝ) ^ Λ.card else 0 := by
    by_cases hsrc : sources (V := V) n = A
    · have hall :
          ∀ x : ↥Λ, Even (degree (V := V) n x + if x ∈ A then 1 else 0) := by
        intro x
        have hx : (Odd (degree (V := V) n x) ↔ x ∈ A) := by
          have : x ∈ sources (V := V) n ↔ x ∈ A := by
            simp [hsrc]
          simpa [mem_sources_iff] using this
        by_cases hxA : x ∈ A
        · have : Odd (degree (V := V) n x) := (hx.2 hxA)
          have : Even (degree (V := V) n x + 1) := by
            simpa [Nat.even_add_one, Nat.not_even_iff_odd] using (show Odd (degree (V := V) n x) from this)
          simpa [hxA] using this
        · have : ¬ Odd (degree (V := V) n x) := by
            intro hOdd
            exact hxA (hx.1 hOdd)
          simpa [hxA, Nat.not_odd_iff_even] using this
      have : (∏ x : ↥Λ, (∑ b : Bool,
          SpinGlass.isingSpin b ^ (degree (V := V) n x + if x ∈ A then 1 else 0)))
          = ∏ _x : ↥Λ, (2 : ℝ) := by
        refine Fintype.prod_congr (f := fun x : ↥Λ =>
          (∑ b : Bool, SpinGlass.isingSpin b ^ (degree (V := V) n x + if x ∈ A then 1 else 0)))
          (g := fun _ : ↥Λ => (2 : ℝ)) ?_
        intro x
        have hxEven := hall x
        simpa [sum_bool_isingSpin_pow, hxEven, if_pos hxEven] using (sum_bool_isingSpin_pow (m := degree (V := V) n x + if x ∈ A then 1 else 0))
      have hconst : (∏ _x : ↥Λ, (2 : ℝ)) = (2 : ℝ) ^ Λ.card := by
        simp
      simpa [hsrc, this, hconst]
    · have hne : ¬ (∀ x : ↥Λ, Odd (degree (V := V) n x) ↔ x ∈ A) := by
        intro hall
        apply hsrc
        ext x
        simpa [mem_sources_iff, IsSource] using hall x
      rcases not_forall.mp hne with ⟨x0, hx0⟩
      have hx0Odd : ¬ Even (degree (V := V) n x0 + if x0 ∈ A then 1 else 0) := by
        intro hxEven
        by_cases hxA : x0 ∈ A
        · have : Odd (degree (V := V) n x0) := by
            have : ¬ Even (degree (V := V) n x0) := by
              have := (Nat.even_add_one (n := degree (V := V) n x0)).1 (by simpa [hxA] using hxEven)
              exact this
            simpa [Nat.not_even_iff_odd] using this
          exact hx0 (Iff.intro (fun _ => hxA) (fun _ => this))
        · have : ¬ Odd (degree (V := V) n x0) := by
            have : Even (degree (V := V) n x0) := by simpa [hxA] using hxEven
            simpa [Nat.not_odd_iff_even] using this
          exact hx0 (Iff.intro (fun hOdd => False.elim (this hOdd)) (fun hxIn => False.elim (hxA hxIn)))
      have hfactor0 :
          (∑ b : Bool,
            SpinGlass.isingSpin b ^ (degree (V := V) n x0 + if x0 ∈ A then 1 else 0)) = 0 := by
        have hxOdd : ¬ Even (degree (V := V) n x0 + if x0 ∈ A then 1 else 0) := hx0Odd
        simpa [hxOdd] using
          (sum_bool_isingSpin_pow (m := degree (V := V) n x0 + if x0 ∈ A then 1 else 0))
      have :
          (∏ x : ↥Λ, (∑ b : Bool,
            SpinGlass.isingSpin b ^ (degree (V := V) n x + if x ∈ A then 1 else 0))) = 0 := by
        simpa using
          (Finset.prod_eq_zero (s := (Finset.univ : Finset (↥Λ)))
            (f := fun x : ↥Λ =>
              (∑ b : Bool,
                SpinGlass.isingSpin b ^ (degree (V := V) n x + if x ∈ A then 1 else 0)))
            (i := x0) (by simp) hfactor0)
      simpa [hsrc, this]
  calc
    (∑ σ : (↥Λ → Bool), (∏ x ∈ A, spinVal (Λ := Λ) σ x) * vertexMonomial (V := V) (Λ := Λ) σ n)
        = ∑ σ : (↥Λ → Bool),
            ∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x + if x ∈ A then 1 else 0) := by
            simp [hintegrand]
    _ = ∏ x : ↥Λ, (∑ b : Bool,
          SpinGlass.isingSpin b ^ (degree (V := V) n x + if x ∈ A then 1 else 0)) := by
          simpa using hfactor
    _ = if sources (V := V) n = A then (2 : ℝ) ^ Λ.card else 0 := hsingle

theorem isingZWithSpin_eq_ZReal (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A : Finset (↥Λ)) :
    isingZWithSpin (V := V) (Λ := Λ) β J A
      = (2 : ℝ) ^ Λ.card * ZReal (V := V) (Λ := Λ) β J A := by
  have hboltz :
      ∀ σ : (↥Λ → Bool),
        isingBoltzmann (V := V) (Λ := Λ) β J σ
          =
          ∑' n : Current (V := V) Λ,
            weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n := by
    intro σ
    simpa using isingBoltzmann_eq_tsum_current (V := V) (Λ := Λ) (β := β) (J := J) σ
  have hswap :
      (∑ σ : (↥Λ → Bool),
          (∏ x ∈ A, spinVal (Λ := Λ) σ x) *
            (∑' n : Current (V := V) Λ,
              weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n))
        =
        ∑' n : Current (V := V) Λ,
          ∑ σ : (↥Λ → Bool),
            (∏ x ∈ A, spinVal (Λ := Λ) σ x) *
              (weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n) := by
    have hsumm :
        ∀ σ : (↥Λ → Bool),
          Summable (fun n : Current (V := V) Λ =>
            (∏ x ∈ A, spinVal (Λ := Λ) σ x) *
              (weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n)) := by
      intro σ
      let f : Edge (V := V) Λ → ℕ → ℝ :=
        fun e k => (β * J e * edgeSpin (V := V) (Λ := Λ) σ e) ^ k / (k.factorial : ℝ)
      have hf : ∀ e, Summable fun k : ℕ => ‖f e k‖ := by
        intro e
        simpa [f] using summable_norm_pow_div_factorial (x := β * J e * edgeSpin (V := V) (Λ := Λ) σ e)
      have hsumN : Summable (fun n : Current (V := V) Λ => ‖currTerm (E := Edge (V := V) Λ) f n‖) :=
        (tsum_pi_currTerm_eq_prod_tsum (E := Edge (V := V) Λ) f hf).1
      have hterm :
          ∀ n : Current (V := V) Λ,
            currTerm (E := Edge (V := V) Λ) f n
              = weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n := by
        intro n
        have hfactor :
            (∏ e : Edge (V := V) Λ, f e (n e))
              =
              (∏ e : Edge (V := V) Λ,
                  ((β * J e) ^ (n e) / (n e).factorial) *
                    (edgeSpin (V := V) (Λ := Λ) σ e) ^ (n e)) := by
          refine Fintype.prod_congr
            (f := fun e : Edge (V := V) Λ => f e (n e))
            (g := fun e : Edge (V := V) Λ =>
              ((β * J e) ^ (n e) / (n e).factorial) *
                (edgeSpin (V := V) (Λ := Λ) σ e) ^ (n e)) ?_
          intro e
          simp [f, mul_pow, mul_div_right_comm, mul_assoc, mul_left_comm, mul_comm]
        have hsplit :
            (∏ e : Edge (V := V) Λ,
                  ((β * J e) ^ (n e) / (n e).factorial) *
                    (edgeSpin (V := V) (Λ := Λ) σ e) ^ (n e))
              =
              (∏ e : Edge (V := V) Λ, (β * J e) ^ (n e) / (n e).factorial) *
                ∏ e : Edge (V := V) Λ, (edgeSpin (V := V) (Λ := Λ) σ e) ^ (n e) := by
          simpa using
            (Finset.prod_mul_distrib
              (s := (Finset.univ : Finset (Edge (V := V) Λ)))
              (f := fun e : Edge (V := V) Λ => (β * J e) ^ (n e) / (n e).factorial)
              (g := fun e : Edge (V := V) Λ => (edgeSpin (V := V) (Λ := Λ) σ e) ^ (n e)))
        calc
          currTerm (E := Edge (V := V) Λ) f n
              = ∏ e : Edge (V := V) Λ, f e (n e) := by rfl
          _ = ∏ e : Edge (V := V) Λ,
                  ((β * J e) ^ (n e) / (n e).factorial) *
                    (edgeSpin (V := V) (Λ := Λ) σ e) ^ (n e) := hfactor
          _ = (∏ e : Edge (V := V) Λ, (β * J e) ^ (n e) / (n e).factorial) *
                ∏ e : Edge (V := V) Λ, (edgeSpin (V := V) (Λ := Λ) σ e) ^ (n e) := hsplit
          _ = weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n := by
                simp [weightReal, edgeMonomial]
      have hsum : Summable (fun n : Current (V := V) Λ =>
          weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n) := by
        have : Summable (fun n : Current (V := V) Λ =>
            ‖weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n‖) := by
          refine Summable.congr hsumN ?_
          intro n
          simp [hterm n]
        exact this.of_norm
      simpa [mul_assoc] using hsum.mul_left (∏ x ∈ A, spinVal (Λ := Λ) σ x)
    have hrewrite :
        (∑ σ : (↥Λ → Bool),
            (∏ x ∈ A, spinVal (Λ := Λ) σ x) *
              (∑' n : Current (V := V) Λ,
                weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n))
          =
          ∑ σ : (↥Λ → Bool),
            ∑' n : Current (V := V) Λ,
              (∏ x ∈ A, spinVal (Λ := Λ) σ x) *
                (weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n) := by
      refine Fintype.sum_congr
        (f := fun σ : (↥Λ → Bool) =>
          (∏ x ∈ A, spinVal (Λ := Λ) σ x) *
            (∑' n : Current (V := V) Λ,
              weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n))
        (g := fun σ : (↥Λ → Bool) =>
          ∑' n : Current (V := V) Λ,
            (∏ x ∈ A, spinVal (Λ := Λ) σ x) *
              (weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n)) ?_
      intro σ
      simpa [mul_assoc] using
        (tsum_mul_left (L := SummationFilter.unconditional (Current (V := V) Λ))
          (f := fun n : Current (V := V) Λ =>
            weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n)
          (a := (∏ x ∈ A, spinVal (Λ := Λ) σ x))).symm
    have hswap' :
        (∑ σ : (↥Λ → Bool),
            ∑' n : Current (V := V) Λ,
              (∏ x ∈ A, spinVal (Λ := Λ) σ x) *
                (weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n))
          =
          ∑' n : Current (V := V) Λ,
            ∑ σ : (↥Λ → Bool),
              (∏ x ∈ A, spinVal (Λ := Λ) σ x) *
                (weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n) := by
      have h :=
        (Summable.tsum_finsetSum
          (L := SummationFilter.unconditional (Current (V := V) Λ))
          (f := fun σ : (↥Λ → Bool) => fun n : Current (V := V) Λ =>
            (∏ x ∈ A, spinVal (Λ := Λ) σ x) *
              (weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n))
          (s := (Finset.univ : Finset (↥Λ → Bool)))
          (by
            intro σ hσ
            simpa using hsumm σ))
      simpa using h.symm
    exact hrewrite.trans hswap'
  have hspin :
      ∀ n : Current (V := V) Λ,
        (∑ σ : (↥Λ → Bool),
            (∏ x ∈ A, spinVal (Λ := Λ) σ x) *
              (weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n))
          =
          (2 : ℝ) ^ Λ.card * (if sources (V := V) n = A then weightReal (V := V) (Λ := Λ) β J n else 0) := by
    intro n
    have hmono :
        ∀ σ : (↥Λ → Bool), edgeMonomial (V := V) (Λ := Λ) σ n = vertexMonomial (V := V) (Λ := Λ) σ n := by
      intro σ
      simpa using edgeMonomial_eq_vertexMonomial (V := V) (Λ := Λ) (σ := σ) (n := n)
    have :
        (∑ σ : (↥Λ → Bool),
            (∏ x ∈ A, spinVal (Λ := Λ) σ x) *
              (weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n))
          =
          weightReal (V := V) (Λ := Λ) β J n *
            (∑ σ : (↥Λ → Bool), (∏ x ∈ A, spinVal (Λ := Λ) σ x) * vertexMonomial (V := V) (Λ := Λ) σ n) := by
      simp [hmono, mul_assoc, mul_comm, Finset.mul_sum]
    rw [this, sum_sigma_vertexMonomial_withSpin (V := V) (Λ := Λ) (n := n) (A := A)]
    by_cases hsrc : sources (V := V) n = A
    · simp [hsrc, mul_comm]
    · simp [hsrc]
  unfold isingZWithSpin ZReal isingBoltzmann
  calc
    (∑ σ : (↥Λ → Bool),
        (∏ x ∈ A, spinVal (Λ := Λ) σ x) * (∏ e : Edge (V := V) Λ, Real.exp (β * J e * edgeSpin (V := V) (Λ := Λ) σ e)))
        =
        (∑ σ : (↥Λ → Bool),
          (∏ x ∈ A, spinVal (Λ := Λ) σ x) *
            (∑' n : Current (V := V) Λ,
              weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n)) := by
            refine Fintype.sum_congr
              (f := fun σ : (↥Λ → Bool) =>
                (∏ x ∈ A, spinVal (Λ := Λ) σ x) *
                  (∏ e : Edge (V := V) Λ, Real.exp (β * J e * edgeSpin (V := V) (Λ := Λ) σ e)))
              (g := fun σ : (↥Λ → Bool) =>
                (∏ x ∈ A, spinVal (Λ := Λ) σ x) *
                  (∑' n : Current (V := V) Λ,
                    weightReal (V := V) (Λ := Λ) β J n *
                      edgeMonomial (V := V) (Λ := Λ) σ n)) ?_
            intro σ
            have hb :
                (∏ e : Edge (V := V) Λ,
                    Real.exp (β * J e * edgeSpin (V := V) (Λ := Λ) σ e))
                  =
                  ∑' n : Current (V := V) Λ,
                    weightReal (V := V) (Λ := Λ) β J n *
                      edgeMonomial (V := V) (Λ := Λ) σ n := by
              simpa [isingBoltzmann] using hboltz σ
            simp [hb]
    _ = ∑' n : Current (V := V) Λ,
          ∑ σ : (↥Λ → Bool),
            (∏ x ∈ A, spinVal (Λ := Λ) σ x) *
              (weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n) := hswap
    _ = ∑' n : Current (V := V) Λ,
          (2 : ℝ) ^ Λ.card * (if sources (V := V) n = A then weightReal (V := V) (Λ := Λ) β J n else 0) := by
            refine tsum_congr ?_
            intro n
            simpa using hspin n
    _ = (2 : ℝ) ^ Λ.card * ∑' n : Current (V := V) Λ,
          (if sources (V := V) n = A then weightReal (V := V) (Λ := Λ) β J n else 0) := by
            simpa using
              (tsum_mul_left (L := SummationFilter.unconditional (Current (V := V) Λ))
                (f := fun n : Current (V := V) Λ =>
                  (if sources (V := V) n = A then weightReal (V := V) (Λ := Λ) β J n else 0))
                (a := (2 : ℝ) ^ Λ.card))
    _ = (2 : ℝ) ^ Λ.card * ZReal (V := V) (Λ := Λ) β J A := by
            rfl

theorem isingZ_eq_ZReal (β : ℝ) (J : Edge (V := V) Λ → ℝ) :
    isingZ (V := V) (Λ := Λ) β J
      = (2 : ℝ) ^ Λ.card * ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) := by
  simpa [isingZ, isingZWithSpin] using
    (isingZWithSpin_eq_ZReal (V := V) (Λ := Λ) (β := β) (J := J) (A := (∅ : Finset (↥Λ))))

/-- The empty-source current sum `ZReal ∅` is always nonzero. -/
theorem ZReal_empty_ne_zero (β : ℝ) (J : Edge (V := V) Λ → ℝ) :
    ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) ≠ 0 := by
  have hZ : isingZ (V := V) (Λ := Λ) β J ≠ 0 :=
    isingZ_ne_zero (V := V) (Λ := Λ) (β := β) (J := J)
  intro h0
  have : isingZ (V := V) (Λ := Λ) β J = 0 := by
    simpa [h0] using (isingZ_eq_ZReal (V := V) (Λ := Λ) (β := β) (J := J))
  exact hZ this

/-- The empty-source current sum `ZReal ∅` is strictly positive (no sign assumptions needed). -/
theorem ZReal_empty_pos (β : ℝ) (J : Edge (V := V) Λ → ℝ) :
    0 < ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) := by
  have hZ : 0 < isingZ (V := V) (Λ := Λ) β J :=
    isingZ_pos (V := V) (Λ := Λ) (β := β) (J := J)
  have hpow : 0 < (2 : ℝ) ^ Λ.card := by
    exact pow_pos (by norm_num : (0 : ℝ) < 2) _
  have hmul :
      0 < (2 : ℝ) ^ Λ.card * ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) := by
    simpa [isingZ_eq_ZReal (V := V) (Λ := Λ) (β := β) (J := J)] using hZ
  exact pos_of_mul_pos_right hmul (le_of_lt hpow)

/-- Finite-volume Ising correlation `⟨∏_{x∈A} σ_x⟩_{Λ,β}` as a normalized spin-inserted partition sum. -/
noncomputable def isingCorr (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A : Finset (↥Λ)) : ℝ :=
  isingZWithSpin (V := V) (Λ := Λ) β J A / isingZ (V := V) (Λ := Λ) β J

/-- Random-current representation of finite-volume correlations: `⟨σ_A⟩ = Z_A / Z_∅`. -/
theorem isingCorr_eq_ZReal_div (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A : Finset (↥Λ)) :
    isingCorr (V := V) (Λ := Λ) β J A
      =
      ZReal (V := V) (Λ := Λ) β J A / ZReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) := by
  have hpow : ((2 : ℝ) ^ Λ.card) ≠ 0 := by
    exact pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)
  unfold isingCorr
  rw [isingZWithSpin_eq_ZReal (V := V) (Λ := Λ) (β := β) (J := J) (A := A),
    isingZ_eq_ZReal (V := V) (Λ := Λ) (β := β) (J := J)]
  simp [mul_div_mul_left, hpow]

theorem isingZWithSpin_eq_zero_of_odd_card
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) {A : Finset (↥Λ)} (hA : Odd A.card) :
    isingZWithSpin (V := V) (Λ := Λ) β J A = 0 := by
  have hZ : ZReal (V := V) (Λ := Λ) β J A = 0 :=
    ZReal_eq_zero_of_odd_card (V := V) (Λ := Λ) (β := β) (J := J) hA
  simp [isingZWithSpin_eq_ZReal, hZ]

theorem isingCorr_eq_zero_of_odd_card
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) {A : Finset (↥Λ)} (hA : Odd A.card) :
    isingCorr (V := V) (Λ := Λ) β J A = 0 := by
  have hZ : ZReal (V := V) (Λ := Λ) β J A = 0 :=
    ZReal_eq_zero_of_odd_card (V := V) (Λ := Λ) (β := β) (J := J) hA
  simp [isingCorr_eq_ZReal_div, hZ]

end RandomCurrent

end SpinGlass.Papers.Triviality4D
