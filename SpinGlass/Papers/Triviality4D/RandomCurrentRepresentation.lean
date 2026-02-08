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

noncomputable def currTerm {E : Type*} [Fintype E] (f : E → ℕ → ℝ) (n : E → ℕ) : ℝ :=
  ∏ e : E, f e (n e)

/-- Finite product of absolutely convergent series factorizes into a `tsum` over functions `E → ℕ`. -/
theorem tsum_pi_currTerm_eq_prod_tsum
    {E : Type*} [Fintype E]
    (f : E → ℕ → ℝ) (hf : ∀ e, Summable fun k : ℕ => ‖f e k‖) :
    (Summable (fun n : E → ℕ => ‖currTerm (E := E) f n‖)) ∧
      (∑' n : E → ℕ, currTerm (E := E) f n) = ∏ e : E, (∑' k : ℕ, f e k) := by
  classical
  refine (Fintype.induction_empty_option
    (P := fun E _ =>
      ∀ (f : E → ℕ → ℝ), (∀ e, Summable fun k : ℕ => ‖f e k‖) →
        (Summable (fun n : E → ℕ => ‖currTerm (E := E) f n‖)) ∧
          (∑' n : E → ℕ, currTerm (E := E) f n) = ∏ e : E, (∑' k : ℕ, f e k))
    (of_equiv := ?_) (h_empty := ?_) (h_option := ?_) E) f hf

  · intro α β hβ e hα
    intro f hf
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
              simpa [hterm n]

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
      _ = ∏ b : β, (∑' k : ℕ, f b k) := by simpa [hprod]

  · intro f _hf
    have hsum : Summable (fun n : (PEmpty → ℕ) => ‖currTerm (E := PEmpty) f n‖) := by
      simpa using (Summable.of_finite (f := fun n : (PEmpty → ℕ) => ‖currTerm (E := PEmpty) f n‖))
    refine ⟨hsum, ?_⟩
    simpa [currTerm] using (tsum_fintype (fun _ : (PEmpty → ℕ) => (1 : ℝ)))

  · intro α _ hα
    intro f hf
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
          simpa [currTerm, rest, fα, ecur, Fintype.prod_option] using
            (norm_mul_le (f none p.1) (rest p.2))
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
              simpa [hmul] using hmul.symm
        _ = (∑' n0 : ℕ, f none n0) * (∏ a : α, (∑' k : ℕ, fα a k)) := by
              simp [hrest_eq]
        _ = ∏ o : Option α, (∑' k : ℕ, f o k) := by
              simpa [fα, Fintype.prod_option]

    exact ⟨hsum, heq⟩


section BoolFunctionSum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (h : ι → Bool → ℝ)

/-- Finite sum over all functions `ι → Bool` factorizes into a product of single-site sums. -/
lemma sum_all_bool_functions_prod :
    (∑ σ : (ι → Bool), ∏ i : ι, h i (σ i)) = ∏ i : ι, (∑ b : Bool, h i b) := by
  classical
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
                h (↑x) (p (↑x) (by simpa using x.2)) := by
      simpa [t, Finset.prod_attach] using
        (Finset.prod_sum (s := (Finset.univ : Finset ι)) (t := t) (f := fun i b => h i b))
    have hs' :
        (∑ p ∈ (Finset.univ : Finset ι).pi t,
            ∏ x ∈ (Finset.univ : Finset ι).attach,
              h (↑x) (p (↑x) (by simpa using x.2)))
          = ∑ σ ∈ Fintype.piFinset t,
              ∏ x ∈ (Finset.univ : Finset ι).attach,
                h (↑x) ((fun a _ => σ a) (↑x) (by simpa using x.2)) := by
      simpa [t] using
        (Finset.sum_univ_pi (ι := ι) (β := ℝ) (t := t)
          (f := fun p =>
            ∏ x ∈ (Finset.univ : Finset ι).attach,
              h (↑x) (p (↑x) (by simpa using x.2))))
    have hs'' :
        (∑ σ ∈ Fintype.piFinset t,
            ∏ x ∈ (Finset.univ : Finset ι).attach,
              h (↑x) ((fun a _ => σ a) (↑x) (by simpa using x.2)))
          = ∑ σ ∈ Fintype.piFinset t, ∏ i : ι, h i (σ i) := by
      simp [Finset.prod_attach]
    calc
      (∏ i ∈ (Finset.univ : Finset ι), ∑ b ∈ (Finset.univ : Finset Bool), h i b)
          = ∑ p ∈ (Finset.univ : Finset ι).pi t,
              ∏ x ∈ (Finset.univ : Finset ι).attach,
                h (↑x) (p (↑x) (by simpa using x.2)) := by
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
    _ = ∑ σ ∈ Fintype.piFinset t, ∏ i : ι, h i (σ i) := by simpa [ht]
    _ = ∏ i ∈ (Finset.univ : Finset ι), ∑ b ∈ (Finset.univ : Finset Bool), h i b := by
          simpa [hprod_sum] using hprod_sum.symm
    _ = ∏ i : ι, (∑ b : Bool, h i b) := by simp [hR]

end BoolFunctionSum

/-! ## Edge-monomials vs vertex-monomials -/

variable {V : Type u} [DecidableEq V]
variable {Λ : Finset V}

noncomputable def spinVal (σ : ↥Λ → Bool) (x : ↥Λ) : ℝ :=
  SpinGlass.isingSpin (σ x)

noncomputable def edgeSpin (σ : ↥Λ → Bool) (e : Edge (V := V) Λ) : ℝ :=
  (e.1.lift
    ⟨fun x y => spinVal (Λ := Λ) σ x * spinVal (Λ := Λ) σ y, by
      intro x y
      simp [spinVal, mul_comm]⟩)

noncomputable def edgeMonomial (σ : ↥Λ → Bool) (n : Current (V := V) Λ) : ℝ :=
  ∏ e : Edge (V := V) Λ, (edgeSpin (V := V) (Λ := Λ) σ e) ^ (n e)

noncomputable def vertexMonomial (σ : ↥Λ → Bool) (n : Current (V := V) Λ) : ℝ :=
  ∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x)

section ProdIndicatorTwo

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def orEqEquivBool (a b : α) (hab : a ≠ b) : {x : α // x = a ∨ x = b} ≃ Bool := by
  classical
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
  classical
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
    simp [hEq, Fintype.prod_bool, mul_comm, mul_left_comm, mul_assoc]
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
  classical
  -- rewrite the RHS as an `if`-product
  have hpow :
      (∏ x : α, (s x) ^ (if x ∈ A then (1 : ℕ) else 0)) = ∏ x : α, (if x ∈ A then s x else (1 : M)) := by
    refine Fintype.prod_congr
      (f := fun x : α => (s x) ^ (if x ∈ A then (1 : ℕ) else 0))
      (g := fun x : α => if x ∈ A then s x else (1 : M)) ?_
    intro x
    by_cases hx : x ∈ A <;> simp [hx]
  -- turn the `if`-product into a filter-product on `Finset.univ`
  have hfilter :
      (∏ x : α, if x ∈ A then s x else (1 : M)) = ∏ x ∈ A, s x := by
    have h1 :
        (∏ x ∈ (Finset.univ : Finset α) with x ∈ A, s x)
          = ∏ x ∈ (Finset.univ : Finset α), if x ∈ A then s x else (1 : M) := by
      simpa using
        (Finset.prod_filter (s := (Finset.univ : Finset α)) (p := fun x : α => x ∈ A) (f := s))
    have huniv : (Finset.univ.filter (fun x : α => x ∈ A)) = A := by
      ext x
      simp
    simpa [huniv] using h1.symm
  -- assemble
  calc
    (∏ x ∈ A, s x)
        = ∏ x : α, if x ∈ A then s x else (1 : M) := by
            simpa [hfilter] using hfilter.symm
    _ = ∏ x : α, (s x) ^ (if x ∈ A then (1 : ℕ) else 0) := by
            simpa [hpow] using hpow.symm

end ProdIndicatorTwo

lemma edge_factor_eq_vertex_prod (σ : ↥Λ → Bool) (n : Current (V := V) Λ) (e : Edge (V := V) Λ) :
    (edgeSpin (V := V) (Λ := Λ) σ e) ^ (n e)
      = ∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (if x ∈ (e.1 : Sym2 (↥Λ)) then n e else 0) := by
  classical
  rcases e with ⟨m, hm⟩
  -- reduce to `m = s(a,b)` using `Sym2.ind`, but quantify the off-diagonal proof
  have hP :
      ∀ m : Sym2 (↥Λ),
        ∀ hm : ¬ Sym2.IsDiag m,
          (edgeSpin (V := V) (Λ := Λ) σ ⟨m, hm⟩) ^ (n ⟨m, hm⟩)
            = ∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (if x ∈ (m : Sym2 (↥Λ)) then n ⟨m, hm⟩ else 0) := by
    intro m
    refine Sym2.ind ?_ m
    intro a b
    intro hm
    have hab : a ≠ b := by
      -- `hm : ¬ Sym2.IsDiag (s(a,b))`
      simpa [Sym2.mk_isDiag_iff] using hm
    -- rewrite membership in a 2-set
    have hmemb :
        (fun x : ↥Λ => x ∈ (s(a, b) : Sym2 (↥Λ)))
          = fun x => x = a ∨ x = b := by
      funext x
      simpa [Sym2.mem_iff]
    -- apply the 2-point product lemma
    have hprod :=
      prod_indicator_two (α := ↥Λ) (M := ℝ) (s := fun x => spinVal (Λ := Λ) σ x) a b hab
        (k := n ⟨s(a, b), hm⟩)
    -- compute `edgeSpin` on `s(a,b)`
    have hedge :
        edgeSpin (V := V) (Λ := Λ) σ ⟨s(a, b), hm⟩
          = spinVal (Λ := Λ) σ a * spinVal (Λ := Λ) σ b := by
      simp [edgeSpin, Sym2.lift_mk]
    -- finish
    calc
      (edgeSpin (V := V) (Λ := Λ) σ ⟨s(a, b), hm⟩) ^ (n ⟨s(a, b), hm⟩)
          = (spinVal (Λ := Λ) σ a) ^ (n ⟨s(a, b), hm⟩) *
              (spinVal (Λ := Λ) σ b) ^ (n ⟨s(a, b), hm⟩) := by
                simpa [hedge, mul_pow]
      _ = ∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (if x = a ∨ x = b then n ⟨s(a, b), hm⟩ else 0) := by
            exact hprod.symm
      _ = ∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (if x ∈ (s(a, b) : Sym2 (↥Λ)) then n ⟨s(a, b), hm⟩ else 0) := by
            -- rewrite membership in `s(a,b)`
            simpa [hmemb]
  simpa using hP m hm

lemma edgeMonomial_eq_vertexMonomial (σ : ↥Λ → Bool) (n : Current (V := V) Λ) :
    edgeMonomial (V := V) (Λ := Λ) σ n = vertexMonomial (V := V) (Λ := Λ) σ n := by
  classical
  -- expand each edge factor into a product over vertices
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

  -- swap product order
  have hswap :
      (∏ e : Edge (V := V) Λ, ∏ x : ↥Λ,
          (spinVal (Λ := Λ) σ x) ^ (if x ∈ (e.1 : Sym2 (↥Λ)) then n e else 0))
        =
        ∏ x : ↥Λ, ∏ e : Edge (V := V) Λ,
          (spinVal (Λ := Λ) σ x) ^ (if x ∈ (e.1 : Sym2 (↥Λ)) then n e else 0) := by
    -- use commutativity of multiplication to swap the two finite products
    simpa using
      (Finset.prod_comm
        (s := (Finset.univ : Finset (Edge (V := V) Λ)))
        (t := (Finset.univ : Finset (↥Λ)))
        (f := fun e x =>
          (spinVal (Λ := Λ) σ x) ^ (if x ∈ (e.1 : Sym2 (↥Λ)) then n e else 0)))

  -- collapse the inner edge-product into the degree exponent
  have hdeg :
      ∀ x : ↥Λ,
        (∏ e : Edge (V := V) Λ,
            (spinVal (Λ := Λ) σ x) ^ (if x ∈ (e.1 : Sym2 (↥Λ)) then n e else 0))
          =
          (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x) := by
    intro x
    -- `∏ a^f = a^(∑ f)` on a finite set
    simpa [degree] using
      (Finset.prod_pow_eq_pow_sum
        (s := (Finset.univ : Finset (Edge (V := V) Λ)))
        (f := fun e : Edge (V := V) Λ =>
          if x ∈ (e.1 : Sym2 (↥Λ)) then n e else 0)
        (a := spinVal (Λ := Λ) σ x))

  -- assemble
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

noncomputable def isingBoltzmann (β : ℝ) (J : Edge (V := V) Λ → ℝ) (σ : ↥Λ → Bool) : ℝ :=
  ∏ e : Edge (V := V) Λ, Real.exp (β * J e * edgeSpin (V := V) (Λ := Λ) σ e)

noncomputable def isingZ (β : ℝ) (J : Edge (V := V) Λ → ℝ) : ℝ :=
  ∑ σ : (↥Λ → Bool), isingBoltzmann (V := V) (Λ := Λ) β J σ

noncomputable def isingZWithSpin (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A : Finset (↥Λ)) : ℝ :=
  ∑ σ : (↥Λ → Bool),
    (∏ x ∈ A, spinVal (Λ := Λ) σ x) * isingBoltzmann (V := V) (Λ := Λ) β J σ

/-- The current weight `w(n) = ∏_e (β J_e)^{n(e)} / n(e)!` (real-valued). -/
noncomputable def weightReal (β : ℝ) (J : Edge (V := V) Λ → ℝ) (n : Current (V := V) Λ) : ℝ :=
  ∏ e : Edge (V := V) Λ, (β * J e) ^ (n e) / (n e).factorial

/-- Source-constrained current partition sum `Z_B = ∑_{∂n = B} w(n)` (real-valued). -/
noncomputable def ZReal (β : ℝ) (J : Edge (V := V) Λ → ℝ) (B : Finset (↥Λ)) : ℝ :=
  ∑' n : Current (V := V) Λ, if sources (V := V) n = B then weightReal (V := V) (Λ := Λ) β J n else 0

lemma real_exp_eq_tsum_pow_div_factorial (x : ℝ) :
    Real.exp x = ∑' n : ℕ, x ^ n / (n.factorial : ℝ) := by
  have hx :
      (NormedSpace.exp : ℝ → ℝ) x = ∑' n : ℕ, x ^ n / (n.factorial : ℝ) := by
    simpa using congrArg (fun f : ℝ → ℝ => f x) (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ))
  simpa [Real.exp_eq_exp_ℝ] using hx

lemma summable_norm_pow_div_factorial (x : ℝ) :
    Summable (fun n : ℕ => ‖x ^ n / (n.factorial : ℝ)‖) := by
  -- `‖x^n / n!‖ = |x|^n / n!`
  have : (fun n : ℕ => ‖x ^ n / (n.factorial : ℝ)‖) = fun n : ℕ => (|x| : ℝ) ^ n / (n.factorial : ℝ) := by
    funext n
    simp [Real.norm_eq_abs, abs_pow, abs_div]
  simpa [this] using (Real.summable_pow_div_factorial (x := |x|))

lemma isingBoltzmann_eq_tsum_current (β : ℝ) (J : Edge (V := V) Λ → ℝ) (σ : ↥Λ → Bool) :
    isingBoltzmann (V := V) (Λ := Λ) β J σ
      =
      ∑' n : Current (V := V) Λ,
        weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n := by
  classical
  -- apply the finite-product-of-series lemma on the edge set
  let f : Edge (V := V) Λ → ℕ → ℝ :=
    fun e k => (β * J e * edgeSpin (V := V) (Λ := Λ) σ e) ^ k / (k.factorial : ℝ)
  have hf : ∀ e, Summable fun k : ℕ => ‖f e k‖ := by
    intro e
    -- reduce to summability of the exponential series
    simpa [f] using summable_norm_pow_div_factorial (x := β * J e * edgeSpin (V := V) (Λ := Λ) σ e)
  have hprod := (tsum_pi_currTerm_eq_prod_tsum (E := Edge (V := V) Λ) f hf).2
  -- rewrite the product of exponentials into the product of series, then into a `tsum` over currents
  have hexp :
      ∏ e : Edge (V := V) Λ, Real.exp (β * J e * edgeSpin (V := V) (Λ := Λ) σ e)
        =
        ∏ e : Edge (V := V) Λ, (∑' k : ℕ, f e k) := by
    refine Fintype.prod_congr (f := fun e => Real.exp (β * J e * edgeSpin (V := V) (Λ := Λ) σ e))
      (g := fun e => (∑' k : ℕ, f e k)) ?_
    intro e
    simpa [f, real_exp_eq_tsum_pow_div_factorial] using
      (real_exp_eq_tsum_pow_div_factorial (x := β * J e * edgeSpin (V := V) (Λ := Λ) σ e))
  -- simplify the `currTerm` into `weightReal * edgeMonomial`
  have hterm :
      ∀ n : Current (V := V) Λ,
        currTerm (E := Edge (V := V) Λ) f n
          = weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n := by
    intro n
    -- split each factor into a weight and a spin monomial, then use `Finset.prod_mul_distrib`
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
      -- `(β J e * edgeSpin)^k / k! = ((β J e)^k / k!) * (edgeSpin)^k`
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
            simp [weightReal, edgeMonomial, mul_assoc]
  -- conclude
  unfold isingBoltzmann
  calc
    (∏ e : Edge (V := V) Λ, Real.exp (β * J e * edgeSpin (V := V) (Λ := Λ) σ e))
        = ∏ e : Edge (V := V) Λ, (∑' k : ℕ, f e k) := hexp
    _ = ∑' n : Current (V := V) Λ, currTerm (E := Edge (V := V) Λ) f n := by
          -- rewrite the equality from `tsum_pi_currTerm_eq_prod_tsum`
          simpa [hprod] using hprod.symm
    _ = ∑' n : Current (V := V) Λ,
          weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n := by
          refine tsum_congr ?_
          intro n
          simpa [hterm n]

lemma sum_bool_isingSpin_pow (m : ℕ) :
    (∑ b : Bool, SpinGlass.isingSpin b ^ m) = if Even m then (2 : ℝ) else 0 := by
  classical
  by_cases h : Even m
  · -- sum over Bool = value at `true` plus value at `false`
    simp [Fintype.sum_bool, SpinGlass.isingSpin, h, neg_one_pow_eq_ite, one_add_one_eq_two]
  · have h' : ¬ Even m := h
    simp [Fintype.sum_bool, SpinGlass.isingSpin, h', neg_one_pow_eq_ite]

lemma sum_sigma_vertexMonomial_withSpin
    (n : Current (V := V) Λ) (A : Finset (↥Λ)) :
    (∑ σ : (↥Λ → Bool), (∏ x ∈ A, spinVal (Λ := Λ) σ x) * vertexMonomial (V := V) (Λ := Λ) σ n)
      =
      if sources (V := V) n = A then (2 : ℝ) ^ Λ.card else 0 := by
  classical
  -- rewrite the integrand as a product over all vertices with modified exponents
  have hintegrand :
      (fun σ : (↥Λ → Bool) =>
          (∏ x ∈ A, spinVal (Λ := Λ) σ x) * vertexMonomial (V := V) (Λ := Λ) σ n)
        =
        fun σ : (↥Λ → Bool) =>
          ∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^
            (degree (V := V) n x + if x ∈ A then 1 else 0) := by
    funext σ
    -- first rewrite `∏ x ∈ A, spinVal σ x` as a product over all vertices with exponent `if x∈A then 1 else 0`
    have hA :
        (∏ x ∈ A, spinVal (Λ := Λ) σ x)
          =
          ∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (if x ∈ A then 1 else 0) := by
      simpa using
        (prod_mem_eq_prod_pow_indicator (α := ↥Λ) (M := ℝ) (A := A)
          (s := fun x => spinVal (Λ := Λ) σ x))
    -- combine the two vertex products pointwise using `Finset.prod_mul_distrib`, then `pow_add`
    have hmul :
        (∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (if x ∈ A then 1 else 0)) *
            (∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x))
          =
          ∏ x : ↥Λ,
            (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x) *
              (spinVal (Λ := Λ) σ x) ^ (if x ∈ A then 1 else 0) := by
      classical
      -- swap the two products, then use `Finset.prod_mul_distrib` on `Finset.univ`
      have hswap :
          (∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (if x ∈ A then 1 else 0)) *
              (∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x))
            =
            (∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x)) *
              (∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (if x ∈ A then 1 else 0)) := by
        simp [mul_comm]
      -- combine products
      have hcomb :
          (∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x)) *
              (∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (if x ∈ A then 1 else 0))
            =
            ∏ x : ↥Λ,
              (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x) *
                (spinVal (Λ := Λ) σ x) ^ (if x ∈ A then 1 else 0) := by
        -- make the underlying `Finset.univ` explicit
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
                simpa [vertexMonomial, hA]
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
            simpa [pow_add] using
              (pow_add (spinVal (Λ := Λ) σ x) (degree (V := V) n x) (if x ∈ A then 1 else 0)).symm

  -- factorize the sum over all functions `σ : ↥Λ → Bool`
  -- using `sum_all_bool_functions_prod`
  have hfactor :
      (∑ σ : (↥Λ → Bool),
          ∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x + if x ∈ A then 1 else 0))
        =
        ∏ x : ↥Λ, (∑ b : Bool,
          SpinGlass.isingSpin b ^ (degree (V := V) n x + if x ∈ A then 1 else 0)) := by
    -- apply the generic factorization lemma with `h x b = isingSpin b ^ exponent`
    simpa [spinVal] using
      (sum_all_bool_functions_prod (ι := ↥Λ)
        (h := fun x b => SpinGlass.isingSpin b ^ (degree (V := V) n x + if x ∈ A then 1 else 0)))

  -- evaluate each single-site sum and determine when the product is nonzero
  have hsingle :
      (∏ x : ↥Λ, (∑ b : Bool,
          SpinGlass.isingSpin b ^ (degree (V := V) n x + if x ∈ A then 1 else 0)))
        =
        if sources (V := V) n = A then (2 : ℝ) ^ Λ.card else 0 := by
    by_cases hsrc : sources (V := V) n = A
    · -- all modified degrees are even, so each factor is `2`
      have hall :
          ∀ x : ↥Λ, Even (degree (V := V) n x + if x ∈ A then 1 else 0) := by
        intro x
        have hx : (Odd (degree (V := V) n x) ↔ x ∈ A) := by
          -- from `sources n = A`
          have : x ∈ sources (V := V) n ↔ x ∈ A := by simpa [hsrc] using congrArg (fun s => x ∈ s) hsrc
          simpa [mem_sources_iff] using this
        by_cases hxA : x ∈ A
        · -- exponent = degree + 1, even iff odd degree
          have : Odd (degree (V := V) n x) := (hx.2 hxA)
          -- `Even (d+1) ↔ Odd d`
          have : Even (degree (V := V) n x + 1) := by
            simpa [Nat.even_add_one, Nat.not_even_iff_odd] using (show Odd (degree (V := V) n x) from this)
          simpa [hxA] using this
        · -- exponent = degree, even since not odd degree
          have : ¬ Odd (degree (V := V) n x) := by
            intro hOdd
            exact hxA (hx.1 hOdd)
          simpa [hxA, Nat.not_odd_iff_even] using this
      -- replace each factor by `2`
      have : (∏ x : ↥Λ, (∑ b : Bool,
          SpinGlass.isingSpin b ^ (degree (V := V) n x + if x ∈ A then 1 else 0)))
          = ∏ _x : ↥Λ, (2 : ℝ) := by
        refine Fintype.prod_congr (f := fun x : ↥Λ =>
          (∑ b : Bool, SpinGlass.isingSpin b ^ (degree (V := V) n x + if x ∈ A then 1 else 0)))
          (g := fun _ : ↥Λ => (2 : ℝ)) ?_
        intro x
        have hxEven := hall x
        simpa [sum_bool_isingSpin_pow, hxEven, if_pos hxEven] using (sum_bool_isingSpin_pow (m := degree (V := V) n x + if x ∈ A then 1 else 0))
      -- compute product of a constant
      -- `Fintype.card (↥Λ) = Λ.card`
      have hconst : (∏ _x : ↥Λ, (2 : ℝ)) = (2 : ℝ) ^ Λ.card := by
        classical
        have h' : (∏ _x : ↥Λ, (2 : ℝ)) = (2 : ℝ) ^ Fintype.card (↥Λ) := by
          simpa [Finset.prod_const] using
            (Finset.prod_const (s := (Finset.univ : Finset (↥Λ))) (b := (2 : ℝ)))
        simpa [Fintype.card_coe Λ] using h'
      simpa [hsrc, this, hconst]
    · -- mismatch in sources: some factor is zero
      -- pick a vertex where the parity constraint fails
      have hne : ¬ (∀ x : ↥Λ, Odd (degree (V := V) n x) ↔ x ∈ A) := by
        intro hall
        apply hsrc
        ext x
        -- `x ∈ sources n ↔ IsSource n x ↔ Odd (degree n x)`
        simpa [mem_sources_iff, IsSource] using hall x
      rcases not_forall.mp hne with ⟨x0, hx0⟩
      -- show the x0-factor equals 0
      have hx0Odd : ¬ Even (degree (V := V) n x0 + if x0 ∈ A then 1 else 0) := by
        -- if it were even, we'd have `Odd degree ↔ x0 ∈ A`
        intro hxEven
        by_cases hxA : x0 ∈ A
        · -- even(d+1) -> odd d
          have : Odd (degree (V := V) n x0) := by
            have : ¬ Even (degree (V := V) n x0) := by
              -- from even(d+1)
              have := (Nat.even_add_one (n := degree (V := V) n x0)).1 (by simpa [hxA] using hxEven)
              exact this
            simpa [Nat.not_even_iff_odd] using this
          exact hx0 (Iff.intro (fun _ => hxA) (fun _ => this))
        · -- even(d) means not odd d, hence `Odd d ↔ False`
          have : ¬ Odd (degree (V := V) n x0) := by
            have : Even (degree (V := V) n x0) := by simpa [hxA] using hxEven
            simpa [Nat.not_odd_iff_even] using this
          exact hx0 (Iff.intro (fun hOdd => False.elim (this hOdd)) (fun hxIn => False.elim (hxA hxIn)))
      -- now use `Finset.prod_eq_zero` on `univ`
      have hfactor0 :
          (∑ b : Bool,
            SpinGlass.isingSpin b ^ (degree (V := V) n x0 + if x0 ∈ A then 1 else 0)) = 0 := by
        have hxOdd : ¬ Even (degree (V := V) n x0 + if x0 ∈ A then 1 else 0) := hx0Odd
        simpa [hxOdd] using
          (sum_bool_isingSpin_pow (m := degree (V := V) n x0 + if x0 ∈ A then 1 else 0))
      -- conclude the full product is zero
      have :
          (∏ x : ↥Λ, (∑ b : Bool,
            SpinGlass.isingSpin b ^ (degree (V := V) n x + if x ∈ A then 1 else 0))) = 0 := by
        -- use `Finset.prod_eq_zero` on `univ`
        classical
        simpa using
          (Finset.prod_eq_zero (s := (Finset.univ : Finset (↥Λ)))
            (f := fun x : ↥Λ =>
              (∑ b : Bool,
                SpinGlass.isingSpin b ^ (degree (V := V) n x + if x ∈ A then 1 else 0)))
            (i := x0) (by simp) hfactor0)
      simpa [hsrc, this]

  -- finalize
  calc
    (∑ σ : (↥Λ → Bool), (∏ x ∈ A, spinVal (Λ := Λ) σ x) * vertexMonomial (V := V) (Λ := Λ) σ n)
        = ∑ σ : (↥Λ → Bool),
            ∏ x : ↥Λ, (spinVal (Λ := Λ) σ x) ^ (degree (V := V) n x + if x ∈ A then 1 else 0) := by
            simpa [hintegrand]
    _ = ∏ x : ↥Λ, (∑ b : Bool,
          SpinGlass.isingSpin b ^ (degree (V := V) n x + if x ∈ A then 1 else 0)) := by
          simpa using hfactor
    _ = if sources (V := V) n = A then (2 : ℝ) ^ Λ.card else 0 := hsingle

theorem isingZWithSpin_eq_ZReal (β : ℝ) (J : Edge (V := V) Λ → ℝ) (A : Finset (↥Λ)) :
    isingZWithSpin (V := V) (Λ := Λ) β J A
      = (2 : ℝ) ^ Λ.card * ZReal (V := V) (Λ := Λ) β J A := by
  classical
  -- expand `isingBoltzmann` as a `tsum` over currents
  have hboltz :
      ∀ σ : (↥Λ → Bool),
        isingBoltzmann (V := V) (Λ := Λ) β J σ
          =
          ∑' n : Current (V := V) Λ,
            weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n := by
    intro σ
    simpa using isingBoltzmann_eq_tsum_current (V := V) (Λ := Λ) (β := β) (J := J) σ
  -- interchange the finite sum over `σ` with the `tsum` over currents
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
    -- use `Summable.tsum_finsetSum` with `s = univ` and then rewrite `∑ σ` back
    classical
    -- summability in `n` for each fixed `σ` follows from `tsum_pi_currTerm_eq_prod_tsum`
    have hsumm :
        ∀ σ : (↥Λ → Bool),
          Summable (fun n : Current (V := V) Λ =>
            (∏ x ∈ A, spinVal (Λ := Λ) σ x) *
              (weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n)) := by
      intro σ
      -- scale a summable series by a constant
      -- we get summability from the summability of the norms in `tsum_pi_currTerm_eq_prod_tsum`
      -- applied to the edge series defining `isingBoltzmann`.
      let f : Edge (V := V) Λ → ℕ → ℝ :=
        fun e k => (β * J e * edgeSpin (V := V) (Λ := Λ) σ e) ^ k / (k.factorial : ℝ)
      have hf : ∀ e, Summable fun k : ℕ => ‖f e k‖ := by
        intro e
        simpa [f] using summable_norm_pow_div_factorial (x := β * J e * edgeSpin (V := V) (Λ := Λ) σ e)
      have hsumN : Summable (fun n : Current (V := V) Λ => ‖currTerm (E := Edge (V := V) Λ) f n‖) :=
        (tsum_pi_currTerm_eq_prod_tsum (E := Edge (V := V) Λ) f hf).1
      -- `currTerm` is exactly `weightReal * edgeMonomial`
      have hterm :
          ∀ n : Current (V := V) Λ,
            currTerm (E := Edge (V := V) Λ) f n
              = weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n := by
        intro n
        -- split each factor into a weight part and a spin part, then distribute the product
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
          -- `(β J e * edgeSpin)^k / k! = ((β J e)^k / k!) * (edgeSpin)^k`
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
                simp [weightReal, edgeMonomial, mul_assoc]
      have hsum : Summable (fun n : Current (V := V) Λ =>
          weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n) := by
        -- use `of_norm` with the `currTerm` summability
        have : Summable (fun n : Current (V := V) Λ =>
            ‖weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n‖) := by
          refine Summable.congr hsumN ?_
          intro n
          simpa [hterm n]
        exact this.of_norm
      -- multiply by the finite constant `(∏ x ∈ A, spinVal σ x)`
      simpa [mul_assoc] using hsum.mul_left (∏ x ∈ A, spinVal (Λ := Λ) σ x)
    -- now apply `Summable.tsum_finsetSum` and rewrite
    -- first push the constant `(∏ x∈A, spinVal σ x)` inside each `tsum`
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
      classical
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
    -- now swap the finite `∑ σ` with the `tsum` over currents
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
      classical
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
  -- evaluate the spin sum for each current using `edgeMonomial = vertexMonomial`
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
    -- factor out the weight and use the explicit spin-sum lemma
    have :
        (∑ σ : (↥Λ → Bool),
            (∏ x ∈ A, spinVal (Λ := Λ) σ x) *
              (weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n))
          =
          weightReal (V := V) (Λ := Λ) β J n *
            (∑ σ : (↥Λ → Bool), (∏ x ∈ A, spinVal (Λ := Λ) σ x) * vertexMonomial (V := V) (Λ := Λ) σ n) := by
      -- move the constant outside and replace `edgeMonomial` by `vertexMonomial`
      simp [hmono, mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
    -- now use the computed spin sum
    rw [this, sum_sigma_vertexMonomial_withSpin (V := V) (Λ := Λ) (n := n) (A := A)]
    by_cases hsrc : sources (V := V) n = A
    · simp [hsrc, mul_assoc, mul_comm, mul_left_comm]
    · simp [hsrc, mul_assoc, mul_comm, mul_left_comm]
  -- finish: rewrite the definition of `isingZWithSpin` using the expansion and collect terms
  unfold isingZWithSpin ZReal isingBoltzmann
  -- start from the definition, expand each boltzmann factor, swap sums, then simplify
  calc
    (∑ σ : (↥Λ → Bool),
        (∏ x ∈ A, spinVal (Λ := Λ) σ x) * (∏ e : Edge (V := V) Λ, Real.exp (β * J e * edgeSpin (V := V) (Λ := Λ) σ e)))
        =
        (∑ σ : (↥Λ → Bool),
          (∏ x ∈ A, spinVal (Λ := Λ) σ x) *
            (∑' n : Current (V := V) Λ,
              weightReal (V := V) (Λ := Λ) β J n * edgeMonomial (V := V) (Λ := Λ) σ n)) := by
            classical
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
            simpa [hb]
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
            -- pull out the constant factor
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

end RandomCurrent

end SpinGlass.Papers.Triviality4D
