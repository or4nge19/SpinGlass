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

@[simp]
lemma restrictInside_apply (S : Finset (↥Λ)) (n : Current (V := V) Λ) (e : Edge (V := V) Λ) :
    restrictInside (V := V) (Λ := Λ) S n e =
      if e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S then n e else 0 := rfl

@[simp]
lemma restrictOutside_apply (S : Finset (↥Λ)) (n : Current (V := V) Λ) (e : Edge (V := V) Λ) :
    restrictOutside (V := V) (Λ := Λ) S n e =
      if e.1.out.1 ∉ S ∧ e.1.out.2 ∉ S then n e else 0 := rfl

lemma restrictInside_idem (S : Finset (↥Λ)) (n : Current (V := V) Λ) :
    restrictInside (V := V) (Λ := Λ) S (restrictInside (V := V) (Λ := Λ) S n) =
      restrictInside (V := V) (Λ := Λ) S n := by
  ext e
  by_cases h : e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S <;> simp [restrictInside, h]

lemma restrictOutside_idem (S : Finset (↥Λ)) (n : Current (V := V) Λ) :
    restrictOutside (V := V) (Λ := Λ) S (restrictOutside (V := V) (Λ := Λ) S n) =
      restrictOutside (V := V) (Λ := Λ) S n := by
  ext e
  by_cases h : e.1.out.1 ∉ S ∧ e.1.out.2 ∉ S <;> simp [restrictOutside, h]

lemma restrictInside_add (S : Finset (↥Λ)) (n₁ n₂ : Current (V := V) Λ) :
    restrictInside (V := V) (Λ := Λ) S (n₁ + n₂) =
      restrictInside (V := V) (Λ := Λ) S n₁ + restrictInside (V := V) (Λ := Λ) S n₂ := by
  ext e
  by_cases h : e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S <;> simp [restrictInside, h]

lemma restrictOutside_add (S : Finset (↥Λ)) (n₁ n₂ : Current (V := V) Λ) :
    restrictOutside (V := V) (Λ := Λ) S (n₁ + n₂) =
      restrictOutside (V := V) (Λ := Λ) S n₁ + restrictOutside (V := V) (Λ := Λ) S n₂ := by
  ext e
  by_cases h : e.1.out.1 ∉ S ∧ e.1.out.2 ∉ S <;> simp [restrictOutside, h]

lemma restrictOutside_eq_zero_of_restrictInside_eq
    (S : Finset (↥Λ)) {n : Current (V := V) Λ} (hn : restrictInside (V := V) (Λ := Λ) S n = n) :
    restrictOutside (V := V) (Λ := Λ) S n = 0 := by
  ext e
  by_cases h : e.1.out.1 ∉ S ∧ e.1.out.2 ∉ S
  · have hnot : ¬ (e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S) := by
      intro hinside
      exact h.1 hinside.1
    have hn0 : n e = 0 := by
      have hn' :
          (if e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S then n e else 0) = n e := by
        simpa [restrictInside] using congrArg (fun f : Current (V := V) Λ => f e) hn
      simpa [hnot] using hn'.symm
    simp [restrictOutside, h, hn0]
  · simp [restrictOutside, h]

lemma restrictInside_eq_zero_of_restrictOutside_eq
    (S : Finset (↥Λ)) {n : Current (V := V) Λ} (hn : restrictOutside (V := V) (Λ := Λ) S n = n) :
    restrictInside (V := V) (Λ := Λ) S n = 0 := by
  ext e
  by_cases h : e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S
  · have hout : ¬ (e.1.out.1 ∉ S ∧ e.1.out.2 ∉ S) := by
      intro hout
      exact hout.1 h.1
    have hn0 : n e = 0 := by
      have hn' :
          (if e.1.out.1 ∉ S ∧ e.1.out.2 ∉ S then n e else 0) = n e := by
        simpa [restrictOutside] using congrArg (fun f : Current (V := V) Λ => f e) hn
      simpa [hout] using hn'.symm
    simp [restrictInside, h, hn0]
  · simp [restrictInside, h]

/-- Currents supported on edges with both endpoints in `S`. -/
def InsideCurrent (S : Finset (↥Λ)) : Type u :=
  {n : Current (V := V) Λ // restrictInside (V := V) (Λ := Λ) S n = n}

/-- Currents supported on edges with both endpoints in `Sᶜ`. -/
def OutsideCurrent (S : Finset (↥Λ)) : Type u :=
  {n : Current (V := V) Λ // restrictOutside (V := V) (Λ := Λ) S n = n}

/-- Currents with no flow across the cut `S`. -/
def NoCrossCurrent (S : Finset (↥Λ)) : Type u :=
  {n : Current (V := V) Λ // NoCross (V := V) (Λ := Λ) S n}

/-!
## Toward Lemma `lem:a` (equality in `eq:mm`)

The TeX proof factors the `n₂`-sum once we know that `n₂` carries no current across the boundary
of a cluster `T = C_{n₁+n₂}(S)`.  Our `NoCross` predicate and the `restrictInside`/`restrictOutside`
decomposition capture that situation. The next step is to expose a convenient `Equiv` between:

- currents with `NoCross S` and prescribed sources, and
- a pair of independent currents on the inside/outside parts with corresponding sources.

We introduce only the minimal API now (enough to factor sums in later lemmas).
-/

noncomputable def ZInsideReal (β : ℝ) (J : Edge (V := V) Λ → ℝ) (S : Finset (↥Λ))
    (A : Finset (↥Λ)) : ℝ :=
  ∑' nI : InsideCurrent (V := V) (Λ := Λ) S,
    if sources (V := V) nI.1 = A then weightReal (V := V) (Λ := Λ) β J nI.1 else 0

noncomputable def ZOutsideReal (β : ℝ) (J : Edge (V := V) Λ → ℝ) (S : Finset (↥Λ))
    (B : Finset (↥Λ)) : ℝ :=
  ∑' nO : OutsideCurrent (V := V) (Λ := Λ) S,
    if sources (V := V) nO.1 = B then weightReal (V := V) (Λ := Λ) β J nO.1 else 0

lemma sources_subset_of_mem_InsideCurrent
    (S : Finset (↥Λ)) (nI : InsideCurrent (V := V) (Λ := Λ) S) :
    sources (V := V) nI.1 ⊆ S := by
  -- rewrite `nI` as a `restrictInside` current and apply the general subset lemma
  simpa [nI.2] using
    (sources_restrictInside_subset (V := V) (Λ := Λ) (S := S) (n := nI.1))

lemma sources_subset_compl_of_mem_OutsideCurrent
    (S : Finset (↥Λ)) (nO : OutsideCurrent (V := V) (Λ := Λ) S) :
    sources (V := V) nO.1 ⊆ Sᶜ := by
  simpa [nO.2] using
    (sources_restrictOutside_subset_compl (V := V) (Λ := Λ) (S := S) (n := nO.1))

lemma disjoint_sources_of_mem_InsideOutside
    (S : Finset (↥Λ)) (nI : InsideCurrent (V := V) (Λ := Λ) S) (nO : OutsideCurrent (V := V) (Λ := Λ) S) :
    Disjoint (sources (V := V) nI.1) (sources (V := V) nO.1) := by
  refine Finset.disjoint_left.2 ?_
  intro x hxI hxO
  have hxS : x ∈ S := (sources_subset_of_mem_InsideCurrent (V := V) (Λ := Λ) S nI) hxI
  have hxSc : x ∈ Sᶜ := (sources_subset_compl_of_mem_OutsideCurrent (V := V) (Λ := Λ) S nO) hxO
  exact (Finset.not_mem_compl.2 hxS) hxSc

lemma sources_add_eq_union_of_mem_InsideOutside
    (S : Finset (↥Λ)) (nI : InsideCurrent (V := V) (Λ := Λ) S) (nO : OutsideCurrent (V := V) (Λ := Λ) S) :
    sources (V := V) (nI.1 + nO.1) =
        sources (V := V) nI.1 ∪ sources (V := V) nO.1 := by
  classical
  have hdisj : Disjoint (sources (V := V) nI.1) (sources (V := V) nO.1) :=
    disjoint_sources_of_mem_InsideOutside (V := V) (Λ := Λ) S nI nO
  simpa [sources_add, Finset.symmDiff_eq_union hdisj]

lemma weightReal_add_eq_mul_of_mem_InsideOutside
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (S : Finset (↥Λ))
    (nI : InsideCurrent (V := V) (Λ := Λ) S) (nO : OutsideCurrent (V := V) (Λ := Λ) S) :
    weightReal (V := V) (Λ := Λ) β J (nI.1 + nO.1)
      =
      weightReal (V := V) (Λ := Λ) β J nI.1 * weightReal (V := V) (Λ := Λ) β J nO.1 := by
  have hNC : NoCross (V := V) (Λ := Λ) S (nI.1 + nO.1) :=
    noCross_of_add_InsideOutside (V := V) (Λ := Λ) S nI nO
  have hfac :=
    weightReal_eq_mul_weightReal_restrictInside_restrictOutside (V := V) (Λ := Λ)
      (β := β) (J := J) (S := S) (n := (nI.1 + nO.1)) hNC
  have h0I : restrictInside (V := V) (Λ := Λ) S nO.1 = 0 :=
    restrictInside_eq_zero_of_restrictOutside_eq (V := V) (Λ := Λ) S nO.2
  have h0O : restrictOutside (V := V) (Λ := Λ) S nI.1 = 0 :=
    restrictOutside_eq_zero_of_restrictInside_eq (V := V) (Λ := Λ) S nI.2
  have hri :
      restrictInside (V := V) (Λ := Λ) S (nI.1 + nO.1) = nI.1 := by
    calc
      restrictInside (V := V) (Λ := Λ) S (nI.1 + nO.1)
          =
          restrictInside (V := V) (Λ := Λ) S nI.1 +
            restrictInside (V := V) (Λ := Λ) S nO.1 := by
              simpa using (restrictInside_add (V := V) (Λ := Λ) S nI.1 nO.1)
      _ = nI.1 := by simp [nI.2, h0I]
  have hro :
      restrictOutside (V := V) (Λ := Λ) S (nI.1 + nO.1) = nO.1 := by
    calc
      restrictOutside (V := V) (Λ := Λ) S (nI.1 + nO.1)
          =
          restrictOutside (V := V) (Λ := Λ) S nI.1 +
            restrictOutside (V := V) (Λ := Λ) S nO.1 := by
              simpa using (restrictOutside_add (V := V) (Λ := Λ) S nI.1 nO.1)
      _ = nO.1 := by simp [nO.2, h0O]
  simpa [hri, hro] using hfac

lemma ZReal_cutCoupling_eq_mul_ZInsideReal_ZOutsideReal_of_disjoint
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (S B : Finset (↥Λ)) (hdisj : Disjoint B S) :
    ZReal (V := V) (Λ := Λ) β (cutCoupling (V := V) (Λ := Λ) J S) B
      =
      ZInsideReal (V := V) (Λ := Λ) β J S (∅ : Finset (↥Λ)) *
        ZOutsideReal (V := V) (Λ := Λ) β J S B := by
  classical
  have hZ :=
    ZReal_cutCoupling_eq_tsum_ite_noCross (V := V) (Λ := Λ) (β := β) (J := J) (S := S) (B := B)
  let g : Current (V := V) Λ → ℝ :=
    fun n => if sources (V := V) n = B then weightReal (V := V) (Λ := Λ) β J n else 0
  have hrewrite :
      (fun n : Current (V := V) Λ =>
          if sources (V := V) n = B then
            (if NoCross (V := V) (Λ := Λ) S n then weightReal (V := V) (Λ := Λ) β J n else 0)
          else 0)
        =
        fun n : Current (V := V) Λ =>
          if NoCross (V := V) (Λ := Λ) S n then g n else 0 := by
    funext n
    by_cases hsrc : sources (V := V) n = B <;> by_cases hNC : NoCross (V := V) (Λ := Λ) S n <;>
      simp [g, hsrc, hNC]
  have hsubtype :
      (∑' n : Current (V := V) Λ,
          if NoCross (V := V) (Λ := Λ) S n then g n else 0)
        =
        ∑' n : NoCrossCurrent (V := V) (Λ := Λ) S, g n.1 := by
    -- use `tsum_subtype` with the set `{n | NoCross S n}`
    -- (rewrite the RHS as a subtype over that set)
    simpa [NoCrossCurrent, Set.indicator, Set.mem_setOf_eq] using
      (tsum_subtype (s := {n : Current (V := V) Λ | NoCross (V := V) (Λ := Λ) S n}) (f := g)).symm
  -- now apply the inside/outside equivalence
  let e := noCrossEquivInsideOutside (V := V) (Λ := Λ) S
  have he :
      (∑' n : NoCrossCurrent (V := V) (Λ := Λ) S, g n.1) =
        ∑' p : InsideCurrent (V := V) (Λ := Λ) S × OutsideCurrent (V := V) (Λ := Λ) S,
          g (p.1.1 + p.2.1) := by
    -- `e` is an equivalence, so we can rewrite `tsum` along it
    simpa [e] using (e.tsum_eq (f := fun p => g (p.1.1 + p.2.1))).symm
  -- put the pieces together
  have hZ' :
      ZReal (V := V) (Λ := Λ) β (cutCoupling (V := V) (Λ := Λ) J S) B
        =
        ∑' p : InsideCurrent (V := V) (Λ := Λ) S × OutsideCurrent (V := V) (Λ := Λ) S,
          g (p.1.1 + p.2.1) := by
    -- from `hZ`, `hrewrite`, `hsubtype`, `he`
    calc
      ZReal (V := V) (Λ := Λ) β (cutCoupling (V := V) (Λ := Λ) J S) B
          =
          ∑' n : Current (V := V) Λ,
            if sources (V := V) n = B then
              (if NoCross (V := V) (Λ := Λ) S n then weightReal (V := V) (Λ := Λ) β J n else 0)
            else 0 := hZ
      _ =
          ∑' n : Current (V := V) Λ,
            if NoCross (V := V) (Λ := Λ) S n then g n else 0 := by
              simp [hrewrite]
      _ =
          ∑' n : NoCrossCurrent (V := V) (Λ := Λ) S, g n.1 := hsubtype
      _ =
          ∑' p : InsideCurrent (V := V) (Λ := Λ) S × OutsideCurrent (V := V) (Λ := Λ) S,
            g (p.1.1 + p.2.1) := he
  -- simplify the integrand using disjointness of `B` and `S`
  have hIntegrand :
      (fun p : InsideCurrent (V := V) (Λ := Λ) S × OutsideCurrent (V := V) (Λ := Λ) S =>
        g (p.1.1 + p.2.1))
        =
        (fun p : InsideCurrent (V := V) (Λ := Λ) S × OutsideCurrent (V := V) (Λ := Λ) S =>
          (if sources (V := V) p.1.1 = (∅ : Finset (↥Λ)) ∧ sources (V := V) p.2.1 = B then
            weightReal (V := V) (Λ := Λ) β J p.1.1 * weightReal (V := V) (Λ := Λ) β J p.2.1
          else 0)) := by
    funext p
    -- abbreviations
    let nI := p.1
    let nO := p.2
    have hsrcUnion :
        sources (V := V) (nI.1 + nO.1) =
            sources (V := V) nI.1 ∪ sources (V := V) nO.1 :=
      sources_add_eq_union_of_mem_InsideOutside (V := V) (Λ := Λ) S nI nO
    have hdisjIO :
        Disjoint (sources (V := V) nI.1) (sources (V := V) nO.1) :=
      disjoint_sources_of_mem_InsideOutside (V := V) (Λ := Λ) S nI nO
    -- rewrite `g` and analyze the source condition
    by_cases hB : sources (V := V) (nI.1 + nO.1) = B
    · have hI0 : sources (V := V) nI.1 = (∅ : Finset (↥Λ)) := by
        -- `sources nI ⊆ S` and `sources (nI+nO) = B` with `B ⟂ S` forces emptiness
        have hsub : sources (V := V) nI.1 ⊆ S :=
          sources_subset_of_mem_InsideCurrent (V := V) (Λ := Λ) S nI
        -- `sources nI ⊆ B` since `B = sources nI ∪ sources nO`
        have hsubB : sources (V := V) nI.1 ⊆ B := by
          intro x hx
          have : x ∈ B := by
            have hxUnion : x ∈ sources (V := V) nI.1 ∪ sources (V := V) nO.1 :=
              Finset.mem_union.2 (Or.inl hx)
            simpa [hB, hsrcUnion] using hxUnion
          exact this
        -- show `sources nI` is empty using `Disjoint B S`
        refine (Finset.eq_empty_iff_forall_notMem).2 ?_
        intro x hxMem
        have hxS : x ∈ S := hsub hxMem
        have hxBmem : x ∈ B := hsubB hxMem
        exact (Finset.disjoint_left.1 hdisj hxBmem hxS)
      have hO : sources (V := V) nO.1 = B := by
        -- since sources(nI+nO)=B and sources nI = ∅, we must have sources nO = B
        have : B = sources (V := V) nI.1 ∪ sources (V := V) nO.1 := by
          simpa [hB, hsrcUnion] using rfl
        simpa [hI0] using this
      have hw :
          weightReal (V := V) (Λ := Λ) β J (nI.1 + nO.1)
            =
            weightReal (V := V) (Λ := Λ) β J nI.1 * weightReal (V := V) (Λ := Λ) β J nO.1 :=
        weightReal_add_eq_mul_of_mem_InsideOutside (V := V) (Λ := Λ) (β := β) (J := J) S nI nO
      simp [g, hB, hI0, hO, hw]
    · simp [g, hB]
  -- rewrite `hZ'` using the simplified integrand, and identify the product of `ZInsideReal` and `ZOutsideReal`
  rw [hZ']
  -- use the integrand simplification
  simp [hIntegrand, ZInsideReal, ZOutsideReal, tsum_mul_tsum_of_summable_norm]

lemma restrictInside_eq_self_of_mem_InsideCurrent
    (S : Finset (↥Λ)) (n : InsideCurrent (V := V) (Λ := Λ) S) :
    restrictInside (V := V) (Λ := Λ) S n.1 = n.1 :=
  n.2

lemma restrictOutside_eq_self_of_mem_OutsideCurrent
    (S : Finset (↥Λ)) (n : OutsideCurrent (V := V) (Λ := Λ) S) :
    restrictOutside (V := V) (Λ := Λ) S n.1 = n.1 :=
  n.2

lemma noCross_of_add_InsideOutside
    (S : Finset (↥Λ)) (nI : InsideCurrent (V := V) (Λ := Λ) S) (nO : OutsideCurrent (V := V) (Λ := Λ) S) :
    NoCross (V := V) (Λ := Λ) S (nI.1 + nO.1) := by
  intro e he
  have hI : nI.1 e = 0 := by
    have hnot : ¬ (e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S) := by
      intro hinside
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2 hinside.2
      · exact h1 hinside.1
    have hn' :
        (if e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S then nI.1 e else 0) = nI.1 e := by
      simpa [restrictInside] using congrArg (fun f : Current (V := V) Λ => f e) nI.2
    simpa [hnot] using hn'.symm
  have hO : nO.1 e = 0 := by
    have hnot : ¬ (e.1.out.1 ∉ S ∧ e.1.out.2 ∉ S) := by
      intro hout
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hout.1 h1
      · exact hout.2 h2
    have hn' :
        (if e.1.out.1 ∉ S ∧ e.1.out.2 ∉ S then nO.1 e else 0) = nO.1 e := by
      simpa [restrictOutside] using congrArg (fun f : Current (V := V) Λ => f e) nO.2
    simpa [hnot] using hn'.symm
  simp [hI, hO]

/--
An equivalence between `NoCross` currents and a pair of independent inside/outside currents.

This is the structural step needed to factor the `n₂`-sum in Lemma `lem:a` once the cut is given.
-/
noncomputable def noCrossEquivInsideOutside (S : Finset (↥Λ)) :
    NoCrossCurrent (V := V) (Λ := Λ) S ≃
      InsideCurrent (V := V) (Λ := Λ) S × OutsideCurrent (V := V) (Λ := Λ) S where
  toFun n :=
    (⟨restrictInside (V := V) (Λ := Λ) S n.1, restrictInside_idem (V := V) (Λ := Λ) S n.1⟩,
      ⟨restrictOutside (V := V) (Λ := Λ) S n.1, restrictOutside_idem (V := V) (Λ := Λ) S n.1⟩)
  invFun p :=
    ⟨p.1.1 + p.2.1, noCross_of_add_InsideOutside (V := V) (Λ := Λ) S p.1 p.2⟩
  left_inv n := by
    apply Subtype.ext
    ext e
    by_cases h1 : e.1.out.1 ∈ S <;> by_cases h2 : e.1.out.2 ∈ S
    · simp [restrictInside, restrictOutside, h1, h2]
    · have hz : n.1 e = 0 := n.2 e (Or.inl ⟨h1, h2⟩)
      simp [restrictInside, restrictOutside, h1, h2, hz]
    · have hz : n.1 e = 0 := n.2 e (Or.inr ⟨h1, h2⟩)
      simp [restrictInside, restrictOutside, h1, h2, hz]
    · simp [restrictInside, restrictOutside, h1, h2]
  right_inv p := by
    ext <;> apply Subtype.ext
    · have h0 :
          restrictInside (V := V) (Λ := Λ) S p.2.1 = 0 :=
        restrictInside_eq_zero_of_restrictOutside_eq (V := V) (Λ := Λ) S p.2.2
      calc
        restrictInside (V := V) (Λ := Λ) S (p.1.1 + p.2.1)
            =
            restrictInside (V := V) (Λ := Λ) S p.1.1 +
              restrictInside (V := V) (Λ := Λ) S p.2.1 := by
              simpa using (restrictInside_add (V := V) (Λ := Λ) S p.1.1 p.2.1)
        _ = p.1.1 := by simp [p.1.2, h0]
    · have h0 :
          restrictOutside (V := V) (Λ := Λ) S p.1.1 = 0 :=
        restrictOutside_eq_zero_of_restrictInside_eq (V := V) (Λ := Λ) S p.1.2
      calc
        restrictOutside (V := V) (Λ := Λ) S (p.1.1 + p.2.1)
            =
            restrictOutside (V := V) (Λ := Λ) S p.1.1 +
              restrictOutside (V := V) (Λ := Λ) S p.2.1 := by
              simpa using (restrictOutside_add (V := V) (Λ := Λ) S p.1.1 p.2.1)
        _ = p.2.1 := by simp [p.2.2, h0]

lemma degree_restrictInside_eq_zero_of_not_mem
    (S : Finset (↥Λ)) (n : Current (V := V) Λ) {x : ↥Λ} (hx : x ∉ S) :
    degree (V := V) (Λ := Λ) (restrictInside (V := V) (Λ := Λ) S n) x = 0 := by
  unfold degree restrictInside
  refine
    Fintype.sum_eq_zero
      (f := fun e : Edge (V := V) Λ =>
        if x ∈ (e.1 : Sym2 (↥Λ)) then
          if e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S then n e else 0
        else 0) ?_
  intro e
  by_cases hmem : x ∈ (e.1 : Sym2 (↥Λ))
  · have hxOut : x = e.1.out.1 ∨ x = e.1.out.2 := by
      have : x ∈ (s(e.1.out.1, e.1.out.2) : Sym2 (↥Λ)) := by
        simpa [e.1.out_eq] using hmem
      exact (Sym2.mem_iff (a := x) (b := e.1.out.1) (c := e.1.out.2)).1 this
    have hnot : ¬ (e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S) := by
      intro h
      rcases hxOut with rfl | rfl
      · exact hx h.1
      · exact hx h.2
    simp [hmem, hnot]
  · simp [hmem]

lemma degree_restrictOutside_eq_zero_of_mem
    (S : Finset (↥Λ)) (n : Current (V := V) Λ) {x : ↥Λ} (hx : x ∈ S) :
    degree (V := V) (Λ := Λ) (restrictOutside (V := V) (Λ := Λ) S n) x = 0 := by
  unfold degree restrictOutside
  refine
    Fintype.sum_eq_zero
      (f := fun e : Edge (V := V) Λ =>
        if x ∈ (e.1 : Sym2 (↥Λ)) then
          if e.1.out.1 ∉ S ∧ e.1.out.2 ∉ S then n e else 0
        else 0) ?_
  intro e
  by_cases hmem : x ∈ (e.1 : Sym2 (↥Λ))
  · have hxOut : x = e.1.out.1 ∨ x = e.1.out.2 := by
      have : x ∈ (s(e.1.out.1, e.1.out.2) : Sym2 (↥Λ)) := by
        simpa [e.1.out_eq] using hmem
      exact (Sym2.mem_iff (a := x) (b := e.1.out.1) (c := e.1.out.2)).1 this
    have hnot : ¬ (e.1.out.1 ∉ S ∧ e.1.out.2 ∉ S) := by
      intro h
      rcases hxOut with rfl | rfl
      · exact h.1 hx
      · exact h.2 hx
    simp [hmem, hnot]
  · simp [hmem]

lemma not_mem_sources_restrictInside_of_not_mem
    (S : Finset (↥Λ)) (n : Current (V := V) Λ) {x : ↥Λ} (hx : x ∉ S) :
    x ∉ sources (V := V) (restrictInside (V := V) (Λ := Λ) S n) := by
  intro hxSrc
  have hxIs :
      IsSource (V := V) (restrictInside (V := V) (Λ := Λ) S n) x :=
    (mem_sources_iff (V := V) (n := restrictInside (V := V) (Λ := Λ) S n) x).1 hxSrc
  have hxOdd :
      Odd (degree (V := V) (Λ := Λ) (restrictInside (V := V) (Λ := Λ) S n) x) := by
    simpa [IsSource] using hxIs
  have hdeg :
      degree (V := V) (Λ := Λ) (restrictInside (V := V) (Λ := Λ) S n) x = 0 :=
    degree_restrictInside_eq_zero_of_not_mem (V := V) (Λ := Λ) S n hx
  have : Odd 0 := by
    simp [hdeg] at hxOdd
  exact Nat.not_odd_zero this

lemma not_mem_sources_restrictOutside_of_mem
    (S : Finset (↥Λ)) (n : Current (V := V) Λ) {x : ↥Λ} (hx : x ∈ S) :
    x ∉ sources (V := V) (restrictOutside (V := V) (Λ := Λ) S n) := by
  intro hxSrc
  have hxIs :
      IsSource (V := V) (restrictOutside (V := V) (Λ := Λ) S n) x :=
    (mem_sources_iff (V := V) (n := restrictOutside (V := V) (Λ := Λ) S n) x).1 hxSrc
  have hxOdd :
      Odd (degree (V := V) (Λ := Λ) (restrictOutside (V := V) (Λ := Λ) S n) x) := by
    simpa [IsSource] using hxIs
  have hdeg :
      degree (V := V) (Λ := Λ) (restrictOutside (V := V) (Λ := Λ) S n) x = 0 :=
    degree_restrictOutside_eq_zero_of_mem (V := V) (Λ := Λ) S n hx
  have : Odd 0 := by
    simp [hdeg] at hxOdd
  exact Nat.not_odd_zero this

lemma sources_restrictInside_subset
    (S : Finset (↥Λ)) (n : Current (V := V) Λ) :
    sources (V := V) (restrictInside (V := V) (Λ := Λ) S n) ⊆ S := by
  intro x hxSrc
  by_contra hx
  exact (not_mem_sources_restrictInside_of_not_mem (V := V) (Λ := Λ) S n hx) hxSrc

lemma sources_restrictOutside_subset_compl
    (S : Finset (↥Λ)) (n : Current (V := V) Λ) :
    sources (V := V) (restrictOutside (V := V) (Λ := Λ) S n) ⊆ Sᶜ := by
  intro x hxSrc
  by_contra hx
  have hxS : x ∈ S := by simpa using hx
  exact (not_mem_sources_restrictOutside_of_mem (V := V) (Λ := Λ) S n hxS) hxSrc

lemma disjoint_sources_restrictInside_restrictOutside
    (S : Finset (↥Λ)) (n : Current (V := V) Λ) :
    Disjoint
        (sources (V := V) (restrictInside (V := V) (Λ := Λ) S n))
        (sources (V := V) (restrictOutside (V := V) (Λ := Λ) S n)) := by
  refine Finset.disjoint_left.2 ?_
  intro x hxIn hxOut
  have hxS :
      x ∈ S :=
    sources_restrictInside_subset (V := V) (Λ := Λ) S n hxIn
  have hxNotS :
      x ∉ S := by
    have : x ∈ Sᶜ := sources_restrictOutside_subset_compl (V := V) (Λ := Λ) S n hxOut
    simpa using this
  exact hxNotS hxS

lemma restrictInside_add_restrictOutside_eq_of_noCross
    (S : Finset (↥Λ)) (n : Current (V := V) Λ) (hNC : NoCross (V := V) (Λ := Λ) S n) :
    restrictInside (V := V) (Λ := Λ) S n + restrictOutside (V := V) (Λ := Λ) S n = n := by
  ext e
  by_cases h1 : e.1.out.1 ∈ S <;> by_cases h2 : e.1.out.2 ∈ S
  · simp [restrictInside, restrictOutside, h1, h2]
  · have hz : n e = 0 := hNC e (Or.inl ⟨h1, h2⟩)
    simp [restrictInside, restrictOutside, h1, h2, hz]
  · have hz : n e = 0 := hNC e (Or.inr ⟨h1, h2⟩)
    simp [restrictInside, restrictOutside, h1, h2, hz]
  · simp [restrictInside, restrictOutside, h1, h2]

lemma sources_eq_symmDiff_sources_restrictInside_restrictOutside_of_noCross
    (S : Finset (↥Λ)) (n : Current (V := V) Λ) (hNC : NoCross (V := V) (Λ := Λ) S n) :
    sources (V := V) n =
      symmDiff
        (sources (V := V) (restrictInside (V := V) (Λ := Λ) S n))
        (sources (V := V) (restrictOutside (V := V) (Λ := Λ) S n)) := by
  have hdecomp :
      restrictInside (V := V) (Λ := Λ) S n + restrictOutside (V := V) (Λ := Λ) S n = n :=
    restrictInside_add_restrictOutside_eq_of_noCross (V := V) (Λ := Λ) S n hNC
  simpa [hdecomp] using
    (sources_add (V := V)
      (n1 := restrictInside (V := V) (Λ := Λ) S n)
      (n2 := restrictOutside (V := V) (Λ := Λ) S n))

lemma sources_eq_union_sources_restrictInside_restrictOutside_of_noCross
    (S : Finset (↥Λ)) (n : Current (V := V) Λ) (hNC : NoCross (V := V) (Λ := Λ) S n) :
    sources (V := V) n =
        sources (V := V) (restrictInside (V := V) (Λ := Λ) S n) ∪
          sources (V := V) (restrictOutside (V := V) (Λ := Λ) S n) := by
  have hsymm :
      sources (V := V) n =
        symmDiff
          (sources (V := V) (restrictInside (V := V) (Λ := Λ) S n))
          (sources (V := V) (restrictOutside (V := V) (Λ := Λ) S n) ) :=
    sources_eq_symmDiff_sources_restrictInside_restrictOutside_of_noCross (V := V) (Λ := Λ) S n hNC
  have hdisj :
      Disjoint
          (sources (V := V) (restrictInside (V := V) (Λ := Λ) S n))
          (sources (V := V) (restrictOutside (V := V) (Λ := Λ) S n)) :=
    disjoint_sources_restrictInside_restrictOutside (V := V) (Λ := Λ) S n
  calc
    sources (V := V) n =
        symmDiff
          (sources (V := V) (restrictInside (V := V) (Λ := Λ) S n))
          (sources (V := V) (restrictOutside (V := V) (Λ := Λ) S n)) := hsymm
    _ =
        sources (V := V) (restrictInside (V := V) (Λ := Λ) S n) ∪
          sources (V := V) (restrictOutside (V := V) (Λ := Λ) S n) := by
        simpa using (Finset.symmDiff_eq_union hdisj)

lemma sources_restrictInside_eq_empty_of_noCross_of_disjoint_of_sources
    (S B : Finset (↥Λ)) (n : Current (V := V) Λ)
    (hNC : NoCross (V := V) (Λ := Λ) S n) (hdisj : Disjoint B S) (hsrc : sources (V := V) n = B) :
    sources (V := V) (restrictInside (V := V) (Λ := Λ) S n) = ∅ := by
  refine (Finset.eq_empty_iff_forall_notMem).2 ?_
  intro x hxIn
  have hxS : x ∈ S :=
    (sources_restrictInside_subset (V := V) (Λ := Λ) S n) hxIn
  have hB :
      B =
          sources (V := V) (restrictInside (V := V) (Λ := Λ) S n) ∪
            sources (V := V) (restrictOutside (V := V) (Λ := Λ) S n) := by
    simpa [hsrc] using
      (sources_eq_union_sources_restrictInside_restrictOutside_of_noCross (V := V) (Λ := Λ) S n hNC)
  have hxBmem : x ∈ B := by
    have hxUnion :
        x ∈
            sources (V := V) (restrictInside (V := V) (Λ := Λ) S n) ∪
              sources (V := V) (restrictOutside (V := V) (Λ := Λ) S n) :=
      Finset.mem_union.2 (Or.inl hxIn)
    simpa [hB] using hxUnion
  exact (Finset.disjoint_left.1 hdisj hxBmem hxS)

lemma sources_restrictOutside_eq_of_noCross_of_disjoint_of_sources
    (S B : Finset (↥Λ)) (n : Current (V := V) Λ)
    (hNC : NoCross (V := V) (Λ := Λ) S n) (hdisj : Disjoint B S) (hsrc : sources (V := V) n = B) :
    sources (V := V) (restrictOutside (V := V) (Λ := Λ) S n) = B := by
  set I := sources (V := V) (restrictInside (V := V) (Λ := Λ) S n)
  set O := sources (V := V) (restrictOutside (V := V) (Λ := Λ) S n)
  have hI0 :
      I = ∅ :=
    sources_restrictInside_eq_empty_of_noCross_of_disjoint_of_sources (V := V) (Λ := Λ) (S := S) (B := B)
      (n := n) hNC hdisj hsrc
  have hB : B = I ∪ O := by
    have hunion :
        sources (V := V) n = I ∪ O :=
      sources_eq_union_sources_restrictInside_restrictOutside_of_noCross (V := V) (Λ := Λ) S n hNC
    simpa [I, O, hsrc] using hunion
  have : B = O := by
    simpa [hI0, I, O] using hB
  simpa [O] using this.symm

lemma weightReal_eq_mul_weightReal_restrictInside_restrictOutside
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) (S : Finset (↥Λ)) (n : Current (V := V) Λ)
    (hzero : ∀ e : Edge (V := V) Λ, EdgeCross (V := V) (Λ := Λ) S e → n e = 0) :
    weightReal (V := V) (Λ := Λ) β J n
      =
      weightReal (V := V) (Λ := Λ) β J (restrictInside (V := V) (Λ := Λ) S n) *
        weightReal (V := V) (Λ := Λ) β J (restrictOutside (V := V) (Λ := Λ) S n) := by
  unfold weightReal restrictInside restrictOutside
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
    · simp [h1, h2]
    · have hz : n e = 0 := hzero e (Or.inl ⟨h1, h2⟩)
      simp [h1, h2, hz]
    · have hz : n e = 0 := hzero e (Or.inr ⟨h1, h2⟩)
      simp [h1, h2, hz]
    · simp [h1, h2]
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
