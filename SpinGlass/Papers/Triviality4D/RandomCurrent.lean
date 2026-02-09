import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.Ring.Parity

/-!
# Random current representation (finite volume): definitions + paper-facing API

This file sets up the *combinatorial* objects used by the random current representation of the
ferromagnetic Ising model (paper Section 1.5):

- currents `n : Sym2 Λ → ℕ` on a finite vertex set `Λ`,
- the set of sources `∂n`,
- connectivity in the multigraph trace `{e | n e > 0}`,
- weights `w(n)`,
- and the associated normalized “probabilities” expressed as ratios of `∑'` weights.

At this stage we only provide the **definition layer** and a small core API.  The switching lemma,
mixing statements, etc. will be stated in terms of these objects and proved later.
-/

open scoped BigOperators
open scoped ENNReal

open Filter Topology

namespace SpinGlass.Papers.Triviality4D

namespace RandomCurrent

universe u

variable {V : Type u} [DecidableEq V]

/-! ## Currents on a finite vertex set -/

/-- An unordered **off-diagonal** edge in `Λ`, i.e. an element of `Sym2 (↥Λ)` not on the diagonal. -/
abbrev Edge (Λ : Finset V) : Type u :=
  {e : Sym2 (↥Λ) // ¬ Sym2.IsDiag e}

/--
A (finite-volume) current on the vertex set `Λ`: an `ℕ`-valued function on unordered **off-diagonal**
edges.

This matches the paper convention where currents live on unordered pairs `{x,y}` with `x ≠ y`.
-/
abbrev Current (Λ : Finset V) : Type u :=
  Edge (V := V) Λ → ℕ

/-- The off-diagonal edge `{x,y}` as an element of `Edge Λ`. -/
def edge {Λ : Finset V} (x y : ↥Λ) (hxy : x ≠ y) : Edge (V := V) Λ :=
  ⟨s(x, y), by
    -- `Sym2.IsDiag (s(x,y)) ↔ x = y`
    simpa [Sym2.mk_isDiag_iff] using hxy⟩

/-- Pointwise order on currents (sub-current relation). -/
def CurrentLE {Λ : Finset V} (m n : Current (V := V) Λ) : Prop :=
  ∀ e, m e ≤ n e

/-! ## Sources `∂n` -/

/-- The total current incident to a vertex `x` (sum of `n(e)` over edges `e` incident to `x`). -/
def degree {Λ : Finset V} (n : Current (V := V) Λ) (x : ↥Λ) : ℕ :=
  ∑ e : Edge (V := V) Λ, if x ∈ (e.1 : Sym2 (↥Λ)) then n e else 0

/-- The source predicate (odd incident degree). -/
def IsSource {Λ : Finset V} (n : Current (V := V) Λ) (x : ↥Λ) : Prop :=
  Odd (degree (V := V) n x)

/-- `IsSource n` is decidable (since `Odd` is decidable on `ℕ`). -/
instance {Λ : Finset V} (n : Current (V := V) Λ) : DecidablePred (IsSource (V := V) n) := by
  intro x
  dsimp [IsSource]
  infer_instance

/-- The set of sources `∂n` as a `Finset`. -/
noncomputable def sources {Λ : Finset V} (n : Current (V := V) Λ) : Finset (↥Λ) :=
  (Finset.univ.filter fun x => IsSource (V := V) n x)

lemma mem_sources_iff {Λ : Finset V} (n : Current (V := V) Λ) (x : ↥Λ) :
    x ∈ sources (V := V) n ↔ IsSource (V := V) n x := by
  classical
  simp [sources]

/-! ## Sources under current addition -/

lemma degree_add {Λ : Finset V} (n1 n2 : Current (V := V) Λ) (x : ↥Λ) :
    degree (V := V) (n1 + n2) x = degree (V := V) n1 x + degree (V := V) n2 x := by
  classical
  simp [degree]
  have hintegrand :
      (fun e : Edge (V := V) Λ => if x ∈ (e.1 : Sym2 (↥Λ)) then n1 e + n2 e else 0) =
        (fun e : Edge (V := V) Λ =>
          (if x ∈ (e.1 : Sym2 (↥Λ)) then n1 e else 0) +
            (if x ∈ (e.1 : Sym2 (↥Λ)) then n2 e else 0)) := by
    funext e
    by_cases hx : x ∈ (e.1 : Sym2 (↥Λ)) <;> simp [hx]
  simpa [hintegrand] using
    (Finset.sum_add_distrib (s := (Finset.univ : Finset (Edge (V := V) Λ)))
      (f := fun e : Edge (V := V) Λ => if x ∈ (e.1 : Sym2 (↥Λ)) then n1 e else 0)
      (g := fun e : Edge (V := V) Λ => if x ∈ (e.1 : Sym2 (↥Λ)) then n2 e else 0))

lemma sources_add {Λ : Finset V} (n1 n2 : Current (V := V) Λ) :
    sources (V := V) (n1 + n2) =
      symmDiff (sources (V := V) n1) (sources (V := V) n2) := by
  classical
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

/-! ### Handshaking lemma for current sources -/

lemma sum_degree_eq_two_mul_sum_current {Λ : Finset V} (n : Current (V := V) Λ) :
    (∑ x : ↥Λ, degree (V := V) n x) = 2 * ∑ e : Edge (V := V) Λ, n e := by
  classical
  have hswap :
      (∑ x : ↥Λ, ∑ e : Edge (V := V) Λ,
          if x ∈ (e.1 : Sym2 (↥Λ)) then n e else 0)
        =
        ∑ e : Edge (V := V) Λ, ∑ x : ↥Λ,
          if x ∈ (e.1 : Sym2 (↥Λ)) then n e else 0 := by
    simpa using
      (Finset.sum_comm (s := (Finset.univ : Finset (↥Λ))) (t := (Finset.univ : Finset (Edge (V := V) Λ)))
        (f := fun x e => if x ∈ (e.1 : Sym2 (↥Λ)) then n e else 0))
  have hinner :
      ∀ e : Edge (V := V) Λ,
        (∑ x : ↥Λ, if x ∈ (e.1 : Sym2 (↥Λ)) then n e else 0) = 2 * n e := by
    intro e
    let p : ↥Λ → Prop := fun x => x ∈ (e.1 : Sym2 (↥Λ))
    have hfilter :
        (Finset.univ.filter fun x : ↥Λ => p x) = (e.1 : Sym2 (↥Λ)).toFinset := by
      ext x
      simp [p, Sym2.mem_toFinset]
    calc
      (∑ x : ↥Λ, if p x then n e else 0)
          = ∑ x ∈ (Finset.univ : Finset (↥Λ)), if p x then n e else 0 := by simp
      _ = ∑ x ∈ (Finset.univ.filter fun x : ↥Λ => p x), n e := by
            simpa [p] using
              (Finset.sum_filter (s := (Finset.univ : Finset (↥Λ)))
                (f := fun _x : ↥Λ => n e) (p := p)).symm
      _ = ∑ x ∈ (e.1 : Sym2 (↥Λ)).toFinset, n e := by
            simpa using
              congrArg (fun t : Finset (↥Λ) => (∑ x ∈ t, n e)) hfilter
      _ = ((e.1 : Sym2 (↥Λ)).toFinset.card) * n e := by simp
      _ = 2 * n e := by
            simpa using congrArg (fun k => k * n e) (Sym2.card_toFinset_of_not_isDiag (z := (e.1 : Sym2 (↥Λ))) e.2)
  have hsum :
      (∑ x : ↥Λ, degree (V := V) n x)
        = ∑ e : Edge (V := V) Λ, 2 * n e := by
    classical
    calc
      (∑ x : ↥Λ, degree (V := V) n x)
          = ∑ x : ↥Λ, ∑ e : Edge (V := V) Λ,
              if x ∈ (e.1 : Sym2 (↥Λ)) then n e else 0 := by
                rfl
      _ = ∑ e : Edge (V := V) Λ, ∑ x : ↥Λ,
              if x ∈ (e.1 : Sym2 (↥Λ)) then n e else 0 := by
                simpa using hswap
      _ = ∑ e : Edge (V := V) Λ, 2 * n e := by
                apply Fintype.sum_congr
                intro e
                simpa using hinner e
  simpa using (hsum.trans (by
    simpa using
      (Finset.mul_sum (a := (2 : ℕ)) (s := (Finset.univ : Finset (Edge (V := V) Λ)))
        (f := fun e : Edge (V := V) Λ => n e)).symm))

lemma even_card_sources {Λ : Finset V} (n : Current (V := V) Λ) :
    Even (sources (V := V) n).card := by
  classical
  have hsum :
      (∑ x : ↥Λ, degree (V := V) n x) = 2 * ∑ e : Edge (V := V) Λ, n e :=
    sum_degree_eq_two_mul_sum_current (V := V) (Λ := Λ) n
  have hEvenSum : Even (∑ x ∈ (Finset.univ : Finset (↥Λ)), degree (V := V) n x) := by
    refine ⟨∑ e : Edge (V := V) Λ, n e, ?_⟩
    simpa [two_mul] using hsum
  have hEvenOdd :=
    (Finset.even_sum_iff_even_card_odd (s := (Finset.univ : Finset (↥Λ)))
      (f := fun x : ↥Λ => degree (V := V) n x)).1 hEvenSum
  simpa [sources, IsSource] using hEvenOdd

/-! ## Connectivity in the trace graph -/

/-- Adjacency relation induced by a current: `x ~ y` iff `x ≠ y` and `n({x,y}) > 0`. -/
def Adj {Λ : Finset V} (n : Current (V := V) Λ) (x y : ↥Λ) : Prop :=
  ∃ hxy : x ≠ y, 0 < n (edge (V := V) x y hxy)

omit [DecidableEq V] in
lemma Adj_comm {Λ : Finset V} (n : Current (V := V) Λ) {x y : ↥Λ} :
    Adj (V := V) n x y ↔ Adj (V := V) n y x := by
  constructor
  · rintro ⟨hxy, h⟩
    refine ⟨hxy.symm, ?_⟩
    have he : edge (V := V) y x hxy.symm = edge (V := V) x y hxy := by
      apply Subtype.ext
      simp [edge]
    simpa [he] using h
  · rintro ⟨hyx, h⟩
    refine ⟨hyx.symm, ?_⟩
    have he : edge (V := V) x y hyx.symm = edge (V := V) y x hyx := by
      apply Subtype.ext
      simp [edge]
    simpa [he] using h

/-- Connectivity (existence of a path of positive-current edges). -/
def Connected {Λ : Finset V} (n : Current (V := V) Λ) (x y : ↥Λ) : Prop :=
  Relation.ReflTransGen (Adj (V := V) n) x y

omit [DecidableEq V] in
lemma Connected.refl {Λ : Finset V} (n : Current (V := V) Λ) (x : ↥Λ) :
    Connected (V := V) n x x :=
  Relation.ReflTransGen.refl

/-! ### Basic API for connectivity -/

omit [DecidableEq V] in
lemma Adj.mono {Λ : Finset V} {m n : Current (V := V) Λ} (hmn : CurrentLE (V := V) m n)
    {x y : ↥Λ} (h : Adj (V := V) m x y) :
    Adj (V := V) n x y := by
  rcases h with ⟨hxy, hpos⟩
  refine ⟨hxy, lt_of_lt_of_le hpos (hmn _ )⟩

omit [DecidableEq V] in
lemma Connected.mono {Λ : Finset V} {m n : Current (V := V) Λ} (hmn : CurrentLE (V := V) m n)
    {x y : ↥Λ} (h : Connected (V := V) m x y) :
    Connected (V := V) n x y := by
  refine Relation.ReflTransGen.mono (p := Adj (V := V) n) ?_ h
  intro a b hab
  exact Adj.mono (V := V) (Λ := Λ) hmn hab

omit [DecidableEq V] in
lemma Connected.trans {Λ : Finset V} (n : Current (V := V) Λ) {x y z : ↥Λ} :
    Connected (V := V) n x y → Connected (V := V) n y z → Connected (V := V) n x z :=
  Relation.ReflTransGen.trans

omit [DecidableEq V] in
lemma Connected.symm {Λ : Finset V} (n : Current (V := V) Λ) {x y : ↥Λ} :
    Connected (V := V) n x y → Connected (V := V) n y x := by
  have hs : Symmetric (Adj (V := V) n) := by
    intro a b hab
    exact (Adj_comm (V := V) (Λ := Λ) n (x := a) (y := b)).1 hab
  intro hxy
  exact (Relation.ReflTransGen.symmetric hs) hxy

/-! ### Clusters -/

/-- The cluster of `x` in a current `n`: the set of vertices connected to `x`. -/
def cluster {Λ : Finset V} (n : Current (V := V) Λ) (x : ↥Λ) : Set (↥Λ) :=
  {y | Connected (V := V) n x y}

omit [DecidableEq V] in
lemma mem_cluster_iff {Λ : Finset V} (n : Current (V := V) Λ) (x y : ↥Λ) :
    y ∈ cluster (V := V) n x ↔ Connected (V := V) n x y := by
  rfl

omit [DecidableEq V] in
lemma mem_cluster_self {Λ : Finset V} (n : Current (V := V) Λ) (x : ↥Λ) :
    x ∈ cluster (V := V) n x := by
  simpa [cluster] using (Connected.refl (V := V) (Λ := Λ) n x)

omit [DecidableEq V] in
lemma cluster_inter_nonempty_iff_connected {Λ : Finset V} (n : Current (V := V) Λ) (x z : ↥Λ) :
    Set.Nonempty (cluster (V := V) n x ∩ cluster (V := V) n z) ↔ Connected (V := V) n x z := by
  constructor
  · rintro ⟨y, ⟨hyx, hyz⟩⟩
    have hyz' : Connected (V := V) n y z := (Connected.symm (V := V) (Λ := Λ) n hyz)
    exact (Connected.trans (V := V) (Λ := Λ) n hyx hyz')
  · intro hxz
    refine ⟨z, ?_, ?_⟩
    · exact hxz
    · simpa [cluster] using (Connected.refl (V := V) (Λ := Λ) n z)

/-! ## The event `ℱ_B`: existence of a subcurrent with sources `B` -/

/-- `HasSubCurrent n B` means: there exists a subcurrent `m ≤ n` with `sources m = B`. -/
def HasSubCurrent {Λ : Finset V} (n : Current (V := V) Λ) (B : Finset (↥Λ)) : Prop :=
  ∃ m : Current (V := V) Λ, CurrentLE (V := V) m n ∧ sources (V := V) m = B

/-! ## Random current weights and normalizations -/

/--
The random current weight
\[
w(n) = \prod_{\{x,y\} \subset Λ} \frac{(\beta J_{x,y})^{n(x,y)}}{n(x,y)!}.
\]

We package it as an `ℝ≥0∞`-valued function using `ENNReal.ofReal` so that infinite sums are always
well-typed.
-/
noncomputable def weight
    (β : ℝ) (J : V → V → ℝ) {Λ : Finset V} (n : Current (V := V) Λ) : ℝ≥0∞ :=
  ∏ e : Edge (V := V) Λ,
    ENNReal.ofReal
      (((β * J (e.1.out.1 : V) (e.1.out.2 : V)) ^ (n e)) /
        ((Nat.factorial (n e) : ℕ) : ℝ))

/-- Edge-coupling version of `weight`, avoiding the arbitrary `out` ordering at the API boundary. -/
noncomputable def weightEdge
    (β : ℝ) {Λ : Finset V} (J : Edge (V := V) Λ → ℝ) (n : Current (V := V) Λ) : ℝ≥0∞ :=
  ∏ e : Edge (V := V) Λ,
    ENNReal.ofReal
      (((β * J e) ^ (n e)) / ((Nat.factorial (n e) : ℕ) : ℝ))

/-- The source-constrained partition function `Z_B = ∑_{n : ∂n = B} w(n)` (as `ℝ≥0∞`). -/
noncomputable def Z
    (β : ℝ) (J : V → V → ℝ) {Λ : Finset V} (B : Finset (↥Λ)) : ℝ≥0∞ := by
  classical
  exact ∑' n : Current (V := V) Λ, if sources (V := V) n = B then weight (V := V) β J n else 0

/-- Edge-coupling version of `Z`, using `weightEdge`. -/
noncomputable def ZEdge
    (β : ℝ) {Λ : Finset V} (J : Edge (V := V) Λ → ℝ) (B : Finset (↥Λ)) : ℝ≥0∞ :=
by
  classical
  exact ∑' n : Current (V := V) Λ, if sources (V := V) n = B then weightEdge (V := V) β J n else 0

/--
“Probability” of an event under the source-constrained random current law, as a ratio of weights.

This is a *definition-level* object: to upgrade it to a genuine probability measure one will prove
`Z ≠ 0` and `Z ≠ ⊤` (and measurability) in a later module.
-/
noncomputable def P
    (β : ℝ) (J : V → V → ℝ) {Λ : Finset V} (B : Finset (↥Λ)) (E : Set (Current (V := V) Λ)) : ℝ≥0∞ := by
  classical
  exact
    (∑' n : Current (V := V) Λ,
        if sources (V := V) n = B ∧ n ∈ E then weight (V := V) β J n else 0) /
      Z (V := V) β J B

end RandomCurrent

end SpinGlass.Papers.Triviality4D
