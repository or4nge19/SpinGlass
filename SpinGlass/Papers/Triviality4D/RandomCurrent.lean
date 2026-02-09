import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

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

/-! ### Clusters -/

/-- The cluster of `x` in a current `n`: the set of vertices connected to `x`. -/
def cluster {Λ : Finset V} (n : Current (V := V) Λ) (x : ↥Λ) : Set (↥Λ) :=
  {y | Connected (V := V) n x y}

lemma mem_cluster_iff {Λ : Finset V} (n : Current (V := V) Λ) (x y : ↥Λ) :
    y ∈ cluster (V := V) n x ↔ Connected (V := V) n x y := by
  rfl

omit [DecidableEq V] in
lemma mem_cluster_self {Λ : Finset V} (n : Current (V := V) Λ) (x : ↥Λ) :
    x ∈ cluster (V := V) n x := by
  simpa [cluster] using (Connected.refl (V := V) (Λ := Λ) n x)

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
    (β : ℝ) (J : V → V → ℝ) {Λ : Finset V} (B : Finset (↥Λ)) : ℝ≥0∞ :=
by
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
    (β : ℝ) (J : V → V → ℝ) {Λ : Finset V} (B : Finset (↥Λ)) (E : Set (Current (V := V) Λ)) : ℝ≥0∞ :=
by
  classical
  exact
    (∑' n : Current (V := V) Λ,
        if sources (V := V) n = B ∧ n ∈ E then weight (V := V) β J n else 0) /
      Z (V := V) β J B

end RandomCurrent

end SpinGlass.Papers.Triviality4D
