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

variable {V : Type u}

/-! ## Currents on a finite vertex set -/

/-- A (finite-volume) current on the vertex set `Λ`: an `ℕ`-valued function on unordered pairs. -/
abbrev Current (Λ : Finset V) : Type u :=
  Sym2 (↥Λ) → ℕ

/-- Pointwise order on currents (sub-current relation). -/
def CurrentLE {Λ : Finset V} (m n : Current (V := V) Λ) : Prop :=
  ∀ e, m e ≤ n e

/-! ## Sources `∂n` -/

/-- The total current incident to a vertex `x`. -/
def degree {Λ : Finset V} (n : Current (V := V) Λ) (x : ↥Λ) : ℕ :=
  ∑ y : ↥Λ, n (s(x, y))

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

/-- Adjacency relation induced by a current: `x ~ y` iff `n(s(x,y)) > 0`. -/
def Adj {Λ : Finset V} (n : Current (V := V) Λ) (x y : ↥Λ) : Prop :=
  0 < n (s(x, y))

lemma Adj_comm {Λ : Finset V} (n : Current (V := V) Λ) {x y : ↥Λ} :
    Adj (V := V) n x y ↔ Adj (V := V) n y x := by
  have hs : (s(y, x) : Sym2 (↥Λ)) = s(x, y) := by
    simp
  constructor <;> intro h <;> simpa [Adj, hs] using h

/-- Connectivity (existence of a path of positive-current edges). -/
def Connected {Λ : Finset V} (n : Current (V := V) Λ) (x y : ↥Λ) : Prop :=
  Relation.ReflTransGen (Adj (V := V) n) x y

lemma Connected.refl {Λ : Finset V} (n : Current (V := V) Λ) (x : ↥Λ) :
    Connected (V := V) n x x :=
  Relation.ReflTransGen.refl

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
  ∏ e : Sym2 (↥Λ),
    ENNReal.ofReal
      (((β * J (e.out.1 : V) (e.out.2 : V)) ^ (n e)) /
        ((Nat.factorial (n e) : ℕ) : ℝ))

/-- The source-constrained partition function `Z_B = ∑_{n : ∂n = B} w(n)` (as `ℝ≥0∞`). -/
noncomputable def Z
    (β : ℝ) (J : V → V → ℝ) {Λ : Finset V} (B : Finset (↥Λ)) : ℝ≥0∞ :=
by
  classical
  exact ∑' n : Current (V := V) Λ, if sources (V := V) n = B then weight (V := V) β J n else 0

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

