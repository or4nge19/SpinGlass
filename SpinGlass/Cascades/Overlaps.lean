import SpinGlass.ReplicaMeasure
import SpinGlass.Defs

/-!
# Vol II infrastructure: overlap arrays from replicas

Talagrand Vol II (and Panchenko/Georgii) treat the Gibbs object primarily through the joint law of
finitely many replicas and their **overlap array**.

This file is deliberately lightweight: it only defines overlap arrays as functions on a replica
tuple, with minimal algebraic lemmas. This is the right abstraction layer before proving:

- ultrametricity statements (laws on arrays),
- Ghirlanda–Guerra identities (expectations of functions of overlap arrays),
- representation theorems (Aldous–Hoover / Dovbysh–Sudakov style).
-/

namespace SpinGlass

open scoped BigOperators

namespace Cascades

section General

universe u

variable {β : Type u} (R : β → β → ℝ) {n : ℕ}

/-- The overlap matrix induced by `R` on an `n`-tuple of replicas. -/
def overlapMatrix (σs : Fin n → β) : Fin n → Fin n → ℝ :=
  fun i j => R (σs i) (σs j)

@[simp] lemma overlapMatrix_apply (σs : Fin n → β) (i j : Fin n) :
    overlapMatrix (R := R) σs i j = R (σs i) (σs j) := rfl

lemma overlapMatrix_symm (hR : ∀ x y, R x y = R y x) (σs : Fin n → β) (i j : Fin n) :
    overlapMatrix (R := R) σs i j = overlapMatrix (R := R) σs j i := by
  simpa [overlapMatrix] using hR (σs i) (σs j)

end General

section SpinGlass

variable {N n : ℕ}

/-- Symmetry of the SK overlap. -/
lemma overlap_symm (N : ℕ) (σ τ : Config N) : overlap N σ τ = overlap N τ σ := by
  classical
  simp [SpinGlass.overlap, mul_comm]

/-- The overlap matrix on `n` replicas in the SK configuration space. -/
noncomputable def skOverlapMatrix (N : ℕ) (σs : ReplicaSpace N n) : Fin n → Fin n → ℝ :=
  overlapMatrix (R := overlap N) σs

@[simp] lemma skOverlapMatrix_apply (N : ℕ) (σs : ReplicaSpace N n) (i j : Fin n) :
    skOverlapMatrix (N := N) σs i j = overlap N (σs i) (σs j) := rfl

lemma skOverlapMatrix_symm (N : ℕ) (σs : ReplicaSpace N n) (i j : Fin n) :
    skOverlapMatrix (N := N) σs i j = skOverlapMatrix (N := N) σs j i := by
  simpa [skOverlapMatrix, overlapMatrix] using overlap_symm (N := N) (σ := σs i) (τ := σs j)

end SpinGlass

end Cascades

end SpinGlass
