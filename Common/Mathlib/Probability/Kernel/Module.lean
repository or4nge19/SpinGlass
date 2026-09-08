/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.Module

/-!
# Kernels form a module over the scalars that act on measures

`MeasureTheory.Measure` is a module over any semiring acting on `ℝ≥0∞` by scalar tower
(`MeasureTheory.Measure.instModule`), but `ProbabilityTheory.Kernel` carries only the `ℕ`-action
inherited from its additive monoid structure. Scaling a kernel is nevertheless the most basic
operation one performs on it: every explicit mixture kernel — a conditional distribution written
as a convex combination of a fixed law and finitely many point masses, say — is built from `+`,
`•` and `Kernel.deterministic`.

This file supplies the missing action. A kernel is a *measurable* family of measures and the
scalar action on measures is pointwise, so the whole `Measure`-side algebra transports verbatim
through `DFunLike`: `smul_apply` holds definitionally and the module axioms come from
`FunLike.module`.

## Main statements

- `ProbabilityTheory.Kernel.instSMul`, `ProbabilityTheory.Kernel.instModule`.
- `ProbabilityTheory.Kernel.isFiniteKernel_smul`: a finite multiple of a finite kernel is finite.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α β : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
variable {R : Type*} [Semiring R] [Module R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]

/-- Scalar multiplication of a kernel, pointwise on measures.

This is stated for the same scalars that act on `MeasureTheory.Measure`; the `ℕ`-action it
specialises to agrees definitionally with `ProbabilityTheory.Kernel.instSMulNat`. -/
noncomputable instance instSMul : SMul R (Kernel α β) where
  smul c κ :=
    ⟨fun a => c • κ a, Measure.measurable_measure.2 fun s hs => by
      have key : (fun a => (c • κ a) s) = fun a => (c • (1 : ℝ≥0∞)) * κ a s := by
        funext a; rw [Measure.smul_apply, smul_one_mul]
      change Measurable fun a => (c • κ a) s
      rw [key]
      exact (κ.measurable_coe hs).const_mul _⟩

instance : IsSMulApply R (Kernel α β) α (Measure β) where
  smul_apply _ _ _ := rfl

@[simp] lemma smul_apply' (c : R) (κ : Kernel α β) (a : α) (s : Set β) :
    (c • κ) a s = c • κ a s := rfl

noncomputable instance instModule : Module R (Kernel α β) := FunLike.module

/-- A finite multiple of a finite kernel is a finite kernel. -/
lemma isFiniteKernel_smul {c : ℝ≥0∞} (hc : c ≠ ∞) (κ : Kernel α β) [IsFiniteKernel κ] :
    IsFiniteKernel (c • κ) := by
  refine ⟨⟨c * κ.bound, ENNReal.mul_lt_top hc.lt_top κ.bound_lt_top, fun a => ?_⟩⟩
  simpa using mul_le_mul' (le_refl c) (κ.measure_le_bound a Set.univ)

end ProbabilityTheory.Kernel
