import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.MeasureTheory.MeasurableSpace.PreorderRestrict
import Mathlib.Order.Restriction

/-!
# Prefix-dependent processes

Time-inhomogeneous process as kernels `κ n : Kernel (Π i : Iic n, X i) (X (n+1))`. Main: `traj`,
`trajMeasure`, `condDistrib_trajMeasure`. Specializes Mathlib's trajectory-kernel API.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SpinGlass

namespace Cascades

universe u

variable {X : ℕ → Type u} [∀ n, MeasurableSpace (X n)]

open ProbabilityTheory.Kernel

/-- Prefix space up to time `n` (indices `≤ n`), as a dependent function on `Iic n`. -/
abbrev Prefix (X : ℕ → Type u) (n : ℕ) : Type u := (i : Finset.Iic n) → X (i : ℕ)

/-- A prefix-dependent process kernel family `κ`. -/
abbrev ProcessKernelFamily (X : ℕ → Type u) [∀ n, MeasurableSpace (X n)] : Type _ :=
  (n : ℕ) → Kernel (Prefix X n) (X (n + 1))

section

variable (κ : ProcessKernelFamily X) [∀ n, IsMarkovKernel (κ n)]

/-- The infinite-trajectory kernel (Ionescu–Tulcea) continuing a prefix up to time `a`. -/
noncomputable abbrev processTraj (a : ℕ) : Kernel (Prefix (X := X) a) (Π n, X n) :=
  ProbabilityTheory.Kernel.traj (κ := κ) a

/-- The finite marginal kernel from a prefix up to `a` to a prefix up to `b`. -/
noncomputable abbrev processPartialTraj (a b : ℕ) :
    Kernel (Prefix (X := X) a) (Prefix (X := X) b) :=
  ProbabilityTheory.Kernel.partialTraj (κ := κ) a b

instance (a : ℕ) : IsMarkovKernel (processTraj (X := X) κ a) := by
  dsimp [processTraj]
  infer_instance

instance (a b : ℕ) : IsMarkovKernel (processPartialTraj (X := X) κ a b) := by
  dsimp [processPartialTraj]
  infer_instance

/-- The distribution of the full trajectory when `X 0` has law `μ₀`. -/
noncomputable abbrev processTrajMeasure (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀] :
    Measure (Π n, X n) :=
  ProbabilityTheory.Kernel.trajMeasure (μ₀ := μ₀) κ

instance (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀] :
    IsProbabilityMeasure (processTrajMeasure (X := X) κ μ₀) := by
  dsimp [processTrajMeasure]
  infer_instance

/-- Under `trajMeasure μ₀ κ`, the conditional law of `X_{a+1}` given the prefix is `κ a`. -/
lemma condDistrib_processTrajMeasure (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    {a : ℕ} [StandardBorelSpace (X (a + 1))] [Nonempty (X (a + 1))] :
    condDistrib (fun x : (Π n, X n) => x (a + 1))
        (Preorder.frestrictLe (π := X) a)
        (processTrajMeasure (X := X) κ μ₀)
      =ᵐ[(processTrajMeasure (X := X) κ μ₀).map (Preorder.frestrictLe (π := X) a)]
        κ a := by
  simpa [processTrajMeasure] using
    (ProbabilityTheory.Kernel.condDistrib_trajMeasure (μ₀ := μ₀) (κ := κ) (a := a))

end

end Cascades

end SpinGlass
