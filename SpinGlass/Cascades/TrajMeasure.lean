import SpinGlass.Cascades.IID
import SpinGlass.Cascades.Traj
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.MeasureTheory.MeasurableSpace.PreorderRestrict
import Mathlib.Order.Restriction

/-!
# Trajectory measures

Measure `trajMeasure μ₀ κ` on infinite trajectories with `X₀ ~ μ₀`. Conditional law of the next
coordinate given the past is `κ a`. Main: `condDistrib_iidTrajMeasure`, `condDistrib_gibbsTrajMeasure`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SpinGlass

namespace Cascades

section General

universe u

variable {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]

open ProbabilityTheory.Kernel

/-- `IidX α β (a+1)` is definitionally `β`, hence inherits `StandardBorelSpace`. -/
instance instStandardBorelSpace_iid_succ (a : ℕ) [StandardBorelSpace β] :
    StandardBorelSpace (IidX (α := α) (β := β) (a + 1)) := by
  simpa [IidX] using (inferInstance : StandardBorelSpace β)

/-- `IidX α β (a+1)` is definitionally `β`, hence inherits `Nonempty`. -/
instance instNonempty_iid_succ (a : ℕ) [Nonempty β] :
    Nonempty (IidX (α := α) (β := β) (a + 1)) := by
  simpa [IidX] using (inferInstance : Nonempty β)

/-- Trajectory measure for i.i.d. sampling from `K`, starting from `μ₀` on the head space. -/
noncomputable def iidTrajMeasure (μ₀ : Measure α) (K : Kernel α β)
    [IsProbabilityMeasure μ₀] [IsMarkovKernel K] :
    Measure (Π n, IidX (α := α) (β := β) n) :=
  ProbabilityTheory.Kernel.trajMeasure (μ₀ := μ₀) (κ := iidκ (α := α) (β := β) K)

instance (μ₀ : Measure α) (K : Kernel α β) [IsProbabilityMeasure μ₀] [IsMarkovKernel K] :
    IsProbabilityMeasure (iidTrajMeasure (α := α) (β := β) μ₀ K) := by
  dsimp [iidTrajMeasure]
  infer_instance

/-- Under the i.i.d. trajectory measure, the next coordinate given the prefix is `iidκ K a`. -/
lemma condDistrib_iidTrajMeasure (μ₀ : Measure α) (K : Kernel α β)
    [IsProbabilityMeasure μ₀] [IsMarkovKernel K]
    {a : ℕ} [StandardBorelSpace β] [Nonempty β] :
    condDistrib (fun x : (Π n, IidX (α := α) (β := β) n) => x (a + 1))
        (Preorder.frestrictLe (π := fun n => IidX (α := α) (β := β) n) a)
        (iidTrajMeasure (α := α) (β := β) μ₀ K)
      =ᵐ[(iidTrajMeasure (α := α) (β := β) μ₀ K).map
        (Preorder.frestrictLe (π := fun n => IidX (α := α) (β := β) n) a)]
        (iidκ (α := α) (β := β) K a) := by
  -- Reduce to Mathlib’s theorem.
  simpa [iidTrajMeasure] using
    (ProbabilityTheory.Kernel.condDistrib_trajMeasure (μ₀ := μ₀)
      (κ := iidκ (α := α) (β := β) K) (a := a))

end General

section SpinGlass

open SpinGlass.KernelBridge

variable (N : ℕ)

/-- The infinite Gibbs trajectory measure: first sample `H ~ μH`, then i.i.d. Gibbs samples. -/
noncomputable def gibbsTrajMeasure (μH : Measure (EnergySpace N)) [IsProbabilityMeasure μH] :
    Measure (Π n, IidX (α := EnergySpace N) (β := Config N) n) :=
  iidTrajMeasure (α := EnergySpace N) (β := Config N) μH (gibbsKernel (N := N))

instance (μH : Measure (EnergySpace N)) [IsProbabilityMeasure μH] :
    IsProbabilityMeasure (gibbsTrajMeasure (N := N) μH) := by
  dsimp [gibbsTrajMeasure]
  infer_instance

/-- Under the Gibbs trajectory measure, the next configuration given the past is `gibbsκ N a`. -/
lemma condDistrib_gibbsTrajMeasure (μH : Measure (EnergySpace N)) [IsProbabilityMeasure μH]
    {a : ℕ} :
    condDistrib
        (fun x : (Π n, IidX (α := EnergySpace N) (β := Config N) n) => x (a + 1))
        (Preorder.frestrictLe (π := fun n => IidX (α := EnergySpace N) (β := Config N) n) a)
        (gibbsTrajMeasure (N := N) μH)
      =ᵐ[(gibbsTrajMeasure (N := N) μH).map
        (Preorder.frestrictLe (π := fun n => IidX (α := EnergySpace N) (β := Config N) n) a)]
        (gibbsκ N a) := by
  classical
  -- `Config N` is finite, hence standard Borel and nonempty.
  haveI : StandardBorelSpace (Config N) := by infer_instance
  haveI : Nonempty (Config N) := by
    classical
    -- `Fin N → Bool` is inhabited, hence nonempty.
    infer_instance
  simpa [gibbsTrajMeasure] using
    (condDistrib_iidTrajMeasure (α := EnergySpace N) (β := Config N) (μ₀ := μH)
      (K := gibbsKernel (N := N)) (a := a))

end SpinGlass

end Cascades

end SpinGlass

