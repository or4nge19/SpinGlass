import SpinGlass.Cascades.IID
import SpinGlass.Cascades.Traj
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.MeasureTheory.MeasurableSpace.PreorderRestrict
import Mathlib.Order.Restriction

set_option maxHeartbeats 800000

/-!
# Vol II infrastructure: trajectory *measures* and DLR-style conditional distributions

Mathlib’s Ionescu–Tulcea theorem provides:

- a kernel `traj κ 0` producing an infinite trajectory from an initial state, and
- a measure `trajMeasure μ₀ κ` when the initial state is distributed according to `μ₀`.

For Talagrand Vol II / Georgii, the crucial correctness interface is not “finite products”, but
the **conditional distribution identity**:

> the conditional law of the next coordinate given the past is the kernel `κ a`.

We package this for the i.i.d.-from-a-kernel construction (`iidκ`) and specialize it to the
finite-volume Gibbs kernel.
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
    Measure (Π n, IidX (α := α) (β := β) n) := by
  let κ := iidκ (α := α) (β := β) K
  have hmarkov : ∀ n, IsMarkovKernel (κ n) := by
    intro n
    dsimp [κ]
    infer_instance
  exact
    @ProbabilityTheory.Kernel.trajMeasure
      (fun n => IidX (α := α) (β := β) n) (fun n => inferInstance) μ₀ κ hmarkov

instance (μ₀ : Measure α) (K : Kernel α β) [IsProbabilityMeasure μ₀] [IsMarkovKernel K] :
    IsProbabilityMeasure (iidTrajMeasure (α := α) (β := β) μ₀ K) := by
  dsimp [iidTrajMeasure]
  let κ := iidκ (α := α) (β := β) K
  have hmarkov : ∀ n, IsMarkovKernel (κ n) := by
    intro n
    dsimp [κ]
    infer_instance
  change IsProbabilityMeasure
    (@ProbabilityTheory.Kernel.trajMeasure
      (fun n => IidX (α := α) (β := β) n) (fun n => inferInstance) μ₀ κ hmarkov)
  rw [ProbabilityTheory.Kernel.trajMeasure]
  haveI :
      IsProbabilityMeasure
        (μ₀.map (MeasurableEquiv.piUnique
          (fun i : Finset.Iic 0 => IidX (α := α) (β := β) i)).symm) := by
    exact Measure.isProbabilityMeasure_map
      ((MeasurableEquiv.piUnique
        (fun i : Finset.Iic 0 => IidX (α := α) (β := β) i)).symm.measurable.aemeasurable)
  change IsProbabilityMeasure
    (((@ProbabilityTheory.Kernel.traj
      (fun n => IidX (α := α) (β := β) n) (fun n => inferInstance) κ hmarkov 0)) ∘ₘ
        (μ₀.map (MeasurableEquiv.piUnique
          (fun i : Finset.Iic 0 => IidX (α := α) (β := β) i)).symm))
  infer_instance

/--
**DLR/consistency law (kernel form):**
the conditional distribution of the next coordinate given the prefix up to time `a`
for the i.i.d. trajectory measure is the step kernel `iidκ K a`.

This is the exact formal statement you want before defining RPC/cascades by prefix-dependent `κ`.
-/
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
  let κ := iidκ (α := α) (β := β) K
  have hmarkov : ∀ n, IsMarkovKernel (κ n) := by
    intro n
    dsimp [κ]
    infer_instance
  haveI : StandardBorelSpace ((fun n => IidX (α := α) (β := β) n) (a + 1)) := by
    simpa [IidX] using (inferInstance : StandardBorelSpace β)
  haveI : Nonempty ((fun n => IidX (α := α) (β := β) n) (a + 1)) := by
    simpa [IidX] using (inferInstance : Nonempty β)
  simpa [iidTrajMeasure, κ] using
    (@ProbabilityTheory.Kernel.condDistrib_trajMeasure
      (fun n => IidX (α := α) (β := β) n) (fun n => inferInstance) κ hmarkov μ₀
      (inferInstance : IsProbabilityMeasure μ₀) a
      (inferInstance : StandardBorelSpace ((fun n => IidX (α := α) (β := β) n) (a + 1)))
      (inferInstance : Nonempty ((fun n => IidX (α := α) (β := β) n) (a + 1))))

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

/--
**DLR/consistency law for Gibbs replicas:**
under the trajectory measure, the conditional law of the next configuration given the past
is exactly `gibbsκ N a`.
-/
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

