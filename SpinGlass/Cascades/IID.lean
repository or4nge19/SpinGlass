import SpinGlass.ReplicaKernel
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.Composition.Comp

/-!
# Vol II infrastructure: i.i.d. trajectories from a kernel (Ionescu–Tulcea)

This file builds a **sequential kernel family** suitable for the Ionescu–Tulcea theorem from a
single Markov kernel `K : Kernel α β`, by declaring that *each new coordinate* is sampled from `K`
based only on the initial state.

This is the clean “replicas as kernel composition” viewpoint needed in Talagrand Vol. II:

- a finite `n`-replica sampler is a finite marginal of an Ionescu–Tulcea trajectory kernel;
- later, cascades/RPCs are built by allowing later kernels to depend on the full past trajectory.

Nothing here assumes `α` or `β` are finite: only measurability is used.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SpinGlass

namespace Cascades

section General

universe u

variable {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]

/-! ## The “trajectory type family” for i.i.d. sampling -/

/-- Time-indexed state spaces for an i.i.d. trajectory: time 0 is `α`, time `n+1` is `β`. -/
def IidX (α β : Type u) : ℕ → Type u
  | 0 => α
  | _ + 1 => β

instance instMeasurableSpaceIidX (n : ℕ) : MeasurableSpace (IidX α β n) := by
  cases n <;> dsimp [IidX] <;> infer_instance

/-- Projection to the initial state (time 0) from a trajectory prefix. -/
def head {n : ℕ} (x : (i : ↑(Finset.Iic n)) → IidX α β i) : α := by
  -- `i = 0` lies in `Finset.Iic n`, hence the `0`-coordinate has type `IidX α β 0 = α`.
  simpa [IidX] using x ⟨0, by simp⟩

lemma measurable_head (n : ℕ) :
    Measurable (head (α := α) (β := β) (n := n)) := by
  -- evaluation at the coordinate `0`
  -- `head` is definitional to evaluation at `0`.
  let i0 : (↑(Finset.Iic n)) := ⟨0, by simp⟩
  simpa [head, i0] using (measurable_pi_apply i0)

/-! ## The Ionescu–Tulcea kernel family -/

/--
The sequential kernel family encoding i.i.d. sampling from `K`, seen as

`κ n : Kernel (Π i : Iic n, X i) (X (n+1))`.
-/
noncomputable def iidκ (K : Kernel α β) (n : ℕ) :
    Kernel ((i : ↑(Finset.Iic n)) → IidX α β i) (IidX α β (n + 1)) :=
  -- sample from `K` after projecting the whole prefix down to its head state
  (K ∘ₖ ProbabilityTheory.Kernel.deterministic
      (head (α := α) (β := β) (n := n))
      (measurable_head (α := α) (β := β) n))

instance (K : Kernel α β) (n : ℕ) [IsMarkovKernel K] :
    IsMarkovKernel (iidκ (α := α) (β := β) K n) := by
  -- composition of Markov kernels is Markov
  dsimp [iidκ]
  -- help typeclass search: the deterministic kernel is Markov
  haveI :
      IsMarkovKernel
        (ProbabilityTheory.Kernel.deterministic
          (head (α := α) (β := β) (n := n))
          (measurable_head (α := α) (β := β) n)) := by
    infer_instance
  infer_instance

/-! ## Finite marginals via `partialTraj` -/

noncomputable def iidPartialTraj (K : Kernel α β) (a b : ℕ) :
    Kernel ((i : ↑(Finset.Iic a)) → IidX α β i) ((i : ↑(Finset.Iic b)) → IidX α β i) :=
  ProbabilityTheory.Kernel.partialTraj (κ := iidκ (α := α) (β := β) K) a b

end General

/-! ## Specialization: Gibbs replicas as an i.i.d. trajectory -/

section SpinGlass

open SpinGlass.KernelBridge

/-- The i.i.d. kernel family whose next-step law is always `gibbsKernel N` based on the initial energy. -/
noncomputable def gibbsκ (N : ℕ) (n : ℕ) :
    Kernel ((i : ↑(Finset.Iic n)) → Cascades.IidX (EnergySpace N) (Config N) i)
      (Cascades.IidX (EnergySpace N) (Config N) (n + 1)) :=
  iidκ (α := EnergySpace N) (β := Config N) (gibbsKernel (N := N)) n

instance (N : ℕ) (n : ℕ) : IsMarkovKernel (gibbsκ N n) := by
  -- `gibbsKernel` is Markov, hence so is the composed step kernel.
  dsimp [gibbsκ, iidκ]
  haveI : IsMarkovKernel (gibbsKernel (N := N)) := by infer_instance
  haveI :
      IsMarkovKernel
        (ProbabilityTheory.Kernel.deterministic
          (head (α := EnergySpace N) (β := Config N) (n := n))
          (measurable_head (α := EnergySpace N) (β := Config N) n)) := by
    infer_instance
  infer_instance

/-- The finite trajectory kernel up to time `b`, starting from a prefix up to time `a`. -/
noncomputable abbrev gibbsPartialTraj (N : ℕ) (a b : ℕ) :
    Kernel ((i : ↑(Finset.Iic a)) → Cascades.IidX (EnergySpace N) (Config N) i)
      ((i : ↑(Finset.Iic b)) → Cascades.IidX (EnergySpace N) (Config N) i) :=
  ProbabilityTheory.Kernel.partialTraj (κ := gibbsκ N) a b

/--
Key sanity check (no “trivialization”):
the pushforward of the one-step extension of the trajectory at time `a+1`
recovers the step kernel `gibbsκ a`.

This is the abstract statement ensuring the trajectory construction really encodes the intended
conditional distributions.
-/
lemma map_gibbsPartialTraj_succ_self (a : ℕ) :
    ∀ N : ℕ,
      (gibbsPartialTraj N a (a + 1)).map (fun x ↦ x ⟨a + 1, by simp⟩) = gibbsκ N a := by
  intro N
  simpa [gibbsPartialTraj, gibbsκ] using
    (ProbabilityTheory.Kernel.map_partialTraj_succ_self (κ := gibbsκ N) a)

end SpinGlass

end Cascades

end SpinGlass
