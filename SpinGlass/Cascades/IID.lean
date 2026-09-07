import SpinGlass.ReplicaKernel
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.Composition.Comp

/-!
# I.i.d. trajectories from a kernel

Sequential kernel family from `K : Kernel α β` for Ionescu–Tulcea: each new coordinate is sampled
from `K` given the initial state. Main: `iidκ`. Talagrand Vol. II.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SpinGlass

namespace Cascades

section General

universe u

variable {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]

/-! ## The “trajectory type family” for i.i.d. sampling -/

/-- Time-indexed state spaces for an i.i.d. trajectory: time 0 is `α`, time `n+1` is `β`.

Reducible so that instance search sees `IidX α β 0 = α` and `IidX α β (n + 1) = β`. -/
@[reducible] def IidX (α β : Type u) : ℕ → Type u
  | 0 => α
  | _ + 1 => β

/-- The measurable structure on `IidX α β n`, matching the definition by cases on `n`. -/
instance instMeasurableSpaceIidX : ∀ n : ℕ, MeasurableSpace (IidX α β n)
  | 0 => ‹MeasurableSpace α›
  | _ + 1 => ‹MeasurableSpace β›

/-- Projection to the initial state (time 0) from a trajectory prefix. -/
def head {n : ℕ} (x : (i : ↑(Finset.Iic n)) → IidX α β i) : α := x ⟨0, by simp⟩

lemma measurable_head (n : ℕ) :
    Measurable (head (α := α) (β := β) (n := n)) :=
  measurable_pi_apply _

/-! ## The Ionescu–Tulcea kernel family -/

/-- Sequential kernel family: each new coordinate is sampled i.i.d. from `K`. -/
noncomputable def iidκ (K : Kernel α β) (n : ℕ) :
    Kernel ((i : ↑(Finset.Iic n)) → IidX α β i) (IidX α β (n + 1)) :=
  -- sample from `K` after projecting the whole prefix down to its head state
  (K ∘ₖ ProbabilityTheory.Kernel.deterministic
      (head (α := α) (β := β) (n := n))
      (measurable_head (α := α) (β := β) n))

instance (K : Kernel α β) (n : ℕ) [IsMarkovKernel K] :
    IsMarkovKernel (iidκ (α := α) (β := β) K n) :=
  -- Composition of Markov kernels is Markov; stated as a term so that the definitional
  -- unfolding `IidX α β (n + 1) = β` is available (instance search stops at `reducible`).
  ProbabilityTheory.Kernel.IsMarkovKernel.comp K
    (ProbabilityTheory.Kernel.deterministic _ (measurable_head (α := α) (β := β) n))

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

instance (N : ℕ) (n : ℕ) : IsMarkovKernel (gibbsκ N n) :=
  inferInstanceAs (IsMarkovKernel (iidκ (gibbsKernel (N := N)) n))

/-- The finite trajectory kernel up to time `b`, starting from a prefix up to time `a`. -/
noncomputable abbrev gibbsPartialTraj (N : ℕ) (a b : ℕ) :
    Kernel ((i : ↑(Finset.Iic a)) → Cascades.IidX (EnergySpace N) (Config N) i)
      ((i : ↑(Finset.Iic b)) → Cascades.IidX (EnergySpace N) (Config N) i) :=
  ProbabilityTheory.Kernel.partialTraj (κ := gibbsκ N) a b

/-- One-step pushforward of the Gibbs trajectory at time `a+1` recovers `gibbsκ a`. -/
lemma map_gibbsPartialTraj_succ_self (a : ℕ) :
    ∀ N : ℕ,
      (gibbsPartialTraj N a (a + 1)).map (fun x ↦ x ⟨a + 1, by simp⟩) = gibbsκ N a := by
  intro N
  exact ProbabilityTheory.Kernel.map_partialTraj_succ_self (κ := gibbsκ N) a

end SpinGlass

end Cascades

end SpinGlass
