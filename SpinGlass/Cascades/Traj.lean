import SpinGlass.Cascades.IID
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.CompMap

/-!
# Vol II infrastructure: trajectory kernels (Ionescu–Tulcea) as a public API

This file upgrades the finite-marginal (`partialTraj`) viewpoint to the **infinite trajectory**
kernel `traj` from Mathlib’s Ionescu–Tulcea theorem, and connects it to the “replicas as kernels”
bridge.

Core principle (Talagrand Vol II / Georgii): **do not** encode replicas via ad-hoc products when a
canonical stochastic process kernel exists.

We provide:

- `iidTrajKernel`: from a Markov kernel `K : Kernel α β`, build a kernel producing an infinite
  trajectory `(X₀, X₁, X₂, …)` with `X₀ = α` and `X_{n+1} = β`, sampling i.i.d. from `K` given `X₀`;
- a sharp sanity lemma: pushing `iidTrajKernel` forward to time `1` recovers exactly `K`;
- specialization to the finite-volume Gibbs kernel.

All statements reduce to Mathlib’s `map_traj_succ_self` and kernel composition laws.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SpinGlass

namespace Cascades

section General

universe u

variable {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]

open ProbabilityTheory.Kernel

/-- The length-`0` prefix constructor: embed `a : α` as a trajectory prefix indexed by `Iic 0`. -/
def prefix0 (a : α) : (i : Finset.Iic 0) → IidX (α := α) (β := β) (i : ℕ) := by
  intro i
  rcases i with ⟨k, hk⟩
  have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp hk)
  subst hk0
  simpa [Cascades.IidX] using a

lemma measurable_prefix0 : Measurable (prefix0 (α := α) (β := β)) := by
  -- `Iic 0` is finite, so measurability is pointwise.
  refine measurable_pi_lambda _ (fun i => ?_)
  rcases i with ⟨k, hk⟩
  have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp hk)
  subst hk0
  simpa [prefix0, Cascades.IidX] using measurable_id

/-- The infinite-trajectory kernel associated to `K` via Ionescu–Tulcea (i.i.d. given the head). -/
noncomputable def iidTrajKernel (K : Kernel α β) [IsMarkovKernel K] :
    Kernel α (Π n, IidX (α := α) (β := β) n) :=
  (ProbabilityTheory.Kernel.traj (κ := iidκ (α := α) (β := β) K) 0)
    ∘ₖ ProbabilityTheory.Kernel.deterministic (prefix0 (α := α) (β := β)) (measurable_prefix0 (α := α) (β := β))

instance (K : Kernel α β) [IsMarkovKernel K] : IsMarkovKernel (iidTrajKernel (α := α) (β := β) K) := by
  dsimp [iidTrajKernel]
  infer_instance

/--
**Sanity check:** the time-`1` marginal of `iidTrajKernel K` is exactly `K`.

This is the precise kernel-level version of “sampling the first replica is governed by `K`”.
-/
lemma iidTrajKernel_map_one (K : Kernel α β) [IsMarkovKernel K] :
    (iidTrajKernel (α := α) (β := β) K).map (fun x : (Π n, IidX (α := α) (β := β) n) => x 1) = K := by
  simp [iidTrajKernel, Kernel.map_comp]
  -- Apply Ionescu–Tulcea: time-`1` marginal of `traj` is the step kernel `iidκ K 0`.
  have hstep :
      (ProbabilityTheory.Kernel.traj (κ := iidκ (α := α) (β := β) K) 0).map
          (fun x : (Π n, IidX (α := α) (β := β) n) => x 1) = iidκ (α := α) (β := β) K 0 := by
    simpa using (ProbabilityTheory.Kernel.map_traj_succ_self (κ := iidκ (α := α) (β := β) K) (a := 0))
  have hstep' :
      (ProbabilityTheory.Kernel.traj (κ := iidκ (α := α) (β := β) K) 0).map
          (fun x : (Π n, IidX (α := α) (β := β) n) => x 1)
        ∘ₖ ProbabilityTheory.Kernel.deterministic (prefix0 (α := α) (β := β))
            (measurable_prefix0 (α := α) (β := β)) = (iidκ (α := α) (β := β) K 0)
          ∘ₖ ProbabilityTheory.Kernel.deterministic (prefix0 (α := α) (β := β))
              (measurable_prefix0 (α := α) (β := β)) := by
    simp [hstep]
  have hhead0 : (head (α := α) (β := β) (n := 0)) ∘ (prefix0 (α := α) (β := β)) = id := by
    funext a
    simp [Cascades.head, prefix0, Cascades.IidX]
  simpa [iidκ, Kernel.comp_assoc, Kernel.deterministic_comp_deterministic, hhead0,
    Kernel.comp_deterministic_eq_comap, Kernel.comap_id] using hstep'

end General

section SpinGlass

open SpinGlass.KernelBridge

variable (N : ℕ)

/-- The infinite Gibbs trajectory kernel: head is the energy, then i.i.d. Gibbs samples. -/
noncomputable def gibbsTrajKernel :
    Kernel (EnergySpace N) (Π n, IidX (α := EnergySpace N) (β := Config N) n) :=
  iidTrajKernel (α := EnergySpace N) (β := Config N) (gibbsKernel (N := N))

instance : IsMarkovKernel (gibbsTrajKernel (N := N)) := by
  dsimp [gibbsTrajKernel]
  infer_instance

lemma gibbsTrajKernel_map_one :
    (gibbsTrajKernel (N := N)).map (fun x : (Π n, IidX (α := EnergySpace N) (β := Config N) n) =>
      x 1) = gibbsKernel (N := N) := by
  simpa [gibbsTrajKernel] using
    (iidTrajKernel_map_one (α := EnergySpace N) (β := Config N) (K := gibbsKernel (N := N)))

end SpinGlass

end Cascades

end SpinGlass
