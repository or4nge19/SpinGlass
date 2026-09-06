import SpinGlass.FiniteGibbs.Kernel
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Order-parameter kernels

Pushforwards of the finite Gibbs sampler along `u : α → β`. Main: `orderKernel`, `orderArrayKernel`.
-/

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ENNReal NNReal

namespace SpinGlass
namespace FiniteGibbs

noncomputable section

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## `1` replica: pushforward of the Gibbs sampler -/

variable {β : Type*} [MeasurableSpace β]

/-- Kernel `H ↦ Law(u(σ))` for `σ ∼ G_H`; definitionally `gibbsKernel.map u`. -/
noncomputable def orderKernel (u : α → β) : Kernel (EnergySpace α) β :=
  (gibbsKernel (α := α)).map u

lemma orderKernel_apply (u : α → β) (hu : Measurable u) (H : EnergySpace α) :
    orderKernel (α := α) u H = (gibbsMeasure (α := α) H).map u := by
  simpa [orderKernel, gibbsKernel_apply] using
    (ProbabilityTheory.Kernel.map_apply (κ := gibbsKernel (α := α)) (f := u) hu H)

lemma orderKernel_apply' (u : α → β) (hu : Measurable u) (H : EnergySpace α)
    {s : Set β} (hs : MeasurableSet s) :
    orderKernel (α := α) u H s = gibbsMeasure (α := α) H (u ⁻¹' s) := by
  simpa [orderKernel, gibbsKernel_apply] using
    (ProbabilityTheory.Kernel.map_apply' (κ := gibbsKernel (α := α)) (f := u) hu H hs)

lemma orderKernel_isMarkovKernel (u : α → β) (hu : Measurable u) :
    IsMarkovKernel (orderKernel (α := α) u) := by
  simpa [orderKernel] using
    (ProbabilityTheory.Kernel.IsMarkovKernel.map (κ := gibbsKernel (α := α)) (f := u) hu)

/-! ## `n` replicas: pushforward of the replica sampler -/

/-- The order-parameter *array* on `n` replicas: `ℓ ↦ u(σ^ℓ)`. -/
noncomputable def orderArray (u : α → β) (n : ℕ) (σs : ReplicaSpace (α := α) n) : Fin n → β :=
  fun ℓ => u (σs ℓ)

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] in
@[simp]
lemma orderArray_apply (u : α → β) (n : ℕ) (σs : ReplicaSpace (α := α) n) (ℓ : Fin n) :
    orderArray (α := α) (β := β) u n σs ℓ = u (σs ℓ) := rfl

/-- Kernel `H ↦ Law(ℓ ↦ u(σ^ℓ))` for `n` independent Gibbs replicas. -/
noncomputable def orderArrayKernel (u : α → β) (n : ℕ) :
    Kernel (EnergySpace α) (Fin n → β) :=
  (replicaGibbsKernel (α := α) n).map (orderArray (α := α) (β := β) u n)

lemma orderArrayKernel_apply (u : α → β) (n : ℕ) (hu : Measurable u) (H : EnergySpace α) :
    orderArrayKernel (α := α) (β := β) u n H =
      (replicaGibbsMeasure (α := α) (n := n) H).map (orderArray (α := α) (β := β) u n) := by
  have hmeas : Measurable (orderArray (α := α) (β := β) u n) := by
    have : Measurable u := hu
    fun_prop
  simpa [orderArrayKernel, replicaGibbsKernel_apply] using
    (ProbabilityTheory.Kernel.map_apply
      (κ := replicaGibbsKernel (α := α) n) (f := orderArray (α := α) (β := β) u n) hmeas H)

lemma orderArrayKernel_apply' (u : α → β) (n : ℕ) (hu : Measurable u) (H : EnergySpace α)
    {s : Set (Fin n → β)} (hs : MeasurableSet s) :
    orderArrayKernel (α := α) (β := β) u n H s =
      replicaGibbsMeasure (α := α) (n := n) H ((orderArray (α := α) (β := β) u n) ⁻¹' s) := by
  have hmeas : Measurable (orderArray (α := α) (β := β) u n) := by
    have : Measurable u := hu
    fun_prop
  simpa [orderArrayKernel, replicaGibbsKernel_apply] using
    (ProbabilityTheory.Kernel.map_apply' (κ := replicaGibbsKernel (α := α) n)
      (f := orderArray (α := α) (β := β) u n) hmeas H hs)

lemma orderArrayKernel_isMarkovKernel (u : α → β) (n : ℕ) (hu : Measurable u) :
    IsMarkovKernel (orderArrayKernel (α := α) (β := β) u n) := by
  have hmeas : Measurable (orderArray (α := α) (β := β) u n) := by
    have : Measurable u := hu
    fun_prop
  simpa [orderArrayKernel] using
    (ProbabilityTheory.Kernel.IsMarkovKernel.map
      (κ := replicaGibbsKernel (α := α) n) (f := orderArray (α := α) (β := β) u n) hmeas)

/-! ## Composition lemmas -/

variable {γ : Type*} [MeasurableSpace γ]

lemma orderKernel_comp (u : α → β) (hu : Measurable u) (v : β → γ) (hv : Measurable v) :
    orderKernel (α := α) (β := γ) (v ∘ u) = (orderKernel (α := α) (β := β) u).map v := by
  simpa [orderKernel] using
    (ProbabilityTheory.Kernel.map_comp_right (κ := gibbsKernel (α := α)) (hf := hu) (hg := hv))

lemma orderArrayKernel_comp (u : α → β) (n : ℕ) (hu : Measurable u) (v : β → γ) (hv : Measurable v) :
    orderArrayKernel (α := α) (β := γ) (v ∘ u) n =
      (orderArrayKernel (α := α) (β := β) u n).map (fun xs : Fin n → β => fun ℓ => v (xs ℓ)) := by
  have hmeas_u : Measurable (orderArray (α := α) (β := β) u n) := by
    have : Measurable u := hu
    fun_prop
  have hmeas_v : Measurable (fun xs : Fin n → β => fun ℓ => v (xs ℓ)) := by
    have : Measurable v := hv
    fun_prop
  have hcomp :
      orderArray (α := α) (β := γ) (v ∘ u) n
        = (fun xs : Fin n → β => fun ℓ => v (xs ℓ)) ∘ orderArray (α := α) (β := β) u n := by
    rfl
  simpa [orderArrayKernel, hcomp] using
    (ProbabilityTheory.Kernel.map_comp_right (κ := replicaGibbsKernel (α := α) n)
      (hf := hmeas_u) (hg := hmeas_v))

end

end FiniteGibbs
end SpinGlass
