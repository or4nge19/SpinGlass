/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Products of product measures

Two facts about product measures that Mathlib states only in special forms:

* **Fubini for a product of functions of the coordinates, in `ℝ≥0∞`**:
  `∫⁻ ∏ᵢ fᵢ(zᵢ) d(⊗ᵢ μᵢ) = ∏ᵢ ∫⁻ fᵢ dμᵢ` (`MeasureTheory.lintegral_fintype_prod_eq_prod`), the
  companion of Mathlib's Bochner `MeasureTheory.integral_fintype_prod_eq_prod`.
* **Zipping independent families** (`MeasureTheory.Measure.infinitePi_prod_eq_map`,
  `MeasureTheory.Measure.infinitePi_prod`): a family of independent pairs
  `(xᵢ, yᵢ) ∼ μᵢ ⊗ νᵢ` is the same as a pair of independent families `(xᵢ) ∼ ⊗ᵢ μᵢ`,
  `(yᵢ) ∼ ⊗ᵢ νᵢ`, i.e. `⊗ᵢ (μᵢ ⊗ νᵢ)` is the image of `(⊗ᵢ μᵢ) ⊗ (⊗ᵢ νᵢ)` under
  `MeasurableEquiv.arrowProdEquivProdArrow`. This is what makes it possible to condition an
  i.i.d. family of marked points on the points alone.
-/

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace MeasureTheory

variable {T : Type*} [MeasurableSpace T]

instance {n : ℕ} {μs : Fin (n + 1) → Measure T} [∀ i, SigmaFinite (μs i)] (i : Fin n) :
    SigmaFinite (Fin.tail μs i) :=
  inferInstanceAs (SigmaFinite (μs i.succ))

/-- The product measure on `Fin (n+1) → T` splits off its first coordinate. -/
theorem lintegral_pi_fin_succ' {n : ℕ} (μs : Fin (n + 1) → Measure T)
    [∀ i, SigmaFinite (μs i)] {G : (Fin (n + 1) → T) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ zs, G zs ∂Measure.pi μs
      = ∫⁻ z, (∫⁻ zs, G (Fin.cons z zs) ∂Measure.pi (Fin.tail μs)) ∂μs 0 := by
  have hmp := (measurePreserving_piFinSuccAbove μs 0).symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => T) 0)
  have hGe : Measurable fun q : T × (Fin n → T) =>
      G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => T) 0).symm q) :=
    hG.comp hmp.measurable
  rw [← hmp.lintegral_comp hG, lintegral_prod _ hGe.aemeasurable]
  simp only [Fin.succAbove_zero]
  refine lintegral_congr fun z => lintegral_congr fun zs => ?_
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero]
  rfl

/-- **Fubini for a product of functions of the coordinates**, `ℝ≥0∞` version, over `Fin n`:
`∫⁻ ∏ᵢ fᵢ(zᵢ) d(⊗ᵢ μᵢ) = ∏ᵢ ∫⁻ fᵢ dμᵢ`. -/
theorem lintegral_fin_prod_eq_prod : ∀ (n : ℕ) (μs : Fin n → Measure T)
    [∀ i, SigmaFinite (μs i)] {f : Fin n → T → ℝ≥0∞}, (∀ i, Measurable (f i)) →
    ∫⁻ zs, ∏ i, f i (zs i) ∂Measure.pi μs = ∏ i, ∫⁻ z, f i z ∂μs i
  | 0, μs, _, f, _ => by
    rw [Measure.pi_of_empty]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, lintegral_const, measure_univ, mul_one]
  | n + 1, μs, _, f, hf => by
    have hG : Measurable fun zs : Fin (n + 1) → T => ∏ i, f i (zs i) :=
      Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
    rw [lintegral_pi_fin_succ' μs hG]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have hf' : ∀ i : Fin n, Measurable (f i.succ) := fun i => hf i.succ
    have hmeas : Measurable fun zs : Fin n → T => ∏ i, f i.succ (zs i) :=
      Finset.measurable_prod _ fun i _ => (hf' i).comp (measurable_pi_apply i)
    have h1 : ∀ z, ∫⁻ zs : Fin n → T, f 0 z * ∏ i : Fin n, f i.succ (zs i) ∂Measure.pi (Fin.tail μs)
        = f 0 z * ∏ i : Fin n, ∫⁻ w, f i.succ w ∂μs i.succ := by
      intro z
      rw [lintegral_const_mul _ hmeas, lintegral_fin_prod_eq_prod n (Fin.tail μs) hf']
      rfl
    simp_rw [h1]
    rw [lintegral_mul_const _ (hf 0)]

/-- **Fubini for a product of functions of the coordinates**, `ℝ≥0∞` version, over a finite
index type: `∫⁻ ∏ᵢ fᵢ(zᵢ) d(⊗ᵢ μᵢ) = ∏ᵢ ∫⁻ fᵢ dμᵢ`. The `ℝ≥0∞` companion of
`MeasureTheory.integral_fintype_prod_eq_prod`. -/
theorem lintegral_fintype_prod_eq_prod {ι : Type*} [Fintype ι] (μs : ι → Measure T)
    [∀ i, SigmaFinite (μs i)] {f : ι → T → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    ∫⁻ zs, ∏ i, f i (zs i) ∂Measure.pi μs = ∏ i, ∫⁻ z, f i z ∂μs i := by
  let e := (Fintype.equivFin ι).symm
  have hG : Measurable fun zs : ι → T => ∏ i, f i (zs i) :=
    Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
  rw [← (measurePreserving_piCongrLeft (μ := μs) e).lintegral_comp hG]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_prod_eq_prod _ (fun i => μs (e i)) fun i => hf (e i)


/-! ### Zipping independent families -/

namespace Measure

variable {ι X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (μ : ι → Measure X) (ν : ι → Measure Y) [∀ i, IsProbabilityMeasure (μ i)]
  [∀ i, IsProbabilityMeasure (ν i)]

/-- **Zipping independent families**: the family of independent pairs `(xᵢ, yᵢ) ∼ μᵢ ⊗ νᵢ` is
the image of the pair of independent families `((xᵢ), (yᵢ)) ∼ (⊗ᵢ μᵢ) ⊗ (⊗ᵢ νᵢ)` under
`(x, y) ↦ (i ↦ (xᵢ, yᵢ))`. -/
theorem infinitePi_prod_eq_map :
    infinitePi (fun i => (μ i).prod (ν i))
      = ((infinitePi μ).prod (infinitePi ν)).map
          (MeasurableEquiv.arrowProdEquivProdArrow X Y ι).symm := by
  symm
  refine eq_infinitePi _ fun s t ht => ?_
  rw [MeasurableEquiv.map_apply]
  have hpre : (MeasurableEquiv.arrowProdEquivProdArrow X Y ι).symm ⁻¹' Set.pi s t
      = {p : (ι → X) × (ι → Y) | ∀ i ∈ s, (p.1 i, p.2 i) ∈ t i} := by
    ext p
    simp [MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow, Set.mem_pi]
  have hmeas : MeasurableSet {p : (ι → X) × (ι → Y) | ∀ i ∈ s, (p.1 i, p.2 i) ∈ t i} := by
    rw [← hpre]
    exact (MeasurableEquiv.arrowProdEquivProdArrow X Y ι).symm.measurable
      (MeasurableSet.pi s.countable_toSet fun i _ => ht i)
  rw [hpre, Measure.prod_apply hmeas]
  have hsec : ∀ a : ι → X, Prod.mk a ⁻¹' {p : (ι → X) × (ι → Y) | ∀ i ∈ s, (p.1 i, p.2 i) ∈ t i}
      = Set.pi s fun i => Prod.mk (a i) ⁻¹' t i := by
    intro a
    ext b
    simp [Set.mem_pi]
  simp_rw [hsec]
  have hg : ∀ i, Measurable fun x : X => ν i (Prod.mk x ⁻¹' t i) := fun i =>
    measurable_measure_prodMk_left (ht i)
  have hint : ∀ a : ι → X, infinitePi ν (Set.pi s fun i => Prod.mk (a i) ⁻¹' t i)
      = (fun a' : (i : s) → X => ∏ i : s, ν i (Prod.mk (a' i) ⁻¹' t i)) (s.restrict a) := by
    intro a
    rw [infinitePi_pi ν fun i _ => measurable_prodMk_left (ht i), ← Finset.prod_coe_sort]
    rfl
  simp_rw [hint]
  change ∫⁻ a, (fun a' : (i : s) → X => ∏ i : s, ν i (Prod.mk (a' i) ⁻¹' t i)) (s.restrict a)
    ∂infinitePi μ = _
  have hf : Measurable fun a' : (i : s) → X => ∏ i : s, ν i (Prod.mk (a' i) ⁻¹' t i) :=
    Finset.measurable_prod _ fun i _ => (hg i).comp (measurable_pi_apply i)
  rw [lintegral_restrict_infinitePi μ hf,
    lintegral_fintype_prod_eq_prod (fun i : s => μ i) (f := fun i x => ν i (Prod.mk x ⁻¹' t i))
      (fun i => hg i)]
  exact (Finset.prod_coe_sort s fun i => ∫⁻ z, ν i (Prod.mk z ⁻¹' t i) ∂μ i).trans
    (Finset.prod_congr rfl fun i _ => (Measure.prod_apply (ht i)).symm)

/-- The zip, in the other direction: `(⊗ᵢ μᵢ) ⊗ (⊗ᵢ νᵢ)` is the image of `⊗ᵢ (μᵢ ⊗ νᵢ)` under
`z ↦ ((zᵢ.1), (zᵢ.2))`. -/
theorem infinitePi_prod :
    (infinitePi μ).prod (infinitePi ν)
      = (infinitePi (fun i => (μ i).prod (ν i))).map
          (MeasurableEquiv.arrowProdEquivProdArrow X Y ι) := by
  rw [infinitePi_prod_eq_map μ ν, MeasurableEquiv.map_map_symm]

/-- `⊗ᵢ (μᵢ ⊗ νᵢ).map fᵢ` is the image of `⊗ᵢ (μᵢ ⊗ νᵢ)` — the map form of `infinitePi_map_pi`. -/
theorem infinitePi_map_eq {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)] {Z : ι → Type*}
    [∀ i, MeasurableSpace (Z i)] (ρ : (i : ι) → Measure (Y i)) [∀ i, IsProbabilityMeasure (ρ i)]
    {f : (i : ι) → Y i → Z i} (hf : ∀ i, Measurable (f i)) :
    infinitePi (fun i => (ρ i).map (f i)) = (infinitePi ρ).map (fun x i => f i (x i)) :=
  (infinitePi_map_pi ρ hf).symm

/-- The zip for finitely many coordinates. -/
theorem pi_prod_eq_map [Fintype ι] :
    Measure.pi (fun i => (μ i).prod (ν i))
      = ((Measure.pi μ).prod (Measure.pi ν)).map
          (MeasurableEquiv.arrowProdEquivProdArrow X Y ι).symm := by
  rw [← infinitePi_eq_pi, ← infinitePi_eq_pi, ← infinitePi_eq_pi, infinitePi_prod_eq_map]

omit [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] in
lemma measurable_zip₂ {κ : Type*} :
    Measurable fun p : (ι → κ → X) × (ι → κ → Y) => fun i j => (p.1 i j, p.2 i j) :=
  measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst)).prodMk
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_snd))

/-- **Zipping doubly-indexed independent families**: `⊗ᵢ ⊗ⱼ (μᵢⱼ ⊗ νᵢⱼ)` is the image of
`(⊗ᵢ ⊗ⱼ μᵢⱼ) ⊗ (⊗ᵢ ⊗ⱼ νᵢⱼ)` under `(x, y) ↦ (i j ↦ (xᵢⱼ, yᵢⱼ))`. -/
theorem infinitePi_infinitePi_prod_eq_map {κ : Type*} (μ : ι → κ → Measure X)
    (ν : ι → κ → Measure Y) [∀ i j, IsProbabilityMeasure (μ i j)]
    [∀ i j, IsProbabilityMeasure (ν i j)] :
    infinitePi (fun i => infinitePi fun j => (μ i j).prod (ν i j))
      = ((infinitePi fun i => infinitePi fun j => μ i j).prod
          (infinitePi fun i => infinitePi fun j => ν i j)).map
          (fun p : (ι → κ → X) × (ι → κ → Y) => fun i j => (p.1 i j, p.2 i j)) := by
  have h1 : ∀ i, infinitePi (fun j => (μ i j).prod (ν i j))
      = ((infinitePi (μ i)).prod (infinitePi (ν i))).map
          (MeasurableEquiv.arrowProdEquivProdArrow X Y κ).symm := fun i =>
    infinitePi_prod_eq_map (μ i) (ν i)
  simp_rw [h1]
  rw [infinitePi_map_eq (fun i => (infinitePi (μ i)).prod (infinitePi (ν i)))
      (fun _ => (MeasurableEquiv.arrowProdEquivProdArrow X Y κ).symm.measurable),
    infinitePi_prod_eq_map (fun i => infinitePi (μ i)) (fun i => infinitePi (ν i))]
  have hm1 : Measurable fun x : ι → (κ → X) × (κ → Y) =>
      fun i => (MeasurableEquiv.arrowProdEquivProdArrow X Y κ).symm (x i) :=
    measurable_pi_lambda _ fun i =>
      (MeasurableEquiv.arrowProdEquivProdArrow X Y κ).symm.measurable.comp (measurable_pi_apply i)
  have hm2 : Measurable (MeasurableEquiv.arrowProdEquivProdArrow (κ → X) (κ → Y) ι).symm :=
    MeasurableEquiv.measurable _
  rw [Measure.map_map hm1 hm2]
  rfl

omit [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] in
/-- `infinitePi` respects pointwise equality of the families (the probability-measure instances
being proofs). -/
lemma infinitePi_congr {ρ ρ' : ι → Measure X} [∀ i, IsProbabilityMeasure (ρ i)]
    [∀ i, IsProbabilityMeasure (ρ' i)] (h : ∀ i, ρ i = ρ' i) : infinitePi ρ = infinitePi ρ' := by
  have : ρ = ρ' := funext h
  subst this
  rfl

/-! ### Infinite products over a sum type -/

instance {ι ι' : Type*} (μ : ι → Measure X) (μ' : ι' → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (μ' i)] (i : ι ⊕ ι') : IsProbabilityMeasure (Sum.elim μ μ' i) := by
  cases i <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> infer_instance

/-- **An infinite product over a sum type is a product of infinite products**:
`⊗_{i ∈ ι ⊕ ι'} μ_i` is the image of `(⊗_{i ∈ ι} μ_i) ⊗ (⊗_{i' ∈ ι'} μ'_{i'})` under
`(x, y) ↦ Sum.elim x y`. -/
theorem infinitePi_sum_eq_map {ι ι' : Type*} (μ : ι → Measure X) (μ' : ι' → Measure X)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (μ' i)] :
    infinitePi (Sum.elim μ μ')
      = ((infinitePi μ).prod (infinitePi μ')).map
          (MeasurableEquiv.sumPiEquivProdPi fun _ : ι ⊕ ι' => X).symm := by
  symm
  refine eq_infinitePi _ fun s t ht => ?_
  rw [MeasurableEquiv.map_apply]
  have hpre : (MeasurableEquiv.sumPiEquivProdPi fun _ : ι ⊕ ι' => X).symm ⁻¹' Set.pi s t
      = (Set.pi s.toLeft fun i => t (Sum.inl i)) ×ˢ (Set.pi s.toRight fun i => t (Sum.inr i)) := by
    ext ⟨x, y⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_toLeft,
      Finset.mem_toRight, MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.symm_mk,
      MeasurableEquiv.coe_mk, Equiv.sumPiEquivProdPi, Equiv.coe_fn_symm_mk]
    constructor
    · intro h
      exact ⟨fun i hi => h (Sum.inl i) hi, fun i hi => h (Sum.inr i) hi⟩
    · rintro ⟨h1, h2⟩ i hi
      cases i with
      | inl i => exact h1 i hi
      | inr i => exact h2 i hi
  rw [hpre, Measure.prod_prod, infinitePi_pi μ fun i _ => ht _, infinitePi_pi μ' fun i _ => ht _,
    Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]
  rfl

/-- The product of two infinite products is the image of the infinite product over the sum
type under `x ↦ (x ∘ inl, x ∘ inr)`. -/
theorem infinitePi_prod_infinitePi_eq_map {ι ι' : Type*} (μ : ι → Measure X)
    (μ' : ι' → Measure X) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (μ' i)] :
    (infinitePi μ).prod (infinitePi μ')
      = (infinitePi (Sum.elim μ μ')).map (MeasurableEquiv.sumPiEquivProdPi fun _ : ι ⊕ ι' => X) := by
  rw [infinitePi_sum_eq_map μ μ', MeasurableEquiv.map_map_symm]

end Measure

/-! ### Rearranging triple products -/

namespace Measure

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  (μ : Measure α) (ν : Measure β) (τ : Measure γ) [SFinite μ] [SFinite ν] [SFinite τ]

/-- `(μ ⊗ ν) ⊗ τ` is the image of `(μ ⊗ τ) ⊗ ν` under `((a, c), b) ↦ ((a, b), c)`. -/
lemma prod_prod_swap_right :
    (μ.prod ν).prod τ
      = ((μ.prod τ).prod ν).map (fun p : (α × γ) × β => ((p.1.1, p.2), p.1.2)) := by
  have hf : (fun p : (α × γ) × β => ((p.1.1, p.2), p.1.2))
      = MeasurableEquiv.prodAssoc.symm ∘ Prod.map id Prod.swap ∘ MeasurableEquiv.prodAssoc := by
    funext p
    rfl
  rw [hf, ← Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
    ((measurable_id.prodMap measurable_swap).comp MeasurableEquiv.prodAssoc.measurable),
    ← Measure.map_map (measurable_id.prodMap measurable_swap) MeasurableEquiv.prodAssoc.measurable,
    Measure.prodAssoc_prod, ← Measure.map_prod_map _ _ measurable_id measurable_swap,
    Measure.map_id, Measure.prod_swap, ← Measure.prodAssoc_prod, MeasurableEquiv.map_symm_map]

/-- `μ ⊗ (ν ⊗ τ)` is the image of `ν ⊗ (μ ⊗ τ)` under `(b, (a, c)) ↦ (a, (b, c))`. -/
lemma prod_swap_left₃ :
    μ.prod (ν.prod τ)
      = (ν.prod (μ.prod τ)).map (fun p : β × α × γ => (p.2.1, (p.1, p.2.2))) := by
  have hf : (fun p : β × α × γ => (p.2.1, (p.1, p.2.2)))
      = MeasurableEquiv.prodAssoc ∘ Prod.map Prod.swap id ∘ MeasurableEquiv.prodAssoc.symm := by
    funext p
    rfl
  rw [hf, ← Measure.map_map MeasurableEquiv.prodAssoc.measurable
    ((measurable_swap.prodMap measurable_id).comp MeasurableEquiv.prodAssoc.symm.measurable),
    ← Measure.map_map (measurable_swap.prodMap measurable_id)
      MeasurableEquiv.prodAssoc.symm.measurable,
    ← Measure.prodAssoc_prod (μ := ν) (ν := μ) (τ := τ), MeasurableEquiv.map_symm_map,
    ← Measure.map_prod_map _ _ measurable_swap measurable_id, Measure.map_id, Measure.prod_swap,
    Measure.prodAssoc_prod]

end Measure

end MeasureTheory
