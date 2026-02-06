import GibbsMeasure.Specification.Extremal
import GibbsMeasure.Prereqs.MeasureExt
import GibbsMeasure.Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.MeasureTheory.Measure.Real

/-!
# Tail disintegration and ergodic decomposition setup (Georgii, Ch. 7 — setup)

This file introduces the **tail conditional kernel** using Mathlib's `ProbabilityTheory.condExpKernel`.

For a finite measure `μ` on the configuration space `S → E`, we define the kernel
`tailKernel μ : Kernel[𝓣] (S → E) (S → E)` (domain σ-algebra is the tail σ-algebra `𝓣`).

We record:

- the disintegration identity `tailKernel μ ∘ₘ μ.trim (𝓣 ≤ pi) = μ`;
- for tail events `A ∈ 𝓣`, the kernel evaluates `A` as the **indicator** (hence is {0,1}-valued a.e.).

These lemmas are the starting point for the ergodic (extremal) decomposition of Gibbs measures.
-/

open Set
open scoped ENNReal ProbabilityTheory
open ProbabilityTheory

namespace MeasureTheory

namespace GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

/-! ## Tail σ-algebra vs. the full product σ-algebra -/

lemma tailSigmaAlgebra_le_pi :
    (@tailSigmaAlgebra S E _ : MeasurableSpace (S → E)) ≤ MeasurableSpace.pi := by
  refine le_trans
    (iInf_le (fun Λ : Finset S =>
      cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) (∅ : Finset S)) ?_
  simp

lemma tailSigmaAlgebra_le_cylinderEvents (Λ : Finset S) :
    (@tailSigmaAlgebra S E _ : MeasurableSpace (S → E))
      ≤ cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ) := by
  simpa [tailSigmaAlgebra] using
    (iInf_le (fun Λ' : Finset S =>
      cylinderEvents (X := fun _ : S ↦ E) ((Λ' : Set S)ᶜ)) Λ)

/-! ## Tail conditional kernel -/

section TailKernel

-- For the Vol II (infinite-volume) development, we primarily care about probability measures.
-- (This automatically provides finiteness hypotheses when needed by conditional expectation APIs.)
variable (μ : Measure (S → E)) [IsProbabilityMeasure μ]
variable [Countable S] [StandardBorelSpace E]

-- The configuration space is standard Borel as a countable product of standard Borel spaces.
instance : StandardBorelSpace (S → E) := by
  infer_instance

/-- The **tail conditional kernel**: a regular conditional distribution of the identity given the
tail σ-algebra `𝓣`. -/
noncomputable def tailKernel : Kernel[@tailSigmaAlgebra S E _] (S → E) (S → E) :=
  ProbabilityTheory.condExpKernel (mΩ := MeasurableSpace.pi) μ (@tailSigmaAlgebra S E _)

instance : IsMarkovKernel (tailKernel (S := S) (E := E) μ) := by
  simpa [tailKernel] using (by infer_instance : IsMarkovKernel (ProbabilityTheory.condExpKernel (mΩ := MeasurableSpace.pi)
    μ (@tailSigmaAlgebra S E _)))

lemma tailKernel_comp_trim :
    tailKernel (S := S) (E := E) μ ∘ₘ μ.trim (tailSigmaAlgebra_le_pi (S := S) (E := E))
      = μ := by
  simpa [tailKernel] using
    (ProbabilityTheory.condExpKernel_comp_trim (μ := μ) (m := (@tailSigmaAlgebra S E _))
      (mΩ := MeasurableSpace.pi) (hm := tailSigmaAlgebra_le_pi (S := S) (E := E)))

/-! ## Tail events are {0,1}-valued under the tail kernel (a.e.) -/

omit [Countable S] [StandardBorelSpace E] in
lemma condExp_tail_of_measurableSet (A : Set (S → E))
    (hA : MeasurableSet[@tailSigmaAlgebra S E _] A) :
    MeasureTheory.condExp (@tailSigmaAlgebra S E _) μ (A.indicator fun _ : S → E => (1 : ℝ))
      = A.indicator fun _ : S → E => (1 : ℝ) := by
  have hm : (@tailSigmaAlgebra S E _ : MeasurableSpace (S → E)) ≤ MeasurableSpace.pi :=
    tailSigmaAlgebra_le_pi (S := S) (E := E)
  haveI : SigmaFinite (μ.trim hm) := by infer_instance
  have hSM : StronglyMeasurable[@tailSigmaAlgebra S E _] (A.indicator fun _ : S → E => (1 : ℝ)) :=
    (stronglyMeasurable_const.indicator hA)
  have hA_pi : MeasurableSet A := hm _ hA
  have hInt : Integrable (A.indicator fun _ : S → E => (1 : ℝ)) μ := by
    simpa using ((integrable_const (μ := μ) (c := (1 : ℝ))).indicator hA_pi)
  simpa using (MeasureTheory.condExp_of_stronglyMeasurable (μ := μ) (m := (@tailSigmaAlgebra S E _))
    (m₀ := MeasurableSpace.pi) (hm := hm) hSM hInt)

lemma tailKernel_real_eq_indicator_of_measurableSet (A : Set (S → E))
    (hA : MeasurableSet[@tailSigmaAlgebra S E _] A) :
    (fun ω : S → E => (tailKernel (S := S) (E := E) μ ω).real A)
      =ᵐ[μ.trim (tailSigmaAlgebra_le_pi (S := S) (E := E))]
        (A.indicator fun _ : S → E => (1 : ℝ)) := by
  have hm : (@tailSigmaAlgebra S E _ : MeasurableSpace (S → E)) ≤ MeasurableSpace.pi :=
    tailSigmaAlgebra_le_pi (S := S) (E := E)
  have hA_pi : MeasurableSet A := hm _ hA
  have h1 :
      (fun ω : S → E => (ProbabilityTheory.condExpKernel (mΩ := MeasurableSpace.pi) μ (@tailSigmaAlgebra S E _) ω).real A)
        =ᵐ[μ.trim hm] μ⟦A|(@tailSigmaAlgebra S E _)⟧ :=
    ProbabilityTheory.condExpKernel_ae_eq_trim_condExp (μ := μ) (m := (@tailSigmaAlgebra S E _))
      (mΩ := MeasurableSpace.pi) (hm := hm) (hs := hA_pi)
  have h2 :
      (μ⟦A|(@tailSigmaAlgebra S E _)⟧ : (S → E) → ℝ)
        = (A.indicator fun _ : S → E => (1 : ℝ)) := by
    simpa using
      (condExp_tail_of_measurableSet (S := S) (E := E) (μ := μ) A hA)
  simpa [tailKernel, h2] using h1

/-! ## The law of the tail-conditional measures and a barycenter identity -/

/-- The **law** of the tail-conditional measures: pushforward of `μ.trim (𝓣 ≤ pi)` under the map
`ω ↦ tailKernel μ ω`. -/
noncomputable def tailKernelLaw : Measure (Measure (S → E)) :=
  μ.map (tailKernel (S := S) (E := E) μ)

lemma measurable_tailKernel_pi :
    @Measurable (S → E) (Measure (S → E)) MeasurableSpace.pi Measure.instMeasurableSpace
      (tailKernel (S := S) (E := E) μ) := by
  exact (tailKernel (S := S) (E := E) μ).measurable.mono
    (tailSigmaAlgebra_le_pi (S := S) (E := E)) le_rfl

lemma lintegral_eval_tailKernelLaw (A : Set (S → E)) (hA : MeasurableSet A) :
    (∫⁻ ν : Measure (S → E), ν A ∂(tailKernelLaw (S := S) (E := E) μ))
      = μ A := by
  have hm : (@tailSigmaAlgebra S E _ : MeasurableSpace (S → E)) ≤ MeasurableSpace.pi :=
    tailSigmaAlgebra_le_pi (S := S) (E := E)
  have hκ_pi : Measurable (tailKernel (S := S) (E := E) μ) :=
    measurable_tailKernel_pi (S := S) (E := E) (μ := μ)
  have hmap :
      (∫⁻ ν : Measure (S → E), ν A ∂(tailKernelLaw (S := S) (E := E) μ))
        =
      ∫⁻ ω : S → E, (tailKernel (S := S) (E := E) μ ω) A ∂μ := by
    have h_eval : Measurable (fun ν : Measure (S → E) => ν A) := Measure.measurable_coe hA
    simpa [tailKernelLaw] using
      (MeasureTheory.lintegral_map (μ := μ)
        (f := fun ν : Measure (S → E) => ν A)
        (g := tailKernel (S := S) (E := E) μ) h_eval hκ_pi)
  have htrim :
      (∫⁻ ω : S → E, (tailKernel (S := S) (E := E) μ ω) A ∂μ)
        =
      ∫⁻ ω : S → E, (tailKernel (S := S) (E := E) μ ω) A ∂(μ.trim hm) := by
    have hmeas_tail :
        Measurable[@tailSigmaAlgebra S E _] (fun ω : S → E => (tailKernel (S := S) (E := E) μ ω) A) := by
      exact (ProbabilityTheory.Kernel.measurable_coe (tailKernel (S := S) (E := E) μ) hA)
    simp [MeasureTheory.lintegral_trim hm hmeas_tail]
  have hdis :
      ∫⁻ ω : S → E, (tailKernel (S := S) (E := E) μ ω) A ∂(μ.trim hm) = μ A := by
    have hκ_tail : Measurable[@tailSigmaAlgebra S E _] (tailKernel (S := S) (E := E) μ) :=
      (tailKernel (S := S) (E := E) μ).measurable
    have hbind :
        (tailKernel (S := S) (E := E) μ ∘ₘ (μ.trim hm)) A
          = ∫⁻ ω : S → E, (tailKernel (S := S) (E := E) μ ω) A ∂(μ.trim hm) := by
      simp [Measure.bind_apply hA hκ_tail.aemeasurable]
    have hcomp : tailKernel (S := S) (E := E) μ ∘ₘ (μ.trim hm) = μ := by
      simpa using tailKernel_comp_trim (S := S) (E := E) (μ := μ)
    simpa [hbind] using congrArg (fun m' : Measure (S → E) => m' A) hcomp
  calc
    (∫⁻ ν : Measure (S → E), ν A ∂(tailKernelLaw (S := S) (E := E) μ))
        = ∫⁻ ω : S → E, (tailKernel (S := S) (E := E) μ ω) A ∂μ := hmap
    _ = ∫⁻ ω : S → E, (tailKernel (S := S) (E := E) μ ω) A ∂(μ.trim hm) := htrim
    _ = μ A := hdis

lemma join_tailKernelLaw :
    MeasureTheory.Measure.join (tailKernelLaw (S := S) (E := E) μ) = μ := by
  ext A hA
  simpa [MeasureTheory.Measure.join_apply (m := tailKernelLaw (S := S) (E := E) μ) hA] using
    (lintegral_eval_tailKernelLaw (S := S) (E := E) (μ := μ) A hA)

lemma isProbabilityMeasure_tailKernelLaw :
    IsProbabilityMeasure (tailKernelLaw (S := S) (E := E) μ) := by
  have hmeas : Measurable (tailKernel (S := S) (E := E) μ) :=
    measurable_tailKernel_pi (S := S) (E := E) (μ := μ)
  simpa [tailKernelLaw] using (MeasureTheory.Measure.isProbabilityMeasure_map (μ := μ) hmeas.aemeasurable)

/-! ### A `ProbabilityMeasure` version of `tailKernelLaw` -/

/-- `tailKernelLaw` packaged as a probability measure (when `μ` is a probability measure). -/
noncomputable def tailKernelLawPM (μ : ProbabilityMeasure (S → E)) : ProbabilityMeasure (Measure (S → E)) :=
  ⟨tailKernelLaw (S := S) (E := E) (μ := (μ : Measure (S → E))), by
    simpa using
      (isProbabilityMeasure_tailKernelLaw (S := S) (E := E) (μ := (μ : Measure (S → E))))⟩

/-! ## Tail-determinism of the tail kernel (hence tail-triviality of its conditional measures) -/

/-- View the tail kernel as a kernel into the **tail σ-algebra**, by mapping each conditional
measure along `id : (S → E) → (S → E)` from `MeasurableSpace.pi` to `𝓣`. -/
noncomputable def tailKernelTail :
    Kernel[@tailSigmaAlgebra S E _, @tailSigmaAlgebra S E _] (S → E) (S → E) :=
  @ProbabilityTheory.Kernel.map (α := (S → E)) (β := (S → E)) (γ := (S → E))
    (@tailSigmaAlgebra S E _) MeasurableSpace.pi (@tailSigmaAlgebra S E _)
    (tailKernel (S := S) (E := E) μ) id

instance : IsMarkovKernel (tailKernelTail (S := S) (E := E) μ) := by
  have hid :
      @Measurable (S → E) (S → E) MeasurableSpace.pi (@tailSigmaAlgebra S E _) id :=
    measurable_id.mono le_rfl (tailSigmaAlgebra_le_pi (S := S) (E := E))
  simpa [tailKernelTail] using
    (ProbabilityTheory.Kernel.IsMarkovKernel.map (κ := tailKernel (S := S) (E := E) μ) (f := id) hid)

lemma tailKernelTail_apply (ω : S → E) :
    tailKernelTail (S := S) (E := E) μ ω =
      @Measure.map (S → E) (S → E) MeasurableSpace.pi (@tailSigmaAlgebra S E _)
        id (tailKernel (S := S) (E := E) μ ω) := by
  have hid :
      @Measurable (S → E) (S → E) MeasurableSpace.pi (@tailSigmaAlgebra S E _) id :=
    measurable_id.mono le_rfl (tailSigmaAlgebra_le_pi (S := S) (E := E))
  simp [tailKernelTail, ProbabilityTheory.Kernel.map_apply, hid]

lemma tailKernelTail_ae_eq_id
    [@MeasurableSpace.CountableOrCountablyGenerated (S → E) (S → E) (@tailSigmaAlgebra S E _)] :
    ∀ᵐ ω ∂μ.trim (tailSigmaAlgebra_le_pi (S := S) (E := E)),
      tailKernelTail (S := S) (E := E) μ ω
        = (@ProbabilityTheory.Kernel.id (S → E) (@tailSigmaAlgebra S E _)) ω := by
  have hm : (@tailSigmaAlgebra S E _ : MeasurableSpace (S → E)) ≤ MeasurableSpace.pi :=
    tailSigmaAlgebra_le_pi (S := S) (E := E)
  let μT : Measure[@tailSigmaAlgebra S E _] (S → E) := μ.trim hm
  haveI : IsProbabilityMeasure μT := by
    refine ⟨?_⟩
    have : μT Set.univ = μ Set.univ := by
      simpa [μT] using
        (MeasureTheory.trim_measurableSet_eq (μ := μ) hm
          (MeasurableSet.univ :
            MeasurableSet[@tailSigmaAlgebra S E _] (Set.univ : Set (S → E))))
    simp [this]
  have hcompProd :
      @Measure.compProd (S → E) (S → E) (@tailSigmaAlgebra S E _) (@tailSigmaAlgebra S E _)
        μT (tailKernelTail (S := S) (E := E) μ)
        =
      @Measure.compProd (S → E) (S → E) (@tailSigmaAlgebra S E _) (@tailSigmaAlgebra S E _)
        μT
          (ProbabilityTheory.Kernel.id :
            Kernel[@tailSigmaAlgebra S E _, @tailSigmaAlgebra S E _] (S → E) (S → E)) := by
    let C : Set (Set ((S → E) × (S → E))) :=
      Set.image2 (fun s t => s ×ˢ t)
        ({s : Set (S → E) | MeasurableSet[@tailSigmaAlgebra S E _] s})
        ({t : Set (S → E) | MeasurableSet[@tailSigmaAlgebra S E _] t})
    have hgen :
        (@Prod.instMeasurableSpace (S → E) (S → E) (@tailSigmaAlgebra S E _) (@tailSigmaAlgebra S E _))
          = MeasurableSpace.generateFrom C := by
      simpa [C] using
        (show MeasurableSpace.generateFrom C =
              (@Prod.instMeasurableSpace (S → E) (S → E) (@tailSigmaAlgebra S E _) (@tailSigmaAlgebra S E _)) from
          (@generateFrom_prod (α := (S → E)) (β := (S → E))
            (@tailSigmaAlgebra S E _) (@tailSigmaAlgebra S E _))).symm
    have hpi : IsPiSystem C := by
      simpa [C] using
        (show IsPiSystem C from
          (@isPiSystem_prod (α := (S → E)) (β := (S → E))
            (@tailSigmaAlgebra S E _) (@tailSigmaAlgebra S E _)))
    haveI : IsProbabilityMeasure (μT ⊗ₘ tailKernelTail (S := S) (E := E) μ) := by infer_instance
    haveI :
        IsProbabilityMeasure
          (μT ⊗ₘ
            (ProbabilityTheory.Kernel.id :
              Kernel[@tailSigmaAlgebra S E _, @tailSigmaAlgebra S E _] (S → E) (S → E))) := by
      infer_instance
    refine
      MeasureTheory.Measure.ext_of_generate_finite_of_isProbabilityMeasure (C := C)
        (m0 := (@Prod.instMeasurableSpace (S → E) (S → E)
          (@tailSigmaAlgebra S E _) (@tailSigmaAlgebra S E _)))
        (μ := (μT ⊗ₘ tailKernelTail (S := S) (E := E) μ))
        (ν := (μT ⊗ₘ
          (ProbabilityTheory.Kernel.id :
            Kernel[@tailSigmaAlgebra S E _, @tailSigmaAlgebra S E _] (S → E) (S → E))))
        (hA := hgen) (hC := hpi) ?_
    intro s hsC
    rcases hsC with ⟨A, hA, B, hB, rfl⟩
    have hA' : MeasurableSet[@tailSigmaAlgebra S E _] A := hA
    have hB' : MeasurableSet[@tailSigmaAlgebra S E _] B := hB
    have hLHS :
        (μT ⊗ₘ tailKernelTail (S := S) (E := E) μ) (A ×ˢ B)
          = ∫⁻ ω in A, (tailKernelTail (S := S) (E := E) μ ω) B ∂μT := by
      simp [MeasureTheory.Measure.compProd_apply_prod hA' hB']
    have hRHS :
        (μT ⊗ₘ
          (ProbabilityTheory.Kernel.id :
            Kernel[@tailSigmaAlgebra S E _, @tailSigmaAlgebra S E _] (S → E) (S → E))) (A ×ˢ B)
          = ∫⁻ ω in A, (B.indicator (fun _ : S → E => (1 : ℝ≥0∞)) ω) ∂μT := by
      have : ∀ ω : S → E,
          (ProbabilityTheory.Kernel.id :
            Kernel[@tailSigmaAlgebra S E _, @tailSigmaAlgebra S E _] (S → E) (S → E)) ω B =
            B.indicator (fun _ : S → E => (1 : ℝ≥0∞)) ω := by
        intro ω
        -- Unfold `Kernel.id` (in the tail σ-algebra) to a Dirac measure, then evaluate.
        change (@Measure.dirac (S → E) (@tailSigmaAlgebra S E _) ω) B =
          B.indicator (fun _ : S → E => (1 : ℝ≥0∞)) ω
        simpa [Set.indicator] using
          (@Measure.dirac_apply' (α := (S → E)) (@tailSigmaAlgebra S E _) (a := ω) (s := B) hB')
      simp [MeasureTheory.Measure.compProd_apply_prod hA' hB', this]
    have hB_val :
        (fun ω : S → E => (tailKernel (S := S) (E := E) μ ω) B)
          =ᵐ[μT] (B.indicator (fun _ : S → E => (1 : ℝ≥0∞))) := by
      have hreal :=
        tailKernel_real_eq_indicator_of_measurableSet (S := S) (E := E) (μ := μ) (A := B) hB'
      filter_upwards [hreal] with ω hω
      have hω' :
          ((tailKernel (S := S) (E := E) μ ω) B).toReal =
            (B.indicator (fun _ : S → E => (1 : ℝ)) ω) := by
        simpa [MeasureTheory.measureReal_def] using hω
      have hne_top : (tailKernel (S := S) (E := E) μ ω) B ≠ (⊤ : ℝ≥0∞) := by
        haveI : IsProbabilityMeasure (tailKernel (S := S) (E := E) μ ω) :=
          ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure (κ := tailKernel (S := S) (E := E) μ) ω
        exact measure_ne_top _ _
      have hne_top' :
          (B.indicator (fun _ : S → E => (1 : ℝ≥0∞)) ω) ≠ (⊤ : ℝ≥0∞) := by
        by_cases hωB : ω ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hωB]
      have : (tailKernel (S := S) (E := E) μ ω) B =
          (B.indicator (fun _ : S → E => (1 : ℝ≥0∞)) ω) := by
        by_cases hωB : ω ∈ B
        · have : (B.indicator (fun _ : S → E => (1 : ℝ)) ω) = 1 := by simp [Set.indicator_of_mem, hωB]
          have : ((tailKernel (S := S) (E := E) μ ω) B).toReal = 1 := by simpa [this] using hω'
          have : (tailKernel (S := S) (E := E) μ ω) B = 1 := by
            exact (ENNReal.toReal_eq_toReal_iff' hne_top (by simp)).1 (by simpa using this)
          simpa [Set.indicator_of_mem, hωB] using this
        · have : (B.indicator (fun _ : S → E => (1 : ℝ)) ω) = 0 := by simp [Set.indicator_of_notMem, hωB]
          have : ((tailKernel (S := S) (E := E) μ ω) B).toReal = 0 := by simpa [this] using hω'
          have : (tailKernel (S := S) (E := E) μ ω) B = 0 := by
            exact (ENNReal.toReal_eq_toReal_iff' hne_top (by simp)).1 (by simpa using this)
          simpa [Set.indicator_of_notMem, hωB] using this
      simp [this]
    have hB_val_restrict :
        (fun ω : S → E => (tailKernelTail (S := S) (E := E) μ ω) B)
          =ᵐ[μT.restrict A] (B.indicator (fun _ : S → E => (1 : ℝ≥0∞))) := by
      have hB_val' :
          (fun ω : S → E => (tailKernelTail (S := S) (E := E) μ ω) B)
            =ᵐ[μT] (B.indicator (fun _ : S → E => (1 : ℝ≥0∞))) := by
        have hid :
            @Measurable (S → E) (S → E) MeasurableSpace.pi (@tailSigmaAlgebra S E _) id :=
          measurable_id.mono le_rfl hm
        filter_upwards [hB_val] with ω hω
        have hmap :
            (tailKernelTail (S := S) (E := E) μ ω) B =
              (tailKernel (S := S) (E := E) μ ω) B := by
          simpa [tailKernelTail, ProbabilityTheory.Kernel.map_apply', hid, hB'] using
            (ProbabilityTheory.Kernel.map_apply'
              (κ := tailKernel (S := S) (E := E) μ)
              (f := (id : (S → E) → (S → E))) hid ω hB')
        simpa [hmap] using hω
      exact MeasureTheory.ae_restrict_of_ae (μ := μT) (s := A) hB_val'
    have hI :
        ∫⁻ ω in A, (tailKernelTail (S := S) (E := E) μ ω) B ∂μT
          = ∫⁻ ω in A, (B.indicator (fun _ : S → E => (1 : ℝ≥0∞)) ω) ∂μT := by
      simp [MeasureTheory.lintegral_congr_ae hB_val_restrict]
    simp [hLHS, hRHS, hI]
  haveI : MeasurableSpace.CountableOrCountablyGenerated (S → E) (S → E) :=
    MeasurableSpace.instCountableOrCountablyGeneratedOfCountablyGenerated
  haveI :
      IsFiniteKernel
        (ProbabilityTheory.Kernel.id :
          Kernel[@tailSigmaAlgebra S E _, @tailSigmaAlgebra S E _] (S → E) (S → E)) := by
    infer_instance
  haveI : MeasurableSpace.CountablyGenerated (S → E) :=
    countablyGenerated_of_standardBorel
  simpa [μT, hm] using
    (ProbabilityTheory.Kernel.ae_eq_of_compProd_eq (μ := μT)
      (κ := tailKernelTail (S := S) (E := E) μ)
      (η := (ProbabilityTheory.Kernel.id :
        Kernel[@tailSigmaAlgebra S E _, @tailSigmaAlgebra S E _] (S → E) (S → E)))
      hcompProd)

/-! ### Pointwise tail determinism (0–1 law for tail events) -/

lemma ae_tailKernel_apply_eq_indicator
    [@MeasurableSpace.CountableOrCountablyGenerated (S → E) (S → E) (@tailSigmaAlgebra S E _)] :
    ∀ᵐ ω ∂μ.trim (tailSigmaAlgebra_le_pi (S := S) (E := E)),
      ∀ A : Set (S → E), MeasurableSet[@tailSigmaAlgebra S E _] A →
        (tailKernel (S := S) (E := E) μ ω) A
          = A.indicator (fun _ : (S → E) => (1 : ℝ≥0∞)) ω := by
  have h := tailKernelTail_ae_eq_id (S := S) (E := E) (μ := μ)
  filter_upwards [h] with ω hω A hA
  have h_eval :
      (tailKernelTail (S := S) (E := E) μ ω) A
        = (@ProbabilityTheory.Kernel.id (S → E) (@tailSigmaAlgebra S E _)) ω A := by
    simpa using congrArg (fun m : Measure[@tailSigmaAlgebra S E _] (S → E) => m A) hω
  have hid :
      @Measurable (S → E) (S → E) MeasurableSpace.pi (@tailSigmaAlgebra S E _) id :=
    measurable_id.mono le_rfl (tailSigmaAlgebra_le_pi (S := S) (E := E))
  have hL :
      (tailKernelTail (S := S) (E := E) μ ω) A = (tailKernel (S := S) (E := E) μ ω) A := by

    simp [tailKernelTail_apply (S := S) (E := E) (μ := μ) ω,
      Measure.map_apply hid hA, Set.preimage_id]
  have hR :
      (@ProbabilityTheory.Kernel.id (S → E) (@tailSigmaAlgebra    S E _)) ω A
        = A.indicator (fun _ : (S → E) => (1 : ℝ≥0∞)) ω := by
    letI : MeasurableSpace (S → E) := @tailSigmaAlgebra S E _
    have hdirac : (MeasureTheory.Measure.dirac ω) A = A.indicator (fun _ : (S → E) => (1 : ℝ≥0∞)) ω :=
      by simpa using (MeasureTheory.Measure.dirac_apply' (a := ω) (s := A) hA)
    simpa [ProbabilityTheory.Kernel.id_apply (mα := (@tailSigmaAlgebra S E _)) ω] using hdirac
  simpa [hL, hR] using h_eval

/-- For `μ.trim 𝓣`-a.e. `ω`, integrating a tail-measurable function against the conditional
measure `tailKernel μ ω` evaluates the function at `ω`.

This is the functional form of the tail determinism `tailKernelTail μ ω = δ_ω`. -/
lemma ae_lintegral_tailKernel_eq
    [@MeasurableSpace.CountableOrCountablyGenerated (S → E) (S → E) (@tailSigmaAlgebra S E _)]
    (f : (S → E) → ℝ≥0∞) (hf : @Measurable (S → E) ℝ≥0∞ (@tailSigmaAlgebra S E _) _ f) :
    ∀ᵐ ω ∂μ.trim (tailSigmaAlgebra_le_pi (S := S) (E := E)),
      (∫⁻ x, f x ∂(tailKernel (S := S) (E := E) μ ω)) = f ω := by
  have h := tailKernelTail_ae_eq_id (S := S) (E := E) (μ := μ)
  filter_upwards [h] with ω hω
  have hid :
      @Measurable (S → E) (S → E) MeasurableSpace.pi (@tailSigmaAlgebra S E _) id :=
    measurable_id.mono le_rfl (tailSigmaAlgebra_le_pi (S := S) (E := E))
  have hmap :
      (∫⁻ x, f x ∂(tailKernelTail (S := S) (E := E) μ ω))
        =
      (∫⁻ x, f x ∂(tailKernel (S := S) (E := E) μ ω)) := by
    have hlintegral :
        (∫⁻ x, f x ∂(@Measure.map (S → E) (S → E) MeasurableSpace.pi (@tailSigmaAlgebra S E _)
          id (tailKernel (S := S) (E := E) μ ω)))
          =
        (∫⁻ x, f x ∂(tailKernel (S := S) (E := E) μ ω)) := by
      simpa using
        (@MeasureTheory.lintegral_map (S → E) (S → E)
          MeasurableSpace.pi (@tailSigmaAlgebra S E _)
          (tailKernel (S := S) (E := E) μ ω) (f := f) (g := id) hf hid)
    simpa [tailKernelTail_apply (S := S) (E := E) (μ := μ) ω] using hlintegral
  have hdirac :
      (∫⁻ x, f x ∂(tailKernelTail (S := S) (E := E) μ ω)) = f ω := by
    letI : MeasurableSpace (S → E) := @tailSigmaAlgebra S E _
    have : (tailKernelTail (S := S) (E := E) μ ω) = Measure.dirac ω := by
      simpa [ProbabilityTheory.Kernel.id_apply (mα := (@tailSigmaAlgebra S E _)) ω] using hω
    simpa [this] using (MeasureTheory.lintegral_dirac' (a := ω) hf)
  have : (∫⁻ x, f x ∂(tailKernel (S := S) (E := E) μ ω))
      = ∫⁻ x, f x ∂(tailKernelTail (S := S) (E := E) μ ω) := by
    simpa using hmap.symm
  simpa [this] using hdirac

/-- On tail events `B`, the conditional measure `tailKernel μ ω` behaves like a Dirac measure at `ω`,
so intersections with `B` factor as multiplication by `1_B(ω)`. -/
lemma ae_tailKernel_inter_eq_indicator_mul
    [@MeasurableSpace.CountableOrCountablyGenerated (S → E) (S → E) (@tailSigmaAlgebra S E _)]
    {A B : Set (S → E)} (hB : MeasurableSet[@tailSigmaAlgebra S E _] B) :
    ∀ᵐ ω ∂μ.trim (tailSigmaAlgebra_le_pi (S := S) (E := E)),
      (tailKernel (S := S) (E := E) μ ω) (A ∩ B)
        =
      (B.indicator (fun _ : (S → E) => (1 : ℝ≥0∞)) ω) * (tailKernel (S := S) (E := E) μ ω) A := by
  have h := ae_tailKernel_apply_eq_indicator (S := S) (E := E) (μ := μ)
  filter_upwards [h] with ω hω
  have hB_pi : MeasurableSet B :=
    (tailSigmaAlgebra_le_pi (S := S) (E := E)) B hB
  by_cases hωB : ω ∈ B
  · have h_one : (tailKernel (S := S) (E := E) μ ω) B = 1 := by
      simpa [Set.indicator_of_mem, hωB] using (hω B hB)
    have h_ae : ∀ᵐ x ∂(tailKernel (S := S) (E := E) μ ω), x ∈ B := by
      have h_zero : (tailKernel (S := S) (E := E) μ ω) (Bᶜ) = 0 := by
        haveI : IsProbabilityMeasure (tailKernel (S := S) (E := E) μ ω) :=
          ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure
            (κ := tailKernel (S := S) (E := E) μ) ω
        simp [h_one, hB_pi]
      refine (MeasureTheory.ae_iff (μ := tailKernel (S := S) (E := E) μ ω) (p := fun x => x ∈ B)).2 ?_
      simpa using h_zero
    have h_inter : (tailKernel (S := S) (E := E) μ ω) (B ∩ A) = (tailKernel (S := S) (E := E) μ ω) A :=
      Measure.measure_inter_eq_of_ae (μ := tailKernel (S := S) (E := E) μ ω) (s := A) (t := B) h_ae
    have : (tailKernel (S := S) (E := E) μ ω) (A ∩ B) = (tailKernel (S := S) (E := E) μ ω) A := by
      simpa [inter_comm, inter_left_comm, inter_assoc] using h_inter
    simp [this, Set.indicator_of_mem, hωB]
  · have h_zero : (tailKernel (S := S) (E := E) μ ω) B = 0 := by
      simpa [Set.indicator_of_notMem, hωB] using (hω B hB)
    have : (tailKernel (S := S) (E := E) μ ω) (A ∩ B) = 0 := by
      exact le_antisymm (le_trans (measure_mono (by intro x hx; exact hx.2)) (le_of_eq h_zero)) (zero_le _)
    simp [this, Set.indicator_of_notMem, hωB]

/-- For `μ.trim 𝓣`-a.e. `ω`, the conditional measure `tailKernel μ ω` is tail-trivial. -/
theorem ae_isTailTrivial_tailKernel
    [@MeasurableSpace.CountableOrCountablyGenerated (S → E) (S → E) (@tailSigmaAlgebra S E _)] :
    ∀ᵐ ω ∂μ.trim (tailSigmaAlgebra_le_pi (S := S) (E := E)),
      IsTailTrivial (S := S) (E := E)
        (μ := (⟨tailKernel (S := S) (E := E) μ ω, by
          -- each fiber of a Markov kernel is a probability measure
          infer_instance⟩ : ProbabilityMeasure (S → E))) := by
  filter_upwards [ae_tailKernel_apply_eq_indicator (S := S) (E := E) (μ := μ)] with ω hω
  intro A hA
  have hA' := hω A hA
  by_cases hωA : ω ∈ A
  · right
    simpa [Set.indicator_of_mem, hωA] using hA'
  · left
    simpa [Set.indicator_of_notMem, hωA] using hA'

/-!
### Gibbs fixed-point transported to the tail disintegration (measure-level)

This is a clean “bookkeeping” lemma: from the DLR fixed point `μ.bind (γ Λ) = μ` and the
disintegration identity `tailKernel μ ∘ₘ μ.trim = μ`, we get an equality of composed measures after
pushing `γ Λ` through the tail-kernel disintegration.

This is the right starting point for the (harder) a.e.-Gibbsness of the conditional measures.
-/

section GibbsComp

variable {γ : Specification S E} [γ.IsMarkov]

variable (Λ : Finset S)

/-! #### A tail-parameterized DLR identity (measure-level) -/

omit [Countable S] [StandardBorelSpace E] in
/-- If `μ` is Gibbs for `γ`, then for a tail event `B` (hence also `Λᶜ`-measurable),
the DLR identity reads `μ(A ∩ B) = ∫⁻ ω in B, γ Λ ω A ∂μ`. -/
lemma isGibbsMeasure_measure_inter_eq_setLIntegral
    (hγ : γ.IsProper) (hμ : γ.IsGibbsMeasure μ)
    {A B : Set (S → E)} (hA : MeasurableSet A) (hB : MeasurableSet[@tailSigmaAlgebra S E _] B) :
    μ (A ∩ B) = ∫⁻ ω in B, (γ Λ ω) A ∂μ := by
  -- Use the fixed point `μ.bind (γ Λ) = μ`.
  have hfix : μ.bind (γ Λ) = μ :=
    ((Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob (γ := γ) hγ).1 hμ) Λ
  have hB_pi : MeasurableSet B :=
    (tailSigmaAlgebra_le_pi (S := S) (E := E)) B hB
  have hB_cyl : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] B :=
    (tailSigmaAlgebra_le_cylinderEvents (S := S) (E := E) Λ) B hB
  have hAB : MeasurableSet (A ∩ B) := hA.inter hB_pi
  have hmeasγ : Measurable (γ Λ : (S → E) → Measure (S → E)) :=
    (ProbabilityTheory.Kernel.measurable (γ Λ)).mono cylinderEvents_le_pi le_rfl
  have hbind :
      (μ.bind (γ Λ)) (A ∩ B) = ∫⁻ ω, (γ Λ ω) (A ∩ B) ∂μ := by
    simp [Measure.bind_apply hAB hmeasγ.aemeasurable]
  have hprop : ∀ ω, (γ Λ ω) (A ∩ B) =
      (B.indicator (fun _ : (S → E) => (1 : ℝ≥0∞)) ω) * (γ Λ ω) A := by
    intro ω
    simpa using (hγ.inter_eq_indicator_mul (Λ := Λ) (A := A) (B := B) hA hB_cyl ω)
  have hind :
      (fun ω => (B.indicator (fun _ : (S → E) => (1 : ℝ≥0∞)) ω) * (γ Λ ω) A)
        =
      fun ω => B.indicator (fun ω => (γ Λ ω) A) ω := by
    funext ω
    by_cases hω : ω ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
  calc
    μ (A ∩ B) = (μ.bind (γ Λ)) (A ∩ B) := by simp [hfix]
    _ = ∫⁻ ω, (γ Λ ω) (A ∩ B) ∂μ := hbind
    _ = ∫⁻ ω, (B.indicator (fun _ : (S → E) => (1 : ℝ≥0∞)) ω) * (γ Λ ω) A ∂μ := by
          simp_rw [hprop]
    _ = ∫⁻ ω, B.indicator (fun ω => (γ Λ ω) A) ω ∂μ := by
          simp [hind]
    _ = ∫⁻ ω in B, (γ Λ ω) A ∂μ := by
          have hmeasA : Measurable fun ω : S → E => (γ Λ ω) A :=
            (ProbabilityTheory.Kernel.measurable_coe (γ Λ) hA).mono
              (MeasureTheory.cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := ((Λ : Set S)ᶜ))) le_rfl
          simp [hB_pi]

/-!
#### Tail-conditional measures are Gibbs: kernel fixed point for a fixed `Λ`
-/

private lemma ae_lintegral_indicator_eq_indicator_lintegral
    [@MeasurableSpace.CountableOrCountablyGenerated (S → E) (S → E) (@tailSigmaAlgebra S E _)]
    {B : Set (S → E)} (hB : MeasurableSet[@tailSigmaAlgebra S E _] B)
    (g : (S → E) → ℝ≥0∞) (_hg : Measurable g) :
    ∀ᵐ ω ∂μ.trim (tailSigmaAlgebra_le_pi (S := S) (E := E)),
      (∫⁻ x, B.indicator g x ∂(tailKernel (S := S) (E := E) μ ω))
        =
      B.indicator (fun ω => ∫⁻ x, g x ∂(tailKernel (S := S) (E := E) μ ω)) ω := by
  have htail := ae_tailKernel_apply_eq_indicator (S := S) (E := E) (μ := μ)
  have hB_pi : MeasurableSet B :=
    (tailSigmaAlgebra_le_pi (S := S) (E := E)) B hB
  filter_upwards [htail] with ω hω
  by_cases hωB : ω ∈ B
  · have h_one : (tailKernel (S := S) (E := E) μ ω) B = 1 := by
      simpa [Set.indicator_of_mem, hωB] using hω B hB
    have h_aeB : ∀ᵐ x ∂(tailKernel (S := S) (E := E) μ ω), x ∈ B := by
      have h_zero : (tailKernel (S := S) (E := E) μ ω) (Bᶜ) = 0 := by
        haveI : IsProbabilityMeasure (tailKernel (S := S) (E := E) μ ω) :=
          ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure
            (κ := tailKernel (S := S) (E := E) μ) ω
        simp [h_one, hB_pi]
      refine (MeasureTheory.ae_iff (μ := tailKernel (S := S) (E := E) μ ω) (p := fun x => x ∈ B)).2 ?_
      simpa using h_zero
    have hind :
        (fun x => B.indicator g x) =ᵐ[(tailKernel (S := S) (E := E) μ ω)] g := by
      filter_upwards [h_aeB] with x hx
      simp [Set.indicator_of_mem, hx]
    have hlintegral :
        (∫⁻ x, B.indicator g x ∂(tailKernel (S := S) (E := E) μ ω))
          =
        (∫⁻ x, g x ∂(tailKernel (S := S) (E := E) μ ω)) := by
      simpa using (MeasureTheory.lintegral_congr_ae hind)
    simp [Set.indicator_of_mem, hωB, hlintegral]
  · have h_zero : (tailKernel (S := S) (E := E) μ ω) B = 0 := by
      simpa [Set.indicator_of_notMem, hωB] using hω B hB
    have h_aeB : ∀ᵐ x ∂(tailKernel (S := S) (E := E) μ ω), x ∉ B := by
      refine (MeasureTheory.ae_iff (μ := tailKernel (S := S) (E := E) μ ω) (p := fun x => x ∉ B)).2 ?_
      simpa using h_zero
    have hind :
        (fun x => B.indicator g x) =ᵐ[(tailKernel (S := S) (E := E) μ ω)] 0 := by
      filter_upwards [h_aeB] with x hx
      simp [Set.indicator_of_notMem, hx]
    have hlintegral :
        (∫⁻ x, B.indicator g x ∂(tailKernel (S := S) (E := E) μ ω)) = 0 := by
      simpa using (MeasureTheory.lintegral_congr_ae hind)
    simp [Set.indicator_of_notMem, hωB, hlintegral]

/-- For a fixed finite volume `Λ`, the tail kernel is `μ.trim 𝓣`-a.e. a fixed point for `γ Λ`. -/
lemma ae_comp_comap_tailKernel_eq_tailKernel
    [@MeasurableSpace.CountableOrCountablyGenerated (S → E) (S → E) (@tailSigmaAlgebra S E _)]
    (hγ : γ.IsProper) (hμ : γ.IsGibbsMeasure μ) :
    ∀ᵐ ω ∂μ.trim (tailSigmaAlgebra_le_pi (S := S) (E := E)),
      ((γ Λ).comap id cylinderEvents_le_pi ∘ₖ tailKernel (S := S) (E := E) μ) ω
        = tailKernel (S := S) (E := E) μ ω := by
  let hm : (@tailSigmaAlgebra S E _ : MeasurableSpace (S → E)) ≤ MeasurableSpace.pi :=
    tailSigmaAlgebra_le_pi (S := S) (E := E)
  let μT : Measure[@tailSigmaAlgebra S E _] (S → E) := μ.trim hm
  haveI : IsProbabilityMeasure μT := by
    refine ⟨?_⟩
    have : μT Set.univ = μ Set.univ := by
      simpa [μT] using
        (MeasureTheory.trim_measurableSet_eq (μ := μ) hm
          (MeasurableSet.univ :
            MeasurableSet[@tailSigmaAlgebra S E _] (Set.univ : Set (S → E))))
    simp [this]
  let κ₁ : Kernel[@tailSigmaAlgebra S E _] (S → E) (S → E) :=
    (γ Λ).comap id cylinderEvents_le_pi ∘ₖ tailKernel (S := S) (E := E) μ
  let κ₂ : Kernel[@tailSigmaAlgebra S E _] (S → E) (S → E) :=
    tailKernel (S := S) (E := E) μ
  have hcompProd : μT ⊗ₘ κ₁ = μT ⊗ₘ κ₂ := by
    let C : Set (Set ((S → E) × (S → E))) :=
      Set.image2 (fun s t => s ×ˢ t)
        ({s : Set (S → E) | MeasurableSet[@tailSigmaAlgebra S E _] s})
        ({t : Set (S → E) | MeasurableSet t})
    have hgen :
        (@Prod.instMeasurableSpace (S → E) (S → E) (@tailSigmaAlgebra S E _) MeasurableSpace.pi)
          = MeasurableSpace.generateFrom C := by
      simpa [C] using
        (show MeasurableSpace.generateFrom C =
              (@Prod.instMeasurableSpace (S → E) (S → E) (@tailSigmaAlgebra S E _) MeasurableSpace.pi) from
          (@generateFrom_prod (α := (S → E)) (β := (S → E))
            (@tailSigmaAlgebra S E _) MeasurableSpace.pi)).symm
    have hpi : IsPiSystem C := by
      simpa [C] using
        (show IsPiSystem C from
          (@isPiSystem_prod (α := (S → E)) (β := (S → E))
            (@tailSigmaAlgebra S E _) MeasurableSpace.pi))
    haveI : IsMarkovKernel κ₁ := by infer_instance
    haveI : IsMarkovKernel κ₂ := by infer_instance
    haveI : IsProbabilityMeasure (μT ⊗ₘ κ₁) := by infer_instance
    haveI : IsProbabilityMeasure (μT ⊗ₘ κ₂) := by infer_instance
    refine
      MeasureTheory.Measure.ext_of_generate_finite_of_isProbabilityMeasure (C := C)
        (m0 := (@Prod.instMeasurableSpace (S → E) (S → E) (@tailSigmaAlgebra S E _) MeasurableSpace.pi))
        (μ := (μT ⊗ₘ κ₁)) (ν := (μT ⊗ₘ κ₂)) (hA := hgen) (hC := hpi) ?_
    intro s hsC
    rcases hsC with ⟨B, hB, A, hA, rfl⟩
    have hB' : MeasurableSet[@tailSigmaAlgebra S E _] B := hB
    have hA' : MeasurableSet A := hA
    have hB_pi : MeasurableSet B := hm _ hB'
    have h_rhs :
        (∫⁻ ω in B, κ₂ ω A ∂μT) = μ (A ∩ B) := by
      have hcomp : κ₂ ∘ₘ μT = μ := by
        simpa [κ₂, μT, hm] using tailKernel_comp_trim (S := S) (E := E) (μ := μ)
      have hAB_pi : MeasurableSet (A ∩ B) := hA'.inter hB_pi
      have hbind :
          (κ₂ ∘ₘ μT) (A ∩ B) = ∫⁻ ω, κ₂ ω (A ∩ B) ∂μT := by
        have hκ₂_tail : Measurable[@tailSigmaAlgebra S E _] κ₂ := by
          simpa [κ₂] using (κ₂.measurable : Measurable[@tailSigmaAlgebra S E _] κ₂)
        simp [Measure.bind_apply hAB_pi hκ₂_tail.aemeasurable]
      have hAE' :
          (fun ω => κ₂ ω (A ∩ B))
            =ᵐ[μT]
              (fun ω => (B.indicator (fun _ : (S → E) => (1 : ℝ≥0∞)) ω) * κ₂ ω A) := by
        simpa [κ₂] using
          (ae_tailKernel_inter_eq_indicator_mul (S := S) (E := E) (μ := μ) (A := A) (B := B) hB')
      have hind :
          (fun ω => (B.indicator (fun _ : (S → E) => (1 : ℝ≥0∞)) ω) * κ₂ ω A)
            = fun ω => B.indicator (fun ω => κ₂ ω A) ω := by
        funext ω
        by_cases hωB : ω ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hωB]
      have hI :
          (∫⁻ ω, κ₂ ω (A ∩ B) ∂μT) = ∫⁻ ω in B, κ₂ ω A ∂μT := by
        calc
          (∫⁻ ω, κ₂ ω (A ∩ B) ∂μT)
              = ∫⁻ ω, (B.indicator (fun _ : (S → E) => (1 : ℝ≥0∞)) ω) * κ₂ ω A ∂μT := by
                  exact MeasureTheory.lintegral_congr_ae hAE'
          _ = ∫⁻ ω, B.indicator (fun ω => κ₂ ω A) ω ∂μT := by simp [hind]
          _ = ∫⁻ ω in B, κ₂ ω A ∂μT := by
                simpa using (_root_.MeasureTheory.lintegral_indicator
                  (μ := μT) (s := B) (f := fun ω => κ₂ ω A) hB')
      calc
        (∫⁻ ω in B, κ₂ ω A ∂μT)
            = (∫⁻ ω, κ₂ ω (A ∩ B) ∂μT) := by simpa using hI.symm
        _ = (κ₂ ∘ₘ μT) (A ∩ B) := by simp [hbind]
        _ = μ (A ∩ B) := by simp [hcomp]
    have h_lhs :
        (∫⁻ ω in B, κ₁ ω A ∂μT) = μ (A ∩ B) := by
      have hgA : Measurable fun x : S → E => (γ Λ x) A :=
        (ProbabilityTheory.Kernel.measurable_coe (γ Λ) hA').mono cylinderEvents_le_pi le_rfl
      have hκ₁_apply :
          (fun ω => κ₁ ω A) = fun ω => ∫⁻ x, (γ Λ x) A ∂(κ₂ ω) := by
        funext ω
        simp [κ₁, κ₂, ProbabilityTheory.Kernel.comp_apply', ProbabilityTheory.Kernel.comap_apply, hA']
      have hswap :
          (fun ω => ∫⁻ x, B.indicator (fun x => (γ Λ x) A) x ∂(κ₂ ω))
            =ᵐ[μT]
          fun ω => B.indicator (fun ω => κ₁ ω A) ω := by
        have hpoint :=
          ae_lintegral_indicator_eq_indicator_lintegral (S := S) (E := E) (μ := μ)
            (B := B) hB' (g := fun x => (γ Λ x) A) hgA
        filter_upwards [hpoint] with ω hω
        have hrew :
            B.indicator (fun ω => ∫⁻ x, (γ Λ x) A ∂(κ₂ ω)) ω
              = B.indicator (fun ω => κ₁ ω A) ω := by
          simp [hκ₁_apply]
        simpa [κ₂, hrew] using hω
      have hμ_eq : (κ₂ ∘ₘ μT) = μ := by
        simpa [κ₂, μT, hm] using tailKernel_comp_trim (S := S) (E := E) (μ := μ)
      have hμB :
          (∫⁻ ω, B.indicator (fun ω => κ₁ ω A) ω ∂μT)
            =
          ∫⁻ x, B.indicator (fun x => (γ Λ x) A) x ∂μ := by
        have hμfun : AEMeasurable (fun ω => κ₂ ω) μT := κ₂.measurable.aemeasurable
        have hf_meas : Measurable fun x => B.indicator (fun x => (γ Λ x) A) x :=
          hgA.indicator hB_pi
        have hf_ae_bind :
            AEMeasurable (fun x => B.indicator (fun x => (γ Λ x) A) x)
              (Measure.bind μT κ₂) := hf_meas.aemeasurable
        calc
          (∫⁻ ω, B.indicator (fun ω => κ₁ ω A) ω ∂μT)
              = ∫⁻ ω, (∫⁻ x, B.indicator (fun x => (γ Λ x) A) x ∂(κ₂ ω)) ∂μT := by
                  simpa using (MeasureTheory.lintegral_congr_ae hswap.symm)
          _ = ∫⁻ x, B.indicator (fun x => (γ Λ x) A) x ∂(κ₂ ∘ₘ μT) := by
                symm
                simpa using (_root_.MeasureTheory.Measure.lintegral_bind (m := μT) (μ := κ₂)
                  (f := fun x => B.indicator (fun x => (γ Λ x) A) x) hμfun (by
                    simpa using hf_ae_bind))
          _ = ∫⁻ x, B.indicator (fun x => (γ Λ x) A) x ∂μ := by simp [hμ_eq]
      have hDLR :
          ∫⁻ x, B.indicator (fun x => (γ Λ x) A) x ∂μ = μ (A ∩ B) := by
        have h :=
          isGibbsMeasure_measure_inter_eq_setLIntegral (S := S) (E := E) (μ := μ)
            (γ := γ) (Λ := Λ) hγ hμ (A := A) (B := B) hA' hB'
        simpa [hB_pi] using h.symm
      calc
        (∫⁻ ω in B, κ₁ ω A ∂μT) = ∫⁻ ω, B.indicator (fun ω => κ₁ ω A) ω ∂μT := by
          simpa using (_root_.MeasureTheory.lintegral_indicator (μ := μT) (s := B)
            (f := fun ω => κ₁ ω A) hB').symm
        _ = ∫⁻ x, B.indicator (fun x => (γ Λ x) A) x ∂μ := by
              simpa [hκ₁_apply] using hμB
        _ = μ (A ∩ B) := hDLR
    calc
      (μT ⊗ₘ κ₁) (B ×ˢ A)
          = ∫⁻ ω in B, κ₁ ω A ∂μT := by
              simp [MeasureTheory.Measure.compProd_apply_prod hB' hA']
      _ = μ (A ∩ B) := h_lhs
      _ = ∫⁻ ω in B, κ₂ ω A ∂μT := by
              simpa using h_rhs.symm
      _ = (μT ⊗ₘ κ₂) (B ×ˢ A) := by
              symm
              simp [MeasureTheory.Measure.compProd_apply_prod hB' hA']
  haveI : MeasurableSpace.CountablyGenerated (S → E) := countablyGenerated_of_standardBorel
  haveI : MeasurableSpace.CountableOrCountablyGenerated (S → E) (S → E) :=
    MeasurableSpace.instCountableOrCountablyGeneratedOfCountablyGenerated
  have hkernel : κ₁ =ᵐ[μT] κ₂ :=
    ProbabilityTheory.Kernel.ae_eq_of_compProd_eq (μ := μT) (κ := κ₁) (η := κ₂) hcompProd
  simpa [μT, hm, κ₁, κ₂] using hkernel

lemma ae_forall_bind_eq_tailKernel
    [@MeasurableSpace.CountableOrCountablyGenerated (S → E) (S → E) (@tailSigmaAlgebra S E _)]
    (hγ : γ.IsProper) (hμ : γ.IsGibbsMeasure μ) :
    ∀ᵐ ω ∂μ.trim (tailSigmaAlgebra_le_pi (S := S) (E := E)),
      ∀ Λ : Finset S, (tailKernel (S := S) (E := E) μ ω).bind (γ Λ) = tailKernel (S := S) (E := E) μ ω := by
  have hΛ :
      ∀ Λ : Finset S,
        ∀ᵐ ω ∂μ.trim (tailSigmaAlgebra_le_pi (S := S) (E := E)),
          (tailKernel (S := S) (E := E) μ ω).bind ((γ Λ).comap id cylinderEvents_le_pi)
            = tailKernel (S := S) (E := E) μ ω := by
    intro Λ
    have hcomp :=
      ae_comp_comap_tailKernel_eq_tailKernel (S := S) (E := E) (μ := μ) (γ := γ) (Λ := Λ) hγ hμ
    filter_upwards [hcomp] with ω hω
    simpa [ProbabilityTheory.Kernel.comp_apply] using hω
  have hΛ' :
      ∀ Λ : Finset S,
        ∀ᵐ ω ∂μ.trim (tailSigmaAlgebra_le_pi (S := S) (E := E)),
          (tailKernel (S := S) (E := E) μ ω).bind (γ Λ) = tailKernel (S := S) (E := E) μ ω := by
    intro Λ
    filter_upwards [hΛ Λ] with ω hω
    have hsame :
        (tailKernel (S := S) (E := E) μ ω).bind (γ Λ)
          = (tailKernel (S := S) (E := E) μ ω).bind ((γ Λ).comap id cylinderEvents_le_pi) := by
      ext A hA
      have hmeas : Measurable (γ Λ : (S → E) → Measure (S → E)) :=
        (ProbabilityTheory.Kernel.measurable (γ Λ)).mono cylinderEvents_le_pi le_rfl
      have hAEM : AEMeasurable (γ Λ : (S → E) → Measure (S → E)) (tailKernel (S := S) (E := E) μ ω) :=
        hmeas.aemeasurable
      have hAEM' :
          AEMeasurable ((γ Λ).comap id cylinderEvents_le_pi : (S → E) → Measure (S → E))
            (tailKernel (S := S) (E := E) μ ω) :=
        (ProbabilityTheory.Kernel.measurable ((γ Λ).comap id cylinderEvents_le_pi)).aemeasurable
      rw [Measure.bind_apply hA hAEM, Measure.bind_apply hA hAEM']
      simp [ProbabilityTheory.Kernel.comap_apply]
    simpa [hsame] using hω
  haveI : Countable (Finset S) := by infer_instance
  simpa [MeasureTheory.ae_all_iff] using (MeasureTheory.ae_all_iff.2 hΛ')

/-- **Georgii step:** if `μ` is Gibbs, then its tail conditional measures are Gibbs `μ.trim 𝓣`-a.e. -/
theorem ae_isGibbsMeasure_tailKernel
    [@MeasurableSpace.CountableOrCountablyGenerated (S → E) (S → E) (@tailSigmaAlgebra S E _)]
    (hγ : γ.IsProper) (hμ : γ.IsGibbsMeasure μ) :
    ∀ᵐ ω ∂μ.trim (tailSigmaAlgebra_le_pi (S := S) (E := E)),
      γ.IsGibbsMeasure (tailKernel (S := S) (E := E) μ ω) := by
  filter_upwards [ae_forall_bind_eq_tailKernel (S := S) (E := E) (μ := μ) (γ := γ) hγ hμ] with ω hω
  haveI : IsProbabilityMeasure (tailKernel (S := S) (E := E) μ ω) :=
    ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure
      (κ := tailKernel (S := S) (E := E) μ) ω
  exact (Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob (γ := γ) hγ).2 hω

/-!
### Extremal (ergodic) components (Georgii Thm 7.7 + tail disintegration)

Using:
- `ae_isGibbsMeasure_tailKernel` (DLR fixed point transported to components),
- `ae_isTailTrivial_tailKernel` (tail determinism ⇒ tail triviality of components),
- `ExtremePoints.mem_extremePoints_G_of_isTailTrivial` (Georgii Thm 7.7, direction `tail-trivial → extreme`),
we conclude that the tail conditional measures are **extreme points** of `G(γ)` almost surely.
-/

open scoped Convex

theorem ae_mem_extremePoints_G_tailKernel
    [@MeasurableSpace.CountableOrCountablyGenerated (S → E) (S → E) (@tailSigmaAlgebra S E _)]
    (hγ : γ.IsProper) (hμ : γ.IsGibbsMeasure μ) :
    ∀ᵐ ω ∂μ.trim (tailSigmaAlgebra_le_pi (S := S) (E := E)),
      (tailKernel (S := S) (E := E) μ ω) ∈ (G (γ := γ)).extremePoints ENNReal := by
  classical
  have hGibbs :=
    ae_isGibbsMeasure_tailKernel (S := S) (E := E) (μ := μ) (γ := γ) hγ hμ
  have hTail :=
    ae_isTailTrivial_tailKernel (S := S) (E := E) (μ := μ)
  filter_upwards [hGibbs, hTail] with ω hωGibbs hωTail
  have hμG : (tailKernel (S := S) (E := E) μ ω) ∈ G (γ := γ) := by
    refine ⟨?_, hωGibbs⟩
    infer_instance
  have htail' :
      IsTailTrivial (S := S) (E := E)
        (⟨tailKernel (S := S) (E := E) μ ω, by
          infer_instance⟩ : ProbabilityMeasure (S → E)) := hωTail
  exact
    mem_extremePoints_G_of_isTailTrivial (S := S) (E := E) (γ := γ)
      (hγ := hγ) (μ := tailKernel (S := S) (E := E) μ ω) hμG htail'

omit [Countable S] [StandardBorelSpace E] in
/-- A Gibbs measure is a fixed point for `((γ Λ).comap id cylinderEvents_le_pi) ∘ₘ ·`. -/
lemma compMeasure_comap_eq_of_isGibbsMeasure (hγ : γ.IsProper) (hμ : γ.IsGibbsMeasure μ) :
    ((γ Λ).comap id cylinderEvents_le_pi) ∘ₘ μ = μ := by
  have hfix :
      μ.bind (γ Λ) = μ := by
    simpa using ((Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob (γ := γ) hγ).1 hμ) Λ
  have hsame : μ.bind ((γ Λ).comap id cylinderEvents_le_pi) = μ.bind (γ Λ) := by
    ext A hA
    have hAEM : AEMeasurable (γ Λ : (S → E) → Measure (S → E)) μ :=
      ((ProbabilityTheory.Kernel.measurable (γ Λ)).mono
          (MeasureTheory.cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := ((Λ : Set S)ᶜ))) le_rfl).aemeasurable
    simp [Measure.bind_apply hA hAEM]
  change μ.bind ((γ Λ).comap id cylinderEvents_le_pi) = μ
  exact (hsame.trans hfix)

/-- Push the DLR fixed-point property through the tail disintegration identity. -/
lemma comp_assoc_tailKernel_of_isGibbsMeasure (hγ : γ.IsProper) (hμ : γ.IsGibbsMeasure μ) :
    ((γ Λ).comap id cylinderEvents_le_pi ∘ₖ tailKernel (S := S) (E := E) μ)
        ∘ₘ (μ.trim (tailSigmaAlgebra_le_pi (S := S) (E := E)))
      =
      (tailKernel (S := S) (E := E) μ)
        ∘ₘ (μ.trim (tailSigmaAlgebra_le_pi (S := S) (E := E))) := by
  have hdis :
      (tailKernel (S := S) (E := E) μ)
          ∘ₘ (μ.trim (tailSigmaAlgebra_le_pi (S := S) (E := E))) = μ :=
    tailKernel_comp_trim (S := S) (E := E) (μ := μ)
  have hfix :
      ((γ Λ).comap id cylinderEvents_le_pi)
        ∘ₘ ((tailKernel (S := S) (E := E) μ)
              ∘ₘ (μ.trim (tailSigmaAlgebra_le_pi (S := S) (E := E))))
        =
      (tailKernel (S := S) (E := E) μ)
        ∘ₘ (μ.trim (tailSigmaAlgebra_le_pi (S := S) (E := E))) := by
    have hfix0 :
        ((γ Λ).comap id cylinderEvents_le_pi) ∘ₘ μ = μ :=
      compMeasure_comap_eq_of_isGibbsMeasure (S := S) (E := E) (μ := μ) (γ := γ) (Λ := Λ) hγ hμ
    simpa [hdis] using hfix0
  have hassoc :
      ((γ Λ).comap id cylinderEvents_le_pi)
        ∘ₘ ((tailKernel (S := S) (E := E) μ)
              ∘ₘ (μ.trim (tailSigmaAlgebra_le_pi (S := S) (E := E))))
        =
      ((γ Λ).comap id cylinderEvents_le_pi ∘ₖ tailKernel (S := S) (E := E) μ)
        ∘ₘ (μ.trim (tailSigmaAlgebra_le_pi (S := S) (E := E))) := by
    simpa using
      (MeasureTheory.Measure.comp_assoc (μ := (μ.trim (tailSigmaAlgebra_le_pi (S := S) (E := E))))
        (κ := tailKernel (S := S) (E := E) μ)
        (η := (γ Λ).comap id cylinderEvents_le_pi))
  simpa using hassoc.symm.trans hfix

end GibbsComp

end TailKernel

end GibbsMeasure

end MeasureTheory
