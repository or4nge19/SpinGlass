import GibbsMeasure.Mathlib.MeasureTheory.Measure.GiryMonad
import GibbsMeasure.KolmogorovExtension4.ProductMeasure
import GibbsMeasure.Prereqs.CylinderEvents
import GibbsMeasure.Prereqs.Filtration.Consistent
import GibbsMeasure.Prereqs.Juxt
import GibbsMeasure.Prereqs.MeasureExt
import GibbsMeasure.Prereqs.Kernel.CondExp
import GibbsMeasure.Prereqs.Kernel.Proper
import GibbsMeasure.Prereqs.SquareCylinders


/-!
# Gibbs measures

This file defines Gibbs measures.
-/

open ProbabilityTheory Set MeasureTheory ENNReal NNReal

variable {S E : Type*} {mE : MeasurableSpace E} {Λ₁ Λ₂ : Finset S}

/-- A family of kernels `γ` is consistent if `γ Λ₁ ∘ₖ γ Λ₂ = γ Λ₂` for all `Λ₁ ⊆ Λ₂`.

Morally, the LHS should be thought of as discovering `Λ₁` then `Λ₂`, while the RHS should be
thought of as discovering `Λ₂` straight away. -/
def IsConsistent (γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E)) : Prop :=
  ∀ ⦃Λ₁ Λ₂⦄, Λ₁ ⊆ Λ₂ → (γ Λ₁).comap id cylinderEvents_le_pi ∘ₖ γ Λ₂ = γ Λ₂

/-- A family of kernels `γ` is consistent (DLR consistency) if `γ Λ₂ ∘ₖ γ Λ₁ = γ Λ₂` for all `Λ₁ ⊆ Λ₂`.
This reflects the tower property of conditional expectations: conditioning on `Λ₂ᶜ` (less info)
makes subsequent conditioning on `Λ₁ᶜ` (more info, since Λ₁ᶜ ⊇ Λ₂ᶜ) redundant when integrated
against a measure already conditioned on `Λ₂ᶜ`.
-/
-- Corrected definition (DLR consistency).
--def IsConsistent' (γ : ∀ Λ : Finset S, Kernel[cylinderEvents (Λᶜ : Set S)] (S → E) (S → E)) : Prop :=
--  ∀ ⦃Λ₁ Λ₂⦄, Λ₁ ⊆ Λ₂ → γ Λ₂ ∘ₖ γ Λ₁ = γ Λ₂

lemma isConsistentKernel_cylinderEventsCompl
    {γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E)} :
    Filtration.cylinderEventsCompl.IsConsistentKernel (fun Λ ↦ γ (OrderDual.ofDual Λ)) ↔
      IsConsistent γ := forall_swap

variable (S E) in
/-- A specification from `S` to `E` is a collection of "boundary condition kernels" on the
complement of finite sets, compatible under restriction.

The term "boundary condition kernels" is chosen because for a Gibbs measure associated to
a specification, the kernels of the specification are precisely the regular conditional
probabilities of the Gibbs measure conditionally on the configurations in the complements of
finite sets (which serve as "boundary conditions"). -/
structure Specification [MeasurableSpace E] where
  /-- The boundary condition kernels of a specification.

  DO NOT USE. Instead use the coercion to function `⇑γ`. Lean should insert it automatically in most
  cases. -/
  toFun (Λ : Finset S) : Kernel[cylinderEvents Λᶜ] (S → E) (S → E)
  /-- The boundary condition kernels of a specification are consistent.

  DO NOT USE. Instead use `Specification.isConsistent`. -/
  isConsistent' : IsConsistent toFun

namespace Specification

instance instDFunLike :
    DFunLike (Specification S E) (Finset S) fun Λ ↦ Kernel[cylinderEvents Λᶜ] (S → E) (S → E)
    where
  coe := toFun
  coe_injective' γ₁ γ₂ h := by cases γ₁; cases γ₂; congr

/-- The boundary condition kernels of a specification are consistent. -/
lemma isConsistent (γ : Specification S E) : IsConsistent γ := γ.isConsistent'

initialize_simps_projections Specification (toFun → apply)

variable {γ γ₁ γ₂ : Specification S E} {Λ Λ₁ Λ₂ : Finset S}

@[ext] lemma ext : (∀ Λ, γ₁ Λ = γ₂ Λ) → γ₁ = γ₂ := DFunLike.ext _ _

protected lemma bind (hΛ : Λ₁ ⊆ Λ₂) (η : S → E) : (γ Λ₂ η).bind (γ Λ₁) = γ Λ₂ η :=
  DFunLike.congr_fun (γ.isConsistent hΛ) η

section IsIndep

/-- An independent specification is a specification `γ` where `γ Λ₁ ∘ₖ γ Λ₂ = γ (Λ₁ ∪ Λ₂)` for all
`Λ₁ Λ₂`. -/
def IsIndep (γ : Specification S E) : Prop :=
  ∀ ⦃Λ₁ Λ₂⦄ [DecidableEq S], (γ Λ₁).comap id cylinderEvents_le_pi ∘ₖ γ Λ₂ = (γ (Λ₁ ∪ Λ₂)).comap id
      (measurable_id'' <| by
        gcongr
        exact Finset.subset_union_right)

end IsIndep

section IsMarkov

/-- A Markov specification is a specification whose boundary condition kernels are all Markov
kernels. -/
class IsMarkov (γ : Specification S E) : Prop where
  isMarkovKernel : ∀ Λ, IsMarkovKernel (γ Λ)

instance IsMarkov.toIsMarkovKernel [γ.IsMarkov] {Λ : Finset S} : IsMarkovKernel (γ Λ) :=
  isMarkovKernel _

end IsMarkov

section IsProper

/-- A specification is proper if all its boundary condition kernels are. -/
def IsProper (γ : Specification S E) : Prop := ∀ Λ : Finset S, (γ Λ).IsProper

lemma isProper_iff_restrict_eq_indicator_smul :
    γ.IsProper ↔
      ∀ (Λ : Finset S) ⦃B : Set (S → E)⦄ (hB : MeasurableSet[cylinderEvents Λᶜ] B) (x : S → E),
      (γ Λ).restrict (cylinderEvents_le_pi _ hB) x = B.indicator (1 : (S → E) → ℝ≥0∞) x • γ Λ x :=
  forall_congr' fun _ ↦ Kernel.isProper_iff_restrict_eq_indicator_smul _

lemma isProper_iff_inter_eq_indicator_mul :
    γ.IsProper ↔
      ∀ (Λ : Finset S) ⦃A : Set (S → E)⦄ (_hA : MeasurableSet A) ⦃B : Set (S → E)⦄
        (_hB : MeasurableSet[cylinderEvents Λᶜ] B) (η : S → E),
      γ Λ η (A ∩ B) = B.indicator 1 η * γ Λ η A :=
  forall_congr' fun _ ↦ Kernel.isProper_iff_inter_eq_indicator_mul cylinderEvents_le_pi

alias ⟨IsProper.restrict_eq_indicator_smul, IsProper.of_restrict_eq_indicator_smul⟩ :=
  isProper_iff_restrict_eq_indicator_smul

alias ⟨IsProper.inter_eq_indicator_mul, IsProper.of_inter_eq_indicator_mul⟩ :=
  isProper_iff_inter_eq_indicator_mul

variable {A B : Set (S → E)} {f g : (S → E) → ℝ≥0∞} {η₀ : S → E}

lemma IsProper.setLIntegral_eq_indicator_mul_lintegral (hγ : γ.IsProper) (Λ : Finset S)
    (hf : Measurable f) (hB : MeasurableSet[cylinderEvents Λᶜ] B) :
    ∫⁻ x in B, f x ∂(γ Λ η₀) = B.indicator 1 η₀ * ∫⁻ x, f x ∂(γ Λ η₀) :=
  (hγ Λ).setLIntegral_eq_indicator_mul_lintegral cylinderEvents_le_pi hf hB _

lemma IsProper.setLIntegral_inter_eq_indicator_mul_setLIntegral (Λ : Finset S) (hγ : γ.IsProper)
    (hf : Measurable f) (hA : MeasurableSet A) (hB : MeasurableSet[cylinderEvents Λᶜ] B) :
    ∫⁻ x in A ∩ B, f x ∂(γ Λ η₀) = B.indicator 1 η₀ * ∫⁻ x in A, f x ∂(γ Λ η₀) :=
  (hγ Λ).setLIntegral_inter_eq_indicator_mul_setLIntegral cylinderEvents_le_pi hf hA hB _

lemma IsProper.lintegral_mul (hγ : γ.IsProper) (Λ : Finset S) (hf : Measurable f)
    (hg : Measurable[cylinderEvents Λᶜ] g) :
    ∫⁻ x, g x * f x ∂(γ Λ η₀) = g η₀ * ∫⁻ x, f x ∂(γ Λ η₀) :=
  (hγ _).lintegral_mul cylinderEvents_le_pi hf hg _

end IsProper

section IsGibbsMeasure
variable {μ : Measure (S → E)}

/-- For a specification `γ`, a Gibbs measure is a measure whose conditional expectation kernels
conditionally on configurations exterior to finite sets agree with the boundary condition kernels
of the specification `γ`. -/
def IsGibbsMeasure (γ : Specification S E) (μ : Measure (S → E)) : Prop := ∀ Λ, (γ Λ).IsCondExp μ

-- The following two lemmas should generalise to a family of kernels indexed by a filtration
lemma isGibbsMeasure_iff_forall_bind_eq (hγ : γ.IsProper) [IsFiniteMeasure μ] [IsMarkov γ] :
    γ.IsGibbsMeasure μ ↔ ∀ Λ, μ.bind (γ Λ) = μ :=
  forall_congr' fun _Λ ↦ Kernel.isCondExp_iff_bind_eq_left (hγ _) cylinderEvents_le_pi

/-!
### Probability-measure specializations

In the Vol. II / infinite-volume development, Gibbs measures are probability measures.
These wrappers avoid threading `[IsFiniteMeasure μ]` explicitly.
-/

lemma isGibbsMeasure_iff_forall_bind_eq_of_prob (hγ : γ.IsProper) [IsProbabilityMeasure μ] [IsMarkov γ] :
    γ.IsGibbsMeasure μ ↔ ∀ Λ, μ.bind (γ Λ) = μ := by
  haveI : IsFiniteMeasure μ := by infer_instance
  simpa using (isGibbsMeasure_iff_forall_bind_eq (γ := γ) (μ := μ) hγ)

lemma isGibbsMeasure_iff_frequently_bind_eq (hγ : γ.IsProper) [IsFiniteMeasure μ] [IsMarkov γ] :
    γ.IsGibbsMeasure μ ↔ ∃ᶠ Λ in .atTop, μ.bind (γ Λ) = μ := by
  rw [isGibbsMeasure_iff_forall_bind_eq hγ]
  refine ⟨Filter.Frequently.of_forall, fun h Λ ↦ ?_⟩
  obtain ⟨Λ', h, hΛ'⟩ := h.forall_exists_of_atTop Λ
  rw [← hΛ', Measure.bind_bind, funext (γ.bind h)] <;>
    exact ((γ _).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable

lemma isGibbsMeasure_iff_frequently_bind_eq_of_prob (hγ : γ.IsProper) [IsProbabilityMeasure μ] [IsMarkov γ] :
    γ.IsGibbsMeasure μ ↔ ∃ᶠ Λ in .atTop, μ.bind (γ Λ) = μ := by
  haveI : IsFiniteMeasure μ := by infer_instance
  simpa using (isGibbsMeasure_iff_frequently_bind_eq (γ := γ) (μ := μ) hγ)

end IsGibbsMeasure

noncomputable section ISSSD
variable (ν : Measure E) [IsProbabilityMeasure ν] (η : S → E)

lemma measurable_isssdFun (Λ : Finset S) :
    Measurable[cylinderEvents Λᶜ]
      fun η : S → E ↦ (Measure.pi fun _ : Λ ↦ ν).map (juxt Λ η) := by
  classical -- needed for decidability
  -- We use a π-system generating the product σ-algebra on `S → E` (measurable rectangles).
  let C : Set (Set (S → E)) := squareCylindersMeas S E
  have hC_pi : IsPiSystem C := by
    simpa [C] using (isPiSystem_squareCylindersMeas S E)
  have hgen : (inferInstance : MeasurableSpace (S → E)) = .generateFrom C := by
    simpa [C] using (generateFrom_squareCylindersMeas S E)
  let μ' : (S → E) → Measure (S → E) := fun η ↦ (Measure.pi fun _ : Λ ↦ ν).map (juxt Λ η)
  haveI : ∀ η, IsProbabilityMeasure (μ' η) := by
    intro η
    haveI : IsProbabilityMeasure (Measure.pi (fun _ : Λ ↦ ν)) := by infer_instance
    exact Measure.isProbabilityMeasure_map
      (μ := Measure.pi (fun _ : Λ ↦ ν))
      (f := juxt (Λ := (Λ : Set S)) (η := η))
      (hf := (Measurable.juxt (Λ := (Λ : Set S)) (η := η) (𝓔 := mE)).aemeasurable)
  refine (Measurable.measure_of_isPiSystem_of_isProbabilityMeasure (μ := μ') (S := C)
    (hgen := hgen) (hpi := hC_pi) ?_)
  intro A hA
  rcases hA with ⟨s, t, ht, rfl⟩
  have ht_meas : ∀ i : S, MeasurableSet (t i) := by
    simpa [Set.mem_pi, Set.mem_univ, true_implies] using ht
  have h_rect_meas :
      Measurable[cylinderEvents (Λ : Set S)ᶜ] fun η : S → E =>
        (μ' η) ((s : Set S).pi t) := by
    let P : (S → E) → Prop := fun η => ∀ i ∈ (s : Set S), i ∉ (Λ : Set S) → η i ∈ t i
    have hP : MeasurableSet[cylinderEvents (Λ : Set S)ᶜ] {η | P η} := by
      have :
          {η | P η} =
            ⋂ i ∈ (s : Finset S),
              (if hi : i ∈ (Λ : Set S) then Set.univ else (fun η : S → E => η i) ⁻¹' (t i)) := by
        ext η
        simp [P, Set.mem_iInter, Set.mem_preimage]
      rw [this]
      refine Finset.measurableSet_biInter s (fun i hi => ?_)
      by_cases hΛi : i ∈ (Λ : Set S)
      · simp [hΛi]
      · have hi' : i ∈ (Λ : Set S)ᶜ := by simpa [Set.mem_compl_iff] using hΛi
        have hproj : Measurable[cylinderEvents (Λ : Set S)ᶜ] (fun η : S → E => η i) :=
          measurable_cylinderEvent_apply (i := i) (X := fun _ : S ↦ E) hi'
        simpa [hΛi] using (ht_meas i).preimage hproj
    let tΛ : Λ → Set E := fun j =>
      if hjs : (j : S) ∈ s then t j else Set.univ
    have htΛ_meas : ∀ j : Λ, MeasurableSet (tΛ j) := by
      intro j
      by_cases hjs : (j : S) ∈ s
      · simpa [tΛ, hjs] using ht_meas j
      · simp [tΛ, hjs]
    let c : ℝ≥0∞ := (Measure.pi fun _ : Λ ↦ ν) (Set.univ.pi tΛ)
    have h_eval :
        (fun η : S → E => (μ' η) ((s : Set S).pi t))
          = fun η => ite (P η) c 0 := by
      funext η
      have hmeas_rect : MeasurableSet ((s : Set S).pi t) :=
        MeasurableSet.pi s.countable_toSet (fun i _ => ht_meas i)
      have : (μ' η) ((s : Set S).pi t)
          = (Measure.pi fun _ : Λ ↦ ν) ((juxt (Λ : Set S) η) ⁻¹' ((s : Set S).pi t)) := by
        simp [μ', Measure.map_apply (Measurable.juxt (Λ := (Λ : Set S)) (η := η) (𝓔 := mE)) hmeas_rect]
      rw [this]
      by_cases hPη : P η
      · have hpre :
            (juxt (Λ : Set S) η) ⁻¹' ((s : Set S).pi t) = Set.univ.pi tΛ := by
          ext ζ
          constructor
          · intro hζ
            have hζ' : juxt (Λ : Set S) η ζ ∈ (s : Set S).pi t := hζ
            have hcond :
                ∀ i, i ∈ (s : Set S) → juxt (Λ : Set S) η ζ i ∈ t i := by
              simpa [Set.mem_pi] using hζ'
            refine Set.mem_univ_pi.2 ?_
            intro j
            by_cases hj_s : (j : S) ∈ s
            · have hj_s' : (j : S) ∈ (s : Set S) := by
                exact (Finset.mem_coe.2 hj_s)
              have hjΛ : (j : S) ∈ (Λ : Set S) := by
                exact (Finset.mem_coe.2 j.2)
              have : juxt (Λ : Set S) η ζ (j : S) = ζ j := by
                simp [juxt, hjΛ]
              have : ζ j ∈ t (j : S) := by
                simpa [this] using hcond (j : S) hj_s'
              simpa [tΛ, hj_s] using this
            · simp [tΛ, hj_s]
          · intro hζ
            have hζ' : ∀ j : Λ, ζ j ∈ tΛ j := by
              simpa [Set.mem_univ_pi] using hζ
            refine Set.mem_pi.2 ?_
            intro i hi_s'
            have hi_s : i ∈ s := by
              simpa using hi_s'
            by_cases hiΛ : i ∈ Λ
            · let j : Λ := ⟨i, hiΛ⟩
              have : ζ j ∈ t i := by
                -- `tΛ j = t i`  `i ∈ s`.
                have hj_s : (j : S) ∈ s := by simpa [j] using hi_s
                have hζj : ζ j ∈ tΛ j := hζ' j
                have hζj' : (j : S) ∈ s → ζ j ∈ t (j : S) := by
                  simpa [tΛ] using hζj
                have : ζ j ∈ t (j : S) := hζj' hj_s
                simpa [j] using this
              have hiΛ' : i ∈ (Λ : Set S) := Finset.mem_coe.2 hiΛ
              simpa [juxt, hiΛ', j] using this
            · have hiΛ' : i ∉ (Λ : Set S) := by
                simpa [Finset.mem_coe] using hiΛ
              have : η i ∈ t i := hPη i hi_s' hiΛ'
              simp [juxt, hiΛ', this]
        simp [hPη, hpre, c]
      · have hpre_empty :
            (juxt (Λ : Set S) η) ⁻¹' ((s : Set S).pi t) = ∅ := by
          ext ζ
          constructor
          · intro hζ
            have : ¬ (∀ i ∈ (s : Set S), i ∉ (Λ : Set S) → η i ∈ t i) := hPη
            simp only [SetLike.mem_coe, not_forall] at this
            rcases this with ⟨i, hi_s, hi_Λ, hi_not⟩
            have hi_s' : i ∈ (s : Set S) := hi_s
            have hi_Λ' : i ∉ (Λ : Set S) := hi_Λ
            have hcond :
                ∀ j, j ∈ (s : Set S) → juxt (Λ : Set S) η ζ j ∈ t j := by
              simpa [Set.mem_preimage, Set.mem_pi] using hζ
            have : juxt (Λ : Set S) η ζ i ∈ t i := hcond i hi_s'
            have : η i ∈ t i := by
              simpa [juxt_apply_of_not_mem (Λ := (Λ : Set S)) (η := η) (ζ := ζ) hi_Λ'] using this
            exact (hi_not this).elim
          · intro hζ
            simp at hζ
        simp [hPη, hpre_empty, c]
    letI : MeasurableSpace (S → E) := cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)ᶜ
    have hp : MeasurableSet {η : S → E | P η} := by simpa using hP
    haveI : DecidablePred P := fun η => Classical.propDecidable (P η)
    have h_ite : Measurable (fun η : S → E => ite (P η) c (0 : ℝ≥0∞)) :=
      Measurable.ite (p := P) (hp := hp) measurable_const measurable_const
    simpa [h_eval, P] using h_ite
  simpa [μ'] using h_rect_meas

/-- Auxiliary definition for `Specification.isssd`. -/
@[simps -fullyApplied]
def isssdFun (ν : Measure E) [IsProbabilityMeasure ν] (Λ : Finset S) :
    Kernel[cylinderEvents Λᶜ] (S → E) (S → E) :=
  @Kernel.mk _ _ (_) _
    (fun η ↦ Measure.map (juxt Λ η) (Measure.pi fun _ : Λ ↦ ν))
    (measurable_isssdFun ν Λ)

/-!
### Evaluating `isssdFun` on square cylinders

For a measurable rectangle `(s : Set S).pi t`, the ISSSD kernel either gives `0` (if the boundary
condition violates an outside-`Λ` constraint) or a finite product of the single-site masses `ν (t i)`
over the coordinates in `s ∩ Λ`.
-/

lemma isssdFun_apply_squareCylinder
    [DecidableEq S] (Λ s : Finset S) (t : S → Set E) (ht : ∀ i, MeasurableSet (t i)) (η : S → E) :
    isssdFun ν Λ η ((s : Set S).pi t) =
      (by
        classical -- needed
        exact ite (∀ i ∈ s, i ∉ Λ → η i ∈ t i)
          (∏ i ∈ s ∩ Λ, ν (t i)) 0) := by
  classical -- needed
  have hmeas_rect : MeasurableSet ((s : Set S).pi t) :=
    MeasurableSet.pi s.countable_toSet (fun i _ => ht i)
  simp only [isssdFun_apply, Measure.map_apply (Measurable.juxt (Λ := (Λ : Set S)) (η := η) (𝓔 := mE))
    hmeas_rect]
  let P : Prop := ∀ i ∈ (s : Set S), i ∉ (Λ : Set S) → η i ∈ t i
  have hP_iff : P ↔ ∀ i ∈ s, i ∉ Λ → η i ∈ t i := by
    simp [P]
  have hprod :
      (Measure.pi fun _ : Λ ↦ ν)
          (Set.univ.pi fun j : Λ => if (j : S) ∈ (s : Set S) then t j else Set.univ)
        = ∏ i ∈ s ∩ Λ, ν (t i) := by
    haveI : SigmaFinite ν := by infer_instance
    have hpi :
        (Measure.pi fun _ : Λ ↦ ν)
            (Set.univ.pi fun j : Λ => if (j : S) ∈ (s : Set S) then t j else Set.univ)
          = ∏ j : Λ, ν (if (j : S) ∈ (s : Set S) then t j else Set.univ) := by
      simp
    have hnu : ν (Set.univ : Set E) = 1 := by
      simp
    have hpi' :
        (∏ j : Λ, ν (if (j : S) ∈ (s : Set S) then t j else Set.univ))
          = ∏ j ∈ Λ.attach, ν (if (j : S) ∈ (s : Set S) then t j else Set.univ) := by
      simp [Finset.univ_eq_attach]
    have hpi'' :
        (∏ j ∈ Λ.attach, ν (if (j : S) ∈ (s : Set S) then t j else Set.univ))
          = ∏ i ∈ Λ, ν (if i ∈ s then t i else Set.univ) := by
      simpa [Finset.prod_attach, Finset.mem_coe] using
        (Finset.prod_attach (s := Λ) (f := fun i : S => ν (if i ∈ s then t i else Set.univ)))
    have hpi''' :
        (∏ i ∈ Λ, ν (if i ∈ s then t i else Set.univ))
          = ∏ i ∈ s ∩ Λ, ν (t i) := by
      have h' :
          (∏ i ∈ Λ, ν (if i ∈ s then t i else Set.univ))
            = ∏ i ∈ Λ, (if i ∈ s then ν (t i) else 1) := by
        refine Finset.prod_congr rfl ?_
        intro i hi
        by_cases his : i ∈ s
        · simp [his]
        · simp [his, hnu]
      simp [h', Finset.prod_ite_mem, Finset.inter_comm]
    calc
      (Measure.pi fun _ : Λ ↦ ν)
          (Set.univ.pi fun j : Λ => if (j : S) ∈ (s : Set S) then t j else Set.univ)
          = ∏ j : Λ, ν (if (j : S) ∈ (s : Set S) then t j else Set.univ) := hpi
      _ = ∏ j ∈ Λ.attach, ν (if (j : S) ∈ (s : Set S) then t j else Set.univ) := hpi'
      _ = ∏ i ∈ Λ, ν (if i ∈ s then t i else Set.univ) := hpi''
      _ = ∏ i ∈ s ∩ Λ, ν (t i) := hpi'''
  by_cases hP : P
  · have hpre :
        (juxt (Λ : Set S) η) ⁻¹' ((s : Set S).pi t)
          = Set.univ.pi (fun j : Λ => if (j : S) ∈ (s : Set S) then t j else Set.univ) := by
      ext ζ
      constructor
      · intro hζ
        have hζ' : ∀ i, i ∈ (s : Set S) → juxt (Λ : Set S) η ζ i ∈ t i := by
          simpa [Set.mem_preimage, Set.mem_pi] using hζ
        refine Set.mem_pi.2 (fun j _ => ?_)
        by_cases hjs : (j : S) ∈ (s : Set S)
        · have : juxt (Λ : Set S) η ζ (j : S) ∈ t (j : S) := hζ' (j : S) hjs
          simpa [hjs, juxt_apply_of_mem (Λ := (Λ : Set S)) (η := η) (ζ := ζ) j.property] using this
        · simp [hjs]
      · intro hζ
        have hζ' : ∀ j : Λ, ζ j ∈ (if (j : S) ∈ (s : Set S) then t j else Set.univ) := by
          simpa [Set.mem_univ_pi] using hζ
        refine Set.mem_pi.2 (fun i hi => ?_)
        by_cases hiΛ : i ∈ (Λ : Set S)
        · let j : Λ := ⟨i, hiΛ⟩
          have hjs : (j : S) ∈ (s : Set S) := by simpa using hi
          have : ζ j ∈ t i := by
            have : ζ j ∈ (if (j : S) ∈ (s : Set S) then t j else Set.univ) := hζ' j
            simpa [hjs] using this
          simpa [juxt_apply_of_mem (Λ := (Λ : Set S)) (η := η) (ζ := ζ) hiΛ] using this
        · have : η i ∈ t i := hP i hi (by simpa [Set.mem_compl_iff] using hiΛ)
          simpa [juxt_apply_of_not_mem (Λ := (Λ : Set S)) (η := η) (ζ := ζ) hiΛ] using this
    have hP' : (∀ i ∈ s, i ∉ Λ → η i ∈ t i) := (hP_iff.mp hP)
    have hL :
        (Measure.pi fun _ : Λ ↦ ν) ((juxt (Λ : Set S) η) ⁻¹' ((s : Set S).pi t))
          = ∏ i ∈ s ∩ Λ, ν (t i) := by
      simpa [hpre] using hprod
    calc
      (Measure.pi fun _ : Λ ↦ ν) ((juxt (Λ : Set S) η) ⁻¹' ((s : Set S).pi t))
          = ∏ i ∈ s ∩ Λ, ν (t i) := hL
      _ = ite (∀ i ∈ s, i ∉ Λ → η i ∈ t i) (∏ i ∈ s ∩ Λ, ν (t i)) 0 := by
            rw [if_pos hP']
  · have hpre :
        (juxt (Λ : Set S) η) ⁻¹' ((s : Set S).pi t) = (∅ : Set (Λ → E)) := by
      ext ζ
      constructor
      · intro hζ
        have : ¬ (∀ i ∈ (s : Set S), i ∉ (Λ : Set S) → η i ∈ t i) := hP
        simp only [not_forall] at this
        rcases this with ⟨i, hi_s, hi_Λ, hi_not⟩
        have hcond : ∀ j, j ∈ (s : Set S) → juxt (Λ : Set S) η ζ j ∈ t j := by
          simpa [Set.mem_preimage, Set.mem_pi] using hζ
        have : juxt (Λ : Set S) η ζ i ∈ t i := hcond i hi_s
        have : η i ∈ t i := by
          simpa [juxt_apply_of_not_mem (Λ := (Λ : Set S)) (η := η) (ζ := ζ) hi_Λ] using this
        exact (hi_not this).elim
      · intro hζ
        simp at hζ
    have hP' : ¬ (∀ i ∈ s, i ∉ Λ → η i ∈ t i) := by
      intro h
      exact hP (hP_iff.mpr h)
    simp [hpre, hP']

/-- The ISSSD of a measure is strongly consistent. -/
lemma isssdFun_comp_isssdFun [DecidableEq S] (Λ₁ Λ₂ : Finset S) :
    (isssdFun ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ isssdFun ν Λ₂ =
      (isssdFun ν (Λ₁ ∪ Λ₂)).comap id
        (measurable_id'' <| by
          gcongr
          exact Finset.subset_union_right) := by
  classical
  -- We prove equality of kernels by showing that, for every boundary condition `η`, the resulting
  -- measures agree on the π-system of square cylinders generating the product σ-algebra.
  ext η
  -- Let `C` be the generating π-system of measurable rectangles.
  let C : Set (Set (S → E)) := squareCylindersMeas S E
  have hC_pi : IsPiSystem C := by
    simpa [C] using (isPiSystem_squareCylindersMeas S E)
  have hgen : (inferInstance : MeasurableSpace (S → E)) = .generateFrom C := by
    simpa [C] using (generateFrom_squareCylindersMeas S E)
  have huniv : (Set.univ : Set (S → E)) ∈ C := by
    simpa [C] using (univ_mem_squareCylindersMeas S E)
  have hL_univ :
      (( (isssdFun ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ isssdFun ν Λ₂) η) Set.univ ≠ ∞ := by
    have huniv_meas : MeasurableSet (Set.univ : Set (S → E)) := MeasurableSet.univ
    have h1 : ∀ ω, (isssdFun ν Λ₁ ω) Set.univ = 1 := by
      intro ω
      haveI : IsProbabilityMeasure (isssdFun ν Λ₁ ω) := by
        haveI : IsProbabilityMeasure (Measure.pi (fun _ : Λ₁ ↦ ν)) := by infer_instance
        simpa [isssdFun_apply] using
          (Measure.isProbabilityMeasure_map
            (μ := Measure.pi (fun _ : Λ₁ ↦ ν))
            (f := juxt (Λ := (Λ₁ : Set S)) (η := ω))
            (hf := (Measurable.juxt (Λ := (Λ₁ : Set S)) (η := ω) (𝓔 := mE)).aemeasurable))
      simpa using (IsProbabilityMeasure.measure_univ (μ := isssdFun ν Λ₁ ω))
    have hΛ₂_prob : IsProbabilityMeasure (isssdFun ν Λ₂ η) := by
      haveI : IsProbabilityMeasure (Measure.pi (fun _ : Λ₂ ↦ ν)) := by infer_instance
      simpa [isssdFun_apply] using
        (Measure.isProbabilityMeasure_map
          (μ := Measure.pi (fun _ : Λ₂ ↦ ν))
          (f := juxt (Λ := (Λ₂ : Set S)) (η := η))
          (hf := (Measurable.juxt (Λ := (Λ₂ : Set S)) (η := η) (𝓔 := mE)).aemeasurable))
    have h_comp_univ :
        (( (isssdFun ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ isssdFun ν Λ₂) η) Set.univ = 1 := by
      haveI : IsProbabilityMeasure (isssdFun ν Λ₂ η) := hΛ₂_prob
      haveI :
          IsProbabilityMeasure
            (Measure.map (juxt (Λ := (Λ₂ : Set S)) (η := η)) (Measure.pi fun _ : Λ₂ ↦ ν)) := by
        simpa [isssdFun_apply] using hΛ₂_prob
      have h_integrand :
          (fun b : S → E =>
              (Measure.map (juxt (Λ := (Λ₁ : Set S)) (η := b)) (Measure.pi fun _ : Λ₁ ↦ ν))
                Set.univ)
            = fun _ => (1 : ℝ≥0∞) := by
        funext b
        simpa [isssdFun_apply] using h1 b
      simp [Kernel.comp_apply' _ _ _ huniv_meas, Kernel.comap_apply, h_integrand,
        MeasureTheory.lintegral_const]
    simp [h_comp_univ]
  have hmeas_eq :
      (( (isssdFun ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ isssdFun ν Λ₂) η)
        =
        ((isssdFun ν (Λ₁ ∪ Λ₂)).comap id
            (measurable_id'' <| by gcongr) η) := by
    refine MeasureTheory.Measure.ext_of_generateFrom_of_iUnion_univ (C := C)
      (μ := (( (isssdFun ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ isssdFun ν Λ₂) η))
      (ν := ((isssdFun ν (Λ₁ ∪ Λ₂)).comap id (measurable_id'' <| by gcongr) η))
      (hA := hgen) (hC := hC_pi) (huniv := huniv) (hμ_univ := hL_univ) ?_
    intro A hA
    rcases hA with ⟨s, t, ht, rfl⟩
    have ht_meas : ∀ i : S, MeasurableSet (t i) := by
      simpa [Set.mem_pi, Set.mem_univ, true_implies] using ht
    let P1 : (S → E) → Prop := fun ω =>
      ∀ i ∈ (s : Set S), i ∉ (Λ₁ : Set S) → ω i ∈ t i
    have h_rect_meas : MeasurableSet ((s : Set S).pi t) :=
      MeasurableSet.pi s.countable_toSet (fun i _ => ht_meas i)
    have h_int :
        (fun ω : S → E => isssdFun ν Λ₁ ω ((s : Set S).pi t))
          = fun ω => ite (P1 ω) (∏ i ∈ s ∩ Λ₁, ν (t i)) 0 := by
      funext ω
      simpa [P1] using (isssdFun_apply_squareCylinder (ν := ν) (mE := mE)
        (Λ := Λ₁) (s := s) (t := t) ht_meas ω)
    simp [Kernel.comp_apply' _ _ _ h_rect_meas, Kernel.comap_apply]
    have hP1_set :
        {ω : S → E | P1 ω} =
          ((s : Set S).pi fun i => if i ∈ (Λ₁ : Set S) then Set.univ else t i) := by
      ext ω
      simp [P1, Set.mem_pi]
    have hP1_meas : MeasurableSet {ω : S → E | P1 ω} := by
      rw [hP1_set]
      refine MeasurableSet.pi s.countable_toSet ?_
      intro i hi
      by_cases hiΛ : i ∈ (Λ₁ : Set S)
      · simp [hiΛ]
      · simpa [hiΛ] using ht_meas i
    have h_outer :
        (isssdFun ν Λ₂ η) {ω : S → E | P1 ω}
          = ite (∀ i ∈ (s : Set S), i ∉ (Λ₁ ∪ Λ₂ : Finset S) → η i ∈ t i)
              (∏ i ∈ s ∩ (Λ₂ \ Λ₁), ν (t i)) 0 := by
      have :
          (isssdFun ν Λ₂ η)
              (((s : Set S).pi fun i => if i ∈ (Λ₁ : Set S) then Set.univ else t i))
            =
            ite (∀ i ∈ (s : Set S), i ∉ (Λ₂ : Set S) →
                  η i ∈ (if i ∈ (Λ₁ : Set S) then Set.univ else t i))
              (∏ i ∈ s ∩ Λ₂, ν (if i ∈ (Λ₁ : Set S) then Set.univ else t i)) 0 := by
        simpa using (isssdFun_apply_squareCylinder (ν := ν) (mE := mE)
          (Λ := Λ₂) (s := s) (t := fun i => if i ∈ (Λ₁ : Set S) then Set.univ else t i)
          (ht := fun i => by by_cases hiΛ : i ∈ (Λ₁ : Set S) <;> simp [hiΛ, ht_meas i]) (η := η))
      have hpred :
          (∀ i ∈ s, i ∉ Λ₂ → i ∉ Λ₁ → η i ∈ t i)
            ↔ (∀ i ∈ (s : Set S), i ∉ (Λ₁ ∪ Λ₂ : Finset S) → η i ∈ t i) := by
        constructor
        · intro h i hi hsU
          have hiΛ2 : i ∉ Λ₂ := by
            intro hiΛ2
            exact hsU (Finset.mem_union.2 (Or.inr hiΛ2))
          have hiΛ1 : i ∉ Λ₁ := by
            intro hiΛ1
            exact hsU (Finset.mem_union.2 (Or.inl hiΛ1))
          exact h i hi hiΛ2 hiΛ1
        · intro h i hi hiΛ2 hiΛ1
          have hsU : i ∉ (Λ₁ ∪ Λ₂ : Finset S) := by
            intro hsU
            have : i ∈ Λ₁ ∨ i ∈ Λ₂ := by simpa [Finset.mem_union] using hsU
            exact (hiΛ2 (this.resolve_left hiΛ1))
          exact h i hi hsU
      have hprod' :
          (∏ i ∈ s ∩ Λ₂, ν (if i ∈ Λ₁ then (Set.univ : Set E) else t i))
            = ∏ i ∈ s ∩ (Λ₂ \ Λ₁), ν (t i) := by
        classical
        have hnu : ν (Set.univ : Set E) = 1 := by
          simp
        have hrewrite :
            (∏ i ∈ s ∩ Λ₂, ν (if i ∈ Λ₁ then (Set.univ : Set E) else t i))
              = ∏ i ∈ s ∩ Λ₂, (if i ∈ Λ₁ then (1 : ℝ≥0∞) else ν (t i)) := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          by_cases hiΛ1 : i ∈ Λ₁
          · simp [hiΛ1, hnu]
          · simp [hiΛ1]
        have hdrop :
            (∏ i ∈ s ∩ Λ₂, (if i ∈ Λ₁ then (1 : ℝ≥0∞) else ν (t i)))
              = ∏ i ∈ (s ∩ Λ₂) \ Λ₁, ν (t i) := by
          have hite :
              (∏ i ∈ s ∩ Λ₂, (if i ∈ Λ₁ then (1 : ℝ≥0∞) else ν (t i)))
                =
                ∏ i ∈ s ∩ Λ₂, (if i ∈ (s ∩ Λ₂) \ Λ₁ then ν (t i) else 1) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            by_cases hiΛ1 : i ∈ Λ₁
            · have : i ∉ (s ∩ Λ₂) \ Λ₁ := by
                intro hi'
                exact (Finset.mem_sdiff.1 hi').2 hiΛ1
              simp [hiΛ1, this]
            · have : i ∈ (s ∩ Λ₂) \ Λ₁ := by
                exact Finset.mem_sdiff.2 ⟨hi, hiΛ1⟩
              simp [hiΛ1, this]
          calc
            (∏ i ∈ s ∩ Λ₂, (if i ∈ Λ₁ then (1 : ℝ≥0∞) else ν (t i)))
                = ∏ i ∈ s ∩ Λ₂, (if i ∈ (s ∩ Λ₂) \ Λ₁ then ν (t i) else 1) := hite
            _ = ∏ i ∈ (s ∩ Λ₂) ∩ ((s ∩ Λ₂) \ Λ₁), ν (t i) := by
                  simpa using (Finset.prod_ite_mem (s ∩ Λ₂) ((s ∩ Λ₂) \ Λ₁) (fun i => ν (t i)))
            _ = ∏ i ∈ (s ∩ Λ₂) \ Λ₁, ν (t i) := by
                  have hsub : (s ∩ Λ₂) \ Λ₁ ⊆ s ∩ Λ₂ := by
                    intro i hi; exact (Finset.mem_sdiff.1 hi).1
                  simp [Finset.inter_eq_right.2 hsub]
        have hidx : (s ∩ Λ₂) \ Λ₁ = s ∩ (Λ₂ \ Λ₁) := by
          ext i
          simp [Finset.mem_inter, Finset.mem_sdiff, and_assoc, and_comm]
        calc
          (∏ i ∈ s ∩ Λ₂, ν (if i ∈ Λ₁ then (Set.univ : Set E) else t i))
              = ∏ i ∈ s ∩ Λ₂, (if i ∈ Λ₁ then (1 : ℝ≥0∞) else ν (t i)) := hrewrite
          _ = ∏ i ∈ (s ∩ Λ₂) \ Λ₁, ν (t i) := hdrop
          _ = ∏ i ∈ s ∩ (Λ₂ \ Λ₁), ν (t i) := by simp [hidx]
      simpa [hP1_set, hpred, hprod'] using this
    by_cases hU : (∀ i ∈ (s : Set S), i ∉ (Λ₁ ∪ Λ₂ : Finset S) → η i ∈ t i)
    · have h_outer' :
          (isssdFun ν Λ₂ η) {ω : S → E | P1 ω} = (∏ i ∈ s ∩ (Λ₂ \ Λ₁), ν (t i)) := by
        have hU' : (∀ i ∈ s, i ∉ Λ₁ → i ∉ Λ₂ → η i ∈ t i) := by
          intro i hi hiΛ1 hiΛ2
          have hiU : i ∉ (Λ₁ ∪ Λ₂ : Finset S) := by
            intro hiU
            have : i ∈ Λ₁ ∨ i ∈ Λ₂ := by simpa [Finset.mem_union] using hiU
            exact hiΛ2 (this.resolve_left hiΛ1)
          exact hU i (by simpa using hi) hiU
        simpa [if_pos hU'] using h_outer
      have hprod_union :
          (∏ i ∈ s ∩ Λ₁, ν (t i)) * (∏ i ∈ s ∩ (Λ₂ \ Λ₁), ν (t i))
            = ∏ i ∈ s ∩ (Λ₁ ∪ Λ₂), ν (t i) := by
        classical
        have hdisj : Disjoint (s ∩ Λ₁) (s ∩ (Λ₂ \ Λ₁)) := by
          refine Finset.disjoint_left.2 ?_
          intro i hi1 hi2
          have hiΛ1 : i ∈ Λ₁ := (Finset.mem_inter.1 hi1).2
          have hiΛ1' : i ∉ Λ₁ :=
            (Finset.mem_sdiff.1 (Finset.mem_inter.1 hi2).2).2
          exact hiΛ1' hiΛ1
        have hunion :
            (s ∩ Λ₁) ∪ (s ∩ (Λ₂ \ Λ₁)) = s ∩ (Λ₁ ∪ Λ₂) := by
          ext i
          constructor
          · intro hi
            rcases Finset.mem_union.1 hi with hi | hi
            · rcases Finset.mem_inter.1 hi with ⟨his, hi1⟩
              exact Finset.mem_inter.2 ⟨his, Finset.mem_union.2 (Or.inl hi1)⟩
            · rcases Finset.mem_inter.1 hi with ⟨his, hi2⟩
              rcases Finset.mem_sdiff.1 hi2 with ⟨hiΛ2, _hiΛ1⟩
              exact Finset.mem_inter.2 ⟨his, Finset.mem_union.2 (Or.inr hiΛ2)⟩
          · intro hi
            rcases Finset.mem_inter.1 hi with ⟨his, hiU⟩
            rcases Finset.mem_union.1 hiU with hi1 | hi2
            · exact Finset.mem_union.2 (Or.inl (Finset.mem_inter.2 ⟨his, hi1⟩))
            · by_cases hi1 : i ∈ Λ₁
              · exact Finset.mem_union.2 (Or.inl (Finset.mem_inter.2 ⟨his, hi1⟩))
              · have hiSdiff : i ∈ Λ₂ \ Λ₁ := Finset.mem_sdiff.2 ⟨hi2, hi1⟩
                exact Finset.mem_union.2 (Or.inr (Finset.mem_inter.2 ⟨his, hiSdiff⟩))
        simpa [hunion] using
          (Finset.prod_union (s₁ := s ∩ Λ₁) (s₂ := s ∩ (Λ₂ \ Λ₁))
            (f := fun i : S => ν (t i)) hdisj).symm
      have hR :
          (isssdFun ν (Λ₁ ∪ Λ₂) η) ((s : Set S).pi t)
            = ∏ i ∈ s ∩ (Λ₁ ∪ Λ₂), ν (t i) := by
        have hU' : ∀ i ∈ s, i ∉ Λ₁ → i ∉ Λ₂ → η i ∈ t i := by
          intro i hi hiΛ1 hiΛ2
          have hiU : i ∉ (Λ₁ ∪ Λ₂ : Finset S) := by
            intro hiU
            have : i ∈ Λ₁ ∨ i ∈ Λ₂ := by simpa [Finset.mem_union] using hiU
            exact hiΛ2 (this.resolve_left hiΛ1)
          exact hU i (by simpa using hi) hiU
        simpa [if_pos hU'] using (isssdFun_apply_squareCylinder (ν := ν) (mE := mE)
          (Λ := Λ₁ ∪ Λ₂) (s := s) (t := t) ht_meas η)
      have h_int_eval (b : S → E) :
          (Measure.map (juxt (↑Λ₁) b) (Measure.pi fun _ : Λ₁ ↦ ν)) ((s : Set S).pi t) =
            ite (P1 b) (∏ i ∈ s ∩ Λ₁, ν (t i)) 0 := by
        have hb := congrArg (fun f => f b) h_int
        simpa [isssdFun_apply] using hb
      calc
        ∫⁻ (b : S → E),
            (Measure.map (juxt (↑Λ₁) b) (Measure.pi fun _ : Λ₁ ↦ ν)) ((s : Set S).pi t)
              ∂Measure.map (juxt (↑Λ₂) η) (Measure.pi fun _ : Λ₂ ↦ ν)
            =
            ∫⁻ (b : S → E),
              ite (P1 b) (∏ i ∈ s ∩ Λ₁, ν (t i)) 0 ∂(isssdFun ν Λ₂ η) := by
              simp [isssdFun_apply, h_int_eval]
        _ = (∏ i ∈ s ∩ Λ₁, ν (t i)) * (isssdFun ν Λ₂ η) {b : S → E | P1 b} := by
              classical
              have hite :
                  (fun b : S → E => ite (P1 b) (∏ i ∈ s ∩ Λ₁, ν (t i)) 0)
                    =
                    ({b : S → E | P1 b}).indicator (fun _ => (∏ i ∈ s ∩ Λ₁, ν (t i))) := by
                funext b
                by_cases hb : P1 b <;> simp [hb]
              simp [hite, hP1_meas]
        _ = (∏ i ∈ s ∩ Λ₁, ν (t i)) * (∏ i ∈ s ∩ (Λ₂ \ Λ₁), ν (t i)) := by
              aesop
        _ = ∏ i ∈ s ∩ (Λ₁ ∪ Λ₂), ν (t i) := by
              simpa [mul_assoc] using hprod_union
        _ = (isssdFun ν (Λ₁ ∪ Λ₂) η) ((s : Set S).pi t) := by
              aesop
        _ = (Measure.map (juxt (↑(Λ₁ ∪ Λ₂)) η) (Measure.pi fun _ : ↥(Λ₁ ∪ Λ₂) ↦ ν)) ((s : Set S).pi t) := by
              simp [isssdFun_apply]
    · have h_outer' :
          (isssdFun ν Λ₂ η) {ω : S → E | P1 ω} = 0 := by
        have hU' : ¬ (∀ i ∈ s, i ∉ Λ₁ → i ∉ Λ₂ → η i ∈ t i) := by
          intro h
          apply hU
          intro i hi hiU
          have hiΛ1 : i ∉ Λ₁ := by
            intro hiΛ1
            exact hiU (Finset.mem_union.2 (Or.inl hiΛ1))
          have hiΛ2 : i ∉ Λ₂ := by
            intro hiΛ2
            exact hiU (Finset.mem_union.2 (Or.inr hiΛ2))
          exact h i (by simpa using hi) hiΛ1 hiΛ2
        simpa [hU'] using h_outer
      have hR :
          (isssdFun ν (Λ₁ ∪ Λ₂) η) ((s : Set S).pi t) = 0 := by
        classical
        have hU' : ¬ (∀ i ∈ s, i ∉ Λ₁ → i ∉ Λ₂ → η i ∈ t i) := by
          intro h
          apply hU
          intro i hi hiU
          have hiΛ1 : i ∉ Λ₁ := by
            intro hiΛ1
            exact hiU (Finset.mem_union.2 (Or.inl hiΛ1))
          have hiΛ2 : i ∉ Λ₂ := by
            intro hiΛ2
            exact hiU (Finset.mem_union.2 (Or.inr hiΛ2))
          exact h i (by simpa using hi) hiΛ1 hiΛ2
        simpa [if_neg hU'] using (isssdFun_apply_squareCylinder (ν := ν) (mE := mE)
          (Λ := Λ₁ ∪ Λ₂) (s := s) (t := t) ht_meas η)
      have h_int_eval (b : S → E) :
          (Measure.map (juxt (↑Λ₁) b) (Measure.pi fun _ : Λ₁ ↦ ν)) ((s : Set S).pi t) =
            ite (P1 b) (∏ i ∈ s ∩ Λ₁, ν (t i)) 0 := by
        have hb := congrArg (fun f => f b) h_int
        simpa [isssdFun_apply] using hb
      have hite :
          (fun b : S → E => ite (P1 b) (∏ i ∈ s ∩ Λ₁, ν (t i)) 0)
            =
            ({b : S → E | P1 b}).indicator (fun _ => (∏ i ∈ s ∩ Λ₁, ν (t i))) := by
        funext b
        by_cases hb : P1 b <;> simp [hb]
      calc
        ∫⁻ (b : S → E),
            (Measure.map (juxt (↑Λ₁) b) (Measure.pi fun _ : Λ₁ ↦ ν)) ((s : Set S).pi t)
              ∂Measure.map (juxt (↑Λ₂) η) (Measure.pi fun _ : Λ₂ ↦ ν)
            =
            ∫⁻ (b : S → E),
              ite (P1 b) (∏ i ∈ s ∩ Λ₁, ν (t i)) 0 ∂(isssdFun ν Λ₂ η) := by
              simp [isssdFun_apply, h_int_eval]
        _ = (∏ i ∈ s ∩ Λ₁, ν (t i)) * (isssdFun ν Λ₂ η) {b : S → E | P1 b} := by
              classical
              rw [hite]
              exact MeasureTheory.lintegral_indicator_const hP1_meas _
        _ = (∏ i ∈ s ∩ Λ₁, ν (t i)) * 0 := by rw [h_outer']
        _ = 0 := by simp
        _ = (isssdFun ν (Λ₁ ∪ Λ₂) η) ((s : Set S).pi t) := by
              exact hR.symm
        _ = (Measure.map (juxt (↑(Λ₁ ∪ Λ₂)) η) (Measure.pi fun _ : ↥(Λ₁ ∪ Λ₂) ↦ ν)) ((s : Set S).pi t) := by
              simp [isssdFun_apply]
  simp [hmeas_eq]

/-- The **Independent Specification with Single Spin Distribution**.

This is the specification corresponding to the product measure. -/
@[simps]
def isssd : Specification S E where
  toFun := isssdFun ν
  isConsistent' Λ₁ Λ₂ hΛ := by
    classical
    rw [isssdFun_comp_isssdFun]
    ext a s _
    simp only [Kernel.comap_apply, id_eq, isssdFun_apply, Finset.coe_sort_coe]
    rw [Finset.union_eq_right.2 hΛ]

/-- The ISSSD of a measure is strongly consistent. -/
lemma isssd_comp_isssd [DecidableEq S] (Λ₁ Λ₂ : Finset S) :
    (isssd ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ isssd ν Λ₂ =
      (isssd ν (Λ₁ ∪ Λ₂)).comap id
        (measurable_id'' <| by
          gcongr
          exact Finset.subset_union_right) := isssdFun_comp_isssdFun ..

protected lemma IsProper.isssd : (isssd (S := S) ν).IsProper := by
  classical
  refine IsProper.of_inter_eq_indicator_mul fun Λ A hA B hB x ↦ ?_
  simp only [isssd_apply, isssdFun_apply, Finset.coe_sort_coe]
  set Δ : Set S := (Λ : Set S)ᶜ
  have hmeas_restrict :
      Measurable (Set.restrict (π := fun _ : S ↦ E) Δ) := by
    rw [measurable_pi_iff]
    intro i
    simpa [Set.restrict] using (measurable_pi_apply (i : S))
  have hBcomap :
      MeasurableSet[
          MeasurableSpace.comap (Set.restrict (π := fun _ : S ↦ E) Δ)
            (inferInstance : MeasurableSpace (Δ → E))] B := by
    simpa [Δ, MeasureTheory.cylinderEvents_eq_comap_restrict (S := S) (E := E) (Δ := Δ)] using hB
  rcases hBcomap with ⟨C, hC, rfl⟩
  have hB_pi : MeasurableSet ((Set.restrict (π := fun _ : S ↦ E) Δ) ⁻¹' C) :=
    hC.preimage hmeas_restrict
  have hAB_pi :
      MeasurableSet (A ∩ (Set.restrict (π := fun _ : S ↦ E) Δ) ⁻¹' C) := hA.inter hB_pi
  have hrestrict :
      ∀ ζ : Λ → E,
        Set.restrict (π := fun _ : S ↦ E) Δ (juxt (Λ := (Λ : Set S)) x ζ) =
          Set.restrict (π := fun _ : S ↦ E) Δ x := by
    intro ζ
    ext i
    have hi : (i : S) ∉ (Λ : Set S) := by
      change (i : S) ∈ Δ
      exact i.property
    simp [Set.restrict, juxt_apply_of_not_mem (Λ := (Λ : Set S)) (η := x) (x := (i : S)) hi]
  have hpreB :
      (juxt (Λ := (Λ : Set S)) x) ⁻¹'
          ((Set.restrict (π := fun _ : S ↦ E) Δ) ⁻¹' C)
        =
        if x ∈ (Set.restrict (π := fun _ : S ↦ E) Δ) ⁻¹' C then Set.univ else ∅ := by
    ext ζ
    by_cases hx : x ∈ (Set.restrict (π := fun _ : S ↦ E) Δ) ⁻¹' C
    · have hx' : Set.restrict (π := fun _ : S ↦ E) Δ x ∈ C := by
        simpa [Set.mem_preimage] using hx
      have : Set.restrict (π := fun _ : S ↦ E) Δ (juxt (Λ := (Λ : Set S)) x ζ) ∈ C := by
        simpa [hrestrict ζ] using hx'
      simp [hx, Set.mem_preimage, this]
    · have hx' : Set.restrict (π := fun _ : S ↦ E) Δ x ∉ C := by
        simpa [Set.mem_preimage] using hx
      have : Set.restrict (π := fun _ : S ↦ E) Δ (juxt (Λ := (Λ : Set S)) x ζ) ∉ C := by
        simpa [hrestrict ζ] using hx'
      simp [hx, Set.mem_preimage, this]
  by_cases hx : x ∈ (Set.restrict (π := fun _ : S ↦ E) Δ) ⁻¹' C
  · have hpreB' :
        (juxt (Λ := (Λ : Set S)) x) ⁻¹'
            ((Set.restrict (π := fun _ : S ↦ E) Δ) ⁻¹' C)
          = Set.univ := by
      simp [hpreB, hx]
    -- If `x ∈ B`, then `B` holds a.s. under the kernel, so intersecting with `B` does nothing.
    simp [hx, Set.indicator, hpreB',
      Measure.map_apply (Measurable.juxt (Λ := (Λ : Set S)) (η := x) (𝓔 := mE)) hAB_pi,
      Measure.map_apply (Measurable.juxt (Λ := (Λ : Set S)) (η := x) (𝓔 := mE)) hA,
      preimage_inter, Set.inter_univ]
  · have hpreB' :
        (juxt (Λ := (Λ : Set S)) x) ⁻¹'
            ((Set.restrict (π := fun _ : S ↦ E) Δ) ⁻¹' C)
          = (∅ : Set (Λ → E)) := by
      simp [hpreB, hx]
    simp [hx, Set.indicator, hpreB',
      Measure.map_apply (Measurable.juxt (Λ := (Λ : Set S)) (η := x) (𝓔 := mE)) hAB_pi,
      Measure.map_apply (Measurable.juxt (Λ := (Λ : Set S)) (η := x) (𝓔 := mE)) hA,
      preimage_inter]

instance isssd.instIsMarkov : (isssd (S := S) ν).IsMarkov where
  isMarkovKernel Λ := by
    classical
    refine ⟨?_⟩
    intro η
    haveI : IsProbabilityMeasure (Measure.pi (fun _ : Λ ↦ ν)) := by infer_instance
    have : IsProbabilityMeasure
        (Measure.map (juxt (Λ := (Λ : Set S)) (η := η)) (Measure.pi fun _ : Λ ↦ ν)) :=
      Measure.isProbabilityMeasure_map
        (μ := Measure.pi (fun _ : Λ ↦ ν))
        (f := juxt (Λ := (Λ : Set S)) (η := η))
        (hf := (Measurable.juxt (Λ := (Λ : Set S)) (η := η) (𝓔 := mE)).aemeasurable)
    simpa [isssd_apply, isssdFun_apply, Finset.coe_sort_coe] using this

end ISSSD

section ProductMeasure

/-- The product measure `ν ^ S` is a `isssd μ`-Gibbs measure. -/
lemma isGibbsMeasure_isssd_productMeasure (ν : Measure E) [IsProbabilityMeasure ν] :
    (isssd ν).IsGibbsMeasure (productMeasure fun _ : S ↦  ν) := by
  classical
  intro Λ
  let μ : Measure (S → E) := productMeasure (fun _ : S ↦ ν)
  haveI : IsFiniteMeasure μ := inferInstance
  have hproper : (isssd (S := S) (E := E) ν).IsProper := Specification.IsProper.isssd (S := S) (E := E)
    (mE := mE) (ν := ν)
  have hπ : (isssd (S := S) (E := E) ν Λ).IsProper := hproper Λ
  haveI : IsMarkovKernel (isssd (S := S) (E := E) ν Λ) := by
    infer_instance
  haveI : SigmaFinite (μ.trim (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S)ᶜ))) := by
    infer_instance
  have h_bind : μ.bind (isssd (S := S) (E := E) ν Λ) = μ := by
    let C : Set (Set (S → E)) := squareCylindersMeas S E
    have hC_pi : IsPiSystem C := by
      simpa [C] using (isPiSystem_squareCylindersMeas S E)
    have hgen : (inferInstance : MeasurableSpace (S → E)) = .generateFrom C := by
      simpa [C] using (generateFrom_squareCylindersMeas S E)
    have huniv : (Set.univ : Set (S → E)) ∈ C := by
      simpa [C] using (univ_mem_squareCylindersMeas S E)
    have hμ_univ : (μ.bind (isssd (S := S) (E := E) ν Λ)) Set.univ ≠ ∞ := by
      have huniv_meas : MeasurableSet (Set.univ : Set (S → E)) := MeasurableSet.univ
      have hκ :
          AEMeasurable (fun η : S → E => isssd (S := S) (E := E) ν Λ η) μ :=
        ((isssd (S := S) (E := E) ν Λ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable
      have h1 : ∀ η : S → E, isssd (S := S) (E := E) ν Λ η Set.univ = 1 := by
        intro η
        simpa using (IsProbabilityMeasure.measure_univ (μ := isssd (S := S) (E := E) ν Λ η))
      haveI : IsProbabilityMeasure μ := by
        dsimp [μ]
        infer_instance
      have h_bind_univ :
          (μ.bind (isssd (S := S) (E := E) ν Λ)) Set.univ = 1 := by
        rw [Measure.bind_apply (m := μ) (f := isssd (S := S) (E := E) ν Λ)
          (s := Set.univ) huniv_meas hκ]
        simp; aesop
      simp; aesop -- using (ENNReal.one_ne_top)
    refine MeasureTheory.Measure.ext_of_generateFrom_of_iUnion_univ (C := C)
      (μ := (μ.bind (isssd (S := S) (E := E) ν Λ))) (ν := μ)
      (hA := hgen) (hC := hC_pi) (huniv := huniv) (hμ_univ := hμ_univ) ?_
    intro A hA
    rcases hA with ⟨s, t, ht, rfl⟩
    have ht_meas : ∀ i : S, MeasurableSet (t i) := by
      simpa [Set.mem_pi, Set.mem_univ, true_implies] using ht
    have h_rect_meas : MeasurableSet ((s : Set S).pi t) :=
      MeasurableSet.pi s.countable_toSet (fun i _ => ht_meas i)
    have hκ :
        AEMeasurable (fun η : S → E => isssd (S := S) (E := E) ν Λ η) μ :=
      ((isssd (S := S) (E := E) ν Λ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable
    simp [μ]
    have h_eval :
        (fun η : S → E => isssd (S := S) (E := E) ν Λ η ((s : Set S).pi t))
          =
          fun η =>
            ite (∀ i ∈ s, i ∉ Λ → η i ∈ t i) (∏ i ∈ s ∩ Λ, ν (t i)) 0 := by
      funext η
      simpa [isssd_apply, isssdFun_apply, Finset.coe_sort_coe] using
        (isssdFun_apply_squareCylinder (ν := ν) (mE := mE) (Λ := Λ) (s := s) (t := t) ht_meas η)
    let P : (S → E) → Prop := fun η => ∀ i ∈ s, i ∉ Λ → η i ∈ t i
    have hP_set :
        {η : S → E | P η} = Set.pi (s \ Λ) t := by
      ext η
      simp [P, Set.mem_pi]
    have hP_meas : MeasurableSet {η : S → E | P η} := by
      rw [hP_set]
      refine MeasurableSet.pi ?_ ?_
      · exact Set.Countable.mono (Set.diff_subset) s.countable_toSet
      · intro i hi
        exact ht_meas i
    have hite :
        (fun η : S → E => ite (P η) (∏ i ∈ s ∩ Λ, ν (t i)) 0)
          =
          ({η : S → E | P η}).indicator (fun _ => (∏ i ∈ s ∩ Λ, ν (t i))) := by
      funext η
      by_cases hPη : P η <;> simp [P, hPη]; aesop
    have hμP :
        μ {η : S → E | P η} = ∏ i ∈ s \ Λ, ν (t i) := by
      rw [hP_set]
      have hset_eq : (↑s \ ↑Λ : Set S).pi t = (↑(s \ Λ) : Set S).pi t := by
        ext η
        simp only [Set.mem_pi, Set.mem_diff, Finset.mem_coe, Finset.mem_sdiff]
      rw [hset_eq, MeasureTheory.productMeasure_boxes (μ := fun _ : S ↦ ν) (s := s \ Λ) (t := t)]
      aesop
    have hμA :
        μ ((s : Set S).pi t) = ∏ i ∈ s, ν (t i) := by
      simpa [μ] using
        (MeasureTheory.productMeasure_boxes (μ := fun _ : S ↦ ν) (s := s) (t := t)
          (mt := fun i hi => ht_meas i))
    have hsub : s ∩ Λ ⊆ s := Finset.inter_subset_left
    have hsdiff : s \ (s ∩ Λ) = s \ Λ := by
      ext i
      simp [Finset.mem_sdiff]
    have hprod_decomp :
        (∏ i ∈ s ∩ Λ, ν (t i)) * (∏ i ∈ s \ Λ, ν (t i)) = ∏ i ∈ s, ν (t i) := by
      have := (Finset.prod_sdiff (s₁ := s ∩ Λ) (s₂ := s) (f := fun i : S => ν (t i)) hsub)
      exact Finset.prod_inter_mul_prod_diff s Λ fun x ↦ ν (t x)
    aesop --simpa [hμA, hprod_decomp]
  have : Kernel.IsCondExp (isssd (S := S) (E := E) ν Λ) μ := by
    exact (Kernel.isCondExp_iff_bind_eq_left (μ := μ) (π := isssd (S := S) (E := E) ν Λ)
      hπ (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S)ᶜ))).2 h_bind
  simpa [μ] using this

end ProductMeasure

section Modifier
variable {ρ : Finset S → (S → E) → ℝ≥0∞}

/-- The kernel of a modification specification.

Modifying the specification `γ` by a family indexed by finsets `Λ : Finset S` of densities
`ρ Λ : (S → E) → ℝ≥0∞` results in a family of kernels `γ.modificationKer ρ _ Λ` whose density is
that of `γ Λ` multiplied by `ρ Λ`.

This is an auxiliary definition for `Specification.modification`, which you should generally use
instead of `Specification.modificationKer`. -/
@[simps]
noncomputable def modificationKer (γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E))
    (ρ : Finset S → (S → E) → ℝ≥0∞) (hρ : ∀ Λ, Measurable (ρ Λ)) (Λ : Finset S) :
    Kernel[cylinderEvents Λᶜ] (S → E) (S → E) :=
  @Kernel.mk _ _ (_) _
    (fun η ↦ (γ Λ η).withDensity (ρ Λ))
    (@Measure.measurable_of_measurable_coe _ _ _ (_) _ fun s hs ↦ by
      simp_rw [MeasureTheory.withDensity_apply _ hs]
      exact (Measure.measurable_setLIntegral (hρ _) hs).comp (γ Λ).measurable)

@[simp] lemma modificationKer_one' (γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E)) :
    modificationKer γ (fun _Λ _η ↦ 1) (fun _Λ ↦ measurable_const) = γ := by ext Λ; simp

@[simp] lemma modificationKer_one (γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E)) :
    modificationKer γ 1 (fun _Λ ↦ measurable_const) = γ := by ext Λ; simp

/-- A modifier of a specification `γ` is a family indexed by finsets `Λ : Finset S` of densities
`ρ Λ : (S → E) → ℝ≥0∞` such that:
* Each `ρ Λ` is measurable.
* `γ.modificationKer ρ` (informally, `ρ * γ`) is consistent. -/
@[mk_iff]
structure IsModifier (γ : Specification S E) (ρ : Finset S → (S → E) → ℝ≥0∞) : Prop where
  measurable Λ : Measurable (ρ Λ)
  isConsistent : IsConsistent (modificationKer γ ρ measurable)

@[simp] lemma IsModifier.one' : γ.IsModifier (fun _Λ _η ↦ 1) where
  measurable _ := measurable_const
  isConsistent := by simpa using γ.isConsistent

@[simp] lemma IsModifier.one : γ.IsModifier 1 := .one'

lemma isModifier_iff_ae_eq (_hγ : γ.IsProper) :
    γ.IsModifier ρ ↔
      (∀ Λ, Measurable (ρ Λ)) ∧
      ∀ ⦃Λ₁ Λ₂⦄, Λ₁ ⊆ Λ₂ → ∀ η,
        (fun ξ ↦ (γ Λ₁ ξ).withDensity (ρ Λ₁)) ∘ₘ (γ Λ₂ η).withDensity (ρ Λ₂)
          = (γ Λ₂ η).withDensity (ρ Λ₂) := by
  classical
  simp [isModifier_iff, IsConsistent, modificationKer, Kernel.ext_iff, Kernel.comp_apply, Measure.ext_iff]

lemma isModifier_iff_ae_comm [DecidableEq S] (hγ : γ.IsProper) :
    γ.IsModifier ρ ↔
      (∀ Λ, Measurable (ρ Λ)) ∧
      ∀ ⦃Λ₁ Λ₂⦄, Λ₁ ⊆ Λ₂ → ∀ η,
        (fun ξ ↦ (γ Λ₁ ξ).withDensity (ρ Λ₁)) ∘ₘ (γ Λ₂ η).withDensity (ρ Λ₂)
          = (γ Λ₂ η).withDensity (ρ Λ₂) := by
  simpa using (isModifier_iff_ae_eq (γ := γ) (ρ := ρ) hγ)

/-- Modification specification.

Modifying the specification `γ` by a family indexed by finsets `Λ : Finset S` of densities
`ρ Λ : (S → E) → ℝ≥0∞` results in a family of kernels `γ.modificationKer ρ _ Λ` whose density is
that of `γ Λ` multiplied by `ρ Λ`.

When the family of densities `ρ` is a modifier (`Specification.IsModifier`), modifying a
specification results in a specification `γ.modification ρ _`. -/
noncomputable def modification (γ : Specification S E) (ρ : Finset S → (S → E) → ℝ≥0∞)
    (hρ : γ.IsModifier ρ) : Specification S E where
  toFun := modificationKer γ ρ hρ.measurable
  isConsistent' := hρ.isConsistent

-- This is not simp as we want to keep `modificationKer` an implementation detail
lemma coe_modification (γ : Specification S E) (ρ : Finset S → (S → E) → ℝ≥0∞)
    (hρ : γ.IsModifier ρ) : γ.modification ρ hρ = modificationKer γ ρ hρ.measurable := rfl

@[simp]
lemma modification_apply (γ : Specification S E) (ρ : Finset S → (S → E) → ℝ≥0∞)
    (hρ : γ.IsModifier ρ) (Λ : Finset S) (η : S → E) :
    γ.modification ρ hρ Λ η = (γ Λ η).withDensity (ρ Λ) := rfl

@[simp] lemma IsModifier.mul {ρ₁ ρ₂ : Finset S → (S → E) → ℝ≥0∞}
    (hρ₁ : γ.IsModifier ρ₁) (hρ₂ : (γ.modification ρ₁ hρ₁).IsModifier ρ₂) :
    γ.IsModifier (ρ₁ * ρ₂) where
  measurable Λ := (hρ₁.measurable _).mul (hρ₂.measurable _)
  isConsistent Λ₁ Λ₂ hΛ := by
    simpa [modificationKer, modification_apply, Pi.mul_apply, MeasureTheory.withDensity_mul,
      hρ₁.measurable, hρ₂.measurable]
      using (hρ₂.isConsistent (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ)

@[simp] lemma modification_one' (γ : Specification S E) :
    γ.modification (fun _Λ _η ↦ 1) .one' = γ := by ext; simp

@[simp] lemma modification_one (γ : Specification S E) : γ.modification 1 .one = γ := by ext; simp

@[simp] lemma modification_modification (γ : Specification S E) (ρ₁ ρ₂ : Finset S → (S → E) → ℝ≥0∞)
    (hρ₁ : γ.IsModifier ρ₁) (hρ₂ : (γ.modification ρ₁ hρ₁).IsModifier ρ₂) :
    (γ.modification ρ₁ hρ₁).modification ρ₂ hρ₂ = γ.modification (ρ₁ * ρ₂) (hρ₁.mul hρ₂) := by
  ext Λ σ s hs
  simp only [modification_apply, Pi.mul_apply]
  rw [withDensity_apply _ hs, withDensity_apply _ hs,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (hρ₁.measurable Λ) (hρ₂.1 Λ) hs]

protected lemma IsProper.modification (hγ : γ.IsProper) {hρ} : (γ.modification ρ hρ).IsProper := by
  refine IsProper.of_inter_eq_indicator_mul fun Λ A hA B hB η ↦ ?_
  rw [modification_apply, withDensity_apply _ hA,
    withDensity_apply _ (hA.inter <| cylinderEvents_le_pi _ hB),
    hγ.setLIntegral_inter_eq_indicator_mul_setLIntegral _ (hρ.measurable _) hA hB]

/-- A premodifier is a family indexed by finsets `Λ : Finset S` of densities
`ρ Λ : (S → E) → ℝ≥0∞` such that:
* Each `ρ Λ` is measurable.
* `ρ Λ₂ ζ * ρ Λ₁ η = ρ Λ₁ ζ * ρ Λ₂ η` for all `Λ₁ Λ₂ : Finset S` and `ζ η : S → E` such that
  `Λ₁ ⊆ Λ₂` and `∀ (s : Λ₁ᶜ), ζ s = η s`-/
structure IsPremodifier [MeasurableSpace E] (ρ : Finset S → (S → E) → ℝ≥0∞) : Prop where
  measurable Λ : Measurable (ρ Λ)
  comm_of_subset ⦃Λ₁ Λ₂ : Finset S⦄ ⦃ζ η : S → E⦄ (hΛ : Λ₁ ⊆ Λ₂)
    (hrestrict : ∀ s ∉ Λ₁, ζ s = η s) : ρ Λ₂ ζ * ρ Λ₁ η = ρ Λ₁ ζ * ρ Λ₂ η

/-- For a premodifier `ρ`, the normalized density
`σ ↦ ρ Λ σ / ∫⁻ x, ρ Λ x ∂(isssd ν Λ σ)` is measurable. -/
lemma IsPremodifier.measurable_div_isssd (hρ : IsPremodifier ρ) (ν : Measure E) [IsProbabilityMeasure ν] :
    ∀ Λ, Measurable (fun σ : S → E ↦ ρ Λ σ / ∫⁻ x, ρ Λ x ∂(isssd ν Λ σ)) := by
  intro Λ
  -- `σ ↦ ∫⁻ x, ρ Λ x ∂(isssd ν Λ σ)` is measurable by the kernel measurability API.
  exact (hρ.measurable Λ).div ((hρ.measurable Λ).lintegral_kernel.mono cylinderEvents_le_pi le_rfl)

/-! ### Normalization of a premodifier (Georgii 4.6 ⇒ DLR consistency) -/

variable (ν : Measure E) [IsProbabilityMeasure ν]

/-- The *partition function* (normalizing factor) associated to a density `ρ Λ` and the independent
specification `isssd ν`. -/
noncomputable def premodifierZ (ρ : Finset S → (S → E) → ℝ≥0∞) (Λ : Finset S) (η : S → E) : ℝ≥0∞ :=
  ∫⁻ x, ρ Λ x ∂(isssd (S := S) (E := E) ν Λ η)

/-- The normalized density associated to a premodifier `ρ`:
`ρ' Λ η = ρ Λ η / Z_Λ(η)` where `Z_Λ(η) = ∫ ρ Λ x d(isssd ν Λ η)`. -/
noncomputable def premodifierNorm (ρ : Finset S → (S → E) → ℝ≥0∞) (Λ : Finset S) (η : S → E) : ℝ≥0∞ :=
  ρ Λ η / premodifierZ (S := S) (E := E) ν ρ Λ η

lemma premodifierNorm_measurable (hρ : IsPremodifier ρ) :
    ∀ Λ, Measurable (premodifierNorm (S := S) (E := E) ν ρ Λ) := by
  intro Λ
  simpa [premodifierNorm, premodifierZ] using (hρ.measurable_div_isssd (S := S) (E := E) (ρ := ρ) ν Λ)

lemma premodifierZ_congr_of_eqOn_compl
    {Λ : Finset S} (hρΛ : Measurable (ρ Λ)) {η₁ η₂ : S → E} (h : ∀ s ∉ Λ, η₁ s = η₂ s) :
    premodifierZ (S := S) (E := E) ν ρ Λ η₁ = premodifierZ (S := S) (E := E) ν ρ Λ η₂ := by
  classical
  have hjuxt : juxt (Λ := (Λ : Set S)) η₁ = juxt (Λ := (Λ : Set S)) η₂ := by
    funext ζ x
    by_cases hx : x ∈ (Λ : Set S)
    · simp [juxt_apply_of_mem (Λ := (Λ : Set S)) (η := η₁) (ζ := ζ) hx,
        juxt_apply_of_mem (Λ := (Λ : Set S)) (η := η₂) (ζ := ζ) hx]
    · have hx' : x ∉ Λ := by
        simpa [Finset.mem_coe] using hx
      simp [juxt_apply_of_not_mem (Λ := (Λ : Set S)) (η := η₁) (ζ := ζ) hx,
        juxt_apply_of_not_mem (Λ := (Λ : Set S)) (η := η₂) (ζ := ζ) hx, h x hx']
  simp [premodifierZ, isssd_apply, isssdFun_apply]
  rw [lintegral_map hρΛ (Measurable.juxt (Λ := (Λ : Set S)) (η := η₁) (𝓔 := mE))]
  simpa [hjuxt] using
    (lintegral_map hρΛ (Measurable.juxt (Λ := (Λ : Set S)) (η := η₂) (𝓔 := mE))).symm

set_option maxHeartbeats 800000 in
lemma IsPremodifier.isModifier_premodifierNorm (hρ : IsPremodifier ρ)
    (hZ : ∀ (Λ : Finset S) (η : S → E),
      premodifierZ (S := S) (E := E) ν ρ Λ η ≠ 0 ∧
        premodifierZ (S := S) (E := E) ν ρ Λ η ≠ ⊤) :
    (isssd (S := S) (E := E) ν).IsModifier (premodifierNorm (S := S) (E := E) ν ρ) := by
  classical
  refine ⟨premodifierNorm_measurable (S := S) (E := E) (ρ := ρ) ν hρ, ?_⟩
  intro Λ₁ Λ₂ hΛ
  ext η A hA
  let Z : Finset S → (S → E) → ℝ≥0∞ := premodifierZ (S := S) (E := E) ν ρ
  let ρ' : Finset S → (S → E) → ℝ≥0∞ := premodifierNorm (S := S) (E := E) ν ρ
  have hZmeas : ∀ Λ : Finset S, Measurable[cylinderEvents (Λ : Set S)ᶜ] (Z Λ) := by
    intro Λ
    simpa [Z, premodifierZ] using
      (Measurable.lintegral_kernel (κ := (isssd (S := S) (E := E) ν Λ)) (f := ρ Λ) (hρ.measurable Λ))
  have hρ'meas : ∀ Λ, Measurable (ρ' Λ) := premodifierNorm_measurable (S := S) (E := E) (ρ := ρ) ν hρ
  have hLHS :
      (((fun x : S → E => ((isssd (S := S) (E := E) ν Λ₁ x).withDensity (ρ' Λ₁))) ∘ₘ
            ((isssd (S := S) (E := E) ν Λ₂ η).withDensity (ρ' Λ₂))) A)
        =
        ∫⁻ x, ((isssd (S := S) (E := E) ν Λ₁ x).withDensity (ρ' Λ₁)) A
          ∂((isssd (S := S) (E := E) ν Λ₂ η).withDensity (ρ' Λ₂)) := by
    have hκ₁_ae :
        AEMeasurable
          (fun x : S → E => ((isssd (S := S) (E := E) ν Λ₁ x).withDensity (ρ' Λ₁)))
          (((isssd (S := S) (E := E) ν Λ₂ η).withDensity (ρ' Λ₂))) := by
      let K₁ : Kernel[cylinderEvents Λ₁ᶜ] (S → E) (S → E) :=
        modificationKer (γ := (isssd (S := S) (E := E) ν)) (ρ := ρ' ) (hρ := hρ'meas) Λ₁
      have hK₁ : Measurable (fun x : S → E => (K₁ x)) :=
        (K₁.measurable).mono cylinderEvents_le_pi le_rfl
      exact hK₁.aemeasurable
    simpa using
      (Measure.bind_apply (m := (isssd (S := S) (E := E) ν Λ₂ η).withDensity (ρ' Λ₂))
        (f := fun x : S → E => (isssd (S := S) (E := E) ν Λ₁ x).withDensity (ρ' Λ₁))
        (s := A) hA hκ₁_ae)
  have hinner :
      (fun x : S → E => ((isssd (S := S) (E := E) ν Λ₁ x).withDensity (ρ' Λ₁)) A)
        =
        fun x : S → E => ∫⁻ y in A, ρ' Λ₁ y ∂((isssd (S := S) (E := E) ν Λ₁) x) := by
    funext x
    simp [withDensity_apply _ hA]
  have houter :
      ∫⁻ x, ((isssd (S := S) (E := E) ν Λ₁ x).withDensity (ρ' Λ₁)) A
        ∂((isssd (S := S) (E := E) ν Λ₂ η).withDensity (ρ' Λ₂))
        =
      ∫⁻ x, (ρ' Λ₂ x) *
          ((isssd (S := S) (E := E) ν Λ₁ x).withDensity (ρ' Λ₁)) A
        ∂((isssd (S := S) (E := E) ν Λ₂) η) := by
    have hmeas_integrand :
        Measurable fun x : S → E => ((isssd (S := S) (E := E) ν Λ₁ x).withDensity (ρ' Λ₁)) A := by
      let K₁ : Kernel[cylinderEvents Λ₁ᶜ] (S → E) (S → E) :=
        modificationKer (γ := (isssd (S := S) (E := E) ν)) (ρ := ρ') (hρ := hρ'meas) Λ₁
      have hmeas_dom : Measurable[cylinderEvents Λ₁ᶜ] (fun x : S → E => (K₁ x) A) :=
        Kernel.measurable_coe K₁ hA
      exact hmeas_dom.mono cylinderEvents_le_pi le_rfl
    simpa using
      (lintegral_withDensity_eq_lintegral_mul (μ := (isssd (S := S) (E := E) ν Λ₂ η))
        (f := (ρ' Λ₂)) (h_mf := hρ'meas Λ₂) (g := fun x =>
          ((isssd (S := S) (E := E) ν Λ₁ x).withDensity (ρ' Λ₁)) A) hmeas_integrand)
  let K : Finset S → (S → E) → Measure (S → E) := fun Λ η => (isssd (S := S) (E := E) ν Λ) η
  let μ : (Λ : Finset S) → Measure (Λ → E) := fun Λ => Measure.pi (fun _ : Λ ↦ ν)
  have hK_apply (Λ : Finset S) (η : S → E) :
      K Λ η = Measure.map (juxt (Λ := (Λ : Set S)) (η := η)) (μ Λ) := by
    simp [K, μ, isssd_apply, isssdFun_apply]
  have hLHS' :
      (((fun x : S → E => ((isssd (S := S) (E := E) ν Λ₁ x).withDensity (ρ' Λ₁))) ∘ₘ
              ((isssd (S := S) (E := E) ν Λ₂ η).withDensity (ρ' Λ₂))) A)
        =
      ∫⁻ x, (ρ' Λ₂ x) * ((isssd (S := S) (E := E) ν Λ₁ x).withDensity (ρ' Λ₁)) A
        ∂((isssd (S := S) (E := E) ν Λ₂) η) := by
    calc
      (((fun x : S → E => ((isssd (S := S) (E := E) ν Λ₁ x).withDensity (ρ' Λ₁))) ∘ₘ
            ((isssd (S := S) (E := E) ν Λ₂ η).withDensity (ρ' Λ₂))) A)
          =
          ∫⁻ x, ((isssd (S := S) (E := E) ν Λ₁ x).withDensity (ρ' Λ₁)) A
            ∂((isssd (S := S) (E := E) ν Λ₂ η).withDensity (ρ' Λ₂)) := hLHS
      _ =
          ∫⁻ x, (ρ' Λ₂ x) * ((isssd (S := S) (E := E) ν Λ₁ x).withDensity (ρ' Λ₁)) A
            ∂((isssd (S := S) (E := E) ν Λ₂) η) := houter
  have hRHS' :
      ((isssd (S := S) (E := E) ν Λ₂ η).withDensity (ρ' Λ₂)) A =
        ∫⁻ x in A, (ρ' Λ₂) x ∂((isssd (S := S) (E := E) ν Λ₂) η) := by
    simp [withDensity_apply _ hA]
  have hZ₂_meas : Measurable[cylinderEvents (Λ₂ : Set S)ᶜ] (Z Λ₂) := hZmeas Λ₂
  have hZ₂inv_meas : Measurable[cylinderEvents (Λ₂ : Set S)ᶜ] (fun x : S → E => (Z Λ₂ x)⁻¹) :=
    hZ₂_meas.inv
  have hproper : (isssd (S := S) (E := E) ν).IsProper := Specification.IsProper.isssd (S := S) (E := E) (ν := ν)
  have hinner_simpl :
      (fun x : S → E => ((isssd (S := S) (E := E) ν Λ₁ x).withDensity (ρ' Λ₁)) A)
        =
      fun x : S → E =>
        (Z Λ₁ x)⁻¹ * ∫⁻ y in A, ρ Λ₁ y ∂((isssd (S := S) (E := E) ν Λ₁) x) := by
    funext x
    have hρΛ₁ : Measurable (ρ Λ₁) := hρ.measurable Λ₁
    have hZ₁_meas : Measurable[cylinderEvents (Λ₁ : Set S)ᶜ] (Z Λ₁) := hZmeas Λ₁
    have hZ₁inv_meas : Measurable[cylinderEvents (Λ₁ : Set S)ᶜ] (fun y : S → E => (Z Λ₁ y)⁻¹) :=
      hZ₁_meas.inv
    have hpull :
        ∫⁻ y, (fun y : S → E => (Z Λ₁ y)⁻¹) y *
            (A.indicator fun y : S → E => ρ Λ₁ y) y
          ∂((isssd (S := S) (E := E) ν Λ₁) x)
          =
          (fun y : S → E => (Z Λ₁ y)⁻¹) x *
            ∫⁻ y, (A.indicator fun y : S → E => ρ Λ₁ y) y
              ∂((isssd (S := S) (E := E) ν Λ₁) x) :=
      Specification.IsProper.lintegral_mul (γ := isssd (S := S) (E := E) ν)
        (f := A.indicator fun y : S → E => ρ Λ₁ y)
        (g := fun y : S → E => (Z Λ₁ y)⁻¹)
        (η₀ := x) (Λ := Λ₁) (hγ := hproper)
        (hf := (Measurable.indicator hρΛ₁ hA))
        (hg := hZ₁inv_meas)
    calc
      ((isssd (S := S) (E := E) ν Λ₁ x).withDensity (ρ' Λ₁)) A
          = ∫⁻ y in A, (ρ' Λ₁) y ∂((isssd (S := S) (E := E) ν Λ₁) x) := by
              simp [withDensity_apply _ hA]
      _ = ∫⁻ y in A, ρ Λ₁ y * (Z Λ₁ y)⁻¹ ∂((isssd (S := S) (E := E) ν Λ₁) x) := by
            simp [ρ', premodifierNorm, Z, div_eq_mul_inv]
      _ = (Z Λ₁ x)⁻¹ * ∫⁻ y in A, ρ Λ₁ y ∂((isssd (S := S) (E := E) ν Λ₁) x) := by
            have hL :
                ∫⁻ y in A, ρ Λ₁ y * (Z Λ₁ y)⁻¹ ∂((isssd (S := S) (E := E) ν Λ₁) x)
                  =
                ∫⁻ y, (Z Λ₁ y)⁻¹ * (A.indicator fun y : S → E => ρ Λ₁ y) y
                  ∂((isssd (S := S) (E := E) ν Λ₁) x) := by
              rw [← lintegral_indicator (μ := ((isssd (S := S) (E := E) ν Λ₁) x)) hA
                    (f := fun y : S → E => ρ Λ₁ y * (Z Λ₁ y)⁻¹)]
              simp [Set.indicator_mul_left, mul_comm]
            have hR :
                (Z Λ₁ x)⁻¹ * ∫⁻ y, (A.indicator fun y : S → E => ρ Λ₁ y) y
                  ∂((isssd (S := S) (E := E) ν Λ₁) x)
                  =
                (Z Λ₁ x)⁻¹ * ∫⁻ y in A, ρ Λ₁ y ∂((isssd (S := S) (E := E) ν Λ₁) x) := by
              simp [lintegral_indicator hA]
            calc
              ∫⁻ y in A, ρ Λ₁ y * (Z Λ₁ y)⁻¹ ∂((isssd (S := S) (E := E) ν Λ₁) x)
                  = ∫⁻ y, (Z Λ₁ y)⁻¹ * (A.indicator fun y : S → E => ρ Λ₁ y) y
                      ∂((isssd (S := S) (E := E) ν Λ₁) x) := hL
              _ = (Z Λ₁ x)⁻¹ * ∫⁻ y, (A.indicator fun y : S → E => ρ Λ₁ y) y
                      ∂((isssd (S := S) (E := E) ν Λ₁) x) := by
                    simpa using hpull
              _ = (Z Λ₁ x)⁻¹ * ∫⁻ y in A, ρ Λ₁ y ∂((isssd (S := S) (E := E) ν Λ₁) x) := hR
  let γ : Finset S → (S → E) → Measure (S → E) := fun Λ ξ => (isssd (S := S) (E := E) ν Λ) ξ
  let kA : (S → E) → ℝ≥0∞ := fun ξ => ((γ Λ₁ ξ).withDensity (ρ' Λ₁)) A
  let I₁ : (S → E) → ℝ≥0∞ := fun ξ => ∫⁻ ζ in A, ρ Λ₁ ζ ∂(γ Λ₁ ξ)
  let H : (S → E) → ℝ≥0∞ := fun ξ => ∫⁻ ζ in A, ρ Λ₂ ζ ∂(γ Λ₁ ξ)
  have hkA_meas : Measurable kA := by
    let K₁ : Kernel[cylinderEvents (Λ₁ : Set S)ᶜ] (S → E) (S → E) :=
      modificationKer (γ := (isssd (S := S) (E := E) ν)) (ρ := ρ') (hρ := hρ'meas) Λ₁
    have hmeas_dom : Measurable[cylinderEvents (Λ₁ : Set S)ᶜ] (fun ξ : S → E => (K₁ ξ) A) :=
      Kernel.measurable_coe K₁ hA
    simpa [kA, γ, K₁, modificationKer] using hmeas_dom.mono cylinderEvents_le_pi le_rfl
  have hI₁_meas : Measurable I₁ := by
    have hmeas_dom : Measurable[cylinderEvents (Λ₁ : Set S)ᶜ] I₁ := by
      have hρΛ₁ : Measurable (ρ Λ₁) := hρ.measurable Λ₁
      have h_ind : Measurable (A.indicator fun ζ : S → E => ρ Λ₁ ζ) :=
        (Measurable.indicator hρΛ₁ hA)
      simpa [I₁, γ, lintegral_indicator hA] using
        (Measurable.lintegral_kernel (κ := (isssd (S := S) (E := E) ν Λ₁))
          (f := A.indicator fun ζ : S → E => ρ Λ₁ ζ) h_ind)
    exact hmeas_dom.mono cylinderEvents_le_pi le_rfl
  have hH_meas_Λ₁c : Measurable[cylinderEvents (Λ₁ : Set S)ᶜ] H := by
    have hρΛ₂ : Measurable (ρ Λ₂) := hρ.measurable Λ₂
    have h_ind : Measurable (A.indicator fun ζ : S → E => ρ Λ₂ ζ) :=
      (Measurable.indicator hρΛ₂ hA)
    simpa [H, γ, lintegral_indicator hA] using
      (Measurable.lintegral_kernel (κ := (isssd (S := S) (E := E) ν Λ₁))
        (f := A.indicator fun ζ : S → E => ρ Λ₂ ζ) h_ind)
  have hH_meas : Measurable H := hH_meas_Λ₁c.mono cylinderEvents_le_pi le_rfl
  have hρΛ₂ : Measurable (ρ Λ₂) := hρ.measurable Λ₂
  have hZ₂inv_meas : Measurable[cylinderEvents (Λ₂ : Set S)ᶜ] (fun ξ : S → E => (Z Λ₂ ξ)⁻¹) :=
    (hZmeas Λ₂).inv
  have hZ₂inv_meas_pi : Measurable (fun ξ : S → E => (Z Λ₂ ξ)⁻¹) :=
    hZ₂inv_meas.mono cylinderEvents_le_pi le_rfl
  have hLHS_factor :
      (∫⁻ ξ, ρ' Λ₂ ξ * kA ξ ∂(γ Λ₂ η))
        =
      (Z Λ₂ η)⁻¹ * ∫⁻ ξ, ρ Λ₂ ξ * kA ξ ∂(γ Λ₂ η) := by
    have hproper' : (isssd (S := S) (E := E) ν).IsProper := Specification.IsProper.isssd (S := S) (E := E) (ν := ν)
    have hpull :
        (∫⁻ ξ, (fun x : S → E => (Z Λ₂ x)⁻¹) ξ * (fun ξ : S → E => ρ Λ₂ ξ * kA ξ) ξ ∂(γ Λ₂ η)) =
          (fun x : S → E => (Z Λ₂ x)⁻¹) η * ∫⁻ ξ, (fun ξ : S → E => ρ Λ₂ ξ * kA ξ) ξ ∂(γ Λ₂ η) :=
      Specification.IsProper.lintegral_mul (γ := isssd (S := S) (E := E) ν)
        (hγ := hproper') (Λ := Λ₂) (η₀ := η)
        (f := fun ξ : S → E => ρ Λ₂ ξ * kA ξ)
        (g := fun ξ : S → E => (Z Λ₂ ξ)⁻¹)
        (hf := (hρΛ₂.mul hkA_meas))
        (hg := hZ₂inv_meas)
    calc
      ∫⁻ ξ, ρ' Λ₂ ξ * kA ξ ∂(γ Λ₂ η)
          = ∫⁻ ξ, (Z Λ₂ ξ)⁻¹ * (ρ Λ₂ ξ * kA ξ) ∂(γ Λ₂ η) := by
              simp [ρ', premodifierNorm, Z, div_eq_mul_inv, mul_assoc, mul_left_comm]
      _ = (Z Λ₂ η)⁻¹ * ∫⁻ ξ, ρ Λ₂ ξ * kA ξ ∂(γ Λ₂ η) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hpull
  have hRHS_factor :
      (∫⁻ ξ in A, ρ' Λ₂ ξ ∂(γ Λ₂ η))
        =
      (Z Λ₂ η)⁻¹ * ∫⁻ ξ in A, ρ Λ₂ ξ ∂(γ Λ₂ η) := by
    have hproper' : (isssd (S := S) (E := E) ν).IsProper := Specification.IsProper.isssd (S := S) (E := E) (ν := ν)
    have hpull :
        (∫⁻ ξ, (fun x : S → E => (Z Λ₂ x)⁻¹) ξ * (A.indicator fun ξ : S → E => ρ Λ₂ ξ) ξ ∂(γ Λ₂ η)) =
          (fun x : S → E => (Z Λ₂ x)⁻¹) η *
            ∫⁻ ξ, (A.indicator fun ξ : S → E => ρ Λ₂ ξ) ξ ∂(γ Λ₂ η) :=
      Specification.IsProper.lintegral_mul (γ := isssd (S := S) (E := E) ν)
        (hγ := hproper') (Λ := Λ₂) (η₀ := η)
        (f := A.indicator fun ξ : S → E => ρ Λ₂ ξ)
        (g := fun ξ : S → E => (Z Λ₂ ξ)⁻¹)
        (hf := (Measurable.indicator hρΛ₂ hA))
        (hg := hZ₂inv_meas)
    have :
        ∫⁻ ξ in A, ρ' Λ₂ ξ ∂(γ Λ₂ η) =
          ∫⁻ ξ, (Z Λ₂ ξ)⁻¹ * (A.indicator fun ξ : S → E => ρ Λ₂ ξ) ξ ∂(γ Λ₂ η) := by
      rw [← lintegral_indicator hA]
      refine lintegral_congr_ae ?_
      filter_upwards with ξ
      by_cases hξ : ξ ∈ A
      · simp [hξ, ρ', premodifierNorm, Z, div_eq_mul_inv, mul_comm]
      · simp [hξ, ρ', Z]
    calc
      ∫⁻ ξ in A, ρ' Λ₂ ξ ∂(γ Λ₂ η)
          = ∫⁻ ξ, (Z Λ₂ ξ)⁻¹ * (A.indicator fun ξ : S → E => ρ Λ₂ ξ) ξ ∂(γ Λ₂ η) := this
      _ = (Z Λ₂ η)⁻¹ * ∫⁻ ξ, (A.indicator fun ξ : S → E => ρ Λ₂ ξ) ξ ∂(γ Λ₂ η) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hpull
      _ = (Z Λ₂ η)⁻¹ * ∫⁻ ξ in A, ρ Λ₂ ξ ∂(γ Λ₂ η) := by
            simp [lintegral_indicator hA]
  have h_noZ :
      (∫⁻ ξ, ρ Λ₂ ξ * kA ξ ∂(γ Λ₂ η)) = ∫⁻ ξ in A, ρ Λ₂ ξ ∂(γ Λ₂ η) := by
    have hkA_simpl : kA = fun ξ : S → E => (Z Λ₁ ξ)⁻¹ * I₁ ξ := by
      ext ξ
      have := congrArg (fun f => f ξ) hinner_simpl
      simpa [kA, I₁, γ] using this
    have h_cocycle (ξ : S → E) : ρ Λ₂ ξ * I₁ ξ = ρ Λ₁ ξ * H ξ := by
      classical
      have hI_map :
          I₁ ξ =
            ∫⁻ (ζ : Λ₁ → E) in (juxt (Λ := (Λ₁ : Set S)) (η := ξ)) ⁻¹' A,
              ρ Λ₁ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ) ∂(Measure.pi (fun _ : Λ₁ => ν)) := by
        simpa [I₁, γ] using
          (show ∫⁻ x in A, ρ Λ₁ x ∂(isssd (S := S) (E := E) ν Λ₁ ξ)
              =
              ∫⁻ (ζ : Λ₁ → E) in (juxt (Λ := (Λ₁ : Set S)) (η := ξ)) ⁻¹' A,
                ρ Λ₁ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ) ∂(Measure.pi (fun _ : Λ₁ => ν)) by
            classical
            simp [isssd_apply, isssdFun_apply]
            simpa using
              (setLIntegral_map (μ := Measure.pi (fun _ : Λ₁ => ν)) (s := A) (f := ρ Λ₁)
                (g := juxt (Λ := (Λ₁ : Set S)) (η := ξ)) hA (hρ.measurable Λ₁)
                (Measurable.juxt (Λ := (Λ₁ : Set S)) (η := ξ) (𝓔 := mE))))
      have hH_map :
          H ξ =
            ∫⁻ (ζ : Λ₁ → E) in (juxt (Λ := (Λ₁ : Set S)) (η := ξ)) ⁻¹' A,
              ρ Λ₂ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ) ∂(Measure.pi (fun _ : Λ₁ => ν)) := by
        simpa [H, γ] using
          (show ∫⁻ x in A, ρ Λ₂ x ∂(isssd (S := S) (E := E) ν Λ₁ ξ)
              =
              ∫⁻ (ζ : Λ₁ → E) in (juxt (Λ := (Λ₁ : Set S)) (η := ξ)) ⁻¹' A,
                ρ Λ₂ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ) ∂(Measure.pi (fun _ : Λ₁ => ν)) by
            classical
            simp [isssd_apply, isssdFun_apply]
            simpa using
              (setLIntegral_map (μ := Measure.pi (fun _ : Λ₁ => ν)) (s := A) (f := ρ Λ₂)
                (g := juxt (Λ := (Λ₁ : Set S)) (η := ξ)) hA (hρ.measurable Λ₂)
                (Measurable.juxt (Λ := (Λ₁ : Set S)) (η := ξ) (𝓔 := mE))))
      have hpoint :
          ∀ ζ : Λ₁ → E,
            ρ Λ₂ ξ * ρ Λ₁ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ) =
              ρ Λ₁ ξ * ρ Λ₂ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ) := by
        intro ζ
        have hrestrict : ∀ s ∉ Λ₁, (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ) s = ξ s := by
          intro s hs
          simpa using (juxt_agree_on_compl (Λ := Λ₁) (η := ξ) (ζ := ζ) s hs)
        have hc := hρ.comm_of_subset (Λ₁ := Λ₁) (Λ₂ := Λ₂) (ζ := (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ))
          (η := ξ) hΛ hrestrict
        simpa [mul_comm, mul_left_comm, mul_assoc] using hc.symm
      rw [hI_map, hH_map]
      have hpre : MeasurableSet ((juxt (Λ := (Λ₁ : Set S)) (η := ξ)) ⁻¹' A) := by
        exact hA.preimage (Measurable.juxt (Λ := (Λ₁ : Set S)) (η := ξ) (𝓔 := mE))
      have hL :
          ρ Λ₂ ξ *
              ∫⁻ (ζ : Λ₁ → E) in (juxt (Λ := (Λ₁ : Set S)) (η := ξ)) ⁻¹' A,
                ρ Λ₁ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ) ∂Measure.pi (fun _ : Λ₁ => ν)
            =
            ∫⁻ (ζ : Λ₁ → E) in (juxt (Λ := (Λ₁ : Set S)) (η := ξ)) ⁻¹' A,
              ρ Λ₂ ξ * ρ Λ₁ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ) ∂Measure.pi (fun _ : Λ₁ => ν) := by
        have hf : Measurable fun ζ : Λ₁ → E => ρ Λ₁ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ) := by
          exact (hρ.measurable Λ₁).comp (Measurable.juxt (Λ := (Λ₁ : Set S)) (η := ξ) (𝓔 := mE))
        rw [← lintegral_indicator hpre (μ := Measure.pi (fun _ : Λ₁ => ν))
              (f := fun ζ : Λ₁ → E => ρ Λ₁ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ))]
        rw [← lintegral_indicator hpre (μ := Measure.pi (fun _ : Λ₁ => ν))
              (f := fun ζ : Λ₁ → E => ρ Λ₂ ξ * ρ Λ₁ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ))]
        have hconst :
            ρ Λ₂ ξ *
                (∫⁻ ζ : Λ₁ → E,
                  ((juxt (Λ := (Λ₁ : Set S)) (η := ξ)) ⁻¹' A).indicator
                      (fun ζ : Λ₁ → E => ρ Λ₁ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ)) ζ
                    ∂Measure.pi (fun _ : Λ₁ => ν))
              =
              ∫⁻ ζ : Λ₁ → E,
                ρ Λ₂ ξ *
                    ((juxt (Λ := (Λ₁ : Set S)) (η := ξ)) ⁻¹' A).indicator
                        (fun ζ : Λ₁ → E => ρ Λ₁ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ)) ζ
                  ∂Measure.pi (fun _ : Λ₁ => ν) := by
          simpa using
            (lintegral_const_mul (μ := Measure.pi (fun _ : Λ₁ => ν)) (ρ Λ₂ ξ)
              (f := fun ζ : Λ₁ → E =>
                ((juxt (Λ := (Λ₁ : Set S)) (η := ξ)) ⁻¹' A).indicator
                  (fun ζ : Λ₁ → E => ρ Λ₁ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ)) ζ)
              (Measurable.indicator hf hpre)).symm
        refine hconst.trans ?_
        refine lintegral_congr_ae ?_
        filter_upwards with ζ
        by_cases hζ : ζ ∈ (juxt (Λ := (Λ₁ : Set S)) (η := ξ)) ⁻¹' A
        · simp [hζ]
        · simp [hζ]
      have hR :
          ρ Λ₁ ξ *
              ∫⁻ (ζ : Λ₁ → E) in (juxt (Λ := (Λ₁ : Set S)) (η := ξ)) ⁻¹' A,
                ρ Λ₂ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ) ∂Measure.pi (fun _ : Λ₁ => ν)
            =
            ∫⁻ (ζ : Λ₁ → E) in (juxt (Λ := (Λ₁ : Set S)) (η := ξ)) ⁻¹' A,
              ρ Λ₁ ξ * ρ Λ₂ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ) ∂Measure.pi (fun _ : Λ₁ => ν) := by
        have hf : Measurable fun ζ : Λ₁ → E => ρ Λ₂ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ) := by
          exact (hρ.measurable Λ₂).comp (Measurable.juxt (Λ := (Λ₁ : Set S)) (η := ξ) (𝓔 := mE))
        rw [← lintegral_indicator hpre (μ := Measure.pi (fun _ : Λ₁ => ν))
              (f := fun ζ : Λ₁ → E => ρ Λ₂ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ))]
        rw [← lintegral_indicator hpre (μ := Measure.pi (fun _ : Λ₁ => ν))
              (f := fun ζ : Λ₁ → E => ρ Λ₁ ξ * ρ Λ₂ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ))]
        have hconst :
            ρ Λ₁ ξ *
                (∫⁻ ζ : Λ₁ → E,
                  ((juxt (Λ := (Λ₁ : Set S)) (η := ξ)) ⁻¹' A).indicator
                      (fun ζ : Λ₁ → E => ρ Λ₂ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ)) ζ
                    ∂Measure.pi (fun _ : Λ₁ => ν))
              =
              ∫⁻ ζ : Λ₁ → E,
                ρ Λ₁ ξ *
                    ((juxt (Λ := (Λ₁ : Set S)) (η := ξ)) ⁻¹' A).indicator
                        (fun ζ : Λ₁ → E => ρ Λ₂ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ)) ζ
                  ∂Measure.pi (fun _ : Λ₁ => ν) := by
          simpa using
            (lintegral_const_mul (μ := Measure.pi (fun _ : Λ₁ => ν)) (ρ Λ₁ ξ)
              (f := fun ζ : Λ₁ → E =>
                ((juxt (Λ := (Λ₁ : Set S)) (η := ξ)) ⁻¹' A).indicator
                  (fun ζ : Λ₁ → E => ρ Λ₂ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ)) ζ)
              (Measurable.indicator hf hpre)).symm
        refine hconst.trans ?_
        refine lintegral_congr_ae ?_
        filter_upwards with ζ
        by_cases hζ : ζ ∈ (juxt (Λ := (Λ₁ : Set S)) (η := ξ)) ⁻¹' A
        · simp [hζ]
        · simp [hζ]
      -- Use `hpoint` inside the set-lintegral to swap `ρ Λ₂ ξ` across the resampling in `Λ₁`.
      have hEqInt :
          (∫⁻ (ζ : Λ₁ → E) in (juxt (Λ := (Λ₁ : Set S)) (η := ξ)) ⁻¹' A,
              ρ Λ₂ ξ * ρ Λ₁ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ) ∂Measure.pi (fun _ : Λ₁ => ν))
            =
            (∫⁻ (ζ : Λ₁ → E) in (juxt (Λ := (Λ₁ : Set S)) (η := ξ)) ⁻¹' A,
              ρ Λ₁ ξ * ρ Λ₂ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ) ∂Measure.pi (fun _ : Λ₁ => ν)) := by
        rw [← lintegral_indicator hpre (μ := Measure.pi (fun _ : Λ₁ => ν))]
        rw [← lintegral_indicator hpre (μ := Measure.pi (fun _ : Λ₁ => ν))]
        refine lintegral_congr_ae ?_
        filter_upwards with ζ
        by_cases hζ : ζ ∈ (juxt (Λ := (Λ₁ : Set S)) (η := ξ)) ⁻¹' A
        · simp [hζ, hpoint ζ]
        · simp [hζ]
      calc
        ρ Λ₂ ξ *
            ∫⁻ (ζ : Λ₁ → E) in (juxt (Λ := (Λ₁ : Set S)) (η := ξ)) ⁻¹' A,
              ρ Λ₁ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ) ∂Measure.pi (fun _ : Λ₁ => ν)
            =
            ∫⁻ (ζ : Λ₁ → E) in (juxt (Λ := (Λ₁ : Set S)) (η := ξ)) ⁻¹' A,
              ρ Λ₂ ξ * ρ Λ₁ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ) ∂Measure.pi (fun _ : Λ₁ => ν) := hL
        _ =
            ∫⁻ (ζ : Λ₁ → E) in (juxt (Λ := (Λ₁ : Set S)) (η := ξ)) ⁻¹' A,
              ρ Λ₁ ξ * ρ Λ₂ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ) ∂Measure.pi (fun _ : Λ₁ => ν) := hEqInt
        _ =
            ρ Λ₁ ξ *
              ∫⁻ (ζ : Λ₁ → E) in (juxt (Λ := (Λ₁ : Set S)) (η := ξ)) ⁻¹' A,
                ρ Λ₂ (juxt (Λ := (Λ₁ : Set S)) (η := ξ) ζ) ∂Measure.pi (fun _ : Λ₁ => ν) := by
              simpa using hR.symm
    have h_rearrange (ξ : S → E) : ρ Λ₂ ξ * kA ξ = ρ' Λ₁ ξ * H ξ := by
      calc
        ρ Λ₂ ξ * kA ξ
            = ρ Λ₂ ξ * ((Z Λ₁ ξ)⁻¹ * I₁ ξ) := by
                simp [hkA_simpl]
        _ = (Z Λ₁ ξ)⁻¹ * (ρ Λ₂ ξ * I₁ ξ) := by
              simp [mul_left_comm]
        _ = (Z Λ₁ ξ)⁻¹ * (ρ Λ₁ ξ * H ξ) := by
              simp [h_cocycle ξ]
        _ = (ρ Λ₁ ξ * (Z Λ₁ ξ)⁻¹) * H ξ := by
              simp [mul_assoc, mul_left_comm]
        _ = ρ' Λ₁ ξ * H ξ := by
              simp [ρ', premodifierNorm, Z, div_eq_mul_inv, mul_assoc]
    have hI :
        (∫⁻ ξ, ρ Λ₂ ξ * kA ξ ∂(γ Λ₂ η)) = ∫⁻ ξ, ρ' Λ₁ ξ * H ξ ∂(γ Λ₂ η) := by
      refine lintegral_congr_ae ?_
      filter_upwards with ξ
      exact h_rearrange ξ
    have hNorm :
        ∀ (Λ : Finset S) (ξ : S → E), ∫⁻ x, ρ' Λ x ∂(γ Λ ξ) = 1 := by
      intro Λ ξ
      have hproper' : (isssd (S := S) (E := E) ν).IsProper := Specification.IsProper.isssd (S := S) (E := E) (ν := ν)
      have hZmeasΛ : Measurable[cylinderEvents (Λ : Set S)ᶜ] (Z Λ) := hZmeas Λ
      have hZinvΛ : Measurable[cylinderEvents (Λ : Set S)ᶜ] (fun x : S → E => (Z Λ x)⁻¹) := hZmeasΛ.inv
      have hpull :=
        Specification.IsProper.lintegral_mul (γ := isssd (S := S) (E := E) ν)
          (hγ := hproper') (Λ := Λ) (η₀ := ξ) (f := ρ Λ) (g := fun x : S → E => (Z Λ x)⁻¹)
          (hf := hρ.measurable Λ) (hg := hZinvΛ)
      have hZξ : Z Λ ξ ≠ 0 ∧ Z Λ ξ ≠ ⊤ := hZ Λ ξ
      calc
        ∫⁻ x, ρ' Λ x ∂(γ Λ ξ)
            = ∫⁻ x, (Z Λ x)⁻¹ * ρ Λ x ∂(γ Λ ξ) := by
                simp [ρ', premodifierNorm, Z, div_eq_mul_inv, mul_comm]
        _ = (Z Λ ξ)⁻¹ * ∫⁻ x, ρ Λ x ∂(γ Λ ξ) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using hpull
        _ = (Z Λ ξ)⁻¹ * Z Λ ξ := by simp [Z, premodifierZ, γ]
        _ = 1 := ENNReal.inv_mul_cancel hZξ.1 hZξ.2
    have h_boundary :
        ∫⁻ ξ, ρ' Λ₁ ξ * H ξ ∂(γ Λ₂ η) = ∫⁻ ξ, H ξ ∂(γ Λ₂ η) := by
      have hproper' : (isssd (S := S) (E := E) ν).IsProper := Specification.IsProper.isssd (S := S) (E := E) (ν := ν)
      have hcons : ((isssd (S := S) (E := E) ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ
          (isssd (S := S) (E := E) ν Λ₂)) = (isssd (S := S) (E := E) ν Λ₂) :=
        (isssd (S := S) (E := E) ν).isConsistent hΛ
      have hcons_eta :
          (((isssd (S := S) (E := E) ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ
              (isssd (S := S) (E := E) ν Λ₂)) η) = (γ Λ₂ η) := by
        simpa [γ] using congrArg (fun κ => κ η) hcons
      have hmeas_prod : Measurable fun ξ : S → E => ρ' Λ₁ ξ * H ξ :=
        (hρ'meas Λ₁).mul hH_meas
      calc
        ∫⁻ ξ, ρ' Λ₁ ξ * H ξ ∂(γ Λ₂ η)
            = ∫⁻ ξ, ρ' Λ₁ ξ * H ξ
                ∂(((isssd (S := S) (E := E) ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ
                    (isssd (S := S) (E := E) ν Λ₂)) η) := by
                  rw [hcons_eta]
        _ = ∫⁻ x, ∫⁻ ξ, ρ' Λ₁ ξ * H ξ ∂((isssd (S := S) (E := E) ν Λ₁) x) ∂(γ Λ₂ η) := by
              simpa [Kernel.comap_apply, measurable_id''] using
                (Kernel.lintegral_comp ((isssd (S := S) (E := E) ν Λ₁).comap id cylinderEvents_le_pi)
                  (isssd (S := S) (E := E) ν Λ₂) η hmeas_prod)
        _ = ∫⁻ x, H x ∂(γ Λ₂ η) := by
              refine lintegral_congr_ae ?_
              filter_upwards with x
              have hinner :=
                Specification.IsProper.lintegral_mul (γ := isssd (S := S) (E := E) ν)
                  (hγ := hproper') (Λ := Λ₁) (η₀ := x)
                  (f := ρ' Λ₁) (g := H)
                  (hf := hρ'meas Λ₁) (hg := hH_meas_Λ₁c)
              have hnormx : ∫⁻ ξ, ρ' Λ₁ ξ ∂(γ Λ₁ x) = 1 := hNorm Λ₁ x
              have hinner' :
                  (∫⁻ ξ, ρ' Λ₁ ξ * H ξ ∂(γ Λ₁ x)) =
                    H x * ∫⁻ ξ, ρ' Λ₁ ξ ∂(γ Λ₁ x) := by
                have hcomm :
                    (∫⁻ ξ, ρ' Λ₁ ξ * H ξ ∂(γ Λ₁ x)) =
                      ∫⁻ ξ, H ξ * ρ' Λ₁ ξ ∂(γ Λ₁ x) := by
                  refine lintegral_congr_ae ?_
                  filter_upwards with ξ
                  simp [mul_comm]
                calc
                  (∫⁻ ξ, ρ' Λ₁ ξ * H ξ ∂(γ Λ₁ x))
                      = ∫⁻ ξ, H ξ * ρ' Λ₁ ξ ∂(γ Λ₁ x) := hcomm
                  _ = H x * ∫⁻ ξ, ρ' Λ₁ ξ ∂(γ Λ₁ x) := hinner
              calc
                ∫⁻ ξ, ρ' Λ₁ ξ * H ξ ∂(γ Λ₁ x)
                    = H x * ∫⁻ ξ, ρ' Λ₁ ξ ∂(γ Λ₁ x) := hinner'
                _ = H x * 1 := by simp [hnormx]
                _ = H x := by simp
        _ = ∫⁻ ξ, H ξ ∂(γ Λ₂ η) := by rfl
    have hH_integral :
        (∫⁻ ξ, H ξ ∂(γ Λ₂ η)) = ∫⁻ ξ in A, ρ Λ₂ ξ ∂(γ Λ₂ η) := by
      have hcons : ((isssd (S := S) (E := E) ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ
          (isssd (S := S) (E := E) ν Λ₂)) = (isssd (S := S) (E := E) ν Λ₂) :=
        (isssd (S := S) (E := E) ν).isConsistent hΛ
      have hcons_eta :
          (((isssd (S := S) (E := E) ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ
              (isssd (S := S) (E := E) ν Λ₂)) η) = (γ Λ₂ η) := by
        simpa [γ] using congrArg (fun κ => κ η) hcons
      let gA : (S → E) → ℝ≥0∞ := A.indicator fun ζ : S → E => ρ Λ₂ ζ
      have hgA : Measurable gA := Measurable.indicator hρΛ₂ hA
      calc
        (∫⁻ ξ, H ξ ∂(γ Λ₂ η))
            = ∫⁻ x, ∫⁻ ζ, gA ζ ∂(γ Λ₁ x) ∂(γ Λ₂ η) := by
                  simp [H, γ, gA, lintegral_indicator hA]
        _ = ∫⁻ ζ, gA ζ ∂(((isssd (S := S) (E := E) ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ
              (isssd (S := S) (E := E) ν Λ₂)) η) := by
              simpa [Kernel.comap_apply, measurable_id''] using
                (Kernel.lintegral_comp ((isssd (S := S) (E := E) ν Λ₁).comap id cylinderEvents_le_pi)
                  (isssd (S := S) (E := E) ν Λ₂) η hgA).symm
        _ = ∫⁻ ζ, gA ζ ∂(γ Λ₂ η) := by
              rw [hcons_eta]
        _ = ∫⁻ ξ in A, ρ Λ₂ ξ ∂(γ Λ₂ η) := by
              simp [gA, lintegral_indicator hA]

    calc
      ∫⁻ ξ, ρ Λ₂ ξ * kA ξ ∂(γ Λ₂ η)
          = ∫⁻ ξ, ρ' Λ₁ ξ * H ξ ∂(γ Λ₂ η) := hI
      _ = ∫⁻ ξ, H ξ ∂(γ Λ₂ η) := h_boundary
      _ = ∫⁻ ξ in A, ρ Λ₂ ξ ∂(γ Λ₂ η) := hH_integral

  have h_goal_integral :
      (∫⁻ ξ, ρ' Λ₂ ξ * kA ξ ∂(γ Λ₂ η)) = ∫⁻ ξ in A, ρ' Λ₂ ξ ∂(γ Λ₂ η) := by
    calc
      ∫⁻ ξ, ρ' Λ₂ ξ * kA ξ ∂(γ Λ₂ η)
          = (Z Λ₂ η)⁻¹ * ∫⁻ ξ, ρ Λ₂ ξ * kA ξ ∂(γ Λ₂ η) := hLHS_factor
      _ = (Z Λ₂ η)⁻¹ * ∫⁻ ξ in A, ρ Λ₂ ξ ∂(γ Λ₂ η) := by simp [h_noZ]
      _ = ∫⁻ ξ in A, ρ' Λ₂ ξ ∂(γ Λ₂ η) := by
            simp [hRHS_factor]
  have hLHS_eval :
      (((modificationKer (γ := (isssd (S := S) (E := E) ν)) (ρ := ρ') (hρ := hρ'meas) Λ₁).comap id
            cylinderEvents_le_pi ∘ₖ
          modificationKer (γ := (isssd (S := S) (E := E) ν)) (ρ := ρ') (hρ := hρ'meas) Λ₂)
        η) A
        =
      ∫⁻ ξ, ρ' Λ₂ ξ * kA ξ ∂(γ Λ₂ η) := by
    have hcomp :
        (((modificationKer (γ := (isssd (S := S) (E := E) ν)) (ρ := ρ') (hρ := hρ'meas) Λ₁).comap id
              cylinderEvents_le_pi ∘ₖ
            modificationKer (γ := (isssd (S := S) (E := E) ν)) (ρ := ρ') (hρ := hρ'meas) Λ₂)
          η) A
          =
        ∫⁻ x, ((modificationKer (γ := (isssd (S := S) (E := E) ν)) (ρ := ρ') (hρ := hρ'meas) Λ₁).comap id
              cylinderEvents_le_pi x) A
            ∂(modificationKer (γ := (isssd (S := S) (E := E) ν)) (ρ := ρ') (hρ := hρ'meas) Λ₂ η) := by
      simpa using
        (Kernel.comp_apply' ((modificationKer (γ := (isssd (S := S) (E := E) ν))
              (ρ := ρ') (hρ := hρ'meas) Λ₁).comap id cylinderEvents_le_pi)
          (modificationKer (γ := (isssd (S := S) (E := E) ν)) (ρ := ρ') (hρ := hρ'meas) Λ₂) η hA)
    have h_integrand :
        (fun x : S → E =>
            ((modificationKer (γ := (isssd (S := S) (E := E) ν)) (ρ := ρ') (hρ := hρ'meas) Λ₁).comap id
                  cylinderEvents_le_pi x) A)
          =
        kA := by
          funext x
          simp [kA, γ, modificationKer, Kernel.comap_apply]
    have hpush :
        (∫⁻ x, kA x ∂((modificationKer (γ := (isssd (S := S) (E := E) ν)) (ρ := ρ') (hρ := hρ'meas) Λ₂) η))
          =
        ∫⁻ x, ρ' Λ₂ x * kA x ∂(γ Λ₂ η) := by
      simpa [modificationKer, γ] using
        (lintegral_withDensity_eq_lintegral_mul (μ := γ Λ₂ η) (f := ρ' Λ₂) (h_mf := hρ'meas Λ₂)
          (g := kA) hkA_meas)
    calc
      (((modificationKer (γ := (isssd (S := S) (E := E) ν)) (ρ := ρ') (hρ := hρ'meas) Λ₁).comap id
              cylinderEvents_le_pi ∘ₖ
            modificationKer (γ := (isssd (S := S) (E := E) ν)) (ρ := ρ') (hρ := hρ'meas) Λ₂)
          η) A
          = ∫⁻ x, ((modificationKer (γ := (isssd (S := S) (E := E) ν)) (ρ := ρ') (hρ := hρ'meas) Λ₁).comap id
                cylinderEvents_le_pi x) A
              ∂(modificationKer (γ := (isssd (S := S) (E := E) ν)) (ρ := ρ') (hρ := hρ'meas) Λ₂ η) := hcomp
      _ = ∫⁻ x, kA x ∂((modificationKer (γ := (isssd (S := S) (E := E) ν)) (ρ := ρ') (hρ := hρ'meas) Λ₂) η) := by
            simp; grind
      _ = ∫⁻ ξ, ρ' Λ₂ ξ * kA ξ ∂(γ Λ₂ η) := hpush
  have hRHS_eval :
      (modificationKer (γ := (isssd (S := S) (E := E) ν)) (ρ := ρ') (hρ := hρ'meas) Λ₂ η) A
        = ∫⁻ ξ in A, ρ' Λ₂ ξ ∂(γ Λ₂ η) := by
    simp [modificationKer, withDensity_apply _ hA, γ]
  calc
    (((modificationKer (γ := (isssd (S := S) (E := E) ν)) (ρ := ρ') (hρ := hρ'meas) Λ₁).comap id
            cylinderEvents_le_pi ∘ₖ
          modificationKer (γ := (isssd (S := S) (E := E) ν)) (ρ := ρ') (hρ := hρ'meas) Λ₂)
        η) A
        = ∫⁻ ξ, ρ' Λ₂ ξ * kA ξ ∂(γ Λ₂ η) := hLHS_eval
    _ = ∫⁻ ξ in A, ρ' Λ₂ ξ ∂(γ Λ₂ η) := h_goal_integral
    _ = (modificationKer (γ := (isssd (S := S) (E := E) ν)) (ρ := ρ') (hρ := hρ'meas) Λ₂ η) A := by
          simp only [modificationKer_apply, isssd_apply, isssdFun_apply, SetLike.coe_sort_coe]; exact Eq.symm (withDensity_apply' (ρ' Λ₂) A)

end Modifier
end Specification
