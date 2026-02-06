import GibbsMeasure.Specification.Structure
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Data.Set.Countable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Extremality and tail events (Georgii, Ch. 7 — first step)

This file starts the route to Georgii Thm. 7.7 (extreme points ↔ tail triviality) by proving the
easy direction: if a Gibbs measure is **not** tail-trivial, then it admits a nontrivial convex
decomposition into two Gibbs measures obtained by conditioning on a tail event.

We keep the formalization purely measure-theoretic, using only the fixed-point characterization
`μ.bind (γ Λ) = μ` and the properness of `γ` to show stability under restriction to tail events.
-/

open Set
open scoped ENNReal

namespace MeasureTheory

namespace GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

/-! ### Tail events are boundary events for every finite volume -/

lemma measurableSet_cylinderEvents_compl_of_measurableSet_tail
    (Λ : Finset S) {A : Set (S → E)} (hA : MeasurableSet[@tailSigmaAlgebra S E _] A) :
    MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] A := by
  have hle :
      (@tailSigmaAlgebra S E _ : MeasurableSpace (S → E)) ≤
        cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ) :=
    iInf_le (fun Λ : Finset S => cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) Λ
  exact hle _ hA

/-! ### Restricting a Gibbs measure to a tail event gives another Gibbs measure -/

section Restrict

variable (γ : Specification S E) [γ.IsMarkov]

omit [γ.IsMarkov] in
lemma bind_restrict_eq_of_measurableSet_boundary (hγ : γ.IsProper) (Λ : Finset S)
    {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] A)
    (μ : Measure (S → E)) :
    (μ.restrict A).bind (γ Λ) = (μ.bind (γ Λ)).restrict A := by
  classical
  ext s hs
  have hA_pi :
      MeasurableSet A :=
    (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := ((Λ : Set S)ᶜ))) _ hA
  have hker_meas : Measurable (γ Λ : (S → E) → Measure (S → E)) :=
    (ProbabilityTheory.Kernel.measurable (γ Λ)).mono
      (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := ((Λ : Set S)ᶜ))) le_rfl
  have hker_ae : AEMeasurable (γ Λ) μ := hker_meas.aemeasurable
  have hker_ae_restrict : AEMeasurable (γ Λ) (μ.restrict A) := hker_meas.aemeasurable
  have hproper :
      ∀ x : S → E, γ Λ x (s ∩ A) = A.indicator 1 x * γ Λ x s := by
    intro x
    simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
      (_root_.Specification.IsProper.inter_eq_indicator_mul (γ := γ) hγ Λ (A := s) (B := A) (η := x)
        hs hA)
  calc
    ((μ.restrict A).bind (γ Λ)) s
        = ∫⁻ x, (γ Λ x) s ∂(μ.restrict A) := by
          simp [Measure.bind_apply hs hker_ae_restrict]
    _ = ∫⁻ x in A, (γ Λ x) s ∂μ := by
          rfl
    _ = ∫⁻ x, A.indicator (fun x => (γ Λ x) s) x ∂μ := by
          simpa using (lintegral_indicator (μ := μ) hA_pi (f := fun x => (γ Λ x) s)).symm
    _ = ∫⁻ x, A.indicator 1 x * (γ Λ x) s ∂μ := by
          have hind :
              (fun x : S → E => A.indicator (fun x => (γ Λ x) s) x)
                =
              (fun x : S → E => A.indicator 1 x * (γ Λ x) s) := by
            funext x
            simpa [mul_assoc] using
              (Set.indicator_mul_left (s := A)
                (f := (1 : (S → E) → ℝ≥0∞))
                (g := fun x : S → E => (γ Λ x) s) (i := x))
          simp [hind]
    _ = ∫⁻ x, (γ Λ x) (s ∩ A) ∂μ := by
          simp [hproper]
    _ = (μ.bind (γ Λ)) (s ∩ A) := by
          simp [Measure.bind_apply (hs.inter hA_pi) hker_ae]
    _ = ((μ.bind (γ Λ)).restrict A) s := by
          simp [Measure.restrict_apply, hs, hA_pi, Set.inter_comm]

omit [γ.IsMarkov] in
lemma bind_restrict_eq_of_measurableSet_tail (hγ : γ.IsProper) (Λ : Finset S)
    {A : Set (S → E)} (hA : MeasurableSet[@tailSigmaAlgebra S E _] A)
    (μ : Measure (S → E)) :
    (μ.restrict A).bind (γ Λ) = (μ.bind (γ Λ)).restrict A := by
  exact bind_restrict_eq_of_measurableSet_boundary (γ := γ) (hγ := hγ) (Λ := Λ)
    (hA := measurableSet_cylinderEvents_compl_of_measurableSet_tail (S := S) (E := E) Λ hA) μ

/-- If `μ` is Gibbs for `γ`, then the restriction of `μ` to a tail event is also Gibbs. -/
lemma isGibbsMeasure_restrict_of_measurableSet_tail
    (hγ : γ.IsProper) {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    (hμ : _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ μ)
    {A : Set (S → E)} (hA : MeasurableSet[@tailSigmaAlgebra S E _] A) :
    _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ (μ.restrict A) := by
  have hfix : ∀ Λ : Finset S, μ.bind (γ Λ) = μ := by
    simpa [_root_.Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob (γ := γ) hγ] using hμ
  have hfix_restrict : ∀ Λ : Finset S, (μ.restrict A).bind (γ Λ) = μ.restrict A := by
    intro Λ
    calc
      (μ.restrict A).bind (γ Λ)
          = (μ.bind (γ Λ)).restrict A :=
            bind_restrict_eq_of_measurableSet_tail (γ := γ) (hγ := hγ) (Λ := Λ) (hA := hA) μ
      _ = μ.restrict A := by simp [hfix Λ]
  -- `μ.restrict A` is not a probability measure in general, so use the finite-measure fixed-point lemma.
  haveI : IsFiniteMeasure μ := by infer_instance
  haveI : IsFiniteMeasure (μ.restrict A) := by infer_instance
  exact (_root_.Specification.isGibbsMeasure_iff_forall_bind_eq (γ := γ) (μ := μ.restrict A) hγ).2 hfix_restrict

end Restrict

/-! ### From non-tail-triviality to non-extremality (Georgii Thm. 7.7, easy direction) -/

section ExtremePoints

open scoped Convex

variable (γ : Specification S E)

/-- The set `G(γ)` of Gibbs **probability** measures, viewed as a subset of `Measure (S → E)` so that
we can use Mathlib's `Set.extremePoints`. -/
def G : Set (Measure (S → E)) :=
  {μ | IsProbabilityMeasure μ ∧ _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ μ}

namespace G

variable {γ}

@[simp] lemma mem_iff (μ : Measure (S → E)) :
    μ ∈ G (γ := γ) ↔
      IsProbabilityMeasure μ ∧ _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ μ :=
  Iff.rfl

end G

section

variable {γ}
variable [γ.IsMarkov]

local notation3 "Ω" => (S → E)

lemma measurableSet_of_measurableSet_tail {A : Set Ω}
    (hA : MeasurableSet[@tailSigmaAlgebra S E _] A) : MeasurableSet A := by
  have hle_tail_pi :
      (@tailSigmaAlgebra S E _ : MeasurableSpace Ω) ≤ MeasurableSpace.pi := by
    refine le_trans
      (iInf_le (fun Λ : Finset S =>
          cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) (∅ : Finset S)) ?_
    simp
  exact hle_tail_pi _ hA

lemma bind_smul (c : ENNReal) (μ : Measure Ω) (κ : Ω → Measure Ω) (hκ : Measurable κ) :
    (c • μ).bind κ = c • (μ.bind κ) := by
  ext s hs
  simp [Measure.bind_apply hs hκ.aemeasurable, lintegral_smul_measure]

lemma bind_add (μ ν : Measure Ω) (κ : Ω → Measure Ω) (hκ : Measurable κ) :
    (μ + ν).bind κ = μ.bind κ + ν.bind κ := by
  ext s hs
  simp [Measure.bind_apply hs hκ.aemeasurable, lintegral_add_measure]

/-! ### Proper kernels commute with `withDensity` for boundary-measurable densities -/

omit [γ.IsMarkov] in
lemma withDensity_bind_eq_bind_withDensity (Λ : Finset S) (hγ : γ.IsProper)
    (μ : Measure[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] Ω)
    (f : Ω → ℝ≥0∞) (hf : Measurable[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] f) :
    (μ.bind (γ Λ)).withDensity f = (μ.withDensity f).bind (γ Λ) := by
  ext A hA
  have hf_pi : Measurable f :=
    (hf.mono (MeasureTheory.cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := ((Λ : Set S)ᶜ))) le_rfl)
  have hAem : AEMeasurable (γ Λ) μ := (ProbabilityTheory.Kernel.measurable (γ Λ)).aemeasurable
  have hAem' : AEMeasurable (fun x : Ω => A.indicator f x) (μ.bind (γ Λ)) :=
    (hf_pi.indicator hA).aemeasurable
  have hLHS :
      (∫⁻ x, A.indicator f x ∂(μ.bind (γ Λ)))
        = ∫⁻ η, f η * (γ Λ η) A ∂μ := by
    have hbind :=
      (Measure.lintegral_bind (m := μ) (μ := (γ Λ)) (f := fun x : Ω => A.indicator f x)
        hAem hAem')
    have hind :
        (fun x : Ω => A.indicator f x) = fun x => f x * A.indicator (1 : Ω → ℝ≥0∞) x := by
      funext x
      by_cases hx : x ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
    have hinner :
        (fun η : Ω => ∫⁻ x, A.indicator f x ∂(γ Λ η))
          = fun η : Ω => f η * (γ Λ η) A := by
      funext η
      have hmul :
          (∫⁻ x, f x * A.indicator (1 : Ω → ℝ≥0∞) x ∂(γ Λ η))
            =
            f η * ∫⁻ x, A.indicator (1 : Ω → ℝ≥0∞) x ∂(γ Λ η) :=
        Specification.IsProper.lintegral_mul (γ := γ) (hγ := hγ) (Λ := Λ)
          (η₀ := η)
          (f := fun x : Ω => A.indicator (1 : Ω → ℝ≥0∞) x)
          (g := f)
          (hf := (measurable_one.indicator hA))
          (hg := hf)
      have hind1 : (∫⁻ x, A.indicator (1 : Ω → ℝ≥0∞) x ∂(γ Λ η)) = (γ Λ η) A := by
        simpa using (lintegral_indicator_one (μ := (γ Λ η)) hA)
      simp [hind, hmul, hind1]
    simp [hinner] at hbind
    simpa using hbind
  calc
    ((μ.bind (γ Λ)).withDensity f) A
        = ∫⁻ x in A, f x ∂(μ.bind (γ Λ)) := by
            simpa using (withDensity_apply f (μ := μ.bind (γ Λ)) hA)
    _ = ∫⁻ x, A.indicator f x ∂(μ.bind (γ Λ)) := by
          simpa using (lintegral_indicator (μ := (μ.bind (γ Λ))) hA (f := f)).symm
    _ = ∫⁻ η, f η * (γ Λ η) A ∂μ := hLHS
    _ = ∫⁻ η, (γ Λ η) A ∂(μ.withDensity f) := by
          have hkerA :
              Measurable[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)]
                (fun η : Ω => (γ Λ η) A) :=
            (ProbabilityTheory.Kernel.measurable_coe (γ Λ) hA)
          simpa [Pi.mul_apply, mul_comm, mul_left_comm, mul_assoc] using
            (lintegral_withDensity_eq_lintegral_mul (μ := μ) (f := f) hf (g := fun η : Ω => (γ Λ η) A)
              hkerA).symm
    _ = ((μ.withDensity f).bind (γ Λ)) A := by
          simp [Measure.bind_apply hA (ProbabilityTheory.Kernel.measurable (γ Λ)).aemeasurable]

/-- Normalized restriction of a probability measure to an event `A` (as a measure). -/
noncomputable def normRestrict (μ : Measure Ω) (A : Set Ω) : Measure Ω :=
  (μ A)⁻¹ • μ.restrict A

lemma normRestrict_apply (μ : Measure Ω) (A s : Set Ω) :
    normRestrict (μ := μ) A s = (μ A)⁻¹ * (μ.restrict A) s := by
  simp [normRestrict, Measure.smul_apply, smul_eq_mul]

lemma isProbabilityMeasure_normRestrict
    (μ : Measure Ω) [IsProbabilityMeasure μ] {A : Set Ω} (hA0 : μ A ≠ 0) :
    IsProbabilityMeasure (normRestrict (μ := μ) A) := by
  haveI : IsFiniteMeasure (μ.restrict A) := by infer_instance
  have hne : μ.restrict A ≠ 0 := by
    intro h
    have : (μ.restrict A) Set.univ = 0 := by simp [h]
    have : μ A = 0 := by simpa [Measure.restrict_apply] using this
    exact hA0 this
  haveI : NeZero (μ.restrict A) := ⟨hne⟩
  haveI : IsProbabilityMeasure (((μ.restrict A) Set.univ)⁻¹ • (μ.restrict A)) := by infer_instance
  simpa [normRestrict, Measure.restrict_apply, smul_smul, smul_eq_mul] using
    (inferInstance : IsProbabilityMeasure (((μ.restrict A) Set.univ)⁻¹ • (μ.restrict A)))

lemma isGibbsMeasure_normRestrict_of_tail (hγ : γ.IsProper)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hμ : _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ μ)
    {A : Set Ω} (hA_tail : MeasurableSet[@tailSigmaAlgebra S E _] A) (hA0 : μ A ≠ 0) :
    _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ (normRestrict (μ := μ) A) := by
  -- Use the fixed-point characterization `μ.bind (γ Λ) = μ`.
  have hfix : ∀ Λ : Finset S, μ.bind (γ Λ) = μ := by
    haveI : IsFiniteMeasure μ := by infer_instance
    exact (_root_.Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob (γ := γ) hγ).1 hμ
  have hfix_restrict : ∀ Λ : Finset S, (μ.restrict A).bind (γ Λ) = μ.restrict A := by
    intro Λ
    calc
      (μ.restrict A).bind (γ Λ)
          = (μ.bind (γ Λ)).restrict A := by
              simpa using
                (bind_restrict_eq_of_measurableSet_tail (γ := γ) (hγ := hγ) (Λ := Λ) (hA := hA_tail) μ)
      _ = μ.restrict A := by simp [hfix Λ]
  have hfix_norm : ∀ Λ : Finset S,
      (normRestrict (μ := μ) A).bind (γ Λ) = normRestrict (μ := μ) A := by
    intro Λ
    have hκ : Measurable (γ Λ) :=
      (ProbabilityTheory.Kernel.measurable (γ Λ)).mono
        (MeasureTheory.cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := ((Λ : Set S)ᶜ))) le_rfl
    calc
      (normRestrict (μ := μ) A).bind (γ Λ)
          = ((μ A)⁻¹ • (μ.restrict A)).bind (γ Λ) := rfl
      _ = (μ A)⁻¹ • ((μ.restrict A).bind (γ Λ)) := by
            simpa [normRestrict] using (bind_smul (c := (μ A)⁻¹) (μ := μ.restrict A) (κ := γ Λ) hκ)
      _ = (μ A)⁻¹ • (μ.restrict A) := by simp [hfix_restrict Λ]
      _ = normRestrict (μ := μ) A := rfl
  haveI : IsFiniteMeasure (normRestrict (μ := μ) A) := by
    haveI : IsProbabilityMeasure (normRestrict (μ := μ) A) := isProbabilityMeasure_normRestrict (μ := μ) (A := A) hA0
    infer_instance
  haveI : IsProbabilityMeasure (normRestrict (μ := μ) A) :=
    isProbabilityMeasure_normRestrict (μ := μ) (A := A) hA0
  exact (_root_.Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob (γ := γ) hγ).2 hfix_norm

/-! #### Conditioning a Gibbs probability measure on a tail event stays Gibbs -/

namespace ProbabilityMeasure

/-- Normalize the restriction of a probability measure to an event with positive mass. -/
noncomputable def normRestrict (μ : ProbabilityMeasure Ω) (A : Set Ω) (hA0 : (μ : Measure Ω) A ≠ 0) :
    ProbabilityMeasure Ω :=
  ⟨MeasureTheory.GibbsMeasure.normRestrict (μ := (μ : Measure Ω)) A, by
    -- `MeasureTheory.GibbsMeasure.normRestrict` is a probability measure once we know `μ A ≠ 0`.
    haveI : IsProbabilityMeasure (μ : Measure Ω) := by infer_instance
    exact isProbabilityMeasure_normRestrict (μ := (μ : Measure Ω)) (A := A) hA0⟩

@[simp] lemma coe_normRestrict (μ : ProbabilityMeasure Ω) (A : Set Ω) (hA0 : (μ : Measure Ω) A ≠ 0) :
    ((normRestrict (μ := μ) A hA0 : ProbabilityMeasure Ω) : Measure Ω)
      =
      MeasureTheory.GibbsMeasure.normRestrict (μ := (μ : Measure Ω)) A :=
  rfl

lemma mem_GP_normRestrict_of_tail (hγ : γ.IsProper) {μ : ProbabilityMeasure Ω}
    (hμ : μ ∈ GP (S := S) (E := E) γ)
    {A : Set Ω} (hA_tail : MeasurableSet[@tailSigmaAlgebra S E _] A) (hA0 : (μ : Measure Ω) A ≠ 0) :
    normRestrict (μ := μ) A hA0 ∈ GP (S := S) (E := E) γ := by
  have hμ_gibbs : _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ (μ : Measure Ω) := hμ
  have hcond_gibbs :
      _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ
        (MeasureTheory.GibbsMeasure.normRestrict (μ := (μ : Measure Ω)) A) :=
    isGibbsMeasure_normRestrict_of_tail (γ := γ) (hγ := hγ) (μ := (μ : Measure Ω)) hμ_gibbs
      (A := A) hA_tail hA0
  exact hcond_gibbs

end ProbabilityMeasure

/-- If a Gibbs probability measure assigns a tail event probability strictly between `0` and `1`,
then it is **not** an extreme point of `G(γ)`. -/
theorem not_mem_extremePoints_G_of_tail_prob
    (hγ : γ.IsProper)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hμ : _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ μ)
    {A : Set Ω} (hA_tail : MeasurableSet[@tailSigmaAlgebra S E _] A)
    (hA0 : 0 < μ A) (hA1 : μ A < 1) :
    μ ∉ (G (γ := γ)).extremePoints ENNReal := by
  let μA : Measure Ω := normRestrict (μ := μ) A
  let μAc : Measure Ω := normRestrict (μ := μ) Aᶜ
  have hA0' : μ A ≠ 0 := ne_of_gt hA0
  have hAc0' : μ Aᶜ ≠ 0 := by
    have hA_meas : MeasurableSet A := measurableSet_of_measurableSet_tail (S := S) (E := E) hA_tail
    intro hAcompl0
    have hμA_le : μ A ≤ 1 := by
      have : μ A ≤ μ (Set.univ : Set Ω) := measure_mono (subset_univ A)
      simpa [IsProbabilityMeasure.measure_univ (μ := μ)] using this
    have hμA : μ A = 1 := by
      have hcompl : μ Aᶜ = 1 - μ A := prob_compl_eq_one_sub (μ := μ) hA_meas
      have : 1 - μ A = 0 := by simpa [hcompl] using hAcompl0
      have hge : 1 ≤ μ A := (tsub_eq_zero_iff_le).1 this
      exact le_antisymm hμA_le hge
    exact (ne_of_lt hA1) hμA
  have hμA_prob : IsProbabilityMeasure μA := isProbabilityMeasure_normRestrict (μ := μ) (A := A) hA0'
  have hμAc_prob : IsProbabilityMeasure μAc := isProbabilityMeasure_normRestrict (μ := μ) (A := Aᶜ) hAc0'
  have hμA_gibbs : _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ μA :=
    isGibbsMeasure_normRestrict_of_tail (γ := γ) (hγ := hγ) (μ := μ) hμ (A := A) hA_tail hA0'
  have hμAc_gibbs : _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ μAc := by
    have hA_tail' : MeasurableSet[@tailSigmaAlgebra S E _] Aᶜ := by
      simpa using (MeasurableSet.compl hA_tail)
    exact isGibbsMeasure_normRestrict_of_tail (γ := γ) (hγ := hγ) (μ := μ) hμ (A := Aᶜ) hA_tail' hAc0'
  have hμA_mem : μA ∈ G (γ := γ) := ⟨hμA_prob, hμA_gibbs⟩
  have hμAc_mem : μAc ∈ G (γ := γ) := ⟨hμAc_prob, hμAc_gibbs⟩
  have hμ_mem : μ ∈ G (γ := γ) := ⟨inferInstance, hμ⟩
  have hA_meas : MeasurableSet A := measurableSet_of_measurableSet_tail (S := S) (E := E) hA_tail
  have hsum : μ A + μ Aᶜ = 1 := prob_add_prob_compl (μ := μ) hA_meas
  have hseg : μ ∈ openSegment ENNReal μA μAc := by
    refine ⟨μ A, μ Aᶜ, hA0, ?_, hsum, ?_⟩
    · have : μ Aᶜ ≠ 0 := hAc0'
      exact pos_iff_ne_zero.2 this
    · have hA_ne_top : μ A ≠ ∞ := by
        have : μ A ≤ 1 := by simpa [measure_univ] using (prob_le_one)
        exact ne_top_of_le_ne_top (by simp) this
      have hAc_ne_top : μ Aᶜ ≠ ∞ := by
        have : μ Aᶜ ≤ 1 := by simpa [measure_univ] using (prob_le_one)
        exact ne_top_of_le_ne_top (by simp) this
      have hmulA : (μ A) • μA = μ.restrict A := by
        have : (μ A) * (μ A)⁻¹ = (1 : ENNReal) := by
          simpa [mul_comm] using ENNReal.inv_mul_cancel hA0' hA_ne_top
        simp [μA, normRestrict, smul_smul, this]
      have hmulAc : (μ Aᶜ) • μAc = μ.restrict Aᶜ := by
        have : (μ Aᶜ) * (μ Aᶜ)⁻¹ = (1 : ENNReal) := by
          simpa [mul_comm] using ENNReal.inv_mul_cancel hAc0' hAc_ne_top
        simp [μAc, normRestrict, smul_smul, this]
      have : (μ A) • μA + (μ Aᶜ) • μAc = μ := by
        simp [hmulA, hmulAc, Measure.restrict_add_restrict_compl hA_meas]
      simp [this]
  intro hext
  rcases (mem_extremePoints_iff_left (𝕜 := ENNReal) (A := G (γ := γ)) (x := μ)).1 hext with ⟨_hμ_in, hleft⟩
  have hEq : μA = μ := hleft μA hμA_mem μAc hμAc_mem hseg
  have hμA_A : μA A = 1 := by
    have hA_ne_top : μ A ≠ ∞ := by
      have : μ A ≤ 1 := by simpa using (prob_le_one)
      exact ne_top_of_le_ne_top (by simp) this
    calc
      μA A = (μ A)⁻¹ * (μ.restrict A) A := by
        simp [μA, normRestrict, Measure.smul_apply, smul_eq_mul]
      _ = (μ A)⁻¹ * μ A := by simp [Measure.restrict_apply hA_meas, Set.inter_self]
      _ = 1 := ENNReal.inv_mul_cancel hA0' hA_ne_top
  have : μ A = 1 := by simpa [hEq] using hμA_A
  exact (ne_of_lt hA1) this

/-- **Extreme** Gibbs probability measures are **tail-trivial** (Georgii Thm. 7.7, direction
`extreme → tail-trivial`). -/
theorem tailTrivial_of_mem_extremePoints_G
    (hγ : γ.IsProper) {μ : Measure Ω}
    (hμext : μ ∈ (G (γ := γ)).extremePoints ENNReal) :
    ∀ A, MeasurableSet[@tailSigmaAlgebra S E _] A → μ A = 0 ∨ μ A = 1 := by
  intro A hA_tail
  rcases (mem_extremePoints (𝕜 := ENNReal) (A := G (γ := γ)) (x := μ)).1 hμext with ⟨hμG, _hleft⟩
  rcases hμG with ⟨hμ_prob, hμ_gibbs⟩
  haveI : IsProbabilityMeasure μ := hμ_prob
  by_contra h
  have hne0 : μ A ≠ 0 := by
    intro h0
    exact h (Or.inl h0)
  have hne1 : μ A ≠ 1 := by
    intro h1
    exact h (Or.inr h1)
  have hpos : 0 < μ A := pos_iff_ne_zero.2 hne0
  have hle : μ A ≤ 1 := by
    have : μ A ≤ μ (Set.univ : Set Ω) := measure_mono (subset_univ A)
    simpa [IsProbabilityMeasure.measure_univ (μ := μ)] using this
  have hlt : μ A < 1 := lt_of_le_of_ne hle hne1
  exact (not_mem_extremePoints_G_of_tail_prob (γ := γ) (hγ := hγ) (μ := μ) hμ_gibbs
      (hA_tail := hA_tail) hpos hlt) hμext

/-- Probability-measure version of `tailTrivial_of_mem_extremePoints_G`. -/
theorem isTailTrivial_of_mem_extremePoints_G
    (hγ : γ.IsProper) (μ : ProbabilityMeasure Ω)
    (hμext : (μ : Measure Ω) ∈ (G (γ := γ)).extremePoints ENNReal) :
    IsTailTrivial (S := S) (E := E) μ := by
  intro A hA
  simpa using
    tailTrivial_of_mem_extremePoints_G (γ := γ) (hγ := hγ) (μ := (μ : Measure Ω)) hμext A hA

/-! ### Tail-triviality implies extremality (Georgii Thm. 7.7, hard direction) -/

section TailTrivialImpliesExtreme

open Filter

variable [Countable S]

omit [MeasurableSpace E] [Countable S] in
lemma measurable_iInf_iff {ι : Sort*} (m : ι → MeasurableSpace Ω) {X : Type*}
    [MeasurableSpace X] {f : Ω → X} :
    Measurable[iInf m] f ↔ ∀ i, Measurable[m i] f := by
  constructor
  · intro hf i
    exact hf.mono (iInf_le m i) le_rfl
  · intro hf s hs
    exact (MeasurableSpace.measurableSet_iInf (m := m) (s := f ⁻¹' s)).2 (fun i => (hf i) hs)

lemma iInf_eq_iInf_ge_of_antitone {α : Type*} [CompleteLattice α] (h : ℕ → α)
    (hh : Antitone h) (N : ℕ) :
    (⨅ n : ℕ, h n) = (⨅ n : {n // N ≤ n}, h n.1) := by
  refine le_antisymm ?_ ?_
  · refine le_iInf ?_
    intro n
    exact iInf_le (fun k : ℕ => h k) n.1
  · refine le_iInf ?_
    intro n
    by_cases hn : N ≤ n
    · simpa using (iInf_le (fun k : {k // N ≤ k} => h k.1) ⟨n, hn⟩)
    · have hNle : (⨅ k : {k // N ≤ k}, h k.1) ≤ h N := by
        simpa using (iInf_le (fun k : {k // N ≤ k} => h k.1) ⟨N, le_rfl⟩)
      have hn' : n ≤ N := le_of_not_ge hn
      have hhn : h N ≤ h n := hh hn'
      exact hNle.trans hhn

lemma antitone_iSup_ge {α : Type*} [CompleteLattice α] (g : ℕ → α) :
    Antitone (fun n : ℕ => (⨆ i : ℕ, ⨆ (_ : i ≥ n), g i)) := by
  intro a b hab
  refine iSup_le ?_
  intro i
  refine iSup_le ?_
  intro hib
  exact le_iSup_of_le i (le_iSup_of_le (le_trans hab hib) le_rfl)

omit [MeasurableSpace E] [Countable S] in
lemma measurable_limsup_of_antitone_measurableSpace
    (m : ℕ → MeasurableSpace Ω) (hm : Antitone m)
    (g : ℕ → Ω → ℝ≥0∞) (hg : ∀ n, Measurable[m n] (g n)) :
    Measurable[iInf m] (fun ω : Ω => Filter.limsup (fun n => g n ω) atTop) := by
  have himp : Measurable[iInf m] (fun ω : Ω => Filter.limsup (fun n => g n ω) atTop) ↔
      ∀ N : ℕ, Measurable[m N] (fun ω : Ω => Filter.limsup (fun n => g n ω) atTop) :=
    measurable_iInf_iff (m := m)
  refine (himp).2 ?_
  intro N
  have h_limsup :
      (fun ω : Ω => Filter.limsup (fun n => g n ω) atTop) =
        fun ω : Ω => (⨅ n : ℕ, ⨆ i : ℕ, ⨆ (_ : i ≥ n), g i ω) := by
    funext ω
    simpa using (Filter.limsup_eq_iInf_iSup_of_nat (u := fun n => g n ω))
  let h : ℕ → Ω → ℝ≥0∞ := fun n ω => ⨆ i : ℕ, ⨆ (_ : i ≥ n), g i ω
  have h_drop :
      (fun ω : Ω => (⨅ n : ℕ, h n ω)) =
        fun ω : Ω => (⨅ n : {n // N ≤ n}, h n.1 ω) := by
    funext ω
    have hhω : Antitone (fun n : ℕ => h n ω) := by
      intro a b hab
      exact antitone_iSup_ge (g := fun i => g i ω) hab
    exact iInf_eq_iInf_ge_of_antitone (h := fun n => h n ω) (hh := hhω) N
  have h_meas_h :
      ∀ n : {n // N ≤ n}, Measurable[m N] (h n.1) := by
    intro n
    have h_meas_each :
        ∀ i : {i // i ≥ n.1}, Measurable[m N] (g i.1) := by
      intro i
      have hNi : N ≤ i.1 := le_trans n.2 i.2
      have hmi : m i.1 ≤ m N := hm hNi
      exact (hg i.1).mono hmi le_rfl
    have :
        Measurable[m N] (fun ω : Ω => ⨆ i : {i // i ≥ n.1}, g i.1 ω) :=
      Measurable.iSup (f := fun i : {i // i ≥ n.1} => g i.1) h_meas_each
    simpa [h, iSup_subtype] using this
  have h_meas_drop :
      Measurable[m N] (fun ω : Ω => (⨅ n : {n // N ≤ n}, h n.1 ω)) :=
    Measurable.iInf (f := fun n : {n // N ≤ n} => h n.1) h_meas_h
  have :
      Measurable[m N] (fun ω : Ω => Filter.limsup (fun n => g n ω) atTop) := by
    simpa [h_limsup, h_drop, h] using h_meas_drop
  exact this

noncomputable def exhaustionVolumes : ℕ → Finset S := by
  classical
  by_cases hS : Nonempty S
  · exact fun n => (Finset.range n).image (Classical.choose (exists_surjective_nat S))
  · exact fun _ => ∅

lemma exhaustionVolumes_monotone :
    Monotone (exhaustionVolumes (S := S) : ℕ → Finset S) := by
  classical
  by_cases hS : Nonempty S
  · simp [exhaustionVolumes, hS]
    intro a b hab
    exact Finset.image_subset_image (Finset.range_mono hab)
  · intro a b hab
    simp [exhaustionVolumes, hS]

lemma exhaustionVolumes_cofinal (Λ : Finset S) :
    ∃ n : ℕ, Λ ⊆ exhaustionVolumes (S := S) n := by
  by_cases hS : Nonempty S
  · let f : ℕ → S := Classical.choose (exists_surjective_nat S)
    classical
    have hf : Function.Surjective f := Classical.choose_spec (exists_surjective_nat S)
    have hexh : (exhaustionVolumes (S := S) : ℕ → Finset S) = fun n => (Finset.range n).image f := by
      simp [exhaustionVolumes, hS, f]
    classical
    have : ∀ x : S, x ∈ Λ → ∃ n, f n = x := by
      intro x hx
      exact ⟨Classical.choose (hf x), Classical.choose_spec (hf x)⟩
    let ns : Finset ℕ := Λ.attach.image fun x => Classical.choose (hf x.1)
    have hns : ∀ x : S, x ∈ Λ → Classical.choose (hf x) ∈ ns := by
      intro x hx
      have : (⟨x, hx⟩ : {y // y ∈ Λ}) ∈ Λ.attach := by
        simp
      exact Finset.mem_image_of_mem _ this
    let n0 : ℕ := ns.sup id + 1
    refine ⟨n0, ?_⟩
    intro x hx
    have hx_idx : Classical.choose (hf x) < n0 := by
      have hle : Classical.choose (hf x) ≤ ns.sup id := by
        exact Finset.le_sup (f := id) (hns x hx)
      exact lt_of_le_of_lt hle (Nat.lt_succ_self _)
    have hx_mem_range : Classical.choose (hf x) ∈ Finset.range n0 := by
      simpa [Finset.mem_range] using hx_idx
    have hfx : f (Classical.choose (hf x)) = x := Classical.choose_spec (hf x)
    have : x ∈ (Finset.range n0).image f := by
      refine Finset.mem_image.2 ?_
      refine ⟨Classical.choose (hf x), hx_mem_range, ?_⟩
      simp [hfx]
    simpa [hexh] using this
  · have : Λ = ∅ := by
      classical
      simpa using (Finset.eq_empty_of_forall_notMem (s := Λ) (by
        intro x hx
        exact (hS ⟨x⟩)))
    subst this
    refine ⟨0, by simp [exhaustionVolumes, hS]⟩

lemma tailSigmaAlgebra_eq_iInf_exhaustion :
    (@tailSigmaAlgebra S E _ : MeasurableSpace Ω)
      =
      ⨅ n : ℕ,
        cylinderEvents (X := fun _ : S ↦ E) (((exhaustionVolumes (S := S) n : Finset S) : Set S)ᶜ) := by
  let m : Finset S → MeasurableSpace Ω :=
    fun Λ => cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)
  have hle :
      (⨅ Λ : Finset S, m Λ) ≤
        (⨅ n : ℕ, m (exhaustionVolumes (S := S) n)) := by
    refine le_iInf ?_
    intro n
    exact iInf_le (fun Λ : Finset S => m Λ) (exhaustionVolumes (S := S) n)
  have hge :
      (⨅ n : ℕ, m (exhaustionVolumes (S := S) n)) ≤
        (⨅ Λ : Finset S, m Λ) := by
    refine le_iInf ?_
    intro Λ
    rcases exhaustionVolumes_cofinal (S := S) (Λ := Λ) with ⟨n, hn⟩
    have hcompl : (((exhaustionVolumes (S := S) n : Finset S) : Set S)ᶜ) ⊆ ((Λ : Set S)ᶜ) := by
      intro x hx hxΛ
      exact hx (hn hxΛ)
    have hmmono : m (exhaustionVolumes (S := S) n) ≤ m Λ :=
      MeasureTheory.cylinderEvents_mono (X := fun _ : S ↦ E) (h := hcompl)
    exact (iInf_le (fun n : ℕ => m (exhaustionVolumes (S := S) n)) n).trans hmmono
  simpa [tailSigmaAlgebra, m] using le_antisymm hle hge

omit [γ.IsMarkov] [Countable S] in
lemma bind_eq_bind_trim (Λ : Finset S) (μ : Measure Ω) {A : Set Ω} (hA : MeasurableSet A) :
    (μ.trim (MeasureTheory.cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := ((Λ : Set S)ᶜ)))).bind (γ Λ) A
      =
    μ.bind (γ Λ) A := by
  have hkerA :
      Measurable[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] (fun η : Ω => (γ Λ η) A) :=
    (ProbabilityTheory.Kernel.measurable_coe (γ Λ) hA)
  have hkerA_pi : Measurable (fun η : Ω => (γ Λ η) A) :=
    hkerA.mono (MeasureTheory.cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := ((Λ : Set S)ᶜ))) le_rfl
  have hAEM : AEMeasurable (γ Λ) μ :=
    ((ProbabilityTheory.Kernel.measurable (γ Λ)).mono
        (MeasureTheory.cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := ((Λ : Set S)ᶜ))) le_rfl).aemeasurable
  have hAEM_trim : AEMeasurable (γ Λ) (μ.trim (MeasureTheory.cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := ((Λ : Set S)ᶜ)))) :=
    (ProbabilityTheory.Kernel.measurable (γ Λ)).aemeasurable
  simp [Measure.bind_apply hA hAEM, Measure.bind_apply hA hAEM_trim,
    MeasureTheory.lintegral_trim (hm := MeasureTheory.cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := ((Λ : Set S)ᶜ)))
      (f := fun η : Ω => (γ Λ η) A) hkerA]

omit [Countable S] in
lemma exists_withDensity_of_absolutelyContinuous_gibbs
    (hγ : γ.IsProper)
    {μ ν : Measure Ω}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ μ)
    (hν : _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ ν)
    (hνμ : ν ≪ μ) (Λ : Finset S) :
    ∃ g : Ω → ℝ≥0∞,
      Measurable[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] g ∧
      μ.withDensity g = ν := by
  let hm := MeasureTheory.cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := ((Λ : Set S)ᶜ))
  let μb : Measure[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] Ω := μ.trim hm
  let νb : Measure[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] Ω := ν.trim hm
  have hνbμb : νb ≪ μb := (Measure.AbsolutelyContinuous.trim (hμν := hνμ) hm)
  let g : Ω → ℝ≥0∞ := (νb.rnDeriv μb)
  have hg : Measurable[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] g :=
    Measure.measurable_rnDeriv νb μb
  haveI : IsFiniteMeasure μb := by infer_instance
  haveI : IsFiniteMeasure νb := by infer_instance
  haveI : SigmaFinite μb := by infer_instance
  haveI : SFinite νb := by infer_instance
  haveI : νb.HaveLebesgueDecomposition μb := Measure.haveLebesgueDecomposition_of_sigmaFinite νb μb
  have hμb : μb.withDensity g = νb := by
    simpa [g] using (Measure.withDensity_rnDeriv_eq (μ := νb) (ν := μb) hνbμb)
  have hbindμ : μ.bind (γ Λ) = μ := by
    have := (_root_.Specification.isGibbsMeasure_iff_forall_bind_eq (S := S) (E := E) (γ := γ) (μ := μ) hγ).1 hμ
    simpa using this Λ
  have hbindν : ν.bind (γ Λ) = ν := by
    have := (_root_.Specification.isGibbsMeasure_iff_forall_bind_eq (S := S) (E := E) (γ := γ) (μ := ν) hγ).1 hν
    simpa using this Λ
  have hμb_bind : μb.bind (γ Λ) = μ := by
    ext A hA
    have := bind_eq_bind_trim (γ := γ) (Λ := Λ) (μ := μ) (A := A) hA
    simpa [μb, hbindμ] using this
  have hνb_bind : νb.bind (γ Λ) = ν := by
    ext A hA
    have := bind_eq_bind_trim (γ := γ) (Λ := Λ) (μ := ν) (A := A) hA
    simpa [νb, hbindν] using this
  have hcomm :
      (μb.bind (γ Λ)).withDensity g = (μb.withDensity g).bind (γ Λ) :=
    withDensity_bind_eq_bind_withDensity (γ := γ) (Λ := Λ) hγ μb g hg
  refine ⟨g, hg, ?_⟩
  calc
    μ.withDensity g = (μb.bind (γ Λ)).withDensity g := by simp [hμb_bind]
    _ = (μb.withDensity g).bind (γ Λ) := hcomm
    _ = (νb).bind (γ Λ) := by simp [hμb, μb] -- `μb.withDensity g = νb`
    _ = ν := hνb_bind

lemma ae_eq_tailMeasurable_of_forall_boundary
    (hγ : γ.IsProper)
    {μ ν : Measure Ω}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ μ)
    (hν : _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ ν)
    (hνμ : ν ≪ μ) :
    ∃ g : Ω → ℝ≥0∞,
      Measurable[@tailSigmaAlgebra S E _] g ∧
      (ν.rnDeriv μ) =ᵐ[μ] g := by
  let Λn : ℕ → Finset S := exhaustionVolumes (S := S)
  have hmonoΛ : Monotone Λn := exhaustionVolumes_monotone (S := S)
  let m : ℕ → MeasurableSpace Ω :=
    fun n => cylinderEvents (X := fun _ : S ↦ E) (((Λn n : Finset S) : Set S)ᶜ)
  have hm_antitone : Antitone m := by
    intro a b hab
    have hsub : (Λn a : Set S) ⊆ (Λn b : Set S) := by
      intro x hx
      exact hmonoΛ hab hx
    have hcompl : ((Λn b : Set S)ᶜ) ⊆ ((Λn a : Set S)ᶜ) := by
      intro x hx hxa
      exact hx (hsub hxa)
    exact MeasureTheory.cylinderEvents_mono (X := fun _ : S ↦ E) (h := hcompl)
  choose g hgmeas hμg using
    fun n =>
      exists_withDensity_of_absolutelyContinuous_gibbs (S := S) (E := E) (γ := γ) hγ
        (hμ := hμ) (hν := hν) (hνμ := hνμ) (Λ := Λn n)
  have hfg : ∀ n, (ν.rnDeriv μ) =ᵐ[μ] g n := by
    intro n
    haveI : SigmaFinite μ := by
      haveI : IsFiniteMeasure μ := by infer_instance
      infer_instance
    have hνeq : ν = μ.withDensity (g n) := (hμg n).symm
    have hg_pi : Measurable (g n) :=
      (hgmeas n).mono
        (MeasureTheory.cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := ((Λn n : Set S)ᶜ))) le_rfl
    simpa [hνeq] using (Measure.rnDeriv_withDensity (ν := μ) (f := g n) hg_pi)
  let gtail : Ω → ℝ≥0∞ := fun ω => Filter.limsup (fun n => g n ω) atTop
  have hgtail_meas : Measurable[iInf m] gtail := by
    have hg' : ∀ n, Measurable[m n] (g n) := hgmeas
    exact measurable_limsup_of_antitone_measurableSpace (m := m) hm_antitone (g := g) hg'
  have htail_eq : (@tailSigmaAlgebra S E _ : MeasurableSpace Ω) = iInf m := by
    simpa [m, Λn] using (tailSigmaAlgebra_eq_iInf_exhaustion (S := S) (E := E))
  have hgtail_tail : Measurable[@tailSigmaAlgebra S E _] gtail := by
    simpa [htail_eq] using hgtail_meas
  have hpoint :
      ∀ᵐ ω ∂μ, (∀ n, g n ω = (ν.rnDeriv μ) ω) := by
    have h_event : ∀ n, ∀ᵐ ω ∂μ, g n ω = (ν.rnDeriv μ) ω := by
      intro n
      simpa [Filter.EventuallyEq] using (hfg n).symm
    exact (ae_all_iff).2 (fun n => h_event n)
  have hlimsup :
      (ν.rnDeriv μ) =ᵐ[μ] gtail := by
    filter_upwards [hpoint] with ω hω
    have : (fun n => g n ω) = fun _ : ℕ => (ν.rnDeriv μ) ω := by
      funext n; simpa using (hω n)
    simp [gtail, this]
  exact ⟨gtail, hgtail_tail, hlimsup⟩

/-- If `μ` is Gibbs and tail-trivial, then any absolutely continuous Gibbs measure equals `μ`.

This is the key analytic step in Georgii Thm. 7.7, direction `tail-trivial → extreme`. -/
theorem eq_of_absolutelyContinuous_of_isTailTrivial
    (hγ : γ.IsProper)
    {μ ν : Measure Ω}
    (hμG : _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ μ)
    (hνG : _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ ν)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμtail : IsTailTrivial (S := S) (E := E) (⟨μ, ‹IsProbabilityMeasure μ›⟩ : ProbabilityMeasure Ω))
    (hνμ : ν ≪ μ) :
    ν = μ := by
  obtain ⟨g, hg_tail, hfg⟩ :=
    ae_eq_tailMeasurable_of_forall_boundary (S := S) (E := E) (γ := γ) hγ hμG hνG hνμ
  haveI : MeasurableSpace.CountablySeparated ℝ≥0∞ := by infer_instance
  haveI : Nonempty ℝ≥0∞ := by infer_instance
  obtain ⟨c, hgc⟩ :=
    IsTailTrivial.ae_eq_const_of_measurable (S := S) (E := E)
      (μ := (⟨μ, ‹IsProbabilityMeasure μ›⟩ : ProbabilityMeasure Ω)) hμtail (f := g) hg_tail
  have hfc : (ν.rnDeriv μ) =ᵐ[μ] fun _ => c := hfg.trans hgc
  haveI : SigmaFinite μ := by
    haveI : IsFiniteMeasure μ := by infer_instance
    infer_instance
  haveI : μ.HaveLebesgueDecomposition ν := Measure.haveLebesgueDecomposition_of_sigmaFinite μ ν
  have hν_repr : μ.withDensity (ν.rnDeriv μ) = ν := by
    simpa using (Measure.withDensity_rnDeriv_eq (μ := ν) (ν := μ) hνμ)
  have hν_const : μ.withDensity (fun _ => c) = ν := by
    have : μ.withDensity (ν.rnDeriv μ) = μ.withDensity (fun _ => c) :=
      withDensity_congr_ae (μ := μ) (h := hfc)
    simpa [hν_repr] using this.symm
  have hν_smul : ν = c • μ := by
    simpa [withDensity_const (μ := μ)] using hν_const.symm
  have hmass : c = 1 := by
    have hμ1 : μ (Set.univ : Set Ω) = 1 := by simp
    have hν1 : ν (Set.univ : Set Ω) = 1 := by simp
    have : ν (Set.univ : Set Ω) = c * μ (Set.univ : Set Ω) := by
      simp [hν_smul, Measure.smul_apply, smul_eq_mul]
    simpa [hμ1, hν1] using this.symm
  simp [hmass, hν_smul]

/-- **Tail-trivial** Gibbs probability measures are **extreme** (Georgii Thm. 7.7, direction
`tail-trivial → extreme`). -/
theorem mem_extremePoints_G_of_isTailTrivial
    (hγ : γ.IsProper)
    {μ : Measure Ω}
    (hμG : μ ∈ G (γ := γ))
    (hμtail : IsTailTrivial (S := S) (E := E) (⟨μ, hμG.1⟩ : ProbabilityMeasure Ω)) :
    μ ∈ (G (γ := γ)).extremePoints ENNReal := by
  classical
  rw [mem_extremePoints_iff_left]
  refine ⟨hμG, ?_⟩
  rintro ν₁ hν₁ ν₂ hν₂ ⟨a, b, ha, hb, hab, hμeq⟩
  have hμ_prob : IsProbabilityMeasure μ := hμG.1
  haveI : IsProbabilityMeasure μ := hμ_prob
  haveI : IsProbabilityMeasure ν₁ := hν₁.1
  haveI : IsProbabilityMeasure ν₂ := hν₂.1
  have hν₁μ : ν₁ ≪ μ := by
    intro s hsμ
    have ha0 : a ≠ 0 := ne_of_gt ha
    have hμs : μ s = a * ν₁ s + b * ν₂ s := by
      have := congrArg (fun m : Measure Ω => m s) hμeq.symm
      simpa [Measure.add_apply, Measure.smul_apply, smul_eq_mul, add_assoc, add_comm, add_left_comm] using this
    have hsum0 : a * ν₁ s + b * ν₂ s = 0 := by simpa [hμs] using hsμ
    have hterm0 : a * ν₁ s = 0 := (add_eq_zero.1 hsum0).1
    rcases (mul_eq_zero.1 hterm0) with ha0' | hν₁0
    · exact (ha0 ha0').elim
    · exact hν₁0
  have hμ_gibbs : _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ μ := hμG.2
  have hν₁_gibbs : _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ ν₁ := hν₁.2
  have hEq : ν₁ = μ :=
    eq_of_absolutelyContinuous_of_isTailTrivial (S := S) (E := E) (γ := γ) (hγ := hγ)
      (μ := μ) (ν := ν₁) hμ_gibbs hν₁_gibbs (hμtail := hμtail) hν₁μ
  simp [hEq]

end TailTrivialImpliesExtreme

end

end ExtremePoints

end GibbsMeasure

end MeasureTheory
