import GibbsMeasure.Potential
import GibbsMeasure.Specification
import GibbsMeasure.Prereqs.Filtration.Consistent
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Measure.MeasureSpace

open ENNReal MeasureTheory
open scoped BigOperators

namespace GibbsMeasure.Examples.SpinGlass

variable {V : Type*} [DecidableEq V] [Fintype V] -- Vertices/Spins

-- Ensure Int has a measurable space
instance : MeasurableSpace Int := ⊤


/-- The Sherrington-Kirkpatrick (or Edwards-Anderson) potential.
    Φ_{ij}(σ) = - J_{ij} * σ_i * σ_j.
    (Using -J for ferromagnetic convention, or just J). -/
noncomputable def skPotential (J : V → V → ℝ) : Potential V Int :=
  fun Δ σ ↦
    -- we use a symmetric sum over ordered pairs in `Δ` and divide by 2.
    -- For `Δ = {i, j}` this equals `-J i j * σ_i * σ_j` when `J` is symmetric.
    if Δ.card = 2 then
      (1 / 2 : ℝ) *
        Finset.sum Δ (fun i =>
          Finset.sum (Δ.erase i) (fun j =>
            -((J i j) * (σ i : ℝ) * (σ j : ℝ))))
    else
      0

instance (J : V → V → ℝ) : Potential.IsFinitary (skPotential J) where
  finite_support := by
    let s : Finset (Finset V) :=
      Finset.univ.biUnion fun i ↦
        Finset.univ.map
          ⟨(fun j ↦ ({i, j} : Finset V)), by
            intro j₁ j₂ h
            have hj₁ : j₁ = i ∨ j₁ = j₂ := by
              have : j₁ ∈ ({i, j₂} : Finset V) := by
                have : j₁ ∈ ({i, j₁} : Finset V) := by simp
                simpa [h] using this
              simpa using this
            cases hj₁ with
            | inr h12 => exact h12
            | inl h1i =>
                have hj₂ : j₂ = i ∨ j₂ = j₁ := by
                  have : j₂ ∈ ({i, j₁} : Finset V) := by
                    have : j₂ ∈ ({i, j₂} : Finset V) := by simp
                    simpa [h.symm] using this
                  simpa using this
                cases hj₂ with
                | inl h2i => simp [h1i, h2i]
                | inr h21 => simpa [h1i] using h21.symm⟩
    apply Set.Finite.subset (s := (s : Set (Finset V)))
    · exact Finset.finite_toSet s
    · intro Δ hΔ
      have hne : skPotential J Δ ≠ 0 := by
        simpa [Set.mem_setOf_eq] using hΔ
      have hcard : Δ.card = 2 := by
        by_contra hcard
        have : skPotential J Δ = 0 := by
          funext σ
          simp [skPotential, hcard]
        exact hne this
      obtain ⟨i, j, hij, rfl⟩ := (Finset.card_eq_two.1 hcard)
      simp [s]

instance (J : V → V → ℝ) : Potential.IsPotential (skPotential J) where
  measurable Δ := by
    by_cases hcard : Δ.card = 2
    · let μ := cylinderEvents (X := fun _ : V ↦ Int) (Δ : Set V)
      have hcast : Measurable (fun z : Int => (z : ℝ)) := measurable_from_top
      have hmeas_apply (i : V) (hi : i ∈ Δ) :
          Measurable[μ] (fun σ : V → Int => (σ i : ℝ)) :=
        hcast.comp <|
          measurable_cylinderEvent_apply (i := i) (X := fun _ : V ↦ Int) (Δ := (Δ : Set V))
            (by exact (Finset.mem_coe.2 hi))
      have hmeas_term (i j : V) (hi : i ∈ Δ) (hj : j ∈ Δ) :
          Measurable[μ] (fun σ : V → Int => -((J i j) * (σ i : ℝ) * (σ j : ℝ))) := by
        have hi_meas := hmeas_apply i hi
        have hj_meas := hmeas_apply j hj
        have hmul : Measurable[μ] (fun σ : V → Int => (σ i : ℝ) * (σ j : ℝ)) :=
          hi_meas.mul hj_meas
        have hbase :
            Measurable[μ] (fun σ : V → Int => (J i j) * (σ i : ℝ) * (σ j : ℝ)) := by
          simpa [mul_assoc] using (measurable_const.mul hmul)
        simpa using hbase.neg
      have hmeas_inner (i : V) (hi : i ∈ Δ) :
          Measurable[μ] (fun σ : V → Int =>
              Finset.sum (Δ.erase i) (fun j =>
                -((J i j) * (σ i : ℝ) * (σ j : ℝ)))) := by
        have hmeas_sum :
            ∀ t : Finset V,
              t ⊆ Δ →
                Measurable[μ] (fun σ : V → Int =>
                  Finset.sum t (fun j =>
                    -((J i j) * (σ i : ℝ) * (σ j : ℝ)))) := by
          intro t ht
          refine Finset.induction_on t
            (motive := fun t =>
              t ⊆ Δ →
                Measurable[μ] (fun σ : V → Int =>
                  Finset.sum t (fun j =>
                    -((J i j) * (σ i : ℝ) * (σ j : ℝ)))))
            ?_ ?_ ht
          · intro _
            simp
          · intro a s ha hs ht'
            have haΔ : a ∈ Δ := ht' (by simp)
            have hs_sub : s ⊆ Δ := by
              intro x hx
              exact ht' (by simp [hx])
            have hterm := hmeas_term i a hi haΔ
            have hs_meas := hs hs_sub
            simpa [Finset.sum_insert ha] using (hterm.add hs_meas)
        refine hmeas_sum (Δ.erase i) ?_
        intro x hx
        exact Finset.mem_of_mem_erase hx
      have hmeas_outer :
          Measurable[μ] (fun σ : V → Int =>
              Finset.sum Δ (fun i =>
                Finset.sum (Δ.erase i) (fun j =>
                  -((J i j) * (σ i : ℝ) * (σ j : ℝ))))) := by
        have hmeas_sum :
            ∀ t : Finset V,
              t ⊆ Δ →
                Measurable[μ] (fun σ : V → Int =>
                  Finset.sum t (fun i =>
                    Finset.sum (Δ.erase i) (fun j =>
                      -((J i j) * (σ i : ℝ) * (σ j : ℝ))))) := by
          intro t ht
          refine Finset.induction_on t
            (motive := fun t =>
              t ⊆ Δ →
                Measurable[μ] (fun σ : V → Int =>
                  Finset.sum t (fun i =>
                    Finset.sum (Δ.erase i) (fun j =>
                      -((J i j) * (σ i : ℝ) * (σ j : ℝ))))))
            ?_ ?_ ht
          · intro _
            simp
          · intro a s ha hs ht'
            have haΔ : a ∈ Δ := ht' (by simp)
            have hs_sub : s ⊆ Δ := by
              intro x hx
              exact ht' (by simp [hx])
            have hinner_a := hmeas_inner a haΔ
            have hs_meas := hs hs_sub
            simpa [Finset.sum_insert ha] using (hinner_a.add hs_meas)
        exact hmeas_sum Δ (by intro x hx; exact hx)
      have hmeas_final :
          Measurable[μ] (fun σ : V → Int =>
              (1 / 2 : ℝ) *
                Finset.sum Δ (fun i =>
                  Finset.sum (Δ.erase i) (fun j =>
                    -((J i j) * (σ i : ℝ) * (σ j : ℝ))))) :=
        measurable_const.mul hmeas_outer
      have hrewrite :
          skPotential J Δ =
            (fun σ : V → Int =>
              (1 / 2 : ℝ) *
                Finset.sum Δ (fun i =>
                  Finset.sum (Δ.erase i) (fun j =>
                    -((J i j) * (σ i : ℝ) * (σ j : ℝ))))) := by
        funext σ
        simp [skPotential, hcard]
      simpa [hrewrite] using hmeas_final
    · have hzero : skPotential J Δ = 0 := by
        funext σ
        simp [skPotential, hcard]
      rw [hzero]
      change
        Measurable[
          cylinderEvents (X := fun _ : V ↦ Int) (Δ : Set V)
        ] (fun _ : V → Int => (0 : ℝ))
      exact measurable_const

/-- The Gibbs specification for the SK model. -/
noncomputable def skSpecification (J : V → V → ℝ) (β : ℝ) (ν : Measure Int)
    [IsProbabilityMeasure ν]
    (hZ : ∀ (Λ : Finset V) (η : V → Int),
      Specification.premodifierZ ν (Potential.boltzmannWeight (Φ := skPotential J) β) Λ η ≠ ⊤) :
    Specification V Int :=
  Potential.gibbsSpecification (skPotential J) β ν hZ


end GibbsMeasure.Examples.SpinGlass
