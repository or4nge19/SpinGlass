import GibbsMeasure.Potential
import SpinGlass.Papers.Triviality4D.GSClass
import SpinGlass.Papers.Triviality4D.Ising

/-!
# Nearest-neighbour ferromagnetic models with single-site law in the GS class

This file defines a concrete `GibbsMeasure.Specification` for a nearest-neighbour *quadratic* pair
interaction on `ZLattice d` with real-valued spins and a given single-site a priori measure `ρ`.

It then provides the corresponding “Gibbs state” predicate and ties it to the GS class predicate
(`SpinGlass.Papers.Triviality4D.GSClass.IsGSClass`).

The GS-class theorem statements should quantify over measures that are *actually* Gibbs measures
for a ferromagnetic n.n. model, not over arbitrary probability measures on fields.
-/

open scoped BigOperators

open MeasureTheory ProbabilityTheory

namespace SpinGlass.Papers.Triviality4D

namespace GSModel

open SpinGlass.Lattice.Zd
open GibbsMeasure

/--
Nearest-neighbour quadratic pair potential on `ZLattice d`:

For `Δ = {x,y}` a neighbour pair, `Φ Δ η = - J * η x * η y`, otherwise `0`.
We write it using the symmetric “sum over ordered pairs / 2” normalization, matching the Ising
example and avoiding any dependence on an ordering of `{x,y}`.
-/
noncomputable def nnQuadraticPotential (d : ℕ) (J : ℝ) : Potential (ZLattice d) ℝ :=
  fun Δ η ↦
    if Δ.card = 2 then
      (1 / 2 : ℝ) *
        ∑ x ∈ Δ, ∑ y ∈ Δ.erase x,
          if (Ising.zdNeighborSystem d).IsNN x y then
            - (J * (η x) * (η y))
          else
            0
    else
      0

namespace nnQuadraticPotential

variable {d : ℕ} (J : ℝ)

instance : Potential.IsPotential (nnQuadraticPotential (d := d) J) where
  measurable Δ := by
    classical
    by_cases hcard : Δ.card = 2
    · let μ := cylinderEvents (X := fun _ : ZLattice d ↦ ℝ) (Δ : Set (ZLattice d))
      have hmeas_apply (x : ZLattice d) (hx : x ∈ Δ) :
          Measurable[μ] (fun η : ZLattice d → ℝ => η x) :=
        measurable_cylinderEvent_apply (i := x) (X := fun _ : ZLattice d ↦ ℝ) (Δ := (Δ : Set (ZLattice d)))
          (by exact (Finset.mem_coe.2 hx))
      have hterm (x y : ZLattice d) (hx : x ∈ Δ) (hy : y ∈ Δ) :
          Measurable[μ] (fun η : ZLattice d → ℝ =>
            if (Ising.zdNeighborSystem d).IsNN x y then - (J * (η x) * (η y)) else 0) := by
        have hx' := hmeas_apply x hx
        have hy' := hmeas_apply y hy
        have hmul : Measurable[μ] (fun η : ZLattice d → ℝ => (η x) * (η y)) :=
          hx'.mul hy'
        have hbase :
            Measurable[μ] (fun η : ZLattice d → ℝ => J * (η x) * (η y)) := by
          simpa [mul_assoc] using (measurable_const.mul hmul)
        have hneg :
            Measurable[μ] (fun η : ZLattice d → ℝ => - (J * (η x) * (η y))) := by
          simpa using hbase.neg
        by_cases hxy : (Ising.zdNeighborSystem d).IsNN x y
        · simp [hxy, hneg]
        · simp [hxy]
      have hinner (x : ZLattice d) (hx : x ∈ Δ) :
          Measurable[μ] (fun η : ZLattice d → ℝ =>
            ∑ y ∈ Δ.erase x,
              if (Ising.zdNeighborSystem d).IsNN x y then - (J * (η x) * (η y)) else 0) := by
        have hmeas_sum :
            ∀ t : Finset (ZLattice d), t ⊆ Δ →
              Measurable[μ] (fun η : ZLattice d → ℝ =>
                ∑ y ∈ t,
                  if (Ising.zdNeighborSystem d).IsNN x y then - (J * (η x) * (η y)) else 0) := by
          intro t ht
          refine Finset.induction_on t
            (motive := fun t =>
              t ⊆ Δ →
                Measurable[μ] (fun η : ZLattice d → ℝ =>
                  ∑ y ∈ t,
                    if (Ising.zdNeighborSystem d).IsNN x y then - (J * (η x) * (η y)) else 0))
            ?_ ?_ ht
          · intro _
            simp
          · intro a s ha hs ht'
            have haΔ : a ∈ Δ := ht' (by simp)
            have hs_sub : s ⊆ Δ := by
              intro y hy
              exact ht' (by simp [hy])
            have hterm_a :
                Measurable[μ] (fun η : ZLattice d → ℝ =>
                  if (Ising.zdNeighborSystem d).IsNN x a then - (J * (η x) * (η a)) else 0) :=
              hterm x a hx haΔ
            have hs_meas := hs hs_sub
            simpa [Finset.sum_insert, ha, add_assoc] using (hterm_a.add hs_meas)
        refine hmeas_sum (Δ.erase x) ?_
        intro y hy
        exact Finset.mem_of_mem_erase hy
      have houter :
          Measurable[μ] (fun η : ZLattice d → ℝ =>
            ∑ x ∈ Δ, ∑ y ∈ Δ.erase x,
              if (Ising.zdNeighborSystem d).IsNN x y then - (J * (η x) * (η y)) else 0) := by
        have hmeas_sum :
            ∀ t : Finset (ZLattice d), t ⊆ Δ →
              Measurable[μ] (fun η : ZLattice d → ℝ =>
                ∑ x ∈ t, ∑ y ∈ Δ.erase x,
                  if (Ising.zdNeighborSystem d).IsNN x y then - (J * (η x) * (η y)) else 0) := by
          intro t ht
          refine Finset.induction_on t
            (motive := fun t =>
              t ⊆ Δ →
                Measurable[μ] (fun η : ZLattice d → ℝ =>
                  ∑ x ∈ t, ∑ y ∈ Δ.erase x,
                    if (Ising.zdNeighborSystem d).IsNN x y then - (J * (η x) * (η y)) else 0))
            ?_ ?_ ht
          · intro _
            simp
          · intro a s ha hs ht'
            have haΔ : a ∈ Δ := ht' (by simp)
            have hs_sub : s ⊆ Δ := by
              intro x hx
              exact ht' (by simp [hx])
            have hinner_a :
                Measurable[μ] (fun η : ZLattice d → ℝ =>
                  ∑ y ∈ Δ.erase a,
                    if (Ising.zdNeighborSystem d).IsNN a y then - (J * (η a) * (η y)) else 0) :=
              hinner a haΔ
            have hs_meas := hs hs_sub
            simpa [Finset.sum_insert, ha, add_assoc] using (hinner_a.add hs_meas)
        exact hmeas_sum Δ (by intro x hx; exact hx)
      have hfinal :
          Measurable[μ] (fun η : ZLattice d → ℝ =>
            (1 / 2 : ℝ) *
              ∑ x ∈ Δ, ∑ y ∈ Δ.erase x,
                if (Ising.zdNeighborSystem d).IsNN x y then - (J * (η x) * (η y)) else 0) :=
        measurable_const.mul houter
      have hrewrite :
          nnQuadraticPotential (d := d) J Δ =
            (fun η : ZLattice d → ℝ =>
              (1 / 2 : ℝ) *
                ∑ x ∈ Δ, ∑ y ∈ Δ.erase x,
                  if (Ising.zdNeighborSystem d).IsNN x y then - (J * (η x) * (η y)) else 0) := by
        funext η
        simp [nnQuadraticPotential, hcard]
      change Measurable[μ] (nnQuadraticPotential (d := d) J Δ)
      rw [hrewrite]
      exact hfinal
    · have hzero : nnQuadraticPotential (d := d) J Δ = 0 := by
        funext η
        simp [nnQuadraticPotential, hcard]
      rw [hzero]
      exact measurable_const

instance : Potential.IsLocallyFinitary (nnQuadraticPotential (d := d) J) where
  finite_support Λ := by
    classical
    let supp : Finset (Finset (ZLattice d)) :=
      Λ.biUnion fun x =>
        (neighbors d x).image fun y => ({x, y} : Finset (ZLattice d))
    refine Set.Finite.subset (s := (supp : Set (Finset (ZLattice d)))) (Finset.finite_toSet supp) ?_
    intro Δ hΔ
    rcases hΔ with ⟨hΔΛ, hΔne0⟩
    have hcard : Δ.card = 2 := by
      by_contra hcard
      have : nnQuadraticPotential (d := d) J Δ = 0 := by
        funext η
        simp [nnQuadraticPotential, hcard]
      exact hΔne0 this
    rcases (Finset.card_eq_two.1 hcard) with ⟨x, y, hxy, rfl⟩
    rcases hΔΛ with ⟨w, hw⟩
    have hwΔ : w ∈ ({x, y} : Finset (ZLattice d)) := by
      simpa using hw.1
    have hwΛ : w ∈ Λ := by
      simpa using hw.2
    have hw_cases : w = x ∨ w = y := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hwΔ
    have hxyNN : (Ising.zdNeighborSystem d).IsNN x y := by
      by_contra hnot
      have hz : nnQuadraticPotential (d := d) J ({x, y} : Finset (ZLattice d)) = 0 := by
        funext η
        have hnot' : ¬ (Ising.zdNeighborSystem d).IsNN y x := by
          intro hyx
          exact hnot ((Ising.zdNeighborSystem d).isNN_comm.1 hyx)
        simp [nnQuadraticPotential, hcard, hnot, hnot', Finset.sum_insert, Finset.sum_singleton, hxy]
      exact hΔne0 hz
    have hxΛ_or_hyΛ : x ∈ Λ ∨ y ∈ Λ := by
      rcases hw_cases with rfl | rfl <;> simp [hwΛ]
    have hmem : ({x, y} : Finset (ZLattice d)) ∈ supp := by
      rcases hxΛ_or_hyΛ with hxΛ | hyΛ
      · have hyN : y ∈ neighbors d x := by
          simpa [GibbsMeasure.Examples.IsingNN.NeighborSystem.IsNN, Ising.zdNeighborSystem] using hxyNN
        refine (Finset.mem_biUnion).2 ?_
        refine ⟨x, hxΛ, ?_⟩
        refine (Finset.mem_image).2 ?_
        exact ⟨y, hyN, by simp⟩
      · have hxN : x ∈ neighbors d y := by
          have : (Ising.zdNeighborSystem d).IsNN y x :=
            (Ising.zdNeighborSystem d).isNN_comm.1 hxyNN
          simpa [GibbsMeasure.Examples.IsingNN.NeighborSystem.IsNN, Ising.zdNeighborSystem] using this
        refine (Finset.mem_biUnion).2 ?_
        refine ⟨y, hyΛ, ?_⟩
        refine (Finset.mem_image).2 ?_
        exact ⟨x, hxN, by simp [Finset.pair_comm]⟩
    simpa using hmem

end nnQuadraticPotential

/--
Nearest-neighbour quadratic Gibbs specification on `ZLattice d` with prior `ρ` and coupling `J`.

The finiteness hypothesis `hZ : Z ≠ ⊤` is kept explicit.
-/
noncomputable def nnQuadraticSpecification
    (d : ℕ) (J β : ℝ) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hZ :
      ∀ (Λ : Finset (ZLattice d)) (η : ZLattice d → ℝ),
        Specification.premodifierZ ρ
            (Potential.boltzmannWeight (Φ := nnQuadraticPotential (d := d) J) β) Λ η ≠ ⊤) :
    Specification (ZLattice d) ℝ :=
  Potential.gibbsSpecification (nnQuadraticPotential (d := d) J) β ρ hZ

/-- A paper-specific Gibbs-state predicate (probability + DLR) for the n.n. quadratic model. -/
def IsNNQuadraticGibbsState
    (d : ℕ) (J β : ℝ) (ρ : ProbabilityMeasure ℝ) (μ : Measure (ZLattice d → ℝ)) : Prop :=
  IsProbabilityMeasure μ ∧
    ∃ hZ :
        ∀ (Λ : Finset (ZLattice d)) (η : ZLattice d → ℝ),
          Specification.premodifierZ (ρ : Measure ℝ)
              (Potential.boltzmannWeight (Φ := nnQuadraticPotential (d := d) J) β) Λ η ≠ ⊤,
      (nnQuadraticSpecification (d := d) (J := J) (β := β) (ρ := (ρ : Measure ℝ)) hZ).IsGibbsMeasure μ

/--
“Model in the GS class on `ZLattice d`”: a Gibbs state for the n.n. quadratic interaction with a
single-site prior `ρ` that is in the GS class.

This is the minimal concrete predicate needed to de-vacuify Theorem 6.1 statements.
-/
def IsGSNNQuadraticModel
    (d : ℕ) (J β : ℝ) (ρ : ProbabilityMeasure ℝ) (μ : Measure (ZLattice d → ℝ)) : Prop :=
  GSClass.IsGSClass ρ ∧ IsNNQuadraticGibbsState (d := d) (J := J) (β := β) ρ μ

end GSModel

end SpinGlass.Papers.Triviality4D
