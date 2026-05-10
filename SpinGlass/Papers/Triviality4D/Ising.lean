import SpinGlass.GibbsMeasure.Examples.IsingNN
import SpinGlass.Lattice.Zd

/-!
# Nearest-neighbour Ising Gibbs states on `ℤ^d` (DLR/specification layer)

This file ties the paper-specific lattice `ZLattice d` to the `GibbsMeasure` DLR framework.

It provides:

- the canonical neighbour system on `ZLattice d` (from `SpinGlass.Lattice.Zd.neighbors`),
- the induced nearest-neighbour Ising specification (via `GibbsMeasure.Examples.IsingNN`),
- and a bundled predicate `IsIsingNNGibbsState` (probability measure + DLR condition).

The point is to make the theorems in `SpinGlass.Papers.Triviality4D` quantify over **actual Ising
Gibbs states** rather than arbitrary families of measures.
-/

open scoped BigOperators

open MeasureTheory ProbabilityTheory

namespace SpinGlass.Papers.Triviality4D

namespace Ising

open SpinGlass.Lattice.Zd

open GibbsMeasure.Examples.IsingNN

/-! ## A canonical single-site a priori measure -/

/-- The uniform single-site a priori measure on `Bool` (counting measure conditioned on `univ`). -/
noncomputable def prior : Measure Bool :=
  ProbabilityTheory.uniformOn (Set.univ : Set Bool)

instance : IsProbabilityMeasure (prior) := by
  simpa [prior] using (ProbabilityTheory.instIsProbabilityMeasure_uniformOn_univ (Ω := Bool))

/-- The nearest-neighbour system on `ZLattice d`. -/
noncomputable def zdNeighborSystem (d : ℕ) : NeighborSystem (ZLattice d) where
  neighbors := neighbors d
  symm := by
    intro x y hy
    have hxy : SpinGlass.Lattice.Zd.IsNN d x y := by
      simpa [SpinGlass.Lattice.Zd.IsNN] using hy
    have hyx : SpinGlass.Lattice.Zd.IsNN d y x :=
      SpinGlass.Lattice.Zd.IsNN_symm (d := d) (x := x) (y := y) hxy
    simpa [SpinGlass.Lattice.Zd.IsNN] using hyx
  irrefl := by
    intro x hx
    have hxx : SpinGlass.Lattice.Zd.IsNN d x x := by
      simpa [SpinGlass.Lattice.Zd.IsNN] using hx
    exact SpinGlass.Lattice.Zd.IsNN_irrefl (d := d) x hxx

@[simp] lemma zdNeighborSystem_neighbors (d : ℕ) (x : ZLattice d) :
    (zdNeighborSystem d).neighbors x = neighbors d x := rfl

/--
The nearest-neighbour Ising Gibbs specification on `ZLattice d`.

We keep the finiteness hypothesis `hZ : Z ≠ ⊤` explicit, matching `Potential.gibbsSpecification`.
For finite-spin systems (e.g. Ising), this can be discharged, but the proof is orthogonal to the
paper-facing layer.
-/
noncomputable def isingNNSpecification
    (d : ℕ) (J β : ℝ) (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hZ :
      ∀ (Λ : Finset (ZLattice d)) (η : ZLattice d → Bool),
        Specification.premodifierZ ν
            (Potential.boltzmannWeight
              (Φ := isingNNPotential (S := ZLattice d) (zdNeighborSystem d) J) β) Λ η ≠ ⊤) :
    Specification (ZLattice d) Bool :=
  GibbsMeasure.Examples.IsingNN.isingNNSpecification
    (S := ZLattice d) (N := zdNeighborSystem d) (J := J) (β := β) (ν := ν) hZ

/-- `μ` is a (possibly infinite-volume) Gibbs measure for the `ZLattice d` n.n. Ising specification. -/
def IsIsingNNGibbsMeasure
    (d : ℕ) (J β : ℝ) (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hZ :
      ∀ (Λ : Finset (ZLattice d)) (η : ZLattice d → Bool),
        Specification.premodifierZ ν
            (Potential.boltzmannWeight
              (Φ := isingNNPotential (S := ZLattice d) (zdNeighborSystem d) J) β) Λ η ≠ ⊤) :
    Measure (ZLattice d → Bool) → Prop :=
  GibbsMeasure.Examples.IsingNN.IsIsingNNGibbsMeasure
    (S := ZLattice d) (N := zdNeighborSystem d) (J := J) (β := β) (ν := ν) hZ

/--
Bundled “Ising Gibbs state” predicate: a probability measure satisfying the DLR equation for the
nearest-neighbour Ising specification.
-/
structure IsIsingNNGibbsState
    (d : ℕ) (J β : ℝ) (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hZ :
      ∀ (Λ : Finset (ZLattice d)) (η : ZLattice d → Bool),
        Specification.premodifierZ ν
            (Potential.boltzmannWeight
              (Φ := isingNNPotential (S := ZLattice d) (zdNeighborSystem d) J) β) Λ η ≠ ⊤)
    (μ : Measure (ZLattice d → Bool)) : Prop where
  isProb : IsProbabilityMeasure μ
  isGibbs : IsIsingNNGibbsMeasure (d := d) (J := J) (β := β) (ν := ν) hZ μ

lemma IsIsingNNGibbsState.isGibbsMeasure
    {d : ℕ} {J β : ℝ} {ν : Measure Bool} [IsProbabilityMeasure ν]
    {hZ :
      ∀ (Λ : Finset (ZLattice d)) (η : ZLattice d → Bool),
        Specification.premodifierZ ν
            (Potential.boltzmannWeight
              (Φ := isingNNPotential (S := ZLattice d) (zdNeighborSystem d) J) β) Λ η ≠ ⊤}
    {μ : Measure (ZLattice d → Bool)}
    (hμ : IsIsingNNGibbsState (d := d) (J := J) (β := β) (ν := ν) hZ μ) :
    (isingNNSpecification (d := d) (J := J) (β := β) (ν := ν) hZ).IsGibbsMeasure μ :=
  hμ.isGibbs

/-!
## Paper-specific existential finiteness witness

`Potential.gibbsSpecification` requires a finiteness witness `hZ : Z ≠ ⊤`.
For finite-spin models this should be provable, but we keep it existential at the interface level
to avoid blocking theorems on analytic bookkeeping.
-/

/-- A paper-specific “Ising Gibbs state” predicate with canonical single-site prior `prior`. -/
def IsIsingNNGibbsState'
    (d : ℕ) (J β : ℝ) (μ : Measure (ZLattice d → Bool)) : Prop :=
  IsProbabilityMeasure μ ∧
    ∃ hZ :
        ∀ (Λ : Finset (ZLattice d)) (η : ZLattice d → Bool),
          Specification.premodifierZ (prior)
              (Potential.boltzmannWeight
                (Φ := isingNNPotential (S := ZLattice d) (zdNeighborSystem d) J) β) Λ η ≠ ⊤,
      IsIsingNNGibbsMeasure (d := d) (J := J) (β := β) (ν := prior) hZ μ

end Ising

end SpinGlass.Papers.Triviality4D
