import GibbsMeasure.Potential
import Mathlib.Data.Finset.Union
import Mathlib.Probability.UniformOn

/-!
# Nearest-neighbor Ising model (DLR specification)

This file provides a reusable API for the nearest-neighbor ferromagnetic Ising model
within the `GibbsMeasure` (DLR/specification) library:

- a small “finite-neighbourhood system” structure `NeighborSystem`,
- the induced pair-interaction potential `isingNNPotential`,
- the associated Gibbs specification `isingNNSpecification`,
- and the predicate `IsIsingNNGibbsMeasure` for infinite-volume Gibbs states.

The goal is to let downstream developments (e.g. `SpinGlass.Papers.Triviality4D`) state results
*about the actual Ising model* while postponing the heavy probabilistic/graphical machinery
(random currents, infrared bound, etc.) to later modules.
-/

open scoped BigOperators

open MeasureTheory ProbabilityTheory ENNReal

namespace GibbsMeasure.Examples.IsingNN

universe u

variable {S : Type u} [DecidableEq S]

/-! ## Neighbour system -/

/-- A finite-neighbourhood system on a set of sites `S`. -/
structure NeighborSystem (S : Type u) where
  /-- The (finite) set of neighbors of each site. -/
  neighbors : S → Finset S
  /-- Symmetry of the neighbour relation. -/
  symm : ∀ {x y : S}, y ∈ neighbors x → x ∈ neighbors y
  /-- No self-neighbours. -/
  irrefl : ∀ x : S, x ∉ neighbors x

namespace NeighborSystem

variable (N : NeighborSystem S)

/-- The nearest-neighbour relation associated to a neighbour system. -/
def IsNN (x y : S) : Prop :=
  y ∈ N.neighbors x

instance (N : NeighborSystem S) (x y : S) : Decidable (N.IsNN x y) := by
  dsimp [NeighborSystem.IsNN]
  infer_instance

omit [DecidableEq S] in
lemma isNN_comm {x y : S} : N.IsNN x y ↔ N.IsNN y x := by
  constructor <;> intro h
  · exact N.symm h
  · exact N.symm h

omit [DecidableEq S] in
lemma isNN_irrefl (x : S) : ¬ N.IsNN x x := by
  simpa [NeighborSystem.IsNN] using N.irrefl x

omit [DecidableEq S] in
lemma IsNN.ne {x y : S} (hxy : N.IsNN x y) : x ≠ y := by
  intro h
  subst h
  exact N.isNN_irrefl x hxy

end NeighborSystem

/-! ## Spin map and Ising potential -/

/-- The standard Ising embedding `{false,true} → {−1,+1} ⊆ ℝ`. -/
def isingSpin : Bool → ℝ :=
  fun b => if b then (1 : ℝ) else (-1)

lemma measurable_isingSpin : Measurable isingSpin := by
  simpa [isingSpin] using (measurable_of_finite isingSpin)

/--
Nearest-neighbour Ising potential with coupling strength `J`.

For `Δ` of cardinality `2`, we symmetrize over ordered pairs `(x,y)` in `Δ` and divide by `2`
to obtain a canonical, order-independent two-body interaction term.
-/
noncomputable def isingNNPotential (N : NeighborSystem S) (J : ℝ) : Potential S Bool :=
  fun Δ σ ↦
    if Δ.card = 2 then
      (1 / 2 : ℝ) *
        ∑ x ∈ Δ, ∑ y ∈ Δ.erase x,
          if N.IsNN x y then
            - (J * isingSpin (σ x) * isingSpin (σ y))
          else
            0
    else
      0

namespace IsingNNPotential

variable (N : NeighborSystem S) (J : ℝ)

lemma eq_zero_of_forall_not_isNN {Δ : Finset S}
    (h : ∀ x ∈ Δ, ∀ y ∈ Δ.erase x, ¬ N.IsNN x y) :
    isingNNPotential (S := S) N J Δ = 0 := by
  classical
  funext σ
  by_cases hcard : Δ.card = 2
  · have hinner (x : S) (hx : x ∈ Δ) :
        (∑ y ∈ Δ.erase x,
            if N.IsNN x y then - (J * isingSpin (σ x) * isingSpin (σ y)) else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro y hy
      have : ¬ N.IsNN x y := h x hx y hy
      simp [this]
    have houter :
        (∑ x ∈ Δ,
            ∑ y ∈ Δ.erase x,
              if N.IsNN x y then - (J * isingSpin (σ x) * isingSpin (σ y)) else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x hx
      exact hinner x hx
    simp [isingNNPotential, hcard, houter]
  · simp [isingNNPotential, hcard]

instance : Potential.IsPotential (isingNNPotential (S := S) N J) where
  measurable Δ := by
    classical
    by_cases hcard : Δ.card = 2
    ·
      -- Work in the cylinder σ-algebra over `Δ`.
      let μ := cylinderEvents (X := fun _ : S ↦ Bool) (Δ : Set S)
      have hSpin : Measurable isingSpin := measurable_isingSpin
      have hmeas_apply (x : S) (hx : x ∈ Δ) :
          Measurable[μ] (fun σ : S → Bool => isingSpin (σ x)) :=
        hSpin.comp <|
          measurable_cylinderEvent_apply (i := x) (X := fun _ : S ↦ Bool) (Δ := (Δ : Set S))
            (by exact (Finset.mem_coe.2 hx))
      have hterm (x y : S) (hx : x ∈ Δ) (hy : y ∈ Δ) :
          Measurable[μ] (fun σ : S → Bool =>
            if N.IsNN x y then - (J * isingSpin (σ x) * isingSpin (σ y)) else 0) := by
        have hx' := hmeas_apply x hx
        have hy' := hmeas_apply y hy
        have hmul : Measurable[μ] (fun σ : S → Bool => isingSpin (σ x) * isingSpin (σ y)) :=
          hx'.mul hy'
        have hbase :
            Measurable[μ] (fun σ : S → Bool => J * isingSpin (σ x) * isingSpin (σ y)) := by
          simpa [mul_assoc] using (measurable_const.mul hmul)
        have hneg :
            Measurable[μ] (fun σ : S → Bool => - (J * isingSpin (σ x) * isingSpin (σ y))) := by
          simpa using hbase.neg
        by_cases hxy : N.IsNN x y
        · simp [hxy, hneg]
        · simp [hxy]
      have hinner (x : S) (hx : x ∈ Δ) :
          Measurable[μ] (fun σ : S → Bool =>
            ∑ y ∈ Δ.erase x,
              if N.IsNN x y then - (J * isingSpin (σ x) * isingSpin (σ y)) else 0) := by
        -- Induction with a `t ⊆ Δ` side-condition to keep terms measurable in `cylinderEvents Δ`.
        have hmeas_sum :
            ∀ t : Finset S, t ⊆ Δ →
              Measurable[μ] (fun σ : S → Bool =>
                ∑ y ∈ t,
                  if N.IsNN x y then - (J * isingSpin (σ x) * isingSpin (σ y)) else 0) := by
          intro t ht
          refine Finset.induction_on t
            (motive := fun t =>
              t ⊆ Δ →
                Measurable[μ] (fun σ : S → Bool =>
                  ∑ y ∈ t,
                    if N.IsNN x y then - (J * isingSpin (σ x) * isingSpin (σ y)) else 0))
            ?_ ?_ ht
          · intro _
            simp
          · intro a s ha hs ht'
            have haΔ : a ∈ Δ := ht' (by simp)
            have hs_sub : s ⊆ Δ := by
              intro y hy
              exact ht' (by simp [hy])
            have hterm_a : Measurable[μ] (fun σ : S → Bool =>
                if N.IsNN x a then - (J * isingSpin (σ x) * isingSpin (σ a)) else 0) :=
              hterm x a hx haΔ
            have hs_meas := hs hs_sub
            simpa [Finset.sum_insert, ha, add_assoc] using (hterm_a.add hs_meas)
        -- Apply to `t = Δ.erase x` (clearly a subset of `Δ`).
        refine hmeas_sum (Δ.erase x) ?_
        intro y hy
        exact Finset.mem_of_mem_erase hy
      have houter :
          Measurable[μ] (fun σ : S → Bool =>
            ∑ x ∈ Δ, ∑ y ∈ Δ.erase x,
              if N.IsNN x y then - (J * isingSpin (σ x) * isingSpin (σ y)) else 0) := by
        -- Same pattern as above: induct with a `t ⊆ Δ` side-condition.
        have hmeas_sum :
            ∀ t : Finset S, t ⊆ Δ →
              Measurable[μ] (fun σ : S → Bool =>
                ∑ x ∈ t, ∑ y ∈ Δ.erase x,
                  if N.IsNN x y then - (J * isingSpin (σ x) * isingSpin (σ y)) else 0) := by
          intro t ht
          refine Finset.induction_on t
            (motive := fun t =>
              t ⊆ Δ →
                Measurable[μ] (fun σ : S → Bool =>
                  ∑ x ∈ t, ∑ y ∈ Δ.erase x,
                    if N.IsNN x y then - (J * isingSpin (σ x) * isingSpin (σ y)) else 0))
            ?_ ?_ ht
          · intro _
            simp
          · intro a s ha hs ht'
            have haΔ : a ∈ Δ := ht' (by simp)
            have hs_sub : s ⊆ Δ := by
              intro x hx
              exact ht' (by simp [hx])
            have hinner_a : Measurable[μ] (fun σ : S → Bool =>
                ∑ y ∈ Δ.erase a,
                  if N.IsNN a y then - (J * isingSpin (σ a) * isingSpin (σ y)) else 0) :=
              hinner a haΔ
            have hs_meas := hs hs_sub
            simpa [Finset.sum_insert, ha, add_assoc] using (hinner_a.add hs_meas)
        exact hmeas_sum Δ (by intro x hx; exact hx)
      have hfinal :
          Measurable[μ] (fun σ : S → Bool =>
            (1 / 2 : ℝ) *
              ∑ x ∈ Δ, ∑ y ∈ Δ.erase x,
                if N.IsNN x y then - (J * isingSpin (σ x) * isingSpin (σ y)) else 0) :=
        measurable_const.mul houter
      have hrewrite :
          isingNNPotential (S := S) N J Δ =
            (fun σ : S → Bool =>
              (1 / 2 : ℝ) *
                ∑ x ∈ Δ, ∑ y ∈ Δ.erase x,
                  if N.IsNN x y then - (J * isingSpin (σ x) * isingSpin (σ y)) else 0) := by
        funext σ
        simp [isingNNPotential, hcard]
      -- Rewrite the goal using the explicit formula, then discharge measurability.
      change Measurable[μ] (isingNNPotential (S := S) N J Δ)
      rw [hrewrite]
      exact hfinal
    ·
      have hzero : isingNNPotential (S := S) N J Δ = 0 := by
        funext σ
        simp [isingNNPotential, hcard]
      -- Reduce to measurability of a constant.
      rw [hzero]
      exact measurable_const

instance : Potential.IsLocallyFinitary (isingNNPotential (S := S) N J) where
  finite_support Λ := by
    classical
    -- Supports meeting `Λ` are contained in the finite set of edges touching `Λ`.
    let supp : Finset (Finset S) :=
      Λ.biUnion fun x => (N.neighbors x).image fun y => ({x, y} : Finset S)
    refine Set.Finite.subset (s := (supp : Set (Finset S))) (Finset.finite_toSet supp) ?_
    intro Δ hΔ
    rcases hΔ with ⟨hΔΛ, hΔne0⟩
    -- If `Δ` contributes, then it must be a 2-set.
    have hcard : Δ.card = 2 := by
      by_contra hcard
      have : isingNNPotential (S := S) N J Δ = 0 := by
        funext σ
        simp [isingNNPotential, hcard]
      exact hΔne0 this
    -- Extract the two endpoints `x,y` of `Δ`.
    rcases (Finset.card_eq_two.1 hcard) with ⟨x, y, hxy, rfl⟩
    -- Pick a site in `Δ ∩ Λ`.
    rcases hΔΛ with ⟨w, hw⟩
    have hwΔ : w ∈ ({x, y} : Finset S) := by
      simpa using hw.1
    have hwΛ : w ∈ Λ := by
      simpa using hw.2
    have hw_cases : w = x ∨ w = y := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hwΔ
    have hxyNN : N.IsNN x y := by
      by_contra hnot
      have hnot' : ¬ N.IsNN y x := by
        intro hyx
        exact hnot (N.symm hyx)
      have hz :
          isingNNPotential (S := S) N J ({x, y} : Finset S) = 0 := by
        refine eq_zero_of_forall_not_isNN (S := S) (N := N) (J := J) ?_
        intro a ha b hb
        have ha' : a = x ∨ a = y := by
          simpa [Finset.mem_insert, Finset.mem_singleton] using ha
        have hb' : b = x ∨ b = y := by
          have : b ∈ ({x, y} : Finset S) := by
            exact Finset.mem_of_mem_erase hb
          simpa [Finset.mem_insert, Finset.mem_singleton] using this
        rcases ha' with hax | hay
        · subst a
          rcases hb' with hbx | hby
          · subst b
            exact (NeighborSystem.isNN_irrefl (N := N) x)
          · subst b
            exact hnot
        · subst a
          rcases hb' with hbx | hby
          · subst b
            exact hnot'
          · subst b
            exact (NeighborSystem.isNN_irrefl (N := N) y)
      exact hΔne0 hz
    -- Reduce to the case that the endpoint in `Λ` is the first argument.
    have hxΛ_or_hyΛ : x ∈ Λ ∨ y ∈ Λ := by
      rcases hw_cases with rfl | rfl <;> simp [hwΛ]
    -- Conclude membership in the finite edge set `supp`.
    have hmem : ({x, y} : Finset S) ∈ supp := by
      -- Choose the endpoint in `Λ` as the `biUnion` index.
      rcases hxΛ_or_hyΛ with hxΛ | hyΛ
      ·
        -- use `x ∈ Λ` and `y ∈ neighbors x`
        have hyN : y ∈ N.neighbors x := hxyNN
        -- unpack `biUnion` + `image`
        refine (Finset.mem_biUnion).2 ?_
        refine ⟨x, hxΛ, ?_⟩
        refine (Finset.mem_image).2 ?_
        exact ⟨y, hyN, by simp⟩
      ·
        -- use `y ∈ Λ` and `x ∈ neighbors y` (by symmetry)
        have hxN : x ∈ N.neighbors y := N.symm hxyNN
        refine (Finset.mem_biUnion).2 ?_
        refine ⟨y, hyΛ, ?_⟩
        refine (Finset.mem_image).2 ?_
        exact ⟨x, hxN, by simp [Finset.pair_comm]⟩
    simpa using hmem

end IsingNNPotential

/-! ## Specification and Gibbs measures -/

/--
The nearest-neighbour Ising Gibbs specification induced by:

- a neighbour system `N` on `S`,
- coupling strength `J`,
- inverse temperature `β`,
- and a single-site a priori measure `ν` on `Bool`.

As in `Potential.gibbsSpecification`, we require a finiteness hypothesis `hZ` ensuring the
normalizing partition function is not `⊤`.
-/
noncomputable def isingNNSpecification
    (N : NeighborSystem S) (J β : ℝ) (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hZ :
      ∀ (Λ : Finset S) (η : S → Bool),
        Specification.premodifierZ ν
            (Potential.boltzmannWeight (Φ := isingNNPotential (S := S) N J) β) Λ η ≠ ⊤) :
    Specification S Bool :=
  Potential.gibbsSpecification (isingNNPotential (S := S) N J) β ν hZ

/--
Predicate asserting that `μ` is an infinite-volume Gibbs measure for the nearest-neighbour Ising
specification determined by `N,J,β` and a priori `ν`.
-/
def IsIsingNNGibbsMeasure
    (N : NeighborSystem S) (J β : ℝ) (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hZ :
      ∀ (Λ : Finset S) (η : S → Bool),
        Specification.premodifierZ ν
            (Potential.boltzmannWeight (Φ := isingNNPotential (S := S) N J) β) Λ η ≠ ⊤)
    (μ : Measure (S → Bool)) : Prop :=
  (isingNNSpecification (S := S) N J β ν hZ).IsGibbsMeasure μ

end GibbsMeasure.Examples.IsingNN
