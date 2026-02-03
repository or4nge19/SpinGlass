import SpinGlass.HopfieldCascades

/-!
# Hopfield localization: statement layer (Talagrand/Bovier–Gayrard)

This file introduces **formal statement objects** for the main Hopfield localization theorems:

- Talagrand Vol I, Thm 4.3.2 (Bovier–Gayrard): concentration near the `± m* e_k` "lumps";
- Talagrand Vol II, Thm 10.3.1: concentration near the random center `c(Ξ)`.

At this stage we only build the *measurable-set / measure* infrastructure in a Vol II–friendly
kernel/law form, so later proofs can be plugged in without changing statement shapes.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal

namespace SpinGlass

section General

variable {α : Type*} [MeasurableSpace α]

/--
“Overwhelming” / “exponentially small” tail bound at scale `N`.

This is the standard Talagrand/Georgii error term shape \(K e^{-N/K}\) (up to constants).
We phrase it directly as a bound on `μ (sᶜ)`.
-/
def EssentiallySupportedExp (μ : Measure α) (N : ℕ) (s : Set α) : Prop :=
  ∃ K : ℝ, 0 < K ∧ μ sᶜ ≤ ENNReal.ofReal (K * Real.exp (-(N : ℝ) / K))

end General

section HopfieldGeometry

variable {N M : ℕ}

open scoped BigOperators

/-- Coordinate basis vector in `Fin M → ℝ`. -/
def finBasis (k : Fin M) : Fin M → ℝ :=
  fun j => if j = k then 1 else 0

/-- Center `m * e_k`. -/
def hopfieldCenter (m : ℝ) (k : Fin M) : Fin M → ℝ :=
  fun j => m * finBasis (M := M) k j

/-- Squared-radius ball using `finVecNormSq` (Euclidean \(ℓ^2\) squared). -/
def hopfieldBallSq (c : Fin M → ℝ) (ρ : ℝ) : Set (Fin M → ℝ) :=
  { z | finVecNormSq M (z - c) ≤ ρ ^ 2 }

lemma measurableSet_hopfieldBallSq (c : Fin M → ℝ) (ρ : ℝ) :
    MeasurableSet (hopfieldBallSq (M := M) c ρ) := by
  classical
  -- `finVecNormSq` is measurable, subtraction is measurable, and `≤` of a constant is measurable.
  have hsub : Measurable fun z : Fin M → ℝ => z - c := by fun_prop
  have hnorm : Measurable fun z : Fin M → ℝ => finVecNormSq M (z - c) :=
    (measurable_finVecNormSq (M := M)).comp hsub
  simpa [hopfieldBallSq] using (measurableSet_le hnorm (measurable_const : Measurable fun _ : (Fin M → ℝ) => ρ ^ 2))

/-- Union of the `2M` “lump” balls centered at `± m e_k`. -/
def hopfieldLumps (m ρ : ℝ) : Set (Fin M → ℝ) :=
  ⋃ k : Fin M, (hopfieldBallSq (M := M) (hopfieldCenter (M := M) m k) ρ)
    ∪ (hopfieldBallSq (M := M) (hopfieldCenter (M := M) (-m) k) ρ)

lemma measurableSet_hopfieldLumps (m ρ : ℝ) :
    MeasurableSet (hopfieldLumps (M := M) m ρ) := by
  classical
  -- `MeasurableSet.iUnion` works since `Fin M` is countable (in fact finite).
  refine MeasurableSet.iUnion ?_
  intro k
  exact (measurableSet_hopfieldBallSq (M := M) (c := hopfieldCenter (M := M) m k) (ρ := ρ)).union
    (measurableSet_hopfieldBallSq (M := M) (c := hopfieldCenter (M := M) (-m) k) (ρ := ρ))

end HopfieldGeometry

section HopfieldStatements

namespace Cascades

variable {N M : ℕ}

section PatternsEnvironment

variable (β h : ℝ) (k0 : Fin M)
variable (μΞ : Measure (Patterns N M)) [IsProbabilityMeasure μΞ]

/--
**Bovier–Gayrard / Talagrand Vol I (Thm 4.3.2)** statement in *annealed overlap-law* form:

the (annealed) law of a fresh overlap vector is essentially supported by the union of
balls around `± m* e_k`.

This matches the textbook quantity \( \mathbb E G_N'(A)\) by construction.
-/
def HopfieldLocalizationLumps
    (mStar ρ : ℝ) : Prop :=
  EssentiallySupportedExp
    (μ := hopfieldOverlapLawOfPatterns (N := N) (M := M) (β := β) (h := h) k0 μΞ)
    (N := N)
    (s := hopfieldLumps (M := M) mStar ρ)

/-- Pattern means \( \frac1N \sum_i η_{i,k}\) (with `η_{i,k} ∈ {±1}`), in our encoding. -/
noncomputable def hopfieldPatternMean (Ξ : Patterns N M) (k : Fin M) : ℝ :=
  (1 / (N : ℝ)) * ∑ i : Fin N, hopfieldEta (N := N) (M := M) Ξ i k

/-- Talagrand Vol II center `c(Ξ)` with components `mStar * patternMean`. -/
noncomputable def hopfieldCenterVec (mStar : ℝ) (Ξ : Patterns N M) : Fin M → ℝ :=
  fun k => mStar * hopfieldPatternMean (N := N) (M := M) Ξ k

/--
**Talagrand Vol II (Thm 10.3.1)** statement in annealed overlap-law form:

concentration of the overlap vector near the random center `c(Ξ)` (a ball in `ℝ^M`).
-/
def HopfieldLocalizationCenter
    (mStar ρ : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧
    ∫⁻ Ξ : Patterns N M,
      (hopfieldOverlapKernelOfPatterns (N := N) (M := M) (β := β) (h := h) k0) Ξ
        (hopfieldBallSq (M := M) (hopfieldCenterVec (N := N) (M := M) mStar Ξ) ρ)ᶜ
      ∂μΞ
      ≤ ENNReal.ofReal (K * Real.exp (-(N : ℝ) / K))

end PatternsEnvironment

end Cascades

end HopfieldStatements

end SpinGlass

