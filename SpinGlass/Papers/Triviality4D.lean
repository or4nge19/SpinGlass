import SpinGlass.Defs
import SpinGlass.Lattice.Zd.Correlations
import SpinGlass.Lattice.Zd.Diagrams
import SpinGlass.Lattice.Zd.Scaling
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Statements from `4D_triviality_June_2021_final.tex`

This file states the main definitions and theorems specific to this paper.

Reusable definitions/layers live in:
- `SpinGlass.Lattice.Zd` (geometry on `ℤ^d`),
- `GibbsMeasure.Observables.Correlations` (model-agnostic correlations/diagrams),
- `SpinGlass.Lattice.Zd.Correlations` and `SpinGlass.Lattice.Zd.BoxDiagrams` (the `ℤ^d`-specialized adapters).
- `SpinGlass.Lattice.Zd.Scaling` (scaling observables `scalePoint`, `sigmaL`, `Tf`).
-/

open scoped BigOperators CompactlySupported

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ENNReal NNReal

namespace SpinGlass.Papers

namespace Triviality4D

open SpinGlass.Lattice.Zd
open SpinGlass.Lattice.Zd.Correlations
open SpinGlass.Lattice.Zd.BoxDiagrams

/-!
## Correlation length `ξ(β)`

The paper defines the (inverse) correlation length via an asymptotic logarithmic decay rate, e.g.
\[
\xi = \lim_{n\to\infty} -n / \log \langle \sigma_0 ; \sigma_{n e_1}\rangle.
\]

We **do not** currently encode this definition as a Lean `def` because:
- the expression involves `Real.log`, hence requires a persistent positivity hypothesis on the
  truncated two-point function along the chosen ray;
- at criticality the paper expects `ξ(βc) = ∞`, so `ℝ≥0∞` is the correct codomain for `ξ`;
- the interface file only needs `ξ` as an *external parameter* for the main theorem statements.

If/when we formalize the underlying positivity/decay hypotheses, we can introduce a robust predicate
`IsCorrelationLength` with codomain `ℝ≥0∞`.
-/

/-! ## “Generalized Gaussian process” (finite-dimensional distributions are Gaussian) -/

section GaussianProcess

variable {ι : Type*}

/--
A family `T : Test → Ω → ℝ` is a generalized Gaussian process under `P` if for every finite family
of test functions, the induced `ℝ^n`-valued random variable has a Gaussian law.

This matches the paper’s “generalized Gaussian process” conclusion in Theorem 1.1.
-/
def IsGeneralizedGaussianProcess
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Test : Type*} (T : Test → Ω → ℝ) : Prop :=
  ∀ n : ℕ, ∀ f : Fin n → Test,
    ProbabilityTheory.IsGaussian (P.map (fun ω => fun i : Fin n => T (f i) ω))

lemma IsGeneralizedGaussianProcess.isGaussian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Test : Type*} {T : Test → Ω → ℝ} (h : IsGeneralizedGaussianProcess (P := P) (T := T))
    (n : ℕ) (f : Fin n → Test) :
    ProbabilityTheory.IsGaussian (P.map (fun ω => fun i : Fin n => T (f i) ω)) :=
  h n f

end GaussianProcess

/-!
## Scaling observables `T_{f,L}` (paper Eq. (def_Tf_scaled))

These are provided by `SpinGlass.Lattice.Zd.Scaling`:
- `scalePoint` (rescaled embedding `x ↦ x/L`),
- `sigmaL` (normalization `Σ_L`),
- `Tf` (smeared field observable).
-/

/-! ## “Reachable scaling limits” and Gaussianity (paper Theorem 1.1) -/

section Phi4Gaussianity

open scoped CompactlySupported

variable {d : ℕ}

/-- The paper’s “no spontaneous magnetization / clustering” hypothesis `Φ_even` (Eq. `Phi_even`). -/
def PhiEven (μ : Measure (ZLattice d → ℝ)) (spin : ℝ → ℝ := fun x => x) : Prop :=
  Tendsto (fun x : ZLattice d => twoPoint (d := d) (spin := spin) (μ := μ) 0 x) (cocompact _)
    (𝓝 0)

variable {Ω : Type*} [MeasurableSpace Ω]

/--
Finite-dimensional convergence of the scaled observables `T_{f,L}` (paper’s notion of convergence
in distribution for the smeared field).

We phrase it using convergence of integrals against bounded continuous test functions, avoiding any
explicit mention of the `ProbabilityMeasure` topology.
-/
def HasFiniteDimensionalScalingLimit
    (μL : ℕ → Measure (ZLattice d → ℝ)) [∀ L, IsProbabilityMeasure (μL L)]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Tlim : C_c(Fin d → ℝ, ℝ) → Ω → ℝ) : Prop :=
  ∀ n : ℕ, ∀ f : Fin n → C_c(Fin d → ℝ, ℝ),
    let lawL (L : ℕ) : Measure (Fin n → ℝ) :=
      (μL L).map (fun φ => fun i : Fin n =>
        Tf (d := d) (S := ℝ) (spin := (fun x : ℝ => x)) (μ := μL L) (f := f i) L φ)
    let law : Measure (Fin n → ℝ) :=
      P.map (fun ω => fun i : Fin n => Tlim (f i) ω)
    ∀ g : BoundedContinuousFunction (Fin n → ℝ) ℝ,
      Tendsto (fun L : ℕ => ∫ x, g x ∂(lawL L)) atTop (𝓝 (∫ x, g x ∂law))

lemma HasFiniteDimensionalScalingLimit.tendsto_integral
    (μL : ℕ → Measure (ZLattice d → ℝ)) [∀ L, IsProbabilityMeasure (μL L)]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Tlim : C_c(Fin d → ℝ, ℝ) → Ω → ℝ)
    (h : HasFiniteDimensionalScalingLimit (d := d) (Ω := Ω) μL P Tlim)
    (n : ℕ) (f : Fin n → C_c(Fin d → ℝ, ℝ)) (g : BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    let lawL (L : ℕ) : Measure (Fin n → ℝ) :=
      (μL L).map (fun φ => fun i : Fin n =>
        Tf (d := d) (S := ℝ) (spin := (fun x : ℝ => x)) (μ := μL L) (f := f i) L φ)
    let law : Measure (Fin n → ℝ) :=
      P.map (fun ω => fun i : Fin n => Tlim (f i) ω)
    Tendsto (fun L : ℕ => ∫ x, g x ∂(lawL L)) atTop (𝓝 (∫ x, g x ∂law)) := by
  simpa [HasFiniteDimensionalScalingLimit] using (h n f g)

/--
**Gaussianity of `Φ⁴₄`** (paper Theorem 1.1, qualitative interface statement).

We state the conclusion as “finite-dimensional marginals of the limit field are Gaussian”.
-/
theorem Gaussianity_phi4_4D
    {Ω : Type*} [MeasurableSpace Ω]
    (μL : ℕ → Measure (Z4 → ℝ)) [∀ L, IsProbabilityMeasure (μL L)]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Tlim : C_c(Fin 4 → ℝ, ℝ) → Ω → ℝ)
    (hPhiEven : ∀ L : ℕ, PhiEven (d := 4) (μ := μL L)) :
    HasFiniteDimensionalScalingLimit (d := 4) (Ω := Ω) μL P Tlim →
    IsGeneralizedGaussianProcess (P := P) (T := Tlim) := by
  sorry

end Phi4Gaussianity

/-! ## Statements of the paper’s main theorems -/

section Statements

/-! ### Theorem 1.2 (Improved tree diagram bound, Ising, d=4) -/

/--
**Theorem (Improved tree diagram bound inequality)** (paper Theorem 1.2 / Theorem 1.3 in the TeX).
-/
theorem ImprovedTreeDiagramBound_Ising4
    (μβ : ℝ → Measure (Z4 → Bool))
    (βc : ℝ) (ξ : ℝ → ℝ≥0∞) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ β : ℝ, β ≤ βc →
        IsProbabilityMeasure (μβ β) →
        (∀ u v : Z4,
          0 ≤ twoPoint (d := 4) (spin := SpinGlass.isingSpin) (μ := μβ β) u v) →
        ∀ L : ℕ, (L : ℝ≥0∞) ≤ ξ β →
          0 < bubbleRaw (d := 4) (spin := SpinGlass.isingSpin) (μ := μβ β) L →
          ∀ x y z t : Z4, pairwiseFar 4 L x y z t →
            ENNReal.ofReal (|ursell4 (d := 4) (spin := SpinGlass.isingSpin) (μ := μβ β) x y z t|)
              ≤ ENNReal.ofReal (C / (bubbleRaw (d := 4) (spin := SpinGlass.isingSpin) (μ := μβ β) L) ^ c) *
                  (∑' u : Z4,
                    ENNReal.ofReal
                      (twoPoint (d := 4) (spin := SpinGlass.isingSpin) (μ := μβ β) u x *
                        twoPoint (d := 4) (spin := SpinGlass.isingSpin) (μ := μβ β) u y *
                        twoPoint (d := 4) (spin := SpinGlass.isingSpin) (μ := μβ β) u z *
                        twoPoint (d := 4) (spin := SpinGlass.isingSpin) (μ := μβ β) u t)) := by
  sorry

/-! ### Proposition 1.3 (quantitative Gaussian characteristic-function bound, Ising) -/

/-- Diameter of the (topological) support of a compactly supported test function. -/
noncomputable def supportDiameter {d : ℕ} (f : C_c(Fin d → ℝ, ℝ)) : ℝ :=
  Metric.diam (tsupport (f : (Fin d → ℝ) → ℝ))

lemma supportDiameter_nonneg {d : ℕ} (f : C_c(Fin d → ℝ, ℝ)) : 0 ≤ supportDiameter f := by
  unfold supportDiameter
  simpa using (Metric.diam_nonneg (s := tsupport (f : (Fin d → ℝ) → ℝ)))

/--
**Proposition (Gaussian characteristic-function bound)** (paper Proposition `prop:gaussian b`).
-/
theorem gaussianCharFnBound_Ising4
    (μβ : ℝ → Measure (Z4 → Bool)) (βc : ℝ) (ξ : ℝ → ℝ≥0∞) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ β : ℝ, β ≤ βc →
        IsProbabilityMeasure (μβ β) →
        ∀ L : ℕ, (L : ℝ≥0∞) ≤ ξ β →
          (2 ≤ L) →
          ∀ f : C_c(Fin 4 → ℝ, ℝ),
            ∀ M : ℝ, (∀ x : Fin 4 → ℝ, |f x| ≤ M) →
            ∀ z : ℝ,
              |(μβ β)[fun σ =>
                    Real.exp
                      (z * Tf (d := 4) (S := Bool) (spin := SpinGlass.isingSpin) (μ := μβ β) (f := f) L σ
                        - (z ^ (2 : ℕ)) / 2 *
                            (μβ β)[fun σ' =>
                              (Tf (d := 4) (S := Bool) (spin := SpinGlass.isingSpin) (μ := μβ β)
                                    (f := f) L σ') ^ (2 : ℕ)])]
                  - 1| ≤
                (C * (M ^ (4 : ℕ)) * (supportDiameter f) ^ (12 : ℕ)) /
                    (Real.log (L : ℝ)) ^ c * z ^ (4 : ℕ) := by
  sorry

/-! ### Theorem 6.1 (Improved tree diagram bound for the GS class, d=4) -/

/--
**Theorem (Improved tree diagram bound for the GS class)** (paper Theorem 6.1).
-/
theorem ImprovedTreeDiagramBound_GS4
    (J : ℝ) (μβ : ℝ → Measure (Z4 → ℝ))
    (βc : ℝ) (ξ : ℝ → ℝ≥0∞) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ β : ℝ, β ≤ βc →
        IsProbabilityMeasure (μβ β) →
        0 ≤ β →
        0 ≤ J →
        (∀ u v : Z4, 0 ≤ twoPoint (d := 4) (spin := (fun x : ℝ => x)) (μ := μβ β) u v) →
        ∀ L : ℕ, (L : ℝ≥0∞) ≤ ξ β →
          0 < twoPoint (d := 4) (spin := (fun x : ℝ => x)) (μ := μβ β) 0 0 →
          0 < bubble (d := 4) (spin := (fun x : ℝ => x)) (μ := μβ β) L →
          ∀ x y z t : Z4, pairwiseFar 4 L x y z t →
            ENNReal.ofReal (|ursell4 (d := 4) (spin := (fun x : ℝ => x)) (μ := μβ β) x y z t|)
              ≤ ENNReal.ofReal
                  (C * ((twoPoint (d := 4) (spin := (fun x : ℝ => x)) (μ := μβ β) 0 0) /
                    (bubble (d := 4) (spin := (fun x : ℝ => x)) (μ := μβ β) L)) ^ c) *
                  (∑' u : Z4,
                    ENNReal.ofReal
                      (twoPoint (d := 4) (spin := (fun x : ℝ => x)) (μ := μβ β) x u *
                        twoPoint (d := 4) (spin := (fun x : ℝ => x)) (μ := μβ β) z u) *
                      (Finset.sum (neighbors 4 u) fun u' =>
                        ENNReal.ofReal
                          ((β * J) *
                            twoPoint (d := 4) (spin := (fun x : ℝ => x)) (μ := μβ β) u' y)) *
                      (Finset.sum (neighbors 4 u) fun u'' =>
                        ENNReal.ofReal
                          ((β * J) *
                            twoPoint (d := 4) (spin := (fun x : ℝ => x)) (μ := μβ β) u'' t))) := by
  sorry

end Statements

end Triviality4D

end SpinGlass.Papers
