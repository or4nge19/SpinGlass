import SpinGlass.Defs
import SpinGlass.Lattice.Zd.Correlations
import SpinGlass.Lattice.Zd.Diagrams
import SpinGlass.Lattice.Zd.Scaling
import SpinGlass.Papers.Triviality4D.Ising
import SpinGlass.Papers.Triviality4D.GSClass
import SpinGlass.Papers.Triviality4D.GSModel
import SpinGlass.Papers.Triviality4D.InfraredBound
import SpinGlass.Papers.Triviality4D.CorrelationLength
import SpinGlass.Papers.Triviality4D.RandomCurrentSwitching
import SpinGlass.Papers.Triviality4D.RandomCurrentConsequences
import SpinGlass.Papers.Triviality4D.RandomCurrentUrsell4
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

## Roadmap / formalization status

This file states the paper’s main theorems and supplies
the reusable algebraic/scaling API needed to *prove* them.  We have started to de-vacuify the
statements by introducing concrete model predicates:

- `SpinGlass.Papers.Triviality4D.Ising`: nearest-neighbour Ising DLR specification/Gibbs-state predicate.
- `SpinGlass.Papers.Triviality4D.GSClass`: Definition 2.1 (GS class) on single-site laws `ρ : ProbabilityMeasure ℝ`.
- `SpinGlass.Papers.Triviality4D.GSModel`: a concrete n.n. quadratic Gibbs specification on `ZLattice d`
  with prior `ρ`, plus the predicate “model in the GS class”.
- `SpinGlass.Papers.Triviality4D.RandomCurrent`: the combinatorial objects of random currents (finite volume).
- `SpinGlass.Papers.Triviality4D.InfraredBound`: paper-specific predicates for x-space infrared bounds.

What is still missing are the core theorems connecting these layers:

- existence/uniqueness/translation invariance of infinite-volume Gibbs states and the critical point `βc`,
- reflection positivity and the (sliding-scale) infrared bound proofs (Section 3),
- the **infinite-volume limit** of the finite-volume Ursell-4 random current identity (Eq. (U4), now in
  `SpinGlass.Papers.Triviality4D.RandomCurrentUrsell4`) and higher cumulant identities,
- the **mixing** and **intersection-clustering** bounds (Section 4).
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

We encode this as a **predicate** `IsCorrelationLength` (see `SpinGlass.Papers.Triviality4D.CorrelationLength`),
with codomain `ℝ≥0∞` to allow the critical case `ξ(βc) = ∞`. The predicate makes the required
positivity assumptions explicit (eventually `0 < ⟨σ_0;σ_{n e₁}⟩ < 1`) and states convergence of the
paper’s expression in `ℝ≥0∞`.  The same file also provides a definition-level object `corrLenLimsup`
(`limsup` of the paper’s terms) and a lemma `IsCorrelationLength.corrLenLimsup_eq` identifying it
with the claimed limit when convergence holds.
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
  (∀ f : Test, Measurable (T f)) ∧
    ∀ n : ℕ, ∀ f : Fin n → Test,
      ProbabilityTheory.IsGaussian (P.map (fun ω => fun i : Fin n => T (f i) ω))

lemma IsGeneralizedGaussianProcess.isGaussian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Test : Type*} {T : Test → Ω → ℝ} (h : IsGeneralizedGaussianProcess (P := P) (T := T))
    (n : ℕ) (f : Fin n → Test) :
    ProbabilityTheory.IsGaussian (P.map (fun ω => fun i : Fin n => T (f i) ω)) :=
  h.2 n f

lemma IsGeneralizedGaussianProcess.measurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Test : Type*} {T : Test → Ω → ℝ} (h : IsGeneralizedGaussianProcess (P := P) (T := T))
    (f : Test) :
    Measurable (T f) :=
  h.1 f

lemma IsGeneralizedGaussianProcess.measurable_vec
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Test : Type*} {T : Test → Ω → ℝ} (h : IsGeneralizedGaussianProcess (P := P) (T := T))
    (n : ℕ) (f : Fin n → Test) :
    Measurable (fun ω : Ω => fun i : Fin n => T (f i) ω) := by
  refine (measurable_pi_iff).2 ?_
  intro i
  simpa using h.measurable (f i)

lemma IsGeneralizedGaussianProcess.isProbabilityMeasure_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Test : Type*} {T : Test → Ω → ℝ} (h : IsGeneralizedGaussianProcess (P := P) (T := T))
    (n : ℕ) (f : Fin n → Test) :
    IsProbabilityMeasure (P.map (fun ω : Ω => fun i : Fin n => T (f i) ω)) := by
  have hω : Measurable (fun ω : Ω => fun i : Fin n => T (f i) ω) :=
    h.measurable_vec (n := n) f
  exact Measure.isProbabilityMeasure_map (μ := P) hω.aemeasurable

lemma IsGeneralizedGaussianProcess.map_eq_gaussianReal
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Test : Type*} {T : Test → Ω → ℝ} (h : IsGeneralizedGaussianProcess (P := P) (T := T))
    (n : ℕ) (f : Fin n → Test) (L : StrongDual ℝ (Fin n → ℝ)) :
    (P.map (fun ω : Ω => fun i : Fin n => T (f i) ω)).map L
      =
      gaussianReal (∫ x, L x ∂(P.map (fun ω : Ω => fun i : Fin n => T (f i) ω)))
        (Var[⇑L; P.map (fun ω : Ω => fun i : Fin n => T (f i) ω)]).toNNReal := by
  letI : ProbabilityTheory.IsGaussian (P.map (fun ω : Ω => fun i : Fin n => T (f i) ω)) :=
    h.isGaussian n f
  simpa using (ProbabilityTheory.IsGaussian.map_eq_gaussianReal (μ := P.map (fun ω : Ω =>
    fun i : Fin n => T (f i) ω)) L)

lemma IsGeneralizedGaussianProcess.charFunDual_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Test : Type*} {T : Test → Ω → ℝ} (h : IsGeneralizedGaussianProcess (P := P) (T := T))
    (n : ℕ) (f : Fin n → Test) (L : StrongDual ℝ (Fin n → ℝ)) :
    MeasureTheory.charFunDual (P.map (fun ω : Ω => fun i : Fin n => T (f i) ω)) L
      =
      Complex.exp
        ((∫ x, (L x : ℝ) ∂(P.map (fun ω : Ω => fun i : Fin n => T (f i) ω)) : ℂ) * Complex.I
          - (Var[⇑L; P.map (fun ω : Ω => fun i : Fin n => T (f i) ω)] : ℝ) / 2) := by
  letI : ProbabilityTheory.IsGaussian (P.map (fun ω : Ω => fun i : Fin n => T (f i) ω)) :=
    h.isGaussian n f
  simpa using
    (ProbabilityTheory.IsGaussian.charFunDual_eq (μ := P.map (fun ω : Ω => fun i : Fin n =>
      T (f i) ω)) L)

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

/-- The paper assumes a “no spontaneous magnetization / clustering” hypothesis `Φ_even` (Eq. `Phi_even`). -/
def PhiEven (μ : Measure (ZLattice d → ℝ)) (spin : ℝ → ℝ := fun x => x) : Prop :=
  Tendsto (fun x : ZLattice d => twoPoint (d := d) (spin := spin) (μ := μ) 0 x) (cocompact _)
    (𝓝 0)

variable {Ω : Type*} [MeasurableSpace Ω]

/--
Finite-dimensional convergence of the scaled observables `T_{f,L}` (paper’s notion of convergence
in distribution for the smeared field).

We follow mathlib’s standard design pattern:
convergence in distribution is weak convergence of the induced laws, i.e. `Tendsto` in
`MeasureTheory.ProbabilityMeasure`.

Implementation note: the definition uses the subsequence `L ↦ L+1` (a harmless finite shift for
`atTop`) to avoid the degenerate scale `L = 0`, for which the summability/measurability API for `Tf`
is not available.
-/
def HasFiniteDimensionalScalingLimit
    (μL : ℕ → Measure (ZLattice d → ℝ)) [∀ L, IsProbabilityMeasure (μL L)]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Tlim : C_c(Fin d → ℝ, ℝ) → Ω → ℝ) : Prop :=
  ∀ n : ℕ, ∀ f : Fin n → C_c(Fin d → ℝ, ℝ),
    let lawL : ℕ → ProbabilityMeasure (Fin n → ℝ) :=
      fun L =>
        let L' : ℕ := L + 1
        let F : (ZLattice d → ℝ) → (Fin n → ℝ) := fun φ i =>
          Tf (d := d) (S := ℝ) (spin := (fun x : ℝ => x)) (μ := μL L') (f := f i) L' φ
        have hF : Measurable F := by
          refine (measurable_pi_iff).2 ?_
          intro i
          simpa [F] using
            (measurable_Tf (d := d) (S := ℝ) (spin := (fun x : ℝ => x)) (μ := μL L') (f := f i)
              (L := L') (Nat.succ_pos L) (measurable_id))
        ⟨(μL L').map F, Measure.isProbabilityMeasure_map (μ := μL L') hF.aemeasurable⟩
    let ωmap : Ω → (Fin n → ℝ) := fun ω i => Tlim (f i) ω
    ∃ hω : Measurable ωmap,
      Tendsto lawL atTop
        (𝓝
          (⟨P.map ωmap, Measure.isProbabilityMeasure_map (μ := P) hω.aemeasurable⟩ :
            ProbabilityMeasure (Fin n → ℝ)))

lemma HasFiniteDimensionalScalingLimit.measurable_Tlim
    (μL : ℕ → Measure (ZLattice d → ℝ)) [∀ L, IsProbabilityMeasure (μL L)]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Tlim : C_c(Fin d → ℝ, ℝ) → Ω → ℝ)
    (h : HasFiniteDimensionalScalingLimit (d := d) (Ω := Ω) μL P Tlim)
    (f : C_c(Fin d → ℝ, ℝ)) :
    Measurable (Tlim f) := by
  let f1 : Fin 1 → C_c(Fin d → ℝ, ℝ) := fun _ => f
  rcases h 1 f1 with ⟨hω, _ht⟩
  have h0 : Measurable (fun ω : Ω => (fun i : Fin 1 => Tlim (f1 i) ω) 0) :=
    (measurable_pi_iff).1 hω 0
  simpa [f1] using h0

lemma HasFiniteDimensionalScalingLimit.tendsto_integral
    (μL : ℕ → Measure (ZLattice d → ℝ)) [∀ L, IsProbabilityMeasure (μL L)]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Tlim : C_c(Fin d → ℝ, ℝ) → Ω → ℝ)
    (h : HasFiniteDimensionalScalingLimit (d := d) (Ω := Ω) μL P Tlim)
    (n : ℕ) (f : Fin n → C_c(Fin d → ℝ, ℝ)) (g : BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    ∃ hω : Measurable (fun ω : Ω => fun i : Fin n => Tlim (f i) ω),
      let lawL : ℕ → ProbabilityMeasure (Fin n → ℝ) :=
        fun L =>
          let L' : ℕ := L + 1
          let F : (ZLattice d → ℝ) → (Fin n → ℝ) := fun φ i =>
            Tf (d := d) (S := ℝ) (spin := (fun x : ℝ => x)) (μ := μL L') (f := f i) L' φ
          have hF : Measurable F := by
            refine (measurable_pi_iff).2 ?_
            intro i
            simpa [F] using
              (measurable_Tf (d := d) (S := ℝ) (spin := (fun x : ℝ => x)) (μ := μL L') (f := f i)
                (L := L') (Nat.succ_pos L) (measurable_id))
          ⟨(μL L').map F, Measure.isProbabilityMeasure_map (μ := μL L') hF.aemeasurable⟩
      let ωmap : Ω → (Fin n → ℝ) := fun ω i => Tlim (f i) ω
      let law : ProbabilityMeasure (Fin n → ℝ) :=
        (⟨P.map ωmap, Measure.isProbabilityMeasure_map (μ := P) hω.aemeasurable⟩ :
          ProbabilityMeasure (Fin n → ℝ))
      Tendsto (fun L : ℕ => ∫ x, g x ∂(lawL L : Measure (Fin n → ℝ)))
        atTop (𝓝 (∫ x, g x ∂(law : Measure (Fin n → ℝ)))) := by
  rcases h n f with ⟨hω, ht⟩
  refine ⟨hω, ?_⟩
  let lawL : ℕ → ProbabilityMeasure (Fin n → ℝ) := fun L =>
    let L' : ℕ := L + 1
    let F : (ZLattice d → ℝ) → (Fin n → ℝ) := fun φ i =>
      Tf (d := d) (S := ℝ) (spin := (fun x : ℝ => x)) (μ := μL L') (f := f i) L' φ
    have hF : Measurable F := by
      refine (measurable_pi_iff).2 ?_
      intro i
      simpa [F] using
        (measurable_Tf (d := d) (S := ℝ) (spin := (fun x : ℝ => x)) (μ := μL L') (f := f i)
          (L := L') (Nat.succ_pos L) (measurable_id))
    ⟨(μL L').map F, Measure.isProbabilityMeasure_map (μ := μL L') hF.aemeasurable⟩
  let ωmap : Ω → (Fin n → ℝ) := fun ω i => Tlim (f i) ω
  let law : ProbabilityMeasure (Fin n → ℝ) :=
    (⟨P.map ωmap, Measure.isProbabilityMeasure_map (μ := P) hω.aemeasurable⟩ :
      ProbabilityMeasure (Fin n → ℝ))
  have ht_int :
      Tendsto (fun L : ℕ => ∫ x, g x ∂(lawL L : Measure (Fin n → ℝ)))
        atTop (𝓝 (∫ x, g x ∂(law : Measure (Fin n → ℝ)))) := by
    have ht' :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto (μs := lawL) (μ := law)).1 (by
        simpa [lawL, ωmap, law] using ht)
    simpa using ht' g
  simpa [lawL, ωmap, law] using ht_int

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
  -- TODO: combine (i) Proposition 1.3 (characteristic-function bound),
  -- (ii) tightness/projective limit machinery, and
  -- (iii) `IsGaussian` characterization via `charFunDual`.
  sorry

end Phi4Gaussianity

/-! ## Statements of the paper’s main theorems -/

section Statements

/-! ### Theorem 1.2 (Improved tree diagram bound, Ising, d=4) -/

/--
**Theorem (Improved tree diagram bound inequality)** (paper Theorem 1.2 / Theorem 1.3 in the TeX).

Implementation note: we state the inequality in `ENNReal` using `ENNReal.ofReal` so that the
infinite sum on the right-hand side is always meaningful (it may take the value `∞`), avoiding
auxiliary `Summable` side-conditions. One can recover a real-valued statement by applying
`ENNReal.toReal` once finiteness is established.
-/
theorem ImprovedTreeDiagramBound_Ising4
    (J : ℝ) (μβ : ℝ → Measure (Z4 → Bool))
    (βc : ℝ) (ξ : ℝ → ℝ≥0∞) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ β : ℝ, β ≤ βc →
        Ising.IsIsingNNGibbsState' (d := 4) (J := J) (β := β) (μ := μβ β) →
        IsCorrelationLength (d := 4) (spin := SpinGlass.isingSpin) (μ := μβ β)
          (x := (0 : Z4)) (i := (0 : Fin 4)) (ξ β) →
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
  -- TODO: random current representation + switching lemma + scale bookkeeping (TeX Sections 3–5).
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
    (J : ℝ) (μβ : ℝ → Measure (Z4 → Bool)) (βc : ℝ) (ξ : ℝ → ℝ≥0∞) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ β : ℝ, β ≤ βc →
        Ising.IsIsingNNGibbsState' (d := 4) (J := J) (β := β) (μ := μβ β) →
        IsCorrelationLength (d := 4) (spin := SpinGlass.isingSpin) (μ := μβ β)
          (x := (0 : Z4)) (i := (0 : Fin 4)) (ξ β) →
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
  -- TODO: implement TeX Proposition `prop:gaussian b` (Section 4.3),
  -- using the cumulant/Ursell bridge for `Tf` from `SpinGlass.Lattice.Zd.Scaling`.
  sorry

/-!
### Structural dependency: Proposition 1.3 from Theorem 1.2

The paper derives Proposition `prop:gaussian b` from the improved tree diagram bound
(Theorem 1.2 / 1.3 in the TeX) combined with a Lee–Yang/Newman moment comparison
inequality.  We record this dependency as an explicit lemma so that the eventual proof
can be filled in modularly.
-/

theorem gaussianCharFnBound_Ising4_of_ImprovedTreeDiagramBound_Ising4
    (J : ℝ) (μβ : ℝ → Measure (Z4 → Bool)) (βc : ℝ) (ξ : ℝ → ℝ≥0∞) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ β : ℝ, β ≤ βc →
        Ising.IsIsingNNGibbsState' (d := 4) (J := J) (β := β) (μ := μβ β) →
        IsCorrelationLength (d := 4) (spin := SpinGlass.isingSpin) (μ := μβ β)
          (x := (0 : Z4)) (i := (0 : Fin 4)) (ξ β) →
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
                        twoPoint (d := 4) (spin := SpinGlass.isingSpin) (μ := μβ β) u t))) →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ β : ℝ, β ≤ βc →
        Ising.IsIsingNNGibbsState' (d := 4) (J := J) (β := β) (μ := μβ β) →
        IsCorrelationLength (d := 4) (spin := SpinGlass.isingSpin) (μ := μβ β)
          (x := (0 : Z4)) (i := (0 : Fin 4)) (ξ β) →
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
  intro _hTree
  -- The proof will combine:
  -- (1) a Lee–Yang/Newman moment comparison inequality (Aizenman switching),
  -- (2) the improved tree diagram bound for `ursell4`,
  -- (3) the cumulant/ursell identity for `Tf` from `SpinGlass.Lattice.Zd.Scaling`.
  --
  -- TODO: implement the full chain as in TeX Section 4.3.
  sorry

/-! ### Theorem 6.1 (Improved tree diagram bound for the GS class, d=4) -/

/--
**Theorem (Improved tree diagram bound for the GS class)** (paper Theorem 6.1).
-/
theorem ImprovedTreeDiagramBound_GS4
    (ρ : ProbabilityMeasure ℝ) (J : ℝ) (μβ : ℝ → Measure (Z4 → ℝ))
    (βc : ℝ) (ξ : ℝ → ℝ≥0∞) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ β : ℝ, β ≤ βc →
        GSModel.IsGSNNQuadraticModel (d := 4) (J := J) (β := β) ρ (μβ β) →
        IsCorrelationLength (d := 4) (spin := (fun x : ℝ => x)) (μ := μβ β)
          (x := (0 : Z4)) (i := (0 : Fin 4)) (ξ β) →
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
  -- TODO: formalize GS class + Griffiths–Simon reduction, then lift the Ising bound.
  sorry

/-!
### Appendix Proposition 3 (finite-volume random current inequalities)

The random-current part of the paper’s Appendix Proposition `prop:3` is developed in
`SpinGlass.Papers.Triviality4D.RandomCurrentConsequences` and
`SpinGlass.Papers.Triviality4D.RandomCurrentUrsell4`.

Here we expose the already-proved implication `(imp) → (prop3b)` as a theorem with explicit
assumptions.
-/

namespace RandomCurrent

universe u

variable {V : Type u} [DecidableEq V]
variable {Λ : Finset V}

/--
Appendix Proposition `prop:3`: the switching-lemma step turning `(imp)` into the “two-step” bound
`(prop3b)` (finite volume).

`RandomCurrent.PPairReal_connected_and_connected_le_twoStep_of_imp`, with the required
nonvanishing hypotheses discharged under:

- nonnegative couplings `β * J e ≥ 0`, and
- reachability in the graph of *strictly positive* couplings between `x` and `y`, between `x` and `u`,
  and between `u` and `y`.
-/
theorem PPairReal_connected_and_connected_le_twoStep_of_imp_of_nonneg_of_reachable_posCouplingGraph
    (β : ℝ) (J : Edge (V := V) Λ → ℝ) {x y u v : ↥Λ}
    (hxy : x ≠ y) (hxu : x ≠ u) (hyu : y ≠ u)
    (hxv : x ≠ v) (hyv : y ≠ v) (huv : u ≠ v)
    (hβJ : ∀ e : Edge (V := V) Λ, 0 ≤ β * J e)
    (hreach_xy : (posCouplingGraph (V := V) (Λ := Λ) β J).Reachable x y)
    (hreach_xu : (posCouplingGraph (V := V) (Λ := Λ) β J).Reachable x u)
    (hreach_uy : (posCouplingGraph (V := V) (Λ := Λ) β J).Reachable u y)
    (himp :
        PPairReal (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) ({u, y} : Finset (↥Λ))
              {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v}
          ≤
          PPairReal (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) (∅ : Finset (↥Λ))
                {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v}
            + PPairReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) ({u, y} : Finset (↥Λ))
                {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v}
            - PPairReal (V := V) (Λ := Λ) β J (∅ : Finset (↥Λ)) (∅ : Finset (↥Λ))
                {n : Current (V := V) Λ | Connected (V := V) (Λ := Λ) n u v}) :
    PPairReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) (∅ : Finset (↥Λ))
        {n : Current (V := V) Λ |
          Connected (V := V) (Λ := Λ) n x u ∧ Connected (V := V) (Λ := Λ) n x v}
      ≤
      (isingCorr (V := V) (Λ := Λ) β J ({x, v} : Finset (↥Λ)) *
            isingCorr (V := V) (Λ := Λ) β J ({u, v} : Finset (↥Λ)) *
          isingCorr (V := V) (Λ := Λ) β J ({u, y} : Finset (↥Λ))) /
        isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ))
        +
      (isingCorr (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) *
            isingCorr (V := V) (Λ := Λ) β J ({u, v} : Finset (↥Λ)) *
          isingCorr (V := V) (Λ := Λ) β J ({v, y} : Finset (↥Λ))) /
        isingCorr (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) := by
  have hZxy : ZReal (V := V) (Λ := Λ) β J ({x, y} : Finset (↥Λ)) ≠ 0 :=
    ZReal_pair_ne_zero_of_reachable_posCouplingGraph (V := V) (Λ := Λ) (β := β) (J := J)
      hβJ hxy hreach_xy
  have hZxu : ZReal (V := V) (Λ := Λ) β J ({x, u} : Finset (↥Λ)) ≠ 0 :=
    ZReal_pair_ne_zero_of_reachable_posCouplingGraph (V := V) (Λ := Λ) (β := β) (J := J)
      hβJ hxu hreach_xu
  have hZuy : ZReal (V := V) (Λ := Λ) β J ({u, y} : Finset (↥Λ)) ≠ 0 :=
    ZReal_pair_ne_zero_of_reachable_posCouplingGraph (V := V) (Λ := Λ) (β := β) (J := J)
      hβJ hyu.symm hreach_uy
  simpa using
    (PPairReal_connected_and_connected_le_twoStep_of_imp (V := V) (Λ := Λ)
      (β := β) (J := J) (x := x) (y := y) (u := u) (v := v)
      hxy hxu hyu hxv hyv huv hZxy hZxu hZuy hβJ himp)

end RandomCurrent

end Statements

end Triviality4D

end SpinGlass.Papers
