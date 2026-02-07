import SpinGlass.Defs
import SpinGlass.FiniteGibbs.GibbsMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The Griffiths–Simon (GS) class of single-site measures

This file introduces a Lean formalization of Definition 2.1 (`\label{def:rho}`) from
`4D_triviality_June_2021_final.tex`.

In the paper, a probability measure `ρ(dφ)` on `ℝ` belongs to the GS class if either

1. it is the law of a **linear combination of finitely many ferromagnetically coupled Ising spins**,
   or
2. it is a **weak limit** of measures of type (1) and satisfies a mild **sub-Gaussian growth**
   integrability condition \( \int \exp(|φ|^α)\, dρ < ∞\) for some \(α>2\).

We bundle weak limits using mathlib’s topology on `MeasureTheory.ProbabilityMeasure`.
-/

open scoped BigOperators

open MeasureTheory ProbabilityTheory Filter Topology Real

namespace SpinGlass.Papers.Triviality4D

namespace GSClass

/-- The GS “core” random variable: a scaled linear combination of finitely many Ising spins. -/
noncomputable def coreVar {N : ℕ} (α : ℝ) (b : Fin N → ℝ) (σ : SpinGlass.Config N) : ℝ :=
  α * ∑ i : Fin N, b i * SpinGlass.isingSpin (σ i)

@[simp] lemma coreVar_zero {N : ℕ} (b : Fin N → ℝ) (σ : SpinGlass.Config N) :
    coreVar (N := N) 0 b σ = 0 := by
  simp [coreVar]

/--
The (finite-dimensional) ferromagnetic Ising Hamiltonian used in Definition 2.1.(1):

`H(σ) = - ∑_{i,j} K i j * σ_i * σ_j`, with `σ_i ∈ {±1}` represented by `SpinGlass.isingSpin`.

No symmetry assumptions are imposed on `K` at this interface level; the paper only requires
`K_{i,j} ≥ 0`.
-/
noncomputable def coreHamiltonian (N : ℕ) (K : Fin N → Fin N → ℝ) :
    SpinGlass.FiniteGibbs.EnergySpace (SpinGlass.Config N) :=
  WithLp.toLp 2 fun σ : SpinGlass.Config N =>
    - ∑ i : Fin N, ∑ j : Fin N, K i j * SpinGlass.isingSpin (σ i) * SpinGlass.isingSpin (σ j)

/-- The associated finite-volume Gibbs measure on `SpinGlass.Config N`. -/
noncomputable def coreIsingMeasure (N : ℕ) (K : Fin N → Fin N → ℝ) :
    Measure (SpinGlass.Config N) :=
  SpinGlass.FiniteGibbs.gibbsMeasure (α := SpinGlass.Config N) (coreHamiltonian (N := N) K)

instance (N : ℕ) (K : Fin N → Fin N → ℝ) : IsProbabilityMeasure (coreIsingMeasure (N := N) K) := by
  dsimp [coreIsingMeasure]
  infer_instance

/-- The GS-core single-site law on `ℝ` (pushforward of the finite Ising Gibbs measure). -/
noncomputable def coreLaw (N : ℕ) (α : ℝ) (b : Fin N → ℝ) (K : Fin N → Fin N → ℝ) :
    ProbabilityMeasure ℝ :=
  let μ : Measure (SpinGlass.Config N) := coreIsingMeasure (N := N) K
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  let f : SpinGlass.Config N → ℝ := fun σ => coreVar (N := N) α b σ
  have hf : Measurable f := by
    simpa [f] using (measurable_of_finite f)
  ⟨μ.map f, Measure.isProbabilityMeasure_map (μ := μ) hf.aemeasurable⟩

/--
The GS “core” condition: `ρ` is exactly the law of a GS-core variable, as in Definition 2.1.(1).
-/
def IsGSCore (ρ : ProbabilityMeasure ℝ) : Prop :=
  ∃ (N : ℕ) (α : ℝ) (b : Fin (N + 1) → ℝ) (K : Fin (N + 1) → Fin (N + 1) → ℝ),
    (∀ i j : Fin (N + 1), 0 ≤ K i j) ∧ ρ = coreLaw (N := N + 1) α b K

/-- The GS growth condition from Definition 2.1.(2) (`\label{sub_gauss}`). -/
def HasSubGaussianGrowth (ρ : ProbabilityMeasure ℝ) : Prop :=
  ∃ a : ℝ, 2 < a ∧ Integrable (fun x : ℝ => Real.exp (|x| ^ a)) (ρ : Measure ℝ)

/--
The Griffiths–Simon (GS) class (Definition 2.1): core or weak limit of core with sub-Gaussian growth.
-/
def IsGSClass (ρ : ProbabilityMeasure ℝ) : Prop :=
  IsGSCore ρ ∨
    (∃ ρn : ℕ → ProbabilityMeasure ℝ,
      (∀ n, IsGSCore (ρn n)) ∧ Tendsto ρn atTop (𝓝 ρ) ∧ HasSubGaussianGrowth ρ)

lemma IsGSClass.core {ρ : ProbabilityMeasure ℝ} (h : IsGSCore ρ) : IsGSClass ρ :=
  Or.inl h

lemma IsGSClass.of_weakLimit
    {ρ : ProbabilityMeasure ℝ} {ρn : ℕ → ProbabilityMeasure ℝ}
    (hcore : ∀ n, IsGSCore (ρn n)) (hlim : Tendsto ρn atTop (𝓝 ρ))
    (hgrowth : HasSubGaussianGrowth ρ) :
    IsGSClass ρ :=
  Or.inr ⟨ρn, hcore, hlim, hgrowth⟩

end GSClass

end SpinGlass.Papers.Triviality4D

