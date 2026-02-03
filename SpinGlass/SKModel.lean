import SpinGlass.Defs
import Common.Mathlib.Probability.Distributions.Gaussian.IntegrationByParts
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology

namespace SpinGlass

/-!
# The Sherrington–Kirkpatrick (SK) model: disorder structures (finite `N`)

This file defines the *random* Hamiltonians used in the SK model and in the simple
reference model used for Guerra's interpolation, in a way compatible with the
Hilbert–space Gaussian IBP machinery.

We keep the disorder abstract: a disorder is a centered Gaussian random vector in
`EnergySpace N` together with a specification of its covariance kernel on the
canonical basis `std_basis`.

## References
* M. Talagrand, *Mean Field Models for Spin Glasses*, Vol. I.
* D. Panchenko, *The Sherrington–Kirkpatrick Model*.
-/

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

variable (N : ℕ)

/-! ### Deterministic thermodynamic quantities (aliases) -/

/-- Partition function \(Z_N(H)\). -/
noncomputable def partition_function (H : EnergySpace N) : ℝ := Z N H

-- NOTE: the free energy density is defined in `SpinGlasses/Defs.lean` as
-- `SpinGlass.free_energy_density`.

/-- Gibbs average \(\langle f \rangle_H\) under the Gibbs weights `gibbs_pmf`. -/
noncomputable def gibbs_average (H : EnergySpace N) (f : Config N → ℝ) : ℝ :=
  ∑ σ, gibbs_pmf N H σ * f σ

/-! ### Gaussian disorder specifications -/

/--
An abstract (finite-volume) **centered Gaussian Hamiltonian** specified by its covariance kernel.

This is the “Vol. II / covariance-first” abstraction: the randomness is carried by a centered
Gaussian random vector `U : Ω → EnergySpace N`, and the model is characterized by an explicit
covariance kernel `cov : Config N → Config N → ℝ` on the canonical basis `std_basis`.

Concretely, `cov σ τ` represents the value of
\[
  \mathbb{E}[U(\sigma)\,U(\tau)].
\]
in the Hilbert-space Gaussian IBP package, expressed via the covariance operator `covOp`.
-/
structure GaussianDisorder where
  /-- The covariance kernel on configurations. -/
  cov : Config N → Config N → ℝ
  /-- The (random) Hamiltonian. -/
  U : Ω → EnergySpace N
  /-- Measurability of the Hamiltonian. -/
  measU : Measurable U
  /-- The law of `U` is Gaussian. -/
  hU : ProbabilityTheory.IsGaussian ((ℙ : Measure Ω).map U)
  /-- Centeredness of the disorder (mean zero). -/
  mean0 : (∫ x : EnergySpace N, x ∂((ℙ : Measure Ω).map U)) = 0
  /-- Covariance kernel agreement on the canonical basis. -/
  cov_eq : ∀ σ τ,
    inner ℝ ((ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map U)) (std_basis N σ))
      (std_basis N τ) = cov σ τ

/--
SK disorder: a centered Gaussian Hamiltonian with covariance kernel `sk_cov_kernel`.

This corresponds (up to the usual normalizations) to the classical SK Hamiltonian
\(H_N(\sigma) = \frac{\beta}{\sqrt{N}}\sum_{i < j} g_{ij}\sigma_i\sigma_j\).
-/
structure SKDisorder (β h : ℝ) where
  /-- The (random) Hamiltonian. -/
  U : Ω → EnergySpace N
  /-- Measurability of the Hamiltonian. -/
  measU : Measurable U
  /-- The law of `U` is Gaussian. -/
  hU : ProbabilityTheory.IsGaussian ((ℙ : Measure Ω).map U)
  /-- Centeredness of the disorder (mean zero). -/
  mean0 : (∫ x : EnergySpace N, x ∂((ℙ : Measure Ω).map U)) = 0
  /-- Covariance on the canonical basis. -/
  cov_eq : ∀ σ τ,
    inner ℝ ((ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map U)) (std_basis N σ))
      (std_basis N τ) =  sk_cov_kernel N β σ τ

/--
Simple (reference) disorder: a centered Gaussian Hamiltonian with covariance kernel
`simple_cov_kernel`.

This matches the “magnetic field” comparison model used in Guerra's bound.
-/
structure SimpleDisorder (β q : ℝ) where
  /-- The (random) Hamiltonian. -/
  V : Ω → EnergySpace N
  /-- Measurability of the Hamiltonian. -/
  measV : Measurable V
  /-- The law of `V` is Gaussian. -/
  hV : ProbabilityTheory.IsGaussian ((ℙ : Measure Ω).map V)
  /-- Centeredness of the disorder (mean zero). -/
  mean0 : (∫ x : EnergySpace N, x ∂((ℙ : Measure Ω).map V)) = 0
  /-- Covariance on the canonical basis. -/
  cov_eq : ∀ σ τ,
    inner ℝ ((ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map V)) (std_basis N σ))
      (std_basis N τ) = simple_cov_kernel N β (fun x => q * x) σ τ

/-- View an `SKDisorder` as an abstract covariance-specified `GaussianDisorder`. -/
@[simp] noncomputable
def SKDisorder.toGaussianDisorder {β h : ℝ} (sk : SKDisorder (Ω := Ω) (N := N) β h) :
    GaussianDisorder (Ω := Ω) (N := N) :=
  { cov := sk_cov_kernel N β
    U := sk.U
    measU := sk.measU
    hU := sk.hU
    mean0 := sk.mean0
    cov_eq := by
      intro σ τ
      simpa using sk.cov_eq σ τ }

/-- View a `SimpleDisorder` as an abstract covariance-specified `GaussianDisorder`. -/
@[simp] noncomputable
def SimpleDisorder.toGaussianDisorder {β q : ℝ} (sim : SimpleDisorder (Ω := Ω) (N := N) β q) :
    GaussianDisorder (Ω := Ω) (N := N) :=
  { cov := simple_cov_kernel N β (fun x => q * x)
    U := sim.V
    measU := sim.measV
    hU := sim.hV
    mean0 := sim.mean0
    cov_eq := by
      intro σ τ
      simpa using sim.cov_eq σ τ }

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/--
Joint Gaussianity of an independent pair of Gaussian disorders.

This is the canonical Mathlib route to get a Gaussian law on the product space: use
`ProbabilityTheory.IndepFun.hasGaussianLaw` and then read it as `IsGaussian` on the pushforward
measure.


Downstream (e.g. `SpinGlass/Replicas.lean`) can use this to discharge the `IsGaussian` assumption
needed for Hilbert-space Gaussian IBP on the product disorder.
-/
lemma SKDisorder.simple_joint_isGaussian_of_indep
    {β h q : ℝ} (sk : SKDisorder (Ω := Ω) (N := N) β h) (sim : SimpleDisorder (Ω := Ω) (N := N) β q)
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V) :
    ProbabilityTheory.IsGaussian
      (((ℙ : Measure Ω).map fun ω => (sk.U ω, sim.V ω))) := by
  -- Upgrade the marginal `IsGaussian` laws to `HasGaussianLaw`, apply independence lemma,
  -- then unwrap back to `IsGaussian` on the pushforward.
  have hX : ProbabilityTheory.HasGaussianLaw sk.U (ℙ : Measure Ω) :=
    ⟨sk.hU⟩
  have hY : ProbabilityTheory.HasGaussianLaw sim.V (ℙ : Measure Ω) :=
    ⟨sim.hV⟩
  exact (ProbabilityTheory.IndepFun.hasGaussianLaw (P := (ℙ : Measure Ω)) hX hY hindep).isGaussian_map

open scoped ENNReal

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/--
`IsGaussian` formulation of joint Gaussianity on the `L²`-product space `WithLp 2 (E × F)`.

This is the form needed to apply the intrinsic Hilbert-space Gaussian IBP theorem to the
`WithLp`-repackaged pair `(U,V)`.
-/
lemma SKDisorder.simple_joint_isGaussian_withLp_of_indep
    {β h q : ℝ} (sk : SKDisorder (Ω := Ω) (N := N) β h) (sim : SimpleDisorder (Ω := Ω) (N := N) β q)
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V) :
    ProbabilityTheory.IsGaussian
      (((ℙ : Measure Ω).map fun ω => WithLp.toLp 2 (sk.U ω, sim.V ω))) := by
  -- Use the canonical `HasGaussianLaw` lemma that already repackages via `toLp`.
  have hX : ProbabilityTheory.HasGaussianLaw sk.U (ℙ : Measure Ω) := ⟨sk.hU⟩
  have hY : ProbabilityTheory.HasGaussianLaw sim.V (ℙ : Measure Ω) := ⟨sim.hV⟩
  have hXY : ProbabilityTheory.HasGaussianLaw (fun ω => (sk.U ω, sim.V ω)) (ℙ : Measure Ω) :=
    ProbabilityTheory.IndepFun.hasGaussianLaw (P := (ℙ : Measure Ω)) hX hY hindep
  have htoLp : ProbabilityTheory.HasGaussianLaw
      (fun ω => WithLp.toLp (p := (2 : ℝ≥0∞)) (sk.U ω, sim.V ω)) (ℙ : Measure Ω) := by
    -- `Fact (1 ≤ 2)` is needed for `toLp`.
    haveI : Fact ((1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
    exact ProbabilityTheory.HasGaussianLaw.toLp_prodMk (X := sk.U) (Y := sim.V)
      (P := (ℙ : Measure Ω)) (p := (2 : ℝ≥0∞)) hXY
  exact htoLp.isGaussian_map

end SpinGlass
