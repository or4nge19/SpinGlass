import Common.Mathlib.Probability.Distributions.Gaussian.MultivariateCovariance
import SpinGlass.SKModel
import SpinGlass.CovariancePosSemidef
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.Basic

/-!
# Existence of the SK and replica-symmetric disorders

Everything in the Guerra development is stated for a pair `sk : SKDisorder N β`,
`sim : SimpleDisorder N β q` of independent centered Gaussian Hamiltonians with prescribed
covariance kernels. This file exhibits such a pair, so that Guerra's bound is not conditional on
unrealizable data.

The construction is the canonical one: `EnergySpace N` is `EuclideanSpace ℝ (Config N)`, the
covariance kernels are positive semidefinite (`posSemidef_skCovMatrix`,
`posSemidef_refCovMatrix`), so Mathlib's `multivariateGaussian` provides centered Gaussian measures
with exactly those covariances, and the product measure on
`EnergySpace N × EnergySpace N` makes the two coordinates independent.

## Main statements

- `mulVec_ofLp_std_basis`, `dotProduct_ofLp_std_basis`: matrices and Dirac vectors.
- `inner_covarianceOperator_multivariateGaussian_std_basis`: the covariance operator of a centered
  `multivariateGaussian` reads off the defining matrix in the Dirac basis.
- `exists_skDisorder_simpleDisorder_indepFun`: **the disorder pair exists** for `0 ≤ q`.
-/

open MeasureTheory ProbabilityTheory Matrix BigOperators
open scoped ENNReal InnerProductSpace

namespace SpinGlass

noncomputable section

variable {N : ℕ}

/-! ### Reading off the covariance of a centered multivariate Gaussian -/

/-- Applying a matrix to a Dirac vector reads off a column. -/
lemma mulVec_ofLp_std_basis (S : Matrix (Config N) (Config N) ℝ) (τ i : Config N) :
    (S *ᵥ (WithLp.ofLp (std_basis N τ))) i = S i τ := by
  classical
  have hbasis : ∀ ρ κ : Config N,
      (std_basis N ρ : Config N → ℝ) κ = if ρ = κ then 1 else 0 := by
    intro ρ κ
    by_cases hρκ : ρ = κ
    · subst hρκ; simp [std_basis]
    · simp [hρκ, std_basis]
  simp [Matrix.mulVec, dotProduct, hbasis]

/-- Pairing with a Dirac vector reads off a coordinate. -/
lemma dotProduct_ofLp_std_basis (v : Config N → ℝ) (τ : Config N) :
    v ⬝ᵥ (WithLp.ofLp (std_basis N τ)) = v τ := by
  classical
  have hbasis : ∀ ρ κ : Config N,
      (std_basis N ρ : Config N → ℝ) κ = if ρ = κ then 1 else 0 := by
    intro ρ κ
    by_cases hρκ : ρ = κ
    · subst hρκ; simp [std_basis]
    · simp [hρκ, std_basis]
  simp [dotProduct, hbasis]

/-- For a centered `multivariateGaussian`, the covariance operator recovers the defining matrix in
the Dirac basis. -/
lemma inner_covarianceOperator_multivariateGaussian_std_basis
    (S : Matrix (Config N) (Config N) ℝ) (hS : S.PosSemidef) (σ τ : Config N) :
    inner ℝ (ProbabilityTheory.covarianceOperator
        (multivariateGaussian (0 : EnergySpace N) S) (std_basis N σ)) (std_basis N τ)
      = S σ τ := by
  classical
  have hbasis : ∀ ρ κ : Config N,
      (std_basis N ρ : Config N → ℝ) κ = if ρ = κ then 1 else 0 := by
    intro ρ κ
    by_cases hρκ : ρ = κ
    · subst hρκ; simp [std_basis]
    · simp [hρκ, std_basis]
  have hmv : ∀ i : Config N, (S *ᵥ (WithLp.ofLp (std_basis N τ))) i = S i τ :=
    mulVec_ofLp_std_basis S τ
  rw [inner_covarianceOperator_multivariateGaussian (ι := Config N) hS]
  calc (WithLp.ofLp (std_basis N σ)) ⬝ᵥ S *ᵥ (WithLp.ofLp (std_basis N τ))
      = ∑ i : Config N, (std_basis N σ : Config N → ℝ) i * S i τ := by
        simp [dotProduct, hmv]
    _ = S σ τ := by simp [hbasis]

/-! ### The canonical disorder sample space -/

/-- The SK covariance matrix `N β² R²/2`. -/
def skCovMatrix (N : ℕ) (β : ℝ) : Matrix (Config N) (Config N) ℝ :=
  Matrix.of fun σ τ => sk_cov_kernel N β σ τ

/-- Guerra's replica-symmetric reference covariance matrix `N β² q R`. -/
def refCovMatrix (N : ℕ) (β q : ℝ) : Matrix (Config N) (Config N) ℝ :=
  Matrix.of fun σ τ => simple_cov_kernel N β (fun r => q * r) σ τ

/-- The canonical sample space: one coordinate for each of the two Hamiltonians. A `def` rather
than an `abbrev`, so that its `MeasureSpace` structure is the disorder law and not the product of
the ambient volumes. -/
def DisorderSample (N : ℕ) : Type := EnergySpace N × EnergySpace N

instance instMeasurableSpaceDisorderSample (N : ℕ) :
    MeasurableSpace (DisorderSample N) :=
  inferInstanceAs (MeasurableSpace (EnergySpace N × EnergySpace N))

/-- First coordinate of a disorder sample (the SK Hamiltonian). -/
def DisorderSample.fst {N : ℕ} (x : DisorderSample N) : EnergySpace N :=
  (show EnergySpace N × EnergySpace N from x).1

/-- Second coordinate of a disorder sample (the reference Hamiltonian). -/
def DisorderSample.snd {N : ℕ} (x : DisorderSample N) : EnergySpace N :=
  (show EnergySpace N × EnergySpace N from x).2

lemma measurable_DisorderSample_fst (N : ℕ) :
    Measurable (DisorderSample.fst (N := N)) :=
  measurable_fst

lemma measurable_DisorderSample_snd (N : ℕ) :
    Measurable (DisorderSample.snd (N := N)) :=
  measurable_snd

/-- **The joint law of a pair of independent centered Gaussian disorders** with prescribed
covariance matrices. -/
def pairSampleLaw (N : ℕ) (S T : Matrix (Config N) (Config N) ℝ) : Measure (DisorderSample N) :=
  (multivariateGaussian (0 : EnergySpace N) S).prod (multivariateGaussian (0 : EnergySpace N) T)

instance isProbabilityMeasure_pairSampleLaw (N : ℕ) (S T : Matrix (Config N) (Config N) ℝ) :
    IsProbabilityMeasure (pairSampleLaw N S T) :=
  inferInstanceAs (IsProbabilityMeasure
    ((multivariateGaussian (0 : EnergySpace N) S).prod
      (multivariateGaussian (0 : EnergySpace N) T)))

/-- `DisorderSample N` as a measure space carrying `pairSampleLaw`. -/
@[instance_reducible] def pairMeasureSpace (N : ℕ) (S T : Matrix (Config N) (Config N) ℝ) :
    MeasureSpace (DisorderSample N) :=
  ⟨pairSampleLaw N S T⟩

/-- **A pair of independent centered Gaussian disorders with prescribed positive semidefinite
covariance kernels exists.** Every downstream interpolation — Guerra's replica-symmetric
comparison, the Guerra–Toninelli splitting, and the isolation of a single `p`-spin term of a mixed
Hamiltonian — is an instance of this. -/
theorem exists_gaussianDisorder_pair_indepFun (N : ℕ) {S T : Matrix (Config N) (Config N) ℝ}
    (hS : S.PosSemidef) (hT : T.PosSemidef) :
    ∃ (Ω : Type) (_ : MeasureSpace Ω) (_ : IsProbabilityMeasure (ℙ : Measure Ω))
      (G₁ : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) (fun σ τ => S σ τ))
      (G₂ : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) (fun σ τ => T σ τ)),
      ProbabilityTheory.IndepFun G₁.U G₂.U (ℙ : Measure Ω) := by
  classical
  let inst : MeasureSpace (DisorderSample N) := pairMeasureSpace N S T
  refine ⟨DisorderSample N, inst, ?_, ?_⟩
  · exact isProbabilityMeasure_pairSampleLaw N S T
  set μ₁ : Measure (EnergySpace N) := multivariateGaussian (0 : EnergySpace N) S with hμ₁
  set μ₂ : Measure (EnergySpace N) := multivariateGaussian (0 : EnergySpace N) T with hμ₂
  have hprob₁ : IsProbabilityMeasure μ₁ := by rw [hμ₁]; infer_instance
  have hprob₂ : IsProbabilityMeasure μ₂ := by rw [hμ₂]; infer_instance
  have hmapfst : (ℙ : Measure (DisorderSample N)).map DisorderSample.fst = μ₁ := by
    have hfp := Measure.map_fst_prod (μ := μ₁) (ν := μ₂)
    rw [measure_univ, one_smul] at hfp
    exact hfp
  have hmapsnd : (ℙ : Measure (DisorderSample N)).map DisorderSample.snd = μ₂ := by
    have hsp := Measure.map_snd_prod (μ := μ₁) (ν := μ₂)
    rw [measure_univ, one_smul] at hsp
    exact hsp
  refine ⟨{ U := DisorderSample.fst
            measU := measurable_DisorderSample_fst N
            hU := by
              have : ProbabilityTheory.IsGaussian
                  ((ℙ : Measure (DisorderSample N)).map DisorderSample.fst) := by
                rw [hmapfst, hμ₁]; infer_instance
              exact ProbabilityTheory.IsGaussian.hasGaussianLaw
            mean0 := by rw [hmapfst, hμ₁]; simp
            cov_eq := fun σ τ => by
              rw [hmapfst, hμ₁]
              exact inner_covarianceOperator_multivariateGaussian_std_basis S hS σ τ },
          { U := DisorderSample.snd
            measU := measurable_DisorderSample_snd N
            hU := by
              have : ProbabilityTheory.IsGaussian
                  ((ℙ : Measure (DisorderSample N)).map DisorderSample.snd) := by
                rw [hmapsnd, hμ₂]; infer_instance
              exact ProbabilityTheory.IsGaussian.hasGaussianLaw
            mean0 := by rw [hmapsnd, hμ₂]; simp
            cov_eq := fun σ τ => by
              rw [hmapsnd, hμ₂]
              exact inner_covarianceOperator_multivariateGaussian_std_basis T hT σ τ }, ?_⟩
  exact ProbabilityTheory.indepFun_prod (μ := μ₁) (ν := μ₂)
    (X := id) (Y := id) measurable_id measurable_id

/-- The joint disorder law: independent centered Gaussians with the SK and reference
covariances. -/
def disorderSampleLaw (N : ℕ) (β q : ℝ) : Measure (DisorderSample N) :=
  pairSampleLaw N (skCovMatrix N β) (refCovMatrix N β q)

instance isProbabilityMeasure_disorderSampleLaw (N : ℕ) (β q : ℝ) :
    IsProbabilityMeasure (disorderSampleLaw N β q) := by
  have : IsProbabilityMeasure
      (multivariateGaussian (0 : EnergySpace N) (skCovMatrix N β)) := inferInstance
  have : IsProbabilityMeasure
      (multivariateGaussian (0 : EnergySpace N) (refCovMatrix N β q)) := inferInstance
  exact inferInstanceAs (IsProbabilityMeasure
    ((multivariateGaussian (0 : EnergySpace N) (skCovMatrix N β)).prod
      (multivariateGaussian (0 : EnergySpace N) (refCovMatrix N β q))))

/-- `DisorderSample N` as a measure space carrying `disorderSampleLaw`. -/
@[instance_reducible] def disorderMeasureSpace (N : ℕ) (β q : ℝ) :
    MeasureSpace (DisorderSample N) :=
  ⟨disorderSampleLaw N β q⟩

/-- **The SK / replica-symmetric disorder pair exists.** For `0 ≤ q` there is a probability space
carrying independent centered Gaussian Hamiltonians whose covariance kernels are the SK kernel
`N β² R²/2` and Guerra's reference kernel `N β² q R`. Consequently `guerraPhi_one_le` and
`integral_free_energy_density_le` are statements about data that exists. -/
theorem exists_skDisorder_simpleDisorder_indepFun (N : ℕ) (β q : ℝ) (hq : 0 ≤ q) :
    ∃ (Ω : Type) (_ : MeasureSpace Ω) (_ : IsProbabilityMeasure (ℙ : Measure Ω))
      (sk : SKDisorder (Ω := Ω) N β) (sim : SimpleDisorder (Ω := Ω) N β q),
      ProbabilityTheory.IndepFun sk.U sim.U (ℙ : Measure Ω) :=
  exists_gaussianDisorder_pair_indepFun N (posSemidef_skCovMatrix N β)
    (posSemidef_refCovMatrix N β q hq)

end

end SpinGlass
