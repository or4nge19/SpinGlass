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

/-- For a centered `multivariateGaussian`, the covariance operator recovers the defining matrix in
the Dirac basis. -/
lemma inner_covarianceOperator_multivariateGaussian_std_basis
    (S : Matrix (Config N) (Config N) ℝ) (hS : S.PosSemidef) (σ τ : Config N) :
    inner ℝ (ProbabilityTheory.covarianceOperator
        (multivariateGaussian (0 : EnergySpace N) S) (std_basis N σ)) (std_basis N τ)
      = S σ τ := by
  classical
  set μ : Measure (EnergySpace N) := multivariateGaussian (0 : EnergySpace N) S with hμdef
  have hmem : MeasureTheory.MemLp (id : EnergySpace N → EnergySpace N) 2 μ :=
    ProbabilityTheory.IsGaussian.memLp_two_id
  have hmean : (∫ x : EnergySpace N, x ∂μ) = 0 := by
    simp [hμdef]
  -- `covarianceBilin` and `⟪covarianceOperator ·, ·⟫` agree because the mean vanishes.
  have hbilin : ProbabilityTheory.covarianceBilin μ (std_basis N σ) (std_basis N τ)
      = inner ℝ (ProbabilityTheory.covarianceOperator μ (std_basis N σ)) (std_basis N τ) := by
    rw [ProbabilityTheory.covarianceBilin_apply hmem,
      ProbabilityTheory.covarianceOperator_inner hmem]
    simp [hmean]
  -- Mathlib evaluates `covarianceBilin` of a `multivariateGaussian` as a quadratic form.
  have hquad : ProbabilityTheory.covarianceBilin μ (std_basis N σ) (std_basis N τ)
      = (std_basis N σ) ⬝ᵥ S *ᵥ (std_basis N τ) := by
    simpa [hμdef] using
      ProbabilityTheory.covarianceBilin_multivariateGaussian (μ := (0 : EnergySpace N)) hS
        (std_basis N σ) (std_basis N τ)
  have hdot : (std_basis N σ) ⬝ᵥ S *ᵥ (std_basis N τ) = S σ τ := by
    have hbasis : ∀ ρ κ : Config N,
        (std_basis N ρ : Config N → ℝ) κ = if ρ = κ then 1 else 0 := by
      intro ρ κ
      by_cases hρκ : ρ = κ
      · subst hρκ; simp [std_basis]
      · simp [hρκ, std_basis]
    have hmv : ∀ i : Config N, (S *ᵥ (std_basis N τ : Config N → ℝ)) i = S i τ := by
      intro i
      simp [Matrix.mulVec, dotProduct, hbasis]
    calc (std_basis N σ) ⬝ᵥ S *ᵥ (std_basis N τ)
        = ∑ i : Config N, (std_basis N σ : Config N → ℝ) i * S i τ := by
          simp [dotProduct, hmv]
      _ = S σ τ := by simp [hbasis]
  rw [← hbilin, hquad, hdot]

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

/-- The joint disorder law: independent centered Gaussians with the SK and reference
covariances. -/
def disorderSampleLaw (N : ℕ) (β q : ℝ) : Measure (DisorderSample N) :=
  (multivariateGaussian (0 : EnergySpace N) (skCovMatrix N β)).prod
    (multivariateGaussian (0 : EnergySpace N) (refCovMatrix N β q))

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
      ProbabilityTheory.IndepFun sk.U sim.U (ℙ : Measure Ω) := by
  classical
  let inst : MeasureSpace (DisorderSample N) := disorderMeasureSpace N β q
  refine ⟨DisorderSample N, inst, ?_, ?_⟩
  · exact isProbabilityMeasure_disorderSampleLaw N β q
  set μsk : Measure (EnergySpace N) :=
    multivariateGaussian (0 : EnergySpace N) (skCovMatrix N β) with hμsk
  set μref : Measure (EnergySpace N) :=
    multivariateGaussian (0 : EnergySpace N) (refCovMatrix N β q) with hμref
  have hSsk : (skCovMatrix N β).PosSemidef := posSemidef_skCovMatrix N β
  have hSref : (refCovMatrix N β q).PosSemidef := posSemidef_refCovMatrix N β q hq
  have hprobsk : IsProbabilityMeasure μsk := by rw [hμsk]; infer_instance
  have hprobref : IsProbabilityMeasure μref := by rw [hμref]; infer_instance
  -- The marginals of the product law are the two prescribed Gaussians.
  have hmapfst : (ℙ : Measure (DisorderSample N)).map DisorderSample.fst = μsk := by
    have hfp := Measure.map_fst_prod (μ := μsk) (ν := μref)
    rw [measure_univ, one_smul] at hfp
    exact hfp
  have hmapsnd : (ℙ : Measure (DisorderSample N)).map DisorderSample.snd = μref := by
    have hsp := Measure.map_snd_prod (μ := μsk) (ν := μref)
    rw [measure_univ, one_smul] at hsp
    exact hsp
  refine ⟨{ U := DisorderSample.fst
            measU := measurable_DisorderSample_fst N
            hU := by
              have : ProbabilityTheory.IsGaussian
                  ((ℙ : Measure (DisorderSample N)).map DisorderSample.fst) := by
                rw [hmapfst, hμsk]; infer_instance
              exact ProbabilityTheory.IsGaussian.hasGaussianLaw
            mean0 := by rw [hmapfst, hμsk]; simp
            cov_eq := fun σ τ => by
              rw [hmapfst, hμsk]
              exact inner_covarianceOperator_multivariateGaussian_std_basis
                (skCovMatrix N β) hSsk σ τ },
          { U := DisorderSample.snd
            measU := measurable_DisorderSample_snd N
            hU := by
              have : ProbabilityTheory.IsGaussian
                  ((ℙ : Measure (DisorderSample N)).map DisorderSample.snd) := by
                rw [hmapsnd, hμref]; infer_instance
              exact ProbabilityTheory.IsGaussian.hasGaussianLaw
            mean0 := by rw [hmapsnd, hμref]; simp
            cov_eq := fun σ τ => by
              rw [hmapsnd, hμref]
              exact inner_covarianceOperator_multivariateGaussian_std_basis
                (refCovMatrix N β q) hSref σ τ }, ?_⟩
  exact ProbabilityTheory.indepFun_prod (μ := μsk) (ν := μref)
    (X := id) (Y := id) measurable_id measurable_id

end

end SpinGlass
