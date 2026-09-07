import SpinGlass.Defs
import SpinGlass.Poincare
import Common.Mathlib.Probability.Distributions.Gaussian.IntegrationByParts
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Common.Mathlib.Probability.Distributions.Gaussian_ProdCovariance
import Mathlib.Probability.Distributions.Gaussian.CharFun

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology
open scoped ENNReal

namespace SpinGlass

/-!
# Sherrington–Kirkpatrick disorder

Centered Gaussian Hamiltonians on `EnergySpace N` specified by a covariance kernel on `std_basis`.
One structure `GaussianDisorder P K` — a centered Gaussian Hamiltonian with prescribed
covariance kernel — of which `SKDisorder` and `SimpleDisorder` are abbreviations at two kernels.
Main: `GaussianDisorder`, `disorderPairLaw`, `covarianceOperator_disorderPairLaw_std_basis_left`.
Talagrand Vol. I.
-/

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

variable (N : ℕ)

/-! ### Gaussian disorder specifications -/

/-- A **centered Gaussian Hamiltonian with prescribed covariance kernel**: a random Hamiltonian
`U : Ω → EnergySpace N` whose law under `P` is Gaussian and centered, and whose covariance operator
has entries `K σ τ` in the Dirac basis. Gaussianity is Mathlib's `HasGaussianLaw`.

The SK and reference disorders of Guerra's interpolation are this structure at two particular
kernels; there is one notion, not three. -/
structure GaussianDisorder (P : Measure Ω) (K : Config N → Config N → ℝ) where
  /-- The (random) Hamiltonian. -/
  U : Ω → EnergySpace N
  /-- Measurability of the Hamiltonian. -/
  measU : Measurable U
  /-- The law of `U` is Gaussian. -/
  hU : ProbabilityTheory.HasGaussianLaw U P
  /-- Centeredness of the disorder (mean zero). -/
  mean0 : (∫ x : EnergySpace N, x ∂(P.map U)) = 0
  /-- The covariance operator has kernel `K` in the Dirac basis. -/
  cov_eq : ∀ σ τ,
    inner ℝ ((ProbabilityTheory.covarianceOperator (P.map U)) (std_basis N σ))
      (std_basis N τ) = K σ τ

namespace GaussianDisorder

variable {N} {P : Measure Ω} {K : Config N → Config N → ℝ}

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The law of a Gaussian disorder is a Gaussian measure. -/
lemma isGaussian (G : GaussianDisorder (Ω := Ω) (N := N) P K) :
    ProbabilityTheory.IsGaussian (P.map G.U) := G.hU.isGaussian_map

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- A Gaussian disorder is integrable. -/
lemma integrable (G : GaussianDisorder (Ω := Ω) (N := N) P K) : Integrable G.U P :=
  G.hU.integrable

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Centeredness read as a Bochner integral over the base space: `𝔼 U = 0`. -/
lemma integral_eq_zero (G : GaussianDisorder (Ω := Ω) (N := N) P K) :
    (∫ ω, G.U ω ∂P) = 0 := by
  have hmap : (∫ x : EnergySpace N, x ∂(P.map G.U)) = ∫ ω, G.U ω ∂P := by
    simpa using (MeasureTheory.integral_map (μ := P) (φ := G.U)
      G.measU.aemeasurable measurable_id.aestronglyMeasurable)
  simpa [hmap] using G.mean0

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The pair of two Gaussian disorders — on possibly *different* systems — is centered. -/
lemma integral_prodMk_eq_zero {N₁ N₂ : ℕ}
    {K₁ : Config N₁ → Config N₁ → ℝ} {K₂ : Config N₂ → Config N₂ → ℝ}
    (G₁ : GaussianDisorder (Ω := Ω) (N := N₁) P K₁)
    (G₂ : GaussianDisorder (Ω := Ω) (N := N₂) P K₂) :
    (∫ ω, (G₁.U ω, G₂.U ω) ∂P) = (0, 0) := by
  have hpair : Integrable (fun ω => (G₁.U ω, G₂.U ω)) P := G₁.integrable.prodMk G₂.integrable
  refine Prod.ext ?_ ?_
  · have hf := ((ContinuousLinearMap.fst ℝ (EnergySpace N₁) (EnergySpace N₂)).integral_comp_comm
      (μ := P) hpair).symm
    simp only [ContinuousLinearMap.coe_fst'] at hf
    rw [hf]; exact G₁.integral_eq_zero
  · have hf := ((ContinuousLinearMap.snd ℝ (EnergySpace N₁) (EnergySpace N₂)).integral_comp_comm
      (μ := P) hpair).symm
    simp only [ContinuousLinearMap.coe_snd'] at hf
    rw [hf]; exact G₂.integral_eq_zero

end GaussianDisorder

/-- SK disorder: a centered Gaussian Hamiltonian with the SK covariance kernel. -/
abbrev SKDisorder (β : ℝ) : Type _ :=
  GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) (sk_cov_kernel N β)

/-- Reference (simple) disorder, for Guerra comparison. -/
abbrev SimpleDisorder (β q : ℝ) : Type _ :=
  GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) (simple_cov_kernel N β (fun x => q * x))

/-! ### Gaussian `L²` self-averaging for the free energy density -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem
    GaussianDisorder.variance_free_energy_density_le
    {N : ℕ} {K : Config N → Config N → ℝ}
    (G : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K) :
    Var[(fun ω : Ω => free_energy_density (N := N) (G.U ω)); (ℙ : Measure Ω)]
      ≤ ‖ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U)‖ *
          (1 / (N : ℝ)) ^ 2 := by
  let μ : Measure (EnergySpace N) := (ℙ : Measure Ω).map G.U
  have : ProbabilityTheory.IsGaussian μ := by
    simpa [μ] using G.isGaussian
  have hmean0 : (∫ x : EnergySpace N, x ∂μ) = 0 := by
    simpa [μ] using G.mean0
  have hX :
      AEMeasurable (fun H : EnergySpace N => free_energy_density (N := N) H) μ := by
    exact (memLp_free_energy_density (N := N) (μ := μ)).1.aemeasurable
  have hY : AEMeasurable G.U (ℙ : Measure Ω) :=
    G.measU.aemeasurable
  have hVarMap :
      Var[(fun H : EnergySpace N => free_energy_density (N := N) H); μ]
        = Var[(fun ω : Ω => free_energy_density (N := N) (G.U ω)); (ℙ : Measure Ω)] := by
    simpa [μ, Function.comp_def] using
      (ProbabilityTheory.variance_map (μ := (ℙ : Measure Ω))
        (X := fun H : EnergySpace N => free_energy_density (N := N) H)
        (Y := G.U) (hX := by simpa [μ] using hX) (hY := hY))
  have hVarBound :
      Var[(fun H : EnergySpace N => free_energy_density (N := N) H); μ]
        ≤ ‖ProbabilityTheory.covarianceOperator μ‖ * (1 / (N : ℝ)) ^ 2 :=
    SpinGlass.variance_free_energy_density_le
      (μ := μ) (N := N) hmean0
  calc
    Var[(fun ω : Ω => free_energy_density (N := N) (G.U ω)); (ℙ : Measure Ω)]
        = Var[(fun H : EnergySpace N => free_energy_density (N := N) H); μ] := by
              simpa using hVarMap.symm
    _ ≤ ‖ProbabilityTheory.covarianceOperator μ‖ * (1 / (N : ℝ)) ^ 2 :=
          hVarBound
    _ = ‖ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U)‖ *
          (1 / (N : ℝ)) ^ 2 := by
          simp [μ]

theorem GaussianDisorder.meas_ge_le_free_energy_density_sub_mean_div_sq
    {N : ℕ} {K : Config N → Config N → ℝ}
    (G : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K) {c : ℝ} (hc : 0 < c) :
    (ℙ : Measure Ω) {ω : Ω |
        c ≤
          |free_energy_density (N := N) (G.U ω)
            - (ℙ : Measure Ω)[fun ω : Ω => free_energy_density (N := N) (G.U ω)]|}
      ≤ ENNReal.ofReal
          ((‖ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U)‖ *
              (1 / (N : ℝ)) ^ 2) / c ^ 2) := by
  let μH : Measure (EnergySpace N) := (ℙ : Measure Ω).map G.U
  have : ProbabilityTheory.IsGaussian μH := by
    simpa [μH] using G.isGaussian
  have hMemH : MemLp (fun H : EnergySpace N => free_energy_density (N := N) H) 2 μH :=
    (SpinGlass.memLp_free_energy_density (N := N) (μ := μH))
  have hMem :
      MemLp (fun ω : Ω => free_energy_density (N := N) (G.U ω)) 2 (ℙ : Measure Ω) := by
    simpa [μH, Function.comp_def] using (hMemH.comp_of_map (f := G.U) (μ := (ℙ : Measure Ω))
      G.measU.aemeasurable)
  have hCheb :
      (ℙ : Measure Ω) {ω : Ω |
          c ≤
            |(fun ω : Ω => free_energy_density (N := N) (G.U ω)) ω
              - (ℙ : Measure Ω)[fun ω : Ω => free_energy_density (N := N) (G.U ω)]|}
        ≤ ENNReal.ofReal
            (Var[(fun ω : Ω => free_energy_density (N := N) (G.U ω)); (ℙ : Measure Ω)] / c ^ 2) :=
    ProbabilityTheory.meas_ge_le_variance_div_sq (μ := (ℙ : Measure Ω))
      (X := fun ω : Ω => free_energy_density (N := N) (G.U ω)) hMem hc
  have hVar :
      Var[(fun ω : Ω => free_energy_density (N := N) (G.U ω)); (ℙ : Measure Ω)]
        ≤ ‖ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U)‖ *
            (1 / (N : ℝ)) ^ 2 :=
    GaussianDisorder.variance_free_energy_density_le
      (Ω := Ω) (G := G)
  have hDiv :
      Var[(fun ω : Ω => free_energy_density (N := N) (G.U ω)); (ℙ : Measure Ω)] / c ^ 2
        ≤
          (‖ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U)‖ *
              (1 / (N : ℝ)) ^ 2) / c ^ 2 :=
    div_le_div_of_nonneg_right hVar (sq_nonneg c)
  have hOfReal :
      ENNReal.ofReal
          (Var[(fun ω : Ω => free_energy_density (N := N) (G.U ω)); (ℙ : Measure Ω)] / c ^ 2)
        ≤
        ENNReal.ofReal
          ((‖ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U)‖ *
              (1 / (N : ℝ)) ^ 2) / c ^ 2) :=
    ENNReal.ofReal_le_ofReal hDiv
  have htail :
      (ℙ : Measure Ω) {ω : Ω |
          c ≤
            |(fun ω : Ω => free_energy_density (N := N) (G.U ω)) ω
              - (ℙ : Measure Ω)[fun ω : Ω => free_energy_density (N := N) (G.U ω)]|}
        ≤ ENNReal.ofReal
            ((‖ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U)‖ *
                (1 / (N : ℝ)) ^ 2) / c ^ 2) :=
    le_trans hCheb hOfReal
  simpa using htail

/-! ### Covariance operator as a kernel expansion -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The coordinates of the covariance operator in the Dirac basis are the kernel entries. -/
lemma GaussianDisorder.covarianceOperator_std_basis_apply
    {N : ℕ} {K : Config N → Config N → ℝ}
    (G : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K) (σ ρ : Config N) :
    (ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U) (std_basis N σ)) ρ
      = K σ ρ := by
  calc
    (ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U) (std_basis N σ)) ρ
        = inner ℝ (std_basis N ρ)
            (ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U) (std_basis N σ)) := by
            simpa using
              (inner_std_basis_apply (N := N) (σ := ρ)
                  (H := ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U) (std_basis
                    N σ))).symm
    _ = inner ℝ
          (ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U) (std_basis N σ))
          (std_basis N ρ) := by simp [real_inner_comm]
    _ = K σ ρ := G.cov_eq σ ρ

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma GaussianDisorder.covarianceOperator_apply_std_basis_eq_sum
    {N : ℕ} {K : Config N → Config N → ℝ}
    (G : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K) (σ : Config N) :
    ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U) (std_basis N σ)
      =
      ∑ τ : Config N, (K σ τ) • std_basis N τ := by
  ext ρ
  have hsum : (∑ τ : Config N, (K σ τ) • std_basis N τ) ρ = K σ ρ := by
    simp [std_basis, FiniteGibbs.std_basis]
  simp [G.covarianceOperator_std_basis_apply σ ρ, hsum]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- **Self-averaging of the free energy, in Talagrand's form.** For a centered Gaussian
Hamiltonian with covariance kernel `K`,

`Var[F_N] ≤ (1/N²) 𝔼 ⟨K(σ¹, σ²)⟩`,

the disorder average of the two-replica Gibbs bracket of the kernel. For a mixed `p`-spin model
`K σ τ = N ξ(R_{στ})` and the bound is `ξ(1)/N`; the operator-norm form
`GaussianDisorder.variance_free_energy_density_le` is far weaker there, since the operator norm of
the covariance on `EnergySpace N` grows with the number of configurations. -/
theorem GaussianDisorder.variance_free_energy_density_le_gibbs_kernel
    {N : ℕ} {K : Config N → Config N → ℝ}
    (G : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K) :
    Var[(fun ω : Ω => free_energy_density (N := N) (G.U ω)); (ℙ : Measure Ω)]
      ≤ (1 / (N : ℝ)) ^ 2 * ∫ H : EnergySpace N,
          gibbs_average₂ N H K ∂((ℙ : Measure Ω).map G.U) := by
  classical
  let μ : Measure (EnergySpace N) := (ℙ : Measure Ω).map G.U
  have : ProbabilityTheory.IsGaussian μ := by simpa [μ] using G.isGaussian
  have hmean0 : (∫ x : EnergySpace N, x ∂μ) = 0 := by simpa [μ] using G.mean0
  have hX : AEMeasurable (fun H : EnergySpace N => free_energy_density (N := N) H) μ :=
    (memLp_free_energy_density (N := N) (μ := μ)).1.aemeasurable
  have hVarMap :
      Var[(fun H : EnergySpace N => free_energy_density (N := N) H); μ]
        = Var[(fun ω : Ω => free_energy_density (N := N) (G.U ω)); (ℙ : Measure Ω)] := by
    simpa [μ, Function.comp_def] using
      (ProbabilityTheory.variance_map (μ := (ℙ : Measure Ω))
        (X := fun H : EnergySpace N => free_energy_density (N := N) H)
        (Y := G.U) (hX := by simpa [μ] using hX) (hY := G.measU.aemeasurable))
  have hbound := variance_free_energy_density_le_gibbs_covariance (N := N) (μ := μ) hmean0
  have hker : (∫ H : EnergySpace N, gibbs_average₂ N H
        (fun σ τ => (ProbabilityTheory.covarianceOperator μ (std_basis N σ)) τ) ∂μ)
      = ∫ H : EnergySpace N, gibbs_average₂ N H K ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun H => ?_)
    simp only [gibbs_average₂]
    exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => by
      rw [G.covarianceOperator_std_basis_apply σ τ]
  rw [← hVarMap]
  simpa [μ, hker] using hbound

/-! ### The law of a Gaussian disorder is determined by its kernel

A centered Gaussian measure on a Hilbert space is determined by its covariance
(`ProbabilityTheory.IsGaussian.ext`), and the covariance of a `GaussianDisorder` is prescribed by
its kernel. So the law of the Hamiltonian — hence every disorder average, the free energy in
particular — depends only on the kernel, not on the probability space carrying it. -/

section Law

variable {N : ℕ} {K : Config N → Config N → ℝ}

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The covariance bilinear form of a centered Gaussian measure whose covariance operator has
kernel `K` in the Dirac basis, expanded in coordinates. -/
private lemma covarianceBilin_of_kernel (μ : Measure (EnergySpace N))
    [ProbabilityTheory.IsGaussian μ] (hmean : (∫ x : EnergySpace N, x ∂μ) = 0)
    (hK : ∀ σ τ, inner ℝ (ProbabilityTheory.covarianceOperator μ (std_basis N σ))
      (std_basis N τ) = K σ τ) (x y : EnergySpace N) :
    ProbabilityTheory.covarianceBilin μ x y
      = ∑ τ : Config N, (∑ ρ : Config N, K τ ρ * x ρ) * y τ := by
  classical
  have hmem : MeasureTheory.MemLp (id : EnergySpace N → EnergySpace N) 2 μ :=
    ProbabilityTheory.IsGaussian.memLp_two_id
  have hbil : ∀ u v : EnergySpace N, ProbabilityTheory.covarianceBilin μ u v
      = inner ℝ (ProbabilityTheory.covarianceOperator μ u) v := by
    intro u v
    rw [ProbabilityTheory.covarianceBilin_apply hmem,
      ProbabilityTheory.covarianceOperator_inner hmem]
    simp [hmean]
  have hCe : ∀ τ : Config N, ProbabilityTheory.covarianceOperator μ (std_basis N τ)
      = WithLp.toLp 2 (fun ρ : Config N => K τ ρ) := by
    intro τ
    ext ρ
    have h := hK τ ρ
    rw [real_inner_comm] at h
    simpa [inner_std_basis_apply] using h
  have hcoord : ∀ τ : Config N,
      (ProbabilityTheory.covarianceOperator μ x) τ = ∑ ρ : Config N, K τ ρ * x ρ := by
    intro τ
    have h1 : (ProbabilityTheory.covarianceOperator μ x) τ
        = inner ℝ (ProbabilityTheory.covarianceOperator μ x) (std_basis N τ) := by
      rw [real_inner_comm, inner_std_basis_apply]
    rw [h1, ← hbil x (std_basis N τ), ProbabilityTheory.covarianceBilin_comm,
      hbil (std_basis N τ) x, hCe τ]
    simp [PiLp.inner_apply, mul_comm]
  rw [hbil, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [hcoord τ]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- **The law of a centered Gaussian disorder is determined by its covariance kernel.** Two
Gaussian Hamiltonians with the same kernel — carried by any two probability spaces — have the same
law. Hence every disorder average, the free energy in particular, is a function of the kernel
alone. -/
theorem GaussianDisorder.map_U_eq {Ω' : Type*} [MeasureSpace Ω']
    (G : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K)
    (G' : GaussianDisorder (Ω := Ω') (N := N) (ℙ : Measure Ω') K) :
    (ℙ : Measure Ω).map G.U = (ℙ : Measure Ω').map G'.U := by
  have hμ : ProbabilityTheory.IsGaussian ((ℙ : Measure Ω).map G.U) := G.isGaussian
  have hν : ProbabilityTheory.IsGaussian ((ℙ : Measure Ω').map G'.U) := G'.isGaussian
  refine ProbabilityTheory.IsGaussian.ext ?_ ?_
  · simp [G.mean0, G'.mean0]
  · ext x y
    rw [covarianceBilin_of_kernel (K := K) _ G.mean0 G.cov_eq x y,
      covarianceBilin_of_kernel (K := K) _ G'.mean0 G'.cov_eq x y]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- **Every disorder average depends only on the covariance kernel.** -/
theorem GaussianDisorder.integral_comp_eq {Ω' : Type*} [MeasureSpace Ω']
    (G : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K)
    (G' : GaussianDisorder (Ω := Ω') (N := N) (ℙ : Measure Ω') K)
    (f : EnergySpace N → ℝ) (hf : AEStronglyMeasurable f ((ℙ : Measure Ω).map G.U)) :
    (∫ ω, f (G.U ω) ∂(ℙ : Measure Ω)) = ∫ ω, f (G'.U ω) ∂(ℙ : Measure Ω') := by
  have hf' : AEStronglyMeasurable f ((ℙ : Measure Ω').map G'.U) := by
    rwa [← GaussianDisorder.map_U_eq G G']
  rw [← MeasureTheory.integral_map G.measU.aemeasurable hf,
    ← MeasureTheory.integral_map G'.measU.aemeasurable hf',
    GaussianDisorder.map_U_eq G G']

end Law

/-! ### Product disorder space -/

/-- The Hilbert `L²`-product space carrying the pair `(U,V)`. -/
abbrev DisorderSpace (N : ℕ) := WithLp 2 (EnergySpace N × EnergySpace N)

/-! ### Product-space basis vectors -/

/-- The Dirac basis vector of the first (SK-disorder) block of `DisorderSpace`. -/
noncomputable def std_basis_left (σ : Config N) : DisorderSpace (N := N) :=
  WithLp.toLp 2 (std_basis N σ, 0)

/-- The Dirac basis vector of the second (reference-disorder) block of `DisorderSpace`. -/
noncomputable def std_basis_right (σ : Config N) : DisorderSpace (N := N) :=
  WithLp.toLp 2 (0, std_basis N σ)

lemma inner_apply_std_basis_left (σ : Config N) (uv : DisorderSpace (N := N)) :
    inner ℝ uv (std_basis_left (N := N) σ) = ((WithLp.ofLp uv).1) σ := by
  classical
  simp [SpinGlass.DisorderSpace, std_basis_left, WithLp.prod_inner_apply, inner_std_basis_apply,
    real_inner_comm]

lemma inner_apply_std_basis_right (σ : Config N) (uv : DisorderSpace (N := N)) :
    inner ℝ uv (std_basis_right (N := N) σ) = ((WithLp.ofLp uv).2) σ := by
  classical
  simp [SpinGlass.DisorderSpace, std_basis_right, WithLp.prod_inner_apply, inner_std_basis_apply,
    real_inner_comm]

/-! ### The disorder pair

Two Gaussian disorders at **arbitrary** covariance kernels `K₁`, `K₂`, repackaged as a single
random vector of the `L²` product `DisorderSpace N`. Nothing in this section mentions the SK or
the reference kernel: Guerra's interpolation, the Guerra–Toninelli splitting interpolation, and
every other two-Hamiltonian smart path consume this layer at their own pair of kernels. -/

section DisorderPair

variable {K₁ K₂ : Config N → Config N → ℝ}

/-- The disorder pair `(U,V)` repackaged as an element of `DisorderSpace`. -/
noncomputable def disorderPair
    (G₁ : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K₁)
    (G₂ : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K₂) :
    Ω → DisorderSpace (N := N) :=
  fun ω => WithLp.toLp 2 (G₁.U ω, G₂.U ω)

/-- The law of the repackaged disorder pair. -/
noncomputable abbrev disorderPairLaw
    (G₁ : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K₁)
    (G₂ : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K₂) :
    Measure (DisorderSpace (N := N)) :=
  (ℙ : Measure Ω).map (disorderPair (Ω := Ω) (N := N) G₁ G₂)

variable (G₁ : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K₁)
  (G₂ : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K₂)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
@[simp] lemma disorderPair_fst (ω : Ω) :
    (WithLp.ofLp (disorderPair (Ω := Ω) (N := N) G₁ G₂ ω)).1 = G₁.U ω := by
  simp [disorderPair]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
@[simp] lemma disorderPair_snd (ω : Ω) :
    (WithLp.ofLp (disorderPair (Ω := Ω) (N := N) G₁ G₂ ω)).2 = G₂.U ω := by
  simp [disorderPair]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma measurable_disorderPair :
    Measurable (disorderPair (Ω := Ω) (N := N) G₁ G₂) :=
  (WithLp.measurable_toLp (p := (2 : ℝ≥0∞))
    (X := (EnergySpace N × EnergySpace N))).comp (G₁.measU.prodMk G₂.measU)

/-- The `L²`-linear equivalence `DisorderSpace N ≃L EnergySpace N × EnergySpace N`. -/
private noncomputable def disorderProdEquiv :
    DisorderSpace (N := N) ≃L[ℝ] (EnergySpace N × EnergySpace N) :=
  WithLp.prodContinuousLinearEquiv (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
    (α := EnergySpace N) (β := EnergySpace N)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma integrable_disorderPair :
    Integrable (disorderPair (Ω := Ω) (N := N) G₁ G₂) (ℙ : Measure Ω) := by
  have hpair : Integrable (fun ω => (G₁.U ω, G₂.U ω)) (ℙ : Measure Ω) :=
    G₁.integrable.prodMk G₂.integrable
  have h := (disorderProdEquiv (N := N)).symm.toContinuousLinearMap.integrable_comp hpair
  have hfun : (fun ω => (disorderProdEquiv (N := N)).symm.toContinuousLinearMap
      (G₁.U ω, G₂.U ω)) = disorderPair (Ω := Ω) (N := N) G₁ G₂ := rfl
  rwa [hfun] at h

/-! ### Mean zero of `disorderPairLaw` -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma disorderPair_integral_eq_zero :
    (∫ ω, disorderPair (Ω := Ω) (N := N) G₁ G₂ ω ∂(ℙ : Measure Ω)) = 0 := by
  -- Push the integral through the continuous linear equivalence to the product space.
  set e := disorderProdEquiv (N := N) with he_def
  have hint := integrable_disorderPair (Ω := Ω) (N := N) G₁ G₂
  have hpair_int : Integrable (fun ω => (G₁.U ω, G₂.U ω)) (ℙ : Measure Ω) :=
    G₁.integrable.prodMk G₂.integrable
  have hpair : (∫ ω, (G₁.U ω, G₂.U ω) ∂(ℙ : Measure Ω)) = (0, 0) :=
    GaussianDisorder.integral_prodMk_eq_zero G₁ G₂
  refine e.injective ?_
  have hcomm := e.toContinuousLinearMap.integral_comp_comm (μ := (ℙ : Measure Ω)) hint
  have hsimp : (fun ω => e (disorderPair (Ω := Ω) (N := N) G₁ G₂ ω))
      = fun ω => (G₁.U ω, G₂.U ω) := rfl
  simp only [ContinuousLinearEquiv.coe_coe] at hcomm
  rw [← hcomm, hsimp, hpair]
  simp

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma disorderPairLaw_mean0 :
    (∫ x : DisorderSpace (N := N),
        x ∂(disorderPairLaw (Ω := Ω) (N := N) G₁ G₂)) = 0 := by
  simpa [disorderPairLaw] using
    (MeasureTheory.integral_map (μ := (ℙ : Measure Ω))
      (φ := disorderPair (Ω := Ω) (N := N) G₁ G₂)
      (measurable_disorderPair (Ω := Ω) (N := N) G₁ G₂).aemeasurable
      (measurable_id.aestronglyMeasurable)).trans
      (disorderPair_integral_eq_zero (Ω := Ω) (N := N) G₁ G₂)

/-! ### Joint Gaussianity -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Two **independent** Gaussian disorders are jointly Gaussian on the `L²` product. This is the
form instance search consumes: the law is written at the explicit repackaging map. -/
lemma isGaussian_map_toLp_prodMk_of_indep
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) :
    ProbabilityTheory.IsGaussian
      ((ℙ : Measure Ω).map fun ω => WithLp.toLp 2 (G₁.U ω, G₂.U ω)) := by
  have : Fact ((1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hXY : ProbabilityTheory.HasGaussianLaw (fun ω => (G₁.U ω, G₂.U ω)) (ℙ : Measure Ω) :=
    ProbabilityTheory.IndepFun.hasGaussianLaw (P := (ℙ : Measure Ω)) G₁.hU G₂.hU hindep
  exact (ProbabilityTheory.HasGaussianLaw.toLp_prodMk (X := G₁.U) (Y := G₂.U)
    (P := (ℙ : Measure Ω)) (p := (2 : ℝ≥0∞)) hXY).isGaussian_map

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The law of the disorder pair of two independent Gaussian disorders is a Gaussian measure on
`DisorderSpace N`. -/
lemma isGaussian_disorderPairLaw_of_indep
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) :
    ProbabilityTheory.IsGaussian (disorderPairLaw (Ω := Ω) (N := N) G₁ G₂) :=
  isGaussian_map_toLp_prodMk_of_indep (Ω := Ω) (N := N) G₁ G₂ hindep

/-! ### Covariance of `disorderPairLaw`

The joint law of an independent pair is block diagonal, so its covariance operator restricted to
either block is the covariance of that marginal. This is Mathlib's
`ProbabilityTheory.covarianceOperator_map_toLp_prodMk_left/right` read at a disorder pair. -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The covariance of the joint disorder law on the first block. -/
lemma covarianceOperator_disorderPairLaw_std_basis_left
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) (σ : Config N) :
    ProbabilityTheory.covarianceOperator (disorderPairLaw (Ω := Ω) (N := N) G₁ G₂)
        (std_basis_left (N := N) σ) = WithLp.toLp 2
        (ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G₁.U) (std_basis N σ), 0) := by
  have := G₁.isGaussian
  have := G₂.isGaussian
  have := isGaussian_map_toLp_prodMk_of_indep (Ω := Ω) (N := N) G₁ G₂ hindep
  exact ProbabilityTheory.covarianceOperator_map_toLp_prodMk_left G₁.measU G₂.measU hindep
    G₁.integral_eq_zero G₂.integral_eq_zero (std_basis N σ)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The covariance of the joint disorder law on the second block. -/
lemma covarianceOperator_disorderPairLaw_std_basis_right
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) (σ : Config N) :
    ProbabilityTheory.covarianceOperator (disorderPairLaw (Ω := Ω) (N := N) G₁ G₂)
        (std_basis_right (N := N) σ) = WithLp.toLp 2
        (0, ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G₂.U) (std_basis N σ)) := by
  have := G₁.isGaussian
  have := G₂.isGaussian
  have := isGaussian_map_toLp_prodMk_of_indep (Ω := Ω) (N := N) G₁ G₂ hindep
  exact ProbabilityTheory.covarianceOperator_map_toLp_prodMk_right G₁.measU G₂.measU hindep
    G₁.integral_eq_zero G₂.integral_eq_zero (std_basis N σ)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The covariance of the joint disorder law on the first block, expanded in the Dirac basis of
that block: the entries are the kernel `K₁` of the first disorder. -/
lemma covarianceOperator_disorderPairLaw_std_basis_left_eq_sum
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) (σ : Config N) :
    ProbabilityTheory.covarianceOperator (disorderPairLaw (Ω := Ω) (N := N) G₁ G₂)
        (std_basis_left (N := N) σ)
      = ∑ τ : Config N, (K₁ σ τ) • std_basis_left (N := N) τ := by
  classical
  refine (WithLp.ofLp_injective (p := (2 : ℝ≥0∞)) (V := EnergySpace N × EnergySpace N)) ?_
  rw [covarianceOperator_disorderPairLaw_std_basis_left (Ω := Ω) (N := N) G₁ G₂ hindep σ]
  have hR : WithLp.ofLp (∑ τ : Config N, (K₁ σ τ) • std_basis_left (N := N) τ)
      = ∑ τ : Config N, (K₁ σ τ) • (std_basis N τ, (0 : EnergySpace N)) := by
    simp [std_basis_left]
  rw [hR]
  refine Prod.ext ?_ ?_
  · simpa [Prod.fst_sum] using G₁.covarianceOperator_apply_std_basis_eq_sum σ
  · simp [Prod.snd_sum]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The covariance of the joint disorder law on the second block, expanded in the Dirac basis of
that block: the entries are the kernel `K₂` of the second disorder. -/
lemma covarianceOperator_disorderPairLaw_std_basis_right_eq_sum
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) (σ : Config N) :
    ProbabilityTheory.covarianceOperator (disorderPairLaw (Ω := Ω) (N := N) G₁ G₂)
        (std_basis_right (N := N) σ)
      = ∑ τ : Config N, (K₂ σ τ) • std_basis_right (N := N) τ := by
  classical
  refine (WithLp.ofLp_injective (p := (2 : ℝ≥0∞)) (V := EnergySpace N × EnergySpace N)) ?_
  rw [covarianceOperator_disorderPairLaw_std_basis_right (Ω := Ω) (N := N) G₁ G₂ hindep σ]
  have hR : WithLp.ofLp (∑ τ : Config N, (K₂ σ τ) • std_basis_right (N := N) τ)
      = ∑ τ : Config N, (K₂ σ τ) • ((0 : EnergySpace N), std_basis N τ) := by
    simp [std_basis_right]
  rw [hR]
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum]
  · simpa [Prod.snd_sum] using G₂.covarianceOperator_apply_std_basis_eq_sum σ

end DisorderPair


end SpinGlass
