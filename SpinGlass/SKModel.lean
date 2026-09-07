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
      ≤ (Real.pi ^ 2 / 8) * ‖ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U)‖ *
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
        ≤ (Real.pi ^ 2 / 8) * ‖ProbabilityTheory.covarianceOperator μ‖ * (1 / (N : ℝ)) ^ 2 :=
    SpinGlass.variance_free_energy_density_le
      (μ := μ) (N := N) hmean0
  calc
    Var[(fun ω : Ω => free_energy_density (N := N) (G.U ω)); (ℙ : Measure Ω)]
        = Var[(fun H : EnergySpace N => free_energy_density (N := N) H); μ] := by
              simpa using hVarMap.symm
    _ ≤ (Real.pi ^ 2 / 8) * ‖ProbabilityTheory.covarianceOperator μ‖ * (1 / (N : ℝ)) ^ 2 :=
          hVarBound
    _ = (Real.pi ^ 2 / 8) * ‖ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U)‖ *
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
          (((Real.pi ^ 2 / 8) * ‖ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U)‖ *
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
        ≤ (Real.pi ^ 2 / 8) * ‖ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U)‖ *
            (1 / (N : ℝ)) ^ 2 :=
    GaussianDisorder.variance_free_energy_density_le
      (Ω := Ω) (G := G)
  have hDiv :
      Var[(fun ω : Ω => free_energy_density (N := N) (G.U ω)); (ℙ : Measure Ω)] / c ^ 2
        ≤
          ((Real.pi ^ 2 / 8) * ‖ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U)‖ *
              (1 / (N : ℝ)) ^ 2) / c ^ 2 :=
    div_le_div_of_nonneg_right hVar (sq_nonneg c)
  have hOfReal :
      ENNReal.ofReal
          (Var[(fun ω : Ω => free_energy_density (N := N) (G.U ω)); (ℙ : Measure Ω)] / c ^ 2)
        ≤
        ENNReal.ofReal
          (((Real.pi ^ 2 / 8) * ‖ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U)‖ *
              (1 / (N : ℝ)) ^ 2) / c ^ 2) :=
    ENNReal.ofReal_le_ofReal hDiv
  have htail :
      (ℙ : Measure Ω) {ω : Ω |
          c ≤
            |(fun ω : Ω => free_energy_density (N := N) (G.U ω)) ω
              - (ℙ : Measure Ω)[fun ω : Ω => free_energy_density (N := N) (G.U ω)]|}
        ≤ ENNReal.ofReal
            (((Real.pi ^ 2 / 8) * ‖ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U)‖ *
                (1 / (N : ℝ)) ^ 2) / c ^ 2) :=
    le_trans hCheb hOfReal
  simpa using htail

/-! ### Covariance operator as a kernel expansion -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma GaussianDisorder.covarianceOperator_apply_std_basis_eq_sum
    {N : ℕ} {K : Config N → Config N → ℝ}
    (G : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K) (σ : Config N) :
    ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U) (std_basis N σ)
      =
      ∑ τ : Config N, (K σ τ) • std_basis N τ := by
  ext ρ
  have hcoord :
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
  have hsum : (∑ τ : Config N, (K σ τ) • std_basis N τ) ρ = K σ ρ := by
    simp [std_basis, FiniteGibbs.std_basis]
  simp [hcoord, hsum]

/-! ### Product disorder space -/

/-- The Hilbert `L²`-product space carrying the pair `(U,V)`. -/
abbrev DisorderSpace (N : ℕ) := WithLp 2 (EnergySpace N × EnergySpace N)

/-! ### Product-space basis vectors -/

noncomputable def std_basis_left (σ : Config N) : DisorderSpace (N := N) :=
  WithLp.toLp 2 (std_basis N σ, 0)

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

/-- The disorder pair `(U,V)` repackaged as an element of `DisorderSpace`. -/
noncomputable def disorderPair (N : ℕ) (β q : ℝ)
    (sk : SKDisorder (Ω := Ω) N β) (sim : SimpleDisorder (Ω := Ω) N β q) :
    Ω → DisorderSpace (N := N) :=
  fun ω => WithLp.toLp 2 (sk.U ω, sim.U ω)

/-- The law of the repackaged disorder pair. -/
noncomputable abbrev disorderPairLaw (N : ℕ) (β q : ℝ)
    (sk : SKDisorder (Ω := Ω) N β) (sim : SimpleDisorder (Ω := Ω) N β q) :
    Measure (DisorderSpace (N := N)) :=
  (ℙ : Measure Ω).map (disorderPair (Ω := Ω) (N := N) (β := β) (q := q) (sk := sk) (sim :=
    sim))

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
@[simp] lemma disorderPair_fst (N : ℕ) (β q : ℝ)
    (sk : SKDisorder (Ω := Ω) N β) (sim : SimpleDisorder (Ω := Ω) N β q) (ω : Ω) :
    (WithLp.ofLp (disorderPair (Ω := Ω) (N := N) (β := β) (q := q) (sk := sk) (sim := sim)
      ω)).1
      = sk.U ω := by
  simp [disorderPair]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
@[simp] lemma disorderPair_snd (N : ℕ) (β q : ℝ)
    (sk : SKDisorder (Ω := Ω) N β) (sim : SimpleDisorder (Ω := Ω) N β q) (ω : Ω) :
    (WithLp.ofLp (disorderPair (Ω := Ω) (N := N) (β := β) (q := q) (sk := sk) (sim := sim)
      ω)).2
      = sim.U ω := by
  simp [disorderPair]

/-! ### Mean zero of `disorderPairLaw` -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma SKDisorder.integral_eq_zero_of_mean0
    {N : ℕ} {β : ℝ} (sk : SKDisorder (Ω := Ω) N β) :
    (∫ ω, sk.U ω ∂(ℙ : Measure Ω)) = 0 := by
  have hmap :
      (∫ x : EnergySpace N, x ∂((ℙ : Measure Ω).map sk.U))
        = ∫ ω, sk.U ω ∂(ℙ : Measure Ω) := by
    simpa using
      (MeasureTheory.integral_map (μ := (ℙ : Measure Ω)) (φ := sk.U)
        sk.measU.aemeasurable (measurable_id.aestronglyMeasurable))
  simpa [hmap] using sk.mean0

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma SimpleDisorder.integral_eq_zero_of_mean0
    {N : ℕ} {β q : ℝ} (sim : SimpleDisorder (Ω := Ω) N β q) :
    (∫ ω, sim.U ω ∂(ℙ : Measure Ω)) = 0 := by
  have hmap :
      (∫ x : EnergySpace N, x ∂((ℙ : Measure Ω).map sim.U))
        = ∫ ω, sim.U ω ∂(ℙ : Measure Ω) := by
    simpa using
      (MeasureTheory.integral_map (μ := (ℙ : Measure Ω)) (φ := sim.U)
        sim.measU.aemeasurable (measurable_id.aestronglyMeasurable))
  simpa [hmap] using sim.mean0

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma disorderPair_integral_eq_zero
    {N : ℕ} {β q : ℝ} (sk : SKDisorder (Ω := Ω) N β) (sim : SimpleDisorder (Ω := Ω) N β q) :
    (∫ ω, disorderPair (Ω := Ω) (N := N) (β := β) (q := q) (sk := sk) (sim := sim) ω
        ∂(ℙ : Measure Ω))
      = 0 := by
  -- Use the continuous linear equivalence `ofLp : DisorderSpace ≃L E×F` to reduce to the product.
  let e : DisorderSpace (N := N) ≃L[ℝ] (EnergySpace N × EnergySpace N) :=
    WithLp.prodContinuousLinearEquiv (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
      (α := EnergySpace N) (β := EnergySpace N)
  have hint : Integrable (disorderPair (Ω := Ω) (N := N) (β := β) (q := q) (sk := sk) (sim
    := sim))
      (ℙ : Measure Ω) := by
    -- Gaussian implies integrable; we use `HasGaussianLaw` on each marginal and the continuity of
    -- `toLp`.
    have hX : ProbabilityTheory.HasGaussianLaw sk.U (ℙ : Measure Ω) := sk.hU
    have hY : ProbabilityTheory.HasGaussianLaw sim.U (ℙ : Measure Ω) := sim.hU
    have hpair : Integrable (fun ω => (sk.U ω, sim.U ω)) (ℙ : Measure Ω) :=
      (Integrable.prodMk hX.integrable hY.integrable)
    -- `toLp` is continuous linear.
    have : Integrable (fun ω => e.symm (sk.U ω, sim.U ω)) (ℙ : Measure Ω) :=
      (e.symm.toContinuousLinearMap.integrable_comp hpair)
    convert this using 1
    ext ω
    simp [disorderPair, e]
  have : e (∫ ω, disorderPair (Ω := Ω) (N := N) (β := β) (q := q) (sk := sk) (sim := sim) ω
        ∂(ℙ : Measure Ω))
      = 0 := by
    have hU0 := SKDisorder.integral_eq_zero_of_mean0 (Ω := Ω) (N := N) sk
    have hV0 := SimpleDisorder.integral_eq_zero_of_mean0 (Ω := Ω) (N := N) sim
    have hpair_int : Integrable (fun ω => (sk.U ω, sim.U ω)) (ℙ : Measure Ω) := by
      have hX : ProbabilityTheory.HasGaussianLaw sk.U (ℙ : Measure Ω) := sk.hU
      have hY : ProbabilityTheory.HasGaussianLaw sim.U (ℙ : Measure Ω) := sim.hU
      exact Integrable.prodMk hX.integrable hY.integrable
    have hpair : (∫ ω, (sk.U ω, sim.U ω) ∂(ℙ : Measure Ω)) = (0, 0) := by
      refine Prod.ext ?_ ?_
      · let fstL : (EnergySpace N × EnergySpace N) →L[ℝ] EnergySpace N :=
          ContinuousLinearMap.fst ℝ (EnergySpace N) (EnergySpace N)
        have hf : fstL (∫ ω, (sk.U ω, sim.U ω) ∂(ℙ : Measure Ω))
            = ∫ ω, fstL (sk.U ω, sim.U ω) ∂(ℙ : Measure Ω) := by
          simpa using (fstL.integral_comp_comm (μ := (ℙ : Measure Ω)) hpair_int).symm
        calc
          (∫ ω, (sk.U ω, sim.U ω) ∂(ℙ : Measure Ω)).1
              = fstL (∫ ω, (sk.U ω, sim.U ω) ∂(ℙ : Measure Ω)) := by rfl
          _ = ∫ ω, sk.U ω ∂(ℙ : Measure Ω) := by simpa [fstL] using hf
          _ = 0 := hU0
      · let sndL : (EnergySpace N × EnergySpace N) →L[ℝ] EnergySpace N :=
          ContinuousLinearMap.snd ℝ (EnergySpace N) (EnergySpace N)
        have hf : sndL (∫ ω, (sk.U ω, sim.U ω) ∂(ℙ : Measure Ω))
            = ∫ ω, sndL (sk.U ω, sim.U ω) ∂(ℙ : Measure Ω) := by
          simpa using (sndL.integral_comp_comm (μ := (ℙ : Measure Ω)) hpair_int).symm
        calc
          (∫ ω, (sk.U ω, sim.U ω) ∂(ℙ : Measure Ω)).2
              = sndL (∫ ω, (sk.U ω, sim.U ω) ∂(ℙ : Measure Ω)) := by rfl
          _ = ∫ ω, sim.U ω ∂(ℙ : Measure Ω) := by simpa [sndL] using hf
          _ = 0 := hV0
    have he :
        e (∫ ω, disorderPair (Ω := Ω) (N := N) (β := β) (q := q) (sk := sk) (sim := sim) ω
            ∂(ℙ : Measure Ω))
          =
        ∫ ω, (sk.U ω, sim.U ω) ∂(ℙ : Measure Ω) := by
      have hcomm :=
        (e.toContinuousLinearMap.integral_comp_comm (μ := (ℙ : Measure Ω)) hint)
      have hsimp :
          (fun ω => e (disorderPair (Ω := Ω) (N := N) (β := β) (q := q)
              (sk := sk) (sim := sim) ω))
            = fun ω => (sk.U ω, sim.U ω) := by
        funext ω
        simp [disorderPair, e]
      simpa [hsimp] using hcomm.symm
    simp [he, hpair]
  exact e.injective this

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma disorderPairLaw_mean0
    {N : ℕ} {β q : ℝ} (sk : SKDisorder (Ω := Ω) N β) (sim : SimpleDisorder (Ω := Ω) N β q) :
    (∫ x : DisorderSpace (N := N),
        x ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (q := q) (sk := sk) (sim := sim)))
      = 0 := by
  have hmeas : Measurable (disorderPair (Ω := Ω) (N := N) (β := β) (q := q) (sk := sk) (sim
    := sim)) := by
    have hpair : Measurable fun ω : Ω => (sk.U ω, sim.U ω) := sk.measU.prodMk sim.measU
    convert (WithLp.prod_continuous_toLp (p := (2 : ℝ≥0∞))
      (α := EnergySpace N) (β := EnergySpace N)).measurable.comp hpair using 1
    ext ω
    simp [disorderPair]
  simpa [disorderPairLaw] using
    (MeasureTheory.integral_map (μ := (ℙ : Measure Ω))
      (φ := disorderPair (Ω := Ω) (N := N) (β := β) (q := q) (sk := sk) (sim := sim))
      (hmeas.aemeasurable) (measurable_id.aestronglyMeasurable)).trans
      (disorderPair_integral_eq_zero
 (Ω := Ω) (N := N) (β := β) (q := q) sk sim)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Independent Gaussian disorders are jointly Gaussian on the product space. -/
lemma SKDisorder.simple_joint_isGaussian_of_indep
    {β q : ℝ} (sk : SKDisorder (Ω := Ω) (N := N) β) (sim : SimpleDisorder (Ω := Ω) (N := N) β q)
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.U) :
    ProbabilityTheory.IsGaussian
      (((ℙ : Measure Ω).map fun ω => (sk.U ω, sim.U ω))) := by
  have hX : ProbabilityTheory.HasGaussianLaw sk.U (ℙ : Measure Ω) :=
    sk.hU
  have hY : ProbabilityTheory.HasGaussianLaw sim.U (ℙ : Measure Ω) :=
    sim.hU
  exact (ProbabilityTheory.IndepFun.hasGaussianLaw (P := (ℙ : Measure Ω)) hX hY
    hindep).isGaussian_map

open scoped ENNReal

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Joint Gaussianity of `(U,V)` on `WithLp 2 (E × F)`. -/
lemma SKDisorder.simple_joint_isGaussian_withLp_of_indep
    {β q : ℝ} (sk : SKDisorder (Ω := Ω) (N := N) β) (sim : SimpleDisorder (Ω := Ω) (N := N) β q)
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.U) :
    ProbabilityTheory.IsGaussian
      (((ℙ : Measure Ω).map fun ω => WithLp.toLp 2 (sk.U ω, sim.U ω))) := by
  -- Use the canonical `HasGaussianLaw` lemma that already repackages via `toLp`.
  have hX : ProbabilityTheory.HasGaussianLaw sk.U (ℙ : Measure Ω) := sk.hU
  have hY : ProbabilityTheory.HasGaussianLaw sim.U (ℙ : Measure Ω) := sim.hU
  have hXY : ProbabilityTheory.HasGaussianLaw (fun ω => (sk.U ω, sim.U ω)) (ℙ : Measure Ω) :=
    ProbabilityTheory.IndepFun.hasGaussianLaw (P := (ℙ : Measure Ω)) hX hY hindep
  have htoLp : ProbabilityTheory.HasGaussianLaw
      (fun ω => WithLp.toLp (p := (2 : ℝ≥0∞)) (sk.U ω, sim.U ω)) (ℙ : Measure Ω) := by
    have : Fact ((1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
    exact ProbabilityTheory.HasGaussianLaw.toLp_prodMk (X := sk.U) (Y := sim.U)
      (P := (ℙ : Measure Ω)) (p := (2 : ℝ≥0∞)) hXY
  exact htoLp.isGaussian_map

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma SKDisorder.simple_joint_isGaussian_disorderPairLaw_of_indep
    {N : ℕ} {β q : ℝ} (sk : SKDisorder (Ω := Ω) N β) (sim : SimpleDisorder (Ω := Ω) N β q)
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.U) :
    ProbabilityTheory.IsGaussian
      (disorderPairLaw (Ω := Ω) (N := N) (β := β) (q := q) (sk := sk) (sim := sim)) :=
  SKDisorder.simple_joint_isGaussian_withLp_of_indep (Ω := Ω) (N := N) sk sim hindep

/-! ### Covariance of `disorderPairLaw` -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The covariance of the joint disorder law on the SK block. This is the general block-diagonal
covariance of the `L²`-joint law of an independent pair
(`ProbabilityTheory.covarianceOperator_map_toLp_prodMk_left`) at the SK disorder. -/
lemma covarianceOperator_disorderPairLaw_std_basis_left
    {N : ℕ} {β q : ℝ} (sk : SKDisorder (Ω := Ω) N β) (sim : SimpleDisorder (Ω := Ω) N β q)
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.U) (σ : Config N) :
    ProbabilityTheory.covarianceOperator
        (disorderPairLaw (Ω := Ω) (N := N) (β := β) (q := q) (sk := sk) (sim := sim))
        (std_basis_left (N := N) σ) = WithLp.toLp 2
        (ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map sk.U) (std_basis N σ), 0) := by
  have hgU : ProbabilityTheory.IsGaussian ((ℙ : Measure Ω).map sk.U) := sk.isGaussian
  have hgV : ProbabilityTheory.IsGaussian ((ℙ : Measure Ω).map sim.U) := sim.isGaussian
  have hgJ : ProbabilityTheory.IsGaussian
      ((ℙ : Measure Ω).map fun ω => WithLp.toLp 2 (sk.U ω, sim.U ω)) :=
    SKDisorder.simple_joint_isGaussian_withLp_of_indep (Ω := Ω) (N := N) sk sim hindep
  exact ProbabilityTheory.covarianceOperator_map_toLp_prodMk_left sk.measU sim.measU hindep
    (SKDisorder.integral_eq_zero_of_mean0 (Ω := Ω) (N := N) sk)
    (SimpleDisorder.integral_eq_zero_of_mean0 (Ω := Ω) (N := N) sim) (std_basis N σ)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The covariance of the joint disorder law on the reference block. -/
lemma covarianceOperator_disorderPairLaw_std_basis_right
    {N : ℕ} {β q : ℝ} (sk : SKDisorder (Ω := Ω) N β) (sim : SimpleDisorder (Ω := Ω) N β q)
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.U) (σ : Config N) :
    ProbabilityTheory.covarianceOperator
        (disorderPairLaw (Ω := Ω) (N := N) (β := β) (q := q) (sk := sk) (sim := sim))
        (std_basis_right (N := N) σ) = WithLp.toLp 2
        (0, ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map sim.U) (std_basis N σ)) := by
  have hgU : ProbabilityTheory.IsGaussian ((ℙ : Measure Ω).map sk.U) := sk.isGaussian
  have hgV : ProbabilityTheory.IsGaussian ((ℙ : Measure Ω).map sim.U) := sim.isGaussian
  have hgJ : ProbabilityTheory.IsGaussian
      ((ℙ : Measure Ω).map fun ω => WithLp.toLp 2 (sk.U ω, sim.U ω)) :=
    SKDisorder.simple_joint_isGaussian_withLp_of_indep (Ω := Ω) (N := N) sk sim hindep
  exact ProbabilityTheory.covarianceOperator_map_toLp_prodMk_right sk.measU sim.measU hindep
    (SKDisorder.integral_eq_zero_of_mean0 (Ω := Ω) (N := N) sk)
    (SimpleDisorder.integral_eq_zero_of_mean0 (Ω := Ω) (N := N) sim) (std_basis N σ)


omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma covarianceOperator_disorderPairLaw_std_basis_left_eq_sum_sk
    {N : ℕ} {β q : ℝ} (sk : SKDisorder (Ω := Ω) N β) (sim : SimpleDisorder (Ω := Ω) N β q)
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.U) (σ : Config N) :
    ProbabilityTheory.covarianceOperator
        (disorderPairLaw (Ω := Ω) (N := N) (β := β) (q := q) (sk := sk) (sim := sim))
        (std_basis_left (N := N) σ)
      =
      ∑ τ : Config N, (sk_cov_kernel N β σ τ) • std_basis_left (N := N) τ := by
  classical
  have hdiag :=
    covarianceOperator_disorderPairLaw_std_basis_left
      (Ω := Ω) (N := N) (β := β) (q := q) (sk := sk) (sim := sim) hindep σ
  have hsumU :
      ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map sk.U) (std_basis N σ)
        =
        ∑ τ : Config N, (sk_cov_kernel N β σ τ) • std_basis N τ :=
    GaussianDisorder.covarianceOperator_apply_std_basis_eq_sum (Ω := Ω) (N := N) sk σ
  refine (WithLp.ofLp_injective (p := (2 : ℝ≥0∞)) (V := EnergySpace N × EnergySpace N)) ?_
  have hL :
      WithLp.ofLp
          (ProbabilityTheory.covarianceOperator
              (disorderPairLaw (Ω := Ω) (N := N) (β := β) (q := q) (sk := sk) (sim := sim))
              (std_basis_left (N := N) σ))
        =
        (ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map sk.U) (std_basis N σ), 0) := by
    simp [hdiag]
  have hR :
      WithLp.ofLp (∑ τ : Config N, (sk_cov_kernel N β σ τ) • std_basis_left (N := N) τ)
        =
        ∑ τ : Config N, (sk_cov_kernel N β σ τ) • (std_basis N τ, (0 : EnergySpace N)) := by
    simp [std_basis_left]
  have :
      (ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map sk.U) (std_basis N σ), 0)
        =
        ∑ τ : Config N, (sk_cov_kernel N β σ τ) • (std_basis N τ, (0 : EnergySpace N)) := by
    refine Prod.ext ?_ ?_
    · simpa [Prod.fst_sum] using hsumU
    · simp [Prod.snd_sum]
  rw [hL, hR]
  exact this

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma covarianceOperator_disorderPairLaw_std_basis_right_eq_sum_simple
    {N : ℕ} {β q : ℝ} (sk : SKDisorder (Ω := Ω) N β) (sim : SimpleDisorder (Ω := Ω) N β q)
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.U) (σ : Config N) :
    ProbabilityTheory.covarianceOperator
        (disorderPairLaw (Ω := Ω) (N := N) (β := β) (q := q) (sk := sk) (sim := sim))
        (std_basis_right (N := N) σ)
      =
      ∑ τ : Config N,
        (simple_cov_kernel N β (fun x => q * x) σ τ) • std_basis_right (N := N) τ := by
  classical
  have hdiag :=
    covarianceOperator_disorderPairLaw_std_basis_right
      (Ω := Ω) (N := N) (β := β) (q := q) (sk := sk) (sim := sim) hindep σ
  have hsumV :
      ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map sim.U) (std_basis N σ)
        =
        ∑ τ : Config N, (simple_cov_kernel N β (fun x => q * x) σ τ) • std_basis N τ :=
    GaussianDisorder.covarianceOperator_apply_std_basis_eq_sum (Ω := Ω) (N := N) sim σ
  refine (WithLp.ofLp_injective (p := (2 : ℝ≥0∞)) (V := EnergySpace N × EnergySpace N)) ?_
  have hL :
      WithLp.ofLp
          (ProbabilityTheory.covarianceOperator
              (disorderPairLaw (Ω := Ω) (N := N) (β := β) (q := q) (sk := sk) (sim := sim))
              (std_basis_right (N := N) σ))
        =
        (0, ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map sim.U) (std_basis N σ)) := by
    simp [hdiag]
  have hR :
      WithLp.ofLp
          (∑ τ : Config N,
            (simple_cov_kernel N β (fun x => q * x) σ τ) • std_basis_right (N := N) τ)
        =
        ∑ τ : Config N,
          (simple_cov_kernel N β (fun x => q * x) σ τ) • ((0 : EnergySpace N), std_basis N τ) := by
    simp [std_basis_right]
  have :
      (0, ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map sim.U) (std_basis N σ))
        =
        ∑ τ : Config N,
          (simple_cov_kernel N β (fun x => q * x) σ τ) • ((0 : EnergySpace N), std_basis N τ) := by
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum]
    · simpa [Prod.snd_sum] using hsumV
  rw [hL, hR]
  exact this

end SpinGlass
