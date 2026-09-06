import SpinGlass.Defs
import SpinGlass.Poincare
import Common.Mathlib.Probability.Distributions.Gaussian.IntegrationByParts
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.InnerProductSpace.ProdL2

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology
open scoped ENNReal

namespace SpinGlass

/-!
# Sherrington–Kirkpatrick disorder

Centered Gaussian Hamiltonians on `EnergySpace N` specified by a covariance kernel on `std_basis`.
Main: `GaussianDisorder`, `SKDisorder`, `SimpleDisorder`, `disorderPairLaw`. Talagrand Vol. I.
-/

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

variable (N : ℕ)

/-! ### Gaussian disorder specifications -/

/-- Centered Gaussian Hamiltonian with covariance kernel `cov σ τ = 𝔼[U(σ) U(τ)]` on `std_basis`. -/
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

/-- SK disorder: centered Gaussian Hamiltonian with kernel `sk_cov_kernel`. -/
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

/-- Reference (simple) disorder with kernel `simple_cov_kernel`, for Guerra comparison. -/
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

/-! ### `SKDisorder` / `SimpleDisorder` as `GaussianDisorder` -/

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

/-! ### Gaussian `L²` self-averaging for the free energy density -/

theorem GaussianDisorder.variance_free_energy_density_le_pi_sq_div_eight_mul_opNorm_covarianceOperator_div_N_sq
    {N : ℕ} (G : GaussianDisorder (Ω := Ω) (N := N)) :
    Var[(fun ω : Ω => free_energy_density (N := N) (G.U ω)); (ℙ : Measure Ω)]
      ≤ (Real.pi ^ 2 / 8) * ‖ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U)‖ *
          (1 / (N : ℝ)) ^ 2 := by
  let μ : Measure (EnergySpace N) := (ℙ : Measure Ω).map G.U
  haveI : ProbabilityTheory.IsGaussian μ := by
    simpa [μ] using G.hU
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
    simpa [μ, Function.comp] using
      (ProbabilityTheory.variance_map (μ := (ℙ : Measure Ω))
        (X := fun H : EnergySpace N => free_energy_density (N := N) H)
        (Y := G.U) (hX := by simpa [μ] using hX) (hY := hY))
  have hVarBound :
      Var[(fun H : EnergySpace N => free_energy_density (N := N) H); μ]
        ≤ (Real.pi ^ 2 / 8) * ‖ProbabilityTheory.covarianceOperator μ‖ * (1 / (N : ℝ)) ^ 2 :=
    SpinGlass.variance_free_energy_density_le_pi_sq_div_eight_mul_opNorm_covarianceOperator_div_N_sq
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

theorem SKDisorder.variance_free_energy_density_le_pi_sq_div_eight_mul_opNorm_covarianceOperator_div_N_sq
    {N : ℕ} {β h : ℝ} (sk : SKDisorder (Ω := Ω) (N := N) β h) :
    Var[(fun ω : Ω => free_energy_density (N := N) (sk.U ω)); (ℙ : Measure Ω)]
      ≤ (Real.pi ^ 2 / 8) * ‖ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map sk.U)‖ *
          (1 / (N : ℝ)) ^ 2 := by
  simpa using
    (GaussianDisorder.variance_free_energy_density_le_pi_sq_div_eight_mul_opNorm_covarianceOperator_div_N_sq
      (Ω := Ω) (G := SKDisorder.toGaussianDisorder (Ω := Ω) (N := N) sk))

theorem SimpleDisorder.variance_free_energy_density_le_pi_sq_div_eight_mul_opNorm_covarianceOperator_div_N_sq
    {N : ℕ} {β q : ℝ} (sim : SimpleDisorder (Ω := Ω) (N := N) β q) :
    Var[(fun ω : Ω => free_energy_density (N := N) (sim.V ω)); (ℙ : Measure Ω)]
      ≤ (Real.pi ^ 2 / 8) * ‖ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map sim.V)‖ *
          (1 / (N : ℝ)) ^ 2 := by
  simpa using
    (GaussianDisorder.variance_free_energy_density_le_pi_sq_div_eight_mul_opNorm_covarianceOperator_div_N_sq
      (Ω := Ω) (G := SimpleDisorder.toGaussianDisorder (Ω := Ω) (N := N) sim))

theorem GaussianDisorder.meas_ge_le_free_energy_density_sub_mean_div_sq
    {N : ℕ} (G : GaussianDisorder (Ω := Ω) (N := N)) {c : ℝ} (hc : 0 < c) :
    (ℙ : Measure Ω) {ω : Ω |
        c ≤
          |free_energy_density (N := N) (G.U ω)
            - (ℙ : Measure Ω)[fun ω : Ω => free_energy_density (N := N) (G.U ω)]|}
      ≤ ENNReal.ofReal
          (((Real.pi ^ 2 / 8) * ‖ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U)‖ *
              (1 / (N : ℝ)) ^ 2) / c ^ 2) := by
  let μH : Measure (EnergySpace N) := (ℙ : Measure Ω).map G.U
  haveI : ProbabilityTheory.IsGaussian μH := by
    simpa [μH] using G.hU
  have hMemH : MemLp (fun H : EnergySpace N => free_energy_density (N := N) H) 2 μH :=
    (SpinGlass.memLp_free_energy_density (N := N) (μ := μH))
  have hMem :
      MemLp (fun ω : Ω => free_energy_density (N := N) (G.U ω)) 2 (ℙ : Measure Ω) := by
    simpa [μH, Function.comp] using (hMemH.comp_of_map (f := G.U) (μ := (ℙ : Measure Ω))
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
    GaussianDisorder.variance_free_energy_density_le_pi_sq_div_eight_mul_opNorm_covarianceOperator_div_N_sq
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

theorem SKDisorder.meas_ge_le_free_energy_density_sub_mean_div_sq
    {N : ℕ} {β h : ℝ} (sk : SKDisorder (Ω := Ω) (N := N) β h) {c : ℝ} (hc : 0 < c) :
    (ℙ : Measure Ω) {ω : Ω |
        c ≤
          |free_energy_density (N := N) (sk.U ω)
            - (ℙ : Measure Ω)[fun ω : Ω => free_energy_density (N := N) (sk.U ω)]|}
      ≤ ENNReal.ofReal
          (((Real.pi ^ 2 / 8) * ‖ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map sk.U)‖ *
              (1 / (N : ℝ)) ^ 2) / c ^ 2) := by
  simpa using
    (GaussianDisorder.meas_ge_le_free_energy_density_sub_mean_div_sq (Ω := Ω)
      (G := SKDisorder.toGaussianDisorder (Ω := Ω) (N := N) sk) hc)

theorem SimpleDisorder.meas_ge_le_free_energy_density_sub_mean_div_sq
    {N : ℕ} {β q : ℝ} (sim : SimpleDisorder (Ω := Ω) (N := N) β q) {c : ℝ} (hc : 0 < c) :
    (ℙ : Measure Ω) {ω : Ω |
        c ≤
          |free_energy_density (N := N) (sim.V ω)
            - (ℙ : Measure Ω)[fun ω : Ω => free_energy_density (N := N) (sim.V ω)]|}
      ≤ ENNReal.ofReal
          (((Real.pi ^ 2 / 8) * ‖ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map sim.V)‖ *
              (1 / (N : ℝ)) ^ 2) / c ^ 2) := by
  simpa using
    (GaussianDisorder.meas_ge_le_free_energy_density_sub_mean_div_sq (Ω := Ω)
      (G := SimpleDisorder.toGaussianDisorder (Ω := Ω) (N := N) sim) hc)

/-! ### Covariance operator as a kernel expansion -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma GaussianDisorder.covarianceOperator_apply_std_basis_eq_sum
    {N : ℕ} (G : GaussianDisorder (Ω := Ω) (N := N)) (σ : Config N) :
    ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U) (std_basis N σ)
      =
      ∑ τ : Config N, (G.cov σ τ) • std_basis N τ := by
  ext ρ
  have hcoord :
      (ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U) (std_basis N σ)) ρ
        = G.cov σ ρ := by
    calc
      (ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U) (std_basis N σ)) ρ
          = inner ℝ (std_basis N ρ)
              (ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U) (std_basis N σ)) := by
              simpa using
                (inner_std_basis_apply (N := N) (σ := ρ)
                    (H := ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U) (std_basis N σ))).symm
      _ = inner ℝ
            (ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map G.U) (std_basis N σ))
            (std_basis N ρ) := by simp [real_inner_comm]
      _ = G.cov σ ρ := G.cov_eq σ ρ
  have hsum : (∑ τ : Config N, (G.cov σ τ) • std_basis N τ) ρ = G.cov σ ρ := by
    simp [std_basis, FiniteGibbs.std_basis]
  simp [hcoord, hsum]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma SKDisorder.covarianceOperator_apply_std_basis_eq_sum
    {N : ℕ} {β h : ℝ} (sk : SKDisorder (Ω := Ω) N β h) (σ : Config N) :
    ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map sk.U) (std_basis N σ)
      =
      ∑ τ : Config N, (sk_cov_kernel N β σ τ) • std_basis N τ := by
  simpa using
    (GaussianDisorder.covarianceOperator_apply_std_basis_eq_sum (Ω := Ω) (N := N)
      (G := SKDisorder.toGaussianDisorder (Ω := Ω) (N := N) sk) σ)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma SimpleDisorder.covarianceOperator_apply_std_basis_eq_sum
    {N : ℕ} {β q : ℝ} (sim : SimpleDisorder (Ω := Ω) N β q) (σ : Config N) :
    ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map sim.V) (std_basis N σ)
      =
      ∑ τ : Config N, (simple_cov_kernel N β (fun x => q * x) σ τ) • std_basis N τ := by
  simpa using
    (GaussianDisorder.covarianceOperator_apply_std_basis_eq_sum (Ω := Ω) (N := N)
      (G := SimpleDisorder.toGaussianDisorder (Ω := Ω) (N := N) sim) σ)

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
noncomputable def disorderPair (N : ℕ) (β h q : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) (sim : SimpleDisorder (Ω := Ω) N β q) :
    Ω → DisorderSpace (N := N) :=
  fun ω => WithLp.toLp 2 (sk.U ω, sim.V ω)

/-- The law of the repackaged disorder pair. -/
noncomputable abbrev disorderPairLaw (N : ℕ) (β h q : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) (sim : SimpleDisorder (Ω := Ω) N β q) :
    Measure (DisorderSpace (N := N)) :=
  (ℙ : Measure Ω).map (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
@[simp] lemma disorderPair_fst (N : ℕ) (β h q : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) (sim : SimpleDisorder (Ω := Ω) N β q) (ω : Ω) :
    (WithLp.ofLp (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) ω)).1
      = sk.U ω := by
  simp [disorderPair]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
@[simp] lemma disorderPair_snd (N : ℕ) (β h q : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) (sim : SimpleDisorder (Ω := Ω) N β q) (ω : Ω) :
    (WithLp.ofLp (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) ω)).2
      = sim.V ω := by
  simp [disorderPair]

/-! ### Mean zero of `disorderPairLaw` -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma SKDisorder.integral_eq_zero_of_mean0
    {N : ℕ} {β h : ℝ} (sk : SKDisorder (Ω := Ω) N β h) :
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
    (∫ ω, sim.V ω ∂(ℙ : Measure Ω)) = 0 := by
  have hmap :
      (∫ x : EnergySpace N, x ∂((ℙ : Measure Ω).map sim.V))
        = ∫ ω, sim.V ω ∂(ℙ : Measure Ω) := by
    simpa using
      (MeasureTheory.integral_map (μ := (ℙ : Measure Ω)) (φ := sim.V)
        sim.measV.aemeasurable (measurable_id.aestronglyMeasurable))
  simpa [hmap] using sim.mean0

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma disorderPair_integral_eq_zero
    {N : ℕ} {β h q : ℝ} (sk : SKDisorder (Ω := Ω) N β h) (sim : SimpleDisorder (Ω := Ω) N β q) :
    (∫ ω, disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) ω
        ∂(ℙ : Measure Ω))
      = 0 := by
  -- Use the continuous linear equivalence `ofLp : DisorderSpace ≃L E×F` to reduce to the product.
  let e : DisorderSpace (N := N) ≃L[ℝ] (EnergySpace N × EnergySpace N) :=
    WithLp.prodContinuousLinearEquiv (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
      (α := EnergySpace N) (β := EnergySpace N)
  have hint : Integrable (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
      (ℙ : Measure Ω) := by
    -- Gaussian implies integrable; we use `HasGaussianLaw` on each marginal and the continuity of `toLp`.
    have hX : ProbabilityTheory.HasGaussianLaw sk.U (ℙ : Measure Ω) := ⟨sk.hU⟩
    have hY : ProbabilityTheory.HasGaussianLaw sim.V (ℙ : Measure Ω) := ⟨sim.hV⟩
    have hpair : Integrable (fun ω => (sk.U ω, sim.V ω)) (ℙ : Measure Ω) :=
      (Integrable.prodMk hX.integrable hY.integrable)
    -- `toLp` is continuous linear.
    have : Integrable (fun ω => e.symm (sk.U ω, sim.V ω)) (ℙ : Measure Ω) :=
      (e.symm.toContinuousLinearMap.integrable_comp hpair)
    simpa [disorderPair, e] using this
  have : e (∫ ω, disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) ω
        ∂(ℙ : Measure Ω))
      = 0 := by
    have hU0 := SKDisorder.integral_eq_zero_of_mean0 (Ω := Ω) (N := N) sk
    have hV0 := SimpleDisorder.integral_eq_zero_of_mean0 (Ω := Ω) (N := N) sim
    have hpair_int : Integrable (fun ω => (sk.U ω, sim.V ω)) (ℙ : Measure Ω) := by
      have hX : ProbabilityTheory.HasGaussianLaw sk.U (ℙ : Measure Ω) := ⟨sk.hU⟩
      have hY : ProbabilityTheory.HasGaussianLaw sim.V (ℙ : Measure Ω) := ⟨sim.hV⟩
      exact Integrable.prodMk hX.integrable hY.integrable
    have hpair : (∫ ω, (sk.U ω, sim.V ω) ∂(ℙ : Measure Ω)) = (0, 0) := by
      refine Prod.ext ?_ ?_
      · let fstL : (EnergySpace N × EnergySpace N) →L[ℝ] EnergySpace N :=
          ContinuousLinearMap.fst ℝ (EnergySpace N) (EnergySpace N)
        have hf : fstL (∫ ω, (sk.U ω, sim.V ω) ∂(ℙ : Measure Ω))
            = ∫ ω, fstL (sk.U ω, sim.V ω) ∂(ℙ : Measure Ω) := by
          simpa using (fstL.integral_comp_comm (μ := (ℙ : Measure Ω)) hpair_int).symm
        calc
          (∫ ω, (sk.U ω, sim.V ω) ∂(ℙ : Measure Ω)).1
              = fstL (∫ ω, (sk.U ω, sim.V ω) ∂(ℙ : Measure Ω)) := by rfl
          _ = ∫ ω, sk.U ω ∂(ℙ : Measure Ω) := by simpa [fstL] using hf
          _ = 0 := hU0
      · let sndL : (EnergySpace N × EnergySpace N) →L[ℝ] EnergySpace N :=
          ContinuousLinearMap.snd ℝ (EnergySpace N) (EnergySpace N)
        have hf : sndL (∫ ω, (sk.U ω, sim.V ω) ∂(ℙ : Measure Ω))
            = ∫ ω, sndL (sk.U ω, sim.V ω) ∂(ℙ : Measure Ω) := by
          simpa using (sndL.integral_comp_comm (μ := (ℙ : Measure Ω)) hpair_int).symm
        calc
          (∫ ω, (sk.U ω, sim.V ω) ∂(ℙ : Measure Ω)).2
              = sndL (∫ ω, (sk.U ω, sim.V ω) ∂(ℙ : Measure Ω)) := by rfl
          _ = ∫ ω, sim.V ω ∂(ℙ : Measure Ω) := by simpa [sndL] using hf
          _ = 0 := hV0
    have he :
        e (∫ ω, disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) ω
            ∂(ℙ : Measure Ω))
          =
        ∫ ω, (sk.U ω, sim.V ω) ∂(ℙ : Measure Ω) := by
      have hcomm :=
        (e.toContinuousLinearMap.integral_comp_comm (μ := (ℙ : Measure Ω)) hint)
      have hsimp :
          (fun ω => e (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
              (sk := sk) (sim := sim) ω))
            = fun ω => (sk.U ω, sim.V ω) := by
        funext ω
        simp [disorderPair, e]
      simpa [hsimp] using hcomm.symm
    simp [he, hpair]
  exact e.injective this

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma disorderPairLaw_mean0
    {N : ℕ} {β h q : ℝ} (sk : SKDisorder (Ω := Ω) N β h) (sim : SimpleDisorder (Ω := Ω) N β q) :
    (∫ x : DisorderSpace (N := N),
        x ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)))
      = 0 := by
  have hmeas : Measurable (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)) := by
    have hpair : Measurable fun ω : Ω => (sk.U ω, sim.V ω) := sk.measU.prodMk sim.measV
    simpa [disorderPair] using
      (WithLp.prod_continuous_toLp (p := (2 : ℝ≥0∞)) (α := EnergySpace N) (β := EnergySpace N)).measurable.comp hpair
  simpa [disorderPairLaw] using
    (MeasureTheory.integral_map (μ := (ℙ : Measure Ω))
      (φ := disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
      (hmeas.aemeasurable) (measurable_id.aestronglyMeasurable)).trans
      (disorderPair_integral_eq_zero (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Independent Gaussian disorders are jointly Gaussian on the product space. -/
lemma SKDisorder.simple_joint_isGaussian_of_indep
    {β h q : ℝ} (sk : SKDisorder (Ω := Ω) (N := N) β h) (sim : SimpleDisorder (Ω := Ω) (N := N) β q)
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V) :
    ProbabilityTheory.IsGaussian
      (((ℙ : Measure Ω).map fun ω => (sk.U ω, sim.V ω))) := by
  have hX : ProbabilityTheory.HasGaussianLaw sk.U (ℙ : Measure Ω) :=
    ⟨sk.hU⟩
  have hY : ProbabilityTheory.HasGaussianLaw sim.V (ℙ : Measure Ω) :=
    ⟨sim.hV⟩
  exact (ProbabilityTheory.IndepFun.hasGaussianLaw (P := (ℙ : Measure Ω)) hX hY hindep).isGaussian_map

open scoped ENNReal

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Joint Gaussianity of `(U,V)` on `WithLp 2 (E × F)`. -/
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
    haveI : Fact ((1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
    exact ProbabilityTheory.HasGaussianLaw.toLp_prodMk (X := sk.U) (Y := sim.V)
      (P := (ℙ : Measure Ω)) (p := (2 : ℝ≥0∞)) hXY
  exact htoLp.isGaussian_map

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma SKDisorder.simple_joint_isGaussian_disorderPairLaw_of_indep
    {N : ℕ} {β h q : ℝ} (sk : SKDisorder (Ω := Ω) N β h) (sim : SimpleDisorder (Ω := Ω) N β q)
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V) :
    ProbabilityTheory.IsGaussian
      (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)) := by
  simpa [disorderPairLaw, disorderPair] using
    (SKDisorder.simple_joint_isGaussian_withLp_of_indep (Ω := Ω) (N := N) sk sim hindep)

/-! ### Covariance of `disorderPairLaw` -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma covarianceOperator_disorderPairLaw_std_basis_left
    {N : ℕ} {β h q : ℝ} (sk : SKDisorder (Ω := Ω) N β h) (sim : SimpleDisorder (Ω := Ω) N β q)
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V) (σ : Config N) :
    ProbabilityTheory.covarianceOperator
        (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
        (std_basis_left (N := N) σ) = WithLp.toLp 2
        (ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map sk.U) (std_basis N σ), 0) := by
  let μ : Measure (DisorderSpace (N := N)) :=
    disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
  let μU : Measure (EnergySpace N) := (ℙ : Measure Ω).map sk.U
  let μV : Measure (EnergySpace N) := (ℙ : Measure Ω).map sim.V
  have hgaussμ : ProbabilityTheory.IsGaussian μ :=
    SKDisorder.simple_joint_isGaussian_disorderPairLaw_of_indep
      (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) hindep
  haveI : ProbabilityTheory.IsGaussian μ := hgaussμ
  have hμ : MemLp id 2 μ := ProbabilityTheory.IsGaussian.memLp_two_id (μ := μ)
  haveI : ProbabilityTheory.IsGaussian μU := sk.hU
  haveI : ProbabilityTheory.IsGaussian μV := sim.hV
  have hμU : MemLp id 2 μU := ProbabilityTheory.IsGaussian.memLp_two_id (μ := μU)
  have hμV : MemLp id 2 μV := ProbabilityTheory.IsGaussian.memLp_two_id (μ := μV)

  refine ext_inner_right ℝ (fun y => ?_)
  set y1 : EnergySpace N := (WithLp.ofLp y).1
  set y2 : EnergySpace N := (WithLp.ofLp y).2

  have hpair_meas :
      Measurable (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)) := by
    have hpair : Measurable fun ω : Ω => (sk.U ω, sim.V ω) := sk.measU.prodMk sim.measV
    simpa [disorderPair] using
      (WithLp.prod_continuous_toLp (p := (2 : ℝ≥0∞)) (α := EnergySpace N) (β := EnergySpace N)).measurable.comp hpair

  have hL :
      inner ℝ (ProbabilityTheory.covarianceOperator μ (std_basis_left (N := N) σ)) y
        =
        ∫ ω,
          (inner ℝ (std_basis N σ) (sk.U ω)) *
            (inner ℝ y1 (sk.U ω) + inner ℝ y2 (sim.V ω)) ∂ℙ := by
    have hcov :
        inner ℝ (ProbabilityTheory.covarianceOperator μ (std_basis_left (N := N) σ)) y
          =
          ∫ z : DisorderSpace (N := N),
            inner ℝ (std_basis_left (N := N) σ) z * inner ℝ y z ∂μ := by
      simpa [μ] using
        (ProbabilityTheory.covarianceOperator_inner (μ := μ) hμ (std_basis_left (N := N) σ) y)
    let g : DisorderSpace (N := N) → ℝ :=
      fun z => inner ℝ (std_basis_left (N := N) σ) z * inner ℝ y z
    have hg_meas : Measurable g := by
      have h1 : Measurable fun z : DisorderSpace (N := N) => inner ℝ (std_basis_left (N := N) σ) z :=
        (innerSL ℝ (std_basis_left (N := N) σ)).measurable
      have h2 : Measurable fun z : DisorderSpace (N := N) => inner ℝ y z :=
        (innerSL ℝ y).measurable
      simpa [g] using h1.mul h2
    have hmap :
        (∫ z : DisorderSpace (N := N), g z ∂μ)
          =
          ∫ ω, g (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) ω) ∂ℙ := by
      simpa [μ, disorderPairLaw] using
        (MeasureTheory.integral_map (μ := (ℙ : Measure Ω))
          (φ := disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
          (hpair_meas.aemeasurable) (hg_meas.aestronglyMeasurable))
    have hstd : ∀ ω,
        inner ℝ (std_basis_left (N := N) σ)
            (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) ω)
          = inner ℝ (std_basis N σ) (sk.U ω) := by
      intro ω
      have :
          inner ℝ (std_basis_left (N := N) σ)
              (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) ω)
            =
            ((WithLp.ofLp
              (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) ω)).1) σ := by
        simpa [real_inner_comm] using
          (inner_apply_std_basis_left (N := N) (σ := σ)
            (uv := disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) ω))
      simpa [this, disorderPair, inner_std_basis_apply]
    have hy : ∀ ω,
        inner ℝ y
            (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) ω)
          = inner ℝ y1 (sk.U ω) + inner ℝ y2 (sim.V ω) := by
      intro ω
      simp [y1, y2, disorderPair, SpinGlass.DisorderSpace, WithLp.prod_inner_apply, real_inner_comm]
    calc
      inner ℝ (ProbabilityTheory.covarianceOperator μ (std_basis_left (N := N) σ)) y
          = ∫ z : DisorderSpace (N := N), inner ℝ (std_basis_left (N := N) σ) z * inner ℝ y z ∂μ := hcov
      _ = ∫ ω,
            inner ℝ (std_basis_left (N := N) σ)
                (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) ω)
              * inner ℝ y
                  (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) ω) ∂ℙ := by
            simpa [g] using hmap
      _ = ∫ ω,
            (inner ℝ (std_basis N σ) (sk.U ω)) *
              (inner ℝ y1 (sk.U ω) + inner ℝ y2 (sim.V ω)) ∂ℙ := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with ω
            simp [hstd ω, hy ω]

  have hU0 : (∫ ω, sk.U ω ∂(ℙ : Measure Ω)) = 0 :=
    SKDisorder.integral_eq_zero_of_mean0 (Ω := Ω) (N := N) sk
  have hV0 : (∫ ω, sim.V ω ∂(ℙ : Measure Ω)) = 0 :=
    SimpleDisorder.integral_eq_zero_of_mean0 (Ω := Ω) (N := N) sim
  have hUmean : (∫ ω, inner ℝ (std_basis N σ) (sk.U ω) ∂ℙ) = 0 := by
    have hint : Integrable sk.U (ℙ : Measure Ω) := by
      have hX : ProbabilityTheory.HasGaussianLaw sk.U (ℙ : Measure Ω) := ⟨sk.hU⟩
      exact hX.integrable
    have hcomm := (innerSL ℝ (std_basis N σ)).integral_comp_comm (μ := (ℙ : Measure Ω)) hint
    calc
      (∫ ω, inner ℝ (std_basis N σ) (sk.U ω) ∂ℙ)
          = (innerSL ℝ (std_basis N σ)) (∫ ω, sk.U ω ∂(ℙ : Measure Ω)) := by
              simpa using hcomm
      _ = 0 := by simp [hU0]
  have hVmean : (∫ ω, inner ℝ y2 (sim.V ω) ∂ℙ) = 0 := by
    have hint : Integrable sim.V (ℙ : Measure Ω) := by
      have hX : ProbabilityTheory.HasGaussianLaw sim.V (ℙ : Measure Ω) := ⟨sim.hV⟩
      exact hX.integrable
    have hcomm := (innerSL ℝ y2).integral_comp_comm (μ := (ℙ : Measure Ω)) hint
    calc
      (∫ ω, inner ℝ y2 (sim.V ω) ∂ℙ)
          = (innerSL ℝ y2) (∫ ω, sim.V ω ∂(ℙ : Measure Ω)) := by
              simpa using hcomm
      _ = 0 := by simp [hV0]
  have hcross :
      (∫ ω, (inner ℝ (std_basis N σ) (sk.U ω)) * (inner ℝ y2 (sim.V ω)) ∂ℙ) = 0 := by
    have hind :
        (fun ω => inner ℝ (std_basis N σ) (sk.U ω))
          ⟂ᵢ[(ℙ : Measure Ω)]
        (fun ω => inner ℝ y2 (sim.V ω)) :=
      (hindep.comp (hφ := (innerSL ℝ (std_basis N σ)).measurable) (hψ := (innerSL ℝ y2).measurable))
    have hsplit :=
      ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral (μ := (ℙ : Measure Ω)) hind
        ((innerSL ℝ (std_basis N σ)).measurable.aestronglyMeasurable.comp_measurable sk.measU)
        ((innerSL ℝ y2).measurable.aestronglyMeasurable.comp_measurable sim.measV)
    simpa [hUmean, hVmean] using hsplit

  have hL' :
      inner ℝ (ProbabilityTheory.covarianceOperator μ (std_basis_left (N := N) σ)) y
        =
        ∫ ω, (inner ℝ (std_basis N σ) (sk.U ω)) * (inner ℝ y1 (sk.U ω)) ∂ℙ := by
    have hA2U : MemLp (innerSL ℝ (std_basis N σ)) 2 μU :=
      ProbabilityTheory.IsGaussian.memLp_dual (μ := μU) (L := innerSL ℝ (std_basis N σ)) 2 (by norm_num)
    have hB2U : MemLp (innerSL ℝ y1) 2 μU :=
      ProbabilityTheory.IsGaussian.memLp_dual (μ := μU) (L := innerSL ℝ y1) 2 (by norm_num)
    have hC2V : MemLp (innerSL ℝ y2) 2 μV :=
      ProbabilityTheory.IsGaussian.memLp_dual (μ := μV) (L := innerSL ℝ y2) 2 (by norm_num)
    have hA2 : MemLp (fun ω => inner ℝ (std_basis N σ) (sk.U ω)) 2 (ℙ : Measure Ω) := by
      simpa [μU, Function.comp] using
        hA2U.comp_of_map (f := sk.U) (μ := (ℙ : Measure Ω)) sk.measU.aemeasurable
    have hB2 : MemLp (fun ω => inner ℝ y1 (sk.U ω)) 2 (ℙ : Measure Ω) := by
      simpa [μU, Function.comp] using
        hB2U.comp_of_map (f := sk.U) (μ := (ℙ : Measure Ω)) sk.measU.aemeasurable
    have hC2 : MemLp (fun ω => inner ℝ y2 (sim.V ω)) 2 (ℙ : Measure Ω) := by
      simpa [μV, Function.comp] using
        hC2V.comp_of_map (f := sim.V) (μ := (ℙ : Measure Ω)) sim.measV.aemeasurable
    have hAB_int :
        Integrable (fun ω => (inner ℝ (std_basis N σ) (sk.U ω)) * (inner ℝ y1 (sk.U ω)))
          (ℙ : Measure Ω) := by
      simpa using (hA2.integrable_mul hB2)
    have hAC_int :
        Integrable (fun ω => (inner ℝ (std_basis N σ) (sk.U ω)) * (inner ℝ y2 (sim.V ω)))
          (ℙ : Measure Ω) := by
      simpa using (hA2.integrable_mul hC2)
    have hsplit_int :
        (∫ ω,
            (inner ℝ (std_basis N σ) (sk.U ω)) *
              (inner ℝ y1 (sk.U ω) + inner ℝ y2 (sim.V ω)) ∂ℙ)
          =
          (∫ ω, (inner ℝ (std_basis N σ) (sk.U ω)) * (inner ℝ y1 (sk.U ω)) ∂ℙ)
          +
          (∫ ω, (inner ℝ (std_basis N σ) (sk.U ω)) * (inner ℝ y2 (sim.V ω)) ∂ℙ) := by
      simpa [mul_add, add_mul] using
        (MeasureTheory.integral_add (μ := (ℙ : Measure Ω))
          (f := fun ω => (inner ℝ (std_basis N σ) (sk.U ω)) * (inner ℝ y1 (sk.U ω)))
          (g := fun ω => (inner ℝ (std_basis N σ) (sk.U ω)) * (inner ℝ y2 (sim.V ω)))
          hAB_int hAC_int)
    calc
      inner ℝ (ProbabilityTheory.covarianceOperator μ (std_basis_left (N := N) σ)) y
          = ∫ ω,
              (inner ℝ (std_basis N σ) (sk.U ω)) *
                (inner ℝ y1 (sk.U ω) + inner ℝ y2 (sim.V ω)) ∂ℙ := hL
      _ = (∫ ω, (inner ℝ (std_basis N σ) (sk.U ω)) * (inner ℝ y1 (sk.U ω)) ∂ℙ)
          + (∫ ω, (inner ℝ (std_basis N σ) (sk.U ω)) * (inner ℝ y2 (sim.V ω)) ∂ℙ) := hsplit_int
      _ = (∫ ω, (inner ℝ (std_basis N σ) (sk.U ω)) * (inner ℝ y1 (sk.U ω)) ∂ℙ) := by simp [hcross]

  have hU :
      inner ℝ (ProbabilityTheory.covarianceOperator μU (std_basis N σ)) y1
        =
        ∫ ω, (inner ℝ (std_basis N σ) (sk.U ω)) * (inner ℝ y1 (sk.U ω)) ∂ℙ := by
    have hcov :
        inner ℝ (ProbabilityTheory.covarianceOperator μU (std_basis N σ)) y1
          =
          ∫ u : EnergySpace N, inner ℝ (std_basis N σ) u * inner ℝ y1 u ∂μU := by
      simpa [μU] using
        (ProbabilityTheory.covarianceOperator_inner (μ := μU) hμU (std_basis N σ) y1)
    let gU : EnergySpace N → ℝ := fun u => inner ℝ (std_basis N σ) u * inner ℝ y1 u
    have hgU_meas : Measurable gU := by
      have h1 : Measurable fun u : EnergySpace N => inner ℝ (std_basis N σ) u :=
        (innerSL ℝ (std_basis N σ)).measurable
      have h2 : Measurable fun u : EnergySpace N => inner ℝ y1 u :=
        (innerSL ℝ y1).measurable
      simpa [gU] using h1.mul h2
    have hmapU :
        (∫ u : EnergySpace N, gU u ∂μU) = ∫ ω, gU (sk.U ω) ∂ℙ := by
      simpa [μU] using
        (MeasureTheory.integral_map (μ := (ℙ : Measure Ω)) (φ := sk.U)
          (sk.measU.aemeasurable) (hgU_meas.aestronglyMeasurable))
    simpa [gU, hmapU] using hcov

  simpa [μ, μU, y1, SpinGlass.DisorderSpace, std_basis_left, WithLp.prod_inner_apply,
    real_inner_comm, hU] using hL'.trans hU.symm

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma covarianceOperator_disorderPairLaw_std_basis_right
    {N : ℕ} {β h q : ℝ} (sk : SKDisorder (Ω := Ω) N β h) (sim : SimpleDisorder (Ω := Ω) N β q)
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V) (σ : Config N) :
    ProbabilityTheory.covarianceOperator
        (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
        (std_basis_right (N := N) σ)
      =
      WithLp.toLp 2
        (0, ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map sim.V) (std_basis N σ)) := by
  let μ : Measure (DisorderSpace (N := N)) :=
    disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
  let μU : Measure (EnergySpace N) := (ℙ : Measure Ω).map sk.U
  let μV : Measure (EnergySpace N) := (ℙ : Measure Ω).map sim.V
  have hgaussμ : ProbabilityTheory.IsGaussian μ :=
    SKDisorder.simple_joint_isGaussian_disorderPairLaw_of_indep
      (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) hindep
  haveI : ProbabilityTheory.IsGaussian μ := hgaussμ
  have hμ : MemLp id 2 μ := ProbabilityTheory.IsGaussian.memLp_two_id (μ := μ)
  haveI : ProbabilityTheory.IsGaussian μU := sk.hU
  haveI : ProbabilityTheory.IsGaussian μV := sim.hV
  have hμU : MemLp id 2 μU := ProbabilityTheory.IsGaussian.memLp_two_id (μ := μU)
  have hμV : MemLp id 2 μV := ProbabilityTheory.IsGaussian.memLp_two_id (μ := μV)
  refine ext_inner_right ℝ (fun y => ?_)
  set y1 : EnergySpace N := (WithLp.ofLp y).1
  set y2 : EnergySpace N := (WithLp.ofLp y).2
  have hpair_meas :
      Measurable (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)) := by
    have hpair : Measurable fun ω : Ω => (sk.U ω, sim.V ω) := sk.measU.prodMk sim.measV
    simpa [disorderPair] using
      (WithLp.prod_continuous_toLp (p := (2 : ℝ≥0∞)) (α := EnergySpace N) (β := EnergySpace N)).measurable.comp hpair
  have hR : inner ℝ (ProbabilityTheory.covarianceOperator μ (std_basis_right (N := N) σ)) y =
        ∫ ω, (inner ℝ (std_basis N σ) (sim.V ω)) *
          (inner ℝ y1 (sk.U ω) + inner ℝ y2 (sim.V ω)) ∂ℙ := by
    have hcov : inner ℝ
            (ProbabilityTheory.covarianceOperator μ (std_basis_right (N := N) σ)) y =
          ∫ z : DisorderSpace (N := N),
            inner ℝ (std_basis_right (N := N) σ) z * inner ℝ y z ∂μ := by
      simpa [μ] using (ProbabilityTheory.covarianceOperator_inner (μ := μ) hμ
        (std_basis_right (N := N) σ) y)
    let g : DisorderSpace (N := N) → ℝ :=
      fun z => inner ℝ (std_basis_right (N := N) σ) z * inner ℝ y z
    have hg_meas : Measurable g := by
      have h1 : Measurable fun z : DisorderSpace (N := N) => inner ℝ (std_basis_right (N := N) σ) z :=
        (innerSL ℝ (std_basis_right (N := N) σ)).measurable
      have h2 : Measurable fun z : DisorderSpace (N := N) => inner ℝ y z :=
        (innerSL ℝ y).measurable
      simpa [g] using h1.mul h2
    have hmap : (∫ z : DisorderSpace (N := N), g z ∂μ) =
          ∫ ω, g (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) ω) ∂ℙ := by
      simpa [μ, disorderPairLaw] using
        (MeasureTheory.integral_map (μ := (ℙ : Measure Ω))
          (φ := disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
          (hpair_meas.aemeasurable) (hg_meas.aestronglyMeasurable))
    have hstd : ∀ ω,
        inner ℝ (std_basis_right (N := N) σ)
            (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) ω)
          = inner ℝ (std_basis N σ) (sim.V ω) := by
      intro ω
      have : inner ℝ (std_basis_right (N := N) σ)
              (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) ω)
            =
            ((WithLp.ofLp
              (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) ω)).2) σ := by
        simpa [real_inner_comm] using (inner_apply_std_basis_right (N := N) (σ := σ)
          (uv := disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) ω))
      simpa [this, disorderPair, inner_std_basis_apply]
    have hy : ∀ ω,
        inner ℝ y
            (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) ω)
          = inner ℝ y1 (sk.U ω) + inner ℝ y2 (sim.V ω) := by
      intro ω
      simp [y1, y2, disorderPair, SpinGlass.DisorderSpace, WithLp.prod_inner_apply, real_inner_comm]
    calc
      inner ℝ (ProbabilityTheory.covarianceOperator μ (std_basis_right (N := N) σ)) y
          = ∫ z : DisorderSpace (N := N), inner ℝ (std_basis_right (N := N) σ) z * inner ℝ y z ∂μ := hcov
      _ = ∫ ω,
            inner ℝ (std_basis_right (N := N) σ)
                (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) ω)
              * inner ℝ y
                  (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) ω) ∂ℙ := by
            simpa [g] using hmap
      _ = ∫ ω,
            (inner ℝ (std_basis N σ) (sim.V ω)) *
              (inner ℝ y1 (sk.U ω) + inner ℝ y2 (sim.V ω)) ∂ℙ := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with ω
            simp [hstd ω, hy ω]

  have hU0 : (∫ ω, sk.U ω ∂(ℙ : Measure Ω)) = 0 :=
    SKDisorder.integral_eq_zero_of_mean0 (Ω := Ω) (N := N) sk
  have hV0 : (∫ ω, sim.V ω ∂(ℙ : Measure Ω)) = 0 :=
    SimpleDisorder.integral_eq_zero_of_mean0 (Ω := Ω) (N := N) sim
  have hVmean : (∫ ω, inner ℝ (std_basis N σ) (sim.V ω) ∂ℙ) = 0 := by
    have hint : Integrable sim.V (ℙ : Measure Ω) := by
      have hX : ProbabilityTheory.HasGaussianLaw sim.V (ℙ : Measure Ω) := ⟨sim.hV⟩
      exact hX.integrable
    have hcomm := (innerSL ℝ (std_basis N σ)).integral_comp_comm (μ := (ℙ : Measure Ω)) hint
    calc
      (∫ ω, inner ℝ (std_basis N σ) (sim.V ω) ∂ℙ)
          = (innerSL ℝ (std_basis N σ)) (∫ ω, sim.V ω ∂(ℙ : Measure Ω)) := by
              simpa using hcomm
      _ = 0 := by simp [hV0]
  have hUmean : (∫ ω, inner ℝ y1 (sk.U ω) ∂ℙ) = 0 := by
    have hint : Integrable sk.U (ℙ : Measure Ω) := by
      have hX : ProbabilityTheory.HasGaussianLaw sk.U (ℙ : Measure Ω) := ⟨sk.hU⟩
      exact hX.integrable
    have hcomm := (innerSL ℝ y1).integral_comp_comm (μ := (ℙ : Measure Ω)) hint
    calc
      (∫ ω, inner ℝ y1 (sk.U ω) ∂ℙ)
          = (innerSL ℝ y1) (∫ ω, sk.U ω ∂(ℙ : Measure Ω)) := by
              simpa using hcomm
      _ = 0 := by simp [hU0]
  have hcross :
      (∫ ω, (inner ℝ (std_basis N σ) (sim.V ω)) * (inner ℝ y1 (sk.U ω)) ∂ℙ) = 0 := by
    have hind :
        (fun ω => inner ℝ (std_basis N σ) (sim.V ω))
          ⟂ᵢ[(ℙ : Measure Ω)]
        (fun ω => inner ℝ y1 (sk.U ω)) :=
      (hindep.symm.comp (hφ := (innerSL ℝ (std_basis N σ)).measurable) (hψ := (innerSL ℝ y1).measurable))
    have hsplit :=
      ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral (μ := (ℙ : Measure Ω)) hind
        ((innerSL ℝ (std_basis N σ)).measurable.aestronglyMeasurable.comp_measurable sim.measV)
        ((innerSL ℝ y1).measurable.aestronglyMeasurable.comp_measurable sk.measU)
    simpa [hVmean, hUmean] using hsplit

  have hR' :
      inner ℝ
          (ProbabilityTheory.covarianceOperator μ (std_basis_right (N := N) σ)) y
        =
        ∫ ω, (inner ℝ (std_basis N σ) (sim.V ω)) * (inner ℝ y2 (sim.V ω)) ∂ℙ := by
    have hA2V : MemLp (innerSL ℝ (std_basis N σ)) 2 μV :=
      ProbabilityTheory.IsGaussian.memLp_dual (μ := μV) (L := innerSL ℝ (std_basis N σ)) 2 (by norm_num)
    have hB2V : MemLp (innerSL ℝ y2) 2 μV :=
      ProbabilityTheory.IsGaussian.memLp_dual (μ := μV) (L := innerSL ℝ y2) 2 (by norm_num)
    have hC2U : MemLp (innerSL ℝ y1) 2 μU :=
      ProbabilityTheory.IsGaussian.memLp_dual (μ := μU) (L := innerSL ℝ y1) 2 (by norm_num)
    have hA2 : MemLp (fun ω => inner ℝ (std_basis N σ) (sim.V ω)) 2 (ℙ : Measure Ω) := by
      simpa [μV, Function.comp] using hA2V.comp_of_map (f := sim.V) (μ := (ℙ : Measure Ω)) sim.measV.aemeasurable
    have hB2 : MemLp (fun ω => inner ℝ y2 (sim.V ω)) 2 (ℙ : Measure Ω) := by
      simpa [μV, Function.comp] using hB2V.comp_of_map (f := sim.V) (μ := (ℙ : Measure Ω)) sim.measV.aemeasurable
    have hC2 : MemLp (fun ω => inner ℝ y1 (sk.U ω)) 2 (ℙ : Measure Ω) := by
      simpa [μU, Function.comp] using hC2U.comp_of_map (f := sk.U) (μ := (ℙ : Measure Ω)) sk.measU.aemeasurable
    have hAB_int : Integrable (fun ω => (inner ℝ (std_basis N σ) (sim.V ω)) * (inner ℝ y2 (sim.V ω)))
        (ℙ : Measure Ω) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using (hA2.integrable_mul hB2)
    have hAC_int : Integrable (fun ω => (inner ℝ (std_basis N σ) (sim.V ω)) * (inner ℝ y1 (sk.U ω)))
        (ℙ : Measure Ω) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using (hA2.integrable_mul hC2)
    have hsplit_int :
        (∫ ω,
            (inner ℝ (std_basis N σ) (sim.V ω)) *
              (inner ℝ y1 (sk.U ω) + inner ℝ y2 (sim.V ω)) ∂ℙ)
          =
          (∫ ω, (inner ℝ (std_basis N σ) (sim.V ω)) * (inner ℝ y1 (sk.U ω)) ∂ℙ)
          +
          (∫ ω, (inner ℝ (std_basis N σ) (sim.V ω)) * (inner ℝ y2 (sim.V ω)) ∂ℙ) := by
      simpa [mul_add, add_mul] using (MeasureTheory.integral_add (μ := (ℙ : Measure Ω))
        (f := fun ω => (inner ℝ (std_basis N σ) (sim.V ω)) * (inner ℝ y1 (sk.U ω)))
        (g := fun ω => (inner ℝ (std_basis N σ) (sim.V ω)) * (inner ℝ y2 (sim.V ω)))
        hAC_int hAB_int)
    calc
      inner ℝ (ProbabilityTheory.covarianceOperator μ (std_basis_right (N := N) σ)) y
          = ∫ ω,
              (inner ℝ (std_basis N σ) (sim.V ω)) *
                (inner ℝ y1 (sk.U ω) + inner ℝ y2 (sim.V ω)) ∂ℙ := hR
      _ = (∫ ω, (inner ℝ (std_basis N σ) (sim.V ω)) * (inner ℝ y1 (sk.U ω)) ∂ℙ)
          + (∫ ω, (inner ℝ (std_basis N σ) (sim.V ω)) * (inner ℝ y2 (sim.V ω)) ∂ℙ) := hsplit_int
      _ = (∫ ω, (inner ℝ (std_basis N σ) (sim.V ω)) * (inner ℝ y2 (sim.V ω)) ∂ℙ) := by simp [hcross]

  have hV :
      inner ℝ (ProbabilityTheory.covarianceOperator μV (std_basis N σ)) y2
        =
        ∫ ω, (inner ℝ (std_basis N σ) (sim.V ω)) * (inner ℝ y2 (sim.V ω)) ∂ℙ := by
    have hcov :
        inner ℝ (ProbabilityTheory.covarianceOperator μV (std_basis N σ)) y2
          =
          ∫ v : EnergySpace N, inner ℝ (std_basis N σ) v * inner ℝ y2 v ∂μV := by
      simpa [μV] using (ProbabilityTheory.covarianceOperator_inner (μ := μV) hμV (std_basis N σ) y2)
    let gV : EnergySpace N → ℝ := fun v => inner ℝ (std_basis N σ) v * inner ℝ y2 v
    have hgV_meas : Measurable gV := by
      have h1 : Measurable fun v : EnergySpace N => inner ℝ (std_basis N σ) v :=
        (innerSL ℝ (std_basis N σ)).measurable
      have h2 : Measurable fun v : EnergySpace N => inner ℝ y2 v :=
        (innerSL ℝ y2).measurable
      simpa [gV] using h1.mul h2
    have hmapV :
        (∫ v : EnergySpace N, gV v ∂μV) = ∫ ω, gV (sim.V ω) ∂ℙ := by
      simpa [μV] using
        (MeasureTheory.integral_map (μ := (ℙ : Measure Ω)) (φ := sim.V)
          (sim.measV.aemeasurable) (hgV_meas.aestronglyMeasurable))
    simpa [gV, hmapV] using hcov

  simpa [μ, μV, y2, SpinGlass.DisorderSpace, std_basis_right, WithLp.prod_inner_apply, real_inner_comm, hV]
    using hR'.trans hV.symm

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma covarianceOperator_disorderPairLaw_std_basis_left_eq_sum_sk
    {N : ℕ} {β h q : ℝ} (sk : SKDisorder (Ω := Ω) N β h) (sim : SimpleDisorder (Ω := Ω) N β q)
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V) (σ : Config N) :
    ProbabilityTheory.covarianceOperator
        (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
        (std_basis_left (N := N) σ)
      =
      ∑ τ : Config N, (sk_cov_kernel N β σ τ) • std_basis_left (N := N) τ := by
  classical
  have hdiag :=
    covarianceOperator_disorderPairLaw_std_basis_left
      (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) hindep σ
  have hsumU :
      ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map sk.U) (std_basis N σ)
        =
        ∑ τ : Config N, (sk_cov_kernel N β σ τ) • std_basis N τ :=
    SKDisorder.covarianceOperator_apply_std_basis_eq_sum (Ω := Ω) (N := N) (β := β) (h := h) sk σ
  refine (WithLp.ofLp_injective (p := (2 : ℝ≥0∞)) (V := EnergySpace N × EnergySpace N)) ?_
  have hL :
      WithLp.ofLp
          (ProbabilityTheory.covarianceOperator
              (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
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
  simpa [hL, hR] using this

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma covarianceOperator_disorderPairLaw_std_basis_right_eq_sum_simple
    {N : ℕ} {β h q : ℝ} (sk : SKDisorder (Ω := Ω) N β h) (sim : SimpleDisorder (Ω := Ω) N β q)
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V) (σ : Config N) :
    ProbabilityTheory.covarianceOperator
        (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
        (std_basis_right (N := N) σ)
      =
      ∑ τ : Config N,
        (simple_cov_kernel N β (fun x => q * x) σ τ) • std_basis_right (N := N) τ := by
  classical
  have hdiag :=
    covarianceOperator_disorderPairLaw_std_basis_right
      (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) hindep σ
  have hsumV :
      ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map sim.V) (std_basis N σ)
        =
        ∑ τ : Config N, (simple_cov_kernel N β (fun x => q * x) σ τ) • std_basis N τ :=
    SimpleDisorder.covarianceOperator_apply_std_basis_eq_sum (Ω := Ω) (N := N) (β := β) (q := q) sim σ
  refine (WithLp.ofLp_injective (p := (2 : ℝ≥0∞)) (V := EnergySpace N × EnergySpace N)) ?_
  have hL :
      WithLp.ofLp
          (ProbabilityTheory.covarianceOperator
              (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
              (std_basis_right (N := N) σ))
        =
        (0, ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map sim.V) (std_basis N σ)) := by
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
      (0, ProbabilityTheory.covarianceOperator ((ℙ : Measure Ω).map sim.V) (std_basis N σ))
        =
        ∑ τ : Config N,
          (simple_cov_kernel N β (fun x => q * x) σ τ) • ((0 : EnergySpace N), std_basis N τ) := by
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum]
    · simpa [Prod.snd_sum] using hsumV
  simpa [hL, hR] using this

end SpinGlass
