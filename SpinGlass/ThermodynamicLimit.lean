/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.GuerraToninelli
import SpinGlass.SKDisorderExists
import Common.Mathlib.Analysis.Superadditive

/-!
# The SK free energy as a sequence

Guerra–Toninelli superadditivity (`SpinGlass.mul_integral_free_energy_density_add_le`) compares
three disorders living on one probability space. To turn it into a statement about a *sequence*
`N ↦ N p_N`, the free energy must first be seen not to depend on the probability space:

* `GaussianDisorder.map_U_eq_multivariateGaussian` — the law of a Gaussian disorder is the
  canonical `multivariateGaussian` at its kernel matrix;
* `skFreeEnergy` — hence the SK free energy is a function of `N`, `β` and `h` alone, and
* `integral_free_energy_density_eq_skFreeEnergy` — every SK disorder on every probability space
  computes it.
-/

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology
open scoped ENNReal NNReal

namespace SpinGlass

noncomputable section

section Law

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ### The free energy is a function of the covariance alone -/

/-- **The free energy of a centered Gaussian disorder with covariance matrix `S`** in the external
field `h`, computed on the canonical Gaussian law. By
`integral_free_energy_density_eq_gaussFreeEnergy` every disorder with that covariance computes it,
so the free energy is a function of `(N, S, h)` alone. -/
def gaussFreeEnergy (N : ℕ) (S : Matrix (Config N) (Config N) ℝ) (h : ℝ) : ℝ :=
  ∫ H : EnergySpace N, free_energy_density (N := N) (H + H_field N h)
    ∂(multivariateGaussian (0 : EnergySpace N) S)

/-- **Every Gaussian disorder with covariance `S` computes `gaussFreeEnergy`.** -/
theorem integral_free_energy_density_eq_gaussFreeEnergy {N : ℕ}
    {S : Matrix (Config N) (Config N) ℝ}
    {K : Config N → Config N → ℝ} (hK : ∀ σ τ, K σ τ = S σ τ) (h : ℝ)
    (G : GaussianDisorder (Ω := Ω) (N := N) P K) :
    (∫ ω, free_energy_density (N := N) (G.U ω + H_field N h) ∂P) = gaussFreeEnergy N S h := by
  have hcont : Continuous fun H : EnergySpace N =>
      free_energy_density (N := N) (H + H_field N h) :=
    (contDiff_free_energy_density (N := N)).continuous.comp (continuous_id.add continuous_const)
  have hmap := MeasureTheory.integral_map (μ := P) (φ := G.U)
    (f := fun H : EnergySpace N => free_energy_density (N := N) (H + H_field N h))
    G.measU.aemeasurable hcont.aestronglyMeasurable
  rw [gaussFreeEnergy, ← hmap, GaussianDisorder.map_U_eq_multivariateGaussian hK G]

/-- **The SK free energy at size `N`**, inverse temperature `β` and external field `h`. This is the
sequence `p_N` of Talagrand Vol. I, §1.3. -/
def skFreeEnergy (N : ℕ) (β h : ℝ) : ℝ := gaussFreeEnergy N (skCovMatrix N β) h

/-- **Every SK disorder computes the SK free energy.** -/
theorem integral_free_energy_density_eq_skFreeEnergy {N : ℕ} {β : ℝ} (h : ℝ)
    (sk : GaussianDisorder (Ω := Ω) N P (sk_cov_kernel N β)) :
    (∫ ω, free_energy_density (N := N) (sk.U ω + H_field N h) ∂P) = skFreeEnergy N β h :=
  integral_free_energy_density_eq_gaussFreeEnergy (fun _ _ => rfl) h sk

end Law

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! ### The canonical splitting sample space

Guerra–Toninelli compares three Hamiltonians: the two block Hamiltonians and the whole-system one.
They must be carried by one probability space, with the composite of the two blocks independent of
the whole-system Hamiltonian. The canonical choice is the product of the three Gaussian laws. -/

/-- The canonical sample space for the Guerra–Toninelli comparison at sizes `N₁`, `N₂`: the two
block Hamiltonians and the whole-system Hamiltonian. A `def` rather than an `abbrev`, so that its
`MeasureSpace` structure is the disorder law and not a product of ambient volumes. -/
def SplitSample (N₁ N₂ : ℕ) : Type :=
  (EnergySpace N₁ × EnergySpace N₂) × EnergySpace (N₁ + N₂)

instance instMeasurableSpaceSplitSample (N₁ N₂ : ℕ) : MeasurableSpace (SplitSample N₁ N₂) :=
  inferInstanceAs
    (MeasurableSpace ((EnergySpace N₁ × EnergySpace N₂) × EnergySpace (N₁ + N₂)))

/-- The Hamiltonian of the first block. -/
def SplitSample.blockOne {N₁ N₂ : ℕ} (x : SplitSample N₁ N₂) : EnergySpace N₁ :=
  (show (EnergySpace N₁ × EnergySpace N₂) × EnergySpace (N₁ + N₂) from x).1.1

/-- The Hamiltonian of the second block. -/
def SplitSample.blockTwo {N₁ N₂ : ℕ} (x : SplitSample N₁ N₂) : EnergySpace N₂ :=
  (show (EnergySpace N₁ × EnergySpace N₂) × EnergySpace (N₁ + N₂) from x).1.2

/-- The Hamiltonian of the whole system. -/
def SplitSample.whole {N₁ N₂ : ℕ} (x : SplitSample N₁ N₂) : EnergySpace (N₁ + N₂) :=
  (show (EnergySpace N₁ × EnergySpace N₂) × EnergySpace (N₁ + N₂) from x).2

lemma measurable_blockOne (N₁ N₂ : ℕ) :
    Measurable (SplitSample.blockOne (N₁ := N₁) (N₂ := N₂)) :=
  measurable_fst.comp measurable_fst

lemma measurable_blockTwo (N₁ N₂ : ℕ) :
    Measurable (SplitSample.blockTwo (N₁ := N₁) (N₂ := N₂)) :=
  measurable_snd.comp measurable_fst

lemma measurable_whole (N₁ N₂ : ℕ) :
    Measurable (SplitSample.whole (N₁ := N₁) (N₂ := N₂)) :=
  measurable_snd

/-- The joint law of three independent centered Gaussians with prescribed covariance matrices. -/
def splitSampleLaw (N₁ N₂ : ℕ) (S₁ : Matrix (Config N₁) (Config N₁) ℝ)
    (S₂ : Matrix (Config N₂) (Config N₂) ℝ)
    (S : Matrix (Config (N₁ + N₂)) (Config (N₁ + N₂)) ℝ) : Measure (SplitSample N₁ N₂) :=
  ((multivariateGaussian (0 : EnergySpace N₁) S₁).prod
      (multivariateGaussian (0 : EnergySpace N₂) S₂)).prod
    (multivariateGaussian (0 : EnergySpace (N₁ + N₂)) S)

instance isProbabilityMeasure_splitSampleLaw (N₁ N₂ : ℕ)
    (S₁ : Matrix (Config N₁) (Config N₁) ℝ) (S₂ : Matrix (Config N₂) (Config N₂) ℝ)
    (S : Matrix (Config (N₁ + N₂)) (Config (N₁ + N₂)) ℝ) :
    IsProbabilityMeasure (splitSampleLaw N₁ N₂ S₁ S₂ S) :=
  inferInstanceAs (IsProbabilityMeasure
    (((multivariateGaussian (0 : EnergySpace N₁) S₁).prod
        (multivariateGaussian (0 : EnergySpace N₂) S₂)).prod
      (multivariateGaussian (0 : EnergySpace (N₁ + N₂)) S)))

/-- `SplitSample N₁ N₂` as a measure space carrying `splitSampleLaw`. -/
@[instance_reducible] def splitMeasureSpace (N₁ N₂ : ℕ)
    (S₁ : Matrix (Config N₁) (Config N₁) ℝ) (S₂ : Matrix (Config N₂) (Config N₂) ℝ)
    (S : Matrix (Config (N₁ + N₂)) (Config (N₁ + N₂)) ℝ) :
    MeasureSpace (SplitSample N₁ N₂) :=
  ⟨splitSampleLaw N₁ N₂ S₁ S₂ S⟩

/-! ### The three marginals -/

section Marginals

variable (N₁ N₂ : ℕ) (S₁ : Matrix (Config N₁) (Config N₁) ℝ)
  (S₂ : Matrix (Config N₂) (Config N₂) ℝ)
  (S : Matrix (Config (N₁ + N₂)) (Config (N₁ + N₂)) ℝ)

lemma map_fst_splitSampleLaw :
    (splitSampleLaw N₁ N₂ S₁ S₂ S).map
        (Prod.fst : (EnergySpace N₁ × EnergySpace N₂) × EnergySpace (N₁ + N₂) →
          EnergySpace N₁ × EnergySpace N₂)
      = (multivariateGaussian (0 : EnergySpace N₁) S₁).prod
          (multivariateGaussian (0 : EnergySpace N₂) S₂) := by
  have h := Measure.map_fst_prod
    (μ := (multivariateGaussian (0 : EnergySpace N₁) S₁).prod
      (multivariateGaussian (0 : EnergySpace N₂) S₂))
    (ν := multivariateGaussian (0 : EnergySpace (N₁ + N₂)) S)
  rw [measure_univ, one_smul] at h
  exact h

lemma map_blockOne_splitSampleLaw :
    (splitSampleLaw N₁ N₂ S₁ S₂ S).map (SplitSample.blockOne (N₁ := N₁) (N₂ := N₂))
      = multivariateGaussian (0 : EnergySpace N₁) S₁ := by
  have hinner := Measure.map_fst_prod
    (μ := multivariateGaussian (0 : EnergySpace N₁) S₁)
    (ν := multivariateGaussian (0 : EnergySpace N₂) S₂)
  rw [measure_univ, one_smul] at hinner
  calc (splitSampleLaw N₁ N₂ S₁ S₂ S).map (SplitSample.blockOne (N₁ := N₁) (N₂ := N₂))
      = ((splitSampleLaw N₁ N₂ S₁ S₂ S).map Prod.fst).map Prod.fst :=
        (Measure.map_map measurable_fst measurable_fst).symm
    _ = multivariateGaussian (0 : EnergySpace N₁) S₁ := by
        rw [map_fst_splitSampleLaw, hinner]

lemma map_blockTwo_splitSampleLaw :
    (splitSampleLaw N₁ N₂ S₁ S₂ S).map (SplitSample.blockTwo (N₁ := N₁) (N₂ := N₂))
      = multivariateGaussian (0 : EnergySpace N₂) S₂ := by
  have hinner := Measure.map_snd_prod
    (μ := multivariateGaussian (0 : EnergySpace N₁) S₁)
    (ν := multivariateGaussian (0 : EnergySpace N₂) S₂)
  rw [measure_univ, one_smul] at hinner
  calc (splitSampleLaw N₁ N₂ S₁ S₂ S).map (SplitSample.blockTwo (N₁ := N₁) (N₂ := N₂))
      = ((splitSampleLaw N₁ N₂ S₁ S₂ S).map Prod.fst).map Prod.snd :=
        (Measure.map_map measurable_snd measurable_fst).symm
    _ = multivariateGaussian (0 : EnergySpace N₂) S₂ := by
        rw [map_fst_splitSampleLaw, hinner]

lemma map_whole_splitSampleLaw :
    (splitSampleLaw N₁ N₂ S₁ S₂ S).map (SplitSample.whole (N₁ := N₁) (N₂ := N₂))
      = multivariateGaussian (0 : EnergySpace (N₁ + N₂)) S := by
  have h := Measure.map_snd_prod
    (μ := (multivariateGaussian (0 : EnergySpace N₁) S₁).prod
      (multivariateGaussian (0 : EnergySpace N₂) S₂))
    (ν := multivariateGaussian (0 : EnergySpace (N₁ + N₂)) S)
  rw [measure_univ, one_smul] at h
  exact h

end Marginals

/-! ### Three independent disorders at prescribed covariances -/

/-- **Three independent Gaussian disorders exist** at any three positive semidefinite covariance
matrices — on the first `N₁` sites, the last `N₂` sites and the whole system — with the
non-interacting composite of the first two independent of the third. This is the data that
Guerra's comparison consumes in a splitting argument. -/
theorem exists_disorder_triple (N₁ N₂ : ℕ) {S₁ : Matrix (Config N₁) (Config N₁) ℝ}
    {S₂ : Matrix (Config N₂) (Config N₂) ℝ}
    {S : Matrix (Config (N₁ + N₂)) (Config (N₁ + N₂)) ℝ}
    (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef) (hS : S.PosSemidef) :
    ∃ (Ω : Type) (_ : MeasureSpace Ω) (_ : IsProbabilityMeasure (ℙ : Measure Ω))
      (G₁ : GaussianDisorder (Ω := Ω) N₁ (ℙ : Measure Ω) (fun σ τ => S₁ σ τ))
      (G₂ : GaussianDisorder (Ω := Ω) N₂ (ℙ : Measure Ω) (fun σ τ => S₂ σ τ))
      (G : GaussianDisorder (Ω := Ω) (N₁ + N₂) (ℙ : Measure Ω) (fun σ τ => S σ τ))
      (h12 : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U),
      (GaussianDisorder.split G₁ G₂ h12).U ⟂ᵢ[(ℙ : Measure Ω)] G.U := by
  classical
  let inst : MeasureSpace (SplitSample N₁ N₂) := splitMeasureSpace N₁ N₂ S₁ S₂ S
  have hprob : IsProbabilityMeasure (ℙ : Measure (SplitSample N₁ N₂)) :=
    isProbabilityMeasure_splitSampleLaw N₁ N₂ S₁ S₂ S
  have hm1 : (ℙ : Measure (SplitSample N₁ N₂)).map SplitSample.blockOne
      = multivariateGaussian (0 : EnergySpace N₁) S₁ :=
    map_blockOne_splitSampleLaw N₁ N₂ S₁ S₂ S
  have hm2 : (ℙ : Measure (SplitSample N₁ N₂)).map SplitSample.blockTwo
      = multivariateGaussian (0 : EnergySpace N₂) S₂ :=
    map_blockTwo_splitSampleLaw N₁ N₂ S₁ S₂ S
  have hm3 : (ℙ : Measure (SplitSample N₁ N₂)).map SplitSample.whole
      = multivariateGaussian (0 : EnergySpace (N₁ + N₂)) S :=
    map_whole_splitSampleLaw N₁ N₂ S₁ S₂ S
  refine ⟨SplitSample N₁ N₂, inst, hprob,
    { U := SplitSample.blockOne
      measU := measurable_blockOne N₁ N₂
      hU := by
        have : ProbabilityTheory.IsGaussian
            ((ℙ : Measure (SplitSample N₁ N₂)).map SplitSample.blockOne) := by
          rw [hm1]; infer_instance
        exact ProbabilityTheory.IsGaussian.hasGaussianLaw
      mean0 := by rw [hm1]; simp
      cov_eq := fun σ τ => by
        rw [hm1]
        exact inner_covarianceOperator_multivariateGaussian_std_basis S₁ hS₁ σ τ },
    { U := SplitSample.blockTwo
      measU := measurable_blockTwo N₁ N₂
      hU := by
        have : ProbabilityTheory.IsGaussian
            ((ℙ : Measure (SplitSample N₁ N₂)).map SplitSample.blockTwo) := by
          rw [hm2]; infer_instance
        exact ProbabilityTheory.IsGaussian.hasGaussianLaw
      mean0 := by rw [hm2]; simp
      cov_eq := fun σ τ => by
        rw [hm2]
        exact inner_covarianceOperator_multivariateGaussian_std_basis S₂ hS₂ σ τ },
    { U := SplitSample.whole
      measU := measurable_whole N₁ N₂
      hU := by
        have : ProbabilityTheory.IsGaussian
            ((ℙ : Measure (SplitSample N₁ N₂)).map SplitSample.whole) := by
          rw [hm3]; infer_instance
        exact ProbabilityTheory.IsGaussian.hasGaussianLaw
      mean0 := by rw [hm3]; simp
      cov_eq := fun σ τ => by
        rw [hm3]
        exact inner_covarianceOperator_multivariateGaussian_std_basis S hS σ τ },
    ?_, ?_⟩
  · refine (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      (measurable_blockOne N₁ N₂).aemeasurable
      (measurable_blockTwo N₁ N₂).aemeasurable).2 ?_
    have hjoint : (ℙ : Measure (SplitSample N₁ N₂)).map
        (fun x => (SplitSample.blockOne x, SplitSample.blockTwo x))
        = (multivariateGaussian (0 : EnergySpace N₁) S₁).prod
            (multivariateGaussian (0 : EnergySpace N₂) S₂) :=
      map_fst_splitSampleLaw N₁ N₂ S₁ S₂ S
    rw [hjoint, hm1, hm2]
  · exact ProbabilityTheory.indepFun_prod
      (μ := (multivariateGaussian (0 : EnergySpace N₁) S₁).prod
        (multivariateGaussian (0 : EnergySpace N₂) S₂))
      (ν := multivariateGaussian (0 : EnergySpace (N₁ + N₂)) S)
      (X := fun p => FiniteGibbs.sumEnergy (configSplit N₁ N₂) p) (Y := id)
      (FiniteGibbs.sumEnergy (configSplit N₁ N₂)).continuous.measurable measurable_id

/-! ### Superadditivity of the sequence `N ↦ N p_N` -/

/-- **Guerra–Toninelli superadditivity for the SK free-energy sequence.**
`N₁ p_{N₁} + N₂ p_{N₂} ≤ (N₁ + N₂) p_{N₁+N₂}`, with `p_N = skFreeEnergy N β h`.
Talagrand Vol. I, Theorem 1.3.9. -/
theorem mul_skFreeEnergy_add_le {N₁ N₂ : ℕ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (β h : ℝ) :
    (N₁ : ℝ) * skFreeEnergy N₁ β h + (N₂ : ℝ) * skFreeEnergy N₂ β h
      ≤ ((N₁ + N₂ : ℕ) : ℝ) * skFreeEnergy (N₁ + N₂) β h := by
  classical
  obtain ⟨Ω, instΩ, instP, G₁, G₂, G, h12, hsplit⟩ :=
    exists_disorder_triple N₁ N₂ (posSemidef_skCovMatrix N₁ β) (posSemidef_skCovMatrix N₂ β)
      (posSemidef_skCovMatrix (N₁ + N₂) β)
  have hGT := mul_integral_free_energy_density_add_le (Ω := Ω) hN₁ hN₂ h G₁ G₂ G h12 hsplit
  rwa [integral_free_energy_density_eq_skFreeEnergy h G₁,
    integral_free_energy_density_eq_skFreeEnergy h G₂,
    integral_free_energy_density_eq_skFreeEnergy h G] at hGT

/-! ### An upper bound uniform in `N`

Guerra's bound at the trivial order parameter `q = 0` compares the SK free energy with the free
energy of the *deterministic* Hamiltonian `H_field N h`, which is bounded by `log 2 + |h|` because
`|m(σ)| ≤ N`. This supplies the `BddAbove` hypothesis of Fekete's lemma. -/

/-- **The trivial disorder.** The zero Hamiltonian is a centered Gaussian disorder with the
replica-symmetric kernel at `q = 0` (which vanishes identically). -/
def simpleDisorderZero {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (N : ℕ) (β : ℝ) : SimpleDisorder (Ω := Ω) N β 0 where
  U := fun _ => 0
  measU := measurable_const
  hU := by
    have hmap : (ℙ : Measure Ω).map (fun _ : Ω => (0 : EnergySpace N))
        = Measure.dirac 0 := by rw [Measure.map_const]; simp
    have : ProbabilityTheory.IsGaussian
        ((ℙ : Measure Ω).map (fun _ : Ω => (0 : EnergySpace N))) := by
      rw [hmap]; infer_instance
    exact ProbabilityTheory.IsGaussian.hasGaussianLaw
  mean0 := by rw [Measure.map_const]; simp
  cov_eq := fun σ τ => by
    have hmap : (ℙ : Measure Ω).map (fun _ : Ω => (0 : EnergySpace N))
        = Measure.dirac 0 := by rw [Measure.map_const]; simp
    rw [hmap]
    have hmem : MeasureTheory.MemLp (id : EnergySpace N → EnergySpace N) 2
        (Measure.dirac (0 : EnergySpace N)) := ProbabilityTheory.IsGaussian.memLp_two_id
    rw [ProbabilityTheory.covarianceOperator_inner hmem]
    simp [simple_cov_kernel_eq]

/-- The magnetization of a configuration of `N` sites is at most `N` in absolute value. -/
lemma abs_magnetization_le (N : ℕ) (σ : Config N) : |magnetization N σ| ≤ (N : ℝ) := by
  calc |magnetization N σ| ≤ ∑ i : Fin N, |isingSpin (σ i)| := by
        simpa [magnetization, magnetizationOf, spinOf] using
          Finset.abs_sum_le_sum_abs (fun i : Fin N => isingSpin (σ i)) Finset.univ
    _ = (N : ℝ) := by simp [abs_isingSpin_eq_one]

/-- **A uniform bound on the free-energy density from a bound on the Hamiltonian.** If
`-H σ ≤ b` for every configuration then `F_N(H) ≤ log 2 + b/N`; there are `2^N` configurations. -/
lemma free_energy_density_le_of_neg_le {N : ℕ} (hN : 0 < N) {H : EnergySpace N} {b : ℝ}
    (hb : ∀ σ, -H σ ≤ b) : free_energy_density (N := N) H ≤ Real.log 2 + b / N := by
  classical
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcard : (Fintype.card (Config N) : ℝ) = 2 ^ N := by
    simp
  have hZ : Z N H ≤ (2 : ℝ) ^ N * Real.exp b := by
    calc Z N H = ∑ σ : Config N, Real.exp (-H σ) := rfl
      _ ≤ ∑ _σ : Config N, Real.exp b :=
          Finset.sum_le_sum fun σ _ => Real.exp_le_exp.mpr (hb σ)
      _ = (Fintype.card (Config N) : ℝ) * Real.exp b := by
          simp [Finset.sum_const, Finset.card_univ]
      _ = (2 : ℝ) ^ N * Real.exp b := by rw [hcard]
  have hlog : Real.log (Z N H) ≤ (N : ℝ) * Real.log 2 + b := by
    calc Real.log (Z N H) ≤ Real.log ((2 : ℝ) ^ N * Real.exp b) :=
          Real.log_le_log (Z_pos N H) hZ
      _ = (N : ℝ) * Real.log 2 + b := by
          rw [Real.log_mul (by positivity) (Real.exp_ne_zero b), Real.log_pow, Real.log_exp]
  have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt (by positivity : (0 : ℝ) < 1 / (N : ℝ)))
  calc free_energy_density (N := N) H = (1 / (N : ℝ)) * Real.log (Z N H) := rfl
    _ ≤ (1 / (N : ℝ)) * ((N : ℝ) * Real.log 2 + b) := hmul
    _ = Real.log 2 + b / N := by field_simp

/-- The free-energy density of the pure external field is at most `log 2 + |h|`. -/
lemma free_energy_density_H_field_le {N : ℕ} (hN : 0 < N) (h : ℝ) :
    free_energy_density (N := N) (H_field N h) ≤ Real.log 2 + |h| := by
  have hb : ∀ σ : Config N, -(H_field N h) σ ≤ |h| * N := by
    intro σ
    have h1 : -(H_field N h) σ = -(h * magnetization N σ) := rfl
    have h2 : |h * magnetization N σ| ≤ |h| * N := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_magnetization_le N σ) (abs_nonneg h)
    calc -(H_field N h) σ = -(h * magnetization N σ) := h1
      _ ≤ |h * magnetization N σ| := neg_le_abs _
      _ ≤ |h| * N := h2
  have := free_energy_density_le_of_neg_le hN hb
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rwa [mul_div_assoc, div_self hNR.ne', mul_one] at this

/-- **The SK free energy is bounded above uniformly in `N`.** Guerra's bound at `q = 0` compares it
with the free energy of the pure external field. Talagrand Vol. I, §1.3. -/
theorem skFreeEnergy_le {N : ℕ} (hN : 0 < N) (β h : ℝ) :
    skFreeEnergy N β h ≤ Real.log 2 + |h| + β ^ 2 / 4 := by
  classical
  obtain ⟨Ω, instΩ, instP, sk, -, -⟩ :=
    exists_skDisorder_simpleDisorder_indepFun N β 0 le_rfl
  have hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] (simpleDisorderZero (Ω := Ω) N β).U :=
    ProbabilityTheory.indepFun_const_right sk.U (0 : EnergySpace N)
  have hle := integral_free_energy_density_le_rs (Ω := Ω) h hN sk
    (simpleDisorderZero (Ω := Ω) N β) hindep
  rw [integral_free_energy_density_eq_skFreeEnergy h sk] at hle
  have hconst : (∫ _ω : Ω, free_energy_density (N := N)
      ((simpleDisorderZero (Ω := Ω) N β).U _ω + H_field N h) ∂ℙ)
      = free_energy_density (N := N) (H_field N h) := by
    simp [simpleDisorderZero]
  rw [hconst] at hle
  have hfield := free_energy_density_H_field_le (N := N) hN h
  nlinarith [hle, hfield]

/-! ### The thermodynamic limit -/

/-- **`N ↦ N p_N` is superadditive**, by Guerra–Toninelli. -/
theorem superadditive_mul_skFreeEnergy (β h : ℝ) :
    Superadditive (fun N : ℕ => (N : ℝ) * skFreeEnergy N β h) := by
  intro m n
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  exact mul_skFreeEnergy_add_le hm hn β h

/-- The averages `p_N` are bounded above, uniformly in `N`. -/
theorem bddAbove_skFreeEnergy (β h : ℝ) :
    BddAbove (Set.range fun N : ℕ => ((N : ℝ) * skFreeEnergy N β h) / N) := by
  refine ⟨Real.log 2 + |h| + β ^ 2 / 4, ?_⟩
  rintro y ⟨N, rfl⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h3 : (0 : ℝ) ≤ β ^ 2 / 4 := by positivity
    simp only [Nat.cast_zero, zero_mul, zero_div]
    linarith [abs_nonneg h]
  · have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    simp only []
    rw [mul_div_cancel_left₀ _ hNR.ne']
    exact skFreeEnergy_le hN β h

/-- **The SK free energy in the thermodynamic limit**, `p(β,h) = lim_N p_N(β,h)`.
Talagrand Vol. I, Theorem 1.3.9. -/
def skFreeEnergyLimit (β h : ℝ) : ℝ := (superadditive_mul_skFreeEnergy β h).lim

/-- **The thermodynamic limit of the SK free energy exists**: `p_N(β,h) → p(β,h)`.
Fekete's lemma applied to the superadditive sequence `N ↦ N p_N`, whose averages are bounded above
by `log 2 + |h| + β²/4`. Talagrand Vol. I, Theorem 1.3.9. -/
theorem tendsto_skFreeEnergy (β h : ℝ) :
    Filter.Tendsto (fun N : ℕ => skFreeEnergy N β h) Filter.atTop
      (nhds (skFreeEnergyLimit β h)) := by
  have hfek := (superadditive_mul_skFreeEnergy β h).tendsto_lim (bddAbove_skFreeEnergy β h)
  refine hfek.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with N hN
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [mul_div_cancel_left₀ _ hNR.ne']

/-- **The limit is the supremum**: every finite-volume free energy is below it.
Talagrand Vol. I, Theorem 1.3.9. -/
theorem skFreeEnergy_le_limit (β h : ℝ) {N : ℕ} (hN : N ≠ 0) :
    skFreeEnergy N β h ≤ skFreeEnergyLimit β h := by
  have hNR : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hN
  have := (superadditive_mul_skFreeEnergy β h).div_le_lim (bddAbove_skFreeEnergy β h) hN
  rwa [mul_div_cancel_left₀ _ hNR.ne'] at this

end

end SpinGlass
