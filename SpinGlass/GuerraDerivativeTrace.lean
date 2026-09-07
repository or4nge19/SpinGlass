/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.GuerraInterpolation
import SpinGlass.GaussianTrace

/-!
# Guerra interpolation: the derivative as a covariance/Hessian trace

Talagrand's computation of `φ'(t)` for the interpolating free energy `φ(t) = 𝔼 F_N(H_t)` is one
instance of the general Gaussian interpolation trace identity
`ProbabilityTheory.IsGaussian.integral_fderiv_gaussianInterp_apply_deriv_eq_sum`: the interpolated
Hamiltonian is `H_t = Z_t x + h·1` where `Z_t = √t · fst + √(1-t) · snd` is
`ProbabilityTheory.gaussianInterp` on the disorder space and `Ż_t` is
`ProbabilityTheory.gaussianInterpDeriv`. The covariance of `disorderPairLaw` is block diagonal
with the SK and reference kernels as its blocks, so the general identity applies directly; all
that remains at the model level is to expand those blocks in the Dirac basis, which turns the two
covariance-weighted Hessian traces into Talagrand's kernel-weighted double sums.

Nothing here integrates by parts: the Gaussian analysis lives entirely in
`Common.Mathlib.Probability.Distributions.Gaussian_Interpolation` and its prerequisites.

## Main statements

- `integrable_kernel_mul_hessian`, `integrable_trace_kernel_hessian`: the kernel-weighted Hessian
  and its trace are integrable under the disorder law (the Hessian is bounded by `2/N`).
- `derivative_value_guerraPhi_eq_trace_integral`: the trace identity for `φ'(t)`,
  Talagrand Vol. I, §1.3, Eq. (1.65).
-/

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology
open scoped ENNReal NNReal

namespace SpinGlass

noncomputable section

variable {N : ℕ}

section Disorder

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable (β h q : ℝ)
variable (sk : SKDisorder (Ω := Ω) (N := N) β) (sim : SimpleDisorder (Ω := Ω) (N := N) β q)

private abbrev μ : Measure (DisorderSpace (N := N)) :=
  disorderPairLaw (Ω := Ω) (N := N) (β := β) (q := q) (sk := sk) (sim := sim)

/-! ### Integrability of the kernel-weighted Hessian trace -/

private lemma hessian_free_energy_std_basis_eq
    (H : EnergySpace N) (σ τ : Config N) :
    hessian_free_energy N H (std_basis N σ) (std_basis N τ)
      =
      (1 / (N : ℝ)) *
        (gibbs_pmf N H σ * (if σ = τ then 1 else 0) - gibbs_pmf N H σ * gibbs_pmf N H τ) := by
  simpa [hessian_free_energy, Z, gibbs_pmf, std_basis, FiniteGibbs.hessian_free_energy,
    FiniteGibbs.Z,
    FiniteGibbs.gibbs_pmf, FiniteGibbs.std_basis, eq_comm] using
    (FiniteGibbs.hessian_free_energy_std_basis_eq (α := Config N) (n := N) (H := H) (σ := σ) (τ :=
      τ))

private lemma measurable_gibbs_pmf_disorder (t : ℝ) (σ : Config N) :
    Measurable (fun x : DisorderSpace (N := N) =>
      gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ) := by
  exact (contDiff_gibbs_pmf_disorder (N := N) (h := h) (t := t) σ).continuous.measurable


omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
private lemma aestronglyMeasurable_hessian_std_basis_disorder (t : ℝ) (σ τ : Config N) :
    AEStronglyMeasurable (fun x : DisorderSpace (N := N) =>
      hessian_free_energy N (H_t_disorder (N := N) (h := h) t x) (std_basis N σ) (std_basis N τ))
      (μ (Ω := Ω) (N := N) (β := β) (q := q) sk sim) := by
  classical
  have hσ := measurable_gibbs_pmf_disorder (N := N) (h := h) (t := t) σ
  have hτ := measurable_gibbs_pmf_disorder (N := N) (h := h) (t := t) τ
  have hδ : Measurable (fun _x : DisorderSpace (N := N) => (if σ = τ then (1 : ℝ) else 0)) :=
    measurable_const
  have hmeas :
      Measurable (fun x : DisorderSpace (N := N) =>
        hessian_free_energy N (H_t_disorder (N := N) (h := h) t x) (std_basis N σ) (std_basis N τ))
          := by
    have hEq : (fun x : DisorderSpace (N := N) =>
        hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
          (std_basis N σ) (std_basis N τ))
        = fun x : DisorderSpace (N := N) => (1 / (N : ℝ)) *
            (gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ * (if σ = τ then 1 else 0)
              - gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ
                * gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) :=
      funext fun x => hessian_free_energy_std_basis_eq (N := N)
        (H := H_t_disorder (N := N) (h := h) t x) (σ := σ) (τ := τ)
    rw [hEq]
    exact measurable_const.mul ((hσ.mul hδ).sub (hσ.mul hτ))
  exact hmeas.aestronglyMeasurable

private lemma abs_hessian_std_basis_le (H : EnergySpace N) (σ τ : Config N) :
    |hessian_free_energy N H (std_basis N σ) (std_basis N τ)| ≤ |(1 / (N : ℝ))| * 2 := by
  classical
  set gσ : ℝ := gibbs_pmf N H σ
  set gτ : ℝ := gibbs_pmf N H τ
  have hσ : |gσ| ≤ 1 := by
    have hle : gibbs_pmf N H σ ≤ 1 := gibbs_pmf_le_one (N := N) (H := H) (σ := σ)
    have hn : 0 ≤ gibbs_pmf N H σ := gibbs_pmf_nonneg (N := N) (H := H) (σ := σ)
    simpa [gσ, abs_of_nonneg hn] using hle
  have hτ : |gτ| ≤ 1 := by
    have hle : gibbs_pmf N H τ ≤ 1 := gibbs_pmf_le_one (N := N) (H := H) (σ := τ)
    have hn : 0 ≤ gibbs_pmf N H τ := gibbs_pmf_nonneg (N := N) (H := H) (σ := τ)
    simpa [gτ, abs_of_nonneg hn] using hle
  have hδ : |(if σ = τ then (1 : ℝ) else 0)| ≤ 1 := by
    by_cases hστ : σ = τ <;> simp [hστ]
  have h1 : |gσ * (if σ = τ then (1 : ℝ) else 0)| ≤ 1 := by
    by_cases hστ : σ = τ
    · subst hστ
      simpa using hσ
    · simp [hστ]
  have h2 : |gσ * gτ| ≤ 1 := by
    calc
      |gσ * gτ| = |gσ| * |gτ| := by simp [abs_mul]
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := by ring
  have hins : |gσ * (if σ = τ then (1 : ℝ) else 0) - gσ * gτ| ≤ 2 := by
    have h' : |gσ * (if σ = τ then (1 : ℝ) else 0) - gσ * gτ|
        ≤ |gσ * (if σ = τ then (1 : ℝ) else 0)| + |gσ * gτ| := by
      -- `|a-b| ≤ |a| + |b|`
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        (abs_sub_le (gσ * (if σ = τ then (1 : ℝ) else 0)) 0 (gσ * gτ))
    exact le_trans h' (by nlinarith [h1, h2])
  simpa [hessian_free_energy_std_basis_eq (N := N) (H := H), gσ, gτ, abs_mul, mul_assoc, mul_comm,
    mul_left_comm]
    using (mul_le_mul_of_nonneg_left hins (abs_nonneg (1 / (N : ℝ))))

/-- A kernel-weighted entry of the free-energy Hessian is integrable under the disorder law:
the Hessian is bounded by `2/N` uniformly in the Hamiltonian. -/
theorem integrable_kernel_mul_hessian
    (t : ℝ) (K : Config N → Config N → ℝ) (σ τ : Config N) :
    Integrable (fun x : DisorderSpace (N := N) =>
        (K σ τ) *
          hessian_free_energy N (H_t_disorder (N := N) (h := h) t x) (std_basis N σ) (std_basis N
            τ))
      (μ (Ω := Ω) (N := N) (β := β) (q := q) sk sim) := by
  classical
  let μ0 := μ (Ω := Ω) (N := N) (β := β) (q := q) sk sim
  have : IsFiniteMeasure μ0 := by infer_instance
  refine Integrable.of_bound (μ := μ0)
    ((aestronglyMeasurable_hessian_std_basis_disorder (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) (t := t) σ τ).const_mul (K σ τ))
    (|(K σ τ)| * (|(1 / (N : ℝ))| * 2)) ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  have hhess :=
    abs_hessian_std_basis_le (N := N) (H := H_t_disorder (N := N) (h := h) t x) (σ := σ) (τ := τ)
  have : |(K σ τ) *
        hessian_free_energy N (H_t_disorder (N := N) (h := h) t x) (std_basis N σ) (std_basis N τ)|
      ≤ |K σ τ| * (|1 / (N : ℝ)| * 2) := by
    simpa [abs_mul, mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_left hhess (abs_nonneg (K σ τ)))
  simpa [Real.norm_eq_abs] using this

/-- The kernel-weighted Hessian **trace** is integrable under the disorder law. -/
theorem integrable_trace_kernel_hessian (t : ℝ) (K : Config N → Config N → ℝ) :
    Integrable (fun x : DisorderSpace (N := N) =>
        ∑ σ : Config N, ∑ τ : Config N, K σ τ *
          hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
            (std_basis N σ) (std_basis N τ))
      (μ (Ω := Ω) (N := N) (β := β) (q := q) sk sim) := by
  classical
  refine MeasureTheory.integrable_finsetSum (s := (Finset.univ : Finset (Config N)))
    (f := fun σ x => ∑ τ : Config N, K σ τ *
      hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
        (std_basis N σ) (std_basis N τ)) (fun σ _ => ?_)
  exact MeasureTheory.integrable_finsetSum (s := (Finset.univ : Finset (Config N)))
    (f := fun τ x => K σ τ *
      hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
        (std_basis N σ) (std_basis N τ))
    (fun τ _ => integrable_kernel_mul_hessian (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) t K σ τ)

/-! ### The Guerra derivative as a covariance/Hessian trace -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Change of variables: the derivative value, an integral over `Ω`, is an integral of the
`DisorderSpace`-level integrand against the disorder law. -/
private lemma integral_derivative_value_eq_integral_disorderPairLaw (t : ℝ) :
    (∫ ω,
        (fderiv ℝ (fun H' : EnergySpace N => free_energy_density (N := N) H')
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω))
          (dH_t (N := N) (β := β) (q := q) (sk := sk) (sim := sim) t ω)
        ∂(ℙ : Measure Ω))
      =
      ∫ x : DisorderSpace (N := N),
        (fderiv ℝ (fun H' : EnergySpace N => free_energy_density (N := N) H')
            (H_t_disorder (N := N) (h := h) t x))
          (gaussianInterpDeriv (E := EnergySpace N) t x)
        ∂(μ (Ω := Ω) (N := N) (β := β) (q := q) sk sim) := by
  classical
  have hcont :
      Continuous fun x : DisorderSpace (N := N) =>
        (fderiv ℝ (fun H' : EnergySpace N => free_energy_density (N := N) H')
            (H_t_disorder (N := N) (h := h) t x))
          (gaussianInterpDeriv (E := EnergySpace N) t x) := by
    have hfd : Continuous
        (fderiv ℝ fun H' : EnergySpace N => free_energy_density (N := N) H') :=
      (FiniteGibbs.contDiff_free_energy_density (α := Config N) (n := N)).continuous_fderiv
        (by simp)
    have hH : Continuous (H_t_disorder (N := N) (h := h) t) :=
      (gaussianInterp (E := EnergySpace N) t).continuous.add continuous_const
    exact (hfd.comp hH).clm_apply (gaussianInterpDeriv (E := EnergySpace N) t).continuous
  rw [MeasureTheory.integral_map
    (measurable_disorderPair (Ω := Ω) (N := N) (β := β) (q := q)
      (sk := sk) (sim := sim)).aemeasurable hcont.aestronglyMeasurable]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp)

/-- The second derivative of the free-energy density, read on the Dirac basis, is Talagrand's
Gibbs covariance `hessian_free_energy`. -/
private lemma fderiv_fderiv_free_energy_density_std_basis
    (H : EnergySpace N) (σ τ : Config N) :
    ((fderiv ℝ (fderiv ℝ (fun H' : EnergySpace N => free_energy_density (N := N) H')) H)
        (std_basis N σ)) (std_basis N τ)
      = hessian_free_energy N H (std_basis N σ) (std_basis N τ) :=
  hessian_free_energy_fderiv_eq_hessian_free_energy (N := N) H (std_basis N σ) (std_basis N τ)

private lemma integrable_half_kernel_hessian
    (t : ℝ) (K : Config N → Config N → ℝ) (a : ℝ) (σ : Config N) :
    Integrable (fun x : DisorderSpace (N := N) =>
        ∑ τ : Config N, (a * K σ τ) *
          hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
            (std_basis N τ) (std_basis N σ))
      (μ (Ω := Ω) (N := N) (β := β) (q := q) sk sim) :=
  MeasureTheory.integrable_finsetSum (s := (Finset.univ : Finset (Config N)))
    (f := fun τ x => (a * K σ τ) *
      hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
        (std_basis N τ) (std_basis N σ))
    (fun τ _ => integrable_kernel_mul_hessian (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) t (fun c d => a * K d c) τ σ)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The covariance of `disorderPairLaw` on the left (SK) block, in the shape the general
interpolation trace identity consumes. -/
private lemma covarianceOperator_disorderPairLaw_toLp_left
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.U) (σ : Config N) :
    covarianceOperator (μ (Ω := Ω) (N := N) (β := β) (q := q) sk sim)
        (WithLp.toLp 2 (std_basis N σ, (0 : EnergySpace N)))
      = WithLp.toLp 2 ((∑ τ : Config N, sk_cov_kernel N β σ τ • std_basis N τ),
          (0 : EnergySpace N)) := by
  classical
  rw [show WithLp.toLp 2 (std_basis N σ, (0 : EnergySpace N)) = std_basis_left (N := N) σ from rfl,
    covarianceOperator_disorderPairLaw_std_basis_left_eq_sum_sk
    (Ω := Ω) (N := N) (β := β) (q := q) (sk := sk) (sim := sim) hindep σ]
  rw [← WithLp.toLp_sum]
  refine congrArg (WithLp.toLp 2) ?_
  rw [Prod.ext_iff]
  simp [std_basis_left, Prod.fst_sum, Prod.snd_sum]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The covariance of `disorderPairLaw` on the right (reference) block. -/
private lemma covarianceOperator_disorderPairLaw_toLp_right
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.U) (σ : Config N) :
    covarianceOperator (μ (Ω := Ω) (N := N) (β := β) (q := q) sk sim)
        (WithLp.toLp 2 ((0 : EnergySpace N), std_basis N σ))
      = WithLp.toLp 2 ((0 : EnergySpace N),
          (∑ τ : Config N, simple_cov_kernel N β (fun r => q * r) σ τ • std_basis N τ)) := by
  classical
  rw [show WithLp.toLp 2 ((0 : EnergySpace N), std_basis N σ) = std_basis_right (N := N) σ from rfl,
    covarianceOperator_disorderPairLaw_std_basis_right_eq_sum_simple
    (Ω := Ω) (N := N) (β := β) (q := q) (sk := sk) (sim := sim) hindep σ]
  rw [← WithLp.toLp_sum]
  refine congrArg (WithLp.toLp 2) ?_
  rw [Prod.ext_iff]
  simp [std_basis_right, Prod.fst_sum, Prod.snd_sum]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Expanding a covariance image in the Dirac basis turns one trace term of the general
interpolation identity into Talagrand's kernel-weighted Hessian double sum. -/
private lemma sum_integral_fderiv2_covariance_image_eq
    (t : ℝ) (K : Config N → Config N → ℝ) (hKsymm : ∀ σ τ, K σ τ = K τ σ) (a : ℝ)
    (hint : ∀ σ : Config N, Integrable (fun x : DisorderSpace (N := N) =>
        ∑ τ : Config N, (a * K σ τ) *
          hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
            (std_basis N τ) (std_basis N σ))
      (μ (Ω := Ω) (N := N) (β := β) (q := q) sk sim)) :
    (∑ σ : Config N, a * ∫ x : DisorderSpace (N := N),
        ((fderiv ℝ (fderiv ℝ (fun H' : EnergySpace N => free_energy_density (N := N) H'))
              (H_t_disorder (N := N) (h := h) t x))
            (∑ τ : Config N, K σ τ • std_basis N τ))
          (std_basis N σ)
        ∂(μ (Ω := Ω) (N := N) (β := β) (q := q) sk sim))
      =
      ∫ x : DisorderSpace (N := N),
        a * (∑ σ : Config N, ∑ τ : Config N, K σ τ *
              hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
                (std_basis N σ) (std_basis N τ))
        ∂(μ (Ω := Ω) (N := N) (β := β) (q := q) sk sim) := by
  classical
  -- Expand the covariance image and pull the scalar `a` inside.
  have hterm : ∀ (σ : Config N) (x : DisorderSpace (N := N)),
      a * (((fderiv ℝ (fderiv ℝ (fun H' : EnergySpace N => free_energy_density (N := N) H'))
              (H_t_disorder (N := N) (h := h) t x))
            (∑ τ : Config N, K σ τ • std_basis N τ))
          (std_basis N σ))
        = ∑ τ : Config N, (a * K σ τ) *
            hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
              (std_basis N τ) (std_basis N σ) := by
    intro σ x
    rw [map_sum, sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_smul, smul_apply, smul_eq_mul,
      fderiv_fderiv_free_energy_density_std_basis (N := N)]
    ring
  have hstep : ∀ σ : Config N,
      a * (∫ x : DisorderSpace (N := N),
          ((fderiv ℝ (fderiv ℝ (fun H' : EnergySpace N => free_energy_density (N := N) H'))
                (H_t_disorder (N := N) (h := h) t x))
              (∑ τ : Config N, K σ τ • std_basis N τ))
            (std_basis N σ)
          ∂(μ (Ω := Ω) (N := N) (β := β) (q := q) sk sim))
        = ∫ x : DisorderSpace (N := N),
            (∑ τ : Config N, (a * K σ τ) *
              hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
                (std_basis N τ) (std_basis N σ))
            ∂(μ (Ω := Ω) (N := N) (β := β) (q := q) sk sim) := by
    intro σ
    rw [← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (hterm σ))
  rw [Finset.sum_congr rfl fun σ (_ : σ ∈ Finset.univ) => hstep σ,
    ← MeasureTheory.integral_finsetSum _ fun σ (_ : σ ∈ Finset.univ) => hint σ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  set Hs : Config N → Config N → ℝ := fun σ τ =>
    hessian_free_energy N (H_t_disorder (N := N) (h := h) t x) (std_basis N σ) (std_basis N τ)
    with hHs
  calc
    (∑ σ : Config N, ∑ τ : Config N, (a * K σ τ) * Hs τ σ)
        = a * ∑ σ : Config N, ∑ τ : Config N, K σ τ * Hs τ σ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun τ _ => by ring
    _ = a * ∑ σ : Config N, ∑ τ : Config N, K σ τ * Hs σ τ := by
          congr 1
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun σ _ =>
            Finset.sum_congr rfl fun τ _ => by rw [hKsymm]

/-- **Talagrand's covariance/Hessian formula for the Guerra derivative**, Vol. I, §1.3,
Eq. (1.65). This is the general Gaussian interpolation trace identity
`ProbabilityTheory.IsGaussian.integral_fderiv_gaussianInterp_apply_deriv_eq_sum` at the SK
disorder: the covariance of `disorderPairLaw` is block diagonal with the SK and reference kernels
as blocks, and expanding those blocks in the Dirac basis produces Talagrand's kernel-weighted
Hessian double sums. -/
theorem derivative_value_guerraPhi_eq_trace_integral
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.U)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ ω,
        (fderiv ℝ (fun H' : EnergySpace N => free_energy_density (N := N) H')
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω))
          (dH_t (N := N) (β := β) (q := q) (sk := sk) (sim := sim) t ω)
        ∂(ℙ : Measure Ω))
      =
      ∫ x : DisorderSpace (N := N),
        (1 / 2 : ℝ) *
          ( (∑ σ : Config N, ∑ τ : Config N,
                sk_cov_kernel N β σ τ *
                  hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
                    (std_basis N σ) (std_basis N τ))
            -
            (∑ σ : Config N, ∑ τ : Config N,
                simple_cov_kernel N β (fun r => q * r) σ τ *
                  hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
                    (std_basis N σ) (std_basis N τ)) )
        ∂(μ (Ω := Ω) (N := N) (β := β) (q := q) sk sim) := by
  classical
  have hgauss : ProbabilityTheory.IsGaussian
      (μ (Ω := Ω) (N := N) (β := β) (q := q) sk sim) :=
    SKDisorder.simple_joint_isGaussian_disorderPairLaw_of_indep (Ω := Ω) (N := N) sk sim hindep
  -- (1) The general Gaussian interpolation trace identity, at the block covariance of the
  -- disorder law.
  have hgen :
      (∫ x : DisorderSpace (N := N),
          (fderiv ℝ (fun H' : EnergySpace N => free_energy_density (N := N) H')
              (H_t_disorder (N := N) (h := h) t x))
            (gaussianInterpDeriv (E := EnergySpace N) t x)
          ∂(μ (Ω := Ω) (N := N) (β := β) (q := q) sk sim))
        = ∑ σ : Config N, (1 / 2 : ℝ) *
            ( (∫ x : DisorderSpace (N := N),
                  ((fderiv ℝ (fderiv ℝ (fun H' : EnergySpace N => free_energy_density (N := N) H'))
                        (H_t_disorder (N := N) (h := h) t x))
                      (∑ τ : Config N, sk_cov_kernel N β σ τ • std_basis N τ))
                    (std_basis N σ)
                  ∂(μ (Ω := Ω) (N := N) (β := β) (q := q) sk sim))
              - ∫ x : DisorderSpace (N := N),
                  ((fderiv ℝ (fderiv ℝ (fun H' : EnergySpace N => free_energy_density (N := N) H'))
                        (H_t_disorder (N := N) (h := h) t x))
                      (∑ τ : Config N,
                        simple_cov_kernel N β (fun r => q * r) σ τ • std_basis N τ))
                    (std_basis N σ)
                  ∂(μ (Ω := Ω) (N := N) (β := β) (q := q) sk sim) ) := by
    have hg := ProbabilityTheory.IsGaussian.integral_fderiv_gaussianInterp_apply_deriv_eq_sum
      (P := μ (Ω := Ω) (N := N) (β := β) (q := q) sk sim)
      (disorderPairLaw_mean0 (Ω := Ω) (N := N) (β := β) (q := q) sk sim)
      (EuclideanSpace.basisFun (Config N) ℝ)
      (fun σ => ∑ τ : Config N, sk_cov_kernel N β σ τ • std_basis N τ)
      (fun σ => ∑ τ : Config N, simple_cov_kernel N β (fun r => q * r) σ τ • std_basis N τ)
      (fun σ => by
        rw [← FiniteGibbs.std_basis_eq_basisFun (α := Config N) σ]
        exact covarianceOperator_disorderPairLaw_toLp_left (Ω := Ω) (β := β) (q := q)
          (sk := sk) (sim := sim) hindep σ)
      (fun σ => by
        rw [← FiniteGibbs.std_basis_eq_basisFun (α := Config N) σ]
        exact covarianceOperator_disorderPairLaw_toLp_right (Ω := Ω) (β := β) (q := q)
          (sk := sk) (sim := sim) hindep σ)
      (H_field (N := N) (h := h))
      (fun H' : EnergySpace N => free_energy_density (N := N) H')
      (FiniteGibbs.contDiff_two_free_energy_density (α := Config N) N)
      (FiniteGibbs.norm_fderiv_free_energy_density_growth_nonneg N)
      (FiniteGibbs.norm_fderiv_free_energy_density_growth (α := Config N) N)
      (FiniteGibbs.norm_fderiv_fderiv_free_energy_density_growth (α := Config N) N) ht
    have hbridge : ∀ σ : Config N, FiniteGibbs.std_basis (α := Config N) σ = std_basis N σ :=
      fun _ => rfl
    simpa only [← FiniteGibbs.std_basis_eq_basisFun, hbridge, H_t_disorder] using hg
  -- (2) Push the derivative value to the disorder law, then split the two blocks.
  rw [integral_derivative_value_eq_integral_disorderPairLaw (Ω := Ω) (β := β) (h := h) (q := q)
    (sk := sk) (sim := sim) t, hgen]
  have hsplit : ∀ (I J : Config N → ℝ),
      (∑ σ : Config N, (1 / 2 : ℝ) * (I σ - J σ))
        = (∑ σ : Config N, (1 / 2 : ℝ) * I σ) + ∑ σ : Config N, (-(1 / 2 : ℝ)) * J σ := by
    intro I J
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => by ring
  rw [hsplit,
    sum_integral_fderiv2_covariance_image_eq (Ω := Ω) (β := β) (h := h) (q := q) (sk := sk)
      (sim := sim) t (sk_cov_kernel N β) (sk_cov_kernel_comm (N := N) (β := β)) (1 / 2)
      (fun σ => integrable_half_kernel_hessian (Ω := Ω) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t (sk_cov_kernel N β) (1 / 2) σ),
    sum_integral_fderiv2_covariance_image_eq (Ω := Ω) (β := β) (h := h) (q := q) (sk := sk)
      (sim := sim) t (simple_cov_kernel N β (fun r => q * r))
      (simple_cov_kernel_comm (N := N) (β := β) (xi := fun r => q * r)) (-(1 / 2))
      (fun σ => integrable_half_kernel_hessian (Ω := Ω) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t (simple_cov_kernel N β (fun r => q * r)) (-(1 / 2)) σ),
    ← MeasureTheory.integral_add
      ((integrable_trace_kernel_hessian (Ω := Ω) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        t (sk_cov_kernel N β)).const_mul _)
      ((integrable_trace_kernel_hessian (Ω := Ω) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        t (simple_cov_kernel N β (fun r => q * r))).const_mul _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

end Disorder

end

end SpinGlass
