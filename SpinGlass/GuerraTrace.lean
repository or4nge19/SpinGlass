import SpinGlass.GuerraIBP
import SpinGlass.Defs
import SpinGlass.SKModel

/-!
## Guerra interpolation: from IBP to the trace/Hessian form

`SpinGlass/GuerraIBP.lean` rewrites the derivative value of the expected free energy density
into a Gaussian IBP expression involving derivatives of `gibbs_pmf` on the disorder space.

In this file we:
- expand the covariance-operator vectors into explicit kernel sums (SK vs simple),
- use the chain rule for the affine map `H_t_disorder` to convert derivatives on the disorder space
  into derivatives on `EnergySpace`,
- identify the resulting double sums with Talagrand’s trace/Hessian expression built from
  `hessian_free_energy`.
-/

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology
open scoped ENNReal NNReal

namespace SpinGlass

noncomputable section

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {N : ℕ} (β h q : ℝ)
variable (sk : SKDisorder (Ω := Ω) (N := N) β h) (sim : SimpleDisorder (Ω := Ω) (N := N) β q)

section

private abbrev μ : Measure (DisorderSpace (N := N)) :=
  disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)

/-! ### Chain rule for `x ↦ gibbs_pmf (H_t_disorder t x)` -/

private lemma fderiv_gibbs_pmf_disorder_eq
    (t : ℝ) (σ : Config N) (x : DisorderSpace (N := N)) :
    fderiv ℝ (fun x : DisorderSpace (N := N) =>
        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ) x
      =
      (fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H σ)
        (H_t_disorder (N := N) (h := h) t x)).comp (H_t_disorder_lin (N := N) t) := by
  classical
  have hH :
      HasFDerivAt (H_t_disorder (N := N) (h := h) t) (H_t_disorder_lin (N := N) t) x :=
    hasFDerivAt_H_t_disorder (N := N) (h := h) t x
  have hdiff :
      DifferentiableAt ℝ (fun H : EnergySpace N => gibbs_pmf N H σ)
        (H_t_disorder (N := N) (h := h) t x) :=
    SpinGlass.differentiableAt_gibbs_pmf (N := N) (H := H_t_disorder (N := N) (h := h) t x) σ
  have h1 :
      HasFDerivAt (fun H : EnergySpace N => gibbs_pmf N H σ)
        (fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H σ)
          (H_t_disorder (N := N) (h := h) t x))
        (H_t_disorder (N := N) (h := h) t x) :=
    hdiff.hasFDerivAt
  have hcomp :
      HasFDerivAt (fun x : DisorderSpace (N := N) =>
          gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ)
        ((fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H σ)
            (H_t_disorder (N := N) (h := h) t x)).comp (H_t_disorder_lin (N := N) t)) x := by
    simpa [Function.comp] using h1.comp x hH
  simpa using hcomp.fderiv

private lemma H_t_disorder_lin_std_basis_left (t : ℝ) (σ : Config N) :
    H_t_disorder_lin (N := N) t (std_basis_left (N := N) σ) = (Real.sqrt t) • (std_basis N σ) := by
  classical
  -- `fstL (toLp (basis,0)) = basis`, `sndL (...) = 0`
  simp [H_t_disorder_lin, std_basis_left, std_basis_right, add_comm, add_left_comm, add_assoc]

private lemma H_t_disorder_lin_std_basis_right (t : ℝ) (σ : Config N) :
    H_t_disorder_lin (N := N) t (std_basis_right (N := N) σ) =
      (Real.sqrt (1 - t)) • (std_basis N σ) := by
  classical
  simp [H_t_disorder_lin, std_basis_left, std_basis_right, add_comm, add_left_comm, add_assoc]

/-! ### Relating `fderiv gibbs_pmf` on basis directions to `hessian_free_energy` -/

private lemma fderiv_gibbs_pmf_apply_std_basis
    (H : EnergySpace N) (σ τ : Config N) :
    fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H σ) H (std_basis N τ)
      =
      (gibbs_pmf N H σ) * ((gibbs_pmf N H τ) - (if σ = τ then 1 else 0)) := by
  simpa [Z, gibbs_pmf, std_basis, FiniteGibbs.Z, FiniteGibbs.gibbs_pmf, FiniteGibbs.std_basis, eq_comm] using
    (FiniteGibbs.fderiv_gibbs_pmf_apply_std_basis (α := Config N) (H := H) (σ := σ) (τ := τ))

private lemma hessian_free_energy_std_basis_eq_neg_fderiv_gibbs_pmf
    (H : EnergySpace N) (σ τ : Config N) :
    hessian_free_energy N H (std_basis N σ) (std_basis N τ)
      =
      - (1 / (N : ℝ)) *
        fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H σ) H (std_basis N τ) := by
  classical
  by_cases hστ : σ = τ
  · subst hστ
    -- rewrite the `fderiv` term *before* unfolding `std_basis`
    have hf :
        fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H σ) H (std_basis N σ)
          =
          (gibbs_pmf N H σ) * ((gibbs_pmf N H σ) - (if σ = σ then 1 else 0)) :=
      fderiv_gibbs_pmf_apply_std_basis (N := N) (H := H) (σ := σ) (τ := σ)
    rw [hf]
    simp [hessian_free_energy, std_basis]
    ring
  · -- off-diagonal: the covariance is `-(gσ*gτ)`
    -- rewrite the `fderiv` term *before* unfolding `std_basis`
    have hf :
        fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H σ) H (std_basis N τ)
          =
          (gibbs_pmf N H σ) * ((gibbs_pmf N H τ) - (if σ = τ then 1 else 0)) :=
      fderiv_gibbs_pmf_apply_std_basis (N := N) (H := H) (σ := σ) (τ := τ)
    rw [hf]
    simp [hessian_free_energy, std_basis, hστ]

/-!
### Bookkeeping lemmas for the trace/Hessian step

These isolate the last-mile steps after `derivative_value_guerraPhi_eq_ibp`:

- swapping finite sums with integrals (requires integrability),
- rewriting the `-(1/N)·fderiv` entries as `hessian_free_energy` entries.
-/

private lemma neg_one_div_N_mul_fderiv_eq_hessian
    (H : EnergySpace N) (σ τ : Config N) :
    (-(1 / (N : ℝ))) *
        fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H σ) H (std_basis N τ)
      =
      hessian_free_energy N H (std_basis N σ) (std_basis N τ) := by
  simpa [mul_assoc] using
    (hessian_free_energy_std_basis_eq_neg_fderiv_gibbs_pmf (N := N) (H := H) (σ := σ) (τ := τ)).symm

private lemma sum_integral_eq_integral_sum
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Config N → α → ℝ)
    (hf : ∀ i : Config N, Integrable (f i) μ) :
    (∑ i : Config N, ∫ a, f i a ∂μ) = ∫ a, (∑ i : Config N, f i a) ∂μ := by
  classical
  -- `integral_finset_sum` is the Mathlib lemma; we use it with `Finset.univ`.
  simpa using
    (MeasureTheory.integral_finset_sum (μ := μ) (s := (Finset.univ : Finset (Config N)))
      (f := fun i : Config N => fun a : α => f i a)
      (by
        intro i hi
        simpa using hf i)).symm

private lemma sk_cov_kernel_symm (σ τ : Config N) :
    sk_cov_kernel N β σ τ = sk_cov_kernel N β τ σ := by
  simpa using sk_cov_kernel_comm (N := N) (β := β) σ τ

private lemma simple_cov_kernel_symm (xi : ℝ → ℝ) (σ τ : Config N) :
    simple_cov_kernel N β xi σ τ = simple_cov_kernel N β xi τ σ := by
  simpa using simple_cov_kernel_comm (N := N) (β := β) (xi := xi) σ τ

private lemma hessian_free_energy_std_basis_eq
    (H : EnergySpace N) (σ τ : Config N) :
    hessian_free_energy N H (std_basis N σ) (std_basis N τ)
      =
      (1 / (N : ℝ)) *
        (gibbs_pmf N H σ * (if σ = τ then 1 else 0) - gibbs_pmf N H σ * gibbs_pmf N H τ) := by
  simpa [hessian_free_energy, Z, gibbs_pmf, std_basis, FiniteGibbs.hessian_free_energy, FiniteGibbs.Z,
    FiniteGibbs.gibbs_pmf, FiniteGibbs.std_basis, eq_comm] using
    (FiniteGibbs.hessian_free_energy_std_basis_eq (α := Config N) (n := N) (H := H) (σ := σ) (τ := τ))

private lemma measurable_gibbs_pmf_disorder (t : ℝ) (σ : Config N) :
    Measurable (fun x : DisorderSpace (N := N) =>
      gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ) := by
  simpa using (contDiff_gibbs_pmf_disorder (N := N) (h := h) (t := t) σ).continuous.measurable


private lemma aestronglyMeasurable_hessian_std_basis_disorder (t : ℝ) (σ τ : Config N) :
    AEStronglyMeasurable (fun x : DisorderSpace (N := N) =>
      hessian_free_energy N (H_t_disorder (N := N) (h := h) t x) (std_basis N σ) (std_basis N τ))
      (μ (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim) := by
  classical
  have hσ := measurable_gibbs_pmf_disorder (N := N) (h := h) (t := t) σ
  have hτ := measurable_gibbs_pmf_disorder (N := N) (h := h) (t := t) τ
  have hδ : Measurable (fun _x : DisorderSpace (N := N) => (if σ = τ then (1 : ℝ) else 0)) :=
    measurable_const
  have hmeas :
      Measurable (fun x : DisorderSpace (N := N) =>
        hessian_free_energy N (H_t_disorder (N := N) (h := h) t x) (std_basis N σ) (std_basis N τ)) := by
    -- rewrite via the explicit basis formula
    simpa [hessian_free_energy_std_basis_eq (N := N) (σ := σ) (τ := τ),
      sub_eq_add_neg, mul_add, mul_assoc, mul_left_comm, mul_comm] using
      (measurable_const.mul ((hσ.mul hδ).sub (hσ.mul hτ)))
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
  -- finish via the explicit formula
  simpa [hessian_free_energy_std_basis_eq (N := N) (H := H), gσ, gτ, abs_mul, mul_assoc, mul_comm, mul_left_comm]
    using (mul_le_mul_of_nonneg_left hins (abs_nonneg (1 / (N : ℝ))))

private lemma integrable_kernel_mul_hessian
    (t : ℝ) (K : Config N → Config N → ℝ) (σ τ : Config N) :
    Integrable (fun x : DisorderSpace (N := N) =>
        (K σ τ) *
          hessian_free_energy N (H_t_disorder (N := N) (h := h) t x) (std_basis N σ) (std_basis N τ))
      (μ (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim) := by
  classical
  let μ0 := μ (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim
  haveI : IsFiniteMeasure μ0 := by infer_instance
  refine Integrable.of_bound (μ := μ0)
    ((aestronglyMeasurable_hessian_std_basis_disorder (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) (t := t) σ τ).const_mul (K σ τ))
    (|(K σ τ)| * (|(1 / (N : ℝ))| * 2)) ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  have hhess :=
    abs_hessian_std_basis_le (N := N) (H := H_t_disorder (N := N) (h := h) t x) (σ := σ) (τ := τ)
  -- multiply the bound by `|K σ τ|` and rewrite `‖·‖ = |·|` in `ℝ`
  have : |(K σ τ) *
        hessian_free_energy N (H_t_disorder (N := N) (h := h) t x) (std_basis N σ) (std_basis N τ)|
      ≤ |K σ τ| * (|1 / (N : ℝ)| * 2) := by
    simpa [abs_mul, mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_left hhess (abs_nonneg (K σ τ)))
  simpa [Real.norm_eq_abs] using this

/-!
### Bookkeeping lemmas: linearity + cancellation of the √t factors
-/

private lemma clm_apply_finset_sum {ι : Type*} (s : Finset ι)
    (L : DisorderSpace (N := N) →L[ℝ] ℝ) (v : ι → DisorderSpace (N := N)) :
    L (Finset.sum s v) = Finset.sum s (fun i => L (v i)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha hs
    simp [ha, hs, map_add]

private lemma hessian_free_energy_std_basis_symm (H : EnergySpace N) (σ τ : Config N) :
    hessian_free_energy N H (std_basis N σ) (std_basis N τ)
      =
      hessian_free_energy N H (std_basis N τ) (std_basis N σ) := by
  classical
  by_cases hστ : σ = τ
  · subst hστ; simp
  ·
    -- both sides reduce to the same explicit formula (the diagonal term vanishes)
    simp [hessian_free_energy_std_basis_eq (N := N) (H := H), hστ, eq_comm, mul_comm]

private lemma left_pointwise_trace
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V)
    (t : ℝ) (hsqt : Real.sqrt t ≠ 0) (x : DisorderSpace (N := N)) (τ : Config N) :
    (-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt t)) *
        (fderiv ℝ (fun x : DisorderSpace (N := N) =>
              gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
            (ProbabilityTheory.covarianceOperator
              (μ (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim)
              (std_basis_left (N := N) τ))
      =
      (1 / 2 : ℝ) *
        (∑ σ : Config N,
          sk_cov_kernel N β τ σ *
            hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
              (std_basis N τ) (std_basis N σ)) := by
  classical
  -- Expand the covariance operator on the `std_basis_left` vector.
  have hcov :
      ProbabilityTheory.covarianceOperator
          (μ (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim)
          (std_basis_left (N := N) τ)
        =
        ∑ σ : Config N, (sk_cov_kernel N β τ σ) • std_basis_left (N := N) σ := by
    simpa [μ] using
      (covarianceOperator_disorderPairLaw_std_basis_left_eq_sum_sk
        (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) (hindep := hindep) τ)
  -- Abbreviate the Fréchet derivative on the disorder space.
  let L :
      DisorderSpace (N := N) →L[ℝ] ℝ :=
    fderiv ℝ (fun x : DisorderSpace (N := N) =>
        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x
  have hL_sum :
      L (∑ σ : Config N, (sk_cov_kernel N β τ σ) • std_basis_left (N := N) σ)
        =
        ∑ σ : Config N, L ((sk_cov_kernel N β τ σ) • std_basis_left (N := N) σ) := by
    simp [L]
  have hL_basis (σ : Config N) :
      L (std_basis_left (N := N) σ)
        =
        (Real.sqrt t) *
          fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H τ)
            (H_t_disorder (N := N) (h := h) t x) (std_basis N σ) := by
    -- Chain rule: `fderiv` on disorder equals energy-`fderiv` composed with `H_t_disorder_lin`.
    have hchain :=
      fderiv_gibbs_pmf_disorder_eq (N := N) (h := h) (t := t) (σ := τ) (x := x)
    -- evaluate both sides at `std_basis_left σ`
    have :=
      congrArg (fun M =>
        M (std_basis_left (N := N) σ)) hchain
    -- simplify the composition and apply the basis evaluation lemma
    simpa [L, ContinuousLinearMap.comp_apply, H_t_disorder_lin_std_basis_left (N := N) (t := t),
      smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using this
  -- Start from the statement, rewrite `covarianceOperator`, and expand `L` over the finite sum.
  rw [hcov]
  -- turn the application to the covariance sum into a sum of applications
  have happly :
      (fderiv ℝ (fun x : DisorderSpace (N := N) =>
            gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
          (∑ σ : Config N, (sk_cov_kernel N β τ σ) • std_basis_left (N := N) σ)
        =
        ∑ σ : Config N,
          (sk_cov_kernel N β τ σ) *
            ((Real.sqrt t) *
              fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H τ)
                (H_t_disorder (N := N) (h := h) t x) (std_basis N σ)) := by
    -- replace the `fderiv` by `L`
    simp [L, hL_sum, hL_basis, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
  -- Use the explicit expression for the application.
  -- Now cancel the `√t` factor and convert `-(1/N) * fderiv` into the Hessian entry.
  rw [happly]
  -- The key scalar identity is `(1 / (2 * √t)) * √t = 1/2`.
  have hsqt' : (2 * Real.sqrt t) ≠ 0 := mul_ne_zero (by norm_num) hsqt
  have hcancel : (1 / (2 * Real.sqrt t) : ℝ) * Real.sqrt t = (1 / 2 : ℝ) := by
    field_simp [hsqt, hsqt']
  -- Rewrite both sides as sums, then prove termwise equality.
  -- (All sums are over `Finset.univ` since `Config N` is finite.)
  -- LHS: distribute the scalar across the sum.
  have hL :
      (-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt t)) *
          (∑ σ : Config N,
              sk_cov_kernel N β τ σ *
                (Real.sqrt t *
                  fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H τ)
                    (H_t_disorder (N := N) (h := h) t x) (std_basis N σ)))
        =
        ∑ σ : Config N,
          (-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt t)) *
            (sk_cov_kernel N β τ σ *
              (Real.sqrt t *
                fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H τ)
                  (H_t_disorder (N := N) (h := h) t x) (std_basis N σ))) := by
    -- turn `a*b*sum` into `(a*b) * sum` then apply `Finset.mul_sum`
    simp [mul_assoc, Finset.mul_sum, mul_left_comm, mul_comm]
  -- RHS: distribute `(1/2)` across the sum.
  have hR :
      (1 / 2 : ℝ) *
          (∑ σ : Config N,
              sk_cov_kernel N β τ σ *
                hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
                  (std_basis N τ) (std_basis N σ))
        =
        ∑ σ : Config N,
          (1 / 2 : ℝ) *
            (sk_cov_kernel N β τ σ *
              hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
                (std_basis N τ) (std_basis N σ)) := by
    simp [mul_assoc, Finset.mul_sum, mul_left_comm, mul_comm]
  -- Apply these rewrites and prove termwise equality.
  -- (We rewrite the goal rather than `rw` to keep the expression stable.)
  -- `rw` in both directions:
  rw [hL, hR]
  refine Finset.sum_congr rfl (fun σ _hσ => ?_)
  -- One σ-summand: cancel `√t`, then convert `-(1/N) * fderiv` into the Hessian entry.
  have hconv :
      (-(1 / (N : ℝ))) *
          fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H τ)
            (H_t_disorder (N := N) (h := h) t x) (std_basis N σ)
        =
        hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
          (std_basis N τ) (std_basis N σ) :=
    neg_one_div_N_mul_fderiv_eq_hessian (N := N)
      (H := H_t_disorder (N := N) (h := h) t x) (σ := τ) (τ := σ)
  -- finish by scalar rearrangement
  calc
    (-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt t)) *
        (sk_cov_kernel N β τ σ *
          (Real.sqrt t *
            fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H τ)
              (H_t_disorder (N := N) (h := h) t x) (std_basis N σ)))
        =
        (1 / 2 : ℝ) *
          (sk_cov_kernel N β τ σ *
            ((-(1 / (N : ℝ))) *
              fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H τ)
                (H_t_disorder (N := N) (h := h) t x) (std_basis N σ))) := by
      -- cancel `√t` using `hcancel` and reorder scalars
      -- (pure commutative algebra, no measure-theory content)
      calc
        (-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt t)) *
            (sk_cov_kernel N β τ σ *
              (Real.sqrt t *
                fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H τ)
                  (H_t_disorder (N := N) (h := h) t x) (std_basis N σ)))
            =
            (-(1 / (N : ℝ))) * ((1 / (2 * Real.sqrt t) : ℝ) * Real.sqrt t) *
              (sk_cov_kernel N β τ σ *
                fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H τ)
                  (H_t_disorder (N := N) (h := h) t x) (std_basis N σ)) := by
          simp [mul_assoc, mul_left_comm, mul_comm]
        _ =
            (-(1 / (N : ℝ))) * (1 / 2 : ℝ) *
              (sk_cov_kernel N β τ σ *
                fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H τ)
                  (H_t_disorder (N := N) (h := h) t x) (std_basis N σ)) := by
          -- multiply the scalar identity `hcancel` by the remaining factors
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            congrArg (fun c =>
                (-(1 / (N : ℝ))) * c *
                  (sk_cov_kernel N β τ σ *
                    fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H τ)
                      (H_t_disorder (N := N) (h := h) t x) (std_basis N σ))) hcancel
        _ =
            (1 / 2 : ℝ) *
              (sk_cov_kernel N β τ σ *
                ((-(1 / (N : ℝ))) *
                  fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H τ)
                    (H_t_disorder (N := N) (h := h) t x) (std_basis N σ))) := by
          simp [mul_assoc, mul_left_comm]
    _ = (1 / 2 : ℝ) *
          (sk_cov_kernel N β τ σ *
            hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
              (std_basis N τ) (std_basis N σ)) := by
      -- apply `hconv` and multiply by the scalar prefactors
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        congrArg (fun y =>
            (1 / 2 : ℝ) * (sk_cov_kernel N β τ σ * y)) hconv

private lemma right_pointwise_trace
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V)
    (t : ℝ) (hsqt1 : Real.sqrt (1 - t) ≠ 0) (x : DisorderSpace (N := N)) (τ : Config N) :
    (-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt (1 - t))) *
        (fderiv ℝ (fun x : DisorderSpace (N := N) =>
              gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
            (ProbabilityTheory.covarianceOperator
              (μ (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim)
              (std_basis_right (N := N) τ))
      =
      (1 / 2 : ℝ) *
        (∑ σ : Config N,
          simple_cov_kernel N β (fun r => q * r) τ σ *
            hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
              (std_basis N τ) (std_basis N σ)) := by
  classical
  -- Expand the covariance operator on the `std_basis_right` vector.
  have hcov :
      ProbabilityTheory.covarianceOperator
          (μ (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim)
          (std_basis_right (N := N) τ)
        =
        ∑ σ : Config N,
          (simple_cov_kernel N β (fun r => q * r) τ σ) • std_basis_right (N := N) σ := by
    simpa [μ] using
      (covarianceOperator_disorderPairLaw_std_basis_right_eq_sum_simple
        (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) (hindep := hindep) τ)
  -- Abbreviate the Fréchet derivative on the disorder space.
  let L :
      DisorderSpace (N := N) →L[ℝ] ℝ :=
    fderiv ℝ (fun x : DisorderSpace (N := N) =>
        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x
  have hL_sum :
      L (∑ σ : Config N, (simple_cov_kernel N β (fun r => q * r) τ σ) • std_basis_right (N := N) σ)
        =
        ∑ σ : Config N,
          L ((simple_cov_kernel N β (fun r => q * r) τ σ) • std_basis_right (N := N) σ) := by
    simpa [L] using
      (clm_apply_finset_sum (N := N) (s := (Finset.univ : Finset (Config N)))
        (L := L)
        (v := fun σ : Config N =>
          (simple_cov_kernel N β (fun r => q * r) τ σ) • std_basis_right (N := N) σ))
  have hL_basis (σ : Config N) :
      L (std_basis_right (N := N) σ)
        =
        (Real.sqrt (1 - t)) *
          fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H τ)
            (H_t_disorder (N := N) (h := h) t x) (std_basis N σ) := by
    have hchain :=
      fderiv_gibbs_pmf_disorder_eq (N := N) (h := h) (t := t) (σ := τ) (x := x)
    have :=
      congrArg (fun M =>
        M (std_basis_right (N := N) σ)) hchain
    simpa [L, ContinuousLinearMap.comp_apply, H_t_disorder_lin_std_basis_right (N := N) (t := t),
      smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using this
  -- Start from the statement, rewrite `covarianceOperator`, and expand `L` over the finite sum.
  rw [hcov]
  have happly :
      (fderiv ℝ (fun x : DisorderSpace (N := N) =>
            gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
          (∑ σ : Config N,
            (simple_cov_kernel N β (fun r => q * r) τ σ) • std_basis_right (N := N) σ)
        =
        ∑ σ : Config N,
          (simple_cov_kernel N β (fun r => q * r) τ σ) *
            ((Real.sqrt (1 - t)) *
              fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H τ)
                (H_t_disorder (N := N) (h := h) t x) (std_basis N σ)) := by
    simp [L, hL_sum, hL_basis, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
  -- Rewrite using `happly`.
  rw [happly]
  -- Scalar identity: `(1 / (2 * √(1-t))) * √(1-t) = 1/2`.
  have hsqt1' : (2 * Real.sqrt (1 - t)) ≠ 0 := mul_ne_zero (by norm_num) hsqt1
  have hcancel : (1 / (2 * Real.sqrt (1 - t)) : ℝ) * Real.sqrt (1 - t) = (1 / 2 : ℝ) := by
    field_simp [hsqt1, hsqt1']
  -- Rewrite both sides as sums and prove termwise equality.
  have hL' :
      (-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt (1 - t))) *
          (∑ σ : Config N,
              simple_cov_kernel N β (fun r => q * r) τ σ *
                (Real.sqrt (1 - t) *
                  fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H τ)
                    (H_t_disorder (N := N) (h := h) t x) (std_basis N σ)))
        =
        ∑ σ : Config N,
          (-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt (1 - t))) *
            (simple_cov_kernel N β (fun r => q * r) τ σ *
              (Real.sqrt (1 - t) *
                fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H τ)
                  (H_t_disorder (N := N) (h := h) t x) (std_basis N σ))) := by
    simp [mul_assoc, Finset.mul_sum, mul_left_comm, mul_comm]
  have hR' :
      (1 / 2 : ℝ) *
          (∑ σ : Config N,
              simple_cov_kernel N β (fun r => q * r) τ σ *
                hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
                  (std_basis N τ) (std_basis N σ))
        =
        ∑ σ : Config N,
          (1 / 2 : ℝ) *
            (simple_cov_kernel N β (fun r => q * r) τ σ *
              hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
                (std_basis N τ) (std_basis N σ)) := by
    simp [Finset.mul_sum]
  rw [hL', hR']
  refine Finset.sum_congr rfl (fun σ _hσ => ?_)
  have hconv :
      (-(1 / (N : ℝ))) *
          fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H τ)
            (H_t_disorder (N := N) (h := h) t x) (std_basis N σ)
        =
        hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
          (std_basis N τ) (std_basis N σ) :=
    neg_one_div_N_mul_fderiv_eq_hessian (N := N)
      (H := H_t_disorder (N := N) (h := h) t x) (σ := τ) (τ := σ)
  calc
    (-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt (1 - t))) *
        (simple_cov_kernel N β (fun r => q * r) τ σ *
          (Real.sqrt (1 - t) *
            fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H τ)
              (H_t_disorder (N := N) (h := h) t x) (std_basis N σ)))
        =
        (1 / 2 : ℝ) *
          (simple_cov_kernel N β (fun r => q * r) τ σ *
            ((-(1 / (N : ℝ))) *
              fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H τ)
                (H_t_disorder (N := N) (h := h) t x) (std_basis N σ))) := by
      calc
        (-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt (1 - t))) *
            (simple_cov_kernel N β (fun r => q * r) τ σ *
              (Real.sqrt (1 - t) *
                fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H τ)
                  (H_t_disorder (N := N) (h := h) t x) (std_basis N σ)))
            =
            (-(1 / (N : ℝ))) * ((1 / (2 * Real.sqrt (1 - t)) : ℝ) * Real.sqrt (1 - t)) *
              (simple_cov_kernel N β (fun r => q * r) τ σ *
                fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H τ)
                  (H_t_disorder (N := N) (h := h) t x) (std_basis N σ)) := by
          simp [mul_assoc, mul_left_comm, mul_comm]
        _ =
            (-(1 / (N : ℝ))) * (1 / 2 : ℝ) *
              (simple_cov_kernel N β (fun r => q * r) τ σ *
                fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H τ)
                  (H_t_disorder (N := N) (h := h) t x) (std_basis N σ)) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            congrArg (fun c =>
                (-(1 / (N : ℝ))) * c *
                  (simple_cov_kernel N β (fun r => q * r) τ σ *
                    fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H τ)
                      (H_t_disorder (N := N) (h := h) t x) (std_basis N σ))) hcancel
        _ =
            (1 / 2 : ℝ) *
              (simple_cov_kernel N β (fun r => q * r) τ σ *
                ((-(1 / (N : ℝ))) *
                  fderiv ℝ (fun H : EnergySpace N => gibbs_pmf N H τ)
                    (H_t_disorder (N := N) (h := h) t x) (std_basis N σ))) := by
          simp [mul_assoc, mul_left_comm, mul_comm]
    _ = (1 / 2 : ℝ) *
          (simple_cov_kernel N β (fun r => q * r) τ σ *
            hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
              (std_basis N τ) (std_basis N σ)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        congrArg (fun y =>
            (1 / 2 : ℝ) * (simple_cov_kernel N β (fun r => q * r) τ σ * y)) hconv

/-!
### Main trace/Hessian form of the Guerra derivative (disorder-law version)
-/

theorem derivative_value_guerraPhi_eq_trace_integral
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ ω,
        (fderiv ℝ (fun H' : EnergySpace N => free_energy_density (N := N) H')
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω))
          (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
        ∂ℙ)
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
        ∂(μ (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim) := by
  classical
  -- Use a short name for the disorder law.
  let μ0 : Measure (DisorderSpace (N := N)) :=
    μ (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim
  have ht0 : 0 < t := ht.1
  have ht1 : 0 < 1 - t := by linarith [ht.2]
  have hsqt : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht0)
  have hsqt1 : Real.sqrt (1 - t) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht1)

  -- The kernel-trace integrands appearing on the RHS.
  let SK (x : DisorderSpace (N := N)) : ℝ :=
    ∑ σ : Config N, ∑ τ : Config N,
      sk_cov_kernel N β σ τ *
        hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
          (std_basis N σ) (std_basis N τ)
  let SIM (x : DisorderSpace (N := N)) : ℝ :=
    ∑ σ : Config N, ∑ τ : Config N,
      simple_cov_kernel N β (fun r => q * r) σ τ *
        hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
          (std_basis N σ) (std_basis N τ)

  -- `SK` and `SIM` are integrable: finite sums of integrable kernel × Hessian terms.
  have hintSK : Integrable SK μ0 := by
    classical
    -- outer sum over `σ`
    refine MeasureTheory.integrable_finset_sum (μ := μ0)
      (s := (Finset.univ : Finset (Config N)))
      (f := fun σ : Config N => fun x : DisorderSpace (N := N) =>
        ∑ τ : Config N,
          sk_cov_kernel N β σ τ *
            hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
              (std_basis N σ) (std_basis N τ)) ?_
    intro σ _hσ
    -- inner sum over `τ`
    refine MeasureTheory.integrable_finset_sum (μ := μ0)
      (s := (Finset.univ : Finset (Config N)))
      (f := fun τ : Config N => fun x : DisorderSpace (N := N) =>
        sk_cov_kernel N β σ τ *
          hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
            (std_basis N σ) (std_basis N τ)) ?_
    intro τ _hτ
    -- integrability of a single (σ,τ)-summand
    simpa [μ0] using
      (integrable_kernel_mul_hessian (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk)
        (sim := sim) (t := t) (K := fun σ τ => sk_cov_kernel N β σ τ) (σ := σ) (τ := τ))
  have hintSIM : Integrable SIM μ0 := by
    classical
    refine MeasureTheory.integrable_finset_sum (μ := μ0)
      (s := (Finset.univ : Finset (Config N)))
      (f := fun σ : Config N => fun x : DisorderSpace (N := N) =>
        ∑ τ : Config N,
          simple_cov_kernel N β (fun r => q * r) σ τ *
            hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
              (std_basis N σ) (std_basis N τ)) ?_
    intro σ _hσ
    refine MeasureTheory.integrable_finset_sum (μ := μ0)
      (s := (Finset.univ : Finset (Config N)))
      (f := fun τ : Config N => fun x : DisorderSpace (N := N) =>
        simple_cov_kernel N β (fun r => q * r) σ τ *
          hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
            (std_basis N σ) (std_basis N τ)) ?_
    intro τ _hτ
    simpa [μ0] using
      (integrable_kernel_mul_hessian (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk)
        (sim := sim) (t := t) (K := fun σ τ => simple_cov_kernel N β (fun r => q * r) σ τ)
        (σ := σ) (τ := τ))

  have hintSK' : Integrable (fun x => (1 / 2 : ℝ) * SK x) μ0 :=
    hintSK.const_mul (1 / 2 : ℝ)
  have hintSIM' : Integrable (fun x => (1 / 2 : ℝ) * SIM x) μ0 :=
    hintSIM.const_mul (1 / 2 : ℝ)

  -- Start from the clean “after IBP, before trace/Hessian” identity.
  have hIBP :=
    derivative_value_guerraPhi_eq_ibp (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) hindep t
  rw [hIBP]
  -- Unfold the disorder law abbreviation on the RHS (and nothing else).
  simp only [μ]

  -- SK part: rewrite into the trace form inside the disorder integral.
  have hSKInt :
      (-(1 / (N : ℝ))) *
          ((1 / (2 * Real.sqrt t)) *
            ∑ τ : Config N,
              ∫ x : DisorderSpace (N := N),
                  (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                    (ProbabilityTheory.covarianceOperator μ0 (std_basis_left (N := N) τ))
                ∂μ0)
        =
        ∫ x : DisorderSpace (N := N), (1 / 2 : ℝ) * SK x ∂μ0 := by
    classical
    -- combine scalar factors, then distribute across the finite sum
    have h0 :
        (-(1 / (N : ℝ))) *
            ((1 / (2 * Real.sqrt t)) *
              ∑ τ : Config N,
                ∫ x : DisorderSpace (N := N),
                    (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                          gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                      (ProbabilityTheory.covarianceOperator μ0 (std_basis_left (N := N) τ))
                  ∂μ0)
          =
          ((-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt t))) *
            ∑ τ : Config N,
              ∫ x : DisorderSpace (N := N),
                  (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                    (ProbabilityTheory.covarianceOperator μ0 (std_basis_left (N := N) τ))
                ∂μ0 := by
      simp [mul_assoc]
    rw [h0]
    -- distribute the scalar across the finite τ-sum (without rewriting the scalar itself)
    have hsum :
        ((-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt t))) *
            (∑ τ : Config N,
              ∫ x : DisorderSpace (N := N),
                  (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                    (ProbabilityTheory.covarianceOperator μ0 (std_basis_left (N := N) τ))
                ∂μ0)
          =
          ∑ τ : Config N,
            ((-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt t))) *
              ∫ x : DisorderSpace (N := N),
                  (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                    (ProbabilityTheory.covarianceOperator μ0 (std_basis_left (N := N) τ))
                ∂μ0 := by
      simpa using
        (Finset.mul_sum (s := (Finset.univ : Finset (Config N)))
          (a := ((-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt t))))
          (f := fun τ : Config N =>
            ∫ x : DisorderSpace (N := N),
                (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                      gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                  (ProbabilityTheory.covarianceOperator μ0 (std_basis_left (N := N) τ))
              ∂μ0))
    rw [hsum]
    -- rewrite each scalar-multiplied integral as an integral of the scalar-multiplied integrand
    have h1 :
        (∑ τ : Config N,
            ((-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt t))) *
              ∫ x : DisorderSpace (N := N),
                  (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                    (ProbabilityTheory.covarianceOperator μ0 (std_basis_left (N := N) τ))
                ∂μ0)
          =
          ∑ τ : Config N,
            ∫ x : DisorderSpace (N := N),
                ((-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt t))) *
                  (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                    (ProbabilityTheory.covarianceOperator μ0 (std_basis_left (N := N) τ))
              ∂μ0 := by
      refine Finset.sum_congr rfl (fun τ _hτ => ?_)
      simpa [mul_assoc] using
        (MeasureTheory.integral_const_mul
          ((-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt t))) (fun x : DisorderSpace (N := N) =>
            (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                  gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
              (ProbabilityTheory.covarianceOperator μ0 (std_basis_left (N := N) τ)))).symm
    rw [h1]
    -- pointwise rewrite via the trace lemma (avoid fragile `simp_rw` matching)
    have hτ (τ : Config N) :
        (∫ x : DisorderSpace (N := N),
            ((-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt t))) *
              (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                    gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                (ProbabilityTheory.covarianceOperator μ0 (std_basis_left (N := N) τ))
          ∂μ0)
          =
          ∫ x : DisorderSpace (N := N),
            (1 / 2 : ℝ) *
              (∑ σ : Config N,
                sk_cov_kernel N β τ σ *
                  hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
                    (std_basis N τ) (std_basis N σ))
          ∂μ0 := by
      refine MeasureTheory.integral_congr_ae ?_
      refine Filter.Eventually.of_forall (fun x => ?_)
      simpa [μ0] using
        (left_pointwise_trace (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          (hindep := hindep) (t := t) (hsqt := hsqt) (x := x) (τ := τ))
    -- rewrite the finite τ-sum using `hτ`
    have hrewrite :
        (∑ τ : Config N,
            ∫ x : DisorderSpace (N := N),
                ((-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt t))) *
                  (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                    (ProbabilityTheory.covarianceOperator μ0 (std_basis_left (N := N) τ))
              ∂μ0)
          =
          ∑ τ : Config N,
            ∫ x : DisorderSpace (N := N),
                (1 / 2 : ℝ) *
                  (∑ σ : Config N,
                    sk_cov_kernel N β τ σ *
                      hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
                        (std_basis N τ) (std_basis N σ))
              ∂μ0 := by
      refine Finset.sum_congr rfl (fun τ _hτ => hτ τ)
    rw [hrewrite]
    -- swap the outer finite sum and the integral
    have hIntτ :
        ∀ τ : Config N,
          Integrable (fun x : DisorderSpace (N := N) =>
            (1 / 2 : ℝ) *
              (∑ σ : Config N,
                sk_cov_kernel N β τ σ *
                  hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
                    (std_basis N τ) (std_basis N σ))) μ0 := by
      intro τ
      -- integrable finite sum over `σ`
      have hσ :
          Integrable (fun x : DisorderSpace (N := N) =>
            ∑ σ : Config N,
              sk_cov_kernel N β τ σ *
                hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
                  (std_basis N τ) (std_basis N σ)) μ0 := by
        refine MeasureTheory.integrable_finset_sum (μ := μ0)
          (s := (Finset.univ : Finset (Config N)))
          (f := fun σ : Config N => fun x : DisorderSpace (N := N) =>
            sk_cov_kernel N β τ σ *
              hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
                (std_basis N τ) (std_basis N σ)) ?_
        intro σ _hσ
        simpa [μ0] using
          (integrable_kernel_mul_hessian (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk)
            (sim := sim) (t := t) (K := fun σ τ => sk_cov_kernel N β σ τ) (σ := τ) (τ := σ))
      simpa [mul_assoc] using hσ.const_mul (1 / 2 : ℝ)
    -- apply the swap lemma, then simplify the inner sum into `SK`
    have hswap :=
      sum_integral_eq_integral_sum (N := N) (f := fun τ : Config N => fun x : DisorderSpace (N := N) =>
        (1 / 2 : ℝ) *
          (∑ σ : Config N,
            sk_cov_kernel N β τ σ *
              hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
                (std_basis N τ) (std_basis N σ)))
        (μ := μ0) hIntτ
    -- rewrite the RHS integrand as `(1/2) * SK x`
    refine hswap.trans ?_
    refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    -- commute the σ/τ-sums, then use symmetry to match the `SK` definition
    simp [SK, Finset.sum_comm, Finset.mul_sum, sk_cov_kernel_symm (N := N) (β := β),
      hessian_free_energy_std_basis_symm (N := N), mul_assoc, mul_left_comm, mul_comm]

  -- SIM part: analogous rewrite into the trace form.
  have hSIMInt :
      (-(1 / (N : ℝ))) *
          ((1 / (2 * Real.sqrt (1 - t))) *
            ∑ τ : Config N,
              ∫ x : DisorderSpace (N := N),
                  (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                    (ProbabilityTheory.covarianceOperator μ0 (std_basis_right (N := N) τ))
                ∂μ0)
        =
        ∫ x : DisorderSpace (N := N), (1 / 2 : ℝ) * SIM x ∂μ0 := by
    classical
    have h0 :
        (-(1 / (N : ℝ))) *
            ((1 / (2 * Real.sqrt (1 - t))) *
              ∑ τ : Config N,
                ∫ x : DisorderSpace (N := N),
                    (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                          gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                      (ProbabilityTheory.covarianceOperator μ0 (std_basis_right (N := N) τ))
                  ∂μ0)
          =
          ((-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt (1 - t)))) *
            ∑ τ : Config N,
              ∫ x : DisorderSpace (N := N),
                  (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                    (ProbabilityTheory.covarianceOperator μ0 (std_basis_right (N := N) τ))
                ∂μ0 := by
      simp [mul_assoc]
    rw [h0]
    have hsum :
        ((-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt (1 - t)))) *
            (∑ τ : Config N,
              ∫ x : DisorderSpace (N := N),
                  (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                    (ProbabilityTheory.covarianceOperator μ0 (std_basis_right (N := N) τ))
                ∂μ0)
          =
          ∑ τ : Config N,
            ((-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt (1 - t)))) *
              ∫ x : DisorderSpace (N := N),
                  (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                    (ProbabilityTheory.covarianceOperator μ0 (std_basis_right (N := N) τ))
                ∂μ0 := by
      simpa using
        (Finset.mul_sum (s := (Finset.univ : Finset (Config N)))
          (a := ((-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt (1 - t)))))
          (f := fun τ : Config N =>
            ∫ x : DisorderSpace (N := N),
                (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                      gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                  (ProbabilityTheory.covarianceOperator μ0 (std_basis_right (N := N) τ))
              ∂μ0))
    rw [hsum]
    have h1 :
        (∑ τ : Config N,
            ((-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt (1 - t)))) *
              ∫ x : DisorderSpace (N := N),
                  (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                    (ProbabilityTheory.covarianceOperator μ0 (std_basis_right (N := N) τ))
                ∂μ0)
          =
          ∑ τ : Config N,
            ∫ x : DisorderSpace (N := N),
                ((-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt (1 - t)))) *
                  (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                    (ProbabilityTheory.covarianceOperator μ0 (std_basis_right (N := N) τ))
              ∂μ0 := by
      refine Finset.sum_congr rfl (fun τ _hτ => ?_)
      simpa [mul_assoc] using
        (MeasureTheory.integral_const_mul
          ((-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt (1 - t)))) (fun x : DisorderSpace (N := N) =>
            (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                  gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
              (ProbabilityTheory.covarianceOperator μ0 (std_basis_right (N := N) τ)))).symm
    rw [h1]
    have hτ (τ : Config N) :
        (∫ x : DisorderSpace (N := N),
            ((-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt (1 - t)))) *
              (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                    gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                (ProbabilityTheory.covarianceOperator μ0 (std_basis_right (N := N) τ))
          ∂μ0)
          =
          ∫ x : DisorderSpace (N := N),
            (1 / 2 : ℝ) *
              (∑ σ : Config N,
                simple_cov_kernel N β (fun r => q * r) τ σ *
                  hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
                    (std_basis N τ) (std_basis N σ))
          ∂μ0 := by
      refine MeasureTheory.integral_congr_ae ?_
      refine Filter.Eventually.of_forall (fun x => ?_)
      simpa [μ0] using
        (right_pointwise_trace (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          (hindep := hindep) (t := t) (hsqt1 := hsqt1) (x := x) (τ := τ))
    have hrewrite :
        (∑ τ : Config N,
            ∫ x : DisorderSpace (N := N),
                ((-(1 / (N : ℝ))) * (1 / (2 * Real.sqrt (1 - t)))) *
                  (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                    (ProbabilityTheory.covarianceOperator μ0 (std_basis_right (N := N) τ))
              ∂μ0)
          =
          ∑ τ : Config N,
            ∫ x : DisorderSpace (N := N),
                (1 / 2 : ℝ) *
                  (∑ σ : Config N,
                    simple_cov_kernel N β (fun r => q * r) τ σ *
                      hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
                        (std_basis N τ) (std_basis N σ))
              ∂μ0 := by
      refine Finset.sum_congr rfl (fun τ _hτ => hτ τ)
    rw [hrewrite]
    have hIntτ :
        ∀ τ : Config N,
          Integrable (fun x : DisorderSpace (N := N) =>
            (1 / 2 : ℝ) *
              (∑ σ : Config N,
                simple_cov_kernel N β (fun r => q * r) τ σ *
                  hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
                    (std_basis N τ) (std_basis N σ))) μ0 := by
      intro τ
      have hσ :
          Integrable (fun x : DisorderSpace (N := N) =>
            ∑ σ : Config N,
              simple_cov_kernel N β (fun r => q * r) τ σ *
                hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
                  (std_basis N τ) (std_basis N σ)) μ0 := by
        refine MeasureTheory.integrable_finset_sum (μ := μ0)
          (s := (Finset.univ : Finset (Config N)))
          (f := fun σ : Config N => fun x : DisorderSpace (N := N) =>
            simple_cov_kernel N β (fun r => q * r) τ σ *
              hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
                (std_basis N τ) (std_basis N σ)) ?_
        intro σ _hσ
        simpa [μ0] using
          (integrable_kernel_mul_hessian (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk)
            (sim := sim) (t := t)
            (K := fun σ τ => simple_cov_kernel N β (fun r => q * r) σ τ) (σ := τ) (τ := σ))
      simpa [mul_assoc] using hσ.const_mul (1 / 2 : ℝ)
    have hswap :=
      sum_integral_eq_integral_sum (N := N) (f := fun τ : Config N => fun x : DisorderSpace (N := N) =>
        (1 / 2 : ℝ) *
          (∑ σ : Config N,
            simple_cov_kernel N β (fun r => q * r) τ σ *
              hessian_free_energy N (H_t_disorder (N := N) (h := h) t x)
                (std_basis N τ) (std_basis N σ)))
        (μ := μ0) hIntτ
    refine hswap.trans ?_
    refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    simp [SIM, Finset.sum_comm, Finset.mul_sum,
      simple_cov_kernel_symm (N := N) (β := β) (xi := fun r => q * r),
      hessian_free_energy_std_basis_symm (N := N), mul_assoc, mul_left_comm, mul_comm]

  -- Combine SK and SIM contributions, then use `integral_sub` to obtain the final integral form.
  -- The current goal is exactly the IBP RHS; expand `mul_sub` and substitute the two identities above.
  -- (The final RHS uses the original measure; rewrite it to `μ0` using `simp`.)
  have hsub :
      (∫ x : DisorderSpace (N := N), (1 / 2 : ℝ) * SK x ∂μ0)
        - (∫ x : DisorderSpace (N := N), (1 / 2 : ℝ) * SIM x ∂μ0)
        =
        ∫ x : DisorderSpace (N := N),
            ((1 / 2 : ℝ) * SK x - (1 / 2 : ℝ) * SIM x) ∂μ0 := by
    simpa using (MeasureTheory.integral_sub hintSK' hintSIM').symm
  -- Finish: rewrite the IBP expression using `hSKInt` and `hSIMInt`,
  -- then fold the difference of integrals into an integral of the difference.
  --
  -- The goal LHS is the IBP RHS after `rw [hIBP]` and `simp [μ0, μ]`.
  -- We convert it into a difference of the two terms handled by `hSKInt`/`hSIMInt`,
  -- and then finish with `integral_sub`.
  have hrewrite :
      (-(1 / (N : ℝ))) *
          ( ((1 / (2 * Real.sqrt t)) *
                ∑ τ : Config N,
                  ∫ x : DisorderSpace (N := N),
                      (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                            gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                        (ProbabilityTheory.covarianceOperator μ0 (std_basis_left (N := N) τ))
                    ∂μ0)
            -
            ((1 / (2 * Real.sqrt (1 - t))) *
                ∑ τ : Config N,
                  ∫ x : DisorderSpace (N := N),
                      (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                            gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                        (ProbabilityTheory.covarianceOperator μ0 (std_basis_right (N := N) τ))
                    ∂μ0) )
        =
        (∫ x : DisorderSpace (N := N), (1 / 2 : ℝ) * SK x ∂μ0)
          - (∫ x : DisorderSpace (N := N), (1 / 2 : ℝ) * SIM x ∂μ0) := by
    -- distribute the outer scalar over the subtraction, then use `hSKInt`/`hSIMInt`
    -- (avoid normalizing scalars to `2⁻¹` / `√t` inverses, so the patterns match syntactically).
    simp only [mul_sub]
    -- first term
    rw [hSKInt]
    -- second term: rewrite `(-a) * b` as `a * (-b)` and use `hSIMInt`
    rw [hSIMInt]
  -- rewrite the goal using `hrewrite`, then finish by folding the difference of integrals
  -- and normalizing the integrand.
  rw [hrewrite]
  calc
    (∫ x : DisorderSpace (N := N), (1 / 2 : ℝ) * SK x ∂μ0)
        - (∫ x : DisorderSpace (N := N), (1 / 2 : ℝ) * SIM x ∂μ0)
        =
        ∫ x : DisorderSpace (N := N),
            ((1 / 2 : ℝ) * SK x - (1 / 2 : ℝ) * SIM x) ∂μ0 := hsub
    _ =
        ∫ x : DisorderSpace (N := N),
            (1 / 2 : ℝ) * (SK x - SIM x) ∂μ0 := by
      simp [mul_sub, sub_eq_add_neg, mul_add, mul_assoc, mul_left_comm, mul_comm]

end

end

end SpinGlass
