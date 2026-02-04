import SpinGlass.GuerraInterpolation

/-!
## Guerra interpolation: the Gaussian IBP rewriting step

Starting from the analytic derivative identity in `SpinGlass/GuerraInterpolation.lean`,
we rewrite the derivative value into an expression over the intrinsic Gaussian disorder law
`disorderPairLaw` and then apply Hilbert-space Gaussian integration by parts term-by-term.

This file does **not** yet convert the IBP output into Talagrand’s overlap/Hessian trace form;
it packages the clean “IBP-ready” expression.
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

private lemma integrable_coord_left (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V) (τ : Config N) :
    Integrable (fun x : DisorderSpace (N := N) => ((WithLp.ofLp x).1 τ))
      (μ (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim) := by
  classical
  let μ' : Measure (DisorderSpace (N := N)) := μ (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim
  have hgauss : ProbabilityTheory.IsGaussian μ' :=
    SKDisorder.simple_joint_isGaussian_disorderPairLaw_of_indep
      (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) hindep
  haveI : ProbabilityTheory.IsGaussian μ' := hgauss
  have : Integrable (fun x : DisorderSpace (N := N) =>
      inner ℝ (std_basis_left (N := N) τ) x) μ' := by
    simpa using
      (ProbabilityTheory.IsGaussian.integrable_dual (μ := μ')
        (L := (innerSL ℝ (std_basis_left (N := N) τ))))
  have : Integrable (fun x : DisorderSpace (N := N) =>
      inner ℝ x (std_basis_left (N := N) τ)) μ' := by
    simpa [real_inner_comm] using this
  simpa [μ', inner_apply_std_basis_left (N := N) (σ := τ)] using this

private lemma integrable_coord_right (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V) (τ : Config N) :
    Integrable (fun x : DisorderSpace (N := N) => ((WithLp.ofLp x).2 τ))
      (μ (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim) := by
  classical
  let μ' : Measure (DisorderSpace (N := N)) := μ (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim
  have hgauss : ProbabilityTheory.IsGaussian μ' :=
    SKDisorder.simple_joint_isGaussian_disorderPairLaw_of_indep
      (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) hindep
  haveI : ProbabilityTheory.IsGaussian μ' := hgauss
  have : Integrable (fun x : DisorderSpace (N := N) =>
      inner ℝ (std_basis_right (N := N) τ) x) μ' := by
    simpa using
      (ProbabilityTheory.IsGaussian.integrable_dual (μ := μ')
        (L := (innerSL ℝ (std_basis_right (N := N) τ))))
  have : Integrable (fun x : DisorderSpace (N := N) =>
      inner ℝ x (std_basis_right (N := N) τ)) μ' := by
    simpa [real_inner_comm] using this
  simpa [μ', inner_apply_std_basis_right (N := N) (σ := τ)] using this

private lemma aestronglyMeasurable_gibbs_pmf_disorder
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V) (t : ℝ) (σ : Config N) :
    AEStronglyMeasurable
        (fun x : DisorderSpace (N := N) => gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ)
        (μ (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim) := by
  classical
  have hcont_g : Continuous (fun H : EnergySpace N => gibbs_pmf N H σ) :=
    (SpinGlass.contDiff_gibbs_pmf (N := N) σ).continuous
  have hcont_H : Continuous (H_t_disorder (N := N) (h := h) t) := by
    simpa [H_t_disorder] using
      (H_t_disorder_lin (N := N) t).continuous.add continuous_const
  have hmeas : Measurable (fun x : DisorderSpace (N := N) =>
      gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ) :=
    (hcont_g.comp hcont_H).measurable
  exact hmeas.aestronglyMeasurable

private lemma ae_bound_norm_gibbs_pmf_disorder
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V) (t : ℝ) (σ : Config N) :
    (∀ᵐ x ∂(μ (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim),
      ‖gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ‖ ≤ (1 : ℝ)) := by
  refine Filter.Eventually.of_forall (fun x => ?_)
  have hle : gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ ≤ 1 :=
    gibbs_pmf_le_one (N := N) (H := H_t_disorder (N := N) (h := h) t x) (σ := σ)
  have hn : 0 ≤ gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ :=
    gibbs_pmf_nonneg (N := N) (H := H_t_disorder (N := N) (h := h) t x) (σ := σ)
  simpa [Real.norm_eq_abs, abs_of_nonneg hn] using hle

private lemma integrable_left_diag
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V) (t : ℝ) (τ : Config N) :
    Integrable (fun x : DisorderSpace (N := N) =>
        ((WithLp.ofLp x).1 τ) * gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ)
      (μ (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim) := by
  classical
  -- boundedness of the Gibbs factor + integrable coordinate
  -- `bdd_mul` yields integrability of `gibbs_pmf * coord`; commute the product.
  have hint :
      Integrable (fun x : DisorderSpace (N := N) =>
          (gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) * ((WithLp.ofLp x).1 τ))
        (μ (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim) := by
    refine (integrable_coord_left (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        hindep τ).bdd_mul
        (aestronglyMeasurable_gibbs_pmf_disorder (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          hindep t τ)
        (ae_bound_norm_gibbs_pmf_disorder (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          hindep t τ)
  simpa [mul_comm, mul_left_comm, mul_assoc] using hint

private lemma integrable_right_diag
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V) (t : ℝ) (τ : Config N) :
    Integrable (fun x : DisorderSpace (N := N) =>
        ((WithLp.ofLp x).2 τ) * gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ)
      (μ (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim) := by
  classical
  have hint :
      Integrable (fun x : DisorderSpace (N := N) =>
          (gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) * ((WithLp.ofLp x).2 τ))
        (μ (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim) := by
    refine (integrable_coord_right (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        hindep τ).bdd_mul
        (aestronglyMeasurable_gibbs_pmf_disorder (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          hindep t τ)
        (ae_bound_norm_gibbs_pmf_disorder (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          hindep t τ)
  simpa [mul_comm, mul_left_comm, mul_assoc] using hint

/--
The scalar derivative integrand value `∫ ω ⟪∇F_N(H_t ω), dH_t ω⟫ dℙ` is equal to a linear combination
of IBP expressions over `disorderPairLaw`.

This is the clean “after IBP, before trace/Hessian” form.
-/
theorem derivative_value_guerraPhi_eq_ibp
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V)
    (t : ℝ) :
    (∫ ω,
        (fderiv ℝ (fun H' : EnergySpace N => free_energy_density (N := N) H')
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω))
          (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
        ∂ℙ)
      =
      (-(1 / (N : ℝ))) *
        ( (1 / (2 * Real.sqrt t)) *
            ∑ τ : Config N,
              ∫ x : DisorderSpace (N := N),
                (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                    gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                  (ProbabilityTheory.covarianceOperator
                    (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
                    (std_basis_left (N := N) τ))
                ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
          -
          (1 / (2 * Real.sqrt (1 - t))) *
            ∑ τ : Config N,
              ∫ x : DisorderSpace (N := N),
                (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                    gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                  (ProbabilityTheory.covarianceOperator
                    (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
                    (std_basis_right (N := N) τ))
                ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)) ) := by
  classical
  -- Start from the analytic simplification: `∫ ⟪∇F, dH⟫ = -(1/N) * ∫ E_Gibbs[dH]`.
  have hder0 :
      (∫ ω,
          (fderiv ℝ (fun H' : EnergySpace N => free_energy_density (N := N) H')
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω))
            (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
          ∂ℙ)
        =
        (-(1 / (N : ℝ))) *
          ∫ ω,
            (∑ σ : Config N,
                gibbs_pmf N
                    (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω) σ *
                  (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω) σ)
            ∂ℙ := by
    -- this is exactly `derivative_value_guerraPhi_eq`
    simpa [derivative_value_guerraPhi_eq (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t]
  -- Push the remaining integral to `disorderPairLaw`.
  let μ' : Measure (DisorderSpace (N := N)) := μ (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim
  have hmeas_pair :
      AEMeasurable
        (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
        (ℙ : Measure Ω) :=
    (measurable_disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)).aemeasurable
  -- Define the disorder-space integrand and record measurability.
  let F : DisorderSpace (N := N) → ℝ :=
    fun x =>
      (∑ σ : Config N,
          gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ *
            (dH_t_disorder (N := N) t x) σ)
  have hF_meas : Measurable F := by
    -- each summand is measurable: `gibbs_pmf` is continuous in `H`, `H_t_disorder` is continuous,
    -- and `dH_t_disorder` is affine in the left/right coordinates.
    have hcont0 : ∀ σ : Config N, Continuous (fun H : EnergySpace N => gibbs_pmf N H σ) :=
      fun σ => (SpinGlass.contDiff_gibbs_pmf (N := N) σ).continuous
    have hcontH : Continuous (H_t_disorder (N := N) (h := h) t) := by
      simpa [H_t_disorder] using
        (H_t_disorder_lin (N := N) t).continuous.add continuous_const
    have hg_meas : ∀ σ : Config N, Measurable (fun x : DisorderSpace (N := N) =>
        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ) :=
      fun σ => (hcont0 σ).comp hcontH |>.measurable
    have hd_meas : ∀ σ : Config N, Measurable (fun x : DisorderSpace (N := N) =>
        (dH_t_disorder (N := N) t x) σ) := by
      intro σ
      have h1 : Measurable (fun x : DisorderSpace (N := N) => ((WithLp.ofLp x).1 σ)) :=
        measurable_coord_left (N := N) (τ := σ)
      have h2 : Measurable (fun x : DisorderSpace (N := N) => ((WithLp.ofLp x).2 σ)) :=
        measurable_coord_right (N := N) (τ := σ)
      have ha : Measurable (fun x : DisorderSpace (N := N) =>
          (1 / (2 * Real.sqrt t)) * ((WithLp.ofLp x).1 σ)) :=
        measurable_const.mul h1
      have hb : Measurable (fun x : DisorderSpace (N := N) =>
          (1 / (2 * Real.sqrt (1 - t))) * ((WithLp.ofLp x).2 σ)) :=
        measurable_const.mul h2
      simpa [dH_t_disorder, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using ha.sub hb
    -- combine: measurable of each summand, then measurable_sum
    refine Finset.measurable_sum (s := (Finset.univ : Finset (Config N)))
      (f := fun σ : Config N => fun x : DisorderSpace (N := N) =>
        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ * (dH_t_disorder (N := N) t x) σ)
      (by
        intro σ _hσ
        exact (hg_meas σ).mul (hd_meas σ))
  have hF_ae : AEStronglyMeasurable F μ' := hF_meas.aestronglyMeasurable
  have hmap :
      (∫ x : DisorderSpace (N := N), F x ∂μ') =
        ∫ ω, F (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) ω) ∂ℙ := by
    simpa [μ', μ, disorderPairLaw] using
      (MeasureTheory.integral_map (μ := (ℙ : Measure Ω))
        (φ := disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
        hmeas_pair hF_ae)
  have hpull :
      (fun ω =>
          (∑ σ : Config N,
              gibbs_pmf N
                  (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω) σ *
                (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω) σ))
        =
      fun ω => F (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) ω) := by
    funext ω
    simp [F,
      H_t_disorder_disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim),
      dH_t_disorder_disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)]
  -- Replace the ℙ-integral by the μ-integral.
  have hpush :
      (∫ ω,
          (∑ σ : Config N,
              gibbs_pmf N
                  (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω) σ *
                (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω) σ)
          ∂ℙ)
        =
      ∫ x : DisorderSpace (N := N), F x ∂μ' := by
    -- `hmap` gives the reverse direction; use `hpull` to rewrite.
    have := hmap.symm
    simpa [hpull] using this
  -- Expand `F` into left/right diagonal sums and apply IBP term-by-term.
  have hdecompF :
      F
        =
      (fun x : DisorderSpace (N := N) =>
          (1 / (2 * Real.sqrt t)) *
            (∑ τ : Config N, ((WithLp.ofLp x).1 τ) * gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ)
          -
          (1 / (2 * Real.sqrt (1 - t))) *
            (∑ τ : Config N, ((WithLp.ofLp x).2 τ) * gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ)) := by
    funext x
    -- expand `dH_t_disorder` and distribute products, then collect the two diagonal sums
    simp [F, dH_t_disorder, sub_eq_add_neg, Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_mul, mul_add, mul_assoc, mul_left_comm, mul_comm]
  -- Integrate the decomposition; use `integral_finset_sum` and apply the packaged IBP lemmas.
  have hIntLeft : ∀ τ : Config N, Integrable (fun x : DisorderSpace (N := N) =>
      ((WithLp.ofLp x).1 τ) * gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) μ' := by
    intro τ
    simpa [μ', μ] using
      (integrable_left_diag (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        hindep t τ)
  have hIntRight : ∀ τ : Config N, Integrable (fun x : DisorderSpace (N := N) =>
      ((WithLp.ofLp x).2 τ) * gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) μ' := by
    intro τ
    simpa [μ', μ] using
      (integrable_right_diag (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        hindep t τ)
  -- Now the actual calculation (kept stable: explicit `integral_sub`, `integral_const_mul`,
  -- and `integral_finset_sum`, avoiding fragile `simp` linearity expansions).
  classical
  -- abbreviations for the left/right coefficient and diagonal sums
  set aU : ℝ := (1 / (2 * Real.sqrt t))
  set aV : ℝ := (1 / (2 * Real.sqrt (1 - t)))
  set sumL : DisorderSpace (N := N) → ℝ :=
    fun x => ∑ τ : Config N, ((WithLp.ofLp x).1 τ) * gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ
  set sumR : DisorderSpace (N := N) → ℝ :=
    fun x => ∑ τ : Config N, ((WithLp.ofLp x).2 τ) * gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ
  have hF_eq : F = fun x : DisorderSpace (N := N) => aU * sumL x - aV * sumR x := by
    funext x
    have := congrArg (fun f => f x) hdecompF
    simpa [aU, aV, sumL, sumR] using this
  have hIntSumL : Integrable sumL μ' := by
    -- integrable finite sum from `hIntLeft`
    have h :=
      MeasureTheory.integrable_finset_sum (μ := μ') (s := (Finset.univ : Finset (Config N)))
        (f := fun τ : Config N => fun x : DisorderSpace (N := N) =>
          ((WithLp.ofLp x).1 τ) * gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ)
        (by
          intro τ _hτ
          simpa using hIntLeft τ)
    simpa [sumL] using h
  have hIntSumR : Integrable sumR μ' := by
    have h :=
      MeasureTheory.integrable_finset_sum (μ := μ') (s := (Finset.univ : Finset (Config N)))
        (f := fun τ : Config N => fun x : DisorderSpace (N := N) =>
          ((WithLp.ofLp x).2 τ) * gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ)
        (by
          intro τ _hτ
          simpa using hIntRight τ)
    simpa [sumR] using h
  have hInt_aU_sumL : Integrable (fun x : DisorderSpace (N := N) => aU * sumL x) μ' :=
    (hIntSumL.const_mul aU)
  have hInt_aV_sumR : Integrable (fun x : DisorderSpace (N := N) => aV * sumR x) μ' :=
    (hIntSumR.const_mul aV)
  have hsumL :
      (∫ x : DisorderSpace (N := N), sumL x ∂μ')
        =
        ∑ τ : Config N,
          ∫ x : DisorderSpace (N := N),
            ((WithLp.ofLp x).1 τ) * gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ ∂μ' := by
    -- swap integral and finite sum
    have :=
      (MeasureTheory.integral_finset_sum (μ := μ') (s := (Finset.univ : Finset (Config N)))
        (f := fun τ : Config N => fun x : DisorderSpace (N := N) =>
          ((WithLp.ofLp x).1 τ) * gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ)
        (by
          intro τ _hτ
          simpa using hIntLeft τ))
    simpa [sumL] using this
  have hsumR :
      (∫ x : DisorderSpace (N := N), sumR x ∂μ')
        =
        ∑ τ : Config N,
          ∫ x : DisorderSpace (N := N),
            ((WithLp.ofLp x).2 τ) * gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ ∂μ' := by
    have :=
      (MeasureTheory.integral_finset_sum (μ := μ') (s := (Finset.univ : Finset (Config N)))
        (f := fun τ : Config N => fun x : DisorderSpace (N := N) =>
          ((WithLp.ofLp x).2 τ) * gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ)
        (by
          intro τ _hτ
          simpa using hIntRight τ))
    simpa [sumR] using this
  -- packaged IBP equalities for the diagonal terms
  have hIBP_left : ∀ τ : Config N,
      (∫ x : DisorderSpace (N := N),
          ((WithLp.ofLp x).1 τ) * gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ
          ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)))
        =
        ∫ x : DisorderSpace (N := N),
          (fderiv ℝ (fun x : DisorderSpace (N := N) =>
              gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
            (ProbabilityTheory.covarianceOperator
              (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
              (std_basis_left (N := N) τ))
          ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)) := by
    intro τ
    simpa using
      (integral_disorderPairLaw_left_apply_mul_gibbs_pmf_eq_integral_fderiv_covarianceOperator
        (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        (hindep := hindep) (t := t) (σ := τ) (τ := τ))
  have hIBP_right : ∀ τ : Config N,
      (∫ x : DisorderSpace (N := N),
          ((WithLp.ofLp x).2 τ) * gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ
          ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)))
        =
        ∫ x : DisorderSpace (N := N),
          (fderiv ℝ (fun x : DisorderSpace (N := N) =>
              gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
            (ProbabilityTheory.covarianceOperator
              (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
              (std_basis_right (N := N) τ))
          ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)) := by
    intro τ
    simpa using
      (integral_disorderPairLaw_right_apply_mul_gibbs_pmf_eq_integral_fderiv_covarianceOperator
        (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        (hindep := hindep) (t := t) (σ := τ) (τ := τ))

  -- main chain (no `calc`: avoid parser/elaboration instability)
  have h0 :
      (∫ ω,
          (fderiv ℝ (fun H' : EnergySpace N => free_energy_density (N := N) H')
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω))
            (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
          ∂ℙ)
        = (-(1 / (N : ℝ))) * ∫ x : DisorderSpace (N := N), F x ∂μ' := by
    have := congrArg (fun I => (-(1 / (N : ℝ))) * I) hpush
    simpa [hder0, mul_assoc] using this

  have hμ' :
      μ' =
        disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) := by
    rfl

  have hIntF :
      (∫ x : DisorderSpace (N := N), F x ∂μ')
        =
        (aU *
            ∑ τ : Config N,
              ∫ x : DisorderSpace (N := N),
                (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                    gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                  (ProbabilityTheory.covarianceOperator
                    (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
                    (std_basis_left (N := N) τ))
                ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)))
        -
        (aV *
            ∑ τ : Config N,
              ∫ x : DisorderSpace (N := N),
                (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                    gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                  (ProbabilityTheory.covarianceOperator
                    (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
                    (std_basis_right (N := N) τ))
                ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))) := by
    -- start: rewrite integrand
    have hFint :
        (∫ x : DisorderSpace (N := N), F x ∂μ')
          =
          ∫ x : DisorderSpace (N := N), (aU * sumL x - aV * sumR x) ∂μ' := by
      simp [hF_eq]
    -- linearity: integral of difference + pull constants out
    have hsub :
        (∫ x : DisorderSpace (N := N), (aU * sumL x - aV * sumR x) ∂μ')
          =
          (∫ x : DisorderSpace (N := N), (aU * sumL x) ∂μ')
            -
          (∫ x : DisorderSpace (N := N), (aV * sumR x) ∂μ') := by
      simpa using (MeasureTheory.integral_sub (μ := μ') hInt_aU_sumL hInt_aV_sumR)
    have hconstL :
        (∫ x : DisorderSpace (N := N), (aU * sumL x) ∂μ')
          = aU * ∫ x : DisorderSpace (N := N), sumL x ∂μ' := by
      simpa using (MeasureTheory.integral_const_mul (μ := μ') (r := aU) (f := sumL))
    have hconstR :
        (∫ x : DisorderSpace (N := N), (aV * sumR x) ∂μ')
          = aV * ∫ x : DisorderSpace (N := N), sumR x ∂μ' := by
      simpa using (MeasureTheory.integral_const_mul (μ := μ') (r := aV) (f := sumR))
    -- swap integral and finite sums
    -- `∫ sumL = ∑ ∫ (leftCoord * gibbs_pmf)`
    -- `∫ sumR = ∑ ∫ (rightCoord * gibbs_pmf)`
    -- then apply IBP term-by-term.
    -- First reduce to the diagonal coordinate integrals:
    have hdiag :
        (∫ x : DisorderSpace (N := N), F x ∂μ')
          =
          (aU *
              ∑ τ : Config N,
                ∫ x : DisorderSpace (N := N),
                  ((WithLp.ofLp x).1 τ) * gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ ∂μ')
          -
          (aV *
              ∑ τ : Config N,
                ∫ x : DisorderSpace (N := N),
                  ((WithLp.ofLp x).2 τ) * gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ ∂μ') := by
      -- rewrite `∫ F` via `hFint`, then `hsub`, then constants and `hsumL/hsumR`
      rw [hFint, hsub, hconstL, hconstR, hsumL, hsumR]
    -- Now apply IBP to each diagonal term.
    have hsumL_ibp :
        (∑ τ : Config N,
            ∫ x : DisorderSpace (N := N),
              ((WithLp.ofLp x).1 τ) * gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ ∂μ')
          =
        (∑ τ : Config N,
            ∫ x : DisorderSpace (N := N),
              (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                  gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                (ProbabilityTheory.covarianceOperator
                  (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
                  (std_basis_left (N := N) τ))
              ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))) := by
      classical
      -- rewrite `μ'` as `disorderPairLaw` and apply `hIBP_left` termwise
      refine Finset.sum_congr rfl (fun τ _hτ => ?_)
      simpa [hμ'] using (hIBP_left (τ := τ))
    have hsumR_ibp :
        (∑ τ : Config N,
            ∫ x : DisorderSpace (N := N),
              ((WithLp.ofLp x).2 τ) * gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ ∂μ')
          =
        (∑ τ : Config N,
            ∫ x : DisorderSpace (N := N),
              (fderiv ℝ (fun x : DisorderSpace (N := N) =>
                  gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) τ) x)
                (ProbabilityTheory.covarianceOperator
                  (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
                  (std_basis_right (N := N) τ))
              ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))) := by
      classical
      refine Finset.sum_congr rfl (fun τ _hτ => ?_)
      simpa [hμ'] using (hIBP_right (τ := τ))
    -- combine
    rw [hdiag, hsumL_ibp, hsumR_ibp]

  -- finish
  -- rewrite the LHS using `h0`, then replace `∫ F` using `hIntF`
  rw [h0, hIntF]
  -- nothing left to do: `rw` closes the goal

end

end

end SpinGlass

