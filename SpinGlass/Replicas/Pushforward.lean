/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Replicas.Derivative

/-!
# Pushforward to the disorder law, and dominated differentiation

The replica quantities of `SpinGlass.Replicas.Derivative` transported to the disorder law
`disorderPairLaw`, and the differentiation under the integral sign that turns the pointwise
derivative of the interpolation into the derivative of `ν_t(f)`. Talagrand Vol. I, Lemma 1.4.2.
-/

open MeasureTheory ProbabilityTheory Real BigOperators SpinGlass Set
open scoped ENNReal NNReal Topology

namespace SpinGlass

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable (N : ℕ) (h : ℝ)
variable {K₁ K₂ : Config N → Config N → ℝ}
variable (G₁ : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K₁)
variable (G₂ : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K₂)

section ReplicaCalculus

variable (n : ℕ)
/-! ### Pushforward to `disorderPairLaw` -/

lemma measurable_coord_left (τ : Config N) :
    Measurable (fun x : DisorderSpace (N := N) => ((WithLp.ofLp x).1 τ)) := by
  -- rewrite as an inner product with `std_basis_left`.
  have hcont : Continuous (fun x : DisorderSpace (N := N) => inner ℝ x (std_basis_left (N := N) τ))
    := by
    have : Continuous (fun x : DisorderSpace (N := N) => (x, std_basis_left (N := N) τ)) :=
      continuous_id.prodMk continuous_const
    exact continuous_inner.comp this
  simpa [inner_apply_std_basis_left (N := N) (σ := τ)] using hcont.measurable

lemma measurable_coord_right (τ : Config N) :
    Measurable (fun x : DisorderSpace (N := N) => ((WithLp.ofLp x).2 τ)) := by
  have hcont : Continuous (fun x : DisorderSpace (N := N) => inner ℝ x (std_basis_right (N := N) τ))
    := by
    have : Continuous (fun x : DisorderSpace (N := N) => (x, std_basis_right (N := N) τ)) :=
      continuous_id.prodMk continuous_const
    exact continuous_inner.comp this
  simpa [inner_apply_std_basis_right (N := N) (σ := τ)] using hcont.measurable

lemma measurable_dgibbs_average_n_disorder (t : ℝ) (f : ReplicaFun N n) :
    Measurable (dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f) := by
  classical
  -- Use the explicit left/right decomposition into finite sums of measurable terms.
  have hA : ∀ τ : Config N,
      Measurable (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) :=
    fun τ => measurable_A_disorder_explicit (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ)
  have hleft :
      Measurable (fun x : DisorderSpace (N := N) =>
        ∑ τ : Config N, ((WithLp.ofLp x).1 τ) *
          A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x) := by
    simpa using
      (Finset.measurable_sum (s := (Finset.univ : Finset (Config N)))
        (f := fun τ : Config N =>
          fun x : DisorderSpace (N := N) => ((WithLp.ofLp x).1 τ) *
            A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x)
        (by
          intro τ _hτ
          exact (measurable_coord_left (N := N) τ).mul (hA τ)))
  have hright :
      Measurable (fun x : DisorderSpace (N := N) =>
        ∑ τ : Config N, ((WithLp.ofLp x).2 τ) *
          A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x) := by
    simpa using
      (Finset.measurable_sum (s := (Finset.univ : Finset (Config N)))
        (f := fun τ : Config N =>
          fun x : DisorderSpace (N := N) => ((WithLp.ofLp x).2 τ) *
            A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x)
        (by
          intro τ _hτ
          exact (measurable_coord_right (N := N) τ).mul (hA τ)))
  -- Combine the two sums with scalar multiplications.
  have hcomb :
      Measurable (fun x : DisorderSpace (N := N) =>
        (1 / (2 * Real.sqrt t)) *
            (∑ τ : Config N, ((WithLp.ofLp x).1 τ) *
              A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x)
          -
          (1 / (2 * Real.sqrt (1 - t))) *
            (∑ τ : Config N, ((WithLp.ofLp x).2 τ) *
              A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x)) :=
    (measurable_const.mul hleft).sub (measurable_const.mul hright)
  -- Rewrite `dgibbs_average_n_disorder` by the explicit formula.
  have hEq :
      dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f
        =
        (fun x : DisorderSpace (N := N) =>
          (1 / (2 * Real.sqrt t)) *
              (∑ τ : Config N, ((WithLp.ofLp x).1 τ) *
                A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x)
            -
            (1 / (2 * Real.sqrt (1 - t))) *
              (∑ τ : Config N, ((WithLp.ofLp x).2 τ) *
                A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x)) := by
    funext x
    simpa using
      (dgibbs_average_n_disorder_eq_sum_left_right_explicit
        (N := N) (n := n) (h := h) (t := t) (f := f) x)
  simpa [hEq] using hcomb

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma integral_dgibbs_average_n_eq_integral_disorderPairLaw (t : ℝ) (f : ReplicaFun N n) :
    (∫ w, dgibbs_average_n (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) n t f w ∂ℙ)
      =
      ∫ x : DisorderSpace (N := N),
        dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f x
          ∂(disorderPairLaw (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂)) :=
            by
  classical
  -- `disorderPairLaw = ℙ.map disorderPair`.
  let μ : Measure (DisorderSpace (N := N)) :=
    disorderPairLaw (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂)
  have hmeas : AEMeasurable (disorderPair (Ω := Ω) (N := N)
      (G₁ := G₁) (G₂ := G₂)) (ℙ : Measure Ω) :=
    (measurable_disorderPair (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂)).aemeasurable
  have hF :
      AEStronglyMeasurable (dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f) μ := by
    -- measurability on `DisorderSpace` implies `AEStronglyMeasurable`.
    simpa [μ] using
      (measurable_dgibbs_average_n_disorder (N := N) (n := n) (h := h) (t := t) (f :=
        f)).aestronglyMeasurable
  -- Use `integral_map` and then the simp lemma relating `dgibbs_average_n_disorder` to
  -- `dgibbs_average_n`.
  have hmap :
      (∫ x : DisorderSpace (N := N), dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f x ∂μ)
        =
        ∫ w, dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f
            (disorderPair (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂) w) ∂ℙ
              := by
    -- `μ = map disorderPair ℙ` by definition.
    simpa [μ, disorderPairLaw] using
      (MeasureTheory.integral_map (μ := (ℙ : Measure Ω)) (φ :=
        disorderPair (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂))
        hmeas hF)
  simp [hmap, μ]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem integral_dgibbs_average_n_disorder_eq_ibp
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) (t : ℝ) (f : ReplicaFun N n) :
    (∫ x : DisorderSpace (N := N),
        dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f x
        ∂(disorderPairLaw (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂)))
      =
      (1 / (2 * Real.sqrt t)) *
          ∑ τ : Config N,
            ∫ x : DisorderSpace (N := N),
              (fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x)
                (ProbabilityTheory.covarianceOperator
                  (disorderPairLaw (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂))
                  (std_basis_left (N := N) τ))
              ∂(disorderPairLaw (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂))
        -
        (1 / (2 * Real.sqrt (1 - t))) *
          ∑ τ : Config N,
            ∫ x : DisorderSpace (N := N),
              (fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x)
                (ProbabilityTheory.covarianceOperator
                  (disorderPairLaw (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂))
                  (std_basis_right (N := N) τ))
              ∂(disorderPairLaw (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂)) := by
  classical
  let μ : Measure (DisorderSpace (N := N)) :=
    disorderPairLaw (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂)
  -- Start from the explicit decomposition.
  have hdecomp :
      (fun x : DisorderSpace (N := N) =>
          dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f x)
        =
        (fun x : DisorderSpace (N := N) =>
          (1 / (2 * Real.sqrt t)) *
              ∑ τ : Config N, ((WithLp.ofLp x).1 τ) *
                A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x
            -
            (1 / (2 * Real.sqrt (1 - t))) *
              ∑ τ : Config N, ((WithLp.ofLp x).2 τ) *
                A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x) := by
    funext x
    simpa using
      (dgibbs_average_n_disorder_eq_sum_left_right_explicit (N := N) (n := n) (h := h) (t := t) (f
        := f) x)
  -- Integrability of each summand (bounded `A_disorder_explicit` times integrable coordinate).
  have hIntLeft :
      ∀ τ : Config N, Integrable (fun x : DisorderSpace (N := N) =>
        ((WithLp.ofLp x).1 τ) *
          A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x) μ := by
    intro τ
    -- coordinate is integrable under Gaussian law
    have hgauss : ProbabilityTheory.IsGaussian μ :=
      isGaussian_disorderPairLaw_of_indep (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂) hindep
    have : ProbabilityTheory.IsGaussian μ := hgauss
    have hcoord :
        Integrable (fun x : DisorderSpace (N := N) => ((WithLp.ofLp x).1 τ)) μ := by
      have : Integrable (fun x : DisorderSpace (N := N) => inner ℝ (std_basis_left (N := N) τ) x) μ
        := by
        simpa using
          (ProbabilityTheory.IsGaussian.integrable_dual (μ := μ) (L := (innerSL ℝ (std_basis_left (N
            := N) τ))))
      have : Integrable (fun x : DisorderSpace (N := N) => inner ℝ x (std_basis_left (N := N) τ)) μ
        := by
        simpa [real_inner_comm] using this
      simpa [inner_apply_std_basis_left (N := N) (σ := τ)] using this
    have hA_meas :
        AEStronglyMeasurable (fun x : DisorderSpace (N := N) =>
          A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x) μ :=
      (measurable_A_disorder_explicit (N := N) (n := n) (h := h) (t := t) (f := f) (τ :=
        τ)).aestronglyMeasurable
    -- uniform bound from `abs_A_disorder_explicit_le`
    let Sf : ℝ := ∑ σs : ReplicaSpace N n, |f σs|
    let C : ℝ := (2 * (n : ℝ)) * Sf
    have hA_bound : ∀ᵐ x ∂μ, ‖A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x‖ ≤ C :=
      by
      refine Filter.Eventually.of_forall (fun x => ?_)
      have : |A_disorder_explicit (N := N) (n := n) (h := h) t f τ x| ≤ C := by
        simpa [C, Sf] using
          (abs_A_disorder_explicit_le (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ) x)
      simpa [Real.norm_eq_abs] using this
    -- `A` is bounded, so `coord * A` is integrable.
    -- Use `bdd_mul` with `g = coord`, `f = A`, then commute.
    have : Integrable (fun x : DisorderSpace (N := N) =>
        (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x) *
          ((WithLp.ofLp x).1 τ)) μ :=
      (Integrable.bdd_mul (hg := hcoord) (hf := hA_meas) (hf_bound := hA_bound))
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hIntRight :
      ∀ τ : Config N, Integrable (fun x : DisorderSpace (N := N) =>
        ((WithLp.ofLp x).2 τ) *
          A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x) μ := by
    intro τ
    have hgauss : ProbabilityTheory.IsGaussian μ :=
      isGaussian_disorderPairLaw_of_indep (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂) hindep
    have : ProbabilityTheory.IsGaussian μ := hgauss
    have hcoord :
        Integrable (fun x : DisorderSpace (N := N) => ((WithLp.ofLp x).2 τ)) μ := by
      have : Integrable (fun x : DisorderSpace (N := N) => inner ℝ (std_basis_right (N := N) τ) x) μ
        := by
        simpa using
          (ProbabilityTheory.IsGaussian.integrable_dual (μ := μ) (L := (innerSL ℝ (std_basis_right
            (N := N) τ))))
      have : Integrable (fun x : DisorderSpace (N := N) => inner ℝ x (std_basis_right (N := N) τ)) μ
        := by
        simpa [real_inner_comm] using this
      simpa [inner_apply_std_basis_right (N := N) (σ := τ)] using this
    have hA_meas :
        AEStronglyMeasurable (fun x : DisorderSpace (N := N) =>
          A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x) μ :=
      (measurable_A_disorder_explicit (N := N) (n := n) (h := h) (t := t) (f := f) (τ :=
        τ)).aestronglyMeasurable
    let Sf : ℝ := ∑ σs : ReplicaSpace N n, |f σs|
    let C : ℝ := (2 * (n : ℝ)) * Sf
    have hA_bound : ∀ᵐ x ∂μ, ‖A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x‖ ≤ C :=
      by
      refine Filter.Eventually.of_forall (fun x => ?_)
      have : |A_disorder_explicit (N := N) (n := n) (h := h) t f τ x| ≤ C := by
        simpa [C, Sf] using
          (abs_A_disorder_explicit_le (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ) x)
      simpa [Real.norm_eq_abs] using this
    have : Integrable (fun x : DisorderSpace (N := N) =>
        (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x) *
          ((WithLp.ofLp x).2 τ)) μ :=
      (Integrable.bdd_mul (hg := hcoord) (hf := hA_meas) (hf_bound := hA_bound))
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  -- Rewrite the integral using `hdecomp`, then push integrals through sums and apply IBP.
  simp only [one_div, mul_inv_rev, WithLp.ofLp_fst, WithLp.ofLp_snd, μ] at *
  -- main computation
  have hleft_sum :
      (∫ x : DisorderSpace (N := N),
          ∑ τ : Config N, ((WithLp.ofLp x).1 τ) *
            A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x ∂μ)
        =
        ∑ τ : Config N,
          ∫ x : DisorderSpace (N := N),
            ((WithLp.ofLp x).1 τ) *
              A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x ∂μ := by
    simpa using
      (MeasureTheory.integral_finsetSum (μ := μ) (s := (Finset.univ : Finset (Config N)))
        (f := fun τ : Config N =>
          fun x : DisorderSpace (N := N) => ((WithLp.ofLp x).1 τ) *
            A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x)
        (hf := by
          intro τ hτ
          simpa using hIntLeft τ))
  have hright_sum :
      (∫ x : DisorderSpace (N := N),
          ∑ τ : Config N, ((WithLp.ofLp x).2 τ) *
            A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x ∂μ)
        =
        ∑ τ : Config N,
          ∫ x : DisorderSpace (N := N),
            ((WithLp.ofLp x).2 τ) *
              A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x ∂μ := by
    simpa using
      (MeasureTheory.integral_finsetSum (μ := μ) (s := (Finset.univ : Finset (Config N)))
        (f := fun τ : Config N =>
          fun x : DisorderSpace (N := N) => ((WithLp.ofLp x).2 τ) *
            A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x)
        (hf := by
          intro τ hτ
          simpa using hIntRight τ))
  -- Apply IBP per coordinate inside the sums.
  have hIBP_left :
      (∑ τ : Config N,
          ∫ x : DisorderSpace (N := N),
            ((WithLp.ofLp x).1 τ) *
              A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x ∂μ)
        =
        ∑ τ : Config N,
          ∫ x : DisorderSpace (N := N),
            (fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x)
              (ProbabilityTheory.covarianceOperator μ (std_basis_left (N := N) τ)) ∂μ := by
    classical
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    -- use the packaged lemma (with `σ = τ`).
    simpa [μ] using
      (integral_disorderPairLaw_left_apply_mul_A_disorder_explicit_eq
        (Ω := Ω) (N := N) (h := h) (G₁ := G₁) (G₂ := G₂)
        (hindep := hindep) (t := t) (f := f) (σ := τ) (τ := τ))
  have hIBP_right :
      (∑ τ : Config N,
          ∫ x : DisorderSpace (N := N),
            ((WithLp.ofLp x).2 τ) *
              A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x ∂μ)
        =
        ∑ τ : Config N,
          ∫ x : DisorderSpace (N := N),
            (fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x)
              (ProbabilityTheory.covarianceOperator μ (std_basis_right (N := N) τ)) ∂μ := by
    classical
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    simpa [μ] using
      (integral_disorderPairLaw_right_apply_mul_A_disorder_explicit_eq
        (Ω := Ω) (N := N) (h := h) (G₁ := G₁) (G₂ := G₂)
        (hindep := hindep) (t := t) (f := f) (σ := τ) (τ := τ))
  -- Assemble: push integrals through constants/sums then apply IBP.
  let Sleft : DisorderSpace (N := N) → ℝ :=
    fun x => ∑ τ : Config N, ((WithLp.ofLp x).1 τ) *
      A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x
  let Sright : DisorderSpace (N := N) → ℝ :=
    fun x => ∑ τ : Config N, ((WithLp.ofLp x).2 τ) *
      A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x
  have hSleft_int : Integrable Sleft μ := by
    -- integrable finite sum
    classical
    simpa [Sleft] using
      (MeasureTheory.integrable_finsetSum (μ := μ) (s := (Finset.univ : Finset (Config N)))
        (f := fun τ : Config N =>
          fun x : DisorderSpace (N := N) => ((WithLp.ofLp x).1 τ) *
            A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x)
        (hf := by
          intro τ hτ
          simpa using hIntLeft τ))
  have hSright_int : Integrable Sright μ := by
    classical
    simpa [Sright] using
      (MeasureTheory.integrable_finsetSum (μ := μ) (s := (Finset.univ : Finset (Config N)))
        (f := fun τ : Config N =>
          fun x : DisorderSpace (N := N) => ((WithLp.ofLp x).2 τ) *
            A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x)
        (hf := by
          intro τ hτ
          simpa using hIntRight τ))
  -- rewrite the LHS using `hdecomp`
  have hLHS :
      (∫ x : DisorderSpace (N := N),
          dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f x ∂μ)
        =
        ∫ x : DisorderSpace (N := N),
          (1 / (2 * Real.sqrt t)) * Sleft x - (1 / (2 * Real.sqrt (1 - t))) * Sright x ∂μ := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    -- unfold `Sleft/Sright` and use `hdecomp`
    simp [Sleft, Sright, hdecomp]
  -- Now compute the RHS integral using linearity.
  rw [hLHS]
  -- integrability for `integral_sub`
  have hL1 : Integrable (fun x => (1 / (2 * Real.sqrt t)) * Sleft x) μ :=
    hSleft_int.const_mul (1 / (2 * Real.sqrt t))
  have hL2 : Integrable (fun x => (1 / (2 * Real.sqrt (1 - t))) * Sright x) μ :=
    hSright_int.const_mul (1 / (2 * Real.sqrt (1 - t)))
  -- split the subtraction
  rw [MeasureTheory.integral_sub hL1 hL2]
  -- rewrite the integrals of the sums
  have hSleft :
      (∫ x : DisorderSpace (N := N), Sleft x ∂μ)
        =
        ∑ τ : Config N,
          ∫ x : DisorderSpace (N := N),
            ((WithLp.ofLp x).1 τ) *
              A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x ∂μ := by
    simpa [Sleft] using hleft_sum
  have hSright :
      (∫ x : DisorderSpace (N := N), Sright x ∂μ)
        =
        ∑ τ : Config N,
          ∫ x : DisorderSpace (N := N),
            ((WithLp.ofLp x).2 τ) *
              A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x ∂μ := by
    simpa [Sright] using hright_sum
  -- now pull constants and apply IBP on each sum
  -- The rewriting steps below sometimes normalize the coordinate functionals using `WithLp.fst/snd`
  -- and `PiLp.ofLp`. We bridge that normalization explicitly, then use `hIBP_left/right`.
  have hIBP_left_fst :
      (∑ τ : Config N,
          ∫ x : DisorderSpace (N := N),
            (WithLp.fst x).ofLp τ *
              A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x ∂μ)
        =
        ∑ τ : Config N,
          ∫ x : DisorderSpace (N := N),
            (fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x)
              (ProbabilityTheory.covarianceOperator μ (std_basis_left (N := N) τ)) ∂μ := by
    classical
    have hL :
        (∑ τ : Config N,
            ∫ x : DisorderSpace (N := N),
              (WithLp.fst x).ofLp τ *
                A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x ∂μ)
          =
          ∑ τ : Config N,
            ∫ x : DisorderSpace (N := N),
              ((WithLp.ofLp x).1 τ) *
                A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x ∂μ := by
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x
      rfl
    simpa [hL] using hIBP_left
  have hIBP_right_snd :
      (∑ τ : Config N,
          ∫ x : DisorderSpace (N := N),
            (WithLp.snd x).ofLp τ *
              A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x ∂μ)
        =
        ∑ τ : Config N,
          ∫ x : DisorderSpace (N := N),
            (fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x)
              (ProbabilityTheory.covarianceOperator μ (std_basis_right (N := N) τ)) ∂μ := by
    classical
    have hL :
        (∑ τ : Config N,
            ∫ x : DisorderSpace (N := N),
              (WithLp.snd x).ofLp τ *
                A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x ∂μ)
          =
          ∑ τ : Config N,
            ∫ x : DisorderSpace (N := N),
              ((WithLp.ofLp x).2 τ) *
                A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x ∂μ := by
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x
      rfl
    simpa [hL] using hIBP_right
  simp [MeasureTheory.integral_const_mul, hSleft, hSright, hIBP_left_fst, hIBP_right_snd, μ]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma hasDerivAt_gibbs_average_n (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (f : ReplicaFun N n) (w : Ω) :
    HasDerivAt
        (fun s =>
          gibbs_average_n (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) n s f w)
        (dgibbs_average_n (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) n t f w) t :=
          by
  classical
  let G : EnergySpace N → ℝ := fun H' => gibbs_average_n_det (N := N) (n := n) H' f
  have hG_diff :
      DifferentiableAt ℝ G
        (H_t (N := N) G₁.U G₂.U (H_field N h) t w) := by
    simpa [G, gibbs_average_n_det] using
      (FiniteGibbs.differentiableAt_gibbs_average_n_det (α := Config N) (n := n)
        (H := H_t (N := N) G₁.U G₂.U (H_field N h) t w) (f := f))
  have hG : HasFDerivAt G (fderiv ℝ G (H_t (N := N) G₁.U G₂.U (H_field N h) t w))
        (H_t (N := N) G₁.U G₂.U (H_field N h) t w) :=
    hG_diff.hasFDerivAt
  have hHt :
      HasDerivAt
          (fun s => H_t (N := N) G₁.U G₂.U (H_field N h) s w)
          (dH_t (N := N) G₁.U G₂.U t w) t :=
    hasDerivAt_H_t (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) t ht w
  have hcomp :=
    (HasFDerivAt.comp_hasDerivAt (x := t) (f := fun s =>
        H_t (N := N) G₁.U G₂.U (H_field N h) s w)
      (l := G) (l' := fderiv ℝ G (H_t (N := N) G₁.U G₂.U (H_field N h) t w)) hG hHt)
  exact hcomp

/-! ### Dominated differentiation of `ν_t(f)` -/

theorem hasDerivAt_nu (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (f : ReplicaFun N n) :
    HasDerivAt
        (fun s => nu (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) n s f)
        (∫ w, dgibbs_average_n (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) n t f w
          ∂ℙ) t := by
  classical
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := ht.2
  have h1t0 : 0 < 1 - t := by linarith
  let ε : ℝ := (min t (1 - t)) / 2
  have hε_pos : 0 < ε := by
    have hmin : 0 < min t (1 - t) := lt_min ht0 h1t0
    have : 0 < (min t (1 - t)) / 2 := by linarith
    simpa [ε] using this
  have hball_Ioo : ∀ x ∈ Metric.ball t ε, x ∈ Ioo (0 : ℝ) 1 := by
    intro x hx
    have hx' : |x - t| < ε := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm, ε] using hx
    have hx1 : x - t < ε := (abs_sub_lt_iff.1 hx').1
    have hx2 : t - x < ε := (abs_sub_lt_iff.1 hx').2
    have hε_le_t : ε ≤ t / 2 := by
      have : min t (1 - t) ≤ t := min_le_left _ _
      have : (min t (1 - t)) / 2 ≤ t / 2 := by nlinarith
      simpa [ε] using this
    have hε_le_1t : ε ≤ (1 - t) / 2 := by
      have : min t (1 - t) ≤ (1 - t) := min_le_right _ _
      have : (min t (1 - t)) / 2 ≤ (1 - t) / 2 := by nlinarith
      simpa [ε] using this
    have hx_lower : t / 2 < x := by
      have ht_eps : t / 2 ≤ t - ε := by nlinarith [hε_le_t]
      have hx_gt : t - ε < x := by linarith
      exact lt_of_le_of_lt ht_eps hx_gt
    have hx_gt0 : 0 < x := by
      have ht_eps : t - ε ≥ t / 2 := by nlinarith [hε_le_t]
      have hx_gt : t - ε < x := by linarith
      have : t / 2 < x := lt_of_le_of_lt ht_eps hx_gt
      have : 0 < t / 2 := by nlinarith [ht0]
      exact Std.lt_trans this hx_lower-- lt_trans this this_1
    have hx_lt1 : x < 1 := by
      have hx_lt : x < t + ε := by linarith
      have ht_eps : t + ε ≤ (1 + t) / 2 := by nlinarith [hε_le_1t]
      have : x < (1 + t) / 2 := lt_of_lt_of_le hx_lt ht_eps
      have : (1 + t) / 2 < 1 := by nlinarith [ht1]
      simp; grind-- lt_trans this this_1
    exact ⟨hx_gt0, hx_lt1⟩
  let F : ℝ → Ω → ℝ :=
    fun s w =>
      gibbs_average_n (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) n s f w
  let F' : ℝ → Ω → ℝ :=
    fun s w =>
      dgibbs_average_n (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) n s f w
  have hF_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) (ℙ : Measure Ω) := by
    refine Filter.Eventually.of_forall (fun s => ?_)
    exact (integrable_gibbs_average_n (N := N) (h := h)
      (G₁ := G₁) (G₂ := G₂) (n := n) (t := s) (f := f)).aestronglyMeasurable
  have hF_int : Integrable (F t) (ℙ : Measure Ω) :=
    integrable_gibbs_average_n (N := N) (h := h)
      (G₁ := G₁) (G₂ := G₂) (n := n) (t := t) (f := f)
  let Cf : ℝ := (2 * (n : ℝ)) * (∑ σs : ReplicaSpace N n, ‖f σs‖)
  have hCf_nonneg : 0 ≤ Cf := by
    have : 0 ≤ (2 : ℝ) * (n : ℝ) := by positivity
    exact mul_nonneg this (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  let cU : ℝ := 1 / (2 * Real.sqrt (t / 2))
  let cV : ℝ := 1 / (2 * Real.sqrt ((1 - t) / 2))
  have hcU_nonneg : 0 ≤ cU := by
    have : 0 ≤ 2 * Real.sqrt (t / 2) := by positivity
    exact one_div_nonneg.2 this
  have hcV_nonneg : 0 ≤ cV := by
    have : 0 ≤ 2 * Real.sqrt ((1 - t) / 2) := by positivity
    exact one_div_nonneg.2 this
  let bound : Ω → ℝ := fun w => Cf * (cU * ‖G₁.U w‖ + cV * ‖G₂.U w‖)
  have hbound_int : Integrable bound (ℙ : Measure Ω) := by
    have hU_int : Integrable (fun w => ‖G₁.U w‖) (ℙ : Measure Ω) :=
      integrable_norm_of_isGaussian_map (P := (ℙ : Measure Ω)) (g := G₁.U) G₁.measU G₁.isGaussian
    have hV_int : Integrable (fun w => ‖G₂.U w‖) (ℙ : Measure Ω) :=
      integrable_norm_of_isGaussian_map (P := (ℙ : Measure Ω)) (g := G₂.U) G₂.measU G₂.isGaussian
    have h1 : Integrable (fun w => cU * ‖G₁.U w‖) (ℙ : Measure Ω) := (hU_int.const_mul cU)
    have h2 : Integrable (fun w => cV * ‖G₂.U w‖) (ℙ : Measure Ω) := (hV_int.const_mul cV)
    have hsum : Integrable (fun w => cU * ‖G₁.U w‖ + cV * ‖G₂.U w‖) (ℙ : Measure Ω) := h1.add h2
    simpa [bound, Cf, mul_add, mul_assoc] using hsum.const_mul Cf
  have hF'_meas : AEStronglyMeasurable (F' t) (ℙ : Measure Ω) := by
    have hU_meas : Measurable (G₁.U) := G₁.measU
    have hV_meas : Measurable (G₂.U) := G₂.measU
    have hHt_meas :
        Measurable (H_t (N := N) G₁.U G₂.U (H_field N h) t) := by
      have h1 : Measurable (fun w => (Real.sqrt t) • G₁.U w) := hU_meas.const_smul (Real.sqrt t)
      have h2 : Measurable (fun w => (Real.sqrt (1 - t)) • G₂.U w) := hV_meas.const_smul (Real.sqrt
        (1 - t))
      have h3 : Measurable (fun _w : Ω => H_field N h) := measurable_const
      exact (h1.add h2).add h3
    have hdHt_meas :
        Measurable (fun w =>
          dH_t (N := N) G₁.U G₂.U t w) := by
      have h1 : Measurable (fun w => (1 / (2 * Real.sqrt t)) • G₁.U w) :=
        hU_meas.const_smul (1 / (2 * Real.sqrt t))
      have h2 : Measurable (fun w => (1 / (2 * Real.sqrt (1 - t))) • G₂.U w) :=
        hV_meas.const_smul (1 / (2 * Real.sqrt (1 - t)))
      exact h1.fun_sub h2
    have h_gibbs_pmf_meas :
        ∀ (σ : Config N),
          Measurable fun w =>
            gibbs_pmf N
              (H_t (N := N) G₁.U G₂.U (H_field N h) t w) σ := by
      intro σ
      have hcont : Continuous fun H : EnergySpace N => gibbs_pmf N H σ :=
        (SpinGlass.contDiff_gibbs_pmf (N := N) (σ := σ)).continuous
      exact hcont.measurable.comp hHt_meas
    have hterm :
        ∀ σs : ReplicaSpace N n,
          Measurable fun w =>
            f σs *
              (∏ l : Fin n,
                gibbs_pmf N
                  (H_t (N := N) G₁.U G₂.U (H_field N h) t w) (σs l)) *
                ∑ l : Fin n,
                  ((∑ τ : Config N,
                      gibbs_pmf N
                        (H_t (N := N) G₁.U G₂.U (H_field N h) t w) τ *
                        (dH_t (N := N) G₁.U G₂.U t w) τ) -
                    (dH_t (N := N) G₁.U G₂.U t w) (σs l))
                      := by
      intro σs
      classical
      have hprod :
          Measurable fun w =>
            ∏ l : Fin n,
              gibbs_pmf N
                (H_t (N := N) G₁.U G₂.U (H_field N h) t w) (σs l) := by
        simpa using
          (Finset.measurable_prod (s := (Finset.univ : Finset (Fin n)))
            (f := fun l w =>
              gibbs_pmf N
                (H_t (N := N) G₁.U G₂.U (H_field N h) t w) (σs l))
            (hf := by
              intro l _hl
              simpa using h_gibbs_pmf_meas (σs l)))
      have h_dHt_eval : ∀ τ : Config N, Measurable fun w =>
          (dH_t (N := N) G₁.U G₂.U t w) τ := by
        intro τ
        exact (evalCLM (N := N) τ).measurable.comp hdHt_meas
      have hEv :
          Measurable fun w =>
            ∑ τ : Config N,
              gibbs_pmf N
                (H_t (N := N) G₁.U G₂.U (H_field N h) t w) τ *
                (dH_t (N := N) G₁.U G₂.U t w) τ := by
        classical
        simpa using
          (Finset.measurable_sum (s := (Finset.univ : Finset (Config N)))
            (f := fun τ w =>
              gibbs_pmf N
                (H_t (N := N) G₁.U G₂.U (H_field N h) t w) τ *
                (dH_t (N := N) G₁.U G₂.U t w) τ)
            (hf := by
              intro τ _hτ
              exact (h_gibbs_pmf_meas τ).mul (h_dHt_eval τ)))
      have hsumL :
          Measurable fun w =>
            ∑ l : Fin n,
              ((∑ τ : Config N,
                  gibbs_pmf N
                    (H_t (N := N) G₁.U G₂.U (H_field N h) t w) τ *
                    (dH_t (N := N) G₁.U G₂.U t w) τ) -
                (dH_t (N := N) G₁.U G₂.U t w) (σs l)) := by
        classical
        simpa using
          (Finset.measurable_sum (s := (Finset.univ : Finset (Fin n)))
            (f := fun l w => (∑ τ : Config N,
                  gibbs_pmf N
                    (H_t (N := N) G₁.U G₂.U (H_field N h) t w) τ *
                    (dH_t (N := N) G₁.U G₂.U t w) τ) -
                (dH_t (N := N) G₁.U G₂.U t w) (σs l))
            (hf := by
              intro l _hl
              exact hEv.sub (h_dHt_eval (σs l))))
      exact (measurable_const.mul hprod).mul hsumL
    have hderiv_meas :
        Measurable fun w =>
          (∑ σs : ReplicaSpace N n,
            f σs *
              (∏ l : Fin n,
                gibbs_pmf N
                  (H_t (N := N) G₁.U G₂.U (H_field N h) t w) (σs l)) *
                ∑ l : Fin n,
                  ((∑ τ : Config N,
                      gibbs_pmf N
                        (H_t (N := N) G₁.U G₂.U (H_field N h) t w) τ *
                        (dH_t (N := N) G₁.U G₂.U t w) τ) -
                    (dH_t (N := N) G₁.U G₂.U t w) (σs l)))
                      := by
      classical
      simpa using
        (Finset.measurable_sum (s := (Finset.univ : Finset (ReplicaSpace N n)))
          (f := fun σs w =>
            f σs *
              (∏ l : Fin n,
                gibbs_pmf N
                  (H_t (N := N) G₁.U G₂.U (H_field N h) t w) (σs l)) *
                ∑ l : Fin n,
                  ((∑ τ : Config N,
                      gibbs_pmf N
                        (H_t (N := N) G₁.U G₂.U (H_field N h) t w) τ *
                        (dH_t (N := N) G₁.U G₂.U t w) τ) -
                    (dH_t (N := N) G₁.U G₂.U t w) (σs l)))
          (hf := by intro σs _; simpa using hterm σs))
    have :
        (fun w => dgibbs_average_n (N := N) (h := h)
          (G₁ := G₁) (G₂ := G₂) n t f w)
          =
        (fun w =>
          ∑ σs : ReplicaSpace N n,
            f σs *
              (∏ l : Fin n,
                gibbs_pmf N
                  (H_t (N := N) G₁.U G₂.U (H_field N h) t w) (σs l)) *
                ∑ l : Fin n,
                  ((∑ τ : Config N,
                      gibbs_pmf N
                        (H_t (N := N) G₁.U G₂.U (H_field N h) t w) τ *
                        (dH_t (N := N) G₁.U G₂.U t w) τ) -
                    (dH_t (N := N) G₁.U G₂.U t w) (σs l)))
                      := by
      funext w
      simpa [dgibbs_average_n, gibbs_average_n_det, gibbs_pmf_eq_FiniteGibbs_gibbs_pmf] using
        (FiniteGibbs.fderiv_gibbs_average_n_det_apply (α := Config N) (n := n)
          (H := H_t (N := N) G₁.U G₂.U (H_field N h) t w)
          (v := dH_t (N := N) G₁.U G₂.U t w) (f := f))
    simpa [F', this] using hderiv_meas.aestronglyMeasurable
  have h_bound :
      ∀ᵐ w ∂(ℙ : Measure Ω), ∀ x ∈ Metric.ball t ε, ‖F' x w‖ ≤ bound w := by
    refine ae_of_all _ (fun w => ?_)
    intro x hx
    have hxIoo : x ∈ Ioo (0 : ℝ) 1 := hball_Ioo x hx
    have hL :
        ‖fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f)
            (H_t (N := N) G₁.U G₂.U (H_field N h) x w)‖ ≤ Cf := by
      simpa [Cf, gibbs_average_n_det] using
        (FiniteGibbs.norm_fderiv_gibbs_average_n_det_le (α := Config N) (n := n)
          (H := H_t (N := N) G₁.U G₂.U (H_field N h) x w) (f := f))
    have hCoeffU :
        |1 / (2 * Real.sqrt x)| ≤ cU := by
      have hx_gt0 : 0 < x := hxIoo.1
      have hx_lower : t / 2 ≤ x := by
        have hx' : |x - t| < ε := by
          simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx
        have hx2 : t - x < ε := (abs_sub_lt_iff.1 hx').2
        have hε_le_t : ε ≤ t / 2 := by
          have : min t (1 - t) ≤ t := min_le_left _ _
          have : (min t (1 - t)) / 2 ≤ t / 2 := by nlinarith
          simpa [ε] using this
        have hx_gt : t - ε < x := by linarith
        have ht_eps : t / 2 ≤ t - ε := by nlinarith [hε_le_t]
        exact le_trans ht_eps (le_of_lt hx_gt)
      have hx_ge : t / 2 ≤ x := hx_lower
      have hsqrt_le : Real.sqrt (t / 2) ≤ Real.sqrt x := Real.sqrt_le_sqrt hx_ge
      have hpos : 0 < 2 * Real.sqrt (t / 2) := by
        have : 0 < Real.sqrt (t / 2) := by
          have : 0 < t / 2 := by nlinarith [ht0]
          exact Real.sqrt_pos.2 this
        nlinarith
      have hle :
          2 * Real.sqrt (t / 2) ≤ 2 * Real.sqrt x := by nlinarith [hsqrt_le]
      have : 1 / (2 * Real.sqrt x) ≤ 1 / (2 * Real.sqrt (t / 2)) := by
        simpa [one_div] using (one_div_le_one_div_of_le hpos hle)
      have hnonneg : 0 ≤ 1 / (2 * Real.sqrt x) := by positivity
      have hnonneg' : 0 ≤ 1 / (2 * Real.sqrt (t / 2)) := by positivity
      simpa [cU, abs_of_nonneg hnonneg, abs_of_nonneg hnonneg', abs_of_nonneg (Real.sqrt_nonneg x),
        one_div]
        using this
    have hCoeffV :
        |1 / (2 * Real.sqrt (1 - x))| ≤ cV := by
      have hx_lt1 : x < 1 := hxIoo.2
      have h1x_pos : 0 < 1 - x := by linarith
      have h1x_lower : (1 - t) / 2 ≤ 1 - x := by
        have hx' : |x - t| < ε := by
          simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx
        have hx1 : x - t < ε := (abs_sub_lt_iff.1 hx').1
        have hε_le_1t : ε ≤ (1 - t) / 2 := by
          have : min t (1 - t) ≤ (1 - t) := min_le_right _ _
          have : (min t (1 - t)) / 2 ≤ (1 - t) / 2 := by nlinarith
          simpa [ε] using this
        have hx_le : x ≤ t + (1 - t) / 2 := by
          have hx_le' : x ≤ t + ε := by linarith
          exact le_trans hx_le' (by nlinarith [hε_le_1t])
        nlinarith [hx_le]
      have hsqrt_le : Real.sqrt ((1 - t) / 2) ≤ Real.sqrt (1 - x) := Real.sqrt_le_sqrt h1x_lower
      have hpos : 0 < 2 * Real.sqrt ((1 - t) / 2) := by
        have : 0 < (1 - t) / 2 := by nlinarith [h1t0]
        have : 0 < Real.sqrt ((1 - t) / 2) := Real.sqrt_pos.2 this
        nlinarith
      have hle :
          2 * Real.sqrt ((1 - t) / 2) ≤ 2 * Real.sqrt (1 - x) := by nlinarith [hsqrt_le]
      have : 1 / (2 * Real.sqrt (1 - x)) ≤ 1 / (2 * Real.sqrt ((1 - t) / 2)) := by
        simpa [one_div] using (one_div_le_one_div_of_le hpos hle)
      have hnonneg : 0 ≤ 1 / (2 * Real.sqrt (1 - x)) := by positivity
      have hnonneg' : 0 ≤ 1 / (2 * Real.sqrt ((1 - t) / 2)) := by positivity
      simpa [cV, abs_of_nonneg hnonneg, abs_of_nonneg hnonneg',
        abs_of_nonneg (Real.sqrt_nonneg (1 - x)), one_div] using this
    have hdH_norm :
        ‖dH_t (N := N) G₁.U G₂.U x w‖
          ≤ cU * ‖G₁.U w‖ + cV * ‖G₂.U w‖ := by
      have htri :
          ‖dH_t (N := N) G₁.U G₂.U x w‖
            ≤ |1 / (2 * Real.sqrt x)| * ‖G₁.U w‖ +
              |1 / (2 * Real.sqrt (1 - x))| * ‖G₂.U w‖ := by
        simpa [dH_t, sub_eq_add_neg, norm_add_le, norm_smul, abs_mul] using
          (norm_add_le ((1 / (2 * Real.sqrt x)) • G₁.U w) (-(1 / (2 * Real.sqrt (1 - x))) • G₂.U
            w))
      have : |1 / (2 * Real.sqrt x)| * ‖G₁.U w‖ +
            |1 / (2 * Real.sqrt (1 - x))| * ‖G₂.U w‖
          ≤ cU * ‖G₁.U w‖ + cV * ‖G₂.U w‖ := by
        gcongr
      exact le_trans htri this
    have hF'_bound :
        ‖F' x w‖ ≤ Cf * ‖dH_t (N := N) G₁.U G₂.U x w‖ := by
      have hop :
          ‖(fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f)
              (H_t (N := N) G₁.U G₂.U (H_field N h) x w))
              (dH_t (N := N) G₁.U G₂.U x w)‖
            ≤ ‖fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f)
                (H_t (N := N) G₁.U G₂.U (H_field N h) x w)‖ *
              ‖dH_t (N := N) G₁.U G₂.U x w‖ := by
        simpa using
          (ContinuousLinearMap.le_opNorm
            (fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f)
              (H_t (N := N) G₁.U G₂.U (H_field N h) x w))
            (dH_t (N := N) G₁.U G₂.U x w))
      have hmul :
          ‖fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f)
              (H_t (N := N) G₁.U G₂.U (H_field N h) x w)‖ *
              ‖dH_t (N := N) G₁.U G₂.U x w‖
            ≤ Cf * ‖dH_t (N := N) G₁.U G₂.U x w‖ := by
        exact mul_le_mul_of_nonneg_right hL (norm_nonneg _)
      simpa [F', dgibbs_average_n, mul_assoc] using le_trans hop hmul
    have : ‖F' x w‖ ≤ bound w := by
      have : ‖F' x w‖ ≤ Cf * (cU * ‖G₁.U w‖ + cV * ‖G₂.U w‖) := by
        exact le_trans hF'_bound (mul_le_mul_of_nonneg_left hdH_norm (hCf_nonneg))
      simpa [bound, mul_add, mul_assoc, mul_left_comm, mul_comm] using this
    exact this
  have h_diff :
      ∀ᵐ w ∂(ℙ : Measure Ω), ∀ x ∈ Metric.ball t ε,
        HasDerivAt (fun s => F s w) (F' x w) x := by
    refine ae_of_all _ (fun w => ?_)
    intro x hx
    have hxIoo : x ∈ Ioo (0 : ℝ) 1 := hball_Ioo x hx
    simpa [F, F'] using
      hasDerivAt_gibbs_average_n (N := N) (h := h)
        (G₁ := G₁) (G₂ := G₂) (n := n) (t := x) (ht := hxIoo) (f := f) w
  have hMain :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := (ℙ : Measure Ω)) (F := F) (F' := F') (x₀ := t) (bound := bound)
      (s := Metric.ball t ε) (hs := Metric.ball_mem_nhds t hε_pos)
      hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  simpa [nu, F, F'] using hMain

/-!
### Gaussian IBP of the smart-path derivative

\(\nu_t'(f) = \mathbb{E}[\mathrm{d}\langle f\rangle_t]\).
-/

theorem hasDerivAt_nu_ibp (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (f : ReplicaFun N n) :
    HasDerivAt
        (fun s => nu (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) n s f)
        ( (1 / (2 * Real.sqrt t)) *
            ∑ τ : Config N,
              ∫ x : DisorderSpace (N := N),
                (fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x)
                  (ProbabilityTheory.covarianceOperator
                    (disorderPairLaw (Ω := Ω) (N := N)
                      (G₁ := G₁) (G₂ := G₂))
                    (std_basis_left (N := N) τ))
                ∂(disorderPairLaw (Ω := Ω) (N := N)
                    (G₁ := G₁) (G₂ := G₂))
          -
          (1 / (2 * Real.sqrt (1 - t))) *
            ∑ τ : Config N,
              ∫ x : DisorderSpace (N := N),
                (fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x)
                  (ProbabilityTheory.covarianceOperator
                    (disorderPairLaw (Ω := Ω) (N := N)
                      (G₁ := G₁) (G₂ := G₂))
                    (std_basis_right (N := N) τ))
                ∂(disorderPairLaw (Ω := Ω) (N := N)
                    (G₁ := G₁) (G₂ := G₂)) ) t := by
  have hder :=
    hasDerivAt_nu (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) (n := n) t ht f
  refine hder.congr_deriv ?_
  calc
    (∫ w,
        dgibbs_average_n (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) n t f w ∂ℙ)
        =
        ∫ x : DisorderSpace (N := N),
          dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f x
            ∂(disorderPairLaw (Ω := Ω) (N := N)
              (G₁ := G₁) (G₂ := G₂)) := by
          simpa using
            (integral_dgibbs_average_n_eq_integral_disorderPairLaw
              (Ω := Ω) (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) (n := n)
              (t := t) (f := f))
    _ =
        ( (1 / (2 * Real.sqrt t)) *
            ∑ τ : Config N,
              ∫ x : DisorderSpace (N := N),
                (fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x)
                  (ProbabilityTheory.covarianceOperator
                    (disorderPairLaw (Ω := Ω) (N := N)
                      (G₁ := G₁) (G₂ := G₂))
                    (std_basis_left (N := N) τ))
                ∂(disorderPairLaw (Ω := Ω) (N := N)
                    (G₁ := G₁) (G₂ := G₂))
          -
          (1 / (2 * Real.sqrt (1 - t))) *
            ∑ τ : Config N,
              ∫ x : DisorderSpace (N := N),
                (fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x)
                  (ProbabilityTheory.covarianceOperator
                    (disorderPairLaw (Ω := Ω) (N := N)
                      (G₁ := G₁) (G₂ := G₂))
                    (std_basis_right (N := N) τ))
                ∂(disorderPairLaw (Ω := Ω) (N := N)
                    (G₁ := G₁) (G₂ := G₂)) ) := by
          simpa using
            (integral_dgibbs_average_n_disorder_eq_ibp
              (Ω := Ω) (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) (n := n)
              (hindep := hindep) (t := t) (f := f))

/-! ### Kernel form of the IBP derivative -/

-- Kernel expansion lemmas moved to `SpinGlass/SKModel.lean`.

theorem hasDerivAt_nu_kernel (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (f : ReplicaFun N n) :
    HasDerivAt
        (fun s => nu (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) n s f)
        ( (1 / (2 * Real.sqrt t)) *
            ∑ τ : Config N,
              ∫ x : DisorderSpace (N := N),
                ∑ σ : Config N,
                  K₁ τ σ *
                    (fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x)
                      (std_basis_left (N := N) σ)
                ∂(disorderPairLaw (Ω := Ω) (N := N)
                    (G₁ := G₁) (G₂ := G₂))
          -
          (1 / (2 * Real.sqrt (1 - t))) *
            ∑ τ : Config N,
              ∫ x : DisorderSpace (N := N),
                ∑ σ : Config N,
                  K₂ τ σ *
                    (fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x)
                      (std_basis_right (N := N) σ)
                ∂(disorderPairLaw (Ω := Ω) (N := N)
                    (G₁ := G₁) (G₂ := G₂)) ) t := by
  have hder := hasDerivAt_nu_ibp (Ω := Ω) (N := N) (h := h)
    (G₁ := G₁) (G₂ := G₂) (n := n) (hindep := hindep) t ht f
  refine hder.congr_deriv ?_
  simp_rw [covarianceOperator_disorderPairLaw_std_basis_left_eq_sum
    (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂) (hindep := hindep)]
  simp_rw [covarianceOperator_disorderPairLaw_std_basis_right_eq_sum
    (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂) (hindep := hindep)]
  simp [mul_assoc, mul_comm, Finset.mul_sum]
end ReplicaCalculus

end SpinGlass
