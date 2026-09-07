import SpinGlass.SKModel
import SpinGlass.GuerraBound
import SpinGlass.Calculus
import SpinGlass.ReplicaMeasure
import SpinGlass.FiniteGibbs.ReplicaCalculus
import Common.Mathlib.Probability.Distributions.Gaussian_IBP_HilbertAPI
import Common.Mathlib.Probability.Distributions.Gaussian_Interpolation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Data.Fintype.Pi
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.L1Space.Integrable

open MeasureTheory ProbabilityTheory Real BigOperators SpinGlass
open scoped ENNReal NNReal

namespace SpinGlass

/-!
# Replica calculus and the smart path

Interpolation `H_t = √t U + √(1-t) V + H_field` and Gibbs averages of functions of `n` replicas.
Talagrand Vol. I, §§1.3–1.4 (not the cavity method, §1.6).
-/

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable (N : ℕ) (h : ℝ)
variable {K₁ K₂ : Config N → Config N → ℝ}
variable (G₁ : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K₁)
variable (G₂ : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K₂)

section ReplicaCalculus

variable (n : ℕ)

/-- A generic two-replica interaction kernel `U(σ,τ)` (Talagrand’s `U_{ℓ,ℓ'}`). -/
abbrev InteractionKernel := Config N → Config N → ℝ

/-- Guerra path `H_t = √t U + √(1-t) V + H_field` with magnetization-dependent field. -/
noncomputable def H_gauss (U V : Ω → EnergySpace N) (t : ℝ) : Ω → EnergySpace N :=
  fun w =>
    (Real.sqrt t) • U w
      + (Real.sqrt (1 - t)) • V w

/-- The deterministic external-field part of the Hamiltonian, `h` times the all-ones vector. -/
noncomputable def H_field : EnergySpace N :=
  magnetic_field_vector (N := N) h

/-- Guerra's interpolating Hamiltonian at time `t`: the interpolated Gaussian part plus the
external field. -/
noncomputable def H_t (U V : Ω → EnergySpace N) (c : EnergySpace N) (t : ℝ) :
    Ω → EnergySpace N :=
  fun w => H_gauss (N := N) U V t w + c

/-! ### Gaussian integrability helpers -/

/-! ### Integrability of `‖g‖` under Gaussian law -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma integrable_norm_of_isGaussian_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → E) (hg_meas : Measurable g) (hg_gauss : ProbabilityTheory.IsGaussian (P.map g)) :
    Integrable (fun ω => ‖g ω‖) P := by
  classical
  let μ : Measure E := P.map g
  have : ProbabilityTheory.IsGaussian μ := hg_gauss
  have hIntμ : Integrable (fun x : E => ‖x‖ ^ (1 : ℕ)) μ :=
    ProbabilityTheory.IsGaussian.integrable_norm_pow (μ := μ) 1
  have hIntμ' : Integrable (fun x : E => ‖x‖) μ := by simpa using hIntμ
  have hpull :=
    (integrable_map_measure (μ := P) (f := g) (g := fun x : E => ‖x‖)
      (by fun_prop) hg_meas.aemeasurable).1 hIntμ'
  simpa [Function.comp_def] using hpull

/-- The `n`-replica Gibbs average along the interpolation, as a function of the disorder. -/
noncomputable def gibbs_average_n (t : ℝ) (f : ReplicaFun N n) : Ω → ℝ :=
  fun w =>
    let H := H_t (N := N) G₁.U G₂.U (H_field N h) t w
    gibbs_average_n_det (N := N) (n := n) H f

/-! ### Bounds for `gibbs_average_n_det` -/

lemma abs_gibbs_average_n_det_le (H : EnergySpace N) (f : ReplicaFun N n) :
    |gibbs_average_n_det (N := N) (n := n) H f| ≤ ∑ σs : ReplicaSpace N n, |f σs| := by
  simpa [gibbs_average_n_det] using
    (FiniteGibbs.abs_gibbs_average_n_det_le_sum_abs (α := Config N) (n := n) (H := H) (f := f))

/-- Expected Gibbs average: ν_t(f) = E[ ⟨f⟩_t ]. -/
noncomputable def nu (t : ℝ) (f : ReplicaFun N n) : ℝ :=
  ∫ w, gibbs_average_n (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) n t f w ∂ℙ

/-- Lift a function of `n` replicas to `n + k` replicas by ignoring the last `k`. -/
def liftReplicaFun (k : ℕ) (f : ReplicaFun N n) : ReplicaFun N (n + k) :=
  fun σs => f (fun i => σs (Fin.castAdd k i))

-- The remaining lemmas about replica measures are now in `SpinGlass/ReplicaMeasure.lean`.

/-
Uniform bound on the n-replica Gibbs average:
\[
|\langle f\rangle_{t,n}| \le \max_{\sigma^1,\dots,\sigma^n} |f(\sigma^1,\dots,\sigma^n)|.
\]
-/
omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma abs_gibbs_average_n_le (t : ℝ) (f : ReplicaFun N n) (w : Ω) :
    |gibbs_average_n (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) n t f w|
      ≤ ∑ σs : ReplicaSpace N n, |f σs| := by
  simpa [gibbs_average_n, gibbs_average_n_det] using
    (FiniteGibbs.abs_gibbs_average_n_det_le_sum_abs (α := Config N) (n := n)
      (H := H_t (N := N) G₁.U G₂.U (H_field N h) t w) (f := f))

-- From the above crude bound, integrability under the probability measure is immediate.
lemma integrable_gibbs_average_n (t : ℝ) (f : ReplicaFun N n) :
    Integrable (fun w => gibbs_average_n (N := N) (h := h) (G₁ := G₁) (G₂ := G₂)
      n t f w) := by
  classical
  have hbound :
      ∀ w, ‖gibbs_average_n (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) n t f w‖
        ≤ ∑ σs : ReplicaSpace N n, ‖f σs‖ := by
    intro w
    simpa [Real.norm_eq_abs] using
      (abs_gibbs_average_n_le (N := N) (h := h)
        (G₁ := G₁) (G₂ := G₂) (n := n) (t := t) (f := f) w)
  have hU_meas : Measurable (G₁.U) := G₁.measU
  have hV_meas : Measurable (G₂.U) := G₂.measU
  have hHt_meas :
      Measurable (H_t (N := N) G₁.U G₂.U (H_field N h) t) := by
    have h1 : Measurable (fun w => (Real.sqrt t) • G₁.U w) := hU_meas.const_smul (Real.sqrt t)
    have h2 : Measurable (fun w => (Real.sqrt (1 - t)) • G₂.U w) := hV_meas.const_smul (Real.sqrt
      (1 - t))
    have h3 : Measurable (fun _w : Ω => H_field N h) := measurable_const
    exact (h1.add h2).add h3
  have h_gibbs_pmf_meas :
      ∀ (σ : Config N),
        Measurable fun w =>
          gibbs_pmf N
            (H_t (N := N) G₁.U G₂.U (H_field N h) t w) σ := by
    intro σ
    have hEval : Measurable fun w =>
        (H_t (N := N) G₁.U G₂.U (H_field N h) t w) σ :=
      (evalCLM (N := N) σ).measurable.comp hHt_meas
    have hNum : Measurable fun w =>
        Real.exp (-
          (H_t (N := N) G₁.U G₂.U (H_field N h) t w) σ) :=
      (Real.continuous_exp.measurable.comp (measurable_neg.comp hEval))
    have hZ : Measurable fun w =>
        Z N (H_t (N := N) G₁.U G₂.U (H_field N h) t w) := by
      classical
      have hterm : ∀ τ : Config N,
          Measurable fun w =>
            Real.exp (-
              (H_t (N := N) G₁.U G₂.U (H_field N h) t w) τ) := by
        intro τ
        have hEvalτ : Measurable fun w =>
            (H_t (N := N) G₁.U G₂.U (H_field N h) t w) τ :=
          (evalCLM (N := N) τ).measurable.comp hHt_meas
        exact (Real.continuous_exp.measurable.comp (measurable_neg.comp hEvalτ))
      simpa [Z] using
        (Finset.measurable_sum (s := (Finset.univ : Finset (Config N)))
          (f := fun τ w =>
            Real.exp (-
              (H_t (N := N) G₁.U G₂.U (H_field N h) t w) τ))
          (hf := by intro τ _hτ; simpa using hterm τ))
    exact hNum.div hZ
  have hMeas :
      Measurable (fun w =>
        gibbs_average_n (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) n t f w) := by
    classical
    have hterm :
        ∀ σs : ReplicaSpace N n,
          Measurable fun w =>
            f σs * ∏ l : Fin n,
              gibbs_pmf N
                (H_t (N := N) G₁.U G₂.U (H_field N h) t w) (σs l) := by
      intro σs
      have hprod :
          Measurable fun w =>
            ∏ l : Fin n,
              gibbs_pmf N
                (H_t (N := N) G₁.U G₂.U (H_field N h) t w) (σs l) := by
        classical
        simpa using
          (Finset.measurable_prod (s := (Finset.univ : Finset (Fin n)))
            (f := fun l w =>
              gibbs_pmf N
                (H_t (N := N) G₁.U G₂.U (H_field N h) t w) (σs l))
            (hf := by
              intro l _hl
              simpa using h_gibbs_pmf_meas (σs l)))
      exact measurable_const.mul hprod
    exact
      (Finset.measurable_sum (s := (Finset.univ : Finset (ReplicaSpace N n)))
        (f := fun σs w =>
          f σs * ∏ l : Fin n,
            gibbs_pmf N
              (H_t (N := N) G₁.U G₂.U (H_field N h) t w) (σs l))
        (hf := by intro σs _hσs; simpa using hterm σs))
  have hAESM :
      AEStronglyMeasurable
        (fun w =>
          gibbs_average_n (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) n t f w) ℙ :=
    hMeas.aestronglyMeasurable
  have hBoundAE :
      ∀ᵐ w ∂ℙ, ‖gibbs_average_n (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) n t f w‖
        ≤ ∑ σs : ReplicaSpace N n, ‖f σs‖ :=
    Filter.Eventually.of_forall hbound
  exact Integrable.of_bound (μ := (ℙ : Measure Ω)) hAESM _ hBoundAE

/-- Interaction kernel `U_{l,l'} = 𝔼[u(σ^l)u(σ^{l'})] - 𝔼[v(σ^l)v(σ^{l'})]`; SK: `(β²/2)(R_{l,l'}^2
- q)`. -/
def U_interaction (U : InteractionKernel (N := N)) (l l' : Fin n) (σs : ReplicaSpace N n) : ℝ :=
  U (σs l) (σs l')

/-- The SK interaction kernel `(β²/2)(R_{στ}² - q)`, the covariance of the SK Hamiltonian
recentred at the reference overlap `q`. Talagrand Vol. I, §1.3. -/
noncomputable def U_kernel_SK (β q : ℝ) : InteractionKernel (N := N) :=
  fun σ τ =>
    let R := overlap N σ τ
    (β^2 / 2) * (R^2 - q)

/-! ### Gaussian IBP on the product disorder space -/

/-! ### Block-diagonal covariance of `disorderPairLaw` -/

-- `covarianceOperator_disorderPairLaw_std_basis_left/right` moved to `SpinGlass/SKModel.lean`.

theorem
    ProbabilityTheory.IsGaussian.integral_apply_mul_eq_integral_fderiv_covarianceOperator_left
    (μ : Measure (DisorderSpace (N := N))) [ProbabilityTheory.IsGaussian μ]
    (hmean0 : (∫ x : DisorderSpace (N := N), x ∂μ) = 0) (σ : Config N)
    (F : DisorderSpace (N := N) → ℝ) (hF_meas : Measurable F) (hF_c1 : ContDiff ℝ 1 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ x, |F x| ≤ C * (1 + ‖x‖) ^ m)
    (hF'_growth : ∀ x, ‖fderiv ℝ F x‖ ≤ C * (1 + ‖x‖) ^ m) :
    (∫ x : DisorderSpace (N := N), ((WithLp.ofLp x).1 σ) * F x ∂μ)
      = ∫ x : DisorderSpace (N := N),
          (fderiv ℝ F x) (ProbabilityTheory.covarianceOperator μ (std_basis_left (N := N) σ)) ∂μ :=
            by
  simpa [inner_apply_std_basis_left (N := N) (σ := σ)] using
    (ProbabilityTheory.IsGaussian.integral_inner_mul_eq_integral_fderiv_covarianceOperator
      (μ := μ) (hmean0 := hmean0) (h := std_basis_left (N := N) σ) (F := F)
      hF_meas hF_c1 hC hF_growth hF'_growth)

theorem
    ProbabilityTheory.IsGaussian.integral_apply_mul_eq_integral_fderiv_covarianceOperator_right
    (μ : Measure (DisorderSpace (N := N))) [ProbabilityTheory.IsGaussian μ]
    (hmean0 : (∫ x : DisorderSpace (N := N), x ∂μ) = 0) (σ : Config N)
    (F : DisorderSpace (N := N) → ℝ) (hF_meas : Measurable F) (hF_c1 : ContDiff ℝ 1 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ x, |F x| ≤ C * (1 + ‖x‖) ^ m)
    (hF'_growth : ∀ x, ‖fderiv ℝ F x‖ ≤ C * (1 + ‖x‖) ^ m) :
    (∫ x : DisorderSpace (N := N), ((WithLp.ofLp x).2 σ) * F x ∂μ)
      = ∫ x : DisorderSpace (N := N),
          (fderiv ℝ F x) (ProbabilityTheory.covarianceOperator μ (std_basis_right (N := N) σ)) ∂μ :=
            by
  simpa [inner_apply_std_basis_right (N := N) (σ := σ)] using
    (ProbabilityTheory.IsGaussian.integral_inner_mul_eq_integral_fderiv_covarianceOperator
      (μ := μ) (hmean0 := hmean0) (h := std_basis_right (N := N) σ) (F := F)
      hF_meas hF_c1 hC hF_growth hF'_growth)

/-! ### IBP on `disorderPairLaw` -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem integral_disorderPairLaw_left_apply_mul_eq
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) (σ : Config N)
    (F : DisorderSpace (N := N) → ℝ) (hF_meas : Measurable F) (hF_c1 : ContDiff ℝ 1 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ x, |F x| ≤ C * (1 + ‖x‖) ^ m)
    (hF'_growth : ∀ x, ‖fderiv ℝ F x‖ ≤ C * (1 + ‖x‖) ^ m) :
    (∫ x : DisorderSpace (N := N),
        ((WithLp.ofLp x).1 σ) * F x ∂(disorderPairLaw (Ω := Ω) (N := N)
          (G₁ := G₁) (G₂ := G₂)))
      =
      ∫ x : DisorderSpace (N := N),
        (fderiv ℝ F x)
          (ProbabilityTheory.covarianceOperator
            (disorderPairLaw (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂))
            (std_basis_left (N := N) σ))
        ∂(disorderPairLaw (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂)) :=
          by
  classical
  let μ : Measure (DisorderSpace (N := N)) :=
    disorderPairLaw (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂)
  have hgauss :
      ProbabilityTheory.IsGaussian μ :=
    isGaussian_disorderPairLaw_of_indep (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂) hindep
  have hmean0 :
      (∫ x : DisorderSpace (N := N), x ∂μ) = 0 :=
    disorderPairLaw_mean0 (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂)
  have : ProbabilityTheory.IsGaussian μ := hgauss
  simpa [μ] using
    (ProbabilityTheory.IsGaussian.integral_apply_mul_eq_integral_fderiv_covarianceOperator_left
      (N := N) (μ := μ) (hmean0 := hmean0) (σ := σ) (F := F)
      hF_meas hF_c1 hC hF_growth hF'_growth)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem integral_disorderPairLaw_right_apply_mul_eq
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U) (σ : Config N)
    (F : DisorderSpace (N := N) → ℝ) (hF_meas : Measurable F) (hF_c1 : ContDiff ℝ 1 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ x, |F x| ≤ C * (1 + ‖x‖) ^ m)
    (hF'_growth : ∀ x, ‖fderiv ℝ F x‖ ≤ C * (1 + ‖x‖) ^ m) :
    (∫ x : DisorderSpace (N := N),
        ((WithLp.ofLp x).2 σ) * F x ∂(disorderPairLaw (Ω := Ω) (N := N)
          (G₁ := G₁) (G₂ := G₂)))
      =
      ∫ x : DisorderSpace (N := N),
        (fderiv ℝ F x)
          (ProbabilityTheory.covarianceOperator
            (disorderPairLaw (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂))
            (std_basis_right (N := N) σ))
        ∂(disorderPairLaw (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂)) :=
          by
  classical
  let μ : Measure (DisorderSpace (N := N)) :=
    disorderPairLaw (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂)
  have hgauss :
      ProbabilityTheory.IsGaussian μ :=
    isGaussian_disorderPairLaw_of_indep (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂) hindep
  have hmean0 :
      (∫ x : DisorderSpace (N := N), x ∂μ) = 0 :=
    disorderPairLaw_mean0 (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂)
  have : ProbabilityTheory.IsGaussian μ := hgauss
  simpa [μ] using
    (ProbabilityTheory.IsGaussian.integral_apply_mul_eq_integral_fderiv_covarianceOperator_right
      (N := N) (μ := μ) (hmean0 := hmean0) (σ := σ) (F := F)
      hF_meas hF_c1 hC hF_growth hF'_growth)

/-! ### Derivative of the replica Gibbs average -/

/-! ### Differentiation of `ν_t(f)` (Talagrand Lemma 1.4.2) -/

open scoped Topology

open Set

/-- Derivative of the interpolated Hamiltonian `H_t` with respect to `t` (pointwise in `ω`). -/
noncomputable def dH_t (U V : Ω → EnergySpace N) (t : ℝ) (w : Ω) : EnergySpace N :=
  (1 / (2 * Real.sqrt t)) • U w - (1 / (2 * Real.sqrt (1 - t))) • V w

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma hasDerivAt_H_gauss (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (w : Ω) :
    HasDerivAt
        (fun s =>
          H_gauss (N := N) G₁.U G₂.U s w)
        (dH_t (N := N) G₁.U G₂.U t w) t := by
  have ht_ne0 : t ≠ 0 := ne_of_gt ht.1
  have h1t_ne0 : (1 - t) ≠ 0 := by
    have : t < 1 := ht.2
    linarith
  have hsqrt : HasDerivAt (fun s : ℝ => Real.sqrt s) (1 / (2 * Real.sqrt t)) t :=
    (Real.hasDerivAt_sqrt ht_ne0)
  have hsub : HasDerivAt (fun s : ℝ => (1 : ℝ) - s) (-1 : ℝ) t := by
    simpa using (HasDerivAt.const_sub (c := (1 : ℝ)) (hasDerivAt_id t))
  have hsqrt_sub :
      HasDerivAt (fun s : ℝ => Real.sqrt ((1 : ℝ) - s))
        ((1 / (2 * Real.sqrt (1 - t))) * (-1 : ℝ)) t := by
    exact (Real.hasDerivAt_sqrt h1t_ne0).comp t hsub
  have hU :
      HasDerivAt (fun s : ℝ => (Real.sqrt s) • G₁.U w)
        ((1 / (2 * Real.sqrt t)) • G₁.U w) t :=
    hsqrt.smul_const (G₁.U w)
  have hV :
      HasDerivAt (fun s : ℝ => (Real.sqrt ((1 : ℝ) - s)) • G₂.U w)
        (((1 / (2 * Real.sqrt (1 - t))) * (-1 : ℝ)) • G₂.U w) t :=
    hsqrt_sub.smul_const (G₂.U w)
  refine (hU.add hV).congr_deriv ?_
  simp [dH_t, sub_eq_add_neg]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma hasDerivAt_H_t (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (w : Ω) :
    HasDerivAt
        (fun s =>
          H_t (N := N) G₁.U G₂.U (H_field N h) s w)
        (dH_t (N := N) G₁.U G₂.U t w) t := by
  simpa [H_t, dH_t, H_field]
    using (hasDerivAt_H_gauss (N := N) (G₁ := G₁) (G₂ := G₂) t ht
      w).add_const

/-! ### Local bound on `dH_t` -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma norm_dH_t_le_on_ball
    (t x : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Metric.ball t ((min t (1 - t)) / 2)) (w : Ω) :
    let cU : ℝ := 1 / (2 * Real.sqrt (t / 2))
    let cV : ℝ := 1 / (2 * Real.sqrt ((1 - t) / 2))
    ‖dH_t (N := N) G₁.U G₂.U x w‖
      ≤ cU * ‖G₁.U w‖ + cV * ‖G₂.U w‖ := by
  classical
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := ht.2
  have h1t0 : 0 < 1 - t := by linarith
  let ε : ℝ := (min t (1 - t)) / 2
  have hx' : |x - t| < ε := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm, ε] using hx
  have hx_pos : 0 < x := by
    have hε_le_t : ε ≤ t / 2 := by
      have : min t (1 - t) ≤ t := min_le_left _ _
      have : (min t (1 - t)) / 2 ≤ t / 2 := by nlinarith
      simpa [ε] using this
    have hx_lower : t - ε < x := by linarith [(abs_sub_lt_iff.1 hx').2]
    have : 0 < t - ε := by nlinarith [ht0, hε_le_t]
    exact lt_trans this hx_lower
  have h1x_pos : 0 < 1 - x := by
    have hε_le_1t : ε ≤ (1 - t) / 2 := by
      have : min t (1 - t) ≤ (1 - t) := min_le_right _ _
      have : (min t (1 - t)) / 2 ≤ (1 - t) / 2 := by nlinarith
      simpa [ε] using this
    have hx_upper : x < t + ε := by linarith [(abs_sub_lt_iff.1 hx').1]
    have : t + ε < 1 := by nlinarith [ht1, hε_le_1t]
    exact sub_pos.2 (lt_trans hx_upper this)
  have hx_lower : t / 2 ≤ x := by
    have hx_lower' : t - ε ≤ x := by
      have hx_lower_lt : t - ε < x := by linarith [(abs_sub_lt_iff.1 hx').2]
      exact le_of_lt hx_lower_lt
    have hε_le_t : ε ≤ t / 2 := by
      have : min t (1 - t) ≤ t := min_le_left _ _
      have : (min t (1 - t)) / 2 ≤ t / 2 := by nlinarith
      simpa [ε] using this
    nlinarith [hx_lower', hε_le_t]
  have h1x_lower : (1 - t) / 2 ≤ 1 - x := by
    have hx_upper' : x ≤ t + ε := by
      have hx_upper_lt : x < t + ε := by linarith [(abs_sub_lt_iff.1 hx').1]
      exact le_of_lt hx_upper_lt
    have hε_le_1t : ε ≤ (1 - t) / 2 := by
      have : min t (1 - t) ≤ (1 - t) := min_le_right _ _
      have : (min t (1 - t)) / 2 ≤ (1 - t) / 2 := by nlinarith
      simpa [ε] using this
    nlinarith [hx_upper', hε_le_1t]
  -- coefficient bounds
  have hcoefU :
      |1 / (2 * Real.sqrt x)| ≤ |1 / (2 * Real.sqrt (t / 2))| := by
    have hsqrt_le : Real.sqrt (t / 2) ≤ Real.sqrt x := Real.sqrt_le_sqrt hx_lower
    have hpos : 0 < 2 * Real.sqrt (t / 2) := by
      have : 0 < t / 2 := by nlinarith [ht0]
      have : 0 < Real.sqrt (t / 2) := Real.sqrt_pos.2 this
      nlinarith
    have hle : 2 * Real.sqrt (t / 2) ≤ 2 * Real.sqrt x := by nlinarith [hsqrt_le]
    have : 1 / (2 * Real.sqrt x) ≤ 1 / (2 * Real.sqrt (t / 2)) := by
      simpa [one_div] using (one_div_le_one_div_of_le hpos hle)
    have hnonneg : 0 ≤ 1 / (2 * Real.sqrt x) := by positivity
    have hnonneg' : 0 ≤ 1 / (2 * Real.sqrt (t / 2)) := by positivity
    -- avoid aggressive simplification of `sqrt (t/2)` into `sqrt2 / sqrt t`
    calc
      |1 / (2 * Real.sqrt x)| = 1 / (2 * Real.sqrt x) := abs_of_nonneg hnonneg
      _ ≤ 1 / (2 * Real.sqrt (t / 2)) := this
      _ = |1 / (2 * Real.sqrt (t / 2))| := (abs_of_nonneg hnonneg').symm
  have hcoefV :
      |1 / (2 * Real.sqrt (1 - x))| ≤ |1 / (2 * Real.sqrt ((1 - t) / 2))| := by
    have hsqrt_le : Real.sqrt ((1 - t) / 2) ≤ Real.sqrt (1 - x) := Real.sqrt_le_sqrt h1x_lower
    have hpos : 0 < 2 * Real.sqrt ((1 - t) / 2) := by
      have : 0 < (1 - t) / 2 := by nlinarith [h1t0]
      have : 0 < Real.sqrt ((1 - t) / 2) := Real.sqrt_pos.2 this
      nlinarith
    have hle : 2 * Real.sqrt ((1 - t) / 2) ≤ 2 * Real.sqrt (1 - x) := by nlinarith [hsqrt_le]
    have : 1 / (2 * Real.sqrt (1 - x)) ≤ 1 / (2 * Real.sqrt ((1 - t) / 2)) := by
      simpa [one_div] using (one_div_le_one_div_of_le hpos hle)
    have hnonneg : 0 ≤ 1 / (2 * Real.sqrt (1 - x)) := by positivity
    have hnonneg' : 0 ≤ 1 / (2 * Real.sqrt ((1 - t) / 2)) := by positivity
    calc
      |1 / (2 * Real.sqrt (1 - x))| = 1 / (2 * Real.sqrt (1 - x)) := abs_of_nonneg hnonneg
      _ ≤ 1 / (2 * Real.sqrt ((1 - t) / 2)) := this
      _ = |1 / (2 * Real.sqrt ((1 - t) / 2))| := (abs_of_nonneg hnonneg').symm
  -- triangle inequality + coefficient comparison
  have htri :
      ‖dH_t (N := N) G₁.U G₂.U x w‖
        ≤ |1 / (2 * Real.sqrt x)| * ‖G₁.U w‖ +
          |1 / (2 * Real.sqrt (1 - x))| * ‖G₂.U w‖ := by
    simpa [dH_t, sub_eq_add_neg, norm_add_le, norm_smul, abs_mul] using
      (norm_add_le ((1 / (2 * Real.sqrt x)) • G₁.U w) (-(1 / (2 * Real.sqrt (1 - x))) • G₂.U w))
  -- conclude with `gcongr` (monotonicity in coefficients)
  dsimp
  have hcu_nonneg : 0 ≤ 1 / (2 * Real.sqrt (t / 2)) := by positivity
  have hcv_nonneg : 0 ≤ 1 / (2 * Real.sqrt ((1 - t) / 2)) := by positivity
  have habsU_le : |1 / (2 * Real.sqrt (t / 2))| ≤ (1 / (2 * Real.sqrt (t / 2))) :=
    le_of_eq (abs_of_nonneg hcu_nonneg)
  have habsV_le : |1 / (2 * Real.sqrt ((1 - t) / 2))| ≤ (1 / (2 * Real.sqrt ((1 - t) / 2))) :=
    le_of_eq (abs_of_nonneg hcv_nonneg)
  have hcoefU' : |1 / (2 * Real.sqrt x)| ≤ (1 / (2 * Real.sqrt (t / 2))) :=
    le_trans hcoefU habsU_le
  have hcoefV' : |1 / (2 * Real.sqrt (1 - x))| ≤ (1 / (2 * Real.sqrt ((1 - t) / 2))) :=
    le_trans hcoefV habsV_le
  have hcmp :
      |1 / (2 * Real.sqrt x)| * ‖G₁.U w‖ +
        |1 / (2 * Real.sqrt (1 - x))| * ‖G₂.U w‖
        ≤ (1 / (2 * Real.sqrt (t / 2))) * ‖G₁.U w‖ +
            (1 / (2 * Real.sqrt ((1 - t) / 2))) * ‖G₂.U w‖ := by
    have hUterm :
        |1 / (2 * Real.sqrt x)| * ‖G₁.U w‖ ≤ (1 / (2 * Real.sqrt (t / 2))) * ‖G₁.U w‖ :=
      mul_le_mul_of_nonneg_right hcoefU' (norm_nonneg _)
    have hVterm :
        |1 / (2 * Real.sqrt (1 - x))| * ‖G₂.U w‖
          ≤ (1 / (2 * Real.sqrt ((1 - t) / 2))) * ‖G₂.U w‖ :=
      mul_le_mul_of_nonneg_right hcoefV' (norm_nonneg _)
    exact add_le_add hUterm hVterm
  exact le_trans htri hcmp

/-- Pointwise derivative of the `n`-replica Gibbs average along the path `H_t`. -/
noncomputable def dgibbs_average_n (t : ℝ) (f : ReplicaFun N n) (w : Ω) : ℝ :=
  fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f)
    (H_t (N := N) G₁.U G₂.U (H_field N h) t w)
    (dH_t (N := N) G₁.U G₂.U t w)

/-! ### Interpolated Hamiltonian on `DisorderSpace` -/

/-! ### Fréchet derivative of `H_t_disorder` -/


/-- Guerra's interpolating Hamiltonian at time `t`, as a function of the disorder pair:
the Gaussian interpolation `√t U + √(1-t) V` of the two disorders, plus the external field. -/
noncomputable def H_t_disorder (c : EnergySpace N) (t : ℝ) (x : DisorderSpace (N := N)) :
    EnergySpace N :=
  gaussianInterp (E := EnergySpace N) t x + c

lemma hasFDerivAt_H_t_disorder (t : ℝ) (x : DisorderSpace (N := N)) :
    HasFDerivAt (H_t_disorder N (H_field N h) t) (gaussianInterp (E := EnergySpace N) t) x := by
  -- `H_t_disorder = (linear part) + const`, so the derivative is the linear part.
  have hderiv := (gaussianInterp (E := EnergySpace N) t).hasFDerivAt.add
    (hasFDerivAt_const (H_field N h) x)
  rwa [add_zero] at hderiv

lemma norm_fderiv_gibbs_pmf_disorder_le (t : ℝ) (σ : Config N) (x : DisorderSpace (N := N)) :
    ‖fderiv ℝ (fun x : DisorderSpace (N := N) =>
        gibbs_pmf N (H_t_disorder N (H_field N h) t x) σ) x‖
      ≤ 2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|) := by
  classical
  have hdiff :
      DifferentiableAt ℝ (fun H' : EnergySpace N => gibbs_pmf N H' σ)
        (H_t_disorder N (H_field N h) t x) :=
    SpinGlass.differentiableAt_gibbs_pmf (N := N) (H := H_t_disorder N (H_field N h) t x) σ
  have h1 :
      HasFDerivAt (fun H' : EnergySpace N => gibbs_pmf N H' σ)
        (fderiv ℝ (fun H' : EnergySpace N => gibbs_pmf N H' σ)
          (H_t_disorder N (H_field N h) t x))
        (H_t_disorder N (H_field N h) t x) :=
    hdiff.hasFDerivAt
  have hHx :
      HasFDerivAt (fun x : DisorderSpace (N := N) =>
          gibbs_pmf N (H_t_disorder N (H_field N h) t x) σ)
        ((fderiv ℝ (fun H' : EnergySpace N => gibbs_pmf N H' σ)
            (H_t_disorder N (H_field N h) t x)).comp
              (gaussianInterp (E := EnergySpace N) t)) x := by
    simpa [Function.comp_def] using h1.comp x (hasFDerivAt_H_t_disorder (N := N) (h := h) t x)
  have hfderiv :
      fderiv ℝ (fun x : DisorderSpace (N := N) =>
          gibbs_pmf N (H_t_disorder N (H_field N h) t x) σ) x
        =
        ((fderiv ℝ (fun H' : EnergySpace N => gibbs_pmf N H' σ)
            (H_t_disorder N (H_field N h) t x)).comp
              (gaussianInterp (E := EnergySpace N) t)) := by
    simpa using hHx.fderiv
  have hσ :
      ‖fderiv ℝ (fun H' : EnergySpace N => gibbs_pmf N H' σ)
            (H_t_disorder N (H_field N h) t x)‖ ≤ 2 :=
    by
      simpa [gibbs_pmf_eq_FiniteGibbs_gibbs_pmf] using
        (FiniteGibbs.norm_fderiv_gibbs_pmf_le_two (α := Config N)
          (H := H_t_disorder N (H_field N h) t x) (σ := σ))
  have ht : ‖gaussianInterp (E := EnergySpace N) t‖ ≤ |Real.sqrt t| + |Real.sqrt (1 - t)| :=
    opNorm_gaussianInterp_le (E := EnergySpace N) t
  calc
    ‖fderiv ℝ (fun x : DisorderSpace (N := N) =>
          gibbs_pmf N (H_t_disorder N (H_field N h) t x) σ) x‖
        = ‖((fderiv ℝ (fun H' : EnergySpace N => gibbs_pmf N H' σ)
              (H_t_disorder N (H_field N h) t x)).comp
                (gaussianInterp (E := EnergySpace N) t))‖ := by
            simp [hfderiv]
    _ ≤ ‖fderiv ℝ (fun H' : EnergySpace N => gibbs_pmf N H' σ)
            (H_t_disorder N (H_field N h) t x)‖ * ‖gaussianInterp (E := EnergySpace N) t‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|) := by
          have hA :
              ‖fderiv ℝ (fun H' : EnergySpace N => gibbs_pmf N H' σ)
                (H_t_disorder N (H_field N h) t x)‖ * ‖gaussianInterp (E := EnergySpace N) t‖
                ≤ 2 * ‖gaussianInterp (E := EnergySpace N) t‖ := by
            gcongr
          have hB : 2 * ‖gaussianInterp (E := EnergySpace N) t‖
              ≤ 2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|) :=
            by
            gcongr
          exact le_trans (le_trans (by rfl) hA) hB

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
@[simp] lemma H_t_disorder_disorderPair (t : ℝ) (w : Ω) :
    H_t_disorder N (H_field N h) t
        (disorderPair (N := N) (G₁ := G₁) (G₂ := G₂) w)
      =
      H_t (N := N) G₁.U G₂.U (H_field N h) t w := by
  simp [H_t_disorder, gaussianInterp, H_t, H_gauss, H_field, disorderPair]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
@[simp] lemma gaussianInterpDeriv_disorderPair (t : ℝ) (w : Ω) :
    gaussianInterpDeriv (E := EnergySpace N) t
        (disorderPair (N := N) (G₁ := G₁) (G₂ := G₂) w)
      =
      dH_t (N := N) G₁.U G₂.U t w := by
  simp [gaussianInterpDeriv, dH_t, disorderPair]

/-- The `n`-replica Gibbs average along the interpolation, as a function on the disorder
space. -/
noncomputable def gibbs_average_n_disorder (t : ℝ) (f : ReplicaFun N n) :
    DisorderSpace (N := N) → ℝ :=
  fun x =>
    gibbs_average_n_det (N := N) (n := n)
      (H_t_disorder N (H_field N h) t x) f

/-- The time derivative of `gibbs_average_n_disorder`, as a function on the disorder space. -/
noncomputable def dgibbs_average_n_disorder (t : ℝ) (f : ReplicaFun N n) :
    DisorderSpace (N := N) → ℝ :=
  fun x =>
    fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f)
      (H_t_disorder N (H_field N h) t x)
      (gaussianInterpDeriv (E := EnergySpace N) t x)

/-! ### Reshaping `dgibbs_average_n_disorder` -/

/-- The Gibbs weight of `σ` under the interpolating Hamiltonian, as a function of the disorder. -/
noncomputable def gibbs_pmf_disorder (t : ℝ) (σ : Config N) : DisorderSpace (N := N) → ℝ :=
  fun x => gibbs_pmf N (H_t_disorder N (H_field N h) t x) σ

lemma contDiff_gibbs_pmf_disorder (t : ℝ) (σ : Config N) :
    ContDiff ℝ 1 (gibbs_pmf_disorder (N := N) (h := h) t σ) := by
  let nTop : WithTop ℕ∞ := (↑(⊤ : ℕ∞))
  have hlin_inf : ContDiff ℝ nTop (gaussianInterp (E := EnergySpace N) t) := by
    simpa [nTop] using (gaussianInterp (E := EnergySpace N) t).contDiff (n := nTop)
  have hlin : ContDiff ℝ 1 (gaussianInterp (E := EnergySpace N) t) :=
    hlin_inf.of_le (by simp [nTop])
  have hconst : ContDiff ℝ 1 (fun _ : DisorderSpace (N := N) => H_field N h) :=
    contDiff_const
  have hH : ContDiff ℝ 1 (H_t_disorder N (H_field N h) t) := by
    exact hlin.add hconst
  have hg_inf : ContDiff ℝ nTop (fun H : EnergySpace N => gibbs_pmf N H σ) := by
    simpa [nTop] using (SpinGlass.contDiff_gibbs_pmf (N := N) σ)
  have hg : ContDiff ℝ 1 (fun H : EnergySpace N => gibbs_pmf N H σ) :=
    hg_inf.of_le (by simp [nTop])
  exact hg.comp hH

/-- The product of Gibbs weights over the replicas, as a function on the disorder space. -/
noncomputable def prod_gibbs_pmf_disorder (t : ℝ) (σs : ReplicaSpace N n) :
    DisorderSpace (N := N) → ℝ :=
  fun x => ∏ l : Fin n, gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := σs l) x

lemma contDiff_prod_gibbs_pmf_disorder (t : ℝ) (σs : ReplicaSpace N n) :
    ContDiff ℝ 1 (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) t σs) := by
  classical
  exact
    (contDiff_prod (𝕜 := ℝ) (n := (1 : ℕ))
      (t := (Finset.univ : Finset (Fin n)))
      (f := fun l : Fin n => fun x : DisorderSpace (N := N) =>
        gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := σs l) x)
      (h := fun l _hl =>
        contDiff_gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := σs l)))

lemma norm_fderiv_prod_gibbs_pmf_disorder_le (t : ℝ) (σs : ReplicaSpace N n) (x : DisorderSpace (N
    := N)) :
    ‖fderiv ℝ (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) t σs) x‖
      ≤ (n : ℝ) * (2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|)) := by
  classical
  let F : EnergySpace N → ℝ := fun H => ∏ l : Fin n, gibbs_pmf N H (σs l)
  have hF_diff :
      DifferentiableAt ℝ F (H_t_disorder N (H_field N h) t x) := by
    simpa [F, gibbs_pmf_eq_FiniteGibbs_gibbs_pmf] using
      (FiniteGibbs.differentiableAt_prod_gibbs_pmf (α := Config N) (n := n)
        (H := H_t_disorder N (H_field N h) t x) (σs := σs))
  have hF :
      HasFDerivAt F (fderiv ℝ F (H_t_disorder N (H_field N h) t x))
        (H_t_disorder N (H_field N h) t x) :=
    hF_diff.hasFDerivAt
  have hcomp :
      HasFDerivAt (fun x : DisorderSpace (N := N) => F (H_t_disorder N (H_field N h) t x))
        ((fderiv ℝ F (H_t_disorder N (H_field N h) t x)).comp
          (gaussianInterp (E := EnergySpace N) t)) x :=
          by
    simpa [Function.comp_def] using hF.comp x (hasFDerivAt_H_t_disorder (N := N) (h := h) t x)
  have hfderiv :
      fderiv ℝ (fun x : DisorderSpace (N := N) => F (H_t_disorder N (H_field N h) t x)) x
        =
        (fderiv ℝ F (H_t_disorder N (H_field N h) t x)).comp
          (gaussianInterp (E := EnergySpace N) t) := by
    simpa using hcomp.fderiv
  have hF_norm :
      ‖fderiv ℝ F (H_t_disorder N (H_field N h) t x)‖ ≤ 2 * (n : ℝ) := by
    simpa [F, gibbs_pmf_eq_FiniteGibbs_gibbs_pmf] using
      (FiniteGibbs.norm_fderiv_prod_gibbs_pmf_le (α := Config N) (n := n)
        (H := H_t_disorder N (H_field N h) t x) (σs := σs))
  have hH_norm : ‖gaussianInterp (E := EnergySpace N) t‖ ≤ |Real.sqrt t| + |Real.sqrt (1 - t)| :=
    opNorm_gaussianInterp_le (E := EnergySpace N) t
  have hrew :
      prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) t σs
        = fun x : DisorderSpace (N := N) => F (H_t_disorder N (H_field N h) t x) := by
    funext x
    simp [prod_gibbs_pmf_disorder, gibbs_pmf_disorder, F]
  have hcomp_norm :
      ‖(fderiv ℝ F (H_t_disorder N (H_field N h) t x)).comp
          (gaussianInterp (E := EnergySpace N) t)‖
        ≤ ‖fderiv ℝ F (H_t_disorder N (H_field N h) t x)‖
            * ‖gaussianInterp (E := EnergySpace N) t‖ :=
    ContinuousLinearMap.opNorm_comp_le _ (gaussianInterp (E := EnergySpace N) t)
  calc
    ‖fderiv ℝ (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) t σs) x‖
        = ‖fderiv ℝ (fun x : DisorderSpace (N := N) => F (H_t_disorder N (H_field N h) t x)) x‖ :=
          by
            simp [hrew]
    _ = ‖(fderiv ℝ F (H_t_disorder N (H_field N h) t x)).comp
            (gaussianInterp (E := EnergySpace N) t)‖ := by
            simp [hfderiv]
    _ ≤ ‖fderiv ℝ F (H_t_disorder N (H_field N h) t x)‖
          * ‖gaussianInterp (E := EnergySpace N) t‖ :=
      hcomp_norm
    _ ≤ (2 * (n : ℝ)) * (|Real.sqrt t| + |Real.sqrt (1 - t)|) := by
            gcongr
    _ = (n : ℝ) * (2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|)) := by ring
end ReplicaCalculus

end SpinGlass
