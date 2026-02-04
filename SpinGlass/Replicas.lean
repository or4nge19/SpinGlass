import SpinGlass.SKModel
import SpinGlass.GuerraBound
import SpinGlass.Calculus
import SpinGlass.ReplicaMeasure
import Common.Mathlib.Probability.Distributions.Gaussian_IBP_HilbertAPI
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Data.Fintype.Pi
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.L1Space.Integrable

open MeasureTheory ProbabilityTheory Real BigOperators SpinGlass SpinGlass.Algebra
open scoped ENNReal NNReal

namespace SpinGlass

/-!
# Section 1.4: General Replica Calculus and Latala's Argument

To prove concentration, we must manage functions of `n` replicas.
Differentiation increases the number of replicas by 2.

**Terminology:** this file implements the **interpolation / smart path** method
(Talagrand Vol. I, §§1.3–1.4). It is *not* the cavity method (Talagrand Vol. I, §1.6),
which is an induction on `N`.
-/

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable (N : ℕ) (β h q : ℝ)
variable (sk : SKDisorder (Ω := Ω) N β h) (sim : SimpleDisorder (Ω := Ω) N β q)

section ReplicaCalculus

variable (n : ℕ)

/-- A generic two-replica interaction kernel `U(σ,τ)` (Talagrand’s `U_{ℓ,ℓ'}`). -/
abbrev InteractionKernel := Config N → Config N → ℝ

/--
Interpolated Hamiltonian (Guerra):
\[
H_t = \sqrt{t}\,U + \sqrt{1-t}\,V + H_{\text{field}}.
\]

The external field term uses the **magnetization-dependent** energy
`magnetic_field_vector` (not a constant shift).
-/
noncomputable def H_gauss (t : ℝ) : Ω → EnergySpace N :=
  fun w =>
    (Real.sqrt t) • sk.U w
      + (Real.sqrt (1 - t)) • sim.V w

noncomputable def H_field : EnergySpace N :=
  magnetic_field_vector (N := N) h

noncomputable def H_t (t : ℝ) : Ω → EnergySpace N :=
  fun w =>
    H_gauss (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w
      + H_field (N := N) (h := h)

/-!
### Gaussian integrability helpers (intrinsic)

We avoid the coordinate-based `IsGaussianHilbert` structure. Instead we work with the intrinsic
law-based predicate `IsGaussian ((ℙ).map g)`. Basic integrability properties are obtained by
pulling back integrability on the law along the map measure.
-/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma integrable_norm_of_isGaussian_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → E) (hg_meas : Measurable g) (hg_gauss : ProbabilityTheory.IsGaussian (P.map g)) :
    Integrable (fun ω => ‖g ω‖) P := by
  classical
  let μ : Measure E := P.map g
  haveI : ProbabilityTheory.IsGaussian μ := hg_gauss
  have hIntμ : Integrable (fun x : E => ‖x‖ ^ (1 : ℕ)) μ :=
    ProbabilityTheory.IsGaussian.integrable_norm_pow (μ := μ) 1
  have hIntμ' : Integrable (fun x : E => ‖x‖) μ := by simpa using hIntμ
  have hpull :=
    (integrable_map_measure (μ := P) (f := g) (g := fun x : E => ‖x‖)
      (by fun_prop) hg_meas.aemeasurable).1 hIntμ'
  simpa [Function.comp] using hpull

noncomputable def gibbs_average_n (t : ℝ) (f : ReplicaFun N n) : Ω → ℝ :=
  fun w =>
    let H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w
    gibbs_average_n_det (N := N) (n := n) H f

/-!
### Basic bounds for `gibbs_average_n_det`

These are used both for integrability and for “moderate growth” hypotheses in Gaussian IBP.
-/

lemma abs_gibbs_average_n_det_le (H : EnergySpace N) (f : ReplicaFun N n) :
    |gibbs_average_n_det (N := N) (n := n) H f| ≤ ∑ σs : ReplicaSpace N n, |f σs| := by
  classical
  have hnonneg :
      ∀ σs : ReplicaSpace N n, 0 ≤ ∏ l, gibbs_pmf N H (σs l) :=
    fun σs => by
      classical
      refine Finset.prod_nonneg ?_
      intro l _hl
      exact SpinGlass.gibbs_pmf_nonneg (N := N) (H := H) (σ := σs l)
  have hprod_le_one :
      ∀ σs : ReplicaSpace N n, (∏ l, gibbs_pmf N H (σs l)) ≤ (1 : ℝ) :=
    fun σs => by
      classical
      have hfac : ∀ l : Fin n, gibbs_pmf N H (σs l) ≤ 1 := by
        intro l
        have hZpos : 0 < Z N H := SpinGlass.Z_pos (N := N) (H := H)
        have hterm_le : Real.exp (-H (σs l)) ≤ Z N H := by
          have :=
            Finset.single_le_sum
              (s := (Finset.univ : Finset (Config N)))
              (f := fun τ => Real.exp (-H τ))
              (hf := fun τ _hτ => (Real.exp_pos _).le)
              (a := σs l) (h := Finset.mem_univ (σs l))
          simpa [Z] using this
        have := (div_le_one hZpos).2 hterm_le
        simpa [SpinGlass.gibbs_pmf] using this
      simpa using
        (Finset.prod_le_one (s := (Finset.univ : Finset (Fin n)))
          (f := fun l => gibbs_pmf N H (σs l))
          (fun l _hl => SpinGlass.gibbs_pmf_nonneg (N := N) (H := H) (σ := σs l))
          (fun l _hl => hfac l))
  calc
    |gibbs_average_n_det (N := N) (n := n) H f|
        = |∑ σs : ReplicaSpace N n, f σs * ∏ l, gibbs_pmf N H (σs l)| := by
            rfl
    _ ≤ ∑ σs : ReplicaSpace N n, |f σs * ∏ l, gibbs_pmf N H (σs l)| := by
          simpa using
            (Finset.abs_sum_le_sum_abs
              (f := fun σs : ReplicaSpace N n => f σs * ∏ l, gibbs_pmf N H (σs l))
              (s := (Finset.univ : Finset (ReplicaSpace N n))))
    _ = ∑ σs : ReplicaSpace N n, (|f σs| * |∏ l, gibbs_pmf N H (σs l)|) := by
          refine Finset.sum_congr rfl (fun σs _hσs => ?_)
          simp [abs_mul]
    _ ≤ ∑ σs : ReplicaSpace N n, |f σs| := by
          refine Finset.sum_le_sum ?_
          intro σs _hσs
          have habs :
              |∏ l, gibbs_pmf N H (σs l)| = ∏ l, gibbs_pmf N H (σs l) := by
            have h0 : 0 ≤ ∏ l, gibbs_pmf N H (σs l) := hnonneg σs
            simp [abs_of_nonneg h0]
          have hle1 : |∏ l, gibbs_pmf N H (σs l)| ≤ 1 := by
            simpa [habs] using hprod_le_one σs
          simpa using (mul_le_mul_of_nonneg_left hle1 (abs_nonneg (f σs)))

/-- Expected Gibbs average: ν_t(f) = E[ ⟨f⟩_t ]. -/
noncomputable def nu (t : ℝ) (f : ReplicaFun N n) : ℝ :=
  ∫ w, gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w ∂ℙ

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
    |gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w|
      ≤ ∑ σs : ReplicaSpace N n, |f σs| := by
  classical
  have hnonneg :
      ∀ σs : ReplicaSpace N n,
        0 ≤ ∏ l, gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) :=
    fun σs => by
      classical
      have : ∀ l : Fin n,
          0 ≤ gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) :=
        fun l => SpinGlass.gibbs_pmf_nonneg (N := N) (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σ := σs l)
      simpa using Finset.prod_nonneg (fun l _hl => this l)
  calc
    |gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w|
        = |∑ σs : ReplicaSpace N n,
            f σs * ∏ l,
              gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)| := by
            rfl
    _ ≤ ∑ σs : ReplicaSpace N n,
          |f σs * ∏ l,
              gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)| := by
          classical
          simpa using
            (Finset.abs_sum_le_sum_abs
              (f := fun σs : ReplicaSpace N n =>
                f σs * ∏ l, gibbs_pmf N
                  (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))
              (s := (Finset.univ : Finset (ReplicaSpace N n))))
    _ = ∑ σs : ReplicaSpace N n,
          (|f σs| * |∏ l,
              gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)|) := by
          refine Finset.sum_congr rfl ?_
          intro σs _hσs
          simp [abs_mul]
    _ ≤ ∑ σs : ReplicaSpace N n, |f σs| := by
          classical
          simpa using
            (Finset.sum_le_sum (s := (Finset.univ : Finset (ReplicaSpace N n))) (fun σs _hσs => by
              have hle1 : |∏ l,
                  gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)| ≤ 1 := by
                have hfac : ∀ l : Fin n,
                    gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) ≤ 1 := by
                  intro l
                  have hZpos :
                      0 < Z N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) :=
                    SpinGlass.Z_pos (N := N)
                      (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
                  have hterm_le :
                      Real.exp (-(H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))
                        ≤ Z N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) := by
                    classical
                    have :=
                      Finset.single_le_sum
                        (s := (Finset.univ : Finset (Config N)))
                        (f := fun τ =>
                          Real.exp (-(H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ))
                        (hf := fun τ _hτ => (Real.exp_pos _).le)
                        (a := (σs l)) (h := Finset.mem_univ (σs l))
                    simpa [Z] using this
                  have := (div_le_one hZpos).2 hterm_le
                  simpa [SpinGlass.gibbs_pmf] using this
                have habs :
                    |∏ l,
                        gibbs_pmf N
                          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)|
                      =
                    ∏ l,
                        gibbs_pmf N
                          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) := by
                  have hnonneg' : 0 ≤ ∏ l,
                      gibbs_pmf N
                        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) :=
                    hnonneg σs
                  simp [abs_of_nonneg hnonneg']
                have hprod :
                    ∏ l,
                        gibbs_pmf N
                          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)
                      ≤ (1 : ℝ) := by
                  classical
                  simpa using
                    (Finset.prod_le_one (s := (Finset.univ : Finset (Fin n)))
                      (f := fun l =>
                        gibbs_pmf N
                          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))
                      (fun l _hl => SpinGlass.gibbs_pmf_nonneg (N := N)
                        (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
                        (σ := σs l))
                      (fun l _hl => hfac l))
                simpa [habs] using hprod
              have : |f σs| * |∏ l,
                  gibbs_pmf N
                    (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)|
                    ≤ |f σs| := by
                simpa using (mul_le_mul_of_nonneg_left hle1 (abs_nonneg (f σs)))
              simpa [mul_assoc] using this))

-- From the above crude bound, integrability under the probability measure is immediate.
lemma integrable_gibbs_average_n (t : ℝ) (f : ReplicaFun N n) :
    Integrable (fun w => gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w) := by
  classical
  have hbound :
      ∀ w, ‖gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w‖
        ≤ ∑ σs : ReplicaSpace N n, ‖f σs‖ := by
    intro w
    simpa [Real.norm_eq_abs] using
      (abs_gibbs_average_n_le (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) (n := n) (t := t) (f := f) w)
  have hU_meas : Measurable (sk.U) := sk.measU
  have hV_meas : Measurable (sim.V) := sim.measV
  have hHt_meas :
      Measurable (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t) := by
    have h1 : Measurable (fun w => (Real.sqrt t) • sk.U w) := hU_meas.const_smul (Real.sqrt t)
    have h2 : Measurable (fun w => (Real.sqrt (1 - t)) • sim.V w) := hV_meas.const_smul (Real.sqrt (1 - t))
    have h3 : Measurable (fun _w : Ω => H_field (N := N) (h := h)) := measurable_const
    simpa [H_t, H_gauss] using ((h1.add h2).add h3)
  have h_gibbs_pmf_meas :
      ∀ (σ : Config N),
        Measurable fun w =>
          gibbs_pmf N
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) σ := by
    intro σ
    have hEval : Measurable fun w =>
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) σ :=
      (evalCLM (N := N) σ).measurable.comp hHt_meas
    have hNum : Measurable fun w =>
        Real.exp (-
          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) σ) :=
      (Real.continuous_exp.measurable.comp (measurable_neg.comp hEval))
    have hZ : Measurable fun w =>
        Z N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) := by
      classical
      have hterm : ∀ τ : Config N,
          Measurable fun w =>
            Real.exp (-
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ) := by
        intro τ
        have hEvalτ : Measurable fun w =>
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ :=
          (evalCLM (N := N) τ).measurable.comp hHt_meas
        exact (Real.continuous_exp.measurable.comp (measurable_neg.comp hEvalτ))
      simpa [Z] using
        (Finset.measurable_sum (s := (Finset.univ : Finset (Config N)))
          (f := fun τ w =>
            Real.exp (-
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ))
          (hf := by intro τ _hτ; simpa using hterm τ))
    simpa [SpinGlass.gibbs_pmf] using hNum.div hZ
  have hMeas :
      Measurable (fun w =>
        gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w) := by
    classical
    have hterm :
        ∀ σs : ReplicaSpace N n,
          Measurable fun w =>
            f σs * ∏ l : Fin n,
              gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) := by
      intro σs
      have hprod :
          Measurable fun w =>
            ∏ l : Fin n,
              gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) := by
        classical
        simpa using
          (Finset.measurable_prod (s := (Finset.univ : Finset (Fin n)))
            (f := fun l w =>
              gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))
            (hf := by
              intro l _hl
              simpa using h_gibbs_pmf_meas (σs l)))
      simpa [mul_assoc] using (measurable_const.mul hprod)
    simpa [gibbs_average_n] using
      (Finset.measurable_sum (s := (Finset.univ : Finset (ReplicaSpace N n)))
        (f := fun σs w =>
          f σs * ∏ l : Fin n,
            gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))
        (hf := by intro σs _hσs; simpa using hterm σs))
  have hAESM :
      AEStronglyMeasurable
        (fun w =>
          gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w) ℙ :=
    hMeas.aestronglyMeasurable
  have hBoundAE :
      ∀ᵐ w ∂ℙ, ‖gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w‖
        ≤ ∑ σs : ReplicaSpace N n, ‖f σs‖ :=
    Filter.Eventually.of_forall hbound
  exact Integrable.of_bound (μ := (ℙ : Measure Ω)) hAESM _ hBoundAE

/--
The Covariance function U(σ^l, σ^l') appearing in the derivative.
U_{l,l'} = E[u(σ^l)u(σ^l')] - E[v(σ^l)v(σ^l')].
For SK: U_{l,l'} = (β²/2)(R_{l,l'}^2 - q).
-/
def U_interaction (U : InteractionKernel (N := N)) (l l' : Fin n) (σs : ReplicaSpace N n) : ℝ :=
  U (σs l) (σs l')

noncomputable def U_kernel_SK : InteractionKernel (N := N) :=
  fun σ τ =>
    let R := overlap N σ τ
    (β^2 / 2) * (R^2 - q)

noncomputable def U_interaction_SK (l l' : Fin n) (σs : ReplicaSpace N n) : ℝ :=
  U_interaction (N := N) (n := n) (U := U_kernel_SK (N := N) (β := β) (q := q)) l l' σs

/-!
### Gaussian IBP on the product disorder space

For the IBP step in the smart-path method, it is convenient to view the pair `(U,V)` of Gaussian
Hamiltonians as a single Gaussian random vector in the product Hilbert space
`EnergySpace N × EnergySpace N`.

The canonical product-basis vectors `std_basis_left/right` and the bridge lemmas
`inner_apply_std_basis_left/right` are defined in `SpinGlass/SKModel.lean` so they can be reused
throughout the project.
-/

/-!
### Covariance operator of the product disorder law

Under independence and centeredness, the covariance operator of the repackaged law
`disorderPairLaw` is **block diagonal**: the left coordinate only “sees” the SK disorder `U`, and
the right coordinate only “sees” the simple disorder `V`.

We record this as explicit identities for `covarianceOperator μ (std_basis_left/right σ)`.
-/

-- `covarianceOperator_disorderPairLaw_std_basis_left/right` moved to `SpinGlass/SKModel.lean`.

theorem ProbabilityTheory.IsGaussian.integral_apply_mul_eq_integral_fderiv_covarianceOperator_std_basis_left_polyGrowth
    (μ : Measure (DisorderSpace (N := N))) [ProbabilityTheory.IsGaussian μ]
    (hmean0 : (∫ x : DisorderSpace (N := N), x ∂μ) = 0) (σ : Config N)
    (F : DisorderSpace (N := N) → ℝ) (hF_meas : Measurable F) (hF_c1 : ContDiff ℝ 1 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ x, |F x| ≤ C * (1 + ‖x‖) ^ m)
    (hF'_growth : ∀ x, ‖fderiv ℝ F x‖ ≤ C * (1 + ‖x‖) ^ m) :
    (∫ x : DisorderSpace (N := N), ((WithLp.ofLp x).1 σ) * F x ∂μ)
      = ∫ x : DisorderSpace (N := N),
          (fderiv ℝ F x) (ProbabilityTheory.covarianceOperator μ (std_basis_left (N := N) σ)) ∂μ := by
  simpa [inner_apply_std_basis_left (N := N) (σ := σ)] using
    (ProbabilityTheory.IsGaussian.integral_inner_mul_eq_integral_fderiv_covarianceOperator_polyGrowth
      (μ := μ) (hmean0 := hmean0) (h := std_basis_left (N := N) σ) (F := F)
      hF_meas hF_c1 hC hF_growth hF'_growth)

theorem ProbabilityTheory.IsGaussian.integral_apply_mul_eq_integral_fderiv_covarianceOperator_std_basis_right_polyGrowth
    (μ : Measure (DisorderSpace (N := N))) [ProbabilityTheory.IsGaussian μ]
    (hmean0 : (∫ x : DisorderSpace (N := N), x ∂μ) = 0) (σ : Config N)
    (F : DisorderSpace (N := N) → ℝ) (hF_meas : Measurable F) (hF_c1 : ContDiff ℝ 1 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ x, |F x| ≤ C * (1 + ‖x‖) ^ m)
    (hF'_growth : ∀ x, ‖fderiv ℝ F x‖ ≤ C * (1 + ‖x‖) ^ m) :
    (∫ x : DisorderSpace (N := N), ((WithLp.ofLp x).2 σ) * F x ∂μ)
      = ∫ x : DisorderSpace (N := N),
          (fderiv ℝ F x) (ProbabilityTheory.covarianceOperator μ (std_basis_right (N := N) σ)) ∂μ := by
  simpa [inner_apply_std_basis_right (N := N) (σ := σ)] using
    (ProbabilityTheory.IsGaussian.integral_inner_mul_eq_integral_fderiv_covarianceOperator_polyGrowth
      (μ := μ) (hmean0 := hmean0) (h := std_basis_right (N := N) σ) (F := F)
      hF_meas hF_c1 hC hF_growth hF'_growth)

/-!
### IBP on the actual disorder law `disorderPairLaw`

The theorems above are “pure Gaussian analysis” on an abstract measure `μ` on `DisorderSpace`.
In the SK interpolation, we apply them with `μ = disorderPairLaw` (the law of the repackaged pair
`(U,V)`), using:

- joint Gaussianity from independence (`SKDisorder.simple_joint_isGaussian_disorderPairLaw_of_indep`);
- centeredness from the model hypotheses (`disorderPairLaw_mean0`).
-/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem integral_disorderPairLaw_left_apply_mul_eq_integral_fderiv_covarianceOperator_polyGrowth
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V) (σ : Config N)
    (F : DisorderSpace (N := N) → ℝ) (hF_meas : Measurable F) (hF_c1 : ContDiff ℝ 1 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ x, |F x| ≤ C * (1 + ‖x‖) ^ m)
    (hF'_growth : ∀ x, ‖fderiv ℝ F x‖ ≤ C * (1 + ‖x‖) ^ m) :
    (∫ x : DisorderSpace (N := N),
        ((WithLp.ofLp x).1 σ) * F x ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim)))
      =
      ∫ x : DisorderSpace (N := N),
        (fderiv ℝ F x)
          (ProbabilityTheory.covarianceOperator
            (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
            (std_basis_left (N := N) σ))
        ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)) := by
  classical
  let μ : Measure (DisorderSpace (N := N)) :=
    disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
  have hgauss :
      ProbabilityTheory.IsGaussian μ :=
    SKDisorder.simple_joint_isGaussian_disorderPairLaw_of_indep (Ω := Ω) (N := N) (β := β) (h := h)
      (q := q) (sk := sk) (sim := sim) hindep
  have hmean0 :
      (∫ x : DisorderSpace (N := N), x ∂μ) = 0 :=
    disorderPairLaw_mean0 (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
  haveI : ProbabilityTheory.IsGaussian μ := hgauss
  simpa [μ] using
    (ProbabilityTheory.IsGaussian.integral_apply_mul_eq_integral_fderiv_covarianceOperator_std_basis_left_polyGrowth
      (N := N) (μ := μ) (hmean0 := hmean0) (σ := σ) (F := F)
      hF_meas hF_c1 hC hF_growth hF'_growth)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem integral_disorderPairLaw_right_apply_mul_eq_integral_fderiv_covarianceOperator_polyGrowth
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V) (σ : Config N)
    (F : DisorderSpace (N := N) → ℝ) (hF_meas : Measurable F) (hF_c1 : ContDiff ℝ 1 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ x, |F x| ≤ C * (1 + ‖x‖) ^ m)
    (hF'_growth : ∀ x, ‖fderiv ℝ F x‖ ≤ C * (1 + ‖x‖) ^ m) :
    (∫ x : DisorderSpace (N := N),
        ((WithLp.ofLp x).2 σ) * F x ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim)))
      =
      ∫ x : DisorderSpace (N := N),
        (fderiv ℝ F x)
          (ProbabilityTheory.covarianceOperator
            (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
            (std_basis_right (N := N) σ))
        ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)) := by
  classical
  let μ : Measure (DisorderSpace (N := N)) :=
    disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
  have hgauss :
      ProbabilityTheory.IsGaussian μ :=
    SKDisorder.simple_joint_isGaussian_disorderPairLaw_of_indep (Ω := Ω) (N := N) (β := β) (h := h)
      (q := q) (sk := sk) (sim := sim) hindep
  have hmean0 :
      (∫ x : DisorderSpace (N := N), x ∂μ) = 0 :=
    disorderPairLaw_mean0 (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
  haveI : ProbabilityTheory.IsGaussian μ := hgauss
  simpa [μ] using
    (ProbabilityTheory.IsGaussian.integral_apply_mul_eq_integral_fderiv_covarianceOperator_std_basis_right_polyGrowth
      (N := N) (μ := μ) (hmean0 := hmean0) (σ := σ) (F := F)
      hF_meas hF_c1 hC hF_growth hF'_growth)

/-!
### The Derivative of the Gibbs Average with respect to the Hamiltonian

This is an essential building block for deriving the replica‑derivative formula (Talagrand Lemma
1.4.2). Given a function `f : ReplicaFun N n` and a test direction `v : EnergySpace N`, the
directional derivative of the Gibbs average with respect to the Hamiltonian `H` in direction `v` is:

  `∑_{σs} f(σs) * ∑_l p_l * (⟨v⟩ - v(σ^l))`

where `p_l` is the product Gibbs weight over replicas **except** replica `l`.
-/

/--
The derivative of the Gibbs weight `∏ l, gibbs_pmf N H (σs l)` with respect to `H` in direction `v`.
Mathematically:
\[
  \frac{d}{dε}\bigg|_{ε=0} ∏_l p_{H + ε v}(σ^l)
    = ∏_l p_H(σ^l) \cdot \sum_l \bigl(\langle v \rangle_H - v(σ^l)\bigr),
\]
where \(\langle v \rangle_H = \sum_\sigma p_H(\sigma) v(\sigma)\).
-/
lemma fderiv_prod_gibbs_pmf_apply (H v : EnergySpace N) (σs : ReplicaSpace N n) :
    fderiv ℝ (fun H' => ∏ l : Fin n, gibbs_pmf N H' (σs l)) H v =
      (∏ l : Fin n, gibbs_pmf N H (σs l)) *
        ∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)) := by
  classical
  have hdiff : ∀ l : Fin n,
      DifferentiableAt ℝ (fun H' => gibbs_pmf N H' (σs l)) H := by
    intro l
    exact SpinGlass.differentiableAt_gibbs_pmf (N := N) (H := H) (σ := σs l)
  have h_fderiv_prod :=
    fderiv_finset_prod
      (𝕜 := ℝ) (E := EnergySpace N) (𝔸' := ℝ) (u := (Finset.univ : Finset (Fin n)))
      (g := fun l H' => gibbs_pmf N H' (σs l))
      (fun l _hl => hdiff l)
  rw [h_fderiv_prod]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  have hterm : ∀ l : Fin n,
      (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l, gibbs_pmf N H (σs j)) *
        fderiv ℝ (fun H' => gibbs_pmf N H' (σs l)) H v
      = (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l, gibbs_pmf N H (σs j)) *
          (gibbs_pmf N H (σs l) *
            ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))) := by
    intro l
    simp [SpinGlass.fderiv_gibbs_pmf_apply]
  calc
    ∑ l ∈ (Finset.univ : Finset (Fin n)),
        (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l, gibbs_pmf N H (σs j)) *
          fderiv ℝ (fun H' => gibbs_pmf N H' (σs l)) H v
      = ∑ l ∈ (Finset.univ : Finset (Fin n)),
          (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l, gibbs_pmf N H (σs j)) *
            (gibbs_pmf N H (σs l) *
              ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))) := by
          refine Finset.sum_congr rfl (fun l _hl => ?_)
          simpa using hterm l
    _ = ∑ l ∈ (Finset.univ : Finset (Fin n)),
          (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l, gibbs_pmf N H (σs j)) *
            (gibbs_pmf N H (σs l) *
              ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))) := by
          rfl
    _ = ∑ l ∈ (Finset.univ : Finset (Fin n)),
          (∏ j : Fin n, gibbs_pmf N H (σs j)) *
            ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)) := by
            refine Finset.sum_congr rfl (fun l _hl => ?_)
            -- `(∏_{j ≠ l} p_j) * p_l = ∏_j p_j`
            have herase : (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l, gibbs_pmf N H (σs j)) *
                gibbs_pmf N H (σs l)
                = ∏ j : Fin n, gibbs_pmf N H (σs j) := by
              classical
              simpa using
                (Finset.prod_erase_mul
                  (s := (Finset.univ : Finset (Fin n)))
                  (f := fun j => gibbs_pmf N H (σs j))
                  (a := l) (Finset.mem_univ l))
            have := congrArg (fun a => a * (((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)))) herase
            simpa [mul_assoc, mul_left_comm, mul_comm] using this
    _ = (∏ j : Fin n, gibbs_pmf N H (σs j)) *
          ∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)) := by
            simpa using
              (Finset.mul_sum (s := (Finset.univ : Finset (Fin n)))
                (f := fun l => (∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))
                (a := (∏ j : Fin n, gibbs_pmf N H (σs j)))).symm

/-- Differentiability of the product Gibbs weight as a function of the Hamiltonian. -/
lemma differentiableAt_prod_gibbs_pmf (H : EnergySpace N) (σs : ReplicaSpace N n) :
    DifferentiableAt ℝ (fun H' => ∏ l : Fin n, gibbs_pmf N H' (σs l)) H := by
  classical
  have hg :
      ∀ l ∈ (Finset.univ : Finset (Fin n)),
        HasFDerivAt (fun H' => gibbs_pmf N H' (σs l))
          (fderiv ℝ (fun H' => gibbs_pmf N H' (σs l)) H) H := by
    intro l _hl
    exact (SpinGlass.differentiableAt_gibbs_pmf (N := N) (H := H) (σ := σs l)).hasFDerivAt
  have hHas :=
    (HasFDerivAt.finset_prod (u := (Finset.univ : Finset (Fin n)))
      (g := fun l H' => gibbs_pmf N H' (σs l))
      (g' := fun l => fderiv ℝ (fun H' => gibbs_pmf N H' (σs l)) H)
      (x := H) hg).differentiableAt
  simpa using hHas

/-- Directional derivative of `gibbs_average_n_det` with respect to the Hamiltonian. -/
lemma fderiv_gibbs_average_n_det_apply (H v : EnergySpace N) (f : ReplicaFun N n) :
    fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f) H v =
      ∑ σs : ReplicaSpace N n,
        f σs * (∏ l : Fin n, gibbs_pmf N H (σs l)) *
          ∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)) := by
  classical
  let u : Finset (ReplicaSpace N n) := Finset.univ
  let A : ReplicaSpace N n → EnergySpace N → ℝ :=
    fun σs H' => f σs * ∏ l : Fin n, gibbs_pmf N H' (σs l)
  have hA_diff : ∀ σs ∈ u, DifferentiableAt ℝ (A σs) H := by
    intro σs _hσs
    have hprod :
        DifferentiableAt ℝ (fun H' => ∏ l : Fin n, gibbs_pmf N H' (σs l)) H :=
      differentiableAt_prod_gibbs_pmf (N := N) (n := n) (H := H) σs
    simpa [A] using (DifferentiableAt.const_mul hprod (f σs))
  have hfderiv_sum :
      fderiv ℝ (fun H' : EnergySpace N => ∑ σs ∈ u, A σs H') H
        = ∑ σs ∈ u, fderiv ℝ (A σs) H := by
    simpa [u] using (fderiv_fun_sum (u := u) (A := A) (x := H) hA_diff)
  have hrewrite :
      (fun H' : EnergySpace N => gibbs_average_n_det (N := N) (n := n) H' f)
        = fun H' : EnergySpace N => ∑ σs ∈ u, A σs H' := by
    funext H'
    simp [gibbs_average_n_det, u, A]
  rw [hrewrite]
  have : fderiv ℝ (fun H' : EnergySpace N => ∑ σs ∈ u, A σs H') H v =
      (∑ σs ∈ u, fderiv ℝ (A σs) H) v := by
    simp [hfderiv_sum]
  simp [this, u, A, fderiv_const_mul, differentiableAt_prod_gibbs_pmf,
    fderiv_prod_gibbs_pmf_apply, mul_assoc, mul_left_comm, mul_comm, mul_add, sub_eq_add_neg,
    Finset.mul_sum]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/--
Differentiability of the `gibbs_average_n` in the Hamiltonian `H`.
-/
lemma differentiableAt_gibbs_average_n (t : ℝ) (f : ReplicaFun N n) (w : Ω) :
    DifferentiableAt ℝ
      (fun H' => ∑ σs : ReplicaSpace N n, f σs * ∏ l, gibbs_pmf N H' (σs l))
      (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) := by
  classical
  let H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w
  have hterm : ∀ σs : ReplicaSpace N n,
      DifferentiableAt ℝ (fun H' => f σs * ∏ l, gibbs_pmf N H' (σs l)) H := by
    intro σs
    have hprod :
        DifferentiableAt ℝ (fun H' => ∏ l : Fin n, gibbs_pmf N H' (σs l)) H := by
      have hg :
          ∀ l ∈ (Finset.univ : Finset (Fin n)),
            HasFDerivAt (fun H' => gibbs_pmf N H' (σs l))
              (fderiv ℝ (fun H' => gibbs_pmf N H' (σs l)) H) H := by
        intro l _hl
        exact
          (SpinGlass.differentiableAt_gibbs_pmf (N := N) (H := H) (σ := σs l)).hasFDerivAt
      have hHas :=
        (HasFDerivAt.finset_prod (u := (Finset.univ : Finset (Fin n)))
          (g := fun l H' => gibbs_pmf N H' (σs l))
          (g' := fun l => fderiv ℝ (fun H' => gibbs_pmf N H' (σs l)) H)
          (x := H) hg).differentiableAt
      simpa using hHas
    exact DifferentiableAt.const_mul hprod (f σs)
  have hsum :
      DifferentiableAt ℝ
        (fun H' => ∑ σs ∈ (Finset.univ : Finset (ReplicaSpace N n)),
          f σs * ∏ l, gibbs_pmf N H' (σs l)) H := by
    refine
      (DifferentiableAt.fun_sum (𝕜 := ℝ) (E := EnergySpace N) (F := ℝ)
        (u := (Finset.univ : Finset (ReplicaSpace N n)))
        (A := fun σs : ReplicaSpace N n => fun H' : EnergySpace N =>
          f σs * ∏ l, gibbs_pmf N H' (σs l))
        (x := H) ?_)
    intro σs _hσs
    simpa using hterm σs
  simpa using hsum

/-!
### Differentiation of `ν_t(f)` with respect to `t`

This is the analytic “outer layer” of Talagrand’s Lemma 1.4.2:
we differentiate the expected Gibbs average along the smart path `H_t`.

At this stage we only push the derivative through the outer expectation;
the subsequent Gaussian IBP step (turning the derivative into replica–interaction terms)
is developed later.
-/

open scoped Topology

open Set

/-- Derivative of the interpolated Hamiltonian `H_t` with respect to `t` (pointwise in `ω`). -/
noncomputable def dH_t (t : ℝ) (w : Ω) : EnergySpace N :=
  (1 / (2 * Real.sqrt t)) • sk.U w - (1 / (2 * Real.sqrt (1 - t))) • sim.V w

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma hasDerivAt_H_gauss (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (w : Ω) :
    HasDerivAt
        (fun s =>
          H_gauss (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s w)
        (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) t := by
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
      HasDerivAt (fun s : ℝ => (Real.sqrt s) • sk.U w)
        ((1 / (2 * Real.sqrt t)) • sk.U w) t :=
    hsqrt.smul_const (sk.U w)
  have hV :
      HasDerivAt (fun s : ℝ => (Real.sqrt ((1 : ℝ) - s)) • sim.V w)
        (((1 / (2 * Real.sqrt (1 - t))) * (-1 : ℝ)) • sim.V w) t :=
    hsqrt_sub.smul_const (sim.V w)
  have hadd := hU.add hV
  simpa [H_gauss, dH_t, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    mul_assoc, mul_left_comm, mul_comm] using hadd

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma hasDerivAt_H_t (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (w : Ω) :
    HasDerivAt
        (fun s =>
          H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s w)
        (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) t := by
  simpa [H_t, dH_t, H_field]
    using (hasDerivAt_H_gauss (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ht w).add_const

/-!
### Uniform control of `dH_t` on a neighborhood (analytic bound)

This is the bound used in the dominated-differentiation proofs: for `x` in a small ball around `t`,
the singular coefficients `1/√x` and `1/√(1-x)` are controlled by constants depending only on `t`.
-/

lemma norm_dH_t_le_on_ball
    (t x : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Metric.ball t ((min t (1 - t)) / 2)) (w : Ω) :
    let cU : ℝ := 1 / (2 * Real.sqrt (t / 2))
    let cV : ℝ := 1 / (2 * Real.sqrt ((1 - t) / 2))
    ‖dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w‖
      ≤ cU * ‖sk.U w‖ + cV * ‖sim.V w‖ := by
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
      ‖dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w‖
        ≤ |1 / (2 * Real.sqrt x)| * ‖sk.U w‖ +
          |1 / (2 * Real.sqrt (1 - x))| * ‖sim.V w‖ := by
    simpa [dH_t, sub_eq_add_neg, norm_add_le, norm_smul, abs_mul] using
      (norm_add_le ((1 / (2 * Real.sqrt x)) • sk.U w) (-(1 / (2 * Real.sqrt (1 - x))) • sim.V w))
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
      |1 / (2 * Real.sqrt x)| * ‖sk.U w‖ +
        |1 / (2 * Real.sqrt (1 - x))| * ‖sim.V w‖
        ≤ (1 / (2 * Real.sqrt (t / 2))) * ‖sk.U w‖ +
            (1 / (2 * Real.sqrt ((1 - t) / 2))) * ‖sim.V w‖ := by
    have hUterm :
        |1 / (2 * Real.sqrt x)| * ‖sk.U w‖ ≤ (1 / (2 * Real.sqrt (t / 2))) * ‖sk.U w‖ :=
      mul_le_mul_of_nonneg_right hcoefU' (norm_nonneg _)
    have hVterm :
        |1 / (2 * Real.sqrt (1 - x))| * ‖sim.V w‖
          ≤ (1 / (2 * Real.sqrt ((1 - t) / 2))) * ‖sim.V w‖ :=
      mul_le_mul_of_nonneg_right hcoefV' (norm_nonneg _)
    exact add_le_add hUterm hVterm
  exact le_trans htri hcmp

/-- Pointwise derivative of the `n`-replica Gibbs average along the path `H_t`. -/
noncomputable def dgibbs_average_n (t : ℝ) (f : ReplicaFun N n) (w : Ω) : ℝ :=
  fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f)
    (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
    (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)

/-! The interpolated Hamiltonian and its `t`-derivative, as functions of the disorder pair. -/

/-!
### Fréchet derivative of `H_t_disorder` and bounds

These lemmas provide the analytic content needed to apply Hilbert-space Gaussian IBP on
`DisorderSpace`: we need explicit (polynomial) bounds on the Fréchet derivative of the relevant
test functions of the disorder pair.
-/

noncomputable def H_t_disorder_lin (t : ℝ) : DisorderSpace (N := N) →L[ℝ] EnergySpace N :=
  (Real.sqrt t) • (WithLp.fstL (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (α := EnergySpace N) (β := EnergySpace N))
    + (Real.sqrt (1 - t)) • (WithLp.sndL (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (α := EnergySpace N) (β := EnergySpace N))

noncomputable def H_t_disorder (t : ℝ) (x : DisorderSpace (N := N)) : EnergySpace N :=
  H_t_disorder_lin (N := N) t x + H_field (N := N) (h := h)

lemma hasFDerivAt_H_t_disorder (t : ℝ) (x : DisorderSpace (N := N)) :
    HasFDerivAt (H_t_disorder (N := N) (h := h) t) (H_t_disorder_lin (N := N) t) x := by
  -- `H_t_disorder = (linear part) + const`, so the derivative is the linear part.
  simpa [H_t_disorder] using
    ( (H_t_disorder_lin (N := N) t).hasFDerivAt.add
        (hasFDerivAt_const (H_field (N := N) (h := h)) x) )

lemma opNorm_H_t_disorder_lin_le (t : ℝ) :
    ‖H_t_disorder_lin (N := N) t‖ ≤ |Real.sqrt t| + |Real.sqrt (1 - t)| := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun x => ?_)
  have hfst : ‖(WithLp.ofLp x).1‖ ≤ ‖x‖ := by
    simpa using (WithLp.norm_fst_le (p := (2 : ℝ≥0∞)) (α := EnergySpace N) (β := EnergySpace N) x)
  have hsnd : ‖(WithLp.ofLp x).2‖ ≤ ‖x‖ := by
    simpa using (WithLp.norm_snd_le (p := (2 : ℝ≥0∞)) (α := EnergySpace N) (β := EnergySpace N) x)
  calc
    ‖H_t_disorder_lin (N := N) t x‖
        ≤ ‖(Real.sqrt t) • (WithLp.ofLp x).1‖ + ‖(Real.sqrt (1 - t)) • (WithLp.ofLp x).2‖ := by
            simpa [H_t_disorder_lin, add_assoc] using norm_add_le _ _
    _ = |Real.sqrt t| * ‖(WithLp.ofLp x).1‖ + |Real.sqrt (1 - t)| * ‖(WithLp.ofLp x).2‖ := by
            simp [norm_smul]
    _ ≤ |Real.sqrt t| * ‖x‖ + |Real.sqrt (1 - t)| * ‖x‖ := by gcongr
    _ = (|Real.sqrt t| + |Real.sqrt (1 - t)|) * ‖x‖ := by ring

lemma norm_fderiv_gibbs_pmf_le_two (H : EnergySpace N) (σ : Config N) :
    ‖fderiv ℝ (fun H' : EnergySpace N => gibbs_pmf N H' σ) H‖ ≤ 2 := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  have hE : |∑ τ : Config N, gibbs_pmf N H τ * v τ| ≤ ‖v‖ := by
    have hs1 : (∑ τ : Config N, gibbs_pmf N H τ) = 1 := sum_gibbs_pmf (N := N) (H := H)
    calc
      |∑ τ : Config N, gibbs_pmf N H τ * v τ|
          ≤ ∑ τ : Config N, |gibbs_pmf N H τ * v τ| := by
              classical
              simpa using
                (Finset.abs_sum_le_sum_abs
                  (f := fun τ : Config N => gibbs_pmf N H τ * v τ)
                  (s := (Finset.univ : Finset (Config N))))
      _ = ∑ τ : Config N, (gibbs_pmf N H τ) * |v τ| := by
              classical
              refine Finset.sum_congr rfl (fun τ _ => ?_)
              simp [abs_mul, abs_of_nonneg (gibbs_pmf_nonneg (N := N) (H := H) (σ := τ))]
      _ ≤ ∑ τ : Config N, (gibbs_pmf N H τ) * ‖v‖ := by
              refine Finset.sum_le_sum (fun τ _ => ?_)
              gcongr
              · exact gibbs_pmf_nonneg (N := N) (H := H) (σ := τ)
              · simpa [Real.norm_eq_abs] using (SpinGlass.abs_apply_le_norm (N := N) v τ)
      _ = ‖v‖ * ∑ τ : Config N, gibbs_pmf N H τ := by
              classical
              simp [Finset.sum_mul, mul_comm]
      _ = ‖v‖ := by simp [hs1]
  have hdiff : |(∑ τ : Config N, gibbs_pmf N H τ * v τ) - v σ| ≤ 2 * ‖v‖ := by
    have hvσ : |v σ| ≤ ‖v‖ := by
      simpa [Real.norm_eq_abs] using (SpinGlass.abs_apply_le_norm (N := N) v σ)
    have : |(∑ τ : Config N, gibbs_pmf N H τ * v τ) - v σ|
        ≤ |∑ τ : Config N, gibbs_pmf N H τ * v τ| + |v σ| := by
          simpa using (abs_sub _ _)
    calc
      |(∑ τ : Config N, gibbs_pmf N H τ * v τ) - v σ|
          ≤ |∑ τ : Config N, gibbs_pmf N H τ * v τ| + |v σ| := this
      _ ≤ ‖v‖ + ‖v‖ := by gcongr
      _ = 2 * ‖v‖ := by ring
  have hformula :
      fderiv ℝ (fun H' : EnergySpace N => gibbs_pmf N H' σ) H v
        = (gibbs_pmf N H σ) * ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v σ) := by
    simpa using (SpinGlass.fderiv_gibbs_pmf_apply (N := N) (H := H) (h := v) σ)
  have hp : 0 ≤ gibbs_pmf N H σ := gibbs_pmf_nonneg (N := N) (H := H) (σ := σ)
  have hp1 : gibbs_pmf N H σ ≤ 1 := gibbs_pmf_le_one (N := N) (H := H) (σ := σ)
  have : ‖fderiv ℝ (fun H' : EnergySpace N => gibbs_pmf N H' σ) H v‖ ≤ 2 * ‖v‖ := by
    have : |fderiv ℝ (fun H' : EnergySpace N => gibbs_pmf N H' σ) H v|
          ≤ (gibbs_pmf N H σ) * (2 * ‖v‖) := by
      -- bound the difference term
      simp [hformula, abs_mul, abs_of_nonneg hp]
      exact mul_le_mul_of_nonneg_left hdiff hp
    have : |fderiv ℝ (fun H' : EnergySpace N => gibbs_pmf N H' σ) H v|
          ≤ 2 * ‖v‖ := by
      calc
        |fderiv ℝ (fun H' : EnergySpace N => gibbs_pmf N H' σ) H v|
            ≤ (gibbs_pmf N H σ) * (2 * ‖v‖) := this
        _ ≤ 1 * (2 * ‖v‖) := by gcongr
        _ = 2 * ‖v‖ := by ring
    simpa [Real.norm_eq_abs] using this
  simpa using this

lemma norm_fderiv_gibbs_pmf_disorder_le (t : ℝ) (σ : Config N) (x : DisorderSpace (N := N)) :
    ‖fderiv ℝ (fun x : DisorderSpace (N := N) =>
        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ) x‖
      ≤ 2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|) := by
  classical
  -- Use the chain rule with the canonical derivative `fderiv` (no need to expose the explicit
  -- derivative map from `hasFDerivAt_gibbs_pmf`).
  have hdiff :
      DifferentiableAt ℝ (fun H' : EnergySpace N => gibbs_pmf N H' σ)
        (H_t_disorder (N := N) (h := h) t x) :=
    SpinGlass.differentiableAt_gibbs_pmf (N := N) (H := H_t_disorder (N := N) (h := h) t x) σ
  have h1 :
      HasFDerivAt (fun H' : EnergySpace N => gibbs_pmf N H' σ)
        (fderiv ℝ (fun H' : EnergySpace N => gibbs_pmf N H' σ)
          (H_t_disorder (N := N) (h := h) t x))
        (H_t_disorder (N := N) (h := h) t x) :=
    hdiff.hasFDerivAt
  have hHx :
      HasFDerivAt (fun x : DisorderSpace (N := N) =>
          gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ)
        ((fderiv ℝ (fun H' : EnergySpace N => gibbs_pmf N H' σ)
            (H_t_disorder (N := N) (h := h) t x)).comp (H_t_disorder_lin (N := N) t)) x := by
    simpa [Function.comp] using h1.comp x (hasFDerivAt_H_t_disorder (N := N) (h := h) t x)
  have hfderiv :
      fderiv ℝ (fun x : DisorderSpace (N := N) =>
          gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ) x
        =
        ((fderiv ℝ (fun H' : EnergySpace N => gibbs_pmf N H' σ)
            (H_t_disorder (N := N) (h := h) t x)).comp (H_t_disorder_lin (N := N) t)) := by
    simpa using hHx.fderiv
  have hσ :
      ‖fderiv ℝ (fun H' : EnergySpace N => gibbs_pmf N H' σ)
            (H_t_disorder (N := N) (h := h) t x)‖ ≤ 2 :=
    norm_fderiv_gibbs_pmf_le_two (N := N) (H := H_t_disorder (N := N) (h := h) t x) σ
  have ht : ‖H_t_disorder_lin (N := N) t‖ ≤ |Real.sqrt t| + |Real.sqrt (1 - t)| :=
    opNorm_H_t_disorder_lin_le (N := N) t
  calc
    ‖fderiv ℝ (fun x : DisorderSpace (N := N) =>
          gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ) x‖
        = ‖((fderiv ℝ (fun H' : EnergySpace N => gibbs_pmf N H' σ)
              (H_t_disorder (N := N) (h := h) t x)).comp (H_t_disorder_lin (N := N) t))‖ := by
            simp [hfderiv]
    _ ≤ ‖fderiv ℝ (fun H' : EnergySpace N => gibbs_pmf N H' σ)
            (H_t_disorder (N := N) (h := h) t x)‖ * ‖H_t_disorder_lin (N := N) t‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|) := by
          have hA :
              ‖fderiv ℝ (fun H' : EnergySpace N => gibbs_pmf N H' σ)
                (H_t_disorder (N := N) (h := h) t x)‖ * ‖H_t_disorder_lin (N := N) t‖
                ≤ 2 * ‖H_t_disorder_lin (N := N) t‖ := by
            gcongr
          have hB : 2 * ‖H_t_disorder_lin (N := N) t‖ ≤ 2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|) := by
            gcongr
          exact le_trans (le_trans (by rfl) hA) hB

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem integral_disorderPairLaw_left_apply_mul_gibbs_pmf_eq_integral_fderiv_covarianceOperator
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V) (t : ℝ) (σ τ : Config N) :
    (∫ x : DisorderSpace (N := N),
        ((WithLp.ofLp x).1 τ) * (gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ)
        ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)))
      =
      ∫ x : DisorderSpace (N := N),
        (fderiv ℝ (fun x : DisorderSpace (N := N) =>
            gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ) x)
          (ProbabilityTheory.covarianceOperator
            (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
            (std_basis_left (N := N) τ))
        ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)) := by
  classical
  let μ : Measure (DisorderSpace (N := N)) :=
    disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
  have hgauss : ProbabilityTheory.IsGaussian μ :=
    SKDisorder.simple_joint_isGaussian_disorderPairLaw_of_indep (Ω := Ω) (N := N) (β := β) (h := h)
      (q := q) (sk := sk) (sim := sim) hindep
  have hmean0 : (∫ x : DisorderSpace (N := N), x ∂μ) = 0 :=
    disorderPairLaw_mean0 (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
  haveI : ProbabilityTheory.IsGaussian μ := hgauss
  -- Regularity and growth hypotheses for IBP.
  have hF_c1 :
      ContDiff ℝ 1 (fun x : DisorderSpace (N := N) =>
        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ) := by
    -- Smoothness of `gibbs_pmf` and affineness of `H_t_disorder`.
    let nTop : WithTop ℕ∞ := (↑(⊤ : ℕ∞))
    have hlin_inf :
        ContDiff ℝ nTop (H_t_disorder_lin (N := N) t) := by
      simpa [nTop] using (H_t_disorder_lin (N := N) t).contDiff (n := nTop)
    have hlin : ContDiff ℝ 1 (H_t_disorder_lin (N := N) t) :=
      hlin_inf.of_le (by simp [nTop])
    have hconst : ContDiff ℝ 1 (fun _ : DisorderSpace (N := N) => H_field (N := N) (h := h)) :=
      contDiff_const
    have hH : ContDiff ℝ 1 (H_t_disorder (N := N) (h := h) t) := by
      simpa [H_t_disorder] using hlin.add hconst
    have hg_inf : ContDiff ℝ nTop (fun H : EnergySpace N => gibbs_pmf N H σ) := by
      simpa [nTop] using (SpinGlass.contDiff_gibbs_pmf (N := N) σ)
    have hg : ContDiff ℝ 1 (fun H : EnergySpace N => gibbs_pmf N H σ) :=
      hg_inf.of_le (by simp [nTop])
    simpa using hg.comp hH
  have hF_meas :
      Measurable (fun x : DisorderSpace (N := N) =>
        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ) :=
    hF_c1.continuous.measurable
  -- Use a single constant `C` for both bounds, with `m = 0`.
  let C : ℝ := max 1 (2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|))
  have hC : 0 ≤ C := by
    have : (0 : ℝ) ≤ 1 := by norm_num
    exact le_trans this (le_max_left _ _)
  have hF_growth : ∀ x, |gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ|
      ≤ C * (1 + ‖x‖) ^ (0 : ℕ) := by
    intro x
    have hle1 : |gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ| ≤ 1 := by
      have : gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ ≤ 1 :=
        gibbs_pmf_le_one (N := N) (H := H_t_disorder (N := N) (h := h) t x) (σ := σ)
      have hn : 0 ≤ gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ :=
        gibbs_pmf_nonneg (N := N) (H := H_t_disorder (N := N) (h := h) t x) (σ := σ)
      simpa [abs_of_nonneg hn] using this
    have h1C : (1 : ℝ) ≤ C := le_trans (le_max_left _ _) (le_rfl)
    simpa [C, pow_zero] using le_trans hle1 (by nlinarith [h1C] : 1 ≤ C)
  have hF'_growth :
      ∀ x, ‖fderiv ℝ (fun x : DisorderSpace (N := N) =>
            gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ) x‖
          ≤ C * (1 + ‖x‖) ^ (0 : ℕ) := by
    intro x
    have hder :
        ‖fderiv ℝ (fun x : DisorderSpace (N := N) =>
              gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ) x‖
          ≤ 2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|) :=
      norm_fderiv_gibbs_pmf_disorder_le (N := N) (h := h) (t := t) (σ := σ) x
    have hleC : 2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|) ≤ C := by
      exact le_max_right _ _
    simpa [C, pow_zero] using le_trans hder (by nlinarith [hleC] : 2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|) ≤ C)
  -- Apply the previously packaged IBP lemma.
  simpa [μ] using
    (integral_disorderPairLaw_left_apply_mul_eq_integral_fderiv_covarianceOperator_polyGrowth
      (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      (hindep := hindep) (σ := τ)
      (F := fun x : DisorderSpace (N := N) =>
        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ)
      hF_meas hF_c1 hC hF_growth hF'_growth)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem integral_disorderPairLaw_right_apply_mul_gibbs_pmf_eq_integral_fderiv_covarianceOperator
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V) (t : ℝ) (σ τ : Config N) :
    (∫ x : DisorderSpace (N := N),
        ((WithLp.ofLp x).2 τ) * (gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ)
        ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)))
      =
      ∫ x : DisorderSpace (N := N),
        (fderiv ℝ (fun x : DisorderSpace (N := N) =>
            gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ) x)
          (ProbabilityTheory.covarianceOperator
            (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
            (std_basis_right (N := N) τ))
        ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)) := by
  classical
  let μ : Measure (DisorderSpace (N := N)) :=
    disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
  have hgauss : ProbabilityTheory.IsGaussian μ :=
    SKDisorder.simple_joint_isGaussian_disorderPairLaw_of_indep (Ω := Ω) (N := N) (β := β) (h := h)
      (q := q) (sk := sk) (sim := sim) hindep
  have hmean0 : (∫ x : DisorderSpace (N := N), x ∂μ) = 0 :=
    disorderPairLaw_mean0 (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
  haveI : ProbabilityTheory.IsGaussian μ := hgauss
  -- Regularity and growth hypotheses for IBP.
  have hF_c1 :
      ContDiff ℝ 1 (fun x : DisorderSpace (N := N) =>
        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ) := by
    -- Smoothness of `gibbs_pmf` and affineness of `H_t_disorder`.
    let nTop : WithTop ℕ∞ := (↑(⊤ : ℕ∞))
    have hlin_inf :
        ContDiff ℝ nTop (H_t_disorder_lin (N := N) t) := by
      simpa [nTop] using (H_t_disorder_lin (N := N) t).contDiff (n := nTop)
    have hlin : ContDiff ℝ 1 (H_t_disorder_lin (N := N) t) :=
      hlin_inf.of_le (by simp [nTop])
    have hconst : ContDiff ℝ 1 (fun _ : DisorderSpace (N := N) => H_field (N := N) (h := h)) :=
      contDiff_const
    have hH : ContDiff ℝ 1 (H_t_disorder (N := N) (h := h) t) := by
      simpa [H_t_disorder] using hlin.add hconst
    have hg_inf : ContDiff ℝ nTop (fun H : EnergySpace N => gibbs_pmf N H σ) := by
      simpa [nTop] using (SpinGlass.contDiff_gibbs_pmf (N := N) σ)
    have hg : ContDiff ℝ 1 (fun H : EnergySpace N => gibbs_pmf N H σ) :=
      hg_inf.of_le (by simp [nTop])
    simpa using hg.comp hH
  have hF_meas :
      Measurable (fun x : DisorderSpace (N := N) =>
        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ) :=
    hF_c1.continuous.measurable
  -- Use a single constant `C` for both bounds, with `m = 0`.
  let C : ℝ := max 1 (2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|))
  have hC : 0 ≤ C := by
    have : (0 : ℝ) ≤ 1 := by norm_num
    exact le_trans this (le_max_left _ _)
  have hF_growth : ∀ x, |gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ|
      ≤ C * (1 + ‖x‖) ^ (0 : ℕ) := by
    intro x
    have hle1 : |gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ| ≤ 1 := by
      have : gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ ≤ 1 :=
        gibbs_pmf_le_one (N := N) (H := H_t_disorder (N := N) (h := h) t x) (σ := σ)
      have hn : 0 ≤ gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ :=
        gibbs_pmf_nonneg (N := N) (H := H_t_disorder (N := N) (h := h) t x) (σ := σ)
      simpa [abs_of_nonneg hn] using this
    have h1C : (1 : ℝ) ≤ C := le_max_left _ _
    simpa [C, pow_zero] using le_trans hle1 (by nlinarith [h1C] : 1 ≤ C)
  have hF'_growth :
      ∀ x, ‖fderiv ℝ (fun x : DisorderSpace (N := N) =>
            gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ) x‖
          ≤ C * (1 + ‖x‖) ^ (0 : ℕ) := by
    intro x
    have hder :
        ‖fderiv ℝ (fun x : DisorderSpace (N := N) =>
              gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ) x‖
          ≤ 2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|) :=
      norm_fderiv_gibbs_pmf_disorder_le (N := N) (h := h) (t := t) (σ := σ) x
    have hleC : 2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|) ≤ C := by
      exact le_max_right _ _
    simpa [C, pow_zero] using le_trans hder (by nlinarith [hleC] : 2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|) ≤ C)
  -- Apply the previously packaged IBP lemma.
  simpa [μ] using
    (integral_disorderPairLaw_right_apply_mul_eq_integral_fderiv_covarianceOperator_polyGrowth
      (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      (hindep := hindep) (σ := τ)
      (F := fun x : DisorderSpace (N := N) =>
        gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ)
      hF_meas hF_c1 hC hF_growth hF'_growth)


noncomputable def dH_t_disorder (t : ℝ) (x : DisorderSpace (N := N)) : EnergySpace N :=
  (1 / (2 * Real.sqrt t)) • (WithLp.ofLp x).1
    - (1 / (2 * Real.sqrt (1 - t))) • (WithLp.ofLp x).2

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
@[simp] lemma H_t_disorder_disorderPair (t : ℝ) (w : Ω) :
    H_t_disorder (N := N) (h := h) t
        (disorderPair (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) w)
      =
      H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w := by
  simp [H_t_disorder, H_t_disorder_lin, H_t, H_gauss, H_field, disorderPair]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
@[simp] lemma dH_t_disorder_disorderPair (t : ℝ) (w : Ω) :
    dH_t_disorder (N := N) t
        (disorderPair (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) w)
      =
      dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w := by
  simp [dH_t_disorder, dH_t, disorderPair]

noncomputable def gibbs_average_n_disorder (t : ℝ) (f : ReplicaFun N n) :
    DisorderSpace (N := N) → ℝ :=
  fun x =>
    gibbs_average_n_det (N := N) (n := n)
      (H_t_disorder (N := N) (h := h) t x) f

noncomputable def dgibbs_average_n_disorder (t : ℝ) (f : ReplicaFun N n) :
    DisorderSpace (N := N) → ℝ :=
  fun x =>
    fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f)
      (H_t_disorder (N := N) (h := h) t x)
      (dH_t_disorder (N := N) t x)

/-!
### Algebraic reshaping of `dgibbs_average_n_disorder`

For IBP we want `dgibbs_average_n_disorder` as a finite sum of coordinate functionals
`x ↦ (WithLp.ofLp x).1 τ` and `x ↦ (WithLp.ofLp x).2 τ` multiplied by smooth bounded factors.
-/

noncomputable def gibbs_pmf_disorder (t : ℝ) (σ : Config N) : DisorderSpace (N := N) → ℝ :=
  fun x => gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) σ

lemma contDiff_gibbs_pmf_disorder (t : ℝ) (σ : Config N) :
    ContDiff ℝ 1 (gibbs_pmf_disorder (N := N) (h := h) t σ) := by
  -- Smoothness of `gibbs_pmf` and affineness of `H_t_disorder`.
  let nTop : WithTop ℕ∞ := (↑(⊤ : ℕ∞))
  have hlin_inf : ContDiff ℝ nTop (H_t_disorder_lin (N := N) t) := by
    simpa [nTop] using (H_t_disorder_lin (N := N) t).contDiff (n := nTop)
  have hlin : ContDiff ℝ 1 (H_t_disorder_lin (N := N) t) :=
    hlin_inf.of_le (by simp [nTop])
  have hconst : ContDiff ℝ 1 (fun _ : DisorderSpace (N := N) => H_field (N := N) (h := h)) :=
    contDiff_const
  have hH : ContDiff ℝ 1 (H_t_disorder (N := N) (h := h) t) := by
    simpa [H_t_disorder] using hlin.add hconst
  have hg_inf : ContDiff ℝ nTop (fun H : EnergySpace N => gibbs_pmf N H σ) := by
    simpa [nTop] using (SpinGlass.contDiff_gibbs_pmf (N := N) σ)
  have hg : ContDiff ℝ 1 (fun H : EnergySpace N => gibbs_pmf N H σ) :=
    hg_inf.of_le (by simp [nTop])
  simpa [gibbs_pmf_disorder] using hg.comp hH

noncomputable def prod_gibbs_pmf_disorder (t : ℝ) (σs : ReplicaSpace N n) :
    DisorderSpace (N := N) → ℝ :=
  fun x => ∏ l : Fin n, gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := σs l) x

lemma contDiff_prod_gibbs_pmf_disorder (t : ℝ) (σs : ReplicaSpace N n) :
    ContDiff ℝ 1 (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) t σs) := by
  classical
  -- Finite product of `C^1` functions.
  -- `prod_gibbs_pmf_disorder` is definitionaly a `Finset.univ.prod`.
  simpa [prod_gibbs_pmf_disorder] using
    (contDiff_prod (𝕜 := ℝ) (n := (1 : ℕ))
      (t := (Finset.univ : Finset (Fin n)))
      (f := fun l : Fin n => fun x : DisorderSpace (N := N) =>
        gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := σs l) x)
      (h := fun l _hl =>
        contDiff_gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := σs l)))

lemma norm_fderiv_prod_gibbs_pmf_disorder_le (t : ℝ) (σs : ReplicaSpace N n) (x : DisorderSpace (N := N)) :
    ‖fderiv ℝ (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) t σs) x‖
      ≤ (n : ℝ) * (2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|)) := by
  classical
  -- Use the explicit `fderiv` formula for a finite product.
  have hdiff :
      ∀ l : Fin n, DifferentiableAt ℝ (fun x : DisorderSpace (N := N) =>
        gibbs_pmf_disorder (N := N) (h := h) t (σs l) x) x :=
    fun l => by
      -- `gibbs_pmf_disorder t σ = (fun H => gibbs_pmf N H σ) ∘ H_t_disorder t`
      have hg :
          DifferentiableAt ℝ (fun H : EnergySpace N => gibbs_pmf N H (σs l))
            (H_t_disorder (N := N) (h := h) t x) :=
        SpinGlass.differentiableAt_gibbs_pmf (N := N) (H := H_t_disorder (N := N) (h := h) t x) (σ := σs l)
      have hH :
          DifferentiableAt ℝ (H_t_disorder (N := N) (h := h) t) x :=
        (hasFDerivAt_H_t_disorder (N := N) (h := h) t x).differentiableAt
      simpa [gibbs_pmf_disorder, Function.comp] using hg.comp x hH
  -- Rewrite `prod_gibbs_pmf_disorder` as a `Finset` product.
  have hprod :
      fderiv ℝ (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) t σs) x
        =
        ∑ l : Fin n,
          (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l,
              gibbs_pmf_disorder (N := N) (h := h) t (σs j) x) •
            fderiv ℝ (fun x : DisorderSpace (N := N) =>
              gibbs_pmf_disorder (N := N) (h := h) t (σs l) x) x := by
    -- `fderiv_finset_prod` applies to `∏ l ∈ univ, g l ·`.
    simpa [prod_gibbs_pmf_disorder, Finset.prod_attach] using
      (fderiv_finset_prod (𝕜 := ℝ) (E := DisorderSpace (N := N)) (u := (Finset.univ : Finset (Fin n)))
        (g := fun l => fun x : DisorderSpace (N := N) =>
          gibbs_pmf_disorder (N := N) (h := h) t (σs l) x) (x := x)
        (hg := fun l hl => hdiff l))
  -- Bound the operator norm by bounding each summand.
  -- Each Gibbs pmf factor is in `[0,1]`, so the product has abs ≤ 1.
  -- Each `‖fderiv gibbs_pmf_disorder‖` is bounded by `2 * (|√t| + |√(1-t)|)`.
  have hderiv_one :
      ∀ l : Fin n,
        ‖fderiv ℝ (fun x : DisorderSpace (N := N) =>
            gibbs_pmf_disorder (N := N) (h := h) t (σs l) x) x‖
          ≤ 2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|) := by
    intro l
    simpa [gibbs_pmf_disorder] using
      (norm_fderiv_gibbs_pmf_disorder_le (N := N) (h := h) (t := t) (σ := σs l) x)
  -- Finish with a crude sum bound: `∑ l, ‖...‖ ≤ n * C`.
  -- We only need a coarse constant for polynomial-growth IBP hypotheses.
  rw [hprod]
  -- `‖∑ l, ...‖ ≤ ∑ l, ‖...‖`.
  have : ‖∑ l : Fin n,
        (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l,
              gibbs_pmf_disorder (N := N) (h := h) t (σs j) x) •
          fderiv ℝ (fun x : DisorderSpace (N := N) =>
            gibbs_pmf_disorder (N := N) (h := h) t (σs l) x) x‖
      ≤ ∑ l : Fin n,
          ‖(∏ j ∈ (Finset.univ : Finset (Fin n)).erase l,
              gibbs_pmf_disorder (N := N) (h := h) t (σs j) x) •
            fderiv ℝ (fun x : DisorderSpace (N := N) =>
              gibbs_pmf_disorder (N := N) (h := h) t (σs l) x) x‖ := by
    -- interpret both sides as `Finset.univ.sum`
    simpa using
      (norm_sum_le (s := (Finset.univ : Finset (Fin n)))
        (f := fun l : Fin n =>
          (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l,
                gibbs_pmf_disorder (N := N) (h := h) t (σs j) x) •
            fderiv ℝ (fun x : DisorderSpace (N := N) =>
              gibbs_pmf_disorder (N := N) (h := h) t (σs l) x) x))
  refine le_trans this ?_
  -- Bound each summand by `‖fderiv‖`, since `|product| ≤ 1`.
  have hsummand :
      ∀ l : Fin n,
        ‖(∏ j ∈ (Finset.univ : Finset (Fin n)).erase l,
              gibbs_pmf_disorder (N := N) (h := h) t (σs j) x) •
            fderiv ℝ (fun x : DisorderSpace (N := N) =>
              gibbs_pmf_disorder (N := N) (h := h) t (σs l) x) x‖
          ≤ 2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|) := by
    intro l
    have hprod_le : ‖∏ j ∈ (Finset.univ : Finset (Fin n)).erase l,
        gibbs_pmf_disorder (N := N) (h := h) t (σs j) x‖ ≤ 1 := by
      -- Each factor is in `[0,1]`, hence the product is in `[0,1]`.
      have hfac0 :
          ∀ j ∈ (Finset.univ : Finset (Fin n)).erase l,
            0 ≤ gibbs_pmf_disorder (N := N) (h := h) t (σs j) x := by
        intro j _hj
        exact gibbs_pmf_nonneg (N := N) (H := H_t_disorder (N := N) (h := h) t x) (σ := σs j)
      have hfac1 :
          ∀ j ∈ (Finset.univ : Finset (Fin n)).erase l,
            gibbs_pmf_disorder (N := N) (h := h) t (σs j) x ≤ 1 := by
        intro j _hj
        exact gibbs_pmf_le_one (N := N) (H := H_t_disorder (N := N) (h := h) t x) (σ := σs j)
      have hfac_abs1 :
          ∀ j ∈ (Finset.univ : Finset (Fin n)).erase l,
            |gibbs_pmf_disorder (N := N) (h := h) t (σs j) x| ≤ 1 := by
        intro j hj
        have hn : 0 ≤ gibbs_pmf_disorder (N := N) (h := h) t (σs j) x := hfac0 j hj
        have h1 : gibbs_pmf_disorder (N := N) (h := h) t (σs j) x ≤ 1 := hfac1 j hj
        simpa [abs_of_nonneg hn] using h1
      have hprod_abs1 :
          (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l,
              |gibbs_pmf_disorder (N := N) (h := h) t (σs j) x|) ≤ 1 := by
        exact Finset.prod_le_one (s := (Finset.univ : Finset (Fin n)).erase l)
          (f := fun j => |gibbs_pmf_disorder (N := N) (h := h) t (σs j) x|)
          (h0 := fun j hj => abs_nonneg _)
          (h1 := hfac_abs1)
      -- turn this into a norm bound
      -- `‖∏ g_j‖ = |∏ g_j| = ∏ |g_j|`.
      simpa [Real.norm_eq_abs, Finset.abs_prod] using hprod_abs1
    -- `‖c • L‖ = ‖c‖ * ‖L‖` for scalar smul on `→L`.
    calc
      ‖(∏ j ∈ (Finset.univ : Finset (Fin n)).erase l,
            gibbs_pmf_disorder (N := N) (h := h) t (σs j) x) •
          fderiv ℝ (fun x : DisorderSpace (N := N) =>
            gibbs_pmf_disorder (N := N) (h := h) t (σs l) x) x‖
          = ‖∏ j ∈ (Finset.univ : Finset (Fin n)).erase l,
                gibbs_pmf_disorder (N := N) (h := h) t (σs j) x‖ *
              ‖fderiv ℝ (fun x : DisorderSpace (N := N) =>
                  gibbs_pmf_disorder (N := N) (h := h) t (σs l) x) x‖ := by
              simp [norm_smul]
      _ ≤ 1 * (2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|)) := by
              gcongr
              exact hderiv_one l
      _ = 2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|) := by ring
  -- Sum the bounds.
  calc
    (∑ l : Fin n,
        ‖(∏ j ∈ (Finset.univ : Finset (Fin n)).erase l,
              gibbs_pmf_disorder (N := N) (h := h) t (σs j) x) •
            fderiv ℝ (fun x : DisorderSpace (N := N) =>
              gibbs_pmf_disorder (N := N) (h := h) t (σs l) x) x‖)
        ≤ ∑ _l : Fin n, (2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|)) := by
            refine Finset.sum_le_sum ?_
            intro l _hl
            exact hsummand l
    _ = (n : ℝ) * (2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|)) := by
          -- sum of a constant over `Fin n`
          simp [Fintype.card_fin]

/-!
`A_disorder t f τ x` is the **directional derivative** of the replica functional
`H ↦ gibbs_average_n_det H f` in the Hamiltonian direction `std_basis N τ`, evaluated at
`H = H_t_disorder t x`.

The explicit combinatorial expression (`n * g τ - count`) is provided as a lemma below.
-/
noncomputable def A_disorder (t : ℝ) (f : ReplicaFun N n) (τ : Config N) :
    DisorderSpace (N := N) → ℝ :=
  fun x =>
    fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f)
      (H_t_disorder (N := N) (h := h) t x)
      (std_basis N τ)

/-!
For analytic estimates/IBP hypotheses it is convenient to have a fully explicit expression for
`A_disorder` that avoids higher derivatives. We package that as `A_disorder_explicit`.
-/
noncomputable def A_disorder_explicit (t : ℝ) (f : ReplicaFun N n) (τ : Config N) :
    DisorderSpace (N := N) → ℝ :=
  fun x =>
    ∑ σs : ReplicaSpace N n,
      f σs * (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x) *
        ((n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
          - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ))

lemma contDiff_A_disorder_explicit (t : ℝ) (f : ReplicaFun N n) (τ : Config N) :
    ContDiff ℝ 1 (A_disorder_explicit (N := N) (n := n) (h := h) t f τ) := by
  classical
  -- Finite sum over `σs`, each summand is a product of `C^1` functions.
  -- We use the convenient `ContDiff.sum` lemma for `Finset`.
  have hsum :
      ContDiff ℝ 1 (fun x : DisorderSpace (N := N) =>
        ∑ σs : ReplicaSpace N n, f σs *
          (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x) *
            (((n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x))
              - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ))) := by
    refine ContDiff.sum (𝕜 := ℝ) (n := (1 : ℕ))
      (s := (Finset.univ : Finset (ReplicaSpace N n))) ?_
    intro σs _hσs
    have hP : ContDiff ℝ 1 (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) t σs) :=
      contDiff_prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs
    have hG : ContDiff ℝ 1 (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ)) :=
      contDiff_gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ)
    have hDiff :
        ContDiff ℝ 1 (fun x : DisorderSpace (N := N) =>
          ((n : ℝ) * gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
            - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)) := by
      simpa using (contDiff_const.mul hG).sub contDiff_const
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (contDiff_const.mul (hP.mul hDiff))
  simpa [A_disorder_explicit] using hsum

lemma measurable_A_disorder_explicit (t : ℝ) (f : ReplicaFun N n) (τ : Config N) :
    Measurable (A_disorder_explicit (N := N) (n := n) (h := h) t f τ) :=
  (contDiff_A_disorder_explicit (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ)).continuous.measurable

lemma abs_prod_gibbs_pmf_disorder_le_one (t : ℝ) (σs : ReplicaSpace N n) (x : DisorderSpace (N := N)) :
    |prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x| ≤ 1 := by
  classical
  -- Each Gibbs pmf is in `[0,1]`, hence the product has absolute value ≤ 1.
  have hfac :
      ∀ l : Fin n, |gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := σs l) x| ≤ 1 := by
    intro l
    have hle : gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) (σs l) ≤ 1 :=
      gibbs_pmf_le_one (N := N) (H := H_t_disorder (N := N) (h := h) t x) (σ := σs l)
    have hn : 0 ≤ gibbs_pmf N (H_t_disorder (N := N) (h := h) t x) (σs l) :=
      gibbs_pmf_nonneg (N := N) (H := H_t_disorder (N := N) (h := h) t x) (σ := σs l)
    simpa [gibbs_pmf_disorder, abs_of_nonneg hn] using hle
  have hprod :
      (∏ l : Fin n, |gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := σs l) x|) ≤ 1 := by
    simpa using
      (Finset.prod_le_one (s := (Finset.univ : Finset (Fin n)))
        (f := fun l : Fin n => |gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := σs l) x|)
        (h0 := fun _ _ => abs_nonneg _)
        (h1 := by
          intro l _hl
          exact hfac l))
  simpa [prod_gibbs_pmf_disorder, Finset.abs_prod] using hprod

lemma abs_n_mul_gibbs_pmf_sub_card_le (t : ℝ) (τ : Config N) (σs : ReplicaSpace N n)
    (x : DisorderSpace (N := N)) :
    |(n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
        - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)|
      ≤ (2 * (n : ℝ)) := by
  classical
  set g : ℝ := gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x
  have hg0 : 0 ≤ g := by
    simpa [g, gibbs_pmf_disorder] using
      (gibbs_pmf_nonneg (N := N) (H := H_t_disorder (N := N) (h := h) t x) (σ := τ))
  have hg1 : g ≤ 1 := by
    simpa [g, gibbs_pmf_disorder] using
      (gibbs_pmf_le_one (N := N) (H := H_t_disorder (N := N) (h := h) t x) (σ := τ))
  have hcard_le : ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ) ≤ n := by
    have h' :
        (Finset.univ.filter fun l : Fin n => σs l = τ).card
          ≤ (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    simpa [Finset.card_univ] using (Nat.cast_le.2 h')
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact Nat.cast_nonneg _
  have ha : |(n : ℝ) * g| ≤ n := by
    have hng0 : 0 ≤ (n : ℝ) * g := mul_nonneg hn0 hg0
    have : (n : ℝ) * g ≤ (n : ℝ) * 1 := mul_le_mul_of_nonneg_left hg1 hn0
    simpa [abs_of_nonneg hng0] using (by simpa using this)
  have hb : |((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)| ≤ n := by
    have hnonneg : 0 ≤ ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ) :=
      Nat.cast_nonneg _
    simpa [abs_of_nonneg hnonneg] using hcard_le
  have hab : |(n : ℝ) * g - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)|
      ≤ |(n : ℝ) * g| + |((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)| := by
    simpa [sub_zero, zero_sub] using
      (abs_sub_le ((n : ℝ) * g) (0 : ℝ) ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ))
  calc
    |(n : ℝ) * g - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)|
        ≤ |(n : ℝ) * g| + |((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)| := hab
    _ ≤ n + n := by gcongr
    _ = 2 * (n : ℝ) := by ring

lemma abs_A_disorder_explicit_le (t : ℝ) (f : ReplicaFun N n) (τ : Config N)
    (x : DisorderSpace (N := N)) :
    |A_disorder_explicit (N := N) (n := n) (h := h) t f τ x|
      ≤ (2 * (n : ℝ)) * (∑ σs : ReplicaSpace N n, |f σs|) := by
  classical
  -- Expand and bound term-by-term.
  have hterm :
      ∀ σs : ReplicaSpace N n,
        |f σs *
            (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x) *
            ((n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
              - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ))|
          ≤ (2 * (n : ℝ)) * |f σs| := by
    intro σs
    have hP : |prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x| ≤ 1 :=
      abs_prod_gibbs_pmf_disorder_le_one (N := N) (n := n) (h := h) (t := t) σs x
    have hD :
        |(n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
            - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)|
          ≤ 2 * (n : ℝ) :=
      abs_n_mul_gibbs_pmf_sub_card_le (N := N) (n := n) (h := h) (t := t) (τ := τ) σs x
    -- `|f * P * D| ≤ |f| * 1 * (2n)`.
    calc
      |f σs *
          (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x) *
          ((n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
            - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ))|
          = |f σs| * |prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x| *
              |(n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
                  - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)| := by
              simp [abs_mul, mul_assoc]
      _ ≤ |f σs| * 1 * (2 * (n : ℝ)) := by
              have hf0 : 0 ≤ |f σs| := abs_nonneg _
              have hD0 :
                  0 ≤ |(n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
                          - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)| :=
                abs_nonneg _
              -- bound `|P|` by `1`, then bound `|D|` by `2n`.
              have hmid :
                  |f σs| * |prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x| *
                      |(n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
                          - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)|
                    ≤ |f σs| * 1 *
                        |(n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
                            - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)| := by
                -- multiply inequality `|P| ≤ 1` by the nonnegative factors.
                have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP hf0) hD0
                -- rearrange
                simpa [mul_assoc] using this
              have hlast :
                  |f σs| * 1 *
                        |(n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
                            - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)|
                    ≤ |f σs| * 1 * (2 * (n : ℝ)) := by
                -- multiply inequality `|D| ≤ 2n` by `|f| * 1 ≥ 0`.
                have hf1 : 0 ≤ |f σs| * (1 : ℝ) := by nlinarith [hf0]
                have := mul_le_mul_of_nonneg_left hD hf1
                -- rearrange
                simpa [mul_assoc] using this
              exact le_trans hmid hlast
      _ = (2 * (n : ℝ)) * |f σs| := by ring
  -- Sum bound.
  calc
    |A_disorder_explicit (N := N) (n := n) (h := h) t f τ x|
        = |∑ σs : ReplicaSpace N n,
            f σs *
              (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x) *
              ((n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
                - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ))| := by
            simp [A_disorder_explicit]
    _ ≤ ∑ σs : ReplicaSpace N n,
          |f σs *
              (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x) *
              ((n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
                - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ))| := by
            simpa using
              (Finset.abs_sum_le_sum_abs
                (f := fun σs : ReplicaSpace N n =>
                  f σs *
                    (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x) *
                    ((n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
                      - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)))
                (s := (Finset.univ : Finset (ReplicaSpace N n))))
    _ ≤ ∑ σs : ReplicaSpace N n, (2 * (n : ℝ)) * |f σs| := by
            refine Finset.sum_le_sum (fun σs _ => hterm σs)
    _ = (2 * (n : ℝ)) * (∑ σs : ReplicaSpace N n, |f σs|) := by
            simp [Finset.mul_sum, mul_comm]

lemma norm_fderiv_A_disorder_explicit_le (t : ℝ) (f : ReplicaFun N n) (τ : Config N)
    (x : DisorderSpace (N := N)) :
    ‖fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) t f τ) x‖
      ≤ ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) *
            (2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|))) *
          (∑ σs : ReplicaSpace N n, |f σs|) := by
  classical
  -- View `A_disorder_explicit` as a finite sum and use triangle inequality on the derivative.
  let μC : ℝ := 2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|)
  have hμC : 0 ≤ μC := by
    have : (0 : ℝ) ≤ |Real.sqrt t| + |Real.sqrt (1 - t)| := by positivity
    nlinarith [this]
  have hfderivG :
      ‖fderiv ℝ (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ)) x‖ ≤ μC := by
    -- This is exactly `norm_fderiv_gibbs_pmf_disorder_le`.
    simpa [gibbs_pmf_disorder, μC] using
      (norm_fderiv_gibbs_pmf_disorder_le (N := N) (h := h) (t := t) (σ := τ) x)
  -- Rewrite `fderiv` of the sum as the sum of `fderiv`s.
  have hsum :
      fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) t f τ) x
        =
        ∑ σs : ReplicaSpace N n,
          fderiv ℝ (fun x : DisorderSpace (N := N) =>
            f σs *
              (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x) *
              ((n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
                - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ))) x := by
    -- `fderiv` of a `Finset` sum.
    have hdiff :
        ∀ σs : ReplicaSpace N n,
          DifferentiableAt ℝ (fun x : DisorderSpace (N := N) =>
            f σs *
              (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x) *
              ((n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
                - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ))) x := by
      intro σs
      -- `C^1` implies differentiable.
      have hC1 :
          ContDiff ℝ 1 (fun x : DisorderSpace (N := N) =>
            f σs *
              (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x) *
              ((n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
                - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ))) := by
        -- This is one summand of `A_disorder_explicit`; reuse the ingredients from `contDiff_A_disorder_explicit`.
        have hP : ContDiff ℝ 1 (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) t σs) :=
          contDiff_prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs
        have hG : ContDiff ℝ 1 (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ)) :=
          contDiff_gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ)
        have hDiff :
            ContDiff ℝ 1 (fun x : DisorderSpace (N := N) =>
              ((n : ℝ) * gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
                - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)) := by
          simpa using (contDiff_const.mul hG).sub contDiff_const
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (contDiff_const.mul (hP.mul hDiff))
      -- `ContDiff 1` implies differentiable.
      exact ((hC1.differentiable (by norm_num)) x)
    -- Use `fderiv_fun_sum` on `Finset.univ`.
    simpa [A_disorder_explicit] using
      (fderiv_fun_sum (𝕜 := ℝ) (u := (Finset.univ : Finset (ReplicaSpace N n)))
        (A := fun σs : ReplicaSpace N n => fun x : DisorderSpace (N := N) =>
          f σs *
            (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x) *
            ((n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
              - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)))
        (x := x)
        (h := fun σs _hσs => hdiff σs))
  -- Now bound the norm by the sum of the norms.
  rw [hsum]
  refine le_trans (norm_sum_le (s := (Finset.univ : Finset (ReplicaSpace N n)))
      (f := fun σs : ReplicaSpace N n =>
        fderiv ℝ (fun x : DisorderSpace (N := N) =>
          f σs *
            (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x) *
            ((n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
              - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ))) x)) ?_
  -- Bound each summand uniformly, then sum.
  have hsum_bound :
      ∀ σs : ReplicaSpace N n,
        ‖fderiv ℝ (fun x : DisorderSpace (N := N) =>
            f σs *
              (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x) *
              ((n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
                - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ))) x‖
          ≤ |f σs| * ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) * μC) := by
    intro σs
    -- Let `P x := prod_gibbs_pmf_disorder ... σs x`, `D x := (n) * G x - card`.
    let P : DisorderSpace (N := N) → ℝ :=
      prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs
    let D : DisorderSpace (N := N) → ℝ :=
      fun x =>
        (n : ℝ) * gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x
          - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)
    have hP_abs : |P x| ≤ 1 := by
      simpa [P] using abs_prod_gibbs_pmf_disorder_le_one (N := N) (n := n) (h := h) (t := t) σs x
    have hD_abs : |D x| ≤ 2 * (n : ℝ) := by
      simpa [D] using
        (abs_n_mul_gibbs_pmf_sub_card_le (N := N) (n := n) (h := h) (t := t) (τ := τ) σs x)
    have hP_der : ‖fderiv ℝ P x‖ ≤ (n : ℝ) * μC := by
      -- This is `norm_fderiv_prod_gibbs_pmf_disorder_le`.
      simpa [P, μC, mul_assoc, mul_left_comm, mul_comm] using
        (norm_fderiv_prod_gibbs_pmf_disorder_le (N := N) (n := n) (h := h) (t := t) σs x)
    have hD_der : ‖fderiv ℝ D x‖ ≤ (n : ℝ) * μC := by
      -- `D = (n) * G - const`, so `‖Df‖ ≤ n * ‖DG‖`.
      have hDG : ‖fderiv ℝ (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ)) x‖ ≤ μC :=
        hfderivG
      -- `fderiv` of `x ↦ (n : ℝ) * G x` is `n • fderiv G x`.
      have hdiffG :
          DifferentiableAt ℝ (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ)) x := by
        -- `ContDiff 1` implies differentiable
        exact ((contDiff_gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ)).differentiable (by norm_num)) x
      have hfderivMul :
          fderiv ℝ (fun x : DisorderSpace (N := N) => (n : ℝ) * gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x) x
            = (n : ℝ) • fderiv ℝ (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ)) x := by
        simpa using (fderiv_const_mul (𝕜 := ℝ) (a := gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ)) hdiffG (b := (n : ℝ)))
      -- subtracting a constant doesn't change the derivative
      -- (the constant derivative is `0`).
      have : ‖fderiv ℝ D x‖ ≤ (n : ℝ) * μC := by
        -- rewrite `fderiv D`
        -- `fderiv (fun x => A x - const) = fderiv A`
        -- and then bound using `hDG`.
        have hsub :
            fderiv ℝ D x
              = fderiv ℝ (fun x : DisorderSpace (N := N) =>
                  (n : ℝ) * gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x) x := by
          -- Use `fderiv_sub_const`.
          simpa [D] using
            (fderiv_sub_const (𝕜 := ℝ)
              (f := fun x : DisorderSpace (N := N) =>
                (n : ℝ) * gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
              (x := x)
              (c := ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)))
        rw [hsub, hfderivMul]
        -- Now bound the operator norm.
        have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
        -- `‖c • L‖ = |c| * ‖L‖` and `|n| = n`.
        simpa [Real.norm_eq_abs, abs_of_nonneg hn0, norm_smul, μC, mul_assoc] using
          (mul_le_mul_of_nonneg_left hDG hn0)
      exact this
    -- Now estimate `‖fderiv (P*D)‖`.
    have hPdiff : DifferentiableAt ℝ P x := by
      exact ((contDiff_prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs).differentiable
        (by norm_num)) x
    have hDdiff : DifferentiableAt ℝ D x := by
      -- `D` is a combination of differentiable functions.
      have hGdiff :
          DifferentiableAt ℝ (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ)) x := by
        exact ((contDiff_gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ)).differentiable
          (by norm_num)) x
      have hmul :
          DifferentiableAt ℝ (fun x : DisorderSpace (N := N) =>
              (n : ℝ) * gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x) x :=
        hGdiff.const_mul (n : ℝ)
      have hconst :
          DifferentiableAt ℝ (fun _ : DisorderSpace (N := N) =>
              ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)) x :=
        by simp
      simpa [D] using hmul.sub hconst
    have hPDdiff : DifferentiableAt ℝ (fun x : DisorderSpace (N := N) => P x * D x) x :=
      hPdiff.mul hDdiff
    have hfderivPD :
        fderiv ℝ (fun x : DisorderSpace (N := N) => P x * D x) x
          = (P x) • fderiv ℝ D x + (D x) • fderiv ℝ P x := by
      simpa [P, D] using (fderiv_fun_mul (𝕜 := ℝ) (c := P) (d := D) (hc := hPdiff) (hd := hDdiff))
    -- Bound the norm of `fderiv (P*D)` using the product rule.
    have hPD_norm :
        ‖fderiv ℝ (fun x : DisorderSpace (N := N) => P x * D x) x‖
          ≤ ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) * μC) := by
      -- `‖a • L + b • M‖ ≤ |a|*‖L‖ + |b|*‖M‖`
      rw [hfderivPD]
      have h1 : ‖(P x) • fderiv ℝ D x‖ ≤ 1 * ((n : ℝ) * μC) := by
        have : ‖(P x) • fderiv ℝ D x‖ = |P x| * ‖fderiv ℝ D x‖ := by
          simp [norm_smul]
        rw [this]
        calc
          |P x| * ‖fderiv ℝ D x‖ ≤ 1 * ‖fderiv ℝ D x‖ := by
              exact mul_le_mul_of_nonneg_right hP_abs (norm_nonneg _)
          _ = ‖fderiv ℝ D x‖ := by ring
          _ ≤ (n : ℝ) * μC := hD_der
          _ = 1 * ((n : ℝ) * μC) := by ring
      have h2 : ‖(D x) • fderiv ℝ P x‖ ≤ (2 * (n : ℝ)) * ((n : ℝ) * μC) := by
        have : ‖(D x) • fderiv ℝ P x‖ = |D x| * ‖fderiv ℝ P x‖ := by
          simp [norm_smul]
        rw [this]
        calc
          |D x| * ‖fderiv ℝ P x‖ ≤ (2 * (n : ℝ)) * ‖fderiv ℝ P x‖ := by
              exact mul_le_mul_of_nonneg_right hD_abs (norm_nonneg _)
          _ ≤ (2 * (n : ℝ)) * ((n : ℝ) * μC) := by
              exact mul_le_mul_of_nonneg_left hP_der (by positivity)
      -- Combine via triangle inequality and simplify constants.
      have htri : ‖(P x) • fderiv ℝ D x + (D x) • fderiv ℝ P x‖
          ≤ 1 * ((n : ℝ) * μC) + (2 * (n : ℝ)) * ((n : ℝ) * μC) := by
        exact (norm_add_le _ _).trans (add_le_add h1 h2)
      have htri' :
          ‖(P x) • fderiv ℝ D x + (D x) • fderiv ℝ P x‖
            ≤ (n : ℝ) * μC + (2 * (n : ℝ)) * ((n : ℝ) * μC) := by
        simpa [mul_assoc] using htri
      have hR' :
          (n : ℝ) * μC + (2 * (n : ℝ)) * ((n : ℝ) * μC)
            = ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) * μC) := by ring
      simpa [hR'] using htri'
    -- Finally scale by the constant `f σs`.
    have hdiffPD :
        DifferentiableAt ℝ (fun x : DisorderSpace (N := N) => P x * D x) x := hPDdiff
    have hfderivConst :
        fderiv ℝ (fun x : DisorderSpace (N := N) => (f σs) * (P x * D x)) x
          = (f σs) • fderiv ℝ (fun x : DisorderSpace (N := N) => P x * D x) x := by
      simpa using (fderiv_const_mul (𝕜 := ℝ) (a := fun x : DisorderSpace (N := N) => P x * D x) hdiffPD (b := f σs))
    -- Use `‖c • L‖ = |c| * ‖L‖`.
    have hn : ‖fderiv ℝ (fun x : DisorderSpace (N := N) =>
          (f σs) * (P x * D x)) x‖
          ≤ |f σs| * ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) * μC) := by
      rw [hfderivConst]
      -- `‖c • L‖ = |c| * ‖L‖`, then use `hPD_norm`.
      have : |f σs| * ‖fderiv ℝ (fun x : DisorderSpace (N := N) => P x * D x) x‖
          ≤ |f σs| * ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) * μC) := by
        exact mul_le_mul_of_nonneg_left hPD_norm (abs_nonneg _)
      simpa [norm_smul] using this
    simpa [P, D, mul_assoc, mul_left_comm, mul_comm] using hn
  have :
      (∑ σs : ReplicaSpace N n,
        ‖fderiv ℝ (fun x : DisorderSpace (N := N) =>
            f σs *
              (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x) *
              ((n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
                - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ))) x‖)
        ≤ ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) * μC) *
            (∑ σs : ReplicaSpace N n, |f σs|) := by
    calc
      (∑ σs : ReplicaSpace N n,
          ‖fderiv ℝ (fun x : DisorderSpace (N := N) =>
              f σs *
                (prod_gibbs_pmf_disorder (N := N) (n := n) (h := h) (t := t) σs x) *
                ((n : ℝ) * (gibbs_pmf_disorder (N := N) (h := h) (t := t) (σ := τ) x)
                  - ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ))) x‖)
          ≤ ∑ σs : ReplicaSpace N n,
              |f σs| * ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) * μC) := by
              refine Finset.sum_le_sum (fun σs _ => hsum_bound σs)
      _ = ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) * μC) * (∑ σs : ReplicaSpace N n, |f σs|) := by
              simp [Finset.mul_sum, mul_comm]
  -- Put everything together and rewrite `μC`.
  have hpow : (1 + ‖x‖) ^ (0 : ℕ) = (1 : ℝ) := by simp
  -- finish
  nlinarith [this]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem integral_disorderPairLaw_left_apply_mul_A_disorder_explicit_eq_integral_fderiv_covarianceOperator
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V) (t : ℝ) (f : ReplicaFun N n) (σ τ : Config N) :
    (∫ x : DisorderSpace (N := N),
        ((WithLp.ofLp x).1 σ) *
          (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x)
        ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)))
      =
      ∫ x : DisorderSpace (N := N),
        (fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x)
          (ProbabilityTheory.covarianceOperator
            (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
            (std_basis_left (N := N) σ))
        ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)) := by
  classical
  -- Regularity and growth hypotheses for IBP.
  have hF_c1 :
      ContDiff ℝ 1 (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) :=
    contDiff_A_disorder_explicit (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ)
  have hF_meas :
      Measurable (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) :=
    measurable_A_disorder_explicit (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ)
  let Sf : ℝ := ∑ σs : ReplicaSpace N n, |f σs|
  let μC : ℝ := 2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|)
  let Cfun : ℝ := (2 * (n : ℝ)) * Sf
  let Cder : ℝ := ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) * μC) * Sf
  let C : ℝ := max Cfun Cder
  have hC : 0 ≤ C := by
    have hSf : 0 ≤ Sf :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hn0 : 0 ≤ (2 * (n : ℝ)) := by positivity
    have hμC : 0 ≤ μC := by
      have : (0 : ℝ) ≤ |Real.sqrt t| + |Real.sqrt (1 - t)| := by positivity
      nlinarith [this]
    have hCfun : 0 ≤ Cfun := mul_nonneg hn0 hSf
    have hcoeff : 0 ≤ (2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) := by positivity
    have hCder : 0 ≤ Cder := by
      have : 0 ≤ ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) * μC) * Sf :=
        mul_nonneg (mul_nonneg hcoeff hμC) hSf
      simpa [Cder, mul_assoc, mul_left_comm, mul_comm] using this
    exact le_trans hCfun (le_max_left _ _)
  have hF_growth :
      ∀ x, |A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x|
        ≤ C * (1 + ‖x‖) ^ (0 : ℕ) := by
    intro x
    have h1 :
        |A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x| ≤ Cfun := by
      simpa [Cfun, Sf] using (abs_A_disorder_explicit_le (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ) x)
    have hCfun : Cfun ≤ C := le_max_left _ _
    have : |A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x| ≤ C := le_trans h1 hCfun
    simpa [pow_zero] using this
  have hF'_growth :
      ∀ x, ‖fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x‖
        ≤ C * (1 + ‖x‖) ^ (0 : ℕ) := by
    intro x
    have h1 :
        ‖fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x‖ ≤ Cder := by
      simpa [Cder, Sf, μC] using
        (norm_fderiv_A_disorder_explicit_le (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ) x)
    have hCder : Cder ≤ C := le_max_right _ _
    have : ‖fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x‖ ≤ C :=
      le_trans h1 hCder
    simpa [pow_zero] using this
  -- Apply the generic packaged IBP lemma.
  simpa using
    (integral_disorderPairLaw_left_apply_mul_eq_integral_fderiv_covarianceOperator_polyGrowth
      (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      (hindep := hindep) (σ := σ) (F := A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ)
      hF_meas hF_c1 hC hF_growth hF'_growth)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem integral_disorderPairLaw_right_apply_mul_A_disorder_explicit_eq_integral_fderiv_covarianceOperator
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V) (t : ℝ) (f : ReplicaFun N n) (σ τ : Config N) :
    (∫ x : DisorderSpace (N := N),
        ((WithLp.ofLp x).2 σ) *
          (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x)
        ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)))
      =
      ∫ x : DisorderSpace (N := N),
        (fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x)
          (ProbabilityTheory.covarianceOperator
            (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
            (std_basis_right (N := N) σ))
        ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)) := by
  classical
  -- Reuse the left lemma with the right-hand packaged IBP.
  have hF_c1 :
      ContDiff ℝ 1 (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) :=
    contDiff_A_disorder_explicit (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ)
  have hF_meas :
      Measurable (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) :=
    measurable_A_disorder_explicit (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ)
  let Sf : ℝ := ∑ σs : ReplicaSpace N n, |f σs|
  let μC : ℝ := 2 * (|Real.sqrt t| + |Real.sqrt (1 - t)|)
  let Cfun : ℝ := (2 * (n : ℝ)) * Sf
  let Cder : ℝ := ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) * μC) * Sf
  let C : ℝ := max Cfun Cder
  have hC : 0 ≤ C := by
    have hSf : 0 ≤ Sf :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hn0 : 0 ≤ (2 * (n : ℝ)) := by positivity
    have hμC : 0 ≤ μC := by
      have : (0 : ℝ) ≤ |Real.sqrt t| + |Real.sqrt (1 - t)| := by positivity
      nlinarith [this]
    have hCfun : 0 ≤ Cfun := mul_nonneg hn0 hSf
    have hcoeff : 0 ≤ (2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) := by positivity
    have hCder : 0 ≤ Cder := by
      have : 0 ≤ ((2 * (n : ℝ) * (n : ℝ) + (n : ℝ)) * μC) * Sf :=
        mul_nonneg (mul_nonneg hcoeff hμC) hSf
      simpa [Cder, mul_assoc, mul_left_comm, mul_comm] using this
    exact le_trans hCfun (le_max_left _ _)
  have hF_growth :
      ∀ x, |A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x|
        ≤ C * (1 + ‖x‖) ^ (0 : ℕ) := by
    intro x
    have h1 :
        |A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x| ≤ Cfun := by
      simpa [Cfun, Sf] using (abs_A_disorder_explicit_le (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ) x)
    have hCfun : Cfun ≤ C := le_max_left _ _
    have : |A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x| ≤ C := le_trans h1 hCfun
    simpa [pow_zero] using this
  have hF'_growth :
      ∀ x, ‖fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x‖
        ≤ C * (1 + ‖x‖) ^ (0 : ℕ) := by
    intro x
    have h1 :
        ‖fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x‖ ≤ Cder := by
      simpa [Cder, Sf, μC] using
        (norm_fderiv_A_disorder_explicit_le (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ) x)
    have hCder : Cder ≤ C := le_max_right _ _
    have : ‖fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x‖ ≤ C :=
      le_trans h1 hCder
    simpa [pow_zero] using this
  simpa using
    (integral_disorderPairLaw_right_apply_mul_eq_integral_fderiv_covarianceOperator_polyGrowth
      (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      (hindep := hindep) (σ := σ) (F := A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ)
      hF_meas hF_c1 hC hF_growth hF'_growth)

lemma A_disorder_eq_explicit (t : ℝ) (f : ReplicaFun N n) (τ : Config N) (x : DisorderSpace (N := N)) :
    A_disorder (N := N) (n := n) (h := h) t f τ x
      =
      A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x := by
  classical
  have hcard :
      ∀ σs : ReplicaSpace N n,
        ((Finset.univ.filter fun l : Fin n => σs l = τ).card : ℝ)
          = ((Finset.univ.filter fun l : Fin n => τ = σs l).card : ℝ) := by
    intro σs
    classical
    simp [eq_comm]
  simpa [A_disorder_explicit, hcard] using (by
    simp [A_disorder, fderiv_gibbs_average_n_det_apply, gibbs_pmf_disorder,
      prod_gibbs_pmf_disorder, std_basis, mul_assoc, mul_comm])

lemma dgibbs_average_n_disorder_eq_sum_A (t : ℝ) (f : ReplicaFun N n) (x : DisorderSpace (N := N)) :
    dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f x
      =
      ∑ τ : Config N, (dH_t_disorder (N := N) t x) τ *
        A_disorder (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ) x := by
  classical
  -- Let `G` be the replica functional. Then `dgibbs_average_n_disorder` is the linear map
  -- `T := fderiv G` applied to the direction `v := dH_t_disorder`.
  let G : EnergySpace N → ℝ := fun H' => gibbs_average_n_det (N := N) (n := n) H' f
  let H : EnergySpace N := H_t_disorder (N := N) (h := h) t x
  let v : EnergySpace N := dH_t_disorder (N := N) t x
  let T : EnergySpace N →L[ℝ] ℝ := fderiv ℝ G H
  have hv : v = ∑ τ : Config N, (v τ) • std_basis N τ := by
    classical
    ext σ
    simp [std_basis]
  -- Start from the definition, then expand `v` in the `std_basis` and use linearity.
  have hdg : dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f x = T v := by
    simp [dgibbs_average_n_disorder, G, H, v, T]
  rw [hdg, hv]
  -- Push `T` through the (finite) sum.
  have hmap :
      T (∑ τ : Config N, (v τ) • std_basis N τ)
        =
      ∑ τ : Config N, T ((v τ) • std_basis N τ) := by
    classical
    -- `∑ τ : Config N` is definitionaly `Finset.univ.sum`.
    simp
  -- Now rewrite each summand using linearity and unfold `A_disorder`.
  classical
  simp [hmap, A_disorder, G, H, v, T, smul_eq_mul]

lemma dgibbs_average_n_disorder_eq_sum_left_right (t : ℝ) (f : ReplicaFun N n)
    (x : DisorderSpace (N := N)) :
    dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f x
      =
      (1 / (2 * Real.sqrt t)) *
          ∑ τ : Config N, ((WithLp.ofLp x).1 τ) *
            A_disorder (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ) x
        -
        (1 / (2 * Real.sqrt (1 - t))) *
          ∑ τ : Config N, ((WithLp.ofLp x).2 τ) *
            A_disorder (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ) x := by
  classical
  rw [dgibbs_average_n_disorder_eq_sum_A (N := N) (n := n) (h := h) (t := t) (f := f) x]
  classical
  simp [dH_t_disorder, smul_eq_mul, sub_eq_add_neg, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm, mul_add]

lemma dgibbs_average_n_disorder_eq_sum_left_right_explicit (t : ℝ) (f : ReplicaFun N n)
    (x : DisorderSpace (N := N)) :
    dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f x
      =
      (1 / (2 * Real.sqrt t)) *
          ∑ τ : Config N, ((WithLp.ofLp x).1 τ) *
            A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x
        -
        (1 / (2 * Real.sqrt (1 - t))) *
          ∑ τ : Config N, ((WithLp.ofLp x).2 τ) *
            A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x := by
  classical
  -- Just rewrite `A_disorder` by its explicit formula in `dgibbs_average_n_disorder_eq_sum_left_right`.
  simpa [A_disorder_eq_explicit] using
    (dgibbs_average_n_disorder_eq_sum_left_right (N := N) (n := n) (h := h) (t := t) (f := f) x)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
@[simp] lemma gibbs_average_n_disorder_disorderPair (t : ℝ) (f : ReplicaFun N n) (w : Ω) :
    gibbs_average_n_disorder (N := N) (n := n) (h := h) t f
        (disorderPair (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) w)
      =
      gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w := by
  simp [gibbs_average_n_disorder, gibbs_average_n, H_t_disorder_disorderPair]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
@[simp] lemma dgibbs_average_n_disorder_disorderPair (t : ℝ) (f : ReplicaFun N n) (w : Ω) :
    dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f
        (disorderPair (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) w)
      =
      dgibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w := by
  simp [dgibbs_average_n_disorder, dgibbs_average_n, H_t_disorder_disorderPair,
    dH_t_disorder_disorderPair]

/-!
### Moving between `ℙ` and `disorderPairLaw`

For Gaussian IBP we integrate over the intrinsic `DisorderSpace` law `disorderPairLaw`, not over `Ω`.
These lemmas rewrite the relevant disorder expectations accordingly.
-/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma measurable_disorderPair :
    Measurable (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)) := by
  -- `ω ↦ (U ω, V ω)` is measurable, and `toLp` is measurable.
  have hpair : Measurable (fun ω : Ω => (sk.U ω, sim.V ω)) :=
    sk.measU.prodMk sim.measV
  -- `WithLp.toLp` is measurable (in the canonical measurable structure on `WithLp`).
  simpa [disorderPair] using (WithLp.measurable_toLp (p := (2 : ℝ≥0∞)) (X := (EnergySpace N × EnergySpace N))).comp hpair

lemma measurable_coord_left (τ : Config N) :
    Measurable (fun x : DisorderSpace (N := N) => ((WithLp.ofLp x).1 τ)) := by
  -- rewrite as an inner product with `std_basis_left`.
  have hcont : Continuous (fun x : DisorderSpace (N := N) => inner ℝ x (std_basis_left (N := N) τ)) := by
    have : Continuous (fun x : DisorderSpace (N := N) => (x, std_basis_left (N := N) τ)) :=
      continuous_id.prodMk continuous_const
    simpa using (continuous_inner.comp this)
  simpa [inner_apply_std_basis_left (N := N) (σ := τ)] using hcont.measurable

lemma measurable_coord_right (τ : Config N) :
    Measurable (fun x : DisorderSpace (N := N) => ((WithLp.ofLp x).2 τ)) := by
  have hcont : Continuous (fun x : DisorderSpace (N := N) => inner ℝ x (std_basis_right (N := N) τ)) := by
    have : Continuous (fun x : DisorderSpace (N := N) => (x, std_basis_right (N := N) τ)) :=
      continuous_id.prodMk continuous_const
    simpa using (continuous_inner.comp this)
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
    (∫ w, dgibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w ∂ℙ)
      =
      ∫ x : DisorderSpace (N := N),
        dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f x
          ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)) := by
  classical
  -- `disorderPairLaw = ℙ.map disorderPair`.
  let μ : Measure (DisorderSpace (N := N)) :=
    disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
  have hmeas : AEMeasurable (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim)) (ℙ : Measure Ω) :=
    (measurable_disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)).aemeasurable
  have hF :
      AEStronglyMeasurable (dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f) μ := by
    -- measurability on `DisorderSpace` implies `AEStronglyMeasurable`.
    simpa [μ] using
      (measurable_dgibbs_average_n_disorder (N := N) (n := n) (h := h) (t := t) (f := f)).aestronglyMeasurable
  -- Use `integral_map` and then the simp lemma relating `dgibbs_average_n_disorder` to `dgibbs_average_n`.
  have hmap :
      (∫ x : DisorderSpace (N := N), dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f x ∂μ)
        =
        ∫ w, dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f
            (disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) w) ∂ℙ := by
    -- `μ = map disorderPair ℙ` by definition.
    simpa [μ, disorderPairLaw] using
      (MeasureTheory.integral_map (μ := (ℙ : Measure Ω)) (φ :=
        disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
        hmeas hF)
  simp [hmap, μ]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem integral_dgibbs_average_n_disorder_eq_ibp
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V) (t : ℝ) (f : ReplicaFun N n) :
    (∫ x : DisorderSpace (N := N),
        dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f x
        ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)))
      =
      (1 / (2 * Real.sqrt t)) *
          ∑ τ : Config N,
            ∫ x : DisorderSpace (N := N),
              (fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x)
                (ProbabilityTheory.covarianceOperator
                  (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
                  (std_basis_left (N := N) τ))
              ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
        -
        (1 / (2 * Real.sqrt (1 - t))) *
          ∑ τ : Config N,
            ∫ x : DisorderSpace (N := N),
              (fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x)
                (ProbabilityTheory.covarianceOperator
                  (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
                  (std_basis_right (N := N) τ))
              ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)) := by
  classical
  let μ : Measure (DisorderSpace (N := N)) :=
    disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
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
      (dgibbs_average_n_disorder_eq_sum_left_right_explicit (N := N) (n := n) (h := h) (t := t) (f := f) x)
  -- Integrability of each summand (bounded `A_disorder_explicit` times integrable coordinate).
  have hIntLeft :
      ∀ τ : Config N, Integrable (fun x : DisorderSpace (N := N) =>
        ((WithLp.ofLp x).1 τ) *
          A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x) μ := by
    intro τ
    -- coordinate is integrable under Gaussian law
    have hgauss : ProbabilityTheory.IsGaussian μ :=
      SKDisorder.simple_joint_isGaussian_disorderPairLaw_of_indep (Ω := Ω) (N := N) (β := β) (h := h)
        (q := q) (sk := sk) (sim := sim) hindep
    haveI : ProbabilityTheory.IsGaussian μ := hgauss
    have hcoord :
        Integrable (fun x : DisorderSpace (N := N) => ((WithLp.ofLp x).1 τ)) μ := by
      have : Integrable (fun x : DisorderSpace (N := N) => inner ℝ (std_basis_left (N := N) τ) x) μ := by
        simpa using
          (ProbabilityTheory.IsGaussian.integrable_dual (μ := μ) (L := (innerSL ℝ (std_basis_left (N := N) τ))))
      have : Integrable (fun x : DisorderSpace (N := N) => inner ℝ x (std_basis_left (N := N) τ)) μ := by
        simpa [real_inner_comm] using this
      simpa [inner_apply_std_basis_left (N := N) (σ := τ)] using this
    have hA_meas :
        AEStronglyMeasurable (fun x : DisorderSpace (N := N) =>
          A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x) μ :=
      (measurable_A_disorder_explicit (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ)).aestronglyMeasurable
    -- uniform bound from `abs_A_disorder_explicit_le`
    let Sf : ℝ := ∑ σs : ReplicaSpace N n, |f σs|
    let C : ℝ := (2 * (n : ℝ)) * Sf
    have hA_bound : ∀ᵐ x ∂μ, ‖A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x‖ ≤ C := by
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
      SKDisorder.simple_joint_isGaussian_disorderPairLaw_of_indep (Ω := Ω) (N := N) (β := β) (h := h)
        (q := q) (sk := sk) (sim := sim) hindep
    haveI : ProbabilityTheory.IsGaussian μ := hgauss
    have hcoord :
        Integrable (fun x : DisorderSpace (N := N) => ((WithLp.ofLp x).2 τ)) μ := by
      have : Integrable (fun x : DisorderSpace (N := N) => inner ℝ (std_basis_right (N := N) τ) x) μ := by
        simpa using
          (ProbabilityTheory.IsGaussian.integrable_dual (μ := μ) (L := (innerSL ℝ (std_basis_right (N := N) τ))))
      have : Integrable (fun x : DisorderSpace (N := N) => inner ℝ x (std_basis_right (N := N) τ)) μ := by
        simpa [real_inner_comm] using this
      simpa [inner_apply_std_basis_right (N := N) (σ := τ)] using this
    have hA_meas :
        AEStronglyMeasurable (fun x : DisorderSpace (N := N) =>
          A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x) μ :=
      (measurable_A_disorder_explicit (N := N) (n := n) (h := h) (t := t) (f := f) (τ := τ)).aestronglyMeasurable
    let Sf : ℝ := ∑ σs : ReplicaSpace N n, |f σs|
    let C : ℝ := (2 * (n : ℝ)) * Sf
    have hA_bound : ∀ᵐ x ∂μ, ‖A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x‖ ≤ C := by
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
  simp [μ] at *
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
      (MeasureTheory.integral_finset_sum (μ := μ) (s := (Finset.univ : Finset (Config N)))
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
      (MeasureTheory.integral_finset_sum (μ := μ) (s := (Finset.univ : Finset (Config N)))
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
      (integral_disorderPairLaw_left_apply_mul_A_disorder_explicit_eq_integral_fderiv_covarianceOperator
        (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
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
      (integral_disorderPairLaw_right_apply_mul_A_disorder_explicit_eq_integral_fderiv_covarianceOperator
        (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
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
      (MeasureTheory.integrable_finset_sum (μ := μ) (s := (Finset.univ : Finset (Config N)))
        (f := fun τ : Config N =>
          fun x : DisorderSpace (N := N) => ((WithLp.ofLp x).1 τ) *
            A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ x)
        (hf := by
          intro τ hτ
          simpa using hIntLeft τ))
  have hSright_int : Integrable Sright μ := by
    classical
    simpa [Sright] using
      (MeasureTheory.integrable_finset_sum (μ := μ) (s := (Finset.univ : Finset (Config N)))
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
      -- `WithLp.fst x = (WithLp.ofLp x).1`
      -- avoid `simp` loops on `WithLp.fst/ofLp_fst`
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
  -- Finish with linearity of the integral and the IBP rewrites.
  simp [MeasureTheory.integral_const_mul, hSleft, hSright, hIBP_left_fst, hIBP_right_snd, μ]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma hasDerivAt_gibbs_average_n (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (f : ReplicaFun N n) (w : Ω) :
    HasDerivAt
        (fun s =>
          gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n s f w)
        (dgibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w) t := by
  classical
  let G : EnergySpace N → ℝ := fun H' => gibbs_average_n_det (N := N) (n := n) H' f
  have hG_diff :
      DifferentiableAt ℝ G
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) := by
    simpa [G, gibbs_average_n_det] using
      differentiableAt_gibbs_average_n (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) (n := n) (t := t) (f := f) w
  have hG : HasFDerivAt G (fderiv ℝ G (H_t (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t w))
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) :=
    hG_diff.hasFDerivAt
  have hHt :
      HasDerivAt
          (fun s => H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s w)
          (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) t :=
    hasDerivAt_H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ht w
  have hcomp :=
    (HasFDerivAt.comp_hasDerivAt (x := t) (f := fun s =>
        H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s w)
      (l := G) (l' := fderiv ℝ G (H_t (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t w)) hG hHt)
  simpa [gibbs_average_n, G, dgibbs_average_n] using hcomp

/-!
To differentiate `ν_t(f) = 𝔼[⟨f⟩_t]`, we use the dominated differentiation lemma
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`.

The only nontrivial analytic inputs are:
- pointwise differentiability of `t ↦ ⟨f⟩_t(ω)`,
- an integrable uniform (in `t` near `t₀`) bound on the derivative.
-/

lemma norm_fderiv_gibbs_average_n_det_le (H : EnergySpace N) (f : ReplicaFun N n) :
    ‖fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f) H‖
      ≤ (2 * (n : ℝ)) * (∑ σs : ReplicaSpace N n, ‖f σs‖) := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ (fun v => ?_)
  · have : 0 ≤ (2 : ℝ) * (n : ℝ) := by positivity
    exact mul_nonneg this (by
      exact Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  · have hv_formula :
        fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f) H v =
          ∑ σs : ReplicaSpace N n,
            f σs * (∏ l : Fin n, gibbs_pmf N H (σs l)) *
              ∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)) := by
      simpa using
        fderiv_gibbs_average_n_det_apply (N := N) (n := n) (H := H) (v := v) f
    have hprod_le_one :
        ∀ σs : ReplicaSpace N n, (∏ l : Fin n, gibbs_pmf N H (σs l)) ≤ (1 : ℝ) := by
      intro σs
      classical
      have hfac : ∀ l : Fin n, gibbs_pmf N H (σs l) ≤ 1 := by
        intro l
        exact SpinGlass.gibbs_pmf_le_one (N := N) (H := H) (σ := σs l)
      have hnonneg : ∀ l : Fin n, 0 ≤ gibbs_pmf N H (σs l) := by
        intro l
        exact SpinGlass.gibbs_pmf_nonneg (N := N) (H := H) (σ := σs l)
      simpa using
        (Finset.prod_le_one (s := (Finset.univ : Finset (Fin n)))
          (f := fun l => gibbs_pmf N H (σs l))
          (fun l _hl => hnonneg l) (fun l _hl => hfac l))
    have hEval_le : ∀ τ : Config N, |v τ| ≤ ‖v‖ := by
      intro τ
      simpa [Real.norm_eq_abs] using
        (SpinGlass.abs_apply_le_norm (N := N) v τ)
    have hE_le : |∑ τ : Config N, gibbs_pmf N H τ * v τ| ≤ ‖v‖ := by
      classical
      have hsum1 : (∑ τ : Config N, gibbs_pmf N H τ) = 1 := by
        simpa using SpinGlass.sum_gibbs_pmf (N := N) (H := H)
      calc
        |∑ τ : Config N, gibbs_pmf N H τ * v τ|
            ≤ ∑ τ : Config N, |gibbs_pmf N H τ * v τ| := by
                simpa using
                  (Finset.abs_sum_le_sum_abs
                    (f := fun τ : Config N => gibbs_pmf N H τ * v τ)
                    (s := (Finset.univ : Finset (Config N))))
        _ = ∑ τ : Config N, (gibbs_pmf N H τ) * |v τ| := by
              refine Finset.sum_congr rfl (fun τ _ => ?_)
              rw [abs_mul]
              congr 1
              exact abs_of_nonneg (SpinGlass.gibbs_pmf_nonneg (N := N) (H := H) (σ := τ))
        _ ≤ ∑ τ : Config N, (gibbs_pmf N H τ) * ‖v‖ := by
              refine Finset.sum_le_sum (fun τ _ => ?_)
              gcongr; exact gibbs_pmf_nonneg N H τ; exact hEval_le τ
        _ = ‖v‖ * ∑ τ : Config N, gibbs_pmf N H τ := by
              rw [← Finset.sum_mul]
              exact CommMonoid.mul_comm (∑ i, gibbs_pmf N H i) ‖v‖ --refine Finset.sum_congr rfl (fun τ _ => ?_)
        _ = ‖v‖ := by simp [hsum1]
    have hdiff_le : ∀ σs : ReplicaSpace N n, ∀ l : Fin n,
        |(∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)| ≤ 2 * ‖v‖ := by
      intro σs l
      -- `|a - b| ≤ |a| + |b|`.
      have : |(∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)|
          ≤ |∑ τ : Config N, gibbs_pmf N H τ * v τ| + |v (σs l)| := by
        simpa [sub_eq_add_neg, abs_add_le] using (abs_sub _ _)
      have hvσ : |v (σs l)| ≤ ‖v‖ := by
        simpa using hEval_le (σs l)
      calc
        |(∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)|
            ≤ |∑ τ : Config N, gibbs_pmf N H τ * v τ| + |v (σs l)| := this
        _ ≤ ‖v‖ + ‖v‖ := by gcongr
        _ = 2 * ‖v‖ := by ring
    rw [hv_formula]
    simp only [Real.norm_eq_abs]
    calc
      |∑ σs : ReplicaSpace N n,
          (f σs * (∏ l : Fin n, gibbs_pmf N H (σs l)) *
            ∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)))|
          ≤ ∑ σs : ReplicaSpace N n,
              |f σs * (∏ l : Fin n, gibbs_pmf N H (σs l)) *
                ∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))| := by
                simpa using
                  (Finset.abs_sum_le_sum_abs
                    (f := fun σs : ReplicaSpace N n =>
                      f σs * (∏ l : Fin n, gibbs_pmf N H (σs l)) *
                        ∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)))
                    (s := (Finset.univ : Finset (ReplicaSpace N n))))
      _ = ∑ σs : ReplicaSpace N n,
            (‖f σs‖ * |∏ l : Fin n, gibbs_pmf N H (σs l)| *
              |∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))|) := by
            refine Finset.sum_congr rfl (fun σs _ => ?_)
            simp [abs_mul, Real.norm_eq_abs, mul_assoc]
      _ ≤ ∑ σs : ReplicaSpace N n,
            (‖f σs‖ * (1 : ℝ) * ((2 * (n : ℝ)) * ‖v‖)) := by
            refine Finset.sum_le_sum (fun σs _ => ?_)
            have hprod_abs : |∏ l : Fin n, gibbs_pmf N H (σs l)|
                ≤ (1 : ℝ) := by
              have hnonneg : 0 ≤ ∏ l : Fin n, gibbs_pmf N H (σs l) := by
                classical
                refine Finset.prod_nonneg ?_
                intro l _hl
                exact SpinGlass.gibbs_pmf_nonneg (N := N) (H := H) (σ := σs l)
              have hle1 : (∏ l : Fin n, gibbs_pmf N H (σs l)) ≤ (1 : ℝ) := hprod_le_one σs
              simpa [abs_of_nonneg hnonneg] using hle1
            have hsum_abs :
                |∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))|
                  ≤ (2 * (n : ℝ)) * ‖v‖ := by
              classical
              calc
                |∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))|
                    ≤ ∑ l : Fin n,
                        |(∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)| := by
                          simpa using
                            (Finset.abs_sum_le_sum_abs
                              (f := fun l : Fin n =>
                                (∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))
                              (s := (Finset.univ : Finset (Fin n))))
                _ ≤ ∑ l : Fin n, (2 * ‖v‖) := by
                      refine Finset.sum_le_sum (fun l _ => ?_)
                      exact hdiff_le σs l
                _ = (2 * ‖v‖) * (n : ℝ) := by
                      -- `∑_{Fin n} c = c * n`
                      simp [Finset.card_univ, mul_comm]
              simp [mul_assoc, mul_comm]
            have : ‖f σs‖ * |∏ l : Fin n, gibbs_pmf N H (σs l)| *
                |∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))|
                ≤ ‖f σs‖ * (1 : ℝ) * ((2 * (n : ℝ)) * ‖v‖) := by
              have h1 : |∏ l : Fin n, gibbs_pmf N H (σs l)| ≤ 1 := hprod_abs
              have h2 : |∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))| ≤ (2 * (n : ℝ)) * ‖v‖ := hsum_abs
              have h3 : 0 ≤ ‖f σs‖ := norm_nonneg (f σs)
              have h4 : 0 ≤ |∏ l : Fin n, gibbs_pmf N H (σs l)| := abs_nonneg _
              have h5 : 0 ≤ |∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))| := abs_nonneg _
              calc ‖f σs‖ * |∏ l : Fin n, gibbs_pmf N H (σs l)| *
                      |∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))|
                  ≤ ‖f σs‖ * 1 * |∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))| := by
                    apply mul_le_mul_of_nonneg_right
                    · apply mul_le_mul_of_nonneg_left h1 h3
                    · exact h5
                _ ≤ ‖f σs‖ * 1 * ((2 * (n : ℝ)) * ‖v‖) := by
                    apply mul_le_mul_of_nonneg_left h2
                    apply mul_nonneg h3
                    norm_num
            simpa [mul_assoc] using this
      _ = ((2 * (n : ℝ)) * ‖v‖) * (∑ σs : ReplicaSpace N n, ‖f σs‖) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun σs _ => ?_)
            ring
      _ = (2 * (n : ℝ)) * (∑ σs : ReplicaSpace N n, ‖f σs‖) * ‖v‖ := by
            ring

set_option maxHeartbeats 600000 in
theorem hasDerivAt_nu (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (f : ReplicaFun N n) :
    HasDerivAt
        (fun s => nu (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n s f)
        (∫ w, dgibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w ∂ℙ) t := by
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
      gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n s f w
  let F' : ℝ → Ω → ℝ :=
    fun s w =>
      dgibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n s f w
  have hF_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) (ℙ : Measure Ω) := by
    refine Filter.Eventually.of_forall (fun s => ?_)
    exact (integrable_gibbs_average_n (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) (n := n) (t := s) (f := f)).aestronglyMeasurable
  have hF_int : Integrable (F t) (ℙ : Measure Ω) :=
    integrable_gibbs_average_n (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) (n := n) (t := t) (f := f)
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
  let bound : Ω → ℝ := fun w => Cf * (cU * ‖sk.U w‖ + cV * ‖sim.V w‖)
  have hbound_int : Integrable bound (ℙ : Measure Ω) := by
    have hU_int : Integrable (fun w => ‖sk.U w‖) (ℙ : Measure Ω) :=
      integrable_norm_of_isGaussian_map (P := (ℙ : Measure Ω)) (g := sk.U) sk.measU sk.hU
    have hV_int : Integrable (fun w => ‖sim.V w‖) (ℙ : Measure Ω) :=
      integrable_norm_of_isGaussian_map (P := (ℙ : Measure Ω)) (g := sim.V) sim.measV sim.hV
    have h1 : Integrable (fun w => cU * ‖sk.U w‖) (ℙ : Measure Ω) := (hU_int.const_mul cU)
    have h2 : Integrable (fun w => cV * ‖sim.V w‖) (ℙ : Measure Ω) := (hV_int.const_mul cV)
    have hsum : Integrable (fun w => cU * ‖sk.U w‖ + cV * ‖sim.V w‖) (ℙ : Measure Ω) := h1.add h2
    simpa [bound, Cf, mul_add, mul_assoc] using hsum.const_mul Cf
  have hF'_meas : AEStronglyMeasurable (F' t) (ℙ : Measure Ω) := by
    have hU_meas : Measurable (sk.U) := sk.measU
    have hV_meas : Measurable (sim.V) := sim.measV
    have hHt_meas :
        Measurable (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t) := by
      have h1 : Measurable (fun w => (Real.sqrt t) • sk.U w) := hU_meas.const_smul (Real.sqrt t)
      have h2 : Measurable (fun w => (Real.sqrt (1 - t)) • sim.V w) := hV_meas.const_smul (Real.sqrt (1 - t))
      have h3 : Measurable (fun _w : Ω => H_field (N := N) (h := h)) := measurable_const
      simpa [H_t, H_gauss] using ((h1.add h2).add h3)
    have hdHt_meas :
        Measurable (fun w =>
          dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) := by
      have h1 : Measurable (fun w => (1 / (2 * Real.sqrt t)) • sk.U w) :=
        hU_meas.const_smul (1 / (2 * Real.sqrt t))
      have h2 : Measurable (fun w => (1 / (2 * Real.sqrt (1 - t))) • sim.V w) :=
        hV_meas.const_smul (1 / (2 * Real.sqrt (1 - t)))
      simpa [dH_t, sub_eq_add_neg] using h1.add h2.neg
    have h_gibbs_pmf_meas :
        ∀ (σ : Config N),
          Measurable fun w =>
            gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) σ := by
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
                  (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)) *
                ∑ l : Fin n,
                  ((∑ τ : Config N,
                      gibbs_pmf N
                        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ *
                        (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ) -
                    (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)) := by
      intro σs
      classical
      have hprod :
          Measurable fun w =>
            ∏ l : Fin n,
              gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) := by
        simpa using
          (Finset.measurable_prod (s := (Finset.univ : Finset (Fin n)))
            (f := fun l w =>
              gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))
            (hf := by
              intro l _hl
              simpa using h_gibbs_pmf_meas (σs l)))
      have h_dHt_eval : ∀ τ : Config N, Measurable fun w =>
          (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ := by
        intro τ
        exact (evalCLM (N := N) τ).measurable.comp hdHt_meas
      have hEv :
          Measurable fun w =>
            ∑ τ : Config N,
              gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ *
                (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ := by
        classical
        simpa using
          (Finset.measurable_sum (s := (Finset.univ : Finset (Config N)))
            (f := fun τ w =>
              gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ *
                (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ)
            (hf := by
              intro τ _hτ
              exact (h_gibbs_pmf_meas τ).mul (h_dHt_eval τ)))
      have hsumL :
          Measurable fun w =>
            ∑ l : Fin n,
              ((∑ τ : Config N,
                  gibbs_pmf N
                    (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ *
                    (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ) -
                (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)) := by
        classical
        simpa using
          (Finset.measurable_sum (s := (Finset.univ : Finset (Fin n)))
            (f := fun l w => (∑ τ : Config N,
                  gibbs_pmf N
                    (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ *
                    (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ) -
                (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))
            (hf := by
              intro l _hl
              exact hEv.sub (h_dHt_eval (σs l))))
      simpa [mul_assoc] using (measurable_const.mul (hprod.mul hsumL))
    have hderiv_meas :
        Measurable fun w =>
          (∑ σs : ReplicaSpace N n,
            f σs *
              (∏ l : Fin n,
                gibbs_pmf N
                  (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)) *
                ∑ l : Fin n,
                  ((∑ τ : Config N,
                      gibbs_pmf N
                        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ *
                        (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ) -
                    (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))) := by
      classical
      simpa using
        (Finset.measurable_sum (s := (Finset.univ : Finset (ReplicaSpace N n)))
          (f := fun σs w =>
            f σs *
              (∏ l : Fin n,
                gibbs_pmf N
                  (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)) *
                ∑ l : Fin n,
                  ((∑ τ : Config N,
                      gibbs_pmf N
                        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ *
                        (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ) -
                    (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)))
          (hf := by intro σs _; simpa using hterm σs))
    have :
        (fun w => dgibbs_average_n (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) n t f w)
          =
        (fun w =>
          ∑ σs : ReplicaSpace N n,
            f σs *
              (∏ l : Fin n,
                gibbs_pmf N
                  (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)) *
                ∑ l : Fin n,
                  ((∑ τ : Config N,
                      gibbs_pmf N
                        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ *
                        (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ) -
                    (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))) := by
      funext w
      simp [dgibbs_average_n, fderiv_gibbs_average_n_det_apply]
    simpa [F', this] using hderiv_meas.aestronglyMeasurable
  have h_bound :
      ∀ᵐ w ∂(ℙ : Measure Ω), ∀ x ∈ Metric.ball t ε, ‖F' x w‖ ≤ bound w := by
    refine ae_of_all _ (fun w => ?_)
    intro x hx
    have hxIoo : x ∈ Ioo (0 : ℝ) 1 := hball_Ioo x hx
    have hL :
        ‖fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f)
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)‖ ≤ Cf := by
      simpa [Cf] using
        (norm_fderiv_gibbs_average_n_det_le (N := N) (n := n)
          (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) (f := f))
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
      simpa [cU, abs_of_nonneg hnonneg, abs_of_nonneg hnonneg', abs_of_nonneg (Real.sqrt_nonneg x), one_div]
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
        ‖dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w‖
          ≤ cU * ‖sk.U w‖ + cV * ‖sim.V w‖ := by
      have htri :
          ‖dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w‖
            ≤ |1 / (2 * Real.sqrt x)| * ‖sk.U w‖ +
              |1 / (2 * Real.sqrt (1 - x))| * ‖sim.V w‖ := by
        simpa [dH_t, sub_eq_add_neg, norm_add_le, norm_smul, abs_mul] using
          (norm_add_le ((1 / (2 * Real.sqrt x)) • sk.U w) (-(1 / (2 * Real.sqrt (1 - x))) • sim.V w))
      have : |1 / (2 * Real.sqrt x)| * ‖sk.U w‖ +
            |1 / (2 * Real.sqrt (1 - x))| * ‖sim.V w‖
          ≤ cU * ‖sk.U w‖ + cV * ‖sim.V w‖ := by
        gcongr
      exact le_trans htri this
    have hF'_bound :
        ‖F' x w‖ ≤ Cf * ‖dH_t (N := N) (β := β) (h := h) (q := q)
              (sk := sk) (sim := sim) x w‖ := by
      have hop :
          ‖(fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f)
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w))
              (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)‖
            ≤ ‖fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f)
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)‖ *
              ‖dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w‖ := by
        simpa using
          (ContinuousLinearMap.le_opNorm
            (fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f)
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w))
            (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w))
      have hmul :
          ‖fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f)
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)‖ *
              ‖dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w‖
            ≤ Cf * ‖dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w‖ := by
        exact mul_le_mul_of_nonneg_right hL (norm_nonneg _)
      simpa [F', dgibbs_average_n, mul_assoc] using le_trans hop hmul
    have : ‖F' x w‖ ≤ bound w := by
      have : ‖F' x w‖ ≤ Cf * (cU * ‖sk.U w‖ + cV * ‖sim.V w‖) := by
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
      hasDerivAt_gibbs_average_n (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) (n := n) (t := x) (ht := hxIoo) (f := f) w
  have hMain :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := (ℙ : Measure Ω)) (F := F) (F' := F') (x₀ := t) (bound := bound)
      (s := Metric.ball t ε) (hs := Metric.ball_mem_nhds t hε_pos)
      hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  simpa [nu, F, F'] using hMain

/-!
### Gaussian IBP rewriting of the smart-path derivative

`hasDerivAt_nu` gives the “outer” derivative formula
\[
  \nu_t'(f) = \mathbb{E}[\,\mathrm{d}\langle f\rangle_t\,].
\]
Using the intrinsic disorder law `disorderPairLaw` and the Hilbert-space Gaussian IBP lemmas
packaged above, we can rewrite this derivative as a sum of covariance-operator contractions.
-/

theorem hasDerivAt_nu_ibp (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (f : ReplicaFun N n) :
    HasDerivAt
        (fun s => nu (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n s f)
        ( (1 / (2 * Real.sqrt t)) *
            ∑ τ : Config N,
              ∫ x : DisorderSpace (N := N),
                (fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x)
                  (ProbabilityTheory.covarianceOperator
                    (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
                      (sk := sk) (sim := sim))
                    (std_basis_left (N := N) τ))
                ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
                    (sk := sk) (sim := sim))
          -
          (1 / (2 * Real.sqrt (1 - t))) *
            ∑ τ : Config N,
              ∫ x : DisorderSpace (N := N),
                (fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x)
                  (ProbabilityTheory.covarianceOperator
                    (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
                      (sk := sk) (sim := sim))
                    (std_basis_right (N := N) τ))
                ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
                    (sk := sk) (sim := sim)) ) t := by
  -- Start from the outer derivative formula, then rewrite the derivative value using the packaged IBP lemmas.
  have hder :=
    hasDerivAt_nu (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) (n := n) t ht f
  refine hder.congr_deriv ?_
  calc
    (∫ w,
        dgibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w ∂ℙ)
        =
        ∫ x : DisorderSpace (N := N),
          dgibbs_average_n_disorder (N := N) (n := n) (h := h) t f x
            ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
              (sk := sk) (sim := sim)) := by
          simpa using
            (integral_dgibbs_average_n_eq_integral_disorderPairLaw
              (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) (n := n)
              (t := t) (f := f))
    _ =
        ( (1 / (2 * Real.sqrt t)) *
            ∑ τ : Config N,
              ∫ x : DisorderSpace (N := N),
                (fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x)
                  (ProbabilityTheory.covarianceOperator
                    (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
                      (sk := sk) (sim := sim))
                    (std_basis_left (N := N) τ))
                ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
                    (sk := sk) (sim := sim))
          -
          (1 / (2 * Real.sqrt (1 - t))) *
            ∑ τ : Config N,
              ∫ x : DisorderSpace (N := N),
                (fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x)
                  (ProbabilityTheory.covarianceOperator
                    (disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
                      (sk := sk) (sim := sim))
                    (std_basis_right (N := N) τ))
                ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
                    (sk := sk) (sim := sim)) ) := by
          simpa using
            (integral_dgibbs_average_n_disorder_eq_ibp
              (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) (n := n)
              (hindep := hindep) (t := t) (f := f))

/-!
### Kernel-form of the IBP derivative (Talagrand Vol. II ready)

Using the covariance-kernel specifications of `sk`/`sim`, we can expand the covariance-operator
vectors into explicit finite sums against the canonical basis. This removes `covarianceOperator`
from the final derivative formula and replaces it by the covariance kernels
`sk_cov_kernel` / `simple_cov_kernel`.
-/

-- Kernel expansion lemmas moved to `SpinGlass/SKModel.lean`.

theorem hasDerivAt_nu_kernel (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (f : ReplicaFun N n) :
    HasDerivAt
        (fun s => nu (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n s f)
        ( (1 / (2 * Real.sqrt t)) *
            ∑ τ : Config N,
              ∫ x : DisorderSpace (N := N),
                ∑ σ : Config N,
                  sk_cov_kernel N β τ σ *
                    (fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x)
                      (std_basis_left (N := N) σ)
                ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
                    (sk := sk) (sim := sim))
          -
          (1 / (2 * Real.sqrt (1 - t))) *
            ∑ τ : Config N,
              ∫ x : DisorderSpace (N := N),
                ∑ σ : Config N,
                  simple_cov_kernel N β (fun x => q * x) τ σ *
                    (fderiv ℝ (A_disorder_explicit (N := N) (n := n) (h := h) (t := t) f τ) x)
                      (std_basis_right (N := N) σ)
                ∂(disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
                    (sk := sk) (sim := sim)) ) t := by
  -- Start from the covariance-operator form, then expand the covariance-operator vectors.
  have hder := hasDerivAt_nu_ibp (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
    (sk := sk) (sim := sim) (n := n) (hindep := hindep) t ht f
  refine hder.congr_deriv ?_
  -- Rewrite the covariance-operator vectors into explicit kernel sums.
  simp_rw [covarianceOperator_disorderPairLaw_std_basis_left_eq_sum_sk
    (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) (hindep := hindep)]
  simp_rw [covarianceOperator_disorderPairLaw_std_basis_right_eq_sum_simple
    (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) (hindep := hindep)]
  -- Then use linearity of `fderiv ℝ (A_disorder_explicit ...) x` to push through the finite sums.
  -- (`smul` on `ℝ`-valued linear maps becomes multiplication.)
  simp [mul_assoc, mul_comm, Finset.mul_sum]

end ReplicaCalculus

end SpinGlass
