import SpinGlass.SKModel
import SpinGlass.GuerraBound
import SpinGlass.Calculus
import SpinGlass.ReplicaMeasure
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

We avoid the coordinate-based `IsGaussianHilbert` packaging. Instead we work with the intrinsic
law-based predicate `IsGaussian ((ℙ).map g)`. Basic integrability properties are obtained by
pulling back integrability on the law along the map measure.
-/

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

/--
Uniform bound on the n-replica Gibbs average:
\[
|\langle f\rangle_{t,n}| \le \max_{\sigma^1,\dots,\sigma^n} |f(\sigma^1,\dots,\sigma^n)|.
\]
-/
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

lemma hasDerivAt_H_t (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (w : Ω) :
    HasDerivAt
        (fun s =>
          H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s w)
        (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) t := by
  simpa [H_t, dH_t, H_field]
    using (hasDerivAt_H_gauss (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ht w).add_const
      (H_field (N := N) (h := h))

/-- Pointwise derivative of the `n`-replica Gibbs average along the path `H_t`. -/
noncomputable def dgibbs_average_n (t : ℝ) (f : ReplicaFun N n) (w : Ω) : ℝ :=
  fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f)
    (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
    (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)

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

end ReplicaCalculus

end SpinGlass
