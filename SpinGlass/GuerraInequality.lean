import SpinGlass.GuerraPipeline
import SpinGlass.GuerraBound
import SpinGlass.SKDisorderExists

/-!
# Guerra's interpolation: the derivative inequality

The analytic half (`hasDerivAt_guerraPhi_eq_trace_integral`: `φ'(t)` is the disorder average of a
Hessian trace) and the algebraic half (`guerra_trace_sub_rs_le`: that trace is at most
`(β²/4)(1-q)²` pointwise) are combined here into the uniform derivative bound

`φ'(t) ≤ (β²/4)(1 - q)²`   for `t ∈ (0,1)`,

which is the analytic input to Guerra's replica-symmetric bound.
Talagrand Vol. I, §1.3, Eq. (1.65)–(1.71).

## Main statements

- `hasDerivAt_guerraPhi_le`: `φ` is differentiable at `t` with derivative at most `(β²/4)(1-q)²`.
- `deriv_guerraPhi_le`: the same, phrased with `deriv`.
-/

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology
open scoped ENNReal NNReal

namespace SpinGlass

noncomputable section

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {N : ℕ} (h : ℝ)
variable {K₁ K₂ : Config N → Config N → ℝ}
variable (G₁ : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K₁)
variable (G₂ : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K₂)

/-- Abbreviation for the joint law of the two disorders on `DisorderSpace`. -/
private abbrev μ : Measure (DisorderSpace (N := N)) :=
  disorderPairLaw (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂)

/-- The **Guerra trace**: the pointwise difference of the two kernel-weighted Hessian traces that
Talagrand's formula produces as the derivative of the interpolating free energy at the Hamiltonian
`H`. Talagrand Vol. I, §1.3, Eq. (1.65). -/
noncomputable def guerraTrace (K₁ K₂ : Config N → Config N → ℝ) (H : EnergySpace N) : ℝ :=
  (1 / 2 : ℝ) *
    ( (∑ σ : Config N, ∑ τ : Config N,
          K₁ σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ))
      - (∑ σ : Config N, ∑ τ : Config N,
          K₂ σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ)) )

/-- The Hessian trace of Guerra's derivative is integrable against the disorder law. -/
lemma integrable_guerra_trace_sub (t : ℝ) :
    Integrable (fun x : DisorderSpace (N := N) =>
        guerraTrace (N := N) K₁ K₂ (H_t_disorder N (H_field N h) t x))
      (μ (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂)) :=
  ((integrable_trace_kernel_hessian (Ω := Ω) (N := N) (h := h)
        (G₁ := G₁) (G₂ := G₂) t K₁).sub
    (integrable_trace_kernel_hessian (Ω := Ω) (N := N) (h := h)
        (G₁ := G₁) (G₂ := G₂) t K₂)).const_mul _

/-- **Guerra's derivative bound.** For `t ∈ (0,1)` the interpolating free energy `guerraPhi` is
differentiable at `t`, with derivative at most any pointwise bound `C` for the Guerra trace of the
two covariance kernels. Talagrand Vol. I, §1.3, Eq. (1.71).

For the replica-symmetric interpolation the bound is `guerra_trace_sub_rs_le`, giving
`C = (β²/4)(1 - q)²` with defect the nonnegative overlap term `(β²/4)⟨(R₁₂ - q)²⟩`; for the
Guerra–Toninelli splitting interpolation it is `trace_le_trace_of_kernel_le`, giving `C = 0`. -/
theorem hasDerivAt_guerraPhi_le
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U)
    (hK₁ : ∀ σ τ, K₁ σ τ = K₁ τ σ) (hK₂ : ∀ σ τ, K₂ σ τ = K₂ τ σ)
    {C : ℝ} (hC : ∀ H : EnergySpace N, guerraTrace (N := N) K₁ K₂ H ≤ C)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ d : ℝ,
      HasDerivAt (guerraPhi (N := N) (h := h) (G₁ := G₁) (G₂ := G₂)) d t ∧ d ≤ C := by
  classical
  -- The disorder law is Gaussian, hence a probability measure.
  have hgauss : ProbabilityTheory.IsGaussian
      (μ (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂)) :=
    isGaussian_disorderPairLaw_of_indep
      (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂) hindep
  have hprob : IsProbabilityMeasure (μ (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂)) :=
    hgauss.toIsProbabilityMeasure
  refine ⟨_, hasDerivAt_guerraPhi_eq_trace_integral (Ω := Ω) (N := N) (h := h)
    (G₁ := G₁) (G₂ := G₂) hindep hK₁ hK₂ t ht, ?_⟩
  have hmono := MeasureTheory.integral_mono
    (integrable_guerra_trace_sub (Ω := Ω) (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) t)
    (integrable_const C)
    (fun x => hC (H_t_disorder N (H_field N h) t x))
  simpa [guerraTrace] using hmono

/-- `deriv`-form of Guerra's derivative bound. Talagrand Vol. I, §1.3, Eq. (1.71). -/
theorem deriv_guerraPhi_le
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U)
    (hK₁ : ∀ σ τ, K₁ σ τ = K₁ τ σ) (hK₂ : ∀ σ τ, K₂ σ τ = K₂ τ σ)
    {C : ℝ} (hC : ∀ H : EnergySpace N, guerraTrace (N := N) K₁ K₂ H ≤ C)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (guerraPhi (N := N) (h := h) (G₁ := G₁) (G₂ := G₂)) t ≤ C := by
  obtain ⟨d, hd, hle⟩ :=
    hasDerivAt_guerraPhi_le (Ω := Ω) (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) hindep hK₁ hK₂ hC t ht
  rwa [hd.deriv]

/-! ### Continuity of the interpolation on the closed interval `[0,1]`

Guerra's bound integrates the derivative estimate from `t = 0` to `t = 1`, so `φ` must be
continuous at the two endpoints, where the derivative formula is unavailable (`√t` fails to be
differentiable at `0`). Continuity comes from dominated convergence: on `[0,1]` both `√t` and
`√(1-t)` are at most `1`, so the interpolated Hamiltonian is dominated by `‖U‖ + ‖V‖ + ‖H_field‖`,
which is integrable because `U` and `V` are Gaussian. -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The interpolated Hamiltonian is measurable. -/
lemma measurable_H_t (t : ℝ) :
    Measurable (H_t (N := N) G₁.U G₂.U (H_field N h) t) :=
  ((G₁.measU.const_smul (Real.sqrt t)).add
    (G₂.measU.const_smul (Real.sqrt (1 - t)))).add measurable_const

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The interpolated Hamiltonian is continuous in the interpolation time. -/
lemma continuous_H_t_time (w : Ω) :
    Continuous fun t : ℝ =>
      H_t (N := N) G₁.U G₂.U (H_field N h) t w := by
  have hU : Continuous fun t : ℝ => Real.sqrt t • G₁.U w :=
    Real.continuous_sqrt.smul continuous_const
  have hV : Continuous fun t : ℝ => Real.sqrt (1 - t) • G₂.U w :=
    (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).smul continuous_const
  exact (hU.add hV).add continuous_const

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- On `[0,1]` the interpolated Hamiltonian is dominated by the two disorder norms. -/
lemma norm_H_t_le (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (w : Ω) :
    ‖H_t (N := N) G₁.U G₂.U (H_field N h) t w‖
      ≤ ‖G₁.U w‖ + ‖G₂.U w‖ + ‖H_field N h‖ := by
  have hst : Real.sqrt t ≤ 1 := by
    calc Real.sqrt t ≤ Real.sqrt 1 := Real.sqrt_le_sqrt ht.2
      _ = 1 := Real.sqrt_one
  have hs1t : Real.sqrt (1 - t) ≤ 1 := by
    have h1t : 1 - t ≤ 1 := by linarith [ht.1]
    calc Real.sqrt (1 - t) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h1t
      _ = 1 := Real.sqrt_one
  have hU : ‖Real.sqrt t • G₁.U w‖ ≤ ‖G₁.U w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t)]
    exact mul_le_of_le_one_left (norm_nonneg _) hst
  have hV : ‖Real.sqrt (1 - t) • G₂.U w‖ ≤ ‖G₂.U w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _) hs1t
  calc ‖H_t (N := N) G₁.U G₂.U (H_field N h) t w‖
      ≤ ‖Real.sqrt t • G₁.U w + Real.sqrt (1 - t) • G₂.U w‖
          + ‖H_field N h‖ := norm_add_le _ _
    _ ≤ (‖Real.sqrt t • G₁.U w‖ + ‖Real.sqrt (1 - t) • G₂.U w‖)
          + ‖H_field N h‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ ‖G₁.U w‖ + ‖G₂.U w‖ + ‖H_field N h‖ := by gcongr

/-- The free-energy growth constant is nonnegative. -/
lemma free_energy_growth_const_nonneg :
    (0 : ℝ) ≤ Real.log (Fintype.card (Config N)) + 1 := by
  have h1 : (1 : ℝ) ≤ (Fintype.card (Config N) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := Config N)
  have := Real.log_nonneg h1
  linarith

/-- The dominating function for `guerraPhi` on `[0,1]` is integrable. -/
lemma integrable_guerra_dominating :
    Integrable (fun w : Ω => (Real.log (Fintype.card (Config N)) + 1) *
        (1 + (‖G₁.U w‖ + ‖G₂.U w‖ + ‖H_field N h‖))) (ℙ : Measure Ω) := by
  have hU : Integrable (fun w : Ω => ‖G₁.U w‖) (ℙ : Measure Ω) :=
    integrable_norm_of_isGaussian_map (P := (ℙ : Measure Ω)) (g := G₁.U) G₁.measU G₁.isGaussian
  have hV : Integrable (fun w : Ω => ‖G₂.U w‖) (ℙ : Measure Ω) :=
    integrable_norm_of_isGaussian_map (P := (ℙ : Measure Ω)) (g := G₂.U) G₂.measU G₂.isGaussian
  exact (((integrable_const (1 : ℝ)).add
    ((hU.add hV).add (integrable_const ‖H_field N h‖)))).const_mul _

/-- **`guerraPhi` is continuous on `[0,1]`.** Dominated convergence in the interpolation
parameter. -/
theorem continuousOn_guerraPhi :
    ContinuousOn (guerraPhi (N := N) (h := h) (G₁ := G₁) (G₂ := G₂)) (Set.Icc 0 1) := by
  classical
  refine MeasureTheory.continuousOn_of_dominated
    (bound := fun w : Ω => (Real.log (Fintype.card (Config N)) + 1) *
      (1 + (‖G₁.U w‖ + ‖G₂.U w‖ + ‖H_field N h‖)))
    (fun t _ht => ?_) (fun t ht => ?_)
    (integrable_guerra_dominating (Ω := Ω) (N := N) (h := h) (G₁ := G₁) (G₂ := G₂))
    (Filter.Eventually.of_forall fun w => ?_)
  · exact (((contDiff_free_energy_density (N := N)).continuous.measurable).comp
      (measurable_H_t (Ω := Ω) (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) t)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun w => ?_
    have hgrow := abs_free_energy_density_le (N := N)
      (H := H_t (N := N) G₁.U G₂.U (H_field N h) t w)
    have hdom := norm_H_t_le (Ω := Ω) (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) t ht w
    have hC := free_energy_growth_const_nonneg (N := N)
    calc ‖free_energy_density (N := N)
            (H_t (N := N) G₁.U G₂.U (H_field N h) t w)‖
        ≤ (Real.log (Fintype.card (Config N)) + 1) *
            (1 + ‖H_t (N := N) G₁.U G₂.U (H_field N h) t w‖) := by
          simpa [Real.norm_eq_abs] using hgrow
      _ ≤ (Real.log (Fintype.card (Config N)) + 1) *
            (1 + (‖G₁.U w‖ + ‖G₂.U w‖ + ‖H_field N h‖)) := by
          gcongr
  · exact ((contDiff_free_energy_density (N := N)).continuous.comp
      (continuous_H_t_time (Ω := Ω) (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) w)).continuousOn

/-! ### Guerra's comparison bound -/

/-- **Guerra's bound (finite `N`).** Integrating the derivative estimate `φ'(t) ≤ C` over `[0,1]`:
`φ(1) ≤ φ(0) + C`, where `φ(1)` is the free energy of the first Hamiltonian and `φ(0)` that of the
second. Talagrand Vol. I, §1.3, Theorem 1.3.7. -/
theorem guerraPhi_one_le
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U)
    (hK₁ : ∀ σ τ, K₁ σ τ = K₁ τ σ) (hK₂ : ∀ σ τ, K₂ σ τ = K₂ τ σ)
    {C : ℝ} (hCbd : ∀ H : EnergySpace N, guerraTrace (N := N) K₁ K₂ H ≤ C) :
    guerraPhi (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) 1
      ≤ guerraPhi (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) 0 + C := by
  classical
  set φ : ℝ → ℝ := guerraPhi (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) with hφ
  -- `ψ t = φ t - C t` is antitone on `[0,1]`, since `ψ' = φ' - C ≤ 0` on `(0,1)`.
  set ψ : ℝ → ℝ := fun t => φ t - C * t with hψ
  have hint : interior (Set.Icc (0 : ℝ) 1) = Set.Ioo (0 : ℝ) 1 := by
    simp
  have hderivφ : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt φ (deriv φ t) t := by
    intro t ht
    obtain ⟨d, hd, _⟩ :=
      hasDerivAt_guerraPhi_le (Ω := Ω) (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) hindep hK₁ hK₂
        hCbd t ht
    have hdd : deriv φ t = d := hd.deriv
    rw [hdd]
    exact hd
  have hlin : ∀ t : ℝ, HasDerivAt (fun y : ℝ => C * y) C t := by
    intro t
    simpa using (hasDerivAt_id t).const_mul C
  have hψ_deriv : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), HasDerivAt ψ (deriv φ t - C) t := by
    intro t ht
    rw [hint] at ht
    exact (hderivφ t ht).sub (hlin t)
  have hψ_cont : ContinuousOn ψ (Set.Icc 0 1) := by
    refine ContinuousOn.sub ?_ (continuous_const.mul continuous_id).continuousOn
    exact continuousOn_guerraPhi (Ω := Ω) (N := N) (h := h) (G₁ := G₁) (G₂ := G₂)
  have hψ_anti : AntitoneOn ψ (Set.Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hψ_cont
      (fun t ht => (hψ_deriv t ht).differentiableAt.differentiableWithinAt) (fun t ht => ?_)
    rw [(hψ_deriv t ht).deriv]
    have := deriv_guerraPhi_le (Ω := Ω) (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) hindep hK₁ hK₂
      hCbd t (by rwa [hint] at ht)
    simp only [hφ] at this ⊢
    linarith
  have := hψ_anti (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
    zero_le_one
  simp only [hψ, mul_zero, mul_one, sub_zero] at this
  linarith

/-! ### Endpoint identification

At `t = 1` the interpolation is the first Hamiltonian and at `t = 0` the second, so
`guerraPhi_one_le` compares the two free energies. -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- At `t = 1` the interpolated Hamiltonian is the first Hamiltonian plus the field. -/
@[simp] lemma H_t_one (w : Ω) :
    H_t (N := N) G₁.U G₂.U (H_field N h) 1 w
      = G₁.U w + H_field N h := by
  simp [H_t, H_gauss]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- At `t = 0` the interpolated Hamiltonian is the second Hamiltonian plus the field. -/
@[simp] lemma H_t_zero (w : Ω) :
    H_t (N := N) G₁.U G₂.U (H_field N h) 0 w
      = G₂.U w + H_field N h := by
  simp [H_t, H_gauss]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- `guerraPhi 1` is the free energy of the first Hamiltonian. -/
lemma guerraPhi_one :
    guerraPhi (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) 1
      = ∫ ω, free_energy_density (N := N) (G₁.U ω + H_field N h) ∂ℙ := by
  simp [guerraPhi]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- `guerraPhi 0` is the free energy of the second Hamiltonian. -/
lemma guerraPhi_zero :
    guerraPhi (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) 0
      = ∫ ω, free_energy_density (N := N) (G₂.U ω + H_field N h) ∂ℙ := by
  simp [guerraPhi]

/-- **Guerra's comparison bound (finite `N`), in free-energy form.** The free-energy density of a
centered Gaussian Hamiltonian with kernel `K₁` is dominated by that of an independent one with
kernel `K₂`, plus any pointwise bound `C` on the Guerra trace of the two kernels. Talagrand
Vol. I, §1.3, Theorem 1.3.7. -/
theorem integral_free_energy_density_le
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U)
    (hK₁ : ∀ σ τ, K₁ σ τ = K₁ τ σ) (hK₂ : ∀ σ τ, K₂ σ τ = K₂ τ σ)
    {C : ℝ} (hCbd : ∀ H : EnergySpace N, guerraTrace (N := N) K₁ K₂ H ≤ C) :
    (∫ ω, free_energy_density (N := N) (G₁.U ω + H_field N h) ∂ℙ)
      ≤ (∫ ω, free_energy_density (N := N) (G₂.U ω + H_field N h) ∂ℙ) + C := by
  have := guerraPhi_one_le (Ω := Ω) (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) hindep hK₁ hK₂ hCbd
  rwa [guerraPhi_one (Ω := Ω) (N := N) (h := h) (G₁ := G₁) (G₂ := G₂),
    guerraPhi_zero (Ω := Ω) (N := N) (h := h) (G₁ := G₁) (G₂ := G₂)] at this

/-! ### The replica-symmetric instance

Guerra's original bound is the general comparison at `K₁ = sk_cov_kernel N β`,
`K₂ = simple_cov_kernel N β (q · )`, where the pointwise trace bound is `guerra_trace_sub_rs_le`. -/

/-- **Guerra's replica-symmetric bound (finite `N`), in free-energy form.** The SK free-energy
density is dominated by the reference free-energy density plus `(β²/4)(1 - q)²`, for every choice
of the order parameter `q`. Talagrand Vol. I, §1.3, Theorem 1.3.7. -/
theorem integral_free_energy_density_le_rs {β q : ℝ} (hN : 0 < N)
    (sk : SKDisorder (Ω := Ω) N β) (sim : SimpleDisorder (Ω := Ω) N β q)
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.U) :
    (∫ ω, free_energy_density (N := N) (sk.U ω + H_field N h) ∂ℙ)
      ≤ (∫ ω, free_energy_density (N := N) (sim.U ω + H_field N h) ∂ℙ)
        + (β ^ 2 / 4) * (1 - q) ^ 2 :=
  integral_free_energy_density_le (Ω := Ω) (N := N) (h := h) (G₁ := sk) (G₂ := sim) hindep
    (sk_cov_kernel_comm (N := N) (β := β))
    (simple_cov_kernel_comm (N := N) (β := β) (xi := fun r => q * r))
    (fun H => by
      simpa [guerraTrace] using guerra_trace_sub_rs_le (N := N) (β := β) hN H q)

/-! ### Guerra's bound, unconditionally -/

/-- **Guerra's replica-symmetric bound, with the disorder constructed.** For every system size
`N > 0`, inverse temperature `β`, field `h` and order parameter `0 ≤ q`, there is a probability
space carrying independent centered Gaussian Hamiltonians with the SK covariance `N β² R²/2` and
Guerra's reference covariance `N β² q R`, on which the SK free-energy density is dominated by the
reference free-energy density plus `(β²/4)(1 - q)²`.

This combines `exists_skDisorder_simpleDisorder_indepFun` (the disorder exists, because the
covariance kernels are positive semidefinite) with `integral_free_energy_density_le` (Guerra's
comparison). Talagrand Vol. I, §1.3, Theorem 1.3.7. -/
theorem exists_guerra_bound {N : ℕ} (hN : 0 < N) (β h q : ℝ) (hq : 0 ≤ q) :
    ∃ (Ω : Type) (_ : MeasureSpace Ω) (_ : IsProbabilityMeasure (ℙ : Measure Ω))
      (sk : SKDisorder (Ω := Ω) N β) (sim : SimpleDisorder (Ω := Ω) N β q),
      (∫ ω, free_energy_density (N := N) (sk.U ω + H_field N h) ∂ℙ)
        ≤ (∫ ω, free_energy_density (N := N) (sim.U ω + H_field N h) ∂ℙ)
          + (β ^ 2 / 4) * (1 - q) ^ 2 := by
  obtain ⟨Ω, instΩ, instP, sk, sim, hindep⟩ :=
    exists_skDisorder_simpleDisorder_indepFun N β q hq
  exact ⟨Ω, instΩ, instP, sk, sim,
    integral_free_energy_density_le_rs (Ω := Ω) (N := N) (h := h) hN sk sim hindep⟩

end

end SpinGlass
