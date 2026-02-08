import SpinGlass.Replicas

/-!
# Guerra interpolation: analytic differentiation of the expected free energy

This file provides the **dominated differentiation** step for the Guerra smart path.

Let `H_t = √t • U + √(1-t) • V + H_field` (see `SpinGlass/Replicas.lean`). Define

`φ(t) := 𝔼[ free_energy_density (H_t) ]`.

For `t ∈ (0,1)`, we prove `HasDerivAt φ(t)` and identify the derivative as

`𝔼[ (fderiv free_energy_density (H_t)) (dH_t) ]`.

No Gaussian IBP is used here; this is the analytic layer used before rewriting `φ'(t)` into
Talagrand’s covariance/Hessian trace form.
-/

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology
open scoped ENNReal NNReal

namespace SpinGlass

noncomputable section

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {N : ℕ} (β h q : ℝ)
variable (sk : SKDisorder (Ω := Ω) (N := N) β h) (sim : SimpleDisorder (Ω := Ω) (N := N) β q)

/-- Expected free energy density along the interpolated Hamiltonian `H_t`. -/
noncomputable def guerraPhi (t : ℝ) : ℝ :=
  ∫ ω, free_energy_density (N := N)
    (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω) ∂ℙ

lemma abs_fderiv_free_energy_density_apply_le (H v : EnergySpace N) :
    |fderiv ℝ (fun H' : EnergySpace N => free_energy_density (N := N) H') H v|
      ≤ (1 / (N : ℝ)) * ‖v‖ := by
  simpa [free_energy_density, Z, gibbs_pmf,
    FiniteGibbs.free_energy_density, FiniteGibbs.Z, FiniteGibbs.gibbs_pmf] using
    (FiniteGibbs.abs_fderiv_free_energy_density_apply_le (α := Config N) (n := N) (H := H) (v := v))

/--
Analytic derivative of the expected free energy along the smart path.
-/
theorem hasDerivAt_guerraPhi (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (guerraPhi (N := N) (β := β) (h := h) (q := q) sk sim)
      (∫ ω,
        (fderiv ℝ (fun H' : EnergySpace N => free_energy_density (N := N) H')
          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω))
          (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
        ∂ℙ) t := by
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := ht.2
  have h1t0 : 0 < 1 - t := by linarith
  let ε : ℝ := (min t (1 - t)) / 2
  have hε_pos : 0 < ε := by
    have hmin : 0 < min t (1 - t) := lt_min ht0 h1t0
    have : 0 < (min t (1 - t)) / 2 := by linarith
    simpa [ε] using this
  have hball_Ioo : ∀ x ∈ Metric.ball t ε, x ∈ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    have hx' : |x - t| < ε := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm, ε] using hx
    have hx_upper : x < t + ε := by linarith [(abs_sub_lt_iff.1 hx').1]
    have hx_lower : t - ε < x := by linarith [(abs_sub_lt_iff.1 hx').2]
    have hx_gt0 : 0 < x := by
      have hε_le_t : ε ≤ t / 2 := by
        have : min t (1 - t) ≤ t := min_le_left _ _
        have : (min t (1 - t)) / 2 ≤ t / 2 := by nlinarith
        simpa [ε] using this
      have : 0 < t - ε := by nlinarith [ht0, hε_le_t]
      exact lt_trans this hx_lower
    have hx_lt1 : x < 1 := by
      have hε_le_1t : ε ≤ (1 - t) / 2 := by
        have : min t (1 - t) ≤ (1 - t) := min_le_right _ _
        have : (min t (1 - t)) / 2 ≤ (1 - t) / 2 := by nlinarith
        simpa [ε] using this
      have : t + ε < 1 := by nlinarith [ht1, hε_le_1t]
      exact lt_trans hx_upper this
    exact ⟨hx_gt0, hx_lt1⟩
  let F : ℝ → Ω → ℝ :=
    fun s ω =>
      free_energy_density (N := N)
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s ω)
  let F' : ℝ → Ω → ℝ :=
    fun s ω =>
      (fderiv ℝ (fun H' : EnergySpace N => free_energy_density (N := N) H')
          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s ω))
        (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s ω)
  have hF_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) (ℙ : Measure Ω) := by
    refine Filter.Eventually.of_forall (fun s => ?_)
    have hU : Measurable sk.U := sk.measU
    have hV : Measurable sim.V := sim.measV
    have hHt_meas :
        Measurable (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s) := by
      have h1 : Measurable (fun w => (Real.sqrt s) • sk.U w) := hU.const_smul (Real.sqrt s)
      have h2 : Measurable (fun w => (Real.sqrt (1 - s)) • sim.V w) := hV.const_smul (Real.sqrt (1 - s))
      have h3 : Measurable (fun _w : Ω => H_field (N := N) (h := h)) := measurable_const
      simpa [H_t, H_gauss] using ((h1.add h2).add h3)
    have hcont : Continuous (fun H : EnergySpace N => free_energy_density (N := N) H) :=
      (contDiff_free_energy_density (N := N)).continuous
    exact (hcont.measurable.comp hHt_meas).aestronglyMeasurable
  have hF_int : Integrable (F t) (ℙ : Measure Ω) := by
    let C : ℝ := Real.log (Fintype.card (Config N)) + 1
    have hbound : ∀ H : EnergySpace N, ‖free_energy_density (N := N) H‖ ≤ C * (1 + ‖H‖) := by
      intro H
      have : |free_energy_density (N := N) H| ≤ C * (1 + ‖H‖) := by
        simpa [C] using (abs_free_energy_density_le (N := N) (H := H))
      simpa [Real.norm_eq_abs] using this
    have hU_int : Integrable (fun w => ‖sk.U w‖) (ℙ : Measure Ω) :=
      integrable_norm_of_isGaussian_map (P := (ℙ : Measure Ω)) (g := sk.U) sk.measU sk.hU
    have hV_int : Integrable (fun w => ‖sim.V w‖) (ℙ : Measure Ω) :=
      integrable_norm_of_isGaussian_map (P := (ℙ : Measure Ω)) (g := sim.V) sim.measV sim.hV
    let D : Ω → ℝ := fun w =>
      ‖(Real.sqrt t) • sk.U w‖ + ‖(Real.sqrt (1 - t)) • sim.V w‖ + ‖H_field (N := N) (h := h)‖
    have hD_int : Integrable D (ℙ : Measure Ω) := by
      have h1 : Integrable (fun w => ‖(Real.sqrt t) • sk.U w‖) (ℙ : Measure Ω) := by
        have := (hU_int.const_mul |Real.sqrt t|)
        simpa [norm_smul, Real.norm_eq_abs, abs_mul, mul_assoc] using this
      have h2 : Integrable (fun w => ‖(Real.sqrt (1 - t)) • sim.V w‖) (ℙ : Measure Ω) := by
        have := (hV_int.const_mul |Real.sqrt (1 - t)|)
        simpa [norm_smul, Real.norm_eq_abs, abs_mul, mul_assoc] using this
      have h3 : Integrable (fun _w : Ω => ‖H_field (N := N) (h := h)‖) (ℙ : Measure Ω) :=
        integrable_const _
      simpa [D, add_assoc] using (h1.add (h2.add h3))
    have hdom : Integrable (fun w => C * (1 + D w)) (ℙ : Measure Ω) := by
      have : Integrable (fun w => (1 : ℝ) + D w) (ℙ : Measure Ω) :=
        (integrable_const (1 : ℝ)).add hD_int
      exact this.const_mul C
    refine hdom.mono' (hF_meas.self_of_nhds) ?_
    refine ae_of_all _ (fun w => ?_)
    have hHt_le :
        ‖H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w‖ ≤ D w := by
      have h1 := norm_add_le ((Real.sqrt t) • sk.U w + (Real.sqrt (1 - t)) • sim.V w) (H_field (N := N) (h := h))
      have h2 := norm_add_le ((Real.sqrt t) • sk.U w) ((Real.sqrt (1 - t)) • sim.V w)
      have : ‖(Real.sqrt t) • sk.U w + (Real.sqrt (1 - t)) • sim.V w + H_field (N := N) (h := h)‖
            ≤ ‖(Real.sqrt t) • sk.U w‖ + ‖(Real.sqrt (1 - t)) • sim.V w‖ + ‖H_field (N := N) (h := h)‖ := by
        have : ‖(Real.sqrt t) • sk.U w + (Real.sqrt (1 - t)) • sim.V w + H_field (N := N) (h := h)‖
              ≤ ‖(Real.sqrt t) • sk.U w + (Real.sqrt (1 - t)) • sim.V w‖ + ‖H_field (N := N) (h := h)‖ := by
          simpa [add_assoc] using h1
        linarith [this, h2]
      simpa [H_t, H_gauss, D, add_assoc] using this
    have := hbound (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
    calc
      ‖F t w‖
          = ‖free_energy_density (N := N)
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)‖ := rfl
      _ ≤ C * (1 + ‖H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w‖) := this
      _ ≤ C * (1 + D w) := by gcongr
  have hF'_meas : AEStronglyMeasurable (F' t) (ℙ : Measure Ω) := by
    have hU : Measurable sk.U := sk.measU
    have hV : Measurable sim.V := sim.measV
    have hHt_meas :
        Measurable (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t) := by
      have h1 : Measurable (fun w => (Real.sqrt t) • sk.U w) := hU.const_smul (Real.sqrt t)
      have h2 : Measurable (fun w => (Real.sqrt (1 - t)) • sim.V w) := hV.const_smul (Real.sqrt (1 - t))
      have h3 : Measurable (fun _w : Ω => H_field (N := N) (h := h)) := measurable_const
      simpa [H_t, H_gauss] using ((h1.add h2).add h3)
    have hdHt_meas :
        Measurable (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t) := by
      let aU : ℝ := (Real.sqrt t)⁻¹ * (2 : ℝ)⁻¹
      let aV : ℝ := (Real.sqrt (1 - t))⁻¹ * (2 : ℝ)⁻¹
      have hmeas_simpl :
          Measurable (fun w => aU • sk.U w - aV • sim.V w) :=
        (hU.const_smul aU).sub (hV.const_smul aV)
      have hEq : (fun w => aU • sk.U w - aV • sim.V w) =
          (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t) := by
        funext w
        simp [aU, aV, dH_t, one_div, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
      simpa [hEq] using hmeas_simpl
    have h_gibbs_pmf_meas :
        ∀ (σ : Config N),
          Measurable fun w =>
            gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) σ := by
      intro σ
      have hcont : Continuous fun H : EnergySpace N => gibbs_pmf N H σ :=
        (SpinGlass.contDiff_gibbs_pmf (N := N) (σ := σ)).continuous
      exact hcont.measurable.comp hHt_meas
    have h_dHt_eval : ∀ τ : Config N, Measurable fun w =>
        (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ := by
      intro τ
      exact (evalCLM (N := N) τ).measurable.comp hdHt_meas
    have hsum :
        Measurable fun w =>
          ∑ σ : Config N,
            gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) σ *
              (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) σ := by
      simpa using
        (Finset.measurable_sum (s := (Finset.univ : Finset (Config N)))
          (f := fun σ w =>
            gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) σ *
              (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) σ)
          (hf := by
            intro σ _hσ
            exact (h_gibbs_pmf_meas σ).mul (h_dHt_eval σ)))
    have hmeas' : Measurable fun w =>
        (-(1 / (N : ℝ))) * (∑ σ : Config N,
          gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) σ *
            (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) σ) := by
      exact measurable_const.mul hsum
    have hEq : (fun w => F' t w) =
        fun w =>
          (-(1 / (N : ℝ))) * (∑ σ : Config N,
            gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) σ *
              (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) σ) := by
      funext w
      simp [F', fderiv_free_energy_density_apply (N := N)
        (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
        (h := dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)]
    simpa [hEq] using hmeas'.aestronglyMeasurable
  let cU : ℝ := 1 / (2 * Real.sqrt (t / 2))
  let cV : ℝ := 1 / (2 * Real.sqrt ((1 - t) / 2))
  let bound : Ω → ℝ := fun w => (1 / (N : ℝ)) * (cU * ‖sk.U w‖ + cV * ‖sim.V w‖)
  have hbound_int : Integrable bound (ℙ : Measure Ω) := by
    have hU_int : Integrable (fun w => ‖sk.U w‖) (ℙ : Measure Ω) :=
      integrable_norm_of_isGaussian_map (P := (ℙ : Measure Ω)) (g := sk.U) sk.measU sk.hU
    have hV_int : Integrable (fun w => ‖sim.V w‖) (ℙ : Measure Ω) :=
      integrable_norm_of_isGaussian_map (P := (ℙ : Measure Ω)) (g := sim.V) sim.measV sim.hV
    have h1 : Integrable (fun w => cU * ‖sk.U w‖) (ℙ : Measure Ω) := hU_int.const_mul cU
    have h2 : Integrable (fun w => cV * ‖sim.V w‖) (ℙ : Measure Ω) := hV_int.const_mul cV
    have hsum : Integrable (fun w => cU * ‖sk.U w‖ + cV * ‖sim.V w‖) (ℙ : Measure Ω) := h1.add h2
    simpa [bound, mul_add, mul_assoc] using hsum.const_mul (1 / (N : ℝ))
  have h_bound :
      ∀ᵐ ω ∂(ℙ : Measure Ω), ∀ x ∈ Metric.ball t ε, ‖F' x ω‖ ≤ bound ω := by
    refine ae_of_all _ (fun ω x hx => ?_)
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := hball_Ioo x hx
    have hball : x ∈ Metric.ball t ((min t (1 - t)) / 2) := by
      simpa [ε] using hx
    have hdH :
        ‖dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x ω‖
          ≤ cU * ‖sk.U ω‖ + cV * ‖sim.V ω‖ := by
      simpa [cU, cV] using
        (norm_dH_t_le_on_ball (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) (t := t) (x := x) ht hball ω)
    have hFderiv :
        ‖F' x ω‖ ≤ (1 / (N : ℝ)) * ‖dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x ω‖ := by
      have habs :=
        abs_fderiv_free_energy_density_apply_le (N := N)
          (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x ω)
          (v := dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x ω)
      simpa [F', Real.norm_eq_abs] using habs
    have : ‖F' x ω‖ ≤ bound ω := by
      have : ‖F' x ω‖ ≤ (1 / (N : ℝ)) * (cU * ‖sk.U ω‖ + cV * ‖sim.V ω‖) := by
        exact le_trans hFderiv (mul_le_mul_of_nonneg_left hdH (by positivity))
      simpa [bound, mul_add, mul_assoc, mul_left_comm, mul_comm] using this
    exact this
  have h_diff :
      ∀ᵐ ω ∂(ℙ : Measure Ω), ∀ x ∈ Metric.ball t ε,
        HasDerivAt (fun s => F s ω) (F' x ω) x := by
    refine ae_of_all _ (fun ω x hx => ?_)
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := hball_Ioo x hx
    have hHt : HasDerivAt
        (fun s => H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s ω)
        (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x ω) x :=
      hasDerivAt_H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x hxIoo ω
    simpa [F, F', free_energy_density, Z, FiniteGibbs.free_energy_density, FiniteGibbs.Z,
      ContinuousLinearMap.one_apply] using
      (FiniteGibbs.hasDerivAt_free_energy_density_comp (α := Config N) (n := N) (t := x)
        (H := fun s =>
          H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s ω)
        (H' := dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x ω) hHt)
  have hMain :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := (ℙ : Measure Ω)) (F := F) (F' := F') (x₀ := t) (bound := bound)
      (s := Metric.ball t ε) (hs := Metric.ball_mem_nhds t hε_pos)
      hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  simpa [guerraPhi, F, F'] using hMain

/-!
### First explicit simplification of the derivative value

This rewrites the Fréchet derivative of `free_energy_density` using the closed form
`fderiv_free_energy_density_apply`.

It is the right interface for the subsequent Gaussian IBP step.
-/

lemma derivative_value_guerraPhi_eq (t : ℝ) :
    (∫ ω,
        (fderiv ℝ (fun H' : EnergySpace N => free_energy_density (N := N) H')
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω))
          (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
        ∂ℙ)
      =
      (-(1 / (N : ℝ))) *  ∫ ω, (∑ σ : Config N,
        gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω) σ *
        (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω) σ) ∂ℙ := by
  have hpoint :
      (fun ω =>
          (fderiv ℝ (fun H' : EnergySpace N => free_energy_density (N := N) H')
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω))
            (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω))
        =
      fun ω =>
        (-(1 / (N : ℝ))) *
          (∑ σ : Config N,
              gibbs_pmf N
                  (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω) σ *
                (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω) σ) := by
    funext ω
    simp [fderiv_free_energy_density_apply (N := N)
        (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
        (h := dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)]
  set g : Ω → ℝ := fun ω =>
    (∑ σ : Config N,
        gibbs_pmf N
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω) σ *
          (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω) σ) with hg
  have hpoint' :
      (fun ω =>
          (fderiv ℝ (fun H' : EnergySpace N => free_energy_density (N := N) H')
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω))
            (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω))
        =
      fun ω => (-(1 / (N : ℝ))) * g ω := by
    simpa [hg] using hpoint
  calc
    (∫ ω,
        (fderiv ℝ (fun H' : EnergySpace N => free_energy_density (N := N) H')
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω))
          (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
        ∂ℙ)
        = ∫ ω, (-(1 / (N : ℝ))) * g ω ∂ℙ := by
            simp [hpoint']
    _ = (-(1 / (N : ℝ))) * ∫ ω, g ω ∂ℙ := by
          simpa using (MeasureTheory.integral_const_mul (r := (-(1 / (N : ℝ)))) (f := g) (μ := (ℙ : Measure Ω)))
    _ = (-(1 / (N : ℝ))) *
          ∫ ω,
            (∑ σ : Config N,
                gibbs_pmf N
                    (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω) σ *
                  (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω) σ)
            ∂ℙ := by
          simp [hg]

/-!
## Rewriting `φ` and `φ'` on the intrinsic disorder space

For the IBP step, it is convenient to push the disorder expectation from `Ω` to the law
`disorderPairLaw` on `DisorderSpace`.
-/

section DisorderLaw

private abbrev μ : Measure (DisorderSpace (N := N)) :=
  disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)

lemma guerraPhi_eq_integral_disorderPairLaw (t : ℝ) :
    guerraPhi (N := N) (β := β) (h := h) (q := q) sk sim t
      =
      ∫ x : DisorderSpace (N := N),
        free_energy_density (N := N) (H_t_disorder (N := N) (h := h) t x) ∂(μ (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim) := by
  let φ : Ω → DisorderSpace (N := N) :=
    disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
  have hφ : AEMeasurable φ (ℙ : Measure Ω) := by
    have hpair : Measurable fun ω : Ω => (sk.U ω, sim.V ω) := sk.measU.prodMk sim.measV
    have hmeas : Measurable φ := by
      simpa [φ, disorderPair] using
        (WithLp.prod_continuous_toLp (p := (2 : ℝ≥0∞)) (α := EnergySpace N) (β := EnergySpace N)).measurable.comp hpair
    exact hmeas.aemeasurable
  have hmap : (μ (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim) = (ℙ : Measure Ω).map φ := by
    rfl
  have hf_meas : Measurable fun x : DisorderSpace (N := N) =>
      free_energy_density (N := N) (H_t_disorder (N := N) (h := h) t x) := by
    have hcontF : Continuous (fun H : EnergySpace N => free_energy_density (N := N) H) :=
      (contDiff_free_energy_density (N := N)).continuous
    have hcontH : Continuous (H_t_disorder (N := N) (h := h) t) := by
      simpa [H_t_disorder] using
        (H_t_disorder_lin (N := N) t).continuous.add continuous_const
    exact (hcontF.measurable.comp hcontH.measurable)
  have hf : AEStronglyMeasurable (fun x : DisorderSpace (N := N) =>
      free_energy_density (N := N) (H_t_disorder (N := N) (h := h) t x))
      ((ℙ : Measure Ω).map φ) :=
    hf_meas.aestronglyMeasurable
  have hmain :=
    (MeasureTheory.integral_map (μ := (ℙ : Measure Ω)) (φ := φ)
      (f := fun x : DisorderSpace (N := N) =>
        free_energy_density (N := N) (H_t_disorder (N := N) (h := h) t x))
      hφ hf)
  have hpull :
      (fun ω =>
        (fun x : DisorderSpace (N := N) =>
          free_energy_density (N := N) (H_t_disorder (N := N) (h := h) t x)) (φ ω))
        =
      (fun ω =>
        free_energy_density (N := N)
          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)) := by
    funext ω
    simp [φ,
      H_t_disorder_disorderPair (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)]
  simpa [guerraPhi, hmap, hpull] using hmain.symm

end DisorderLaw

end
