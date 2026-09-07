import SpinGlass.GuerraTrace

/-!
# Guerra interpolation: combined derivative

`hasDerivAt_guerraPhi` plus the trace/Hessian identity. Main:
`hasDerivAt_guerraPhi_eq_trace_integral`. Talagrand Vol. I, §1.3.
-/

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology
open scoped ENNReal NNReal

namespace SpinGlass

noncomputable section

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {N : ℕ} (β h q : ℝ)
variable (sk : SKDisorder (Ω := Ω) (N := N) β h) (sim : SimpleDisorder (Ω := Ω) (N := N) β q)

private abbrev μ : Measure (DisorderSpace (N := N)) :=
  disorderPairLaw (Ω := Ω) (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)

/-- For `t ∈ (0,1)`, `guerraPhi` is differentiable with Talagrand’s trace/Hessian derivative. -/
theorem hasDerivAt_guerraPhi_eq_trace_integral
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.V)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (guerraPhi (N := N) (β := β) (h := h) (q := q) sk sim)
      (∫ x : DisorderSpace (N := N),
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
        ∂(μ (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim)) t := by
  -- (B1) dominated differentiation.
  have hder :=
    hasDerivAt_guerraPhi (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim t ht
  -- (B2) IBP rewrite of the derivative value.
  have hIBP :=
    derivative_value_guerraPhi_eq_ibp (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) hindep t
  -- (B3) trace/kernel reduction of the IBP expression.
  have hTrace :=
    ibp_value_guerraPhi_eq_trace_integral (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) hindep t ht
  -- Rewrite the derivative value using (B2) then (B3), without letting simp normalize scalars.
  have hderiv_value :
      (∫ ω,
          (fderiv ℝ (fun H' : EnergySpace N => free_energy_density (N := N) H')
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω))
            (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
          ∂ℙ)
        =
        (∫ x : DisorderSpace (N := N),
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
          ∂(μ (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim)) := by
    exact hIBP.trans hTrace
  simpa [hderiv_value] using hder

end

end SpinGlass

