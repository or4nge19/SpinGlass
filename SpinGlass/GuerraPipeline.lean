import SpinGlass.GuerraDerivativeTrace

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
variable (sk : SKDisorder (Ω := Ω) (N := N) β) (sim : SimpleDisorder (Ω := Ω) (N := N) β q)

/-- Abbreviation for the joint law of the SK and reference disorders on `DisorderSpace`. -/
private abbrev μ : Measure (DisorderSpace (N := N)) :=
  disorderPairLaw (Ω := Ω) (N := N) (β := β) (q := q) (sk := sk) (sim := sim)

/-- For `t ∈ (0,1)`, `guerraPhi` is differentiable with Talagrand’s trace/Hessian derivative. -/
theorem hasDerivAt_guerraPhi_eq_trace_integral
    (hindep : sk.U ⟂ᵢ[(ℙ : Measure Ω)] sim.U)
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
        ∂(μ (Ω := Ω) (N := N) (β := β) (q := q) sk sim)) t := by
  -- (B1) dominated differentiation.
  have hder :=
    hasDerivAt_guerraPhi (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim t ht
  -- (B2) the derivative value is a covariance-weighted Hessian trace: the Guerra interpolation
  -- is a two-map affine substitution of the Gaussian disorder, so this is one instance of the
  -- general Gaussian trace identity.
  have hderiv_value :=
    derivative_value_guerraPhi_eq_trace_integral (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) hindep t ht
  simpa [hderiv_value] using hder

end

end SpinGlass

