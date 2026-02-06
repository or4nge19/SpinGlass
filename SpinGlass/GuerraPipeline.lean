import SpinGlass.GuerraTrace

/-!
# Guerra interpolation: combined derivative theorem

`SpinGlass.GuerraTrace` identifies the derivative value appearing in `hasDerivAt_guerraPhi` with
Talagrand’s trace/Hessian expression under the intrinsic disorder law.

This file records the combined statement as `hasDerivAt_guerraPhi_eq_trace_integral`, so that
downstream arguments (e.g. the Guerra bound) can use it directly.
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

/--
**Guerra derivative in trace/Hessian form (combined statement).**

For \(t\in(0,1)\), the function `guerraPhi` is differentiable at `t` and its derivative is given by
the Talagrand trace/Hessian expression, integrated against the intrinsic disorder law
`disorderPairLaw`.

This is exactly `hasDerivAt_guerraPhi` composed with the trace identity
`derivative_value_guerraPhi_eq_trace_integral`.
-/
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
  -- Start from the dominated differentiation step.
  have hder :=
    hasDerivAt_guerraPhi (Ω := Ω) (N := N) (β := β) (h := h) (q := q) sk sim t ht
  -- Rewrite the derivative value using the trace/Hessian identity.
  simpa [μ,
    derivative_value_guerraPhi_eq_trace_integral (Ω := Ω) (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) hindep t ht]
    using hder

end

end SpinGlass

