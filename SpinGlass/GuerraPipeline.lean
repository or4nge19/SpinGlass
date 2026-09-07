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
variable {N : ℕ} (h : ℝ)
variable {K₁ K₂ : Config N → Config N → ℝ}
variable (G₁ : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K₁)
variable (G₂ : GaussianDisorder (Ω := Ω) (N := N) (ℙ : Measure Ω) K₂)

/-- Abbreviation for the joint law of the two disorders on `DisorderSpace`. -/
private abbrev μ : Measure (DisorderSpace (N := N)) :=
  disorderPairLaw (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂)

/-- For `t ∈ (0,1)`, `guerraPhi` is differentiable with Talagrand’s trace/Hessian derivative, for
an arbitrary independent pair of centered Gaussian Hamiltonians with symmetric kernels. -/
theorem hasDerivAt_guerraPhi_eq_trace_integral
    (hindep : G₁.U ⟂ᵢ[(ℙ : Measure Ω)] G₂.U)
    (hK₁ : ∀ σ τ, K₁ σ τ = K₁ τ σ) (hK₂ : ∀ σ τ, K₂ σ τ = K₂ τ σ)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (guerraPhi (N := N) (h := h) (G₁ := G₁) (G₂ := G₂))
      (∫ x : DisorderSpace (N := N),
        (1 / 2 : ℝ) *
          ( (∑ σ : Config N, ∑ τ : Config N,
                K₁ σ τ *
                  hessian_free_energy N (H_t_disorder N (H_field N h) t x)
                    (std_basis N σ) (std_basis N τ))
            -
            (∑ σ : Config N, ∑ τ : Config N,
                K₂ σ τ *
                  hessian_free_energy N (H_t_disorder N (H_field N h) t x)
                    (std_basis N σ) (std_basis N τ)) )
        ∂(μ (Ω := Ω) (N := N) (G₁ := G₁) (G₂ := G₂))) t := by
  -- (B1) dominated differentiation.
  have hder :=
    hasDerivAt_guerraPhi (Ω := Ω) (N := N) (h := h) (G₁ := G₁) (G₂ := G₂) t ht
  -- (B2) the derivative value is a covariance-weighted Hessian trace: the Guerra interpolation
  -- is a two-map affine substitution of the Gaussian disorder, so this is one instance of the
  -- general Gaussian trace identity.
  have hderiv_value :=
    derivative_value_guerraPhi_eq_trace_integral (Ω := Ω) (N := N) (h := h)
      (G₁ := G₁) (G₂ := G₂) hindep hK₁ hK₂ t ht
  simpa [hderiv_value] using hder

end

end SpinGlass

