import SpinGlass.Defs

open MeasureTheory ProbabilityTheory Real BigOperators

namespace SpinGlass

/-!
# Vol. I, §1.3: the SK and replica-symmetric trace identities

The single trace identity `trace_overlapCovKernel` (Talagrand Vol. I, Eq. (1.65)) specialized to
the two choices of `ξ` used in Vol. I, §1.3: `skCovXi β` for the SK Hamiltonian and
`refCovXi β xi` for Guerra's reference Hamiltonian.
-/

variable {N : ℕ} {β : ℝ}

/-- SK trace: `(β²/2) · (1 - ⟨R₁₂²⟩)`. Instance of `trace_overlapCovKernel` at `skCovXi β`.
Talagrand Vol. I, §1.3, Eq. (1.65). -/
theorem trace_sk (hN : 0 < N) (H : EnergySpace N) :
    (∑ σ, ∑ τ, sk_cov_kernel N β σ τ *
        hessian_free_energy N H (std_basis N σ) (std_basis N τ))
      = (β ^ 2 / 2) * (1 - gibbs_average₂ (N := N) H fun σ τ => (overlap N σ τ) ^ 2) := by
  simp only [sk_cov_kernel_def]
  rw [trace_overlapCovKernel (N := N) (hN := hN) (H := H) (xi := skCovXi β)]
  have hbr : gibbs_average₂ (N := N) H (fun σ τ => skCovXi β (overlap N σ τ))
      = (β ^ 2 / 2) * gibbs_average₂ (N := N) H fun σ τ => (overlap N σ τ) ^ 2 := by
    rw [← gibbs_average₂_const_mul (N := N) (H := H) (c := β ^ 2 / 2)
      (f := fun σ τ => (overlap N σ τ) ^ 2)]
    exact congrArg _ (funext fun σ => funext fun τ => by simp [skCovXi]; ring)
  rw [hbr]
  simp [skCovXi]
  ring

/-- Reference trace: `β² · (xi 1 - ⟨xi(R₁₂)⟩)`. Instance of `trace_overlapCovKernel` at
`refCovXi β xi`. Talagrand Vol. I, §1.3. -/
theorem trace_simple (hN : 0 < N) (H : EnergySpace N) (xi : ℝ → ℝ) :
    (∑ σ, ∑ τ, simple_cov_kernel N β xi σ τ *
        hessian_free_energy N H (std_basis N σ) (std_basis N τ))
      = β ^ 2 * (xi 1 - gibbs_average₂ (N := N) H fun σ τ => xi (overlap N σ τ)) := by
  simp only [simple_cov_kernel_def]
  rw [trace_overlapCovKernel (N := N) (hN := hN) (H := H) (xi := refCovXi β xi)]
  have hbr : gibbs_average₂ (N := N) H (fun σ τ => refCovXi β xi (overlap N σ τ))
      = β ^ 2 * gibbs_average₂ (N := N) H fun σ τ => xi (overlap N σ τ) := by
    rw [← gibbs_average₂_const_mul (N := N) (H := H) (c := β ^ 2)
      (f := fun σ τ => xi (overlap N σ τ))]
    rfl
  rw [hbr]
  simp [refCovXi]
  ring

/-- Square completion: `½(1-r²) - q(1-r) = ½((1-q)² - (r-q)²)`. Talagrand Vol. I, Eq. (1.65). -/
lemma square_completion (r q : ℝ) :
    (1 / 2) * (1 - r ^ 2) - q * (1 - r) = (1 / 2) * ((1 - q) ^ 2 - (r - q) ^ 2) := by
  ring

end SpinGlass
