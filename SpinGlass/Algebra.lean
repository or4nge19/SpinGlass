import SpinGlass.Defs

open MeasureTheory ProbabilityTheory Real BigOperators

namespace SpinGlass.Algebra

/-!
# Algebraic identities for finite-`N` SK

Trace identities for SK and simple covariance kernels, and the square-completion identity.
Talagrand Vol. I, §1.3, Eq. (1.65).
-/

variable {N : ℕ} {β : ℝ}

/-- Trace identity for the SK covariance kernel. Talagrand Vol. I, §1.3, Eq. (1.65). -/
lemma trace_sk (hN : 0 < N) (H : EnergySpace N) :
    (∑ σ, ∑ τ, sk_cov_kernel N β σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ)) =
      (β^2 / 2) * (1 - ∑ σ, ∑ τ,
        gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ)^2) :=
  SpinGlass.trace_sk (N := N) (β := β) (hN := hN) (H := H)

/-- Trace identity for the simple covariance kernel. Talagrand Vol. I, §1.3. -/
lemma trace_simple (hN : 0 < N) (H : EnergySpace N) (xi : ℝ → ℝ) :
    (∑ σ, ∑ τ, simple_cov_kernel N β xi σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ)) =
      (β^2) * (xi 1 - ∑ σ, ∑ τ,
        gibbs_pmf N H σ * gibbs_pmf N H τ * xi (overlap N σ τ)) :=
  SpinGlass.trace_simple (N := N) (β := β) (xi := xi) (hN := hN) (H := H)

/-- Square completion: `½(1-r²) - q(1-r) = ½((1-q)² - (r-q)²)`. Talagrand Vol. I, Eq. (1.65). -/
lemma square_completion (r q : ℝ) :
    (1 / 2) * (1 - r^2) - q * (1 - r) = (1 / 2) * ((1 - q)^2 - (r - q)^2) := by
  ring

end SpinGlass.Algebra
